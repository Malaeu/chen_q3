"""Score expansion sanity-check for Lemma 7.2.

Verifies that the commutator norm decomposition matches the theoretical formula:

    ||[H, S] Psi||^2 = C_X^(0) - 2 c_X * T_w(X) + E_X

where:
    C_X^(0) = D_A^2 + D_diag^2  (background)
    T_w(X) = sum_{twin pairs} Lambda(n)*Lambda(n+2) * W_X(n)  (twin sum)
    c_X = calibration constant
    E_X = error term

Also tests multiplicative model: D^2 ~ c / T_raw^beta
"""

from __future__ import annotations

import numpy as np
from math import log, pi, sqrt

from .hamiltonian import build_hamiltonian, fejer_heat_kernel
from .shift import phase_shift
from .twins_state import build_twins_vector
from .commutator_resonance import commutator_metrics


def sieve_primes(n_max: int) -> list[int]:
    """Simple sieve of Eratosthenes."""
    sieve = bytearray(b"\x01") * (n_max + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(n_max ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p : n_max + 1 : p] = b"\x00" * (((n_max - p * p) // p) + 1)
    return [i for i, b in enumerate(sieve) if b]


def find_twin_pairs(X_max: int) -> list[tuple[int, int]]:
    """Find all twin prime pairs (p, p+2) with p <= X_max."""
    primes = set(sieve_primes(X_max + 2))
    twins = []
    for p in primes:
        if p + 2 in primes and p <= X_max:
            twins.append((p, p + 2))
    return sorted(twins)


def twin_sum_weighted(X: int, weight_mode: str = "raw", beta: float = 1.0) -> float:
    """Compute weighted twin sum T_w(X) = sum Lambda(p)*Lambda(p+2) * W_X(p).

    Args:
        X: upper bound for twins
        weight_mode: "raw" (W=1), "inv_p" (W=1/p), "p_power" (W=p^{-beta})
        beta: exponent for p_power mode

    Returns:
        T_w(X)
    """
    twins = find_twin_pairs(X)
    T_w = 0.0

    for p, q in twins:
        Lambda_p = log(p)
        Lambda_q = log(q)
        contrib = Lambda_p * Lambda_q

        if weight_mode == "raw":
            W_p = 1.0
        elif weight_mode == "inv_p":
            W_p = 1.0 / p
        elif weight_mode == "p_power":
            W_p = p ** (-beta)
        else:
            raise ValueError(f"Unknown weight_mode={weight_mode}")

        T_w += contrib * W_p

    return T_w


def twin_sum_raw(X: int) -> float:
    """Compute raw twin sum sum Lambda(n)*Lambda(n+2) for n <= X."""
    twins = find_twin_pairs(X)
    return sum(log(p) * log(q) for p, q in twins)


def score_expansion_check(X_list: list[int], K: float = 2.5, M: int = 256,
                          t_sym: float = 0.3, twin_t: float = 0.3,
                          calibrate_at: int = None,
                          weight_mode: str = "raw",
                          normalize: bool = True) -> list[dict]:
    """Run score expansion sanity check.

    Args:
        X_list: list of X values to test
        K, M, t_sym, twin_t: Hamiltonian/vector parameters
        calibrate_at: X value to calibrate c_X (default: first)
        weight_mode: "raw", "inv_p", or "p_power"
        normalize: whether to normalize Psi_X

    Returns list of dicts with all computed quantities.
    """

    results = []
    c_X_add = None  # additive model: D^2 = C0 - 2c*T + E
    c_X_mult = None  # multiplicative model: D^2 = c / T^beta

    for X in X_list:
        # Build operators
        H, xi, prime_vecs = build_hamiltonian(K, M, X, t_sym=t_sym,
                                               return_prime_vectors=True)
        delta = 1.0 / X
        S = phase_shift(xi, delta)
        psi = build_twins_vector(X, xi, t=twin_t, twin_only=True, normalize=normalize)

        # Geometric computation
        C, D2, R, comps = commutator_metrics(H, S, psi, return_components=True,
                                              diag_vectors=prime_vecs)

        D2_A = comps['D2_A']
        D2_diag = comps['D2_diag']
        D2_twin = comps['D2_twin']

        # Background
        C0_X = D2_A + D2_diag

        # Twin sums
        T_w = twin_sum_weighted(X, weight_mode=weight_mode)
        T_raw = twin_sum_raw(X)

        # Mass (should be 1 if normalized)
        M_Phi = np.sqrt(np.vdot(psi, psi).real)

        # Calibrate at first point
        if c_X_add is None:
            if calibrate_at is None or X == calibrate_at:
                # Additive: D2 = C0 - 2c*T => c = (C0 - D2) / (2T)
                T_use = T_raw if weight_mode == "raw" else T_w
                if abs(T_use) > 1e-10:
                    c_X_add = (C0_X - D2) / (2 * T_use)
                else:
                    c_X_add = 0.0
                # Multiplicative: D2 = c / T^beta => c = D2 * T^beta
                # Use beta=1.12 from our fit
                c_X_mult = D2 * (T_raw ** 1.12)
                print(f"Calibrated at X = {X}:")
                print(f"  c_add = {c_X_add:.6e}")
                print(f"  c_mult = {c_X_mult:.6e} (D2 ~ c/T^1.12)")

        # Predictions
        T_use = T_raw if weight_mode == "raw" else T_w
        D2_pred_add = C0_X - 2 * c_X_add * T_use
        D2_pred_mult = c_X_mult / (T_raw ** 1.12)

        # Errors
        E_add = D2 - D2_pred_add
        E_mult = D2 - D2_pred_mult
        eps_add = abs(E_add) / abs(D2) if abs(D2) > 0 else float('nan')
        eps_mult = abs(E_mult) / abs(D2) if abs(D2) > 0 else float('nan')

        results.append({
            'X': X,
            'D2': D2,
            'D2_A': D2_A,
            'D2_diag': D2_diag,
            'D2_twin': D2_twin,
            'C0_X': C0_X,
            'T_w': T_w,
            'T_raw': T_raw,
            'D2_pred_add': D2_pred_add,
            'D2_pred_mult': D2_pred_mult,
            'E_add': E_add,
            'E_mult': E_mult,
            'eps_add': eps_add,
            'eps_mult': eps_mult,
            'M_Phi': M_Phi,
            'c_add': c_X_add,
            'c_mult': c_X_mult,
        })

    return results


def print_report(results: list[dict]) -> None:
    """Print formatted report of score expansion check."""

    print("=" * 110)
    print("SCORE EXPANSION SANITY CHECK")
    print("=" * 110)
    print()
    print("Model 1 (Additive): D^2 = C_X^(0) - 2 c T(X) + E")
    print("Model 2 (Multiplicative): D^2 = c / T_raw^1.12")
    print()

    print(f"{'X':>10}  {'D^2':>12}  {'D^2_add':>12}  {'eps_add%':>10}  "
          f"{'D^2_mult':>12}  {'eps_mult%':>10}")
    print("-" * 90)

    for r in results:
        eps_add = r['eps_add'] * 100 if not np.isnan(r['eps_add']) else float('nan')
        eps_mult = r['eps_mult'] * 100 if not np.isnan(r['eps_mult']) else float('nan')
        print(f"{r['X']:>10}  {r['D2']:>12.3e}  {r['D2_pred_add']:>12.3e}  {eps_add:>10.2f}  "
              f"{r['D2_pred_mult']:>12.3e}  {eps_mult:>10.2f}")

    print()
    print("=" * 110)
    print("COMPONENT ANALYSIS")
    print("=" * 110)
    print()
    print(f"{'X':>10}  {'D2_A':>12}  {'D2_diag':>12}  {'D2_twin':>12}  "
          f"{'T_raw':>12}  {'M_Phi':>12}")
    print("-" * 80)

    for r in results:
        print(f"{r['X']:>10}  {r['D2_A']:>12.3e}  {r['D2_diag']:>12.3e}  "
              f"{r['D2_twin']:>12.3e}  {r['T_raw']:>12.3e}  {r['M_Phi']:>12.3e}")

    print()

    # Correlations and slopes
    Xs = np.array([r['X'] for r in results])
    D2s = np.array([r['D2'] for r in results])
    D2_twins = np.array([r['D2_twin'] for r in results])
    T_raws = np.array([r['T_raw'] for r in results])

    if len(Xs) > 2:
        corr = np.corrcoef(D2_twins, T_raws)[0, 1]
        print(f"Correlation(D2_twin, T_raw): {corr:.4f}")

        # Also check multiplicative fit quality
        corr_inv = np.corrcoef(D2_twins, 1.0 / T_raws)[0, 1]
        print(f"Correlation(D2_twin, 1/T_raw): {corr_inv:.4f}")

    def loglog_fit(xs, ys):
        mask = (xs > 0) & (ys > 0) & np.isfinite(ys)
        if mask.sum() < 2:
            return float('nan'), float('nan')
        lx, ly = np.log(xs[mask]), np.log(ys[mask])
        A = np.vstack([lx, np.ones_like(lx)]).T
        coef = np.linalg.lstsq(A, ly, rcond=None)[0]
        return coef[0], np.exp(coef[1])

    print()
    print("Log-log fits (y ~ c * x^slope):")
    slope, c = loglog_fit(Xs, D2s)
    print(f"  D2 ~ {c:.2e} * X^{slope:.3f}")
    slope, c = loglog_fit(Xs, np.abs(D2_twins))
    print(f"  D2_twin ~ {c:.2e} * X^{slope:.3f}")
    slope, c = loglog_fit(Xs, T_raws)
    print(f"  T_raw ~ {c:.2e} * X^{slope:.3f}")

    # Fit D2 vs T_raw
    print()
    print("Power-law fit D2_twin ~ c / T_raw^beta:")
    log_D2 = np.log(np.abs(D2_twins[D2_twins > 0]))
    log_T = np.log(T_raws[D2_twins > 0])
    if len(log_D2) > 2:
        A = np.vstack([log_T, np.ones_like(log_T)]).T
        coef = np.linalg.lstsq(A, log_D2, rcond=None)[0]
        beta = -coef[0]
        c = np.exp(coef[1])
        print(f"  D2_twin ~ {c:.2e} / T_raw^{beta:.3f}")


if __name__ == "__main__":
    X_list = [10_000, 20_000, 50_000, 100_000, 200_000, 500_000, 1_000_000]

    print("Running with normalize=True, weight_mode='raw'")
    print()
    results = score_expansion_check(X_list, K=2.5, M=256, t_sym=0.3, twin_t=0.3,
                                     weight_mode="raw", normalize=True)
    print_report(results)
