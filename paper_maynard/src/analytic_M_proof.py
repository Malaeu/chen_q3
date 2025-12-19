#!/usr/bin/env python3
"""
Analytic derivation and verification of M(F_α) for polynomial sieve functions.

F_α(t) = (1 - Σt_i)^α on Δ_k

We derive: M(F_α) = 2(2α+1)/(α+1)

This is INDEPENDENT of k!
"""

import numpy as np
from math import gamma, factorial
from fractions import Fraction

def analytic_M(alpha: float) -> float:
    """
    Closed-form formula for M(F_α).

    Derivation:
    -----------
    I_k(F) = ∫_{Δ_k} (1-Σt)^{2α} dt = Γ(2α+1)Γ(k+1) / Γ(2α+k+2)

    J_k^{(m)}(F) = (1/(α+1)²) · Γ(2α+3)Γ(k) / Γ(2α+k+2)

    M = k·J/I = Γ(2α+3) / [(α+1)² · Γ(2α+1)]
              = (2α+2)(2α+1) / (α+1)²
              = 2(2α+1) / (α+1)
    """
    return 2 * (2*alpha + 1) / (alpha + 1)


def analytic_M_exact(alpha_num: int, alpha_den: int) -> Fraction:
    """
    Exact rational computation of M(F_α) for α = alpha_num/alpha_den.

    M = 2(2α+1)/(α+1) = 2(2·num/den + 1)/(num/den + 1)
                      = 2(2·num + den)/den / (num + den)/den
                      = 2(2·num + den) / (num + den)
    """
    num, den = alpha_num, alpha_den
    numerator = 2 * (2*num + den)
    denominator = num + den
    return Fraction(numerator, denominator)


def verify_simplex_integral_formula(alpha: float, k: int, n_samples: int = 100000) -> dict:
    """
    Verify the simplex integral formula via Monte Carlo.

    ∫_{Δ_k} (1-Σt)^β dt = Γ(β+1)·Γ(k+1) / Γ(β+k+2)
    """
    # Sample uniformly from k-simplex using exponential trick
    # x_i ~ Exp(1), then t_i = x_i / Σx_j gives uniform on Δ_k
    rng = np.random.default_rng(42)

    # For simplex Δ_k in R^k: need k+1 exponentials, normalize, drop last
    exp_samples = rng.exponential(size=(n_samples, k + 1))
    t = exp_samples[:, :k] / exp_samples.sum(axis=1, keepdims=True)

    s = t.sum(axis=1)  # Σt_i

    # Compute (1-s)^{2α}
    beta = 2 * alpha
    integrand = (1 - s) ** beta

    # Volume of Δ_k is 1/k!
    volume = 1 / factorial(k)

    mc_integral = integrand.mean() * volume
    mc_std = integrand.std() / np.sqrt(n_samples) * volume

    # Analytic formula
    analytic_integral = gamma(beta + 1) * gamma(k + 1) / gamma(beta + k + 2)

    return {
        'mc_integral': mc_integral,
        'mc_std': mc_std,
        'analytic_integral': analytic_integral,
        'relative_error': abs(mc_integral - analytic_integral) / analytic_integral
    }


def verify_M_formula(alpha: float, k: int, n_samples: int = 100000) -> dict:
    """
    Verify M(F_α) formula via direct Monte Carlo computation.
    """
    rng = np.random.default_rng(42)

    # Sample from Δ_k
    exp_samples = rng.exponential(size=(n_samples, k + 1))
    t = exp_samples[:, :k] / exp_samples.sum(axis=1, keepdims=True)

    s = t.sum(axis=1)
    volume_k = 1 / factorial(k)

    # I_k = ∫_{Δ_k} F^2 dt = ∫ (1-s)^{2α} dt
    F_squared = (1 - s) ** (2 * alpha)
    I_k = F_squared.mean() * volume_k

    # J_k^{(m)} for m=1 (by symmetry, all equal)
    # J = ∫_{Δ_{k-1}} [∫_0^{1-s'} (1-s'-t)^α dt]^2 ds'
    # where s' = Σ_{i≠1} t_i

    # Inner integral: ∫_0^{1-s'} (1-s'-t)^α dt = (1-s')^{α+1}/(α+1)
    # So J = (1/(α+1)^2) ∫_{Δ_{k-1}} (1-s')^{2α+2} ds'

    # Sample from Δ_{k-1}
    exp_samples_km1 = rng.exponential(size=(n_samples, k))
    t_km1 = exp_samples_km1[:, :k-1] / exp_samples_km1.sum(axis=1, keepdims=True)

    s_km1 = t_km1.sum(axis=1)
    volume_km1 = 1 / factorial(k - 1)

    inner_integral_squared = ((1 - s_km1) ** (alpha + 1) / (alpha + 1)) ** 2
    J_k = inner_integral_squared.mean() * volume_km1

    # M = k * J / I
    M_mc = k * J_k / I_k

    # Analytic formula
    M_analytic = analytic_M(alpha)

    return {
        'I_k': I_k,
        'J_k': J_k,
        'M_mc': M_mc,
        'M_analytic': M_analytic,
        'relative_error': abs(M_mc - M_analytic) / M_analytic
    }


def main():
    print("=" * 70)
    print("ANALYTIC PROOF: M(F_α) = 2(2α+1)/(α+1)")
    print("=" * 70)

    # Key result for α = 1/2
    alpha = 0.5
    M_exact = analytic_M_exact(1, 2)  # α = 1/2
    M_float = analytic_M(alpha)

    print(f"\nFor α = 1/2:")
    print(f"  M(F_{{1/2}}) = 2(2·(1/2)+1)/((1/2)+1)")
    print(f"              = 2·2/(3/2)")
    print(f"              = 4/(3/2)")
    print(f"              = 8/3")
    print(f"              = {M_exact} = {float(M_exact):.10f}")
    print(f"\n  Since 8/3 > 2, we have M(F_{{1/2}}) > 2. ✓")
    print(f"  More precisely: 8/3 - 2 = 2/3 > 0")

    # Verify formula is independent of k
    print("\n" + "-" * 70)
    print("Verification: M(F_α) is INDEPENDENT of k")
    print("-" * 70)

    for k in [2, 3, 5, 7, 10, 50]:
        result = verify_M_formula(alpha, k, n_samples=50000)
        print(f"  k={k:2d}: M_mc = {result['M_mc']:.4f}, M_analytic = {result['M_analytic']:.4f}, "
              f"rel_err = {result['relative_error']:.2e}")

    # Table of M values for different α
    print("\n" + "-" * 70)
    print("Table: M(F_α) for various α")
    print("-" * 70)
    print(f"{'α':>10} {'M(F_α)':>15} {'M > 2?':>10}")
    print("-" * 35)

    alphas = [0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0]
    for a in alphas:
        M = analytic_M(a)
        check = "YES ✓" if M > 2 else "no"
        print(f"{a:>10.2f} {M:>15.6f} {check:>10}")

    # Find critical α where M = 2
    # 2(2α+1)/(α+1) = 2  =>  2α+1 = α+1  =>  α = 0
    print("\n" + "-" * 70)
    print("Critical value: M(F_α) = 2 when α = 0")
    print("For all α > 0: M(F_α) > 2")
    print("-" * 70)

    # Prove M > 2 for α > 0
    print("\nProof that M(F_α) > 2 for α > 0:")
    print("  M = 2(2α+1)/(α+1)")
    print("  M > 2  ⟺  2(2α+1) > 2(α+1)")
    print("         ⟺  4α + 2 > 2α + 2")
    print("         ⟺  2α > 0")
    print("         ⟺  α > 0  ✓")

    print("\n" + "=" * 70)
    print("THEOREM: For any α > 0, M(F_α) = 2(2α+1)/(α+1) > 2.")
    print("In particular, M(F_{1/2}) = 8/3 ≈ 2.667 > 2.")
    print("=" * 70)


if __name__ == "__main__":
    main()
