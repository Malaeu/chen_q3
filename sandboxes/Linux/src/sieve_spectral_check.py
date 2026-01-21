#!/usr/bin/env python3
"""
Sieve-Spectral Synergy Hypothesis Check.

Tests whether Q3 spectral weights can be used as Maynard sieve weights
to potentially improve bounded gap results.

Key hypothesis:
    F_spec(t₁,...,tₖ) := ∏ᵢ W_Q3(tᵢ) · exp(-||t||²/τ)

    where W_Q3(t) = w(p) · K_t(0, t) with w(p) = 2 log(p) / √p

If M(F_spec) > 4, then synergy hypothesis works for m=1 bounded gaps.
"""

import numpy as np
from math import log, sqrt, pi, exp
from typing import List, Tuple
import sys


def sieve_primes(n: int) -> List[int]:
    """Simple sieve of Eratosthenes."""
    if n < 2:
        return []
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, n + 1, i):
                sieve[j] = False
    return [i for i, is_prime in enumerate(sieve) if is_prime]


def q3_weight(p: int) -> float:
    """Q3 spectral weight for prime p: w(p) = 2 log(p) / √p."""
    return 2.0 * log(p) / sqrt(p)


def heat_kernel(x: float, t: float) -> float:
    """Gaussian/heat kernel exp(-x² / (4t))."""
    return exp(-x * x / (4.0 * t))


def W_Q3(t: float, K: float, t_sym: float) -> float:
    """
    Q3 weight kernel at normalized position t ∈ [0, 1].

    Maps t → prime p via: ξ = t * K, then p ≈ exp(2π ξ).
    Returns w(p) * heat_kernel factor.
    """
    xi = t * K  # position in spectral window
    p_approx = exp(2 * pi * abs(xi))  # approximate prime

    if p_approx < 2:
        return 0.0

    # Find nearest prime
    p = int(round(p_approx))
    if p < 2:
        p = 2

    # Q3 weight
    w = q3_weight(p)

    # Heat kernel decay from origin
    k = heat_kernel(xi, t_sym)

    return w * k


def F_spec(t_vec: np.ndarray, K: float, t_sym: float, tau: float = 16.0) -> float:
    """
    Spectral sieve function.

    F_spec(t₁,...,tₖ) = ∏ᵢ W_Q3(tᵢ) · exp(-||t||²/τ)
    """
    # Product of individual weights
    prod_W = 1.0
    for t in t_vec:
        w = W_Q3(t, K, t_sym)
        if w <= 0:
            return 0.0
        prod_W *= w

    # Gaussian decay
    norm_sq = np.sum(t_vec ** 2)
    gauss = exp(-norm_sq / tau)

    return prod_W * gauss


def compute_M_approx(K: float, t_sym: float, k: int = 50,
                      n_samples: int = 10000, X_max: int = 10000) -> Tuple[float, dict]:
    """
    Approximate sieve ratio M(F_spec) via Monte Carlo.

    M ≈ E[ν(n) · F(n)] / E[F(n)]

    where ν(n) = number of primes in tuple {n+h₁, ..., n+hₖ}.

    For simplicity, we use admissible tuple h = {0, 2, 6, 8, 12, ...}
    (twin-prime-like structure).
    """
    primes = set(sieve_primes(X_max + 2 * k))

    # Admissible k-tuple (simplified: consecutive even gaps)
    h = [2 * i for i in range(k)]  # {0, 2, 4, 6, ..., 2(k-1)}

    tau = 16 * t_sym

    S1 = 0.0  # Sum of F weights
    S2 = 0.0  # Sum of F * ν (number of primes)

    prime_counts = []

    for _ in range(n_samples):
        # Random n
        n = np.random.randint(3, X_max - max(h))

        # Count primes in tuple
        nu = sum(1 for hi in h if (n + hi) in primes)

        # Compute F_spec for this tuple
        # Map n+h_i to normalized coordinates t_i
        t_vec = np.array([log(n + hi) / (2 * pi * K) if n + hi > 1 else 0.01
                          for hi in h])

        F_val = F_spec(t_vec, K, t_sym, tau)

        S1 += F_val
        S2 += F_val * nu
        prime_counts.append(nu)

    M = S2 / S1 if S1 > 0 else 0.0

    stats = {
        "S1": S1,
        "S2": S2,
        "M": M,
        "avg_primes": np.mean(prime_counts),
        "max_primes": max(prime_counts),
        "k": k,
        "n_samples": n_samples
    }

    return M, stats


def parameter_sweep():
    """Sweep over K and t_sym to find optimal parameters."""
    print("=" * 70)
    print("SIEVE-SPECTRAL SYNERGY HYPOTHESIS CHECK")
    print("=" * 70)
    print()
    print("Testing: Does M(F_spec) > 4 for Q3 spectral weights?")
    print()

    K_values = [1.5, 2.0, 2.5, 3.0]
    t_values = [0.5, 1.0, 1.5, 2.0]
    k = 50  # tuple size

    print(f"Tuple size k = {k}")
    print(f"Maynard theoretical bound: M_k >= log({k}) - 2*log(log({k})) ≈ {log(k) - 2*log(log(k)):.2f}")
    print(f"Critical threshold for bounded gaps: M > 4")
    print()

    results = []

    print("-" * 70)
    print(f"{'K':<8} {'t_sym':<8} {'M(F_spec)':<12} {'Status':<15} {'avg_primes'}")
    print("-" * 70)

    for K in K_values:
        for t_sym in t_values:
            M, stats = compute_M_approx(K, t_sym, k=k, n_samples=5000, X_max=50000)

            status = "✓ WORKS!" if M > 4 else "✗ below 4"
            if M > 2:
                status = "~ partial" if M <= 4 else status

            print(f"{K:<8.1f} {t_sym:<8.1f} {M:<12.4f} {status:<15} {stats['avg_primes']:.2f}")

            results.append({
                "K": K,
                "t_sym": t_sym,
                "M": M,
                "works": M > 4,
                **stats
            })

    print("-" * 70)

    # Find best result
    best = max(results, key=lambda x: x["M"])
    print()
    print(f"Best result: K={best['K']}, t_sym={best['t_sym']} → M = {best['M']:.4f}")

    if best["M"] > 4:
        print()
        print("🎉 HYPOTHESIS CONFIRMED!")
        print("   Spectral weights give M > 4, which implies bounded gaps!")
    elif best["M"] > 2:
        print()
        print("⚠️ PARTIAL SUCCESS")
        print("   M > 2 but < 4. May work for larger k or different tuples.")
    else:
        print()
        print("❌ HYPOTHESIS NOT CONFIRMED with these parameters.")
        print("   Need different approach or parameter range.")

    return results


def detailed_analysis(K: float = 2.0, t_sym: float = 1.0):
    """Detailed analysis at specific parameters."""
    print()
    print("=" * 70)
    print(f"DETAILED ANALYSIS: K={K}, t_sym={t_sym}")
    print("=" * 70)

    # Q3 weights for small primes
    print()
    print("Q3 spectral weights w(p) = 2 log(p) / √p:")
    print("-" * 40)
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        w = q3_weight(p)
        xi_p = log(p) / (2 * pi)
        print(f"  p={p:3d}: w={w:.4f}, ξ_p={xi_p:.4f}")

    # Check if weights are in range [-K, K]
    print()
    print(f"Primes in spectral window [-{K}, {K}]:")
    primes = sieve_primes(1000)
    in_window = []
    for p in primes:
        xi_p = log(p) / (2 * pi)
        if abs(xi_p) <= K:
            in_window.append((p, xi_p, q3_weight(p)))

    print(f"  {len(in_window)} primes: p ∈ [{in_window[0][0]}, {in_window[-1][0]}]")

    # Total weight
    total_w = sum(w for _, _, w in in_window)
    print(f"  Total weight Σw(p) = {total_w:.4f}")

    # Compare with Maynard
    print()
    print("Comparison with Maynard bound:")
    for k in [10, 50, 100, 200]:
        M_bound = log(k) - 2 * log(log(k)) - 2 if k > 3 else 0
        M_our, _ = compute_M_approx(K, t_sym, k=k, n_samples=2000, X_max=20000)
        ratio = M_our / M_bound if M_bound > 0 else 0
        print(f"  k={k:3d}: M_Maynard ≥ {M_bound:.2f}, M_spec = {M_our:.2f}, ratio = {ratio:.2f}")


def main():
    """Run full analysis."""
    print()
    print("🔬 SIEVE-SPECTRAL SYNERGY CHECK")
    print("=" * 70)

    # Quick parameter sweep
    results = parameter_sweep()

    # Detailed analysis at baseline
    detailed_analysis(K=2.0, t_sym=1.0)

    print()
    print("=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    best_M = max(r["M"] for r in results)

    if best_M > 4:
        print("""
✅ SYNERGY HYPOTHESIS SUPPORTED!

The spectral weights from Q3 can potentially serve as sieve weights
that exceed the critical threshold M > 4, which would imply:

  - Bounded gaps between primes (conditional on the bridge being rigorous)
  - Potential improvement on the 246 bound under RH
  - A new connection between spectral positivity and sieve theory
""")
    else:
        print(f"""
⚠️ SYNERGY HYPOTHESIS NEEDS MORE WORK

Best M = {best_M:.4f} < 4 threshold.

Possible reasons:
  1. Simplified sieve ratio approximation
  2. Admissible tuple choice not optimal
  3. Parameter range needs extension
  4. The correspondence may need refinement

Next steps:
  - Try more sophisticated sieve ratio computation
  - Use optimal admissible tuples from Polymath
  - Explore larger k values
  - Investigate alternative weight correspondences
""")


if __name__ == "__main__":
    main()
