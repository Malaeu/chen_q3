#!/usr/bin/env python3
"""
CORRECT Analytic derivation of M(F_α) for polynomial sieve functions.

F_α(t) = (1 - Σt_i)^α on Δ_k

Using Dirichlet integral formula:
∫_{Δ_n} (1-Σt)^{β} dt = Γ(β+1) / Γ(n + β + 1)

CORRECT FORMULA:
M(F_α, k) = 2k(2α+1) / [(α+1)(k + 2α + 1)]
"""

from math import gamma, factorial
from fractions import Fraction
import numpy as np


def I_k_analytic(alpha: float, k: int) -> float:
    """
    I_k(F_α) = ∫_{Δ_k} (1-Σt)^{2α} dt = Γ(2α+1) / Γ(k + 2α + 1)
    """
    return gamma(2*alpha + 1) / gamma(k + 2*alpha + 1)


def J_k_analytic(alpha: float, k: int) -> float:
    """
    J_k^{(m)}(F_α) = (1/(α+1)^2) · Γ(2α+3) / Γ(k + 2α + 2)

    Derivation:
    Inner integral: ∫_0^{1-s} (1-s-t)^α dt = (1-s)^{α+1}/(α+1)
    J = (1/(α+1)^2) · ∫_{Δ_{k-1}} (1-s)^{2α+2} ds
      = (1/(α+1)^2) · Γ(2α+3) / Γ((k-1) + (2α+2) + 1)
      = (1/(α+1)^2) · Γ(2α+3) / Γ(k + 2α + 2)
    """
    return gamma(2*alpha + 3) / ((alpha + 1)**2 * gamma(k + 2*alpha + 2))


def M_analytic(alpha: float, k: int) -> float:
    """
    M(F_α, k) = k · J_k / I_k

    Simplified form:
    M = k · [Γ(2α+3) / ((α+1)² · Γ(k+2α+2))] / [Γ(2α+1) / Γ(k+2α+1)]
      = k · Γ(2α+3) · Γ(k+2α+1) / [(α+1)² · Γ(2α+1) · Γ(k+2α+2)]

    Using:
    - Γ(2α+3) = (2α+2)(2α+1)Γ(2α+1)
    - Γ(k+2α+1)/Γ(k+2α+2) = 1/(k+2α+1)

    M = k · (2α+2)(2α+1) / [(α+1)² · (k+2α+1)]
      = k · 2(α+1)(2α+1) / [(α+1)² · (k+2α+1)]
      = 2k(2α+1) / [(α+1) · (k+2α+1)]
    """
    return 2 * k * (2*alpha + 1) / ((alpha + 1) * (k + 2*alpha + 1))


def M_exact(alpha_num: int, alpha_den: int, k: int) -> Fraction:
    """
    Exact rational computation of M(F_α, k) for α = alpha_num/alpha_den.

    M = 2k(2α+1) / [(α+1)(k+2α+1)]

    For α = p/q:
    2α + 1 = (2p + q)/q
    α + 1 = (p + q)/q
    k + 2α + 1 = k + (2p + q)/q = (kq + 2p + q)/q

    M = 2k · (2p+q)/q / [(p+q)/q · (kq+2p+q)/q]
      = 2k(2p+q)q / [(p+q)(kq+2p+q)]
    """
    p, q = alpha_num, alpha_den
    numerator = 2 * k * (2*p + q) * q
    denominator = (p + q) * (k*q + 2*p + q)
    return Fraction(numerator, denominator)


def verify_M_mc(alpha: float, k: int, n_samples: int = 200000) -> dict:
    """Monte Carlo verification of M formula."""
    rng = np.random.default_rng(42)

    # Sample from Δ_k using Dirichlet(1,...,1,1)
    # This gives uniform distribution on simplex
    dirichlet_alpha = np.ones(k + 1)
    samples = rng.dirichlet(dirichlet_alpha, size=n_samples)
    t = samples[:, :k]  # First k coordinates

    s = t.sum(axis=1)  # Σt_i

    # I_k = ∫ (1-s)^{2α} dt / Vol(Δ_k)
    # But with Dirichlet sampling, we get E[(1-s)^{2α}] directly
    F_squared = (1 - s) ** (2 * alpha)
    I_k_mc = F_squared.mean()

    # For J_k^{(m)}, sample from Δ_{k-1}
    dirichlet_alpha_km1 = np.ones(k)
    samples_km1 = rng.dirichlet(dirichlet_alpha_km1, size=n_samples)
    t_km1 = samples_km1[:, :k-1]  # First k-1 coordinates

    s_km1 = t_km1.sum(axis=1)
    inner_sq = ((1 - s_km1) ** (alpha + 1) / (alpha + 1)) ** 2
    J_k_mc = inner_sq.mean()

    M_mc = k * J_k_mc / I_k_mc

    return {
        'I_k_mc': I_k_mc,
        'I_k_analytic': I_k_analytic(alpha, k) * factorial(k),  # Adjust for Dirichlet
        'J_k_mc': J_k_mc,
        'J_k_analytic': J_k_analytic(alpha, k) * factorial(k-1),
        'M_mc': M_mc,
        'M_analytic': M_analytic(alpha, k)
    }


def main():
    print("=" * 70)
    print("CORRECT ANALYTIC FORMULA: M(F_α, k) = 2k(2α+1) / [(α+1)(k+2α+1)]")
    print("=" * 70)

    alpha = 0.5  # α = 1/2

    print(f"\nFor α = 1/2:")
    print(f"  M(F_{{1/2}}, k) = 2k·2 / [1.5·(k+2)]")
    print(f"                 = 4k / [1.5(k+2)]")
    print(f"                 = 8k / [3(k+2)]")

    print("\n" + "-" * 70)
    print("Table: M(F_{1/2}, k) for various k")
    print("-" * 70)
    print(f"{'k':>5} {'M_exact':>15} {'M_float':>12} {'M > 2?':>10}")
    print("-" * 45)

    for k in [2, 3, 4, 5, 6, 7, 8, 10, 20, 50, 100]:
        M_ex = M_exact(1, 2, k)
        M_fl = M_analytic(alpha, k)
        check = "YES ✓" if M_fl > 2 else "no"
        print(f"{k:>5} {str(M_ex):>15} {M_fl:>12.6f} {check:>10}")

    print("\n" + "-" * 70)
    print("Finding critical k where M = 2 for α = 1/2:")
    print("-" * 70)
    print("  M = 8k / [3(k+2)] = 2")
    print("  8k = 6(k+2)")
    print("  8k = 6k + 12")
    print("  2k = 12")
    print("  k = 6")
    print("\n  Therefore: M > 2  ⟺  k > 6")
    print("  For k ≥ 7: M(F_{1/2}, k) > 2  ✓")

    # Verify specific case k=7
    print("\n" + "=" * 70)
    print("RIGOROUS PROOF for k = 7, α = 1/2:")
    print("=" * 70)

    k = 7
    M_ex = M_exact(1, 2, k)
    print(f"\n  M(F_{{1/2}}, 7) = 8·7 / [3·(7+2)]")
    print(f"                 = 56 / 27")
    print(f"                 = {M_ex}")
    print(f"                 = {float(M_ex):.10f}")
    print(f"\n  Since 56/27 = 2 + 2/27 > 2:")
    print(f"  M(F_{{1/2}}, 7) > 2  ✓")

    # Monte Carlo verification
    print("\n" + "-" * 70)
    print("Monte Carlo verification:")
    print("-" * 70)
    result = verify_M_mc(alpha, k, n_samples=500000)
    print(f"  M_analytic = {result['M_analytic']:.6f}")
    print(f"  M_mc       = {result['M_mc']:.6f}")
    print(f"  Agreement: {abs(result['M_mc'] - result['M_analytic']) / result['M_analytic'] * 100:.2f}% error")

    # General condition for M > 2
    print("\n" + "=" * 70)
    print("THEOREM: For F_α(t) = (1 - Σt_i)^α on Δ_k:")
    print("=" * 70)
    print("""
    M(F_α, k) = 2k(2α+1) / [(α+1)(k + 2α + 1)]

    M > 2  ⟺  2k(2α+1) > 2(α+1)(k + 2α + 1)
           ⟺  k(2α+1) > (α+1)(k + 2α + 1)
           ⟺  k(2α+1) > (α+1)k + (α+1)(2α+1)
           ⟺  k[(2α+1) - (α+1)] > (α+1)(2α+1)
           ⟺  kα > (α+1)(2α+1)
           ⟺  k > (α+1)(2α+1)/α
           ⟺  k > (2α² + 3α + 1)/α
           ⟺  k > 2α + 3 + 1/α

    For α = 1/2:
    k > 2(1/2) + 3 + 2 = 1 + 3 + 2 = 6

    Therefore: M(F_{1/2}, k) > 2 for k ≥ 7.
    """)

    print("=" * 70)
    print("COROLLARY: Taking k = 7 and α = 1/2:")
    print("  M(F_{1/2}, 7) = 56/27 > 2")
    print("  By Maynard's theorem, lim inf(p_{n+1} - p_n) < ∞.")
    print("=" * 70)


if __name__ == "__main__":
    main()
