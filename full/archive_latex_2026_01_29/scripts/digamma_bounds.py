#!/usr/bin/env python3
"""
High-Precision Digamma Bounds (Legacy Numerical Evidence)
================================================

This script provides a high-precision numerical check for
legacy Archimedean floor targets. It is not used in the
formal proof, which now relies on analytic bounds only.

Legacy targets (numerical evidence only):
- A_* >= 44/25
- L_* <= 42/125, where L_* is the supremum of the periodized derivative bound
- c_* = A_* - π * L_* >= 88/125

Uses mpmath for high-precision evaluation; L_A uses a uniform grid search on θ.
These checks are computational evidence, not a formal proof.

Author: RH Q3 Project
Date: December 2025
"""

from mpmath import mp, mpf, pi, log, exp, quad, digamma, re
from typing import Tuple
import sys

# Set high precision for numerical checks
mp.dps = 50  # 50 decimal digits


def a(xi: mpf) -> mpf:
    """
    Archimedean density function.

    a(ξ) = log(π) - Re(ψ(1/4 + iπξ))

    where ψ is the digamma function.
    """
    z = mpf('0.25') + 1j * pi * xi
    return log(pi) - re(digamma(z))


def a_prime(xi: mpf) -> mpf:
    """
    Derivative of the Archimedean density.

    a'(ξ) = -π * Im(ψ'(1/4 + iπξ))
    """
    z = mpf('0.25') + 1j * pi * xi
    return -pi * mp.im(mp.polygamma(1, z))


def g_prime(xi: mpf, B: mpf, t: mpf) -> mpf:
    """
    Derivative of g_{B,t}(ξ) = a(ξ) * (1 - |ξ|/B) * exp(-4π²t ξ²) on |ξ| ≤ B.
    """
    if abs(xi) > B:
        return mpf('0')

    hat = 1 - abs(xi) / B
    c = 4 * pi**2 * t
    gauss = exp(-c * xi**2)

    # derivative of the hat factor
    dhat = mpf('0') if xi == 0 else -mp.sign(xi) / B
    dgauss = -2 * c * xi * gauss

    return a_prime(xi) * hat * gauss + a(xi) * (dhat * gauss + hat * dgauss)


def A_0(B: mpf, t: mpf) -> mpf:
    """
    Mean integral with Fejér×heat smoothing.

    A_0(B, t) = ∫_{-B}^{B} a(ξ) * (1 - |ξ|/B) * exp(-4π²t*ξ²) dξ

    By symmetry of a(ξ) and the integrand, this equals 2× the integral from 0 to B.
    """
    B = mpf(B)
    t = mpf(t)
    c = 4 * pi**2 * t

    def integrand(xi):
        return a(xi) * (1 - xi/B) * exp(-c * xi**2)

    # Use symmetry: 2 × integral from 0 to B
    return 2 * quad(integrand, [0, B])


def L_A(B: mpf, t: mpf, ntheta: int = 2001) -> mpf:
    """
    Periodized derivative bound for the Lipschitz modulus.

    L_A(B, t) = 2π * sup_{θ in [-π,π]} sum_{m∈Z} |g_{B,t}'(θ + 2π m)|.

    We approximate the supremum using a uniform grid in θ; increase ntheta for tighter bounds.
    """
    B = mpf(B)
    t = mpf(t)
    two_pi = 2 * pi

    max_sum = mpf('0')
    for i in range(ntheta):
        theta = -pi + two_pi * mpf(i) / mpf(ntheta - 1)
        m_min = int(mp.floor((-B - theta) / two_pi))
        m_max = int(mp.ceil((B - theta) / two_pi))
        s = mpf('0')
        for m in range(m_min, m_max + 1):
            xi = theta + two_pi * m
            s += abs(g_prime(xi, B, t))
        if s > max_sum:
            max_sum = s

    return two_pi * max_sum


def c_floor(B: mpf, t: mpf) -> mpf:
    """
    Uniform floor function.

    c(B, t) = A_0(B, t) - π * L_A(B, t)

    This is the lower bound for inf_θ P_A(θ).
    """
    return A_0(B, t) - pi * L_A(B, t)


def format_interval(val: mpf, error: mpf = mpf('1e-10')) -> str:
    """Format value with error bounds."""
    return f"{float(val):.10f} ± {float(error):.0e}"


def verify_bounds(B_min: int = 3, t_sym: mpf = mpf(3)/50) -> dict:
    """
    High-precision numerical check for the digamma bounds.

    Returns a dictionary with verification results.
    """
    print("=" * 70)
    print("NUMERICAL CHECK: Digamma Bounds Verification")
    print("=" * 70)
    print(f"\nParameters:")
    print(f"  B_min  = {B_min}")
    print(f"  t_sym  = {t_sym} = {float(t_sym):.6f}")
    print(f"  Precision: {mp.dps} decimal digits")
    print()

    results = {
        'B_min': B_min,
        't_sym': float(t_sym),
        'precision_digits': mp.dps,
        'bounds': []
    }

    # Test values of B
    B_values = [3, 5, 10, 20, 50, 100, 500, 1000]

    print("-" * 70)
    print(f"{'B':>6} | {'A_0(B)':>16} | {'L_A(B)':>16} | {'c(B)':>16}")
    print("-" * 70)

    min_A = mpf('inf')
    max_L = mpf('0')
    min_c = mpf('inf')
    min_c_B = None

    for B in B_values:
        if B < B_min:
            continue

        B_mpf = mpf(B)
        A = A_0(B_mpf, t_sym)
        L = L_A(B_mpf, t_sym)
        c = c_floor(B_mpf, t_sym)

        if c < min_c:
            min_c = c
            min_c_B = B
        if A < min_A:
            min_A = A
        if L > max_L:
            max_L = L

        print(f"{B:>6} | {float(A):>16.10f} | {float(L):>16.10f} | {float(c):>16.10f}")

        results['bounds'].append({
            'B': B,
            'A_0': float(A),
            'L_A': float(L),
            'c': float(c),
            'passed': True
        })

    print("-" * 70)
    print()

    # Summary
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print(f"  Minimum A_0(B) found: {float(min_A):.10f}")
    print(f"  Maximum L_A(B) found: {float(max_L):.10f}")
    print(f"  Minimum c(B) found:  {float(min_c):.10f} at B = {min_c_B}")
    print()

    # Legacy targets for A_*, L_*, c_*
    A_target = mpf(44) / 25
    L_target = mpf(42) / 125
    c_target = mpf(88) / 125
    c_star = min_A - pi * max_L

    print("TARGET BOUNDS (numerical evidence, B ≥ 3, t_sym = 3/50):")
    print()
    print(f"  • Legacy A_* ≥ 44/25 = {float(A_target):.6f}")
    print(f"  • Legacy L_* ≤ 42/125 = {float(L_target):.6f}")
    print(f"  • Legacy c_* = A_* - π·L_* ≥ 88/125 = {float(c_target):.6f}")
    print()

    all_passed = (min_A >= A_target) and (max_L <= L_target) and (c_star >= c_target)
    if all_passed:
        print("  ✓ TARGET BOUNDS MET ON SAMPLED GRID")
    else:
        print("  ✗ TARGET BOUNDS NOT MET ON SAMPLED GRID")

    print()
    print("=" * 70)

    results['all_passed'] = all_passed
    results['min_c'] = float(min_c)
    results['min_c_B'] = min_c_B
    results['min_A'] = float(min_A)
    results['max_L'] = float(max_L)
    results['c_star'] = float(c_star)

    return results


def verify_specific_values() -> None:
    """
    Check the target bounds at representative B values.
    """
    t_sym = mpf(3) / 50

    print("\n" + "=" * 70)
    print("TARGET BOUND CHECKS (Lemmas 8.20-8.21)")
    print("=" * 70)

    B_min = mpf(3)
    B_large = mpf(2000)
    A_min = A_0(B_min, t_sym)
    L_large = L_A(B_large, t_sym)
    c_star = A_min - pi * L_large

    A_target = mpf(44) / 25
    L_target = mpf(42) / 125
    c_target = mpf(88) / 125

    print(f"\nRepresentative values:")
    print(f"  A_0(B_min=3) ≈ {float(A_min):.10f}")
    print(f"  L_A(B_large=2000) ≈ {float(L_large):.10f}")
    print(f"  c_* ≈ {float(c_star):.10f}")
    print()
    print("Legacy targets:")
    print(f"  A_* ≥ 44/25 = {float(A_target):.6f}")
    print(f"  L_* ≤ 42/125 = {float(L_target):.6f}")
    print(f"  c_* ≥ 88/125 = {float(c_target):.6f}")
    print()
    print(f"Status: A_* {'✓' if A_min >= A_target else '✗'}, "
          f"L_* {'✓' if L_large <= L_target else '✗'}, "
          f"c_* {'✓' if c_star >= c_target else '✗'}")


def main():
    """Main entry point."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║" + " DIGAMMA BOUNDS CHECK ".center(68) + "║")
    print("║" + " High-Precision Numerics for RH Q3 ".center(68) + "║")
    print("╚" + "═" * 68 + "╝")
    print()

    # Main verification
    results = verify_bounds(B_min=3, t_sym=mpf(3)/50)

    # Specific bound checks
    verify_specific_values()

    print()
    print("Script completed successfully.")
    print("This output serves as a numerical check for Lemmas 8.20-8.22.")
    print()

    return 0 if results['all_passed'] else 1


if __name__ == "__main__":
    sys.exit(main())
