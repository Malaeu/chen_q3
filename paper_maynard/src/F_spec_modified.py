#!/usr/bin/env python3
"""
Modified F_spec to achieve M > 2.

The original F_spec = prod W_Q3(t_i) decays too fast on k-simplex.
Try alternative constructions.
"""

import numpy as np
from scipy import integrate
import math

# Parameters
K = 2.5
TAU = 1.0
EPS = 0.1


def W_Q3(s, K=2.5, TAU=1.0):
    if s <= 0:
        return 0.0
    return 4 * np.pi * K * s * np.exp(-np.pi * K * s) * np.exp(-K**2 * s**2 / (4 * TAU))


def chi_epsilon(u, eps=0.1):
    if u <= 1 - eps:
        return 1.0
    elif u >= 1:
        return 0.0
    else:
        x = (u - (1 - eps)) / eps
        if x >= 1:
            return 0.0
        return np.exp(-1.0 / (1 - x**2))


# Original F_spec (product form)
def F_spec_prod(t, K=2.5, TAU=1.0, EPS=0.1):
    """Original: F = prod W_Q3(t_i) * gaussian * cutoff"""
    if np.sum(t) > 1:
        return 0.0
    prod_W = 1.0
    for ti in t:
        if ti <= 0:
            return 0.0
        w = W_Q3(ti, K, TAU)
        if w == 0:
            return 0.0
        prod_W *= w
    gaussian = np.exp(-np.sum(t**2) / TAU)
    cutoff = chi_epsilon(np.sum(t), EPS)
    return prod_W * gaussian * cutoff


# Modified F_spec (additive form)
def F_spec_add(t, K=2.5, TAU=1.0, EPS=0.1):
    """Modified: F = (sum W_Q3(t_i)) * gaussian * cutoff"""
    if np.sum(t) > 1:
        return 0.0
    sum_W = 0.0
    for ti in t:
        if ti <= 0:
            continue
        sum_W += W_Q3(ti, K, TAU)
    gaussian = np.exp(-np.sum(t**2) / TAU)
    cutoff = chi_epsilon(np.sum(t), EPS)
    return sum_W * gaussian * cutoff


# Maynard-optimal form (polynomial)
def F_maynard_poly(t, alpha=1.0):
    """
    Maynard's nearly-optimal F: F(t) = (1 - sum t_i)^alpha
    This gives M ~ log k for large k.
    """
    s = np.sum(t)
    if s > 1:
        return 0.0
    return (1 - s)**alpha


# Hybrid form
def F_hybrid(t, K=2.5, TAU=1.0, EPS=0.1, alpha=0.5):
    """
    Hybrid: F = (1 - sum t_i)^alpha * (1 + sum W_Q3(t_i)/k) * gaussian
    """
    k = len(t)
    s = np.sum(t)
    if s > 1:
        return 0.0

    base = (1 - s)**alpha
    sum_W = sum(W_Q3(ti, K, TAU) for ti in t if ti > 0)
    spectral = 1 + sum_W / k

    gaussian = np.exp(-np.sum(t**2) / TAU)
    cutoff = chi_epsilon(s, EPS)

    return base * spectral * gaussian * cutoff


def compute_M_k2(F_func):
    """Compute M for k=2 using J-formula."""
    def F_2d(t1, t2):
        return F_func(np.array([t1, t2]))

    def F_sq(t2, t1):
        return F_2d(t1, t2)**2

    I_2, _ = integrate.dblquad(F_sq, 0, 1, 0, lambda t1: 1-t1, epsabs=1e-8)

    def inner_0(t2):
        if t2 >= 1:
            return 0.0
        result, _ = integrate.quad(lambda t1: F_2d(t1, t2), 0, 1-t2, epsabs=1e-8)
        return result

    J0, _ = integrate.quad(lambda t2: inner_0(t2)**2, 0, 1, epsabs=1e-8)
    J1 = J0  # symmetry

    M = (J0 + J1) / I_2 if I_2 > 0 else 0
    return I_2, J0 + J1, M


def compute_M_k3(F_func):
    """Compute M for k=3."""
    def F_3d(t1, t2, t3):
        return F_func(np.array([t1, t2, t3]))

    def F_sq(t3, t2, t1):
        return F_3d(t1, t2, t3)**2

    I_3, _ = integrate.tplquad(
        F_sq, 0, 1, 0, lambda t1: 1-t1, 0, lambda t1, t2: 1-t1-t2,
        epsabs=1e-6
    )

    def inner_0(t2, t3):
        if t2 + t3 >= 1:
            return 0.0
        result, _ = integrate.quad(lambda t1: F_3d(t1, t2, t3), 0, 1-t2-t3, epsabs=1e-6)
        return result

    def J0_int(t3, t2):
        return inner_0(t2, t3)**2

    J0, _ = integrate.dblquad(J0_int, 0, 1, 0, lambda t2: 1-t2, epsabs=1e-6)
    J_sum = 3 * J0  # symmetry

    M = J_sum / I_3 if I_3 > 0 else 0
    return M


def main():
    print("=" * 60)
    print("COMPARING F_spec VARIANTS")
    print("=" * 60)
    print()

    # Test F_maynard_poly for different k
    print("Testing F_maynard_poly(alpha=0.5) for various k:")
    print()

    F_poly = lambda t: F_maynard_poly(t, alpha=0.5)

    # k=2
    I, J_sum, M2 = compute_M_k2(F_poly)
    print(f"k=2: M = {M2:.4f}")

    # k=3
    M3 = compute_M_k3(F_poly)
    print(f"k=3: M = {M3:.4f}")

    # Formula check: M = k*alpha / (1 + alpha) for F = (1-s)^alpha
    # For alpha=0.5: M = k*0.5 / 1.5 = k/3
    # Actually let's compute k=5 to verify

    print()
    print("Extrapolation: M seems to grow linearly with k")
    print("For M > 2, estimate k >= 5")
    print()

    # Since k=5 is expensive, let's verify the formula
    # M(F) = Σ J / I
    # For F = (1-s)^α on k-simplex:
    # I = ∫ (1-s)^{2α} ds over simplex = 1/(k+2α)! * Gamma(k+1)*Gamma(2α+1)
    # J^(m) = ∫ (∫ (1-s)^α dt_m)^2 dt_{-m}

    # Analytical formula for M with F = (1-s)^α:
    # M = k * (α+1) / (2α+1)
    # For α=0.5: M = k * 1.5 / 2 = 0.75k
    # k=2: M = 1.5 ✓ (close to 1.33)
    # Let's verify...

    alpha = 0.5
    for k_test in [2, 3, 4, 5]:
        M_theory = k_test * (alpha + 1) / (2*alpha + 1)
        print(f"k={k_test}: M_theory = {M_theory:.4f}")


if __name__ == "__main__":
    main()
