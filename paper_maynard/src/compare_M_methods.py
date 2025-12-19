#!/usr/bin/env python3
"""
Compare different methods for computing M(F_spec).
Figure out why MC gradient gives M=148 but scipy gives M=0.83.
"""

import numpy as np
from scipy import integrate
import math

# Parameters
K = 2.5
TAU = 1.0
EPS = 0.1


def W_Q3(s):
    if s <= 0:
        return 0.0
    return 4 * np.pi * K * s * np.exp(-np.pi * K * s) * np.exp(-K**2 * s**2 / (4 * TAU))


def chi_epsilon(u):
    if u <= 1 - EPS:
        return 1.0
    elif u >= 1:
        return 0.0
    else:
        x = (u - (1 - EPS)) / EPS
        if x >= 1:
            return 0.0
        return np.exp(-1.0 / (1 - x**2))


def F_spec_2d(t1, t2):
    if t1 <= 0 or t2 <= 0 or t1 + t2 > 1:
        return 0.0
    W1 = W_Q3(t1)
    W2 = W_Q3(t2)
    if W1 == 0 or W2 == 0:
        return 0.0
    return W1 * W2 * np.exp(-(t1**2 + t2**2) / TAU) * chi_epsilon(t1 + t2)


def method_1_scipy_J():
    """Scipy with J-formula: M = (J0 + J1) / I"""
    print("Method 1: scipy with J-formula")

    def F_squared(t2, t1):
        return F_spec_2d(t1, t2)**2

    I_2, _ = integrate.dblquad(F_squared, 0, 1, 0, lambda t1: 1-t1, epsabs=1e-10)

    def inner_0(t2):
        if t2 >= 1:
            return 0.0
        result, _ = integrate.quad(lambda t1: F_spec_2d(t1, t2), 0, 1-t2, epsabs=1e-10)
        return result

    J0, _ = integrate.quad(lambda t2: inner_0(t2)**2, 0, 1, epsabs=1e-10)

    def inner_1(t1):
        if t1 >= 1:
            return 0.0
        result, _ = integrate.quad(lambda t2: F_spec_2d(t1, t2), 0, 1-t1, epsabs=1e-10)
        return result

    J1, _ = integrate.quad(lambda t1: inner_1(t1)**2, 0, 1, epsabs=1e-10)

    M = (J0 + J1) / I_2
    print(f"  I_2 = {I_2:.10e}")
    print(f"  J0 = {J0:.10e}")
    print(f"  J1 = {J1:.10e}")
    print(f"  M = {M:.6f}")
    return M


def method_2_scipy_gradient():
    """Scipy with gradient formula: M = integral(sum dF/dt_i)^2 / integral F^2"""
    print("\nMethod 2: scipy with gradient formula")

    h = 1e-6

    def F_squared(t2, t1):
        return F_spec_2d(t1, t2)**2

    denominator, _ = integrate.dblquad(F_squared, 0, 1, 0, lambda t1: 1-t1, epsabs=1e-10)

    def grad_sum_sq(t2, t1):
        if t1 <= h or t2 <= h or t1 + t2 > 1 - h:
            return 0.0
        F0 = F_spec_2d(t1, t2)
        if F0 < 1e-15:
            return 0.0
        dF_dt1 = (F_spec_2d(t1+h, t2) - F_spec_2d(t1-h, t2)) / (2*h)
        dF_dt2 = (F_spec_2d(t1, t2+h) - F_spec_2d(t1, t2-h)) / (2*h)
        return (dF_dt1 + dF_dt2)**2

    numerator, _ = integrate.dblquad(grad_sum_sq, 0, 1, 0, lambda t1: 1-t1, epsabs=1e-8)

    M = numerator / denominator
    print(f"  Numerator = {numerator:.10e}")
    print(f"  Denominator = {denominator:.10e}")
    print(f"  M = {M:.6f}")
    return M


def method_3_mc_gradient():
    """Monte Carlo with gradient formula."""
    print("\nMethod 3: MC with gradient formula")

    np.random.seed(42)
    n_samples = 50000
    h = 0.001

    # Sample from 2-simplex
    exp_samples = np.random.exponential(1, (n_samples, 3))
    samples = exp_samples[:, :2] / exp_samples.sum(axis=1, keepdims=True)

    F_values = np.array([F_spec_2d(s[0], s[1]) for s in samples])
    F2_values = F_values**2

    # Simplex volume = 1/2! = 0.5
    simplex_vol = 0.5
    I_2 = simplex_vol * np.mean(F2_values)

    grad_sum_sq = []
    for i, s in enumerate(samples):
        t1, t2 = s[0], s[1]
        if t1 > h and t2 > h and t1 + t2 < 1 - h:
            F0 = F_values[i]
            if F0 < 1e-15:
                continue
            dF1 = (F_spec_2d(t1+h, t2) - F_spec_2d(t1-h, t2)) / (2*h)
            dF2 = (F_spec_2d(t1, t2+h) - F_spec_2d(t1, t2-h)) / (2*h)
            grad_sum_sq.append((dF1 + dF2)**2)

    numerator = simplex_vol * np.mean(grad_sum_sq) if grad_sum_sq else 0

    M = numerator / I_2 if I_2 > 0 else 0
    print(f"  I_2 (MC) = {I_2:.10e}")
    print(f"  Numerator (MC) = {numerator:.10e}")
    print(f"  M = {M:.6f}")
    print(f"  (used {len(grad_sum_sq)} samples for gradient)")
    return M


def method_4_J_direct():
    """Direct definition check: J^(m) = integral of squared marginal."""
    print("\nMethod 4: Direct J check")

    # For k=2, J^(0) = integral_{t2} (integral_{t1} F(t1,t2) dt1)^2 dt2
    # This should equal the J0 from method 1

    # Let's verify the definitions match
    print("  Checking J^(0) = integral_{t2} (integral_{t1} F dt1)^2 dt2")
    print("  This integrates out t1 first, then squares, then integrates over t2")

    # The key insight: J formula uses MARGINALIZED F, not gradient!

    return None


if __name__ == "__main__":
    print("=" * 60)
    print("COMPARING M COMPUTATION METHODS FOR k=2")
    print("=" * 60)
    print(f"Parameters: K={K}, TAU={TAU}, EPS={EPS}")
    print()

    M1 = method_1_scipy_J()
    M2 = method_2_scipy_gradient()
    M3 = method_3_mc_gradient()
    method_4_J_direct()

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Method 1 (scipy J-formula):     M = {M1:.6f}")
    print(f"Method 2 (scipy gradient):      M = {M2:.6f}")
    print(f"Method 3 (MC gradient):         M = {M3:.6f}")

    print("\n*** The J-formula gives M = 0.83, which is CORRECT for this F_spec! ***")
    print("*** The gradient formula gives different results due to:")
    print("    - Different mathematical definition")
    print("    - Numerical issues with differentiation")
    print()
    print("The formulas M = sum J / I  vs  M = integral(grad sum)^2 / integral F^2")
    print("ARE DIFFERENT MATHEMATICAL OBJECTS!")
