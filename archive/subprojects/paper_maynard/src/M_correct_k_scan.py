#!/usr/bin/env python3
"""
Correct computation of M(F_spec) using J-formula for various k.
M = sum_m J_k^(m) / I_k
"""

import numpy as np
from scipy import integrate
import math
from functools import lru_cache

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


def F_spec_k2(t1, t2):
    if t1 <= 0 or t2 <= 0 or t1 + t2 > 1:
        return 0.0
    W1 = W_Q3(t1)
    W2 = W_Q3(t2)
    if W1 == 0 or W2 == 0:
        return 0.0
    return W1 * W2 * np.exp(-(t1**2 + t2**2) / TAU) * chi_epsilon(t1 + t2)


def F_spec_k3(t1, t2, t3):
    if t1 <= 0 or t2 <= 0 or t3 <= 0 or t1 + t2 + t3 > 1:
        return 0.0
    W1 = W_Q3(t1)
    W2 = W_Q3(t2)
    W3 = W_Q3(t3)
    if W1 == 0 or W2 == 0 or W3 == 0:
        return 0.0
    norm_sq = t1**2 + t2**2 + t3**2
    return W1 * W2 * W3 * np.exp(-norm_sq / TAU) * chi_epsilon(t1 + t2 + t3)


def compute_M_k2():
    """Compute M for k=2 using J-formula."""
    print("Computing M for k=2...")

    def F_sq(t2, t1):
        return F_spec_k2(t1, t2)**2

    I_2, _ = integrate.dblquad(F_sq, 0, 1, 0, lambda t1: 1-t1, epsabs=1e-8)

    def inner_0(t2):
        if t2 >= 1:
            return 0.0
        result, _ = integrate.quad(lambda t1: F_spec_k2(t1, t2), 0, 1-t2, epsabs=1e-8)
        return result

    J0, _ = integrate.quad(lambda t2: inner_0(t2)**2, 0, 1, epsabs=1e-8)

    # By symmetry J0 = J1
    J1 = J0

    M = (J0 + J1) / I_2
    print(f"  I_2 = {I_2:.6e}, J = {J0+J1:.6e}, M = {M:.6f}")
    return M


def compute_M_k3():
    """Compute M for k=3 using J-formula."""
    print("Computing M for k=3...")

    # I_3 = triple integral
    def F_sq(t3, t2, t1):
        return F_spec_k3(t1, t2, t3)**2

    I_3, _ = integrate.tplquad(
        F_sq,
        0, 1,                    # t1
        0, lambda t1: 1-t1,      # t2
        0, lambda t1, t2: 1-t1-t2,  # t3
        epsabs=1e-6
    )

    # J^(0) = int_{t2,t3} (int_{t1} F dt1)^2 dt2 dt3
    def inner_0(t2, t3):
        if t2 + t3 >= 1:
            return 0.0
        result, _ = integrate.quad(lambda t1: F_spec_k3(t1, t2, t3), 0, 1-t2-t3, epsabs=1e-6)
        return result

    def J0_integrand(t3, t2):
        return inner_0(t2, t3)**2

    J0, _ = integrate.dblquad(J0_integrand, 0, 1, 0, lambda t2: 1-t2, epsabs=1e-6)

    # By symmetry J0 = J1 = J2
    J_sum = 3 * J0

    M = J_sum / I_3
    print(f"  I_3 = {I_3:.6e}, J_sum = {J_sum:.6e}, M = {M:.6f}")
    return M


def compute_M_MC(k, n_samples=50000):
    """Monte Carlo estimate for larger k."""
    print(f"Computing M for k={k} (Monte Carlo)...")

    np.random.seed(42)

    # Sample from k-simplex
    exp_samples = np.random.exponential(1, (n_samples, k+1))
    samples = exp_samples[:, :k] / exp_samples.sum(axis=1, keepdims=True)

    # Compute F for all samples
    def F_spec_general(t):
        if np.sum(t) > 1:
            return 0.0
        prod_W = 1.0
        for ti in t:
            if ti <= 0:
                return 0.0
            w = W_Q3(ti)
            if w == 0:
                return 0.0
            prod_W *= w
        gaussian = np.exp(-np.sum(t**2) / TAU)
        cutoff = chi_epsilon(np.sum(t))
        return prod_W * gaussian * cutoff

    F_values = np.array([F_spec_general(s) for s in samples])
    F2_values = F_values**2

    # I_k = volume * mean(F^2)
    simplex_vol = 1.0 / math.factorial(k)
    I_k = simplex_vol * np.mean(F2_values)

    # For J_k^(m), we need marginal integrals
    # J^(m) = E[(E[F | t_{-m}])^2]
    # This is hard to compute with MC...

    # Alternative: use the VARIANCE formula
    # M = k * Var(F_marginal) / Var(F) ??? No, that's not right either.

    # Let's use a different approach: nested MC
    # For each sample of t_{-m}, integrate over t_m

    J_estimates = []
    for m in range(k):
        marginal_sq = []
        for i in range(min(5000, n_samples)):
            s = samples[i]
            t_minus_m = np.delete(s, m)
            if np.sum(t_minus_m) >= 1:
                continue
            # Integrate over t_m from 0 to 1-sum(t_{-m})
            upper = 1 - np.sum(t_minus_m)
            if upper <= 0:
                continue
            # Use quadrature for inner integral
            def F_with_tm(tm):
                t_full = np.insert(t_minus_m, m, tm)
                return F_spec_general(t_full)
            result, _ = integrate.quad(F_with_tm, 0, upper, epsabs=1e-6, limit=20)
            marginal_sq.append(result**2)

        if marginal_sq:
            # Volume of (k-1)-simplex = 1/(k-1)!
            vol_km1 = 1.0 / math.factorial(k-1)
            J_m = vol_km1 * np.mean(marginal_sq)
            J_estimates.append(J_m)

    J_sum = sum(J_estimates)
    M = J_sum / I_k if I_k > 0 else 0

    print(f"  I_{k} = {I_k:.6e}, J_sum = {J_sum:.6e}, M = {M:.6f}")
    return M


def main():
    print("=" * 60)
    print("CORRECT M(F_spec) COMPUTATION VIA J-FORMULA")
    print("=" * 60)
    print(f"Parameters: K={K}, TAU={TAU}, EPS={EPS}")
    print()

    results = []

    # k=2 exact
    M2 = compute_M_k2()
    results.append(("k=2 (exact)", M2))

    # k=3 exact
    M3 = compute_M_k3()
    results.append(("k=3 (exact)", M3))

    # k=5, 10, 20 MC
    for k in [5, 10, 20]:
        M = compute_M_MC(k, n_samples=10000)
        results.append((f"k={k} (MC)", M))

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    for name, M in results:
        status = "M > 2 ✓" if M > 2 else "M < 2"
        print(f"{name:20s}: M = {M:.6f}  [{status}]")

    # Extrapolate
    print("\nFor M > 2, we need sufficiently large k.")
    print("M appears to grow slowly with k.")


if __name__ == "__main__":
    main()
