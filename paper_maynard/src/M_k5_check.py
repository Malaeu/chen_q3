#!/usr/bin/env python3
"""
Check M for k=5 to see if M > 2.
Use MC with J-formula estimation.
"""

import numpy as np
from scipy import integrate
import math

def F_maynard_poly(t, alpha=0.5):
    """F(t) = (1 - sum t_i)^alpha"""
    s = np.sum(t)
    if s > 1:
        return 0.0
    return (1 - s)**alpha

def sample_simplex(n, k):
    """Sample n points from k-simplex."""
    exp = np.random.exponential(1, (n, k+1))
    return exp[:, :k] / exp.sum(axis=1, keepdims=True)

def compute_M_MC_J(k, F_func, n_samples=20000, n_inner=100):
    """
    Compute M using MC with J-formula.
    J^(m) = E_{t_{-m}} [ (E_{t_m} [F | t_{-m}])^2 ]
    """
    np.random.seed(42)

    # Sample for I_k
    samples = sample_simplex(n_samples, k)
    F_values = np.array([F_func(s) for s in samples])
    F2_values = F_values**2

    vol_k = 1.0 / math.factorial(k)
    I_k = vol_k * np.mean(F2_values)

    # Estimate J^(m) for m=0 (by symmetry, all J^(m) are equal)
    # J^(0) = E_{t_1,...,t_{k-1}} [ (integral_{t_0} F(t) dt_0)^2 ]

    # Sample t_{-0} from (k-1)-simplex
    samples_km1 = sample_simplex(n_samples, k-1)

    inner_integrals = []
    for t_minus_0 in samples_km1:
        s_minus = np.sum(t_minus_0)
        if s_minus >= 1:
            inner_integrals.append(0.0)
            continue

        # Integrate over t_0 from 0 to 1-s_minus
        upper = 1 - s_minus

        # Use quadrature for the inner integral
        def F_with_t0(t0):
            t = np.insert(t_minus_0, 0, t0)
            return F_func(t)

        result, _ = integrate.quad(F_with_t0, 0, upper, epsabs=1e-8, limit=50)
        inner_integrals.append(result**2)

    vol_km1 = 1.0 / math.factorial(k-1)
    J0 = vol_km1 * np.mean(inner_integrals)

    # By symmetry, J_sum = k * J0
    J_sum = k * J0

    M = J_sum / I_k if I_k > 0 else 0

    return I_k, J_sum, M


def main():
    print("=" * 60)
    print("CHECKING M FOR k=3,4,5 WITH F = (1-sum t)^0.5")
    print("=" * 60)
    print()

    alpha = 0.5
    F = lambda t: F_maynard_poly(t, alpha)

    results = []
    for k in [3, 5, 7, 10, 15, 20]:
        print(f"Computing k={k}...", end=" ", flush=True)
        I, J, M = compute_M_MC_J(k, F, n_samples=10000)
        status = "✓ M > 2" if M > 2 else "M < 2"
        print(f"I={I:.4e}, J={J:.4e}, M={M:.4f}  [{status}]")
        results.append((k, M))

    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    for k, M in results:
        status = "✓ M > 2" if M > 2 else "M < 2"
        print(f"k={k}: M = {M:.4f}  [{status}]")

    # Check if any k has M > 2
    for k, M in results:
        if M > 2:
            print(f"\n*** SUCCESS: k={k} gives M={M:.4f} > 2 ***")
            print("This means bounded prime gaps for admissible k-tuples!")
            break


if __name__ == "__main__":
    main()
