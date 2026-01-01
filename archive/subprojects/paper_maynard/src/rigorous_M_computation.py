#!/usr/bin/env python3
"""
Computation of M(F_spec) for the spectral sieve function.

Uses scipy for numerical integration with error bounds.
For the paper: "Sieve-Spectral Synergy"
"""

import numpy as np
from scipy import integrate
import json
from datetime import datetime
import os

# Parameters
K = 2.5
TAU = 1.0
EPSILON = 0.1


def W_Q3(s: float) -> float:
    """
    Q3 weight kernel: W_Q3(s) = 4*pi*K*s * exp(-pi*K*s) * exp(-K^2*s^2/(4*tau))
    """
    if s <= 0:
        return 0.0
    term1 = 4 * np.pi * K * s
    term2 = np.exp(-np.pi * K * s)
    term3 = np.exp(-K**2 * s**2 / (4 * TAU))
    return term1 * term2 * term3


def chi_epsilon(u: float) -> float:
    """
    Smooth cutoff: chi_epsilon(u) = 1 for u <= 1-epsilon, 0 for u >= 1
    """
    if u <= 1 - EPSILON:
        return 1.0
    elif u >= 1:
        return 0.0
    else:
        x = (u - (1 - EPSILON)) / EPSILON
        if x >= 1:
            return 0.0
        return np.exp(-1.0 / (1 - x**2))


def F_spec_2d(t1: float, t2: float) -> float:
    """F_spec for k=2"""
    if t1 <= 0 or t2 <= 0:
        return 0.0
    if t1 + t2 > 1:
        return 0.0
    W1 = W_Q3(t1)
    W2 = W_Q3(t2)
    if W1 == 0 or W2 == 0:
        return 0.0
    gaussian = np.exp(-(t1**2 + t2**2) / TAU)
    cutoff = chi_epsilon(t1 + t2)
    return W1 * W2 * gaussian * cutoff


def compute_M_k2():
    """
    Compute M(F_spec) for k=2 using scipy.integrate.
    M = (J^(0) + J^(1)) / I
    """
    print("Computing I_2...")

    # I_2 = integral_{t1+t2 <= 1} F^2 dt
    def F_squared(t2, t1):
        return F_spec_2d(t1, t2)**2

    I_2, I_err = integrate.dblquad(
        F_squared,
        0, 1,           # t1 from 0 to 1
        0, lambda t1: 1 - t1,  # t2 from 0 to 1-t1
        epsabs=1e-10, epsrel=1e-10
    )
    print(f"  I_2 = {I_2:.15e} +/- {I_err:.2e}")

    print("Computing J^(0)...")
    # J^(0) = integral_{t2} (integral_{t1} F dt1)^2 dt2

    def inner_0(t2):
        if t2 >= 1:
            return 0.0
        result, _ = integrate.quad(
            lambda t1: F_spec_2d(t1, t2),
            0, 1 - t2,
            epsabs=1e-10, epsrel=1e-10
        )
        return result

    def J0_integrand(t2):
        return inner_0(t2)**2

    J0, J0_err = integrate.quad(
        J0_integrand, 0, 1,
        epsabs=1e-10, epsrel=1e-10
    )
    print(f"  J^(0) = {J0:.15e} +/- {J0_err:.2e}")

    print("Computing J^(1)...")
    # J^(1) = integral_{t1} (integral_{t2} F dt2)^2 dt1

    def inner_1(t1):
        if t1 >= 1:
            return 0.0
        result, _ = integrate.quad(
            lambda t2: F_spec_2d(t1, t2),
            0, 1 - t1,
            epsabs=1e-10, epsrel=1e-10
        )
        return result

    def J1_integrand(t1):
        return inner_1(t1)**2

    J1, J1_err = integrate.quad(
        J1_integrand, 0, 1,
        epsabs=1e-10, epsrel=1e-10
    )
    print(f"  J^(1) = {J1:.15e} +/- {J1_err:.2e}")

    J_sum = J0 + J1
    M = J_sum / I_2

    # Error propagation
    total_J_err = np.sqrt(J0_err**2 + J1_err**2)
    M_err = M * np.sqrt((total_J_err / J_sum)**2 + (I_err / I_2)**2)

    return {
        "k": 2,
        "I_k": I_2,
        "I_err": I_err,
        "J0": J0,
        "J0_err": J0_err,
        "J1": J1,
        "J1_err": J1_err,
        "J_sum": J_sum,
        "M": M,
        "M_err": M_err,
        "M_lower_bound": M - 3 * M_err,  # 3-sigma lower bound
        "parameters": {"K": K, "tau": TAU, "epsilon": EPSILON}
    }


def compute_M_gradient_k2():
    """
    Alternative: compute M via gradient formula.
    M = integral (dF/dt1 + dF/dt2)^2 / integral F^2
    """
    print("\nAlternative: Gradient formula...")

    h = 1e-6  # finite difference step

    def grad_sum_squared(t2, t1):
        if t1 <= h or t2 <= h or t1 + t2 > 1 - h:
            return 0.0
        F = F_spec_2d(t1, t2)
        if F < 1e-15:
            return 0.0
        dF_dt1 = (F_spec_2d(t1 + h, t2) - F_spec_2d(t1 - h, t2)) / (2 * h)
        dF_dt2 = (F_spec_2d(t1, t2 + h) - F_spec_2d(t1, t2 - h)) / (2 * h)
        return (dF_dt1 + dF_dt2)**2

    numerator, num_err = integrate.dblquad(
        grad_sum_squared,
        0, 1,
        0, lambda t1: 1 - t1,
        epsabs=1e-8, epsrel=1e-8
    )
    print(f"  Numerator = {numerator:.10e}")

    def F_squared(t2, t1):
        return F_spec_2d(t1, t2)**2

    denominator, den_err = integrate.dblquad(
        F_squared,
        0, 1,
        0, lambda t1: 1 - t1,
        epsabs=1e-10, epsrel=1e-10
    )
    print(f"  Denominator = {denominator:.10e}")

    M_grad = numerator / denominator
    return M_grad


def main():
    print("=" * 60)
    print("COMPUTATION OF M(F_spec)")
    print("=" * 60)
    print(f"Parameters: K={K}, tau={TAU}, epsilon={EPSILON}")
    print()

    # Compute for k=2
    result = compute_M_k2()

    print()
    print("=" * 60)
    print("RESULTS FOR k=2 (J-formula)")
    print("=" * 60)
    print(f"I_2 = {result['I_k']:.15e}")
    print(f"J_sum = {result['J_sum']:.15e}")
    print(f"M(F_spec) = {result['M']:.10f}")
    print(f"M uncertainty = {result['M_err']:.2e}")
    print(f"Lower bound (3-sigma): M >= {result['M_lower_bound']:.10f}")

    # Alternative via gradient
    M_grad = compute_M_gradient_k2()
    print(f"\nGradient formula: M = {M_grad:.10f}")

    # Check if M > 2
    if result['M_lower_bound'] > 2:
        print("\n*** VERIFIED: M(F_spec) > 2 with high confidence ***")
        status = "VERIFIED"
    elif result['M'] > 2:
        print("\n*** M(F_spec) > 2 (point estimate) ***")
        status = "LIKELY"
    else:
        print("\n*** M(F_spec) <= 2 ***")
        status = "NOT_VERIFIED"

    result['status'] = status
    result['M_gradient'] = M_grad
    result['timestamp'] = datetime.now().isoformat()

    # Save results
    output_dir = '/Users/emalam/Documents/GitHub/chen_q3/paper_maynard/output'
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, 'M_rigorous_k2.json')

    with open(output_file, 'w') as f:
        json.dump(result, f, indent=2)

    print(f"\nResults saved to: {output_file}")

    return result


def compute_M_monte_carlo(k: int, n_samples: int = 100000):
    """
    Monte Carlo estimation of M(F_spec) for larger k.
    """
    print(f"\n{'='*60}")
    print(f"MONTE CARLO for k={k}")
    print(f"{'='*60}")

    np.random.seed(42)

    # Sample from k-simplex
    def sample_simplex(n, k):
        """Sample n points uniformly from k-simplex."""
        # Use exponential distribution method
        exp_samples = np.random.exponential(1, (n, k + 1))
        return exp_samples[:, :k] / exp_samples.sum(axis=1, keepdims=True)

    samples = sample_simplex(n_samples, k)

    # Compute F_spec for each sample
    def F_spec_general(t):
        """F_spec for general k."""
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

    # Compute integrals
    F_values = np.array([F_spec_general(s) for s in samples])
    F2_values = F_values**2

    # I_k = volume * mean(F^2)
    simplex_volume = 1.0 / np.math.factorial(k)
    I_k = simplex_volume * np.mean(F2_values)

    # For J_k^(m), we need marginal integrals
    # This is harder to do with simple MC...
    # Approximate using ratio of means

    print(f"  Mean F^2 = {np.mean(F2_values):.6e}")
    print(f"  I_k estimate = {I_k:.6e}")

    # Estimate via gradient (MC)
    h = 0.001
    grad_sum_sq = []
    for s in samples[:10000]:  # Subset for speed
        if np.all(s > h) and np.sum(s) < 1 - h:
            F0 = F_spec_general(s)
            if F0 < 1e-15:
                continue
            grad_sum = 0.0
            for j in range(k):
                s_plus = s.copy()
                s_minus = s.copy()
                s_plus[j] += h
                s_minus[j] -= h
                dF = (F_spec_general(s_plus) - F_spec_general(s_minus)) / (2*h)
                grad_sum += dF
            grad_sum_sq.append(grad_sum**2)

    numerator = simplex_volume * np.mean(grad_sum_sq)
    M_estimate = numerator / I_k if I_k > 0 else 0

    print(f"  M(F_spec) estimate = {M_estimate:.4f}")

    return {"k": k, "M_estimate": M_estimate, "I_k": I_k, "n_samples": n_samples}


if __name__ == "__main__":
    result = main()

    # Test larger k values (fewer samples for speed)
    for k in [5, 10, 20]:
        compute_M_monte_carlo(k, n_samples=10000)
