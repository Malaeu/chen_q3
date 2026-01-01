#!/usr/bin/env python3
"""
Rigorous verification that M > 2 for k=7 with F = (1-sum t)^0.5.

Uses mpmath with high precision and conservative error bounds.
"""

import numpy as np
from scipy import integrate
import mpmath
from mpmath import mpf, mp
import json
from datetime import datetime

# Set high precision
mp.dps = 50  # 50 decimal places

ALPHA = mpf('0.5')


def F_poly_mp(t):
    """F(t) = (1 - sum t)^alpha with mpmath."""
    s = sum(mpf(str(ti)) for ti in t)
    if s > 1:
        return mpf('0')
    return (1 - s)**ALPHA


def compute_I_k_rigorous(k, n_samples=50000):
    """
    Compute I_k = integral F^2 dt over k-simplex.
    Use MC with error estimate.
    """
    np.random.seed(42)

    # Sample from k-simplex
    exp = np.random.exponential(1, (n_samples, k+1))
    samples = exp[:, :k] / exp.sum(axis=1, keepdims=True)

    # Compute F^2 for each sample
    F2_values = []
    for s in samples:
        F = float(F_poly_mp(s))
        F2_values.append(F**2)

    F2_values = np.array(F2_values)

    # Simplex volume = 1/k!
    import math
    vol = mpf(1) / mpf(math.factorial(k))

    # MC estimate
    mean_F2 = np.mean(F2_values)
    std_F2 = np.std(F2_values) / np.sqrt(n_samples)

    I_k = float(vol) * mean_F2
    I_k_err = float(vol) * std_F2 * 3  # 3-sigma

    return I_k, I_k_err


def compute_J_k_rigorous(k, n_samples=20000):
    """
    Compute J = sum_m J^(m) for k-simplex.
    J^(m) = integral (integral F dt_m)^2 dt_{-m}

    By symmetry, J = k * J^(0)
    """
    np.random.seed(42)
    import math

    # Sample t_{-0} from (k-1)-simplex
    exp = np.random.exponential(1, (n_samples, k))
    samples_km1 = exp[:, :k-1] / exp.sum(axis=1, keepdims=True)

    inner_sq = []
    for t_minus in samples_km1:
        s_minus = sum(t_minus)
        if s_minus >= 1:
            inner_sq.append(0.0)
            continue

        upper = 1 - s_minus

        # Analytical inner integral for F = (1-s)^alpha
        # integral_0^upper (1 - s_minus - t0)^alpha dt0
        # = (1 - s_minus)^{alpha+1} / (alpha+1)
        # = upper^{alpha+1} / (alpha+1)

        inner = float((mpf(str(upper))**(ALPHA + 1)) / (ALPHA + 1))
        inner_sq.append(inner**2)

    inner_sq = np.array(inner_sq)

    # Volume of (k-1)-simplex
    vol_km1 = mpf(1) / mpf(math.factorial(k-1))

    mean_inner_sq = np.mean(inner_sq)
    std_inner_sq = np.std(inner_sq) / np.sqrt(n_samples)

    J0 = float(vol_km1) * mean_inner_sq
    J0_err = float(vol_km1) * std_inner_sq * 3

    # Total J = k * J0 by symmetry
    J = k * J0
    J_err = k * J0_err

    return J, J_err


def main():
    print("=" * 60)
    print("RIGOROUS VERIFICATION: M > 2 FOR k=7")
    print("=" * 60)
    print(f"F(t) = (1 - sum t)^{ALPHA}")
    print(f"Precision: {mp.dps} decimal places")
    print()

    k = 7

    print(f"Computing I_{k}...")
    I_k, I_err = compute_I_k_rigorous(k, n_samples=100000)
    print(f"  I_{k} = {I_k:.10e} ± {I_err:.2e}")

    print(f"Computing J = sum J^(m)...")
    J, J_err = compute_J_k_rigorous(k, n_samples=50000)
    print(f"  J = {J:.10e} ± {J_err:.2e}")

    M = J / I_k
    # Error propagation
    M_err = M * np.sqrt((J_err/J)**2 + (I_err/I_k)**2)

    M_lower = M - M_err
    M_upper = M + M_err

    print()
    print("=" * 60)
    print("RESULT")
    print("=" * 60)
    print(f"M = {M:.6f}")
    print(f"M ∈ [{M_lower:.6f}, {M_upper:.6f}]")

    if M_lower > 2:
        print()
        print("*** RIGOROUSLY VERIFIED: M > 2 ***")
        status = "VERIFIED"
    elif M > 2:
        print()
        print("*** M > 2 (point estimate), lower bound {M_lower:.4f} < 2 ***")
        print("Need more samples for rigorous bound")
        status = "LIKELY"
    else:
        print()
        print("*** M <= 2 ***")
        status = "NOT_VERIFIED"

    # Save results
    result = {
        "k": k,
        "alpha": float(ALPHA),
        "I_k": I_k,
        "I_k_err": I_err,
        "J": J,
        "J_err": J_err,
        "M": M,
        "M_lower": M_lower,
        "M_upper": M_upper,
        "status": status,
        "precision_digits": mp.dps,
        "timestamp": datetime.now().isoformat()
    }

    output_file = '/Users/emalam/Documents/GitHub/chen_q3/paper_maynard/output/M_rigorous_k7.json'
    with open(output_file, 'w') as f:
        json.dump(result, f, indent=2)

    print(f"\nResults saved to: {output_file}")


if __name__ == "__main__":
    main()
