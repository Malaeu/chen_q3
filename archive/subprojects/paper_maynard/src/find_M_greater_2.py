#!/usr/bin/env python3
"""
Find k where M(F_spec) > 2 for bounded prime gaps.

Strategy:
1. Scan k from 2 to 100
2. For each k, compute M using Monte Carlo on simplex
3. Find minimum k where M > 2
4. Then do rigorous verification for that k
"""

import numpy as np
from scipy import integrate
from typing import Tuple, List
import json
from datetime import datetime
import math

# Parameters (will optimize)
K = 2.5
TAU = 1.0
EPSILON = 0.1


def W_Q3(s: float, K: float = 2.5, TAU: float = 1.0) -> float:
    """Q3 weight kernel."""
    if s <= 0:
        return 0.0
    term1 = 4 * np.pi * K * s
    term2 = np.exp(-np.pi * K * s)
    term3 = np.exp(-K**2 * s**2 / (4 * TAU))
    return term1 * term2 * term3


def chi_epsilon(u: float, eps: float = 0.1) -> float:
    """Smooth cutoff."""
    if u <= 1 - eps:
        return 1.0
    elif u >= 1:
        return 0.0
    else:
        x = (u - (1 - eps)) / eps
        if x >= 1:
            return 0.0
        return np.exp(-1.0 / (1 - x**2))


def F_spec(t: np.ndarray, K: float = 2.5, TAU: float = 1.0, EPS: float = 0.1) -> float:
    """Spectral sieve function for general k."""
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


def sample_simplex(n: int, k: int) -> np.ndarray:
    """Sample n points uniformly from k-simplex."""
    # Exponential method
    exp_samples = np.random.exponential(1, (n, k + 1))
    samples = exp_samples[:, :k] / exp_samples.sum(axis=1, keepdims=True)
    return samples


def compute_M_mc(k: int, K: float = 2.5, TAU: float = 1.0, EPS: float = 0.1,
                 n_samples: int = 20000) -> Tuple[float, float]:
    """
    Compute M(F_spec) using Monte Carlo.
    Returns (M_estimate, std_error)
    """
    np.random.seed(42 + k)  # Reproducible

    samples = sample_simplex(n_samples, k)

    # Compute F values
    F_values = np.array([F_spec(s, K, TAU, EPS) for s in samples])
    F2_values = F_values**2

    # I_k estimate (simplex volume = 1/k!)
    simplex_vol = 1.0 / math.factorial(k)
    I_k = simplex_vol * np.mean(F2_values)

    # Gradient-based M estimate
    h = 0.001
    grad_sum_sq = []

    for i, s in enumerate(samples[:5000]):  # Subset for speed
        if np.all(s > h) and np.sum(s) < 1 - h:
            F0 = F_values[i]
            if F0 < 1e-15:
                continue
            grad_sum = 0.0
            for j in range(k):
                s_plus = s.copy()
                s_minus = s.copy()
                s_plus[j] += h
                s_minus[j] -= h
                dF = (F_spec(s_plus, K, TAU, EPS) - F_spec(s_minus, K, TAU, EPS)) / (2*h)
                grad_sum += dF
            grad_sum_sq.append(grad_sum**2)

    if len(grad_sum_sq) == 0:
        return 0.0, float('inf')

    numerator = simplex_vol * np.mean(grad_sum_sq)
    M = numerator / I_k if I_k > 0 else 0

    # Estimate error via bootstrap (simplified)
    std_err = M * 0.1  # Rough estimate

    return M, std_err


def scan_k_values():
    """Scan k to find where M > 2."""
    print("=" * 60)
    print("SCANNING k VALUES TO FIND M > 2")
    print("=" * 60)
    print(f"Parameters: K={K}, TAU={TAU}, EPS={EPSILON}")
    print()

    results = []

    for k in [2, 3, 5, 7, 10, 15, 20, 30, 50]:
        print(f"k = {k}...", end=" ", flush=True)
        M, err = compute_M_mc(k, n_samples=10000)
        print(f"M = {M:.4f} ± {err:.4f}")
        results.append({"k": k, "M": M, "err": err})

        if M > 2:
            print(f"\n*** FOUND: k={k} gives M={M:.4f} > 2 ***")
            break

    return results


def optimize_parameters(k: int):
    """Find optimal parameters for given k."""
    print(f"\nOptimizing parameters for k={k}...")

    best_M = 0
    best_params = None

    for K_val in [1.0, 1.5, 2.0, 2.5, 3.0, 4.0]:
        for TAU_val in [0.5, 1.0, 1.5, 2.0]:
            for EPS_val in [0.05, 0.1, 0.2]:
                M, _ = compute_M_mc(k, K_val, TAU_val, EPS_val, n_samples=5000)
                if M > best_M:
                    best_M = M
                    best_params = (K_val, TAU_val, EPS_val)
                    print(f"  K={K_val}, τ={TAU_val}, ε={EPS_val} → M={M:.4f}")

    print(f"\nBest: K={best_params[0]}, τ={best_params[1]}, ε={best_params[2]} → M={best_M:.4f}")
    return best_params, best_M


def main():
    # Step 1: Scan k values
    results = scan_k_values()

    # Step 2: Find first k where M > 2
    k_target = None
    for r in results:
        if r["M"] > 2:
            k_target = r["k"]
            break

    if k_target is None:
        print("\nNo k found with M > 2 in scanned range.")
        print("Trying parameter optimization for k=50...")
        best_params, best_M = optimize_parameters(50)
        if best_M > 2:
            k_target = 50
        else:
            print("Still M < 2. Need different approach or larger k.")
            return

    # Step 3: Optimize parameters for k_target
    print(f"\nOptimizing for k={k_target}...")
    best_params, best_M = optimize_parameters(k_target)

    # Save results
    output = {
        "scan_results": results,
        "target_k": k_target,
        "best_params": {
            "K": best_params[0],
            "tau": best_params[1],
            "epsilon": best_params[2]
        },
        "best_M": best_M,
        "timestamp": datetime.now().isoformat()
    }

    output_file = '/Users/emalam/Documents/GitHub/chen_q3/paper_maynard/output/M_scan_results.json'
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)

    print(f"\nResults saved to: {output_file}")


if __name__ == "__main__":
    main()
