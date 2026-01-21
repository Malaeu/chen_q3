#!/usr/bin/env python3
"""
Test scaling at VERY large N to understand true asymptotic behavior.
"""

import numpy as np
import warnings
warnings.filterwarnings('ignore')

def get_twins(X_max):
    sieve = np.ones(X_max + 3, dtype=bool)
    sieve[0] = sieve[1] = False
    for i in range(2, int(np.sqrt(X_max + 3)) + 1):
        if sieve[i]:
            sieve[i*i::i] = False
    twins = []
    for p in range(3, X_max + 1, 2):
        if sieve[p] and sieve[p + 2]:
            twins.append(p)
    return np.array(twins)

def build_matrices(twins, t=1.0):
    N = len(twins)
    xi = np.log(twins) / (2 * np.pi)
    G = np.zeros((N, N))
    A = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = xi[j] - xi[i]
            K = np.sqrt(2 * np.pi * t) * np.exp(-delta**2 / (4 * t))
            G[i, j] = K
            A[i, j] = delta * K
    Q = A.T @ A
    return Q, G, A, xi

print("=" * 70)
print("LARGE N SCALING TEST")
print("=" * 70)

# Test at progressively larger X
X_values = [10000, 20000, 50000, 100000, 200000, 500000]

results = []
for X in X_values:
    twins = get_twins(X)
    N = len(twins)
    if N < 10:
        continue

    print(f"\nX = {X}, N = {N}... ", end="", flush=True)

    Q, G, A, xi = build_matrices(twins)

    min_Q_row = np.min(np.sum(Q, axis=1))
    max_G_row = np.max(np.sum(G, axis=1))
    bound = min_Q_row / max_G_row

    # Where is minimum?
    Q_rowsum = np.sum(Q, axis=1)
    min_idx = np.argmin(Q_rowsum)

    results.append({
        'X': X, 'N': N,
        'min_Q_row': min_Q_row,
        'max_G_row': max_G_row,
        'bound': bound,
        'min_idx': min_idx,
        'min_pct': 100 * min_idx / N
    })

    min_pct = 100 * min_idx / N
    print(f"bound = {bound:.2f}, min at {min_pct:.1f}%")

print("\n" + "=" * 70)
print("SCALING ANALYSIS")
print("=" * 70)

N_arr = np.array([r['N'] for r in results])
bound_arr = np.array([r['bound'] for r in results])
min_Q_arr = np.array([r['min_Q_row'] for r in results])
max_G_arr = np.array([r['max_G_row'] for r in results])

# Power law fits
def fit_power(x, y):
    log_x = np.log(x)
    log_y = np.log(np.abs(y))
    coeffs = np.polyfit(log_x, log_y, 1)
    return coeffs[0], np.exp(coeffs[1])

exp_bound, pref_bound = fit_power(N_arr, bound_arr)
exp_minQ, pref_minQ = fit_power(N_arr, min_Q_arr)
exp_maxG, pref_maxG = fit_power(N_arr, max_G_arr)

print(f"\nPower law fits:")
print(f"  min(Q_rowsum) ~ {pref_minQ:.4f} × N^{exp_minQ:.4f}")
print(f"  max(G_rowsum) ~ {pref_maxG:.4f} × N^{exp_maxG:.4f}")
print(f"  rowsum_bound ~ {pref_bound:.4f} × N^{exp_bound:.4f}")

print(f"\nExpected: bound ~ N^(exp_minQ - exp_maxG) = N^{exp_minQ - exp_maxG:.4f}")
print(f"Actual:   bound ~ N^{exp_bound:.4f}")

print("\n" + "-" * 50)
print("CRITICAL CHECK: Does bound → ∞?")
print("-" * 50)

if exp_bound > 0:
    print(f"\n✅ YES! bound ~ N^{exp_bound:.3f} → ∞")
    print("   This proves P(X) and hence TPC!")
else:
    print(f"\n❌ NO! bound ~ N^{exp_bound:.3f} is NOT growing!")
    print("   Need different approach.")

# Detailed table
print("\n" + "=" * 70)
print("DETAILED DATA")
print("=" * 70)
print(f"{'N':>6} | {'min(Q_row)':>12} | {'max(G_row)':>10} | {'bound':>8} | {'bound/√N':>8} | {'min at':>6}")
print("-" * 70)
for r in results:
    print(f"{r['N']:6d} | {r['min_Q_row']:12.2f} | {r['max_G_row']:10.2f} | {r['bound']:8.4f} | {r['bound']/np.sqrt(r['N']):8.4f} | {r['min_pct']:5.1f}%")
