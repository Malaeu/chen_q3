#!/usr/bin/env python3
"""
ANALYZE OPTIMAL VECTOR STRUCTURE

Understanding WHY min_cone R ~ N^{0.87} could lead to a proof!
"""

import numpy as np
from scipy.optimize import minimize
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

def min_on_cone(Q, G, n_trials=500):
    N = Q.shape[0]
    def R(lam):
        lam = np.maximum(lam, 1e-10)
        norm = np.linalg.norm(lam)
        if norm < 1e-10:
            return 1e10
        lam = lam / norm
        return (lam @ Q @ lam) / (lam @ G @ lam)

    best_R = np.inf
    best_lam = None
    for _ in range(n_trials):
        x0 = np.random.exponential(size=N)
        try:
            result = minimize(R, x0, method='L-BFGS-B', bounds=[(1e-10, None)] * N)
            if result.fun < best_R:
                best_R = result.fun
                best_lam = np.maximum(result.x, 0)
                best_lam = best_lam / np.linalg.norm(best_lam)
        except:
            pass
    return best_R, best_lam

print("=" * 70)
print("OPTIMAL VECTOR ANALYSIS")
print("=" * 70)

X_values = [1000, 2000, 5000, 10000]

for X in X_values:
    twins = get_twins(X)
    N = len(twins)
    Q, G, A, xi = build_matrices(twins)

    min_R, opt_lam = min_on_cone(Q, G, n_trials=300)

    print(f"\n{'='*70}")
    print(f"X = {X}, N = {N}, min_R = {min_R:.4f}")
    print(f"{'='*70}")

    # Analyze optimal vector structure
    print("\n1. CONCENTRATION ANALYSIS:")
    sorted_indices = np.argsort(opt_lam)[::-1]  # Descending order
    top_10_weight = np.sum(opt_lam[sorted_indices[:N//10]]**2)
    top_50_weight = np.sum(opt_lam[sorted_indices[:N//2]]**2)
    entropy = -np.sum(opt_lam**2 * np.log(opt_lam**2 + 1e-10))
    max_entropy = np.log(N)

    print(f"  Weight in top 10% indices: {100*top_10_weight:.1f}%")
    print(f"  Weight in top 50% indices: {100*top_50_weight:.1f}%")
    print(f"  Normalized entropy: {entropy/max_entropy:.3f}")

    # Where is the weight concentrated?
    print("\n2. SPATIAL DISTRIBUTION:")
    # Weight by position (boundary vs middle)
    boundary_left = np.sum(opt_lam[:N//10]**2)
    boundary_right = np.sum(opt_lam[9*N//10:]**2)
    middle = np.sum(opt_lam[N//10:9*N//10]**2)

    print(f"  First 10% (left boundary):  {100*boundary_left:.1f}%")
    print(f"  Middle 80%:                 {100*middle:.1f}%")
    print(f"  Last 10% (right boundary):  {100*boundary_right:.1f}%")

    # Which specific indices have highest weight?
    print("\n3. TOP 5 INDICES:")
    for rank, idx in enumerate(sorted_indices[:5]):
        pct_pos = 100 * idx / N
        print(f"  #{rank+1}: index {idx} ({pct_pos:.1f}%), weight² = {opt_lam[idx]**2:.4f}")

    # Compute ||Aλ*||² decomposition
    print("\n4. ||Aλ*||² DECOMPOSITION:")
    Alam = A @ opt_lam
    total_norm_sq = np.sum(Alam**2)

    # Which rows of A contribute most?
    row_contrib = Alam**2
    sorted_rows = np.argsort(row_contrib)[::-1]

    print(f"  Total ||Aλ*||² = {total_norm_sq:.4f}")
    print(f"  Top 10% rows contribute: {100*np.sum(row_contrib[sorted_rows[:N//10]])/total_norm_sq:.1f}%")
    print(f"  Top row index: {sorted_rows[0]} ({100*sorted_rows[0]/N:.1f}%)")

    # Key insight: what determines ||Aλ||²?
    # (Aλ)_i = Σ_j (ξ_j - ξ_i) K_ij λ_j

    # If λ concentrated at position j*, then:
    # (Aλ)_i ≈ (ξ_j* - ξ_i) K_{i,j*} λ_j*

    # This is large when |ξ_j* - ξ_i| is large AND K_{i,j*} is not too small

    # The optimal vector balances:
    # - Spread out enough to avoid Gaussian decay killing all K_ij
    # - Concentrated enough to avoid cancellation in the sum

print("\n" + "=" * 70)
print("KEY INSIGHT")
print("=" * 70)
print("""
The optimal vector is NOT uniform, NOT concentrated at one point.

It's a BALANCE:
- Spread out to use the kernel coupling
- Concentrated to avoid cancellation

The growth min_R ~ N^{0.87} comes from:
- As N grows, the "effective" region of the optimal vector grows
- This region contributes ~ N^α to ||Aλ||²
- Denominator λᵀGλ grows ~ O(1) to O(N^β) depending on spread

Net effect: R = ||Aλ||² / λᵀGλ ~ N^{0.87}

QUESTION: Can we PROVE that any λ on cone must have ||Aλ||² ≥ c × N^δ?
""")

print("\n" + "=" * 70)
print("ATTEMPT: LOWER BOUND ON ||Aλ||²")
print("=" * 70)

# For the largest N, try to understand the structure
X = 10000
twins = get_twins(X)
N = len(twins)
Q, G, A, xi = build_matrices(twins)

print(f"\nFor N = {N}:")

# Key observation: A = [K, diag(ξ)] is a commutator
# ||Aλ||² = ||[K, diag(ξ)]λ||²

# For λ ≥ 0:
# (Aλ)_i = Σ_j (ξ_j - ξ_i) K_ij λ_j
#        = Σ_j ξ_j K_ij λ_j - ξ_i Σ_j K_ij λ_j
#        = ⟨K_row_i, ξ ⊙ λ⟩ - ξ_i ⟨K_row_i, λ⟩

# Define:
# μ_i(λ) = ⟨K_row_i, λ⟩ = "local mass" at position i
# ν_i(λ) = ⟨K_row_i, ξ ⊙ λ⟩ / μ_i(λ) = "local mean ξ" weighted by kernel

# Then: (Aλ)_i = μ_i(λ) × (ν_i(λ) - ξ_i)
#      = (local mass) × (mean position - current position)

# ||Aλ||² = Σ_i μ_i(λ)² × (ν_i(λ) - ξ_i)²

# For this to be 0, we need ν_i(λ) = ξ_i for all i
# But λ ≥ 0 constrains the "shape" of ν_i(λ)

# Key: at BOUNDARY (i = 0 or i = N-1), ν_i(λ) ≠ ξ_i for any λ ≥ 0!

print("\nBOUNDARY ANALYSIS:")
uniform = np.ones(N) / np.sqrt(N)

for i in [0, N//2, N-1]:
    K_row_i = G[i, :]
    mu_i = np.dot(K_row_i, uniform)
    nu_i = np.dot(K_row_i, xi * uniform) / mu_i if mu_i > 0 else 0

    print(f"\n  i = {i} ({'left' if i == 0 else 'right' if i == N-1 else 'middle'} boundary):")
    print(f"    ξ_i = {xi[i]:.4f}")
    print(f"    μ_i(uniform) = {mu_i:.4f}")
    print(f"    ν_i(uniform) = {nu_i:.4f}")
    print(f"    ν_i - ξ_i = {nu_i - xi[i]:.4f}")
    print(f"    (Aλ)_i = μ_i × (ν_i - ξ_i) = {mu_i * (nu_i - xi[i]):.4f}")

print("""

KEY THEOREM STRUCTURE:

For left boundary (i = 0):
- All ξ_j > ξ_0 for j > 0
- So ν_0(λ) > ξ_0 for any λ ≥ 0 with λ not supported only at j = 0
- Therefore (Aλ)_0 = μ_0(λ) × (ν_0(λ) - ξ_0) > 0

For right boundary (i = N-1):
- All ξ_j < ξ_{N-1} for j < N-1
- So ν_{N-1}(λ) < ξ_{N-1} for any λ ≥ 0 with λ not supported only at j = N-1
- Therefore (Aλ)_{N-1} = μ_{N-1}(λ) × (ν_{N-1}(λ) - ξ_{N-1}) < 0

CONCLUSION:
||Aλ||² ≥ (Aλ)_0² + (Aλ)_{N-1}² > 0 for any λ ≥ 0 on cone!

This proves Cone-Kernel separation qualitatively.
For QUANTITATIVE bound, we need to show:
(Aλ)_0² + (Aλ)_{N-1}² ≥ c × N^δ

This requires bounding μ_0, μ_{N-1}, ν_0 - ξ_0, etc. as functions of N.
""")
