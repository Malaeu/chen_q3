#!/usr/bin/env python3
"""
GOAL: Understand WHY c = min_cone R / [Tr(Q)/Tr(G)] ≈ 0.486 is stable

This is the key to closing the gap in the proof.
"""

import numpy as np
from scipy.optimize import minimize
from scipy.linalg import eigh

# =============================================================================
# Part 1: Numerical deep dive - understand the STRUCTURE
# =============================================================================

def get_twins(X_max):
    """Get twin primes up to X_max"""
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
    """Build Q and G matrices for twin primes"""
    N = len(twins)
    xi = np.log(twins) / (2 * np.pi)

    # Gram matrix G
    G = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = xi[i] - xi[j]
            G[i, j] = np.sqrt(2 * np.pi * t) * np.exp(-delta**2 / (4 * t))

    # Commutator matrix A
    A = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = xi[j] - xi[i]
            K_ij = np.sqrt(2 * np.pi * t) * np.exp(-delta**2 / (4 * t))
            A[i, j] = delta * K_ij

    # Q = A^T A
    Q = A.T @ A

    return Q, G, A, xi

def min_on_cone(Q, G, n_trials=100):
    """Find minimum of R(λ) = λᵀQλ / λᵀGλ on cone"""
    N = Q.shape[0]

    def R(lam):
        lam = np.abs(lam)  # Stay on cone
        lam = lam / np.linalg.norm(lam)
        num = lam @ Q @ lam
        den = lam @ G @ lam
        return num / den

    best_R = np.inf
    best_lam = None

    for _ in range(n_trials):
        x0 = np.random.exponential(size=N)
        x0 = x0 / np.linalg.norm(x0)

        result = minimize(R, x0, method='L-BFGS-B',
                         bounds=[(0, None)] * N)

        if result.fun < best_R:
            best_R = result.fun
            best_lam = np.abs(result.x)

    return best_R, best_lam / np.linalg.norm(best_lam)

def analyze_structure(X_values):
    """Deep analysis of why c is constant"""

    print("=" * 70)
    print("STRUCTURAL ANALYSIS: Why c ≈ 0.486?")
    print("=" * 70)

    results = []

    for X in X_values:
        twins = get_twins(X)
        N = len(twins)
        if N < 5:
            continue

        Q, G, A, xi = build_matrices(twins)

        # Key quantities
        Tr_Q = np.trace(Q)
        Tr_G = np.trace(G)
        Sum_Q = np.sum(Q)
        Sum_G = np.sum(G)

        # Min on cone
        min_R, opt_lam = min_on_cone(Q, G)

        # Uniform vector
        uniform = np.ones(N) / np.sqrt(N)
        R_uniform = (uniform @ Q @ uniform) / (uniform @ G @ uniform)

        # Ratios
        c = min_R / (Tr_Q / Tr_G)
        ratio_sum = Sum_Q / Sum_G
        ratio_tr = Tr_Q / Tr_G

        # Diagonal vs off-diagonal
        diag_Q = np.diag(Q)
        offdiag_Q = Q - np.diag(diag_Q)

        diag_G = np.diag(G)
        offdiag_G = G - np.diag(diag_G)

        # Key structural ratios
        alpha = np.sum(offdiag_Q) / np.sum(diag_Q)  # off/diag ratio for Q
        beta = np.sum(offdiag_G) / np.sum(diag_G)   # off/diag ratio for G

        results.append({
            'X': X, 'N': N,
            'min_R': min_R,
            'R_uniform': R_uniform,
            'Tr_Q': Tr_Q, 'Tr_G': Tr_G,
            'Sum_Q': Sum_Q, 'Sum_G': Sum_G,
            'c': c,
            'ratio_tr': ratio_tr,
            'ratio_sum': ratio_sum,
            'alpha': alpha, 'beta': beta,
            'opt_lam': opt_lam
        })

        print(f"\nX = {X}, N = {N}")
        print(f"  min_cone R = {min_R:.4f}")
        print(f"  R(uniform) = {R_uniform:.4f}")
        print(f"  Tr(Q)/Tr(G) = {ratio_tr:.4f}")
        print(f"  Sum(Q)/Sum(G) = {ratio_sum:.4f}")
        print(f"  c = min_R / [Tr(Q)/Tr(G)] = {c:.6f}")
        print(f"  α = off(Q)/diag(Q) = {alpha:.4f}")
        print(f"  β = off(G)/diag(G) = {beta:.4f}")
        print(f"  min_R / R_uniform = {min_R / R_uniform:.6f}")

    return results

def find_analytical_pattern(results):
    """Look for analytical pattern in c"""

    print("\n" + "=" * 70)
    print("PATTERN SEARCH")
    print("=" * 70)

    # Extract data
    N_vals = np.array([r['N'] for r in results])
    c_vals = np.array([r['c'] for r in results])
    alpha_vals = np.array([r['alpha'] for r in results])
    beta_vals = np.array([r['beta'] for r in results])

    # Test: c = f(α, β)?
    print("\n1. Testing c = α / (1 + α) / [β / (1 + β)]...")
    pred1 = (alpha_vals / (1 + alpha_vals)) / (beta_vals / (1 + beta_vals))
    print(f"   Predicted: {pred1}")
    print(f"   Actual c:  {c_vals}")
    print(f"   Ratio:     {c_vals / pred1}")

    # Test: c = 1/2 as N → ∞?
    print("\n2. Is c → 1/2?")
    print(f"   c values: {c_vals}")
    print(f"   Mean: {np.mean(c_vals):.6f}")
    print(f"   Std:  {np.std(c_vals):.6f}")

    # Test: c related to Sum/Tr ratio?
    sum_tr_ratio = np.array([r['ratio_sum'] / r['ratio_tr'] for r in results])
    print("\n3. Is c = Sum(Q)/Sum(G) / [Tr(Q)/Tr(G)]?")
    print(f"   Sum/Tr ratio: {sum_tr_ratio}")
    print(f"   Actual c:     {c_vals}")
    print(f"   Difference:   {c_vals - sum_tr_ratio}")

    # Test: min_R vs R_uniform
    min_uniform_ratio = np.array([r['min_R'] / r['R_uniform'] for r in results])
    print("\n4. min_R / R_uniform:")
    print(f"   Ratios: {min_uniform_ratio}")
    print(f"   Mean:   {np.mean(min_uniform_ratio):.6f}")

    # Key insight: if uniform is nearly optimal, then
    # min_R ≈ R_uniform = Sum(Q)/Sum(G)
    # and c = min_R / [Tr(Q)/Tr(G)] ≈ [Sum(Q)/Sum(G)] / [Tr(Q)/Tr(G)]
    #       = Sum(Q)/Tr(Q) × Tr(G)/Sum(G)

    sum_over_tr_Q = np.array([r['Sum_Q'] / r['Tr_Q'] for r in results])
    tr_over_sum_G = np.array([r['Tr_G'] / r['Sum_G'] for r in results])
    predicted_c = sum_over_tr_Q * tr_over_sum_G

    print("\n5. c ≈ [Sum(Q)/Tr(Q)] × [Tr(G)/Sum(G)]?")
    print(f"   Predicted: {predicted_c}")
    print(f"   Actual:    {c_vals}")
    print(f"   Ratio:     {c_vals / predicted_c}")

def prove_key_identity():
    """
    Try to prove analytically:

    For uniform λ = (1,...,1)/√N:
    R(uniform) = Sum(Q) / Sum(G)

    And: Sum(Q)/Sum(G) ≈ (1/2) × Tr(Q)/Tr(G) + corrections
    """

    print("\n" + "=" * 70)
    print("ANALYTICAL DERIVATION ATTEMPT")
    print("=" * 70)

    print("""
KEY IDENTITY TO PROVE:

For uniform vector λ = (1/√N, ..., 1/√N):

R(uniform) = λᵀQλ / λᵀGλ
           = (1/N) Σᵢⱼ Qᵢⱼ / (1/N) Σᵢⱼ Gᵢⱼ
           = Sum(Q) / Sum(G)

Now, let's decompose:

Sum(Q) = Tr(Q) + 2 × Σᵢ<ⱼ Qᵢⱼ  (off-diagonal sum)
Sum(G) = Tr(G) + 2 × Σᵢ<ⱼ Gᵢⱼ  (off-diagonal sum)

Define:
  α = [2 × Σᵢ<ⱼ Qᵢⱼ] / Tr(Q)  (off-diagonal fraction for Q)
  β = [2 × Σᵢ<ⱼ Gᵢⱼ] / Tr(G)  (off-diagonal fraction for G)

Then:
  Sum(Q) = Tr(Q) × (1 + α)
  Sum(G) = Tr(G) × (1 + β)

So:
  R(uniform) = Sum(Q)/Sum(G)
             = [Tr(Q)/Tr(G)] × [(1 + α)/(1 + β)]

And:
  c = min_R / [Tr(Q)/Tr(G)]
    ≈ R(uniform) / [Tr(Q)/Tr(G)]   (if uniform near-optimal)
    = (1 + α) / (1 + β)

NUMERICAL CHECK: Is (1 + α)/(1 + β) ≈ 0.49?
""")

def check_alpha_beta_formula(results):
    """Check if c = (1 + α)/(1 + β)"""

    print("\n" + "=" * 70)
    print("CHECKING c = (1 + α)/(1 + β)")
    print("=" * 70)

    for r in results:
        alpha = r['alpha']
        beta = r['beta']
        predicted = (1 + alpha) / (1 + beta)
        actual = r['c']

        print(f"N = {r['N']:3d}: α = {alpha:.3f}, β = {beta:.3f}, "
              f"(1+α)/(1+β) = {predicted:.4f}, c = {actual:.4f}, "
              f"ratio = {actual/predicted:.4f}")

def main():
    print("🔥 PROVING c > 0 FOR ALL N 🔥")
    print()

    # Analyze for range of X
    X_values = [100, 500, 1000, 2000, 5000, 10000]

    results = analyze_structure(X_values)

    find_analytical_pattern(results)

    prove_key_identity()

    check_alpha_beta_formula(results)

    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    print("""
If we can prove:

1. uniform vector is ε-optimal: min_R ≥ (1-ε) × R(uniform)
2. (1 + α)/(1 + β) bounded away from 0

Then c > 0 follows.

The key is that G has STRONGER off-diagonal coupling than Q
(because G is pure kernel, Q has derivative factor that decays faster).

This means β > α, so (1 + α)/(1 + β) < 1 but bounded away from 0.
""")

if __name__ == "__main__":
    main()
