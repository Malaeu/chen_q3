#!/usr/bin/env python3
"""
Lagrangian approach: solve generalized eigenvalue problem Qλ = μGλ
and analyze the eigenvalue structure.

Physics interpretation:
- μ_i are the "natural frequencies" of the system
- Nature chooses the minimal μ (least action)
- On cone: μ_min > 0 (Cone-Kernel theorem)
"""

import numpy as np
from scipy.linalg import eigh

def primes_up_to(n):
    """Sieve of Eratosthenes"""
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, n + 1, i):
                sieve[j] = False
    return [i for i in range(n + 1) if sieve[i]]

def twin_primes_up_to(X):
    """Get twin prime pairs (p, p+2) up to X"""
    primes = set(primes_up_to(X + 2))
    twins = [(p, p+2) for p in primes if p + 2 in primes and p + 2 <= X]
    return sorted(twins)

def build_matrices(twins, t=1.0):
    """Build Q = AᵀA and G matrices"""
    N = len(twins)
    primes = [p for p, _ in twins]
    xi = np.array([np.log(p) / (2 * np.pi) for p in primes])

    # Kernel K and Gram G
    K = np.zeros((N, N))
    G = np.zeros((N, N))

    for i in range(N):
        for j in range(N):
            delta = xi[i] - xi[j]
            K[i, j] = 2 * np.pi * t * np.exp(-delta**2 / (4 * t))
            G[i, j] = np.sqrt(2 * np.pi * t) * np.exp(-delta**2 / (8 * t))

    # Commutator matrix A
    A = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            A[i, j] = (xi[j] - xi[i]) * K[i, j]

    # Q = AᵀA
    Q = A.T @ A

    return Q, G, A, xi, primes

def analyze_lagrangian(X_values):
    """Analyze generalized eigenvalue problem Qλ = μGλ"""

    print("=" * 70)
    print("LAGRANGIAN ANALYSIS: Qλ = μGλ")
    print("=" * 70)
    print()
    print("Physical interpretation:")
    print("  μ_i = 'natural frequencies' of the spectral system")
    print("  min(μ) = minimum Rayleigh quotient on eigenvector directions")
    print()

    results = []

    for X in X_values:
        twins = twin_primes_up_to(X)
        N = len(twins)
        if N < 3:
            continue

        Q, G, A, xi, primes = build_matrices(twins)

        # Solve generalized eigenvalue problem: Qv = μGv
        # Add small regularization to G if needed
        try:
            # Check if G is positive definite
            G_eigs = np.linalg.eigvalsh(G)
            min_G_eig = np.min(G_eigs)
            if min_G_eig < 1e-10:
                # Add regularization
                G_reg = G + 1e-8 * np.eye(N)
                print(f"  (regularized G: min_eig was {min_G_eig:.2e})")
            else:
                G_reg = G

            eigenvalues, eigenvectors = eigh(Q, G_reg)
        except Exception as e:
            print(f"X={X}: Eigenvalue computation failed: {e}")
            continue

        # Sort by eigenvalue
        idx = np.argsort(eigenvalues)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]

        mu_min = eigenvalues[0]
        mu_max = eigenvalues[-1]
        mu_median = np.median(eigenvalues)

        # Check if eigenvectors are in cone
        v_min = eigenvectors[:, 0]
        v_max = eigenvectors[:, -1]

        in_cone_min = np.all(v_min >= -1e-10) or np.all(v_min <= 1e-10)
        in_cone_max = np.all(v_max >= -1e-10) or np.all(v_max <= 1e-10)

        # Twin weights Φ_X
        lambda_twin = np.array([np.log(p) * np.log(p+2) for p, _ in twins])
        lambda_twin = lambda_twin / np.linalg.norm(lambda_twin)

        R_twin = (lambda_twin @ Q @ lambda_twin) / (lambda_twin @ G @ lambda_twin)

        # Span
        span = xi[-1] - xi[0]

        results.append({
            'X': X, 'N': N, 'span': span,
            'mu_min': mu_min, 'mu_max': mu_max, 'mu_median': mu_median,
            'R_twin': R_twin,
            'in_cone_min': in_cone_min, 'in_cone_max': in_cone_max,
            'v_min_pos': np.sum(v_min > 0), 'v_min_neg': np.sum(v_min < 0),
            'eigenvalues': eigenvalues
        })

        print(f"X={X:6d} | N={N:4d} | span={span:.2f}")
        print(f"  μ_min={mu_min:.4f} | μ_max={mu_max:.2f} | μ_med={mu_median:.2f}")
        print(f"  R(Φ_X)={R_twin:.4f}")
        print(f"  v_min: {np.sum(v_min>0)}/{N} positive, in_cone={in_cone_min}")
        print(f"  μ_min/span²={mu_min/span**2:.6f}")
        print()

    # Power law fits
    if len(results) >= 3:
        X_arr = np.array([r['X'] for r in results])
        N_arr = np.array([r['N'] for r in results])
        span_arr = np.array([r['span'] for r in results])
        mu_min_arr = np.array([r['mu_min'] for r in results])
        mu_max_arr = np.array([r['mu_max'] for r in results])

        print("=" * 70)
        print("POWER LAW ANALYSIS")
        print("=" * 70)

        # Fit μ_min ~ c * N^α
        log_N = np.log(N_arr)
        log_mu_min = np.log(np.maximum(mu_min_arr, 1e-10))

        coeffs = np.polyfit(log_N, log_mu_min, 1)
        alpha_N = coeffs[0]
        c_N = np.exp(coeffs[1])
        print(f"\nμ_min ~ {c_N:.4f} × N^{alpha_N:.3f}")

        # Fit μ_min ~ c * span^β
        log_span = np.log(span_arr)
        coeffs = np.polyfit(log_span, log_mu_min, 1)
        beta_span = coeffs[0]
        c_span = np.exp(coeffs[1])
        print(f"μ_min ~ {c_span:.4f} × span^{beta_span:.3f}")

        # Key ratio: μ_min / span²
        ratio = mu_min_arr / span_arr**2
        print(f"\nμ_min / span² = {ratio}")
        print(f"  mean = {np.mean(ratio):.6f}")
        print(f"  std  = {np.std(ratio):.6f}")
        print(f"  CV   = {np.std(ratio)/np.mean(ratio)*100:.1f}%")

        # μ_max analysis
        log_mu_max = np.log(mu_max_arr)
        coeffs = np.polyfit(log_N, log_mu_max, 1)
        print(f"\nμ_max ~ N^{coeffs[0]:.3f}")

        print()
        print("=" * 70)
        print("LAGRANGIAN CONCLUSION")
        print("=" * 70)
        print()
        print("If μ_min ~ span^β with β > 0:")
        print("  Then R(λ) ≥ μ_min → ∞ as span → ∞")
        print("  Combined with SC2: finite twins ⟹ R = O(1)")
        print("  ⟹ CONTRADICTION ⟹ INFINITE TWINS!")
        print()
        if beta_span > 0.5:
            print(f"✅ β = {beta_span:.3f} > 0.5 — STRONG growth!")
        elif beta_span > 0:
            print(f"⚠️ β = {beta_span:.3f} > 0 — growth exists but may need refinement")
        else:
            print(f"❌ β = {beta_span:.3f} ≤ 0 — no growth from eigenvalues")

    return results

if __name__ == "__main__":
    X_values = [100, 500, 1000, 2000, 5000, 10000, 20000]
    results = analyze_lagrangian(X_values)
