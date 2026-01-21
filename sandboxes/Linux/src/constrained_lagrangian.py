#!/usr/bin/env python3
"""
Constrained Lagrangian: minimize R = λᵀQλ/λᵀGλ on CONE.

Key insight from unconstrained analysis:
- Global μ_min ≈ 0, but eigenvector is NOT in cone
- Cone constraint FORCES R > 0
- This is like conservation laws in physics!

Approach: Use KKT conditions or direct optimization on cone.
"""

import numpy as np
from scipy.optimize import minimize
from scipy.linalg import eigh

def primes_up_to(n):
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, n + 1, i):
                sieve[j] = False
    return [i for i in range(n + 1) if sieve[i]]

def twin_primes_up_to(X):
    primes = set(primes_up_to(X + 2))
    twins = [(p, p+2) for p in primes if p + 2 in primes and p + 2 <= X]
    return sorted(twins)

def build_matrices(twins, t=1.0):
    N = len(twins)
    primes = [p for p, _ in twins]
    xi = np.array([np.log(p) / (2 * np.pi) for p in primes])

    K = np.zeros((N, N))
    G = np.zeros((N, N))

    for i in range(N):
        for j in range(N):
            delta = xi[i] - xi[j]
            K[i, j] = 2 * np.pi * t * np.exp(-delta**2 / (4 * t))
            G[i, j] = np.sqrt(2 * np.pi * t) * np.exp(-delta**2 / (8 * t))

    A = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            A[i, j] = (xi[j] - xi[i]) * K[i, j]

    Q = A.T @ A
    return Q, G, A, xi, primes

def rayleigh_on_cone(Q, G, normalize=True):
    """
    Find minimum Rayleigh quotient R = λᵀQλ/λᵀGλ on cone C = {λ ≥ 0}.

    Uses direct optimization with positivity constraints.
    """
    N = Q.shape[0]

    def neg_R(lam):
        """Negative R for minimization (actually we minimize R directly)"""
        lam = np.maximum(lam, 1e-15)  # Ensure positivity
        E_comm = lam @ Q @ lam
        E_lat = lam @ G @ lam
        if E_lat < 1e-15:
            return 1e10
        return E_comm / E_lat

    # Multiple random starts in cone
    best_R = np.inf
    best_lam = None

    for trial in range(20):
        # Random positive start
        x0 = np.abs(np.random.randn(N)) + 0.1

        # Bounds: λ_i ≥ 0
        bounds = [(1e-10, None) for _ in range(N)]

        result = minimize(neg_R, x0, method='L-BFGS-B', bounds=bounds)

        if result.fun < best_R:
            best_R = result.fun
            best_lam = result.x

    if normalize and best_lam is not None:
        best_lam = best_lam / np.linalg.norm(best_lam)

    return best_R, best_lam

def analyze_constrained(X_values):
    """Compare unconstrained vs cone-constrained minima."""

    print("=" * 70)
    print("CONSTRAINED vs UNCONSTRAINED LAGRANGIAN")
    print("=" * 70)
    print()
    print("Physics insight:")
    print("  Unconstrained: system falls to μ_min ≈ 0 (outside cone)")
    print("  Constrained:   cone is like 'conservation law' forcing R > 0")
    print()

    results = []

    for X in X_values:
        twins = twin_primes_up_to(X)
        N = len(twins)
        if N < 3:
            continue

        Q, G, A, xi, primes = build_matrices(twins)
        span = xi[-1] - xi[0]

        # Unconstrained: generalized eigenvalue
        try:
            G_reg = G + 1e-10 * np.eye(N)
            eigenvalues, eigenvectors = eigh(Q, G_reg)
            mu_min_unconstrained = eigenvalues[0]
            v_unconstrained = eigenvectors[:, 0]
            in_cone_unconstrained = np.all(v_unconstrained >= -1e-10) or np.all(v_unconstrained <= 1e-10)
        except:
            mu_min_unconstrained = np.nan
            in_cone_unconstrained = False

        # Constrained: optimization on cone
        R_cone, lam_cone = rayleigh_on_cone(Q, G)

        # Twin weights
        lambda_twin = np.array([np.log(p) * np.log(p+2) for p, _ in twins])
        lambda_twin = lambda_twin / np.linalg.norm(lambda_twin)
        R_twin = (lambda_twin @ Q @ lambda_twin) / (lambda_twin @ G @ lambda_twin)

        results.append({
            'X': X, 'N': N, 'span': span,
            'mu_unconstrained': mu_min_unconstrained,
            'in_cone_unconstrained': in_cone_unconstrained,
            'R_cone': R_cone,
            'R_twin': R_twin
        })

        print(f"X={X:6d} | N={N:4d} | span={span:.2f}")
        print(f"  Unconstrained μ_min = {mu_min_unconstrained:.6f} (in cone: {in_cone_unconstrained})")
        print(f"  Constrained min_cone R = {R_cone:.4f}")
        print(f"  R(Φ_X) = {R_twin:.4f}")
        print(f"  Ratio: R_cone/span² = {R_cone/span**2:.4f}")
        print()

    # Power law analysis
    if len(results) >= 3:
        N_arr = np.array([r['N'] for r in results])
        span_arr = np.array([r['span'] for r in results])
        R_cone_arr = np.array([r['R_cone'] for r in results])
        R_twin_arr = np.array([r['R_twin'] for r in results])

        print("=" * 70)
        print("POWER LAW FITS (Constrained)")
        print("=" * 70)

        # Fit R_cone ~ c * N^α
        log_N = np.log(N_arr)
        log_R = np.log(R_cone_arr)
        coeffs = np.polyfit(log_N, log_R, 1)
        print(f"\nmin_cone R ~ {np.exp(coeffs[1]):.4f} × N^{coeffs[0]:.3f}")

        # Fit R_cone ~ c * span^β
        log_span = np.log(span_arr)
        coeffs_span = np.polyfit(log_span, log_R, 1)
        print(f"min_cone R ~ {np.exp(coeffs_span[1]):.4f} × span^{coeffs_span[0]:.3f}")

        # Key ratio
        ratio = R_cone_arr / span_arr**2
        print(f"\nR_cone / span² = {ratio}")
        print(f"  mean = {np.mean(ratio):.4f}")
        print(f"  CV = {np.std(ratio)/np.mean(ratio)*100:.1f}%")

        print()
        print("=" * 70)
        print("🔥 LAGRANGIAN CONCLUSION")
        print("=" * 70)
        print()
        print("The cone constraint is FUNDAMENTAL!")
        print()
        print(f"Unconstrained: μ_min ≈ 0 (eigenvector outside cone)")
        print(f"Constrained:   min_cone R ~ N^{coeffs[0]:.2f} ~ span^{coeffs_span[0]:.2f}")
        print()

        if coeffs_span[0] > 1.5:
            print("✅ Strong growth: R_cone ~ span^{:.2f} → ∞".format(coeffs_span[0]))
            print("   Combined with SC2 gives CONTRADICTION!")
        elif coeffs_span[0] > 0:
            print("⚠️ Growth exists but needs: R_cone ~ span^{:.2f}".format(coeffs_span[0]))
        else:
            print("❌ No growth detected")

    return results

if __name__ == "__main__":
    X_values = [100, 500, 1000, 2000, 5000, 10000]
    results = analyze_constrained(X_values)
