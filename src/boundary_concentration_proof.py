#!/usr/bin/env python3
"""
PROOF ATTEMPT: Lower bound via boundary concentration

KEY OBSERVATION: Optimal vector λ* ≈ a·δ₀ + b·δ_{N-1}

This means the minimum of R(λ) on cone is achieved by vectors
concentrated at BOTH boundaries!

STRATEGY:
1. Compute R for 2-parameter family: λ = a·e₀ + b·e_{N-1}
2. Minimize over (a, b) with a, b ≥ 0
3. Show that this minimum grows as N^δ for some δ > 0
"""

import numpy as np
from scipy.optimize import minimize_scalar, minimize
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

def R_boundary_family(a, b, Q, G):
    """
    Compute R(λ) for λ = a·e₀ + b·e_{N-1}

    R(λ) = (a²Q₀₀ + 2ab Q_{0,N-1} + b²Q_{N-1,N-1}) /
           (a²G₀₀ + 2ab G_{0,N-1} + b²G_{N-1,N-1})
    """
    N = Q.shape[0]
    num = a**2 * Q[0, 0] + 2*a*b * Q[0, N-1] + b**2 * Q[N-1, N-1]
    den = a**2 * G[0, 0] + 2*a*b * G[0, N-1] + b**2 * G[N-1, N-1]
    if den < 1e-10:
        return 1e10
    return num / den

def min_boundary_R(Q, G):
    """
    Minimize R over the boundary family λ = a·e₀ + b·e_{N-1} with a,b ≥ 0.

    Can parametrize by angle: a = cos(θ), b = sin(θ), θ ∈ [0, π/2]
    """
    N = Q.shape[0]

    def R_theta(theta):
        a = np.cos(theta)
        b = np.sin(theta)
        return R_boundary_family(a, b, Q, G)

    # Grid search + refinement
    best_R = np.inf
    best_theta = 0
    for theta in np.linspace(0, np.pi/2, 100):
        R = R_theta(theta)
        if R < best_R:
            best_R = R
            best_theta = theta

    # Refine
    result = minimize_scalar(R_theta, bounds=(max(0, best_theta - 0.1),
                                               min(np.pi/2, best_theta + 0.1)),
                            method='bounded')
    if result.fun < best_R:
        best_R = result.fun
        best_theta = result.x

    a = np.cos(best_theta)
    b = np.sin(best_theta)
    return best_R, a, b

print("=" * 70)
print("BOUNDARY CONCENTRATION ANALYSIS")
print("=" * 70)

X_values = [500, 1000, 2000, 5000, 10000, 20000, 50000]

results = []
for X in X_values:
    twins = get_twins(X)
    N = len(twins)
    if N < 10:
        continue

    Q, G, A, xi = build_matrices(twins)

    # Minimum on boundary family
    min_R_boundary, a, b = min_boundary_R(Q, G)

    # Key matrix elements
    Q_00 = Q[0, 0]
    Q_NN = Q[N-1, N-1]
    Q_0N = Q[0, N-1]
    G_00 = G[0, 0]
    G_NN = G[N-1, N-1]
    G_0N = G[0, N-1]

    # For comparison: actual min on full cone
    from scipy.optimize import minimize as scipy_min
    def R_full(lam):
        lam = np.maximum(lam, 1e-10)
        lam = lam / np.linalg.norm(lam)
        return (lam @ Q @ lam) / (lam @ G @ lam)

    best_full = np.inf
    for _ in range(100):
        x0 = np.random.exponential(size=N)
        try:
            result = scipy_min(R_full, x0, method='L-BFGS-B', bounds=[(1e-10, None)]*N)
            if result.fun < best_full:
                best_full = result.fun
        except:
            pass

    results.append({
        'N': N,
        'min_R_boundary': min_R_boundary,
        'min_R_full': best_full,
        'a': a, 'b': b,
        'Q_00': Q_00, 'Q_NN': Q_NN, 'Q_0N': Q_0N,
        'G_00': G_00, 'G_NN': G_NN, 'G_0N': G_0N
    })

    print(f"\nN = {N}:")
    print(f"  min R (boundary family) = {min_R_boundary:.4f}")
    print(f"  min R (full cone)       = {best_full:.4f}")
    print(f"  ratio                   = {min_R_boundary/best_full:.3f}")
    print(f"  optimal (a, b) = ({a:.3f}, {b:.3f})")

print("\n" + "=" * 70)
print("SCALING ANALYSIS")
print("=" * 70)

N_arr = np.array([r['N'] for r in results])
boundary_arr = np.array([r['min_R_boundary'] for r in results])
full_arr = np.array([r['min_R_full'] for r in results])

# Power law fits
def fit_power(x, y):
    log_x = np.log(x)
    log_y = np.log(y)
    coeffs = np.polyfit(log_x, log_y, 1)
    return coeffs[0], np.exp(coeffs[1])

exp_boundary, pref_boundary = fit_power(N_arr, boundary_arr)
exp_full, pref_full = fit_power(N_arr, full_arr)

print(f"\nmin R (boundary family) ~ {pref_boundary:.4f} × N^{exp_boundary:.4f}")
print(f"min R (full cone)       ~ {pref_full:.4f} × N^{exp_full:.4f}")

print("\n" + "=" * 70)
print("KEY MATRIX ELEMENTS SCALING")
print("=" * 70)

Q_00_arr = np.array([r['Q_00'] for r in results])
Q_NN_arr = np.array([r['Q_NN'] for r in results])
G_00_arr = np.array([r['G_00'] for r in results])

exp_Q00, _ = fit_power(N_arr, Q_00_arr)
exp_QNN, _ = fit_power(N_arr, Q_NN_arr)
exp_G00, _ = fit_power(N_arr, G_00_arr)

print(f"Q[0,0]   ~ N^{exp_Q00:.3f}")
print(f"Q[N-1,N-1] ~ N^{exp_QNN:.3f}")
print(f"G[0,0]   ~ N^{exp_G00:.3f} (should be ~N^0 = const)")

print("\n" + "=" * 70)
print("THEORETICAL PREDICTION")
print("=" * 70)

print("""
For λ = e_0 (pure left boundary):
R(e_0) = Q[0,0] / G[0,0]

Q[0,0] = Σ_i A[i,0]² = Σ_i [(ξ_0 - ξ_i) K_{i0}]²
       = Σ_i (ξ_i - ξ_0)² K_{i0}²

For Gaussian kernel with width √t:
- K_{i0}² significant only for |ξ_i - ξ_0| ≲ √t
- For twins: spacing between consecutive ξ is ~ 1/(N × density)
- Number of twins within √t of ξ_0: ~ √t × N × density = O(√N) or O(N)
  depending on twin density scaling

Actually, numerical shows Q[0,0] ~ N^{1.0-1.1}, suggesting ~N terms each O(1).

G[0,0] = K(0) = √(2πt) = const

So R(e_0) = Q[0,0]/G[0,0] ~ N^{1.0-1.1}

This gives a lower bound: min_R ≤ R(e_0) ~ N^{1.1}
(Actually upper bound since e_0 may not be optimal)

The fact that min_R_boundary and min_R_full both scale as N^{0.87-0.89}
suggests that the boundary family is close to optimal.

THEOREM STRUCTURE:
1. Q[0,0], Q[N-1,N-1] ~ N^α for some α > 0  [Provable from structure]
2. G[0,0], G[N-1,N-1] = √(2πt) = const     [Exact]
3. min_{a,b≥0} R(a e_0 + b e_{N-1}) ~ N^{α-ε}  [From 1, 2 + optimization]
4. min_cone R ≤ min_boundary R ~ N^{α-ε}    [Upper bound]
5. min_cone R ≥ some_lower_bound?            [Need to prove!]

KEY GAP: We have upper bound from boundary family.
Need lower bound showing min_cone R ≥ c × N^δ for δ > 0.
""")

# Numerical verification of Q[0,0] structure
print("\n" + "=" * 70)
print("Q[0,0] STRUCTURE ANALYSIS")
print("=" * 70)

X = 10000
twins = get_twins(X)
N = len(twins)
Q, G, A, xi = build_matrices(twins)

print(f"\nFor N = {N}:")
print(f"Q[0,0] = {Q[0,0]:.4f}")
print(f"G[0,0] = {G[0,0]:.4f}")
print(f"R(e_0) = Q[0,0]/G[0,0] = {Q[0,0]/G[0,0]:.4f}")

# Decompose Q[0,0]
A_col_0 = A[:, 0]  # Column 0 of A
print(f"\nQ[0,0] = ||A[:, 0]||² = Σ_i A[i,0]²")
print(f"       = Σ_i [(ξ_0 - ξ_i) K_{i0}]²")

# Analyze by region
contrib_near = np.sum(A_col_0[:N//10]**2)
contrib_mid = np.sum(A_col_0[N//10:9*N//10]**2)
contrib_far = np.sum(A_col_0[9*N//10:]**2)

print(f"\nContribution to Q[0,0] by region:")
print(f"  First 10%:  {contrib_near:.4f} ({100*contrib_near/Q[0,0]:.1f}%)")
print(f"  Middle 80%: {contrib_mid:.4f} ({100*contrib_mid/Q[0,0]:.1f}%)")
print(f"  Last 10%:   {contrib_far:.4f} ({100*contrib_far/Q[0,0]:.1f}%)")

# Each term (ξ_i - ξ_0)² K_{i0}²
# For small i: ξ_i - ξ_0 small, K large -> moderate
# For large i: ξ_i - ξ_0 large, K small -> depends on balance

print(f"\nSample terms A[i,0]² = [(ξ_i - ξ_0) K_{{i0}}]²:")
for i in [1, N//10, N//2, 9*N//10, N-1]:
    term = A_col_0[i]**2
    dist = xi[i] - xi[0]
    K = G[i, 0]
    print(f"  i={i}: (ξ_i - ξ_0)={dist:.4f}, K={K:.4f}, term={term:.4f}")
