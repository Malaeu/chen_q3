#!/usr/bin/env python3
"""
АНАЛИТИЧЕСКИЙ АНАЛИЗ: R на boundary family λ = a·e_0 + b·e_{N-1}

Цель: Понять ПОЧЕМУ R_min ~ N^{0.88} → ∞
"""

import numpy as np
from typing import Tuple

def get_twins(X: int) -> list:
    """Все twin primes до X."""
    sieve = [True] * (X + 3)
    sieve[0] = sieve[1] = False
    for i in range(2, int(X**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, X + 3, i):
                sieve[j] = False
    return [p for p in range(3, X + 1) if sieve[p] and sieve[p + 2]]

def build_matrices(twins: list, t: float = 1.0) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Build A, Q, G matrices."""
    N = len(twins)
    xi = np.array([np.log(p) / (2 * np.pi) for p in twins])

    K = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = xi[i] - xi[j]
            K[i, j] = 2 * np.pi * t * np.exp(-delta**2 / (4 * t))

    A = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            A[i, j] = (xi[j] - xi[i]) * K[i, j]

    Q = A.T @ A

    G = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = xi[i] - xi[j]
            G[i, j] = np.sqrt(2 * np.pi * t) * np.exp(-delta**2 / (8 * t))

    return A, Q, G

def compute_boundary_R(Q: np.ndarray, G: np.ndarray, a: float, b: float) -> float:
    """R для λ = a·e_0 + b·e_{N-1}"""
    N = Q.shape[0]

    # λᵀQλ = a²Q[0,0] + 2ab·Q[0,N-1] + b²Q[N-1,N-1]
    num = a**2 * Q[0,0] + 2*a*b*Q[0,N-1] + b**2 * Q[N-1,N-1]

    # λᵀGλ = a²G[0,0] + 2ab·G[0,N-1] + b²G[N-1,N-1]
    den = a**2 * G[0,0] + 2*a*b*G[0,N-1] + b**2 * G[N-1,N-1]

    return num / den if den > 1e-15 else 1e10

def find_boundary_minimum(Q: np.ndarray, G: np.ndarray) -> Tuple[float, float, float]:
    """Найти минимум R на boundary family."""
    best_R = np.inf
    best_a, best_b = 1.0, 0.0

    # Grid search
    for a in np.linspace(0.01, 1.0, 100):
        for b in np.linspace(0.01, 1.0, 100):
            # Normalize: a² + b² = 1
            norm = np.sqrt(a**2 + b**2)
            a_n, b_n = a/norm, b/norm

            R = compute_boundary_R(Q, G, a_n, b_n)
            if R < best_R:
                best_R = R
                best_a, best_b = a_n, b_n

    return best_R, best_a, best_b

def analyze_boundary_elements(Q: np.ndarray, G: np.ndarray) -> dict:
    """Анализ элементов на границе."""
    N = Q.shape[0]

    return {
        'Q_00': Q[0, 0],
        'Q_NN': Q[N-1, N-1],
        'Q_0N': Q[0, N-1],
        'G_00': G[0, 0],
        'G_NN': G[N-1, N-1],
        'G_0N': G[0, N-1],
        'span': np.sqrt(8) * np.sqrt(-np.log(G[0, N-1] / G[0, 0])),  # δ from Gaussian
    }

def main():
    print("=" * 70)
    print("АНАЛИЗ R НА BOUNDARY FAMILY: λ = a·e_0 + b·e_{N-1}")
    print("=" * 70)

    X_values = [500, 1000, 2000, 5000, 10000, 20000, 50000]
    results = []

    print("\n" + "=" * 70)
    print("ЧАСТЬ 1: R на границе vs R_min")
    print("=" * 70)
    print(f"{'X':>7} {'N':>5} {'R_bnd':>10} {'a*':>8} {'b*':>8} {'R_00':>10} {'R_NN':>10}")
    print("-" * 70)

    for X in X_values:
        twins = get_twins(X)
        N = len(twins)
        if N < 5:
            continue

        A, Q, G = build_matrices(twins)

        # Boundary minimum
        R_bnd, a_opt, b_opt = find_boundary_minimum(Q, G)

        # Corner values
        R_00 = Q[0,0] / G[0,0]
        R_NN = Q[N-1,N-1] / G[N-1,N-1]

        results.append({
            'X': X, 'N': N, 'R_bnd': R_bnd,
            'a': a_opt, 'b': b_opt,
            'R_00': R_00, 'R_NN': R_NN
        })

        print(f"{X:>7} {N:>5} {R_bnd:>10.2f} {a_opt:>8.4f} {b_opt:>8.4f} {R_00:>10.2f} {R_NN:>10.2f}")

    # Power law fit for R_bnd
    N_arr = np.array([r['N'] for r in results])
    R_bnd_arr = np.array([r['R_bnd'] for r in results])

    log_N = np.log(N_arr)
    log_R = np.log(R_bnd_arr)
    b_fit, log_a_fit = np.polyfit(log_N, log_R, 1)

    print(f"\n🎯 R_boundary ~ {np.exp(log_a_fit):.4f} × N^{{{b_fit:.4f}}}")

    print("\n" + "=" * 70)
    print("ЧАСТЬ 2: Структура элементов Q, G на границе")
    print("=" * 70)

    # Detailed analysis for X = 20000
    X_detail = 20000
    twins = get_twins(X_detail)
    N = len(twins)
    xi = np.array([np.log(p) / (2 * np.pi) for p in twins])
    A, Q, G = build_matrices(twins)

    elems = analyze_boundary_elements(Q, G)
    span = xi[-1] - xi[0]

    print(f"\nX = {X_detail}, N = {N}")
    print(f"span = ξ_{N-1} - ξ_0 = {span:.4f}")
    print(f"\nЭлементы Q:")
    print(f"  Q[0,0]   = {elems['Q_00']:.4f}")
    print(f"  Q[N-1,N-1] = {elems['Q_NN']:.4f}")
    print(f"  Q[0,N-1] = {elems['Q_0N']:.4f}")
    print(f"\nЭлементы G:")
    print(f"  G[0,0]   = {elems['G_00']:.4f}")
    print(f"  G[N-1,N-1] = {elems['G_NN']:.4f}")
    print(f"  G[0,N-1] = {elems['G_0N']:.4f}")
    print(f"  G[0,N-1]/G[0,0] = {elems['G_0N']/elems['G_00']:.6f} = exp(-span²/8)")

    # Check exp(-span²/8)
    expected_ratio = np.exp(-span**2 / 8)
    print(f"  expected exp(-span²/8) = {expected_ratio:.6f}")

    print("\n" + "=" * 70)
    print("ЧАСТЬ 3: Аналитическая формула для R_boundary")
    print("=" * 70)

    print("""
Для λ = a·e_0 + b·e_{N-1}:

R(a,b) = [a²Q₀₀ + 2ab·Q₀ₙ + b²Qₙₙ] / [a²G₀₀ + 2ab·G₀ₙ + b²Gₙₙ]

Ключевое наблюдение из данных:
- Q₀₀ ~ N²·span² (квадрат row_0(A))
- Qₙₙ ~ N²·span² (квадрат row_{N-1}(A))
- G₀₀ = G_{NN} = √(2π) (диагональ постоянная!)
- G₀ₙ = √(2π)·exp(-span²/8) → 0 при span → ∞

При span → ∞:
  R(a,b) ≈ [a²Q₀₀ + b²Qₙₙ] / [√(2π)·(a² + b²)]
         = [a²Q₀₀ + b²Qₙₙ] / [√(2π)·1]
         ~ N²·span² / √(2π)
         ~ N²·log²(N)

Это даёт R_bnd ~ N^2 × log²(N)!

НО численно видим R_bnd ~ N^{0.89}... почему?
""")

    print("\n" + "=" * 70)
    print("ЧАСТЬ 4: Проверка формулы для Q₀₀")
    print("=" * 70)

    print(f"{'X':>7} {'N':>5} {'Q_00':>12} {'N²':>12} {'Q_00/N²':>10} {'row_0²':>12}")
    print("-" * 70)

    for X in [1000, 5000, 10000, 20000, 50000]:
        twins = get_twins(X)
        N = len(twins)
        A, Q, G = build_matrices(twins)

        row_0 = np.sum(A[0, :])  # Σ_j A_{0j}
        row_0_sq = row_0**2

        # Q[0,0] = Σ_k A[k,0]² = (column 0 of A)²
        col_0 = A[:, 0]
        Q_00_check = np.sum(col_0**2)

        print(f"{X:>7} {N:>5} {Q[0,0]:>12.2f} {N**2:>12} {Q[0,0]/N**2:>10.4f} {row_0_sq:>12.2f}")

    print("""
Видим: Q₀₀/N² ~ 0.1-0.3, т.е. Q₀₀ ~ O(N²)

НО: row_0(A)² >> Q₀₀ потому что:
  Q₀₀ = ||column_0(A)||² = Σ_k A[k,0]²
  row_0² = [Σ_j A[0,j]]²

Это РАЗНЫЕ вещи! Q₀₀ — сумма квадратов СТОЛБЦА, не строки!
""")

    print("\n" + "=" * 70)
    print("ЧАСТЬ 5: Правильная интерпретация")
    print("=" * 70)

    # Analyze Q[0,0] = sum of column_0 squared
    twins = get_twins(20000)
    N = len(twins)
    A, Q, G = build_matrices(twins)
    xi = np.array([np.log(p) / (2 * np.pi) for p in twins])

    col_0 = A[:, 0]
    print(f"\nA[:,0] = column 0 of A:")
    print(f"  A[k,0] = (ξ_0 - ξ_k) × K[k,0]")
    print(f"  Все A[k,0] ≤ 0 для k > 0 (потому что ξ_0 < ξ_k)")
    print(f"  max|A[k,0]| = {np.max(np.abs(col_0)):.4f}")
    print(f"  ||col_0||² = Q[0,0] = {np.sum(col_0**2):.4f}")

    # Row sums
    row_0 = np.sum(A[0, :])
    row_N = np.sum(A[N-1, :])
    print(f"\nRow sums:")
    print(f"  row_0(A) = Σ_j A[0,j] = {row_0:.4f}")
    print(f"  row_{N-1}(A) = {row_N:.4f}")

    # Key insight
    print(f"\nQ = AᵀA, так что:")
    print(f"  Q[0,0] = Σ_k A[k,0]² = ||столбец 0||²")
    print(f"  Q[N-1,N-1] = Σ_k A[k,N-1]² = ||столбец N-1||²")

    col_N = A[:, N-1]
    print(f"\n  ||col_0||² = {np.sum(col_0**2):.4f}")
    print(f"  ||col_{N-1}||² = {np.sum(col_N**2):.4f}")

    print("\n" + "=" * 70)
    print("ВЫВОД:")
    print("=" * 70)
    print(f"""
R_boundary ~ N^{{{b_fit:.3f}}} → ∞

МЕХАНИЗМ РОСТА:
1. Q[0,0] = ||col_0(A)||² ~ N × (средний |A[k,0]|)²
2. Средний |A[k,0]| ~ span × kernel ~ span (для толстого ядра)
3. Q[0,0] ~ N × span² ~ N × log²(N)
4. G[0,0] = √(2π) = const
5. R[0,0] = Q[0,0]/G[0,0] ~ N × log²(N)

ПРОБЛЕМА: Численно видим R_bnd ~ N^{{{b_fit:.2f}}}, а не N×log²(N).

Это потому что оптимум НЕ на углу (0,1) или (1,0),
а на смеси a·e_0 + b·e_{{N-1}} где a, b ~ 0.7.

Смесь "размазывает" рост, но НЕ ОТМЕНЯЕТ его!
R_bnd ~ N^{{{b_fit:.2f}}} → ∞ — это ФАКТ!
""")

if __name__ == "__main__":
    main()
