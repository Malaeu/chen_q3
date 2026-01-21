#!/usr/bin/env python3
"""
КРИТИЧЕСКИЙ ТЕСТ: X-dependence vs N-dependence

ВОПРОС Q2: Можно ли показать R(Φ_X) ≥ c × X^δ НЕЗАВИСИМО от N?

КЛЮЧЕВОЙ ИНСАЙТ:
  При конечных twins: N = const, но X → ∞
  Что происходит с R при фиксированном N но растущем X?
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

def build_matrices(twins: list, t: float = 1.0):
    """Build Q, G matrices."""
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

    return Q, G

def compute_R(lam: np.ndarray, Q: np.ndarray, G: np.ndarray) -> float:
    """R(λ) = λᵀQλ / λᵀGλ"""
    num = lam @ Q @ lam
    den = lam @ G @ lam
    return num / den if den > 1e-15 else 1e10

def main():
    print("=" * 70)
    print("ТЕСТ Q2: X-dependence vs N-dependence")
    print("=" * 70)

    print("""
КЛЮЧЕВОЙ ВОПРОС:
  SC2 говорит: конечные twins ⟹ R(Φ_X) = O(1)
  Численно:     R_min(N) ~ N^{0.9}

  Это НЕ противоречие если N фиксировано!
  При конечных twins N = const, и R = const.

ЭКСПЕРИМЕНТ: Что если twins фиксированы, но X растёт?
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 1: Фиксируем twins, меняем X")
    print("=" * 70)

    # Возьмём twins до X=1000 (35 twins) и притворимся что это ВСЕ twins
    X_fixed = 1000
    twins_fixed = get_twins(X_fixed)
    N_fixed = len(twins_fixed)

    print(f"\nФиксируем twins до X={X_fixed}: N={N_fixed} twins")
    print("Последний twin:", twins_fixed[-1], twins_fixed[-1]+2)

    # Построим матрицы для этих twins
    Q, G = build_matrices(twins_fixed)

    # Twin vector (фиксирован!)
    lam = np.array([np.log(p) * np.log(p+2) for p in twins_fixed])

    R_fixed = compute_R(lam, Q, G)
    print(f"R(Φ) = {R_fixed:.4f}")

    print("""
КЛЮЧЕВОЕ НАБЛЮДЕНИЕ:
  Если twins фиксированы, то Q, G, λ ВСЕ фиксированы!
  R(Φ_X) = const для X ≥ X_0 (где X_0 = последний twin)

  Это ИМЕННО то что говорит SC2!
  При конечных twins R стабилизируется.
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 2: Масштабирование R(N) vs R(X)")
    print("=" * 70)

    print(f"{'X':>7} {'N':>5} {'R':>10} {'R/N':>10} {'R/X':>10}")
    print("-" * 50)

    for X in [100, 500, 1000, 2000, 5000, 10000, 20000, 50000]:
        twins = get_twins(X)
        N = len(twins)
        if N < 5:
            continue

        Q, G = build_matrices(twins)
        lam = np.array([np.log(p) * np.log(p+2) for p in twins])
        R = compute_R(lam, Q, G)

        print(f"{X:>7} {N:>5} {R:>10.2f} {R/N:>10.4f} {R/X:>10.6f}")

    print("""
АНАЛИЗ:
  R/N ≈ 0.4-0.6 (относительно стабильно)
  R/X → 0 при X → ∞ (потому что N/X → 0)

  R ~ N, но N ~ X/log²(X) (Hardy-Littlewood)
  Так что R ~ X/log²(X)
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 3: Power law fits")
    print("=" * 70)

    X_vals = [500, 1000, 2000, 5000, 10000, 20000, 50000]
    N_vals = []
    R_vals = []

    for X in X_vals:
        twins = get_twins(X)
        N = len(twins)
        Q, G = build_matrices(twins)
        lam = np.array([np.log(p) * np.log(p+2) for p in twins])
        R = compute_R(lam, Q, G)
        N_vals.append(N)
        R_vals.append(R)

    N_arr = np.array(N_vals)
    X_arr = np.array(X_vals)
    R_arr = np.array(R_vals)

    # Fit R vs N
    b_N, log_a_N = np.polyfit(np.log(N_arr), np.log(R_arr), 1)
    print(f"R ~ {np.exp(log_a_N):.4f} × N^{{{b_N:.4f}}}")

    # Fit R vs X
    b_X, log_a_X = np.polyfit(np.log(X_arr), np.log(R_arr), 1)
    print(f"R ~ {np.exp(log_a_X):.6f} × X^{{{b_X:.4f}}}")

    # Fit N vs X
    b_NX, log_a_NX = np.polyfit(np.log(X_arr), np.log(N_arr), 1)
    print(f"N ~ {np.exp(log_a_NX):.4f} × X^{{{b_NX:.4f}}}")

    print(f"""
СВЯЗЬ:
  R ~ N^{{{b_N:.3f}}}
  N ~ X^{{{b_NX:.3f}}}
  ⟹ R ~ X^{{{b_N * b_NX:.3f}}}

  Прямой fit: R ~ X^{{{b_X:.3f}}}
  Согласуется!
""")

    print("\n" + "=" * 70)
    print("КЛЮЧЕВОЙ ВЫВОД:")
    print("=" * 70)
    print("""
🚨 ПРОБЛЕМА ЛОГИКИ:

1. SC2 говорит: конечные twins ⟹ R(Φ_X) = const для X ≥ X_0
   Это ВЕРНО! При фиксированном множестве twins R фиксировано.

2. Численно видим: R ~ N^{0.9}
   Это описывает как R МЕНЯЕТСЯ при разном N.

3. ЭТО НЕ ПРОТИВОРЕЧИЕ!
   При конечных twins N фиксировано, и R = const.
   Скейлинг R ~ N^{0.9} описывает РАЗНЫЕ сценарии с разным N.

4. Чтобы получить противоречие, нужно:
   - Либо показать что R(Φ_X) → ∞ при ФИКСИРОВАННОМ множестве twins
     (невозможно — Q, G, λ все фиксированы!)
   - Либо найти ВНЕШНИЙ bound на R который нарушается

🎯 ЧТО НУЖНО ДЛЯ ПРОРЫВА:

A) Weil connection: связать R с RH/Weil positivity
B) Structure argument: показать что twins имеют особую структуру
C) X-dependence: найти bound R(Φ_X) ≤ f(X) который нарушается ростом
D) Chen pairs: проверить на модельном случае (доказанном!)
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 4: Симуляция конечных twins")
    print("=" * 70)

    print("""
Симулируем сценарий "конечных twins":
Берём первые K twins и смотрим что R делает при X → ∞.
""")

    K_twins = 35  # Первые 35 twins (соответствует X ≈ 1000)
    all_twins_large = get_twins(50000)
    fixed_twins = all_twins_large[:K_twins]

    print(f"Фиксируем первые {K_twins} twins: p ∈ [{fixed_twins[0]}, {fixed_twins[-1]}]")

    Q, G = build_matrices(fixed_twins)
    lam = np.array([np.log(p) * np.log(p+2) for p in fixed_twins])
    R = compute_R(lam, Q, G)

    print(f"\nПри ЛЮБОМ X ≥ {fixed_twins[-1]}:")
    print(f"  N = {K_twins} (const)")
    print(f"  R = {R:.4f} (const)")
    print(f"\nЭто и есть SC2! R стабилизируется при конечных twins.")

if __name__ == "__main__":
    main()
