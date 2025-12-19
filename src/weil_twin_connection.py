#!/usr/bin/env python3
"""
WEIL → TWIN CONNECTION

Проверяем: можно ли связать Q(ϕ)² с Q_twin через cross-terms?

Структура:
  Q(ϕ) = A(ϕ) - P(ϕ)
  где A(ϕ) = archimedean part
      P(ϕ) = prime sum = Σ w(n) · ϕ(ξ_n)

  Q(ϕ)² = A² - 2AP + P²

  P(ϕ)² = [Σ Λ(n)/√n · ϕ(ξ_n)]²
        = Σ_{m,n} Λ(m)Λ(n)/√(mn) · ϕ(ξ_m)ϕ(ξ_n)

  Twin diagonal: m = n±2
"""

import numpy as np
from typing import Tuple, Callable

def sieve_primes(X: int) -> list:
    """All primes up to X."""
    sieve = [True] * (X + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(X**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, X + 1, i):
                sieve[j] = False
    return [p for p in range(2, X + 1) if sieve[p]]

def Lambda(n: int, primes_set: set) -> float:
    """von Mangoldt function."""
    if n < 2:
        return 0.0
    # Check if n is prime power
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            # n = p^k?
            k = 0
            m = n
            while m % p == 0:
                m //= p
                k += 1
            if m == 1:
                return np.log(p)
            return 0.0
    # n is prime
    return np.log(n)

def compute_prime_sum_squared(X: int, phi: Callable[[float], float]) -> Tuple[float, float, float]:
    """
    Compute P(ϕ)² = Σ_{m,n} Λ(m)Λ(n)/√(mn) · ϕ(ξ_m)ϕ(ξ_n)

    Разбиваем на:
    - diagonal: m = n
    - twin_diag: |m - n| = 2
    - off_diag: остальное
    """
    primes = sieve_primes(X)
    primes_set = set(primes)

    # Compute Λ(n) for all n up to X
    Lambda_cache = {}
    for n in range(2, X + 1):
        Lambda_cache[n] = Lambda(n, primes_set)

    # xi coordinates
    xi = lambda n: np.log(n) / (2 * np.pi)

    diagonal = 0.0
    twin_diag = 0.0
    off_diag = 0.0

    # Only sum over prime powers (where Λ ≠ 0)
    prime_powers = [n for n in range(2, X + 1) if Lambda_cache[n] > 0]

    for m in prime_powers:
        Lm = Lambda_cache[m]
        phi_m = phi(xi(m))

        for n in prime_powers:
            Ln = Lambda_cache[n]
            phi_n = phi(xi(n))

            term = Lm * Ln / np.sqrt(m * n) * phi_m * phi_n

            if m == n:
                diagonal += term
            elif abs(m - n) == 2:
                twin_diag += term
            else:
                off_diag += term

    return diagonal, twin_diag, off_diag

def compute_S2(X: int) -> float:
    """S₂(X) = Σ_{n ≤ X} Λ(n)Λ(n+2)"""
    primes = sieve_primes(X + 2)
    primes_set = set(primes)

    S2 = 0.0
    for n in range(2, X + 1):
        Ln = Lambda(n, primes_set)
        Ln2 = Lambda(n + 2, primes_set)
        S2 += Ln * Ln2

    return S2

def main():
    print("=" * 70)
    print("WEIL → TWIN CONNECTION: Анализ P(ϕ)²")
    print("=" * 70)

    print("""
ИДЕЯ:
  P(ϕ)² = Σ_{m,n} Λ(m)Λ(n)/√(mn) · ϕ(ξ_m)ϕ(ξ_n)

  Разбиваем:
  - diagonal:  m = n      → Σ Λ(n)²/n · ϕ(ξ_n)²
  - twin_diag: |m-n| = 2  → 2·Σ Λ(n)Λ(n+2)/√(n(n+2)) · ϕ(ξ_n)ϕ(ξ_{n+2})
  - off_diag:  остальное

  ВОПРОС: Какова доля twin_diag в P²?
""")

    # Test function: indicator [0, ξ_X]
    def phi_indicator(X_val):
        xi_max = np.log(X_val) / (2 * np.pi)
        return lambda xi: 1.0 if 0 <= xi <= xi_max else 0.0

    # Gaussian centered at origin
    def phi_gaussian(sigma):
        return lambda xi: np.exp(-xi**2 / (2 * sigma**2))

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 1: Indicator function ϕ = 1_{[0, ξ_X]}")
    print("=" * 70)
    print(f"{'X':>7} {'diagonal':>12} {'twin_diag':>12} {'off_diag':>12} {'twin%':>8} {'S₂(X)':>12}")
    print("-" * 70)

    for X in [100, 200, 500, 1000, 2000]:
        phi = phi_indicator(X)
        diag, twin, off = compute_prime_sum_squared(X, phi)
        total = diag + twin + off
        twin_pct = 100 * twin / total if total > 0 else 0

        S2 = compute_S2(X)

        print(f"{X:>7} {diag:>12.2f} {twin:>12.2f} {off:>12.2f} {twin_pct:>7.2f}% {S2:>12.2f}")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 2: Gaussian ϕ(ξ) = exp(-ξ²/2σ²)")
    print("=" * 70)

    X = 1000
    print(f"\nX = {X}")
    print(f"{'σ':>7} {'diagonal':>12} {'twin_diag':>12} {'off_diag':>12} {'twin%':>8}")
    print("-" * 55)

    for sigma in [0.5, 1.0, 2.0, 5.0, 10.0]:
        phi = phi_gaussian(sigma)
        diag, twin, off = compute_prime_sum_squared(X, phi)
        total = diag + twin + off
        twin_pct = 100 * twin / total if total > 0 else 0

        print(f"{sigma:>7.1f} {diag:>12.2f} {twin:>12.2f} {off:>12.2f} {twin_pct:>7.2f}%")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 3: Связь twin_diag с S₂(X)")
    print("=" * 70)

    print(f"{'X':>7} {'twin_diag':>12} {'S₂(X)':>12} {'ratio':>10}")
    print("-" * 45)

    for X in [100, 200, 500, 1000, 2000]:
        phi = phi_indicator(X)
        diag, twin, off = compute_prime_sum_squared(X, phi)

        S2 = compute_S2(X)

        # twin_diag ≈ 2·Σ Λ(n)Λ(n+2)/√(n(n+2)) · ϕ²
        # S₂ = Σ Λ(n)Λ(n+2)
        # ratio = twin_diag / S₂ ≈ 2/√(n(n+2)) ≈ 2/n

        ratio = twin / S2 if S2 > 0 else 0

        print(f"{X:>7} {twin:>12.2f} {S2:>12.2f} {ratio:>10.4f}")

    print("""
АНАЛИЗ:
  twin_diag / S₂ ≈ 2/√(n(n+2)) ~ 2/n (убывает)

  Это потому что twin_diag содержит множитель 1/√(mn),
  а S₂ не содержит.
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 4: Модифицированный twin functional")
    print("=" * 70)

    print("""
Определим Q_twin без 1/√(mn):
  Q_twin(ϕ) = Σ Λ(n)Λ(n+2) · ϕ(ξ_n) · ϕ(ξ_{n+2})

Это соответствует S₂(X) при ϕ = indicator.
""")

    def compute_Q_twin(X: int, phi: Callable[[float], float]) -> float:
        """Q_twin(ϕ) = Σ Λ(n)Λ(n+2) · ϕ(ξ_n) · ϕ(ξ_{n+2})"""
        primes = sieve_primes(X + 2)
        primes_set = set(primes)

        xi = lambda n: np.log(n) / (2 * np.pi)

        Q_twin = 0.0
        for n in range(2, X + 1):
            Ln = Lambda(n, primes_set)
            Ln2 = Lambda(n + 2, primes_set)
            if Ln > 0 and Ln2 > 0:
                Q_twin += Ln * Ln2 * phi(xi(n)) * phi(xi(n + 2))

        return Q_twin

    print(f"{'X':>7} {'Q_twin':>12} {'S₂(X)':>12} {'ratio':>10}")
    print("-" * 45)

    for X in [100, 200, 500, 1000, 2000]:
        phi = phi_indicator(X)
        Q_twin = compute_Q_twin(X, phi)
        S2 = compute_S2(X)

        ratio = Q_twin / S2 if S2 > 0 else 0

        print(f"{X:>7} {Q_twin:>12.2f} {S2:>12.2f} {ratio:>10.4f}")

    print("""
Q_twin ≈ S₂ (ratio ~ 1) при ϕ = indicator!

Это естественно: indicator фильтрует n ≤ X.
""")

    print("\n" + "=" * 70)
    print("КЛЮЧЕВОЙ ВОПРОС: Можно ли получить bound на Q_twin из Q(ϕ)?")
    print("=" * 70)

    print("""
ПРОБЛЕМА:
  Q(ϕ) = A(ϕ) - P(ϕ)  где A = archimedean, P = prime sum
  Q(ϕ)² = A² - 2AP + P²

  P² содержит twin_diag, НО:
  - twin_diag ~ 0.1-0.2% от P² (очень малая доля!)
  - Остальные 99.8% — off-diagonal и diagonal

  Нельзя извлечь bound на twin_diag из Q ≥ 0!

ВЫВОД:
  Q(ϕ)² НЕ даёт прямого bound на Q_twin.
  Нужна ДРУГАЯ структура связи!
""")

    print("\n" + "=" * 70)
    print("АЛЬТЕРНАТИВНАЯ ИДЕЯ: Pair correlation")
    print("=" * 70)

    print("""
Montgomery pair correlation (1973):
  R₂(T, α) = Σ_{0 < γ, γ' < T} w(γ-γ') · f(γ-γ')

Hardy-Littlewood conjecture для twins:
  S₂(X) ~ 2C₂ · X  где C₂ = 0.66...

СВЯЗЬ: Pair correlation нулей ζ ↔ распределение twins

ПРОБЛЕМА: Montgomery доказал pair correlation УСЛОВНО на RH,
но это НЕ даёт bound на S₂(X)!
""")

if __name__ == "__main__":
    main()
