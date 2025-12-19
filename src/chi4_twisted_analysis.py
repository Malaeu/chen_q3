#!/usr/bin/env python3
"""
χ₄ TWISTED APPROACH: Использование характера χ₄ для выделения twins

КЛЮЧЕВОЕ СВОЙСТВО:
  Для twin pair (p, p+2) где p > 2:
  χ₄(p) · χ₄(p+2) = -1

ПОТОМУ ЧТО:
  Если p ≡ 1 (mod 4), то p+2 ≡ 3 (mod 4)
  χ₄(1 mod 4) = +1, χ₄(3 mod 4) = -1

ИДЕЯ:
  D = P² - P·P_χ где P = Σ w(n)φ_n, P_χ = Σ w(n)χ₄(n)φ_n

  Twin вклад в D имеет определённый знак!
"""

import numpy as np
from typing import List, Tuple
import warnings
warnings.filterwarnings('ignore')

def sieve_primes(X: int) -> List[int]:
    """Primes up to X."""
    if X < 2:
        return []
    sieve = [True] * (X + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(X**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, X + 1, i):
                sieve[j] = False
    return [p for p in range(2, X + 1) if sieve[p]]

def chi4(n: int) -> int:
    """
    Character χ₄ (non-principal character mod 4):
      χ₄(n) = 0 if n even
      χ₄(n) = +1 if n ≡ 1 (mod 4)
      χ₄(n) = -1 if n ≡ 3 (mod 4)
    """
    if n % 2 == 0:
        return 0
    if n % 4 == 1:
        return 1
    else:  # n % 4 == 3
        return -1

def Lambda_function(X: int) -> np.ndarray:
    """von Mangoldt function."""
    Lambda = np.zeros(X + 1)
    primes = sieve_primes(X)
    for p in primes:
        pk = p
        while pk <= X:
            Lambda[pk] = np.log(p)
            pk *= p
    return Lambda

def get_twin_primes(X: int) -> List[Tuple[int, int]]:
    """Twin prime pairs up to X."""
    primes = set(sieve_primes(X + 2))
    return [(p, p+2) for p in sorted(primes) if p + 2 in primes and p >= 3]

def analyze_chi4_twins(X: int):
    """Analyze χ₄ product for twin pairs."""
    twins = get_twin_primes(X)

    print(f"\n{'='*60}")
    print(f"АНАЛИЗ χ₄ для twins до X = {X}")
    print(f"{'='*60}")

    if not twins:
        print("Нет twins!")
        return

    # Check χ₄(p)·χ₄(p+2) for all twins
    products = []
    for p, q in twins[:10]:  # Show first 10
        chi_p = chi4(p)
        chi_q = chi4(q)
        prod = chi_p * chi_q
        products.append(prod)
        print(f"  ({p:>4}, {q:>4}): χ₄({p})={chi_p:+d}, χ₄({q})={chi_q:+d}, product={prod:+d}")

    if len(twins) > 10:
        print(f"  ... ({len(twins)} total twins)")

    # Verify ALL twins have product -1
    all_products = [chi4(p) * chi4(p+2) for p, _ in twins]
    all_minus_one = all(prod == -1 for prod in all_products)

    print(f"\n✅ ALL twins have χ₄(p)·χ₄(p+2) = -1: {all_minus_one}")

    return all_minus_one

def compute_D_functional(X: int) -> dict:
    """
    Compute D = P² - P·P_χ

    P = Σ_n Λ(n)/√n · φ(ξ_n)
    P_χ = Σ_n Λ(n)χ₄(n)/√n · φ(ξ_n)

    Using φ = indicator (φ(ξ) = 1 for all ξ):

    P² = Σ_{m,n} Λ(m)Λ(n)/√(mn)
    P·P_χ = Σ_{m,n} Λ(m)Λ(n)χ₄(n)/√(mn)

    D = P² - P·P_χ = Σ_{m,n} Λ(m)Λ(n)(1-χ₄(n))/√(mn)
    """
    Lambda = Lambda_function(X + 2)
    primes = sieve_primes(X + 2)

    # P² decomposition
    P_squared = 0.0
    P_P_chi = 0.0

    for m in primes:
        for n in primes:
            if m <= X and n <= X:
                weight = Lambda[m] * Lambda[n] / np.sqrt(m * n)
                P_squared += weight
                P_P_chi += weight * chi4(n)

    D = P_squared - P_P_chi

    # Twin-specific contribution in D
    # For twins (n, n+2): χ₄(n+2) = -χ₄(n)
    # So contribution is Λ(n)Λ(n+2)/√(n(n+2)) * (1 - χ₄(n+2))
    # = Λ(n)Λ(n+2)/√(n(n+2)) * (1 + χ₄(n))

    twin_contrib_D = 0.0
    twins = get_twin_primes(X)

    for p, q in twins:
        # m=p, n=q: Λ(p)Λ(q)(1-χ₄(q))/√(pq)
        # Since χ₄(q) = -χ₄(p), we have 1-χ₄(q) = 1+χ₄(p)
        weight = Lambda[p] * Lambda[q] / np.sqrt(p * q)
        twin_contrib_D += weight * (1 - chi4(q))

        # m=q, n=p: Λ(q)Λ(p)(1-χ₄(p))/√(pq)
        twin_contrib_D += weight * (1 - chi4(p))

    return {
        'P_squared': P_squared,
        'P_P_chi': P_P_chi,
        'D': D,
        'twin_contrib_D': twin_contrib_D,
        'twin_ratio': twin_contrib_D / D if D != 0 else 0,
        'num_twins': len(twins)
    }

def compute_alternative_D(X: int) -> dict:
    """
    Alternative: D' = P·P_χ - P_χ²

    Where:
    P·P_χ = Σ Λ(m)Λ(n)χ₄(n)/√(mn)
    P_χ² = Σ Λ(m)χ₄(m)Λ(n)χ₄(n)/√(mn)

    D' = Σ Λ(m)Λ(n)χ₄(n)(1-χ₄(m))/√(mn)

    For twins: χ₄(n)(1-χ₄(m)) where m=p, n=p+2:
      = χ₄(p+2)(1-χ₄(p)) = -χ₄(p)(1-χ₄(p))

    If p ≡ 1 (mod 4): χ₄(p)=+1, so factor = -(1)(0) = 0
    If p ≡ 3 (mod 4): χ₄(p)=-1, so factor = -(-1)(2) = +2
    """
    Lambda = Lambda_function(X + 2)
    primes = sieve_primes(X + 2)

    P_P_chi = 0.0
    P_chi_squared = 0.0

    for m in primes:
        for n in primes:
            if m <= X and n <= X:
                weight = Lambda[m] * Lambda[n] / np.sqrt(m * n)
                chi_n = chi4(n)
                chi_m = chi4(m)
                P_P_chi += weight * chi_n
                P_chi_squared += weight * chi_m * chi_n

    D_prime = P_P_chi - P_chi_squared

    # Twin contribution in D'
    twin_contrib = 0.0
    twins = get_twin_primes(X)

    for p, q in twins:
        weight = Lambda[p] * Lambda[q] / np.sqrt(p * q)
        chi_p = chi4(p)
        chi_q = chi4(q)

        # m=p, n=q: χ₄(q)(1-χ₄(p)) = -χ₄(p)(1-χ₄(p))
        factor_1 = chi_q * (1 - chi_p)
        twin_contrib += weight * factor_1

        # m=q, n=p: χ₄(p)(1-χ₄(q)) = χ₄(p)(1+χ₄(p))
        factor_2 = chi_p * (1 - chi_q)
        twin_contrib += weight * factor_2

    return {
        'P_P_chi': P_P_chi,
        'P_chi_squared': P_chi_squared,
        'D_prime': D_prime,
        'twin_contrib': twin_contrib,
        'twin_ratio': twin_contrib / D_prime if D_prime != 0 else 0
    }

def compute_Q_product(X: int) -> dict:
    """
    Compute Q(φ) · Q_χ(φ) where:
    Q(φ) = A - P (Weil functional)
    Q_χ(φ) = A_χ - P_χ (twisted Weil)

    Product structure:
    Q · Q_χ = A·A_χ - A·P_χ - P·A_χ + P·P_χ

    Under RH: Q ≥ 0, and under GRH for L(s,χ₄): Q_χ ≥ 0

    Can we extract twin info from Q·Q_χ?
    """
    Lambda = Lambda_function(X + 2)
    primes = sieve_primes(X + 2)

    # For simplicity, use φ = indicator (A = 0)
    # So Q = -P, Q_χ = -P_χ
    # Q · Q_χ = P · P_χ

    P = sum(Lambda[p] / np.sqrt(p) for p in primes if p <= X)
    P_chi = sum(Lambda[p] * chi4(p) / np.sqrt(p) for p in primes if p <= X)

    Q = -P
    Q_chi = -P_chi

    Q_product = Q * Q_chi  # = P · P_chi

    # Bilinear form P·P_χ = Σ Λ(m)Λ(n)χ₄(n)/√(mn)
    P_P_chi_bilinear = 0.0
    for m in primes:
        for n in primes:
            if m <= X and n <= X:
                P_P_chi_bilinear += Lambda[m] * Lambda[n] * chi4(n) / np.sqrt(m * n)

    # S₂ = Σ Λ(p)Λ(p+2)
    twins = get_twin_primes(X)
    S2 = sum(Lambda[p] * Lambda[q] for p, q in twins)

    return {
        'P': P,
        'P_chi': P_chi,
        'Q': Q,
        'Q_chi': Q_chi,
        'Q_product': Q_product,
        'P_P_chi': P_P_chi_bilinear,
        'S2': S2,
        'ratio_S2_to_bilinear': S2 / P_P_chi_bilinear if P_P_chi_bilinear != 0 else 0
    }

def main():
    print("=" * 70)
    print("χ₄ TWISTED APPROACH FOR TWINS")
    print("=" * 70)

    # Part 1: Verify χ₄ property
    print("\n" + "=" * 70)
    print("ЧАСТЬ 1: Проверка χ₄(p)·χ₄(p+2) = -1 для twins")
    print("=" * 70)

    for X in [100, 500, 1000]:
        analyze_chi4_twins(X)

    # Part 2: D = P² - P·P_χ functional
    print("\n" + "=" * 70)
    print("ЧАСТЬ 2: Функционал D = P² - P·P_χ")
    print("=" * 70)

    print(f"{'X':>7} {'P²':>12} {'P·P_χ':>12} {'D':>12} {'twin_D':>12} {'twin%':>8}")
    print("-" * 65)

    for X in [100, 200, 500, 1000, 2000]:
        result = compute_D_functional(X)
        print(f"{X:>7} {result['P_squared']:>12.2f} {result['P_P_chi']:>12.2f} "
              f"{result['D']:>12.2f} {result['twin_contrib_D']:>12.2f} "
              f"{100*result['twin_ratio']:>7.2f}%")

    print("""
АНАЛИЗ:
  D = P² - P·P_χ выделяет члены где χ₄(n) ≠ 1
  Twin contribution ~ 10-25% от D

  Но D сам по себе ~ P² (того же порядка)
  Так что twin_D / P² ~ 5-12% — не намного лучше!
""")

    # Part 3: Alternative D' = P·P_χ - P_χ²
    print("\n" + "=" * 70)
    print("ЧАСТЬ 3: Альтернатива D' = P·P_χ - P_χ²")
    print("=" * 70)

    print(f"{'X':>7} {'P·P_χ':>12} {'P_χ²':>12} {'D_prime':>12} {'twin':>12} {'ratio':>8}")
    print("-" * 65)

    for X in [100, 200, 500, 1000]:
        result = compute_alternative_D(X)
        print(f"{X:>7} {result['P_P_chi']:>12.2f} {result['P_chi_squared']:>12.2f} "
              f"{result['D_prime']:>12.2f} {result['twin_contrib']:>12.2f} "
              f"{result['twin_ratio']:>8.4f}")

    print("""
АНАЛИЗ:
  D' = P·P_χ - P_χ² использует χ₄ двояко

  Twin ratio varies! Зависит от распределения twins по mod 4.
""")

    # Part 4: Q·Q_χ product
    print("\n" + "=" * 70)
    print("ЧАСТЬ 4: Произведение Q(φ)·Q_χ(φ)")
    print("=" * 70)

    print(f"{'X':>7} {'P':>10} {'P_χ':>10} {'Q·Q_χ':>12} {'S₂':>10} {'S₂/bilin':>10}")
    print("-" * 65)

    for X in [100, 200, 500, 1000]:
        result = compute_Q_product(X)
        print(f"{X:>7} {result['P']:>10.2f} {result['P_chi']:>10.2f} "
              f"{result['Q_product']:>12.2f} {result['S2']:>10.2f} "
              f"{result['ratio_S2_to_bilinear']:>10.4f}")

    print("""
АНАЛИЗ:
  Q·Q_χ = P·P_χ (при φ = indicator)

  S₂ / (P·P_χ) ~ 0.01-0.02 — ОЧЕНЬ МАЛО!

  Даже χ₄ twist не помогает выделить S₂!
""")

    # Part 5: Key insight
    print("\n" + "=" * 70)
    print("КЛЮЧЕВОЙ ВЫВОД")
    print("=" * 70)

    print("""
🔥 ПРОБЛЕМА χ₄ ПОДХОДА:

1. χ₄(p)·χ₄(p+2) = -1 для ВСЕХ twins — РАБОТАЕТ! ✓

2. НО: twins — это МАЛАЯ часть всех prime pairs

3. D = P² - P·P_χ выделяет members с χ₄ ≠ 1:
   - Это ВСЕ нечётные n ≡ 3 (mod 4)
   - Twins — малая подчасть этого множества!

4. Нет способа "изолировать" именно twin pairs через χ₄

🎯 ФУНДАМЕНТАЛЬНАЯ ПРОБЛЕМА:

   χ₄ character выделяет RESIDUE CLASSES (mod 4)
   Twins — это ADDITIVE структура (gap = 2)

   Эти две структуры ОРТОГОНАЛЬНЫ!

   χ₄(p)·χ₄(p+2) = -1 говорит что twins ЧЕРЕДУЮТСЯ
   между классами 1,3 (mod 4), но НЕ даёт их количество!

🚨 ВЫВОД:
   Dirichlet characters НЕ могут напрямую считать twins.
   Нужен ДРУГОЙ инструмент — возможно sieve methods!
""")

if __name__ == "__main__":
    main()
