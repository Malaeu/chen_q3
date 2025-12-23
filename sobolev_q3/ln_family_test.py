#!/usr/bin/env python3
"""
Тест семейства ln(n) для twin primes cancellation.

Гипотеза: числа связанные с 6 (делители, кратные) дают лучшую отмену.

Семейство:
- ln(2), ln(3) — базовые
- ln(6) = ln(2) + ln(3) — полный период mod 6
- ln(9) = 2·ln(3) — Aristotle доказал five_fold_cancellation!
- ln(12) = 2·ln(2) + ln(3)
- ln(18) = ln(2) + 2·ln(3)
- etc.
"""
import math

def sieve(n):
    is_prime = [True] * (n + 1)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(n**0.5) + 1):
        if is_prime[p]:
            for i in range(p*p, n + 1, p):
                is_prime[i] = False
    return [i for i in range(2, n + 1) if is_prime[i]]

def get_twins(primes):
    prime_set = set(primes)
    return [p for p in primes if p + 2 in prime_set]

def compute_exp_sum(numbers, alpha):
    """Compute |Σ exp(2πi·p·α)|"""
    x, y = 0.0, 0.0
    for p in numbers:
        angle = 2 * math.pi * p * alpha
        x += math.cos(angle)
        y += math.sin(angle)
    return math.sqrt(x*x + y*y)

def compute_delta(numbers, alpha, checkpoints=50):
    """Compute δ from log-log regression: |S| ~ N^(1-δ)"""
    import numpy as np

    if len(numbers) < 100:
        return None

    points = np.unique(np.logspace(2, np.log10(len(numbers)), checkpoints).astype(int))

    log_n, log_s = [], []
    x, y = 0.0, 0.0
    idx = 0

    for i, p in enumerate(numbers):
        angle = 2 * math.pi * p * alpha
        x += math.cos(angle)
        y += math.sin(angle)

        if idx < len(points) and i + 1 >= points[idx]:
            n = i + 1
            mag = math.sqrt(x*x + y*y)
            if mag > 0.1:
                log_n.append(math.log(n))
                log_s.append(math.log(mag))
            idx += 1

    if len(log_n) < 10:
        return None

    # Linear regression
    n_pts = len(log_n)
    sum_x = sum(log_n)
    sum_y = sum(log_s)
    sum_xy = sum(a*b for a, b in zip(log_n, log_s))
    sum_xx = sum(a*a for a in log_n)

    denom = n_pts * sum_xx - sum_x * sum_x
    if abs(denom) < 1e-10:
        return None

    beta = (n_pts * sum_xy - sum_x * sum_y) / denom
    return 1 - beta

def main():
    print("=" * 70)
    print("🔬 СЕМЕЙСТВО ln(n) ДЛЯ TWIN PRIMES")
    print("=" * 70)

    # Generate
    limit = 2_000_000
    print(f"\nГенерация простых до {limit:,}...")
    primes = sieve(limit)
    twins = get_twins(primes)
    print(f"✓ {len(primes):,} простых, {len(twins):,} twins")

    # Test family
    test_values = [
        # Базовые
        (2, "ln(2) — базовый"),
        (3, "ln(3) — базовый"),

        # Композитные от 2 и 3
        (4, "ln(4) = 2·ln(2)"),
        (6, "ln(6) = ln(2)+ln(3) ★"),
        (8, "ln(8) = 3·ln(2)"),
        (9, "ln(9) = 2·ln(3) ★"),
        (12, "ln(12) = 2·ln(2)+ln(3)"),
        (16, "ln(16) = 4·ln(2)"),
        (18, "ln(18) = ln(2)+2·ln(3)"),
        (24, "ln(24) = 3·ln(2)+ln(3)"),
        (27, "ln(27) = 3·ln(3)"),
        (36, "ln(36) = 2·ln(6)"),

        # С другими простыми
        (5, "ln(5) — простое"),
        (7, "ln(7) — простое"),
        (10, "ln(10) = ln(2)+ln(5)"),
        (15, "ln(15) = ln(3)+ln(5)"),
        (30, "ln(30) = ln(2)+ln(3)+ln(5)"),
    ]

    print("\n" + "=" * 70)
    print(f"{'n':<4} | {'α = ln(n)':<25} | {'δ twins':<10} | {'δ primes':<10} | Статус")
    print("-" * 70)

    results = []

    for n, desc in test_values:
        alpha = math.log(n)

        delta_twins = compute_delta(twins, alpha)
        delta_primes = compute_delta(primes, alpha)

        if delta_twins is not None and delta_primes is not None:
            # Status
            if delta_twins > 0.8:
                status = "🔥 EXCELLENT"
            elif delta_twins > 0.6:
                status = "✅ GOOD"
            elif delta_twins > 0.4:
                status = "⚠️ OK"
            else:
                status = "❌ WEAK"

            results.append((n, desc, delta_twins, delta_primes, status))
            print(f"{n:<4} | {desc:<25} | {delta_twins:>8.2f} | {delta_primes:>8.2f} | {status}")

    # Analysis
    print("\n" + "=" * 70)
    print("📊 АНАЛИЗ ПАТТЕРНОВ")
    print("=" * 70)

    # Sort by delta_twins
    results.sort(key=lambda x: -x[2])

    print("\n🏆 TOP-5 для TWINS:")
    for i, (n, desc, dt, dp, _) in enumerate(results[:5], 1):
        print(f"  {i}. ln({n}) → δ = {dt:.2f}")

    # Pattern analysis
    print("\n🔍 ЗАКОНОМЕРНОСТИ:")

    # Only powers of 2 and 3
    powers_23 = [(n, d, dt) for n, d, dt, dp, s in results
                  if all(p in [2, 3] for p in prime_factors(n))]
    powers_23.sort(key=lambda x: -x[2])

    print("\n  Только степени 2 и 3:")
    for n, desc, dt in powers_23[:5]:
        print(f"    ln({n}) = {factorize_log(n)} → δ = {dt:.2f}")

    # With 5
    with_5 = [(n, d, dt) for n, d, dt, dp, s in results if 5 in prime_factors(n)]

    print("\n  С множителем 5:")
    for n, desc, dt in with_5:
        print(f"    ln({n}) = {factorize_log(n)} → δ = {dt:.2f}")

    # Hypothesis
    print("\n" + "=" * 70)
    print("💡 ГИПОТЕЗА")
    print("=" * 70)
    print("""
    Twins живут на решётке 6k±1, поэтому:

    1. ln(6) = ln(2·3) захватывает ПОЛНЫЙ период → δ ≈ 0.9
    2. ln(9) = 2·ln(3) захватывает 3-часть → δ ≈ 0.6-0.7
    3. ln(4), ln(8), ln(16) — только 2-часть → слабее
    4. С множителем 5, 7 — нарушают mod 6 структуру → хуже

    ВЫВОД: Оптимальные α = ln(6^k) = k·ln(6) для k = 1, 2, ...
    """)

def prime_factors(n):
    """Return list of prime factors"""
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def factorize_log(n):
    """Express ln(n) in terms of ln(primes)"""
    factors = prime_factors(n)
    from collections import Counter
    counts = Counter(factors)
    parts = []
    for p, c in sorted(counts.items()):
        if c == 1:
            parts.append(f"ln({p})")
        else:
            parts.append(f"{c}·ln({p})")
    return " + ".join(parts)

if __name__ == "__main__":
    main()
