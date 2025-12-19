"""
Проверка: span ~ log(N) — это факт или гипотеза?

span = (log(p_N) - log(p_1)) / (2π)
     = log(p_N / p_1) / (2π)

где p_N — N-й twin prime.

Вопрос: как растёт p_N с N?
"""
import numpy as np

def get_primes(n_max):
    is_prime = np.ones(n_max + 1, dtype=bool)
    is_prime[0:2] = False
    for i in range(2, int(n_max**0.5) + 1):
        if is_prime[i]:
            is_prime[i*i:n_max+1:i] = False
    return np.nonzero(is_prime)[0]

def get_twin_primes(limit):
    primes = get_primes(limit)
    twins = []
    for i in range(len(primes) - 1):
        if primes[i+1] - primes[i] == 2:
            twins.append(primes[i])
    return np.array(twins)

print("="*70)
print("ПРОВЕРКА: span ~ log(N) — ЭТО ФАКТ ИЛИ ГИПОТЕЗА?")
print("="*70)

X_list = [1000, 5000, 10000, 50000, 100000, 300000, 500000]

print(f"\n{'X':>8} {'N':>6} {'p_N':>10} {'span':>8} {'log(N)':>8} {'span/logN':>10}")
print("-" * 60)

data = []
for X in X_list:
    twins = get_twin_primes(X)
    N = len(twins)
    p_N = twins[-1]
    p_1 = twins[0]  # = 3

    span = np.log(p_N / p_1) / (2 * np.pi)
    log_N = np.log(N)

    data.append((N, span, log_N))

    print(f"{X:>8} {N:>6} {p_N:>10} {span:>8.4f} {log_N:>8.4f} {span/log_N:>10.4f}")

# Fit span vs log(N)
Ns = np.array([d[0] for d in data])
spans = np.array([d[1] for d in data])
log_Ns = np.log(Ns)

# Linear regression: span = a * log(N) + b
A = np.vstack([log_Ns, np.ones_like(log_Ns)]).T
coeffs, residuals, rank, s = np.linalg.lstsq(A, spans, rcond=None)
a, b = coeffs

print(f"\nЛинейная регрессия: span = {a:.4f} × log(N) + {b:.4f}")

# Проверка: span/log(N) → const?
ratios = spans / log_Ns
print(f"\nspan/log(N) по N:")
for i, (N, sp, logN) in enumerate(data):
    print(f"  N={N:>5}: span/log(N) = {sp/logN:.4f}")

print(f"\nMean(span/log(N)) = {np.mean(ratios):.4f}")
print(f"Std(span/log(N))  = {np.std(ratios):.4f}")
print(f"CV = {np.std(ratios)/np.mean(ratios)*100:.1f}%")

print("""
╔══════════════════════════════════════════════════════════════════════════════╗
║                           ВЫВОД                                             ║
╚══════════════════════════════════════════════════════════════════════════════╝

span = log(p_N/3) / (2π)

где p_N — N-й twin prime.

ФАКТ (наблюдаемый): span ~ 0.25 × log(N) для N до 4565.

ВОПРОС: Это гипотеза или следствие плотности twins?

По Hardy-Littlewood: π₂(X) ~ C × X / log²(X)
                     N ~ X / log²(X)
                     X ~ N × log²(N)
                     p_N ~ N × log²(N)
                     span ~ log(N × log²(N)) / (2π)
                          ~ log(N) / (2π) × (1 + o(1))

КРИТИЧЕСКИЙ МОМЕНТ:
Hardy-Littlewood говорит о ПЛОТНОСТИ twins, не об их бесконечности!
Плотность можно оценивать даже для конечного числа twins.

НО: если мы ПРЕДПОЛАГАЕМ что twins бесконечны, то span ~ log(N).
    Если twins конечны, то span = const для N > N_max.

ЭТО ТАВТОЛОГИЯ: span → ∞ ⟺ twins бесконечны.

Мы не можем использовать span → ∞ для доказательства TPC,
потому что это эквивалентно TPC!
""")

print("="*70)
print("АЛЬТЕРНАТИВНЫЙ ПОДХОД: что если использовать ТОЛЬКО row_0 bound?")
print("="*70)

print("""
row_0 ≥ c × N × span

Если span = ε = const (минимум), то:
  row_0 ≥ c × ε × N
  Sum(Q) ≥ [row_0]² ≥ c² × ε² × N²
  Sum(G) ≤ 2.5 × N²
  R(1) ≥ c² × ε² / 2.5 = CONST

Это НЕ даёт R(1) → ∞.

ЕДИНСТВЕННЫЙ способ получить R(1) → ∞:
  - Или span → ∞ (эквивалентно TPC)
  - Или sum по ВСЕМ строкам даёт дополнительный фактор
""")

# Check: sum of ALL rows
print("\nПроверка: как растёт Σ|row_k| vs N?")
print(f"{'X':>8} {'N':>6} {'mean|row|':>12} {'mean/N':>10} {'sum|row|/N²':>12}")
print("-" * 55)

for X in X_list[:5]:
    twins = get_twin_primes(X)
    N = len(twins)
    xi = np.log(twins) / (2 * np.pi)

    t = 1.0
    diff = xi[:, None] - xi[None, :]
    K = np.sqrt(2 * np.pi * t) * np.exp(-diff**2 / (8 * t))
    A = -diff * K

    row_sums = np.abs(np.sum(A, axis=1))
    mean_row = np.mean(row_sums)
    sum_row = np.sum(row_sums)

    print(f"{X:>8} {N:>6} {mean_row:>12.2f} {mean_row/N:>10.4f} {sum_row/N**2:>12.4f}")

print("""
НАБЛЮДЕНИЕ:
  mean|row|/N ~ 0.35-0.45 (КОНСТАНТА!)
  sum|row|/N² ~ 0.35-0.45 (КОНСТАНТА!)

Это означает: mean|row| ~ c × N для КАЖДОЙ строки.

ПОЧЕМУ? Потому что span < 2, и все exp(-δ²/8) ≈ 1.

ЕСЛИ mean|row| ~ c × N:
  Sum(Q) = Σ[row_k]² ~ N × (c×N)² = c² × N³
  R(1) ~ N³ / N² = N → ∞

ЭТО РАБОТАЕТ БЕЗ span → ∞!
""")
