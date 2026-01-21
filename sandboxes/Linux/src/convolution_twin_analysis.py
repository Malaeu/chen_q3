#!/usr/bin/env python3
"""
CONVOLUTION APPROACH: S₂(X) через Fourier

КЛЮЧЕВАЯ ИДЕЯ:
  S₂(X) = Σ Λ(n)Λ(n+2) = Σ Λ(n) · (Λ * δ_{-2})(n)

В Fourier:
  Λ̂(ξ) = Fourier transform of Λ
  δ̂_{-2}(ξ) = e^{-4πiξ}  (сдвиг на 2)

  (Λ * δ_{-2})^ = Λ̂(ξ) · e^{-4πiξ}

По Parseval:
  S₂(X) ~ ∫ |Λ̂(ξ)|² · e^{-4πiξ} · φ̂(ξ) dξ

где φ — cutoff функция.

СВЯЗЬ С НУЛЯМИ ζ:
  Λ̂(ξ) имеет пики на Im(ρ)/(2π) где ρ — нули ζ!
"""

import numpy as np
from typing import Tuple, List
import warnings
warnings.filterwarnings('ignore')

def sieve_primes(X: int) -> List[int]:
    """All primes up to X."""
    if X < 2:
        return []
    sieve = [True] * (X + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(X**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, X + 1, i):
                sieve[j] = False
    return [p for p in range(2, X + 1) if sieve[p]]

def Lambda_function(X: int) -> np.ndarray:
    """von Mangoldt function as array."""
    Lambda = np.zeros(X + 1)
    primes = sieve_primes(X)

    for p in primes:
        # p^k ≤ X
        pk = p
        while pk <= X:
            Lambda[pk] = np.log(p)
            pk *= p

    return Lambda

def compute_S2(X: int) -> float:
    """S₂(X) = Σ_{n ≤ X} Λ(n)Λ(n+2)"""
    Lambda = Lambda_function(X + 2)
    S2 = 0.0
    for n in range(2, X + 1):
        S2 += Lambda[n] * Lambda[n + 2]
    return S2

def fourier_Lambda(Lambda: np.ndarray, xi_values: np.ndarray) -> np.ndarray:
    """
    Compute Λ̂(ξ) = Σ_{n=2}^{N} Λ(n) · e^{-2πi·n·ξ}
    """
    N = len(Lambda) - 1
    result = np.zeros(len(xi_values), dtype=complex)

    for k, xi in enumerate(xi_values):
        for n in range(2, N + 1):
            if Lambda[n] > 0:
                result[k] += Lambda[n] * np.exp(-2j * np.pi * n * xi)

    return result

def compute_twin_fourier_integral(X: int, num_xi: int = 1000) -> Tuple[float, float]:
    """
    Compute S₂ через Fourier:
    S₂ ≈ (1/L) · Σ_ξ |Λ̂(ξ)|² · e^{-4πiξ}

    где L = длина интервала ξ.
    """
    Lambda = Lambda_function(X)

    # ξ values: focus on [0, 1] period
    xi_values = np.linspace(0, 1, num_xi, endpoint=False)
    d_xi = xi_values[1] - xi_values[0]

    # Compute Λ̂(ξ)
    Lambda_hat = fourier_Lambda(Lambda, xi_values)

    # |Λ̂(ξ)|² · e^{-4πiξ}
    phase = np.exp(-4j * np.pi * xi_values)
    integrand = np.abs(Lambda_hat)**2 * phase

    # Integral (real part)
    integral = np.sum(integrand) * d_xi
    S2_fourier = np.real(integral)

    # Direct S₂
    S2_direct = compute_S2(X)

    return S2_fourier, S2_direct

def analyze_phase_contribution(X: int) -> dict:
    """
    Analyze how phase e^{-4πiξ} affects the integral.
    """
    Lambda = Lambda_function(X)
    num_xi = 500
    xi_values = np.linspace(0, 1, num_xi, endpoint=False)

    Lambda_hat = fourier_Lambda(Lambda, xi_values)

    # Without phase: |Λ̂|² dξ
    no_phase = np.sum(np.abs(Lambda_hat)**2) / num_xi

    # With phase: |Λ̂|² · e^{-4πiξ} dξ
    phase = np.exp(-4j * np.pi * xi_values)
    with_phase = np.real(np.sum(np.abs(Lambda_hat)**2 * phase)) / num_xi

    # Phase contribution ratio
    ratio = with_phase / no_phase if no_phase > 0 else 0

    return {
        'no_phase': no_phase,
        'with_phase': with_phase,
        'ratio': ratio
    }

def main():
    print("=" * 70)
    print("CONVOLUTION APPROACH: S₂(X) через Fourier")
    print("=" * 70)

    print("""
ТЕОРИЯ:
  S₂(X) = Σ Λ(n)Λ(n+2) = Σ Λ(n) · (Λ * δ_{-2})(n)

В Fourier пространстве:
  S₂ ~ ∫ |Λ̂(ξ)|² · e^{-4πiξ} dξ

Фазовый множитель e^{-4πiξ} кодирует сдвиг на 2!

Без фазы: ∫ |Λ̂(ξ)|² dξ = Σ Λ(n)² (Parseval)
С фазой:  ∫ |Λ̂(ξ)|² · e^{-4πiξ} dξ ~ S₂

ВОПРОС: Как фаза влияет на результат?
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 1: Parseval без фазы vs S₂")
    print("=" * 70)

    print(f"{'X':>7} {'Σ Λ²':>12} {'S₂(X)':>12} {'ratio':>10}")
    print("-" * 45)

    for X in [100, 200, 500, 1000]:
        Lambda = Lambda_function(X + 2)
        sum_L2 = np.sum(Lambda**2)
        S2 = compute_S2(X)
        ratio = S2 / sum_L2 if sum_L2 > 0 else 0

        print(f"{X:>7} {sum_L2:>12.2f} {S2:>12.2f} {ratio:>10.4f}")

    print("""
S₂ / Σ Λ² ~ 0.1-0.2 и УБЫВАЕТ!

Это показывает что twins — малая часть всех prime powers.
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 2: Phase contribution")
    print("=" * 70)

    print(f"{'X':>7} {'no_phase':>12} {'with_phase':>12} {'ratio':>10}")
    print("-" * 45)

    for X in [100, 200, 500]:
        result = analyze_phase_contribution(X)
        print(f"{X:>7} {result['no_phase']:>12.2f} {result['with_phase']:>12.2f} {result['ratio']:>10.4f}")

    print("""
АНАЛИЗ:
  ratio = (with_phase) / (no_phase) ~ 0.1-0.2

  Фазовый множитель e^{-4πiξ} "выделяет" twin contribution!
  Но результат мал потому что twins редки.
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 3: Λ̂(ξ) структура")
    print("=" * 70)

    X = 500
    Lambda = Lambda_function(X)
    num_xi = 200
    xi_values = np.linspace(0, 0.5, num_xi)  # Half period

    Lambda_hat = fourier_Lambda(Lambda, xi_values)

    # Find peaks
    magnitudes = np.abs(Lambda_hat)
    peak_indices = np.argsort(magnitudes)[-5:][::-1]

    print(f"X = {X}")
    print("\nТоп-5 peaks в |Λ̂(ξ)|:")
    print(f"{'ξ':>10} {'|Λ̂(ξ)|':>12}")
    print("-" * 25)

    for idx in peak_indices:
        print(f"{xi_values[idx]:>10.4f} {magnitudes[idx]:>12.2f}")

    print("""
СВЯЗЬ С НУЛЯМИ ζ:
  Пики Λ̂(ξ) на ξ ~ Im(ρ_k)/(2π)
  где ρ_k — нетривиальные нули ζ(s).

  Первые нули: ρ_1 ≈ 14.13, ρ_2 ≈ 21.02, ...
  Ожидаемые ξ: 14.13/(2π) ≈ 2.25, 21.02/(2π) ≈ 3.35, ...

  Но мы смотрим на ξ ∈ [0, 0.5] — это низкочастотная часть!
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 4: Explicit formula connection")
    print("=" * 70)

    print("""
EXPLICIT FORMULA (Riemann-von Mangoldt):

  ψ(x) = Σ_{n ≤ x} Λ(n) = x - Σ_ρ x^ρ/ρ - log(2π) - (1/2)log(1-x^{-2})

где сумма по нулям ρ функции ζ(s).

ДЛЯ TWINS нужна ДВОЙНАЯ формула:

  ψ_2(x) = Σ_{n ≤ x} Λ(n)Λ(n+2)

ПРОБЛЕМА: Нет известной explicit formula для ψ_2!

Hardy-Littlewood ПРЕДПОЛАГАЛИ:
  ψ_2(x) ~ 2C₂ · x

но это КОНЪЕКТУРА, не теорема!
""")

    print("\n" + "=" * 70)
    print("ЭКСПЕРИМЕНТ 5: Phase as twin detector")
    print("=" * 70)

    print("""
ИДЕЯ: Фаза e^{-4πiξ} = e^{-2πi·2ξ} соответствует сдвигу на 2.

Для РАЗНЫХ сдвигов h:
  e^{-2πi·h·ξ} выделяет пары (n, n+h)

Проверим для h = 2, 4, 6:
""")

    X = 500
    Lambda = Lambda_function(X + 6)
    num_xi = 300
    xi_values = np.linspace(0, 1, num_xi, endpoint=False)
    d_xi = 1.0 / num_xi

    Lambda_hat = fourier_Lambda(Lambda[:X+1], xi_values)

    print(f"{'h':>5} {'S_h (direct)':>15} {'S_h (Fourier)':>15} {'ratio':>10}")
    print("-" * 50)

    for h in [2, 4, 6, 8, 10]:
        # Direct sum
        S_h_direct = sum(Lambda[n] * Lambda[n + h] for n in range(2, X + 1 - h))

        # Fourier: ∫ |Λ̂|² · e^{-2πi·h·ξ} dξ
        phase_h = np.exp(-2j * np.pi * h * xi_values)
        S_h_fourier = np.real(np.sum(np.abs(Lambda_hat)**2 * phase_h) * d_xi)

        ratio = S_h_fourier / S_h_direct if S_h_direct > 0 else 0

        print(f"{h:>5} {S_h_direct:>15.2f} {S_h_fourier:>15.2f} {ratio:>10.4f}")

    print("""
ВЫВОД:
  Fourier с фазой e^{-2πi·h·ξ} действительно выделяет S_h!
  Но это не даёт BOUND, только представление.
""")

    print("\n" + "=" * 70)
    print("ФИНАЛЬНЫЙ ВЫВОД:")
    print("=" * 70)

    print("""
🎯 CONVOLUTION APPROACH:

  S₂(X) = ∫ |Λ̂(ξ)|² · e^{-4πiξ} dξ  (representation)

  ПЛЮСЫ:
  + Фаза e^{-4πiξ} естественно выделяет twins
  + Связь с Fourier структурой Λ
  + Λ̂(ξ) имеет пики на Im(ρ)/(2π) (связь с нулями ζ)

  МИНУСЫ:
  - Не даёт LOWER BOUND на S₂
  - Нет explicit formula для ψ_2(x)
  - Нули ζ дают ОСЦИЛЛЯЦИИ, не bounds

🚨 ПРОБЛЕМА:
  RH говорит что нули на Re(s) = 1/2
  Это контролирует ОШИБКУ в ψ(x) - x
  НО не даёт bound на S₂(x)!

  Hardy-Littlewood: S₂(x) ~ 2C₂·x — это КОНЪЕКТУРА!

  Связь RH → TPC остаётся ОТКРЫТОЙ проблемой!
""")

if __name__ == "__main__":
    main()
