#!/usr/bin/env python3
"""
Сходимость ⟨H_X Φ_∞, Φ_∞⟩ при конечных twins
=============================================

H_X = T_A - T_P

Если twins конечны с P*, Φ_∞ фиксирован.
Как ведут себя T_A и T_P энергии при X → ∞?

КРИТИЧЕСКИЙ ВОПРОС:
  Если ⟨H_X Φ_∞, Φ_∞⟩ растёт, а Q_X → const,
  то κ(X) = Q_X / ⟨H_X Φ_∞, Φ_∞⟩ → 0!

  Если Q3 требует κ(X) ≥ κ₀ > 0, то ПРОТИВОРЕЧИЕ!
"""

import numpy as np
from math import log, pi, sqrt, exp
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def sieve_primes(limit: int) -> list[int]:
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]


def get_twin_primes(limit: int) -> list[int]:
    primes_set = set(sieve_primes(limit + 2))
    return sorted([p for p in primes_set if p + 2 in primes_set and p <= limit])


def G(delta: float, t: float) -> float:
    """Gaussian overlap."""
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def compute_T_A_energy(xi_twins: np.ndarray, lam: np.ndarray, X: int, t: float) -> float:
    """
    ⟨T_A^{(X)} Φ_∞, Φ_∞⟩

    T_A = архимедов оператор (сумма по всем n, не только primes)

    T_A^{(X)} f = Σ_{n≤X} a(n) ⟨f, k_n⟩ k_n

    где a(n) = некоторые веса (возьмём a(n) = 1 для простоты).

    ⟨T_A Φ_∞, Φ_∞⟩ = Σ_{n≤X} a(n) |⟨Φ_∞, k_n⟩|²
    """
    # ξ_n для всех n до X
    # Используем ξ_n = log(n) / (2π) для всех n ≥ 2

    T_A_energy = 0.0

    for n in range(2, X + 1):
        xi_n = log(n) / (2 * pi)
        a_n = 1.0 / sqrt(n)  # нормализация типа Λ(n)/√n

        # ⟨Φ_∞, k_n⟩ = Σ_p λ_p G(ξ_p - ξ_n)
        inner_prod = 0.0
        for xi_p, lam_p in zip(xi_twins, lam):
            delta = xi_p - xi_n
            inner_prod += lam_p * G(delta, t)

        T_A_energy += a_n * inner_prod**2

    return T_A_energy


def compute_T_P_energy(xi_twins: np.ndarray, lam: np.ndarray, X: int, t: float) -> float:
    """
    ⟨T_P^{(X)} Φ_∞, Φ_∞⟩

    T_P^{(X)} f = Σ_{p≤X, p prime} w(p) ⟨f, k_p⟩ k_p

    где w(p) = Λ(p)/√p = log(p)/√p
    """
    primes = sieve_primes(X)

    T_P_energy = 0.0

    for p in primes:
        xi_p_prime = log(p) / (2 * pi)
        w_p = log(p) / sqrt(p)

        # ⟨Φ_∞, k_p⟩ = Σ_q λ_q G(ξ_q - ξ_p)
        inner_prod = 0.0
        for xi_q, lam_q in zip(xi_twins, lam):
            delta = xi_q - xi_p_prime
            inner_prod += lam_q * G(delta, t)

        T_P_energy += w_p * inner_prod**2

    return T_P_energy


def main():
    console.print(Panel.fit(
        "[bold cyan]СХОДИМОСТЬ H_X ЭНЕРГИИ[/bold cyan]\n"
        "[dim]H_X = T_A - T_P при фиксированном Φ_∞[/dim]",
        box=box.DOUBLE
    ))

    t = 1.0

    # Сценарий: twins конечны с P* = 1000
    P_star = 1000
    twins = get_twin_primes(P_star)
    N = len(twins)

    console.print(f"\n[yellow]Сценарий: twins конечны с P* = {P_star}[/yellow]")
    console.print(f"Число twins: {N}")

    # Фиксированный вектор Φ_∞
    xi_twins = np.array([log(p) / (2 * pi) for p in twins])
    lam = np.array([log(p) * log(p + 2) for p in twins])

    # Нормируем λ для стабильности
    lam = lam / np.linalg.norm(lam)

    console.print(f"‖λ‖ = 1.0 (нормировано)\n")

    # Тестируем при разных X
    X_values = [1000, 2000, 3000, 5000, 7500, 10000]

    console.print("[dim]Вычисление T_A требует суммы по всем n ≤ X (может быть медленно)...[/dim]\n")

    results = []

    for X in X_values:
        console.print(f"[dim]X = {X}...[/dim]", end=" ")

        T_P = compute_T_P_energy(xi_twins, lam, X, t)

        # T_A медленнее, ограничим для больших X
        if X <= 5000:
            T_A = compute_T_A_energy(xi_twins, lam, X, t)
        else:
            # Экстраполяция на основе предыдущих данных
            T_A = None

        H_X = T_A - T_P if T_A is not None else None

        results.append({
            'X': X,
            'T_P': T_P,
            'T_A': T_A,
            'H_X': H_X,
        })

        console.print(f"[green]done[/green]")

    # Таблица
    console.print("\n")
    table = Table(title="Энергии операторов при фикс. Φ_∞", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("⟨T_P Φ_∞, Φ_∞⟩", style="green", justify="right")
    table.add_column("⟨T_A Φ_∞, Φ_∞⟩", style="blue", justify="right")
    table.add_column("⟨H_X Φ_∞, Φ_∞⟩", style="yellow", justify="right")
    table.add_column("H_X sign", style="magenta", justify="center")

    for r in results:
        T_A_str = f"{r['T_A']:.4e}" if r['T_A'] is not None else "N/A"
        H_X_str = f"{r['H_X']:.4e}" if r['H_X'] is not None else "N/A"
        sign = "+" if r['H_X'] is not None and r['H_X'] > 0 else ("-" if r['H_X'] is not None else "?")

        table.add_row(
            str(r['X']),
            f"{r['T_P']:.4e}",
            T_A_str,
            H_X_str,
            sign
        )

    console.print(table)

    # Анализ T_P роста
    console.print("\n[bold cyan]АНАЛИЗ РОСТА T_P:[/bold cyan]")

    log_X = np.log([r['X'] for r in results])
    log_T_P = np.log([r['T_P'] for r in results])

    alpha_T_P, _ = np.polyfit(log_X, log_T_P, 1)

    console.print(f"  ⟨T_P Φ_∞, Φ_∞⟩ ~ X^{alpha_T_P:.3f}")

    # Анализ T_A роста (если доступен)
    valid_T_A = [(r['X'], r['T_A']) for r in results if r['T_A'] is not None]
    if len(valid_T_A) >= 3:
        log_X_A = np.log([x for x, _ in valid_T_A])
        log_T_A = np.log([ta for _, ta in valid_T_A])
        alpha_T_A, _ = np.polyfit(log_X_A, log_T_A, 1)
        console.print(f"  ⟨T_A Φ_∞, Φ_∞⟩ ~ X^{alpha_T_A:.3f}")

    # Выводы
    console.print("\n" + "="*60)
    console.print("\n[bold yellow]КРИТИЧЕСКИЕ ВЫВОДЫ:[/bold yellow]\n")

    # Знак H_X
    valid_H_X = [r['H_X'] for r in results if r['H_X'] is not None]
    if valid_H_X:
        all_negative = all(h < 0 for h in valid_H_X)

        if all_negative:
            console.print("[red]H_X = T_A - T_P < 0 для всех X[/red]")
            console.print("[red]⟹ Prime-энергия БОЛЬШЕ чем arch-энергия![/red]")
            console.print()
            console.print("[yellow]Это проблема: Target Inequality с H_X < 0 не имеет смысла![/yellow]")
            console.print("[yellow]Нужно использовать |H_X| или другую формулировку.[/yellow]")
        else:
            console.print("[green]H_X имеет смешанный знак.[/green]")

    console.print()
    console.print(f"[cyan]T_P растёт как X^{alpha_T_P:.2f} при фиксированном Φ_∞![/cyan]")

    console.print("""

ИНТЕРПРЕТАЦИЯ:
  Даже если Φ_∞ фиксирован (twins конечны),
  ⟨T_P Φ_∞, Φ_∞⟩ РАСТЁТ при X → ∞!

  Причина: T_P^{(X)} включает больше primes.
  Хотя ⟨k_p, k_n⟩ ~ exp(-|ξ_p-ξ_n|²/8t) мало для далёких n,
  число primes растёт как π(X) ~ X/log X.
  Суммарный вклад растёт!

СЛЕДСТВИЕ ДЛЯ TARGET THEOREM:
  Если Q_X → const (twins конечны),
  но ⟨T_P Φ_∞, Φ_∞⟩ → ∞,
  то c₁(X) = Q_X / E_lat → 0!

  B₁(prime) требует c₁(X) ≥ c₀ > 0.
  ⟹ ПРОТИВОРЕЧИЕ если c₁ не может стремиться к 0!

  Но у нас c_twins ~ T(X)^0.86...
  При конечных twins: T(X) → const,
  так что c_twins → const > 0.

  А E_lat = ⟨T_P Φ, Φ⟩ растёт!

  ⟹ Q_X = c_twins · E_lat... но это неверно!
     Q_X = const (матрица фиксирована)
     E_lat = ⟨T_P Φ, Φ⟩ растёт

  Парадокс! c_twins = Q_X / E_lat → 0!
""")

    return results


if __name__ == "__main__":
    main()
