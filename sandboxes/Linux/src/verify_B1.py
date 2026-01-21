#!/usr/bin/env python3
"""
Численная верификация B₁
========================

B₁: ‖[T_P, Ξ] Φ_X‖² ≥ c₁(X) · ⟨T_P Φ_X, Φ_X⟩

Вычисляем:
  c₁(X) = ‖[T_P, Ξ] Φ_X‖² / ⟨T_P Φ_X, Φ_X⟩

Если c₁(X) > 0 и не исчезает при X → ∞, то B₁ верна.
"""

import numpy as np
from math import log, pi, sqrt, exp
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def sieve_primes(n_max: int) -> list:
    if n_max < 2:
        return []
    sieve = [True] * (n_max + 1)
    sieve[0] = sieve[1] = False
    for x in range(2, int(n_max**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n_max + 1, x):
                sieve[i] = False
    return [x for x in range(2, n_max + 1) if sieve[x]]


def get_twins(X: int) -> list:
    """Возвращает список p где (p, p+2) — twin pair."""
    primes = set(sieve_primes(X + 2))
    return [p for p in sorted(primes) if p + 2 in primes and p <= X]


def heat_kernel(xi1: float, xi2: float, t: float) -> float:
    """K_t(ξ₁, ξ₂) = exp(-(ξ₁-ξ₂)²/(4t))."""
    return exp(-(xi1 - xi2)**2 / (4 * t))


def heat_overlap(xi_q: float, xi_p: float, t: float) -> float:
    """⟨k_q, k_p⟩ = √(2πt) · K_{2t}(ξ_q, ξ_p)."""
    return sqrt(2 * pi * t) * heat_kernel(xi_q, xi_p, 2 * t)


def compute_B1_ratio(X: int, t: float = 1.0):
    """
    Вычисляет c₁(X) = ‖[T_P, Ξ] Φ_X‖² / ⟨T_P Φ_X, Φ_X⟩

    где Φ_X = Σ_{p ∈ twins} k_p (равномерные веса)
    """
    primes = sieve_primes(X)
    twins = get_twins(X)

    if len(twins) < 2:
        return None, {}

    # Координаты ξ = log(n)/(2π)
    xi = {n: log(n) / (2 * pi) for n in primes}

    # Веса w(n) = Λ(n)/√n ≈ log(n)/√n для простых
    w = {n: log(n) / sqrt(n) for n in primes}

    # Twin-вектор: Φ_X = Σ_{p ∈ twins} k_p
    # Используем равномерные веса λ_p = 1

    # =========================================================================
    # ЧИСЛИТЕЛЬ: ‖[T_P, Ξ] Φ_X‖²
    # =========================================================================
    # Формула: ‖[T_P, Ξ] Φ‖² = Σ_n w(n)² · |⟨(Ξ - ξ_n)k_n, Φ⟩|²
    #
    # где ⟨(Ξ - ξ_n)k_n, Φ⟩ = Σ_p λ_p ⟨(Ξ - ξ_n)k_n, k_p⟩
    #                       = Σ_p λ_p · (ξ_p - ξ_n) · ⟨k_n, k_p⟩  [приближение]
    #
    # Более точно: ⟨∂k_n, k_p⟩ где ∂k_n(ξ) = (ξ - ξ_n) k_n(ξ)
    # Формула: ⟨∂k_n, k_p⟩ = (ξ_p - ξ_n)/2 · √(2πt) · K_{2t}(ξ_n, ξ_p)

    def deriv_overlap(xi_n, xi_p, t):
        """⟨∂k_n, k_p⟩ = (ξ_p - ξ_n)/2 · √(2πt) · K_{2t}"""
        delta = xi_p - xi_n
        return (delta / 2) * sqrt(2 * pi * t) * heat_kernel(xi_n, xi_p, 2 * t)

    numerator = 0.0
    for n in primes:
        xi_n = xi[n]
        wn = w[n]

        # ⟨∂k_n, Φ⟩ = Σ_{p ∈ twins} ⟨∂k_n, k_p⟩
        inner_prod = sum(deriv_overlap(xi_n, xi[p], t) for p in twins)

        numerator += wn**2 * inner_prod**2

    # =========================================================================
    # ЗНАМЕНАТЕЛЬ: ⟨T_P Φ_X, Φ_X⟩
    # =========================================================================
    # Формула: ⟨T_P Φ, Φ⟩ = Σ_n w(n) · |⟨k_n, Φ⟩|²
    #
    # где ⟨k_n, Φ⟩ = Σ_p λ_p ⟨k_n, k_p⟩ = Σ_p heat_overlap(ξ_n, ξ_p, t)

    denominator = 0.0
    for n in primes:
        xi_n = xi[n]
        wn = w[n]

        # ⟨k_n, Φ⟩ = Σ_{p ∈ twins} ⟨k_n, k_p⟩
        inner_prod = sum(heat_overlap(xi_n, xi[p], t) for p in twins)

        denominator += wn * inner_prod**2

    # c₁(X) = numerator / denominator
    if denominator < 1e-30:
        return None, {}

    c1 = numerator / denominator

    info = {
        'n_twins': len(twins),
        'n_primes': len(primes),
        'numerator': numerator,
        'denominator': denominator,
    }

    return c1, info


def main():
    console.print(Panel.fit(
        "[bold cyan]ВЕРИФИКАЦИЯ B₁[/bold cyan]\n"
        "[dim]c₁(X) = ‖[T_P,Ξ]Φ‖² / ⟨T_P Φ,Φ⟩[/dim]",
        box=box.DOUBLE
    ))

    table = Table(title="B₁ Verification: c₁(X) > 0?", box=box.DOUBLE)
    table.add_column("X", style="cyan")
    table.add_column("twins", style="yellow")
    table.add_column("‖[T_P,Ξ]Φ‖²", style="green")
    table.add_column("⟨T_P Φ,Φ⟩", style="blue")
    table.add_column("c₁(X)", style="magenta", justify="right")
    table.add_column("Status", style="red")

    t_heat = 1.0
    c1_values = []
    X_values = []

    for X in [100, 200, 500, 1000, 2000, 5000]:
        c1, info = compute_B1_ratio(X, t_heat)

        if c1 is None:
            table.add_row(str(X), "—", "—", "—", "—", "⚠ No data")
            continue

        c1_values.append(c1)
        X_values.append(X)

        status = "[green]✓ c₁ > 0[/green]" if c1 > 0.01 else "[red]✗ c₁ ≈ 0[/red]"

        table.add_row(
            str(X),
            str(info['n_twins']),
            f"{info['numerator']:.2e}",
            f"{info['denominator']:.2e}",
            f"{c1:.4f}",
            status
        )

    console.print(table)
    console.print()

    # Анализ тренда
    if len(c1_values) >= 3:
        c1_arr = np.array(c1_values)
        X_arr = np.array(X_values)

        # Средний c₁
        avg_c1 = np.mean(c1_arr)
        std_c1 = np.std(c1_arr)
        cv = std_c1 / avg_c1 * 100 if avg_c1 > 0 else float('inf')

        console.print(f"[cyan]Средний c₁(X): {avg_c1:.4f}[/cyan]")
        console.print(f"[cyan]Std dev:       {std_c1:.4f}[/cyan]")
        console.print(f"[cyan]CV:            {cv:.1f}%[/cyan]")
        console.print()

        # Log-log fit для проверки scaling
        if np.all(c1_arr > 0):
            log_X = np.log(X_arr)
            log_c1 = np.log(c1_arr)
            A = np.vstack([log_X, np.ones_like(log_X)]).T
            slope, intercept = np.linalg.lstsq(A, log_c1, rcond=None)[0]
            console.print(f"[yellow]Log-log fit: c₁(X) ~ X^{slope:.3f}[/yellow]")

            if abs(slope) < 0.3:
                console.print("[bold green]✓ c₁(X) ≈ const — B₁ выглядит верной![/bold green]")
            elif slope < -0.3:
                console.print("[bold red]✗ c₁(X) убывает — B₁ под вопросом[/bold red]")
            else:
                console.print("[bold yellow]? c₁(X) растёт — неожиданно, но хорошо[/bold yellow]")

        console.print()

    # Вывод
    console.print(Panel.fit(
        "[bold green]ИНТЕРПРЕТАЦИЯ B₁:[/bold green]\n\n"
        "Если c₁(X) ≈ const > 0 при X → ∞:\n"
        "  → B₁ ВЕРНА\n"
        "  → Коммутатор доминирует prime-энергию\n"
        "  → Можно доказать аналитически (Talagrand-style)\n\n"
        "Если c₁(X) → 0:\n"
        "  → B₁ НЕ верна в такой форме\n"
        "  → Нужна другая формулировка\n",
        box=box.DOUBLE,
        border_style="green"
    ))


if __name__ == "__main__":
    main()
