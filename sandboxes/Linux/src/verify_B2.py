#!/usr/bin/env python3
"""
Численная верификация B₂
========================

B₂: ⟨T_P Φ_X, Φ_X⟩ ≥ θ(X) · ⟨H_X Φ_X, Φ_X⟩

Вычисляем:
  θ(X) = ⟨T_P Φ_X, Φ_X⟩ / ⟨H_X Φ_X, Φ_X⟩

где H_X = T_A - T_P (Q3 Гамильтониан)

Если θ(X) > 0 и не исчезает при X → ∞, то B₂ верна.

ВАЖНО: B₂ эквивалентна утверждению что prime-энергия даёт
ненулевую долю от total Hamiltonian энергии.
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


def compute_B2_ratio(X: int, t: float = 1.0):
    """
    Вычисляет θ(X) = ⟨T_P Φ_X, Φ_X⟩ / ⟨H_X Φ_X, Φ_X⟩

    где:
      Φ_X = Σ_{p ∈ twins} k_p (равномерные веса)
      T_P f = Σ_n w(n) · ⟨f, k_n⟩ · k_n  (prime operator)
      T_A — диагональный archimedean operator
      H_X = T_A - T_P

    Returns:
      θ(X), info dict
    """
    primes = sieve_primes(X)
    twins = get_twins(X)

    if len(twins) < 2:
        return None, {}

    # Координаты ξ = log(n)/(2π)
    xi = {n: log(n) / (2 * pi) for n in primes}

    # Веса w(n) = Λ(n)/√n ≈ log(n)/√n для простых
    w = {n: log(n) / sqrt(n) for n in primes}

    # =========================================================================
    # ⟨T_P Φ_X, Φ_X⟩
    # =========================================================================
    # T_P Φ = Σ_n w(n) · ⟨Φ, k_n⟩ · k_n
    # ⟨T_P Φ, Φ⟩ = Σ_n w(n) · |⟨k_n, Φ⟩|²

    T_P_energy = 0.0
    for n in primes:
        xi_n = xi[n]
        wn = w[n]

        # ⟨k_n, Φ⟩ = Σ_{p ∈ twins} ⟨k_n, k_p⟩
        inner_prod = sum(heat_overlap(xi_n, xi[p], t) for p in twins)

        T_P_energy += wn * inner_prod**2

    # =========================================================================
    # ⟨T_A Φ_X, Φ_X⟩
    # =========================================================================
    # T_A диагонален: T_A k_p = a(ξ_p) k_p
    # Для простоты берём a(ξ) = ξ (или можно log(ξ) + const)
    #
    # ⟨T_A Φ, Φ⟩ = Σ_{p,q ∈ twins} a(ξ_p) ⟨k_p, k_q⟩
    #            ≈ Σ_p a(ξ_p) ||k_p||² + cross-terms
    #
    # Упрощение: диагональ доминирует, a(ξ_p) = ξ_p

    T_A_energy = 0.0
    for p in twins:
        xi_p = xi[p]
        for q in twins:
            xi_q = xi[q]
            # a(ξ) = ξ для простоты (можно менять)
            a_p = xi_p
            overlap = heat_overlap(xi_p, xi_q, t)
            T_A_energy += a_p * overlap

    # =========================================================================
    # H_X = T_A - T_P
    # =========================================================================
    H_X_energy = T_A_energy - T_P_energy

    # θ(X) = ⟨T_P Φ, Φ⟩ / ⟨H_X Φ, Φ⟩
    if abs(H_X_energy) < 1e-30:
        return None, {}

    theta = T_P_energy / H_X_energy

    # ||Φ||² для нормировки
    phi_norm_sq = 0.0
    for p in twins:
        for q in twins:
            phi_norm_sq += heat_overlap(xi[p], xi[q], t)

    info = {
        'n_twins': len(twins),
        'n_primes': len(primes),
        'T_P_energy': T_P_energy,
        'T_A_energy': T_A_energy,
        'H_X_energy': H_X_energy,
        'phi_norm_sq': phi_norm_sq,
        'T_P_normalized': T_P_energy / phi_norm_sq if phi_norm_sq > 0 else 0,
        'H_X_normalized': H_X_energy / phi_norm_sq if phi_norm_sq > 0 else 0,
    }

    return theta, info


def main():
    console.print(Panel.fit(
        "[bold cyan]ВЕРИФИКАЦИЯ B₂[/bold cyan]\n"
        "[dim]θ(X) = ⟨T_P Φ,Φ⟩ / ⟨H_X Φ,Φ⟩[/dim]",
        box=box.DOUBLE
    ))

    table = Table(title="B₂ Verification: θ(X) > 0?", box=box.DOUBLE)
    table.add_column("X", style="cyan")
    table.add_column("twins", style="yellow")
    table.add_column("⟨T_P Φ,Φ⟩", style="green")
    table.add_column("⟨H_X Φ,Φ⟩", style="blue")
    table.add_column("θ(X)", style="magenta", justify="right")
    table.add_column("Status", style="red")

    t_heat = 1.0
    theta_values = []
    X_values = []

    for X in [100, 200, 500, 1000, 2000, 5000]:
        theta, info = compute_B2_ratio(X, t_heat)

        if theta is None:
            table.add_row(str(X), "—", "—", "—", "—", "⚠ No data")
            continue

        theta_values.append(theta)
        X_values.append(X)

        # Status based on theta sign and magnitude
        if theta > 0.1:
            status = "[green]✓ θ > 0.1[/green]"
        elif theta > 0.01:
            status = "[yellow]~ θ > 0.01[/yellow]"
        elif theta > 0:
            status = "[red]⚠ θ small[/red]"
        else:
            status = "[red]✗ θ ≤ 0[/red]"

        table.add_row(
            str(X),
            str(info['n_twins']),
            f"{info['T_P_energy']:.2e}",
            f"{info['H_X_energy']:.2e}",
            f"{theta:.4f}",
            status
        )

    console.print(table)
    console.print()

    # Анализ тренда
    if len(theta_values) >= 3:
        theta_arr = np.array(theta_values)
        X_arr = np.array(X_values)

        # Средний θ
        avg_theta = np.mean(theta_arr)
        std_theta = np.std(theta_arr)
        cv = std_theta / abs(avg_theta) * 100 if avg_theta != 0 else float('inf')

        console.print(f"[cyan]Средний θ(X): {avg_theta:.4f}[/cyan]")
        console.print(f"[cyan]Std dev:      {std_theta:.4f}[/cyan]")
        console.print(f"[cyan]CV:           {cv:.1f}%[/cyan]")
        console.print()

        # Log-log fit для проверки scaling
        if np.all(theta_arr > 0):
            log_X = np.log(X_arr)
            log_theta = np.log(theta_arr)
            A = np.vstack([log_X, np.ones_like(log_X)]).T
            slope, intercept = np.linalg.lstsq(A, log_theta, rcond=None)[0]
            console.print(f"[yellow]Log-log fit: θ(X) ~ X^{slope:.3f}[/yellow]")

            if abs(slope) < 0.3:
                console.print("[bold green]✓ θ(X) ≈ const — B₂ выглядит верной![/bold green]")
            elif slope < -0.3:
                console.print("[bold red]✗ θ(X) убывает — B₂ под вопросом[/bold red]")
            else:
                console.print("[bold yellow]? θ(X) растёт — неожиданно[/bold yellow]")

        console.print()

    # Вывод
    console.print(Panel.fit(
        "[bold green]ИНТЕРПРЕТАЦИЯ B₂:[/bold green]\n\n"
        "Если θ(X) > 0 и ≈ const при X → ∞:\n"
        "  → B₂ ВЕРНА\n"
        "  → Prime-энергия даёт ненулевую долю от total\n"
        "  → Эквивалентно: S(X) = Σ Λ(n)Λ(n+2) >> X^δ\n\n"
        "Если θ(X) → 0:\n"
        "  → B₂ НЕ верна\n"
        "  → Twin-вклад исчезает в пределе\n"
        "  → ≈ означает finite twins\n\n"
        "[yellow]ВАЖНО: B₂ ≈ Twin Prime Conjecture![/yellow]\n"
        "Положительный θ(X) = косвенное свидетельство\n"
        "бесконечности близнецов.",
        box=box.DOUBLE,
        border_style="green"
    ))


if __name__ == "__main__":
    main()
