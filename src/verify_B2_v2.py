#!/usr/bin/env python3
"""
Численная верификация B₂ (версия 2)
====================================

ПЕРЕФОРМУЛИРОВКА:

Старая B₂: ⟨T_P Φ, Φ⟩ ≥ θ · ⟨H_X Φ, Φ⟩
  → Проблема: H_X < 0 на twin-конусе!

Новая B₂: ⟨T_P Φ, Φ⟩ / ‖Φ‖² ≥ θ(X) > 0
  → "Prime density" на twin-векторе

Или эквивалентно:
  ⟨T_P Φ, Φ⟩ ≥ θ · ‖Φ‖²

Это связано с S(X) = Σ Λ(n)Λ(n+2) через:
  ⟨T_P Φ, Φ⟩ ~ S(X)² (грубо)
  ‖Φ‖² ~ T(X) (число близнецов)
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


def compute_B2_v2(X: int, t: float = 1.0):
    """
    Вычисляет несколько метрик для B₂:

    1. θ_norm = ⟨T_P Φ, Φ⟩ / ‖Φ‖²  (prime density)
    2. θ_arch = ⟨T_P Φ, Φ⟩ / ⟨T_A Φ, Φ⟩  (prime/arch ratio)
    3. ratio = |⟨H_X Φ, Φ⟩| / ‖Φ‖²  (spectral gap proxy)
    """
    primes = sieve_primes(X)
    twins = get_twins(X)

    if len(twins) < 2:
        return None

    # Координаты ξ = log(n)/(2π)
    xi = {n: log(n) / (2 * pi) for n in primes}

    # Веса w(n) = Λ(n)/√n ≈ log(n)/√n для простых
    w = {n: log(n) / sqrt(n) for n in primes}

    # ⟨T_P Φ, Φ⟩
    T_P_energy = 0.0
    for n in primes:
        xi_n = xi[n]
        wn = w[n]
        inner_prod = sum(heat_overlap(xi_n, xi[p], t) for p in twins)
        T_P_energy += wn * inner_prod**2

    # ⟨T_A Φ, Φ⟩ с a(ξ) = ξ
    T_A_energy = 0.0
    for p in twins:
        xi_p = xi[p]
        for q in twins:
            xi_q = xi[q]
            a_p = xi_p
            overlap = heat_overlap(xi_p, xi_q, t)
            T_A_energy += a_p * overlap

    # ‖Φ‖²
    phi_norm_sq = 0.0
    for p in twins:
        for q in twins:
            phi_norm_sq += heat_overlap(xi[p], xi[q], t)

    # H_X energy
    H_X_energy = T_A_energy - T_P_energy

    # Метрики
    theta_norm = T_P_energy / phi_norm_sq if phi_norm_sq > 0 else 0
    theta_arch = T_P_energy / T_A_energy if T_A_energy > 0 else float('inf')
    spectral_gap = abs(H_X_energy) / phi_norm_sq if phi_norm_sq > 0 else 0

    # T(X) - twin counting function
    T_X = len(twins)

    # S(X) approximation - sum of Λ(p)Λ(p+2)
    S_X = sum(log(p) * log(p + 2) for p in twins)

    return {
        'n_twins': T_X,
        'n_primes': len(primes),
        'T_P_energy': T_P_energy,
        'T_A_energy': T_A_energy,
        'H_X_energy': H_X_energy,
        'phi_norm_sq': phi_norm_sq,
        'theta_norm': theta_norm,
        'theta_arch': theta_arch,
        'spectral_gap': spectral_gap,
        'S_X': S_X,
        'T_X': T_X,
    }


def main():
    console.print(Panel.fit(
        "[bold cyan]ВЕРИФИКАЦИЯ B₂ v2[/bold cyan]\n"
        "[dim]θ_norm = ⟨T_P Φ,Φ⟩ / ‖Φ‖² (prime density)[/dim]",
        box=box.DOUBLE
    ))

    # Table 1: Basic metrics
    table1 = Table(title="B₂ Metrics: Prime Density", box=box.DOUBLE)
    table1.add_column("X", style="cyan")
    table1.add_column("twins", style="yellow")
    table1.add_column("θ_norm", style="green", justify="right")
    table1.add_column("θ_arch", style="blue", justify="right")
    table1.add_column("|H_X|/‖Φ‖²", style="magenta", justify="right")

    t_heat = 1.0
    results = []

    for X in [100, 200, 500, 1000, 2000, 5000]:
        res = compute_B2_v2(X, t_heat)

        if res is None:
            continue

        results.append((X, res))

        table1.add_row(
            str(X),
            str(res['n_twins']),
            f"{res['theta_norm']:.4f}",
            f"{res['theta_arch']:.4f}",
            f"{res['spectral_gap']:.4f}"
        )

    console.print(table1)
    console.print()

    # Table 2: Twin prime function S(X)
    table2 = Table(title="Twin Prime Function S(X)", box=box.DOUBLE)
    table2.add_column("X", style="cyan")
    table2.add_column("T(X) = #twins", style="yellow")
    table2.add_column("S(X) = ΣΛΛ", style="green")
    table2.add_column("S(X)/X^{0.5}", style="blue")
    table2.add_column("S(X)/T(X)²", style="magenta")

    for X, res in results:
        S_ratio = res['S_X'] / sqrt(X) if X > 0 else 0
        S_T_ratio = res['S_X'] / (res['T_X']**2) if res['T_X'] > 0 else 0

        table2.add_row(
            str(X),
            str(res['T_X']),
            f"{res['S_X']:.1f}",
            f"{S_ratio:.2f}",
            f"{S_T_ratio:.4f}"
        )

    console.print(table2)
    console.print()

    # Scaling analysis
    if len(results) >= 3:
        Xs = np.array([X for X, _ in results])
        theta_norms = np.array([r['theta_norm'] for _, r in results])
        S_Xs = np.array([r['S_X'] for _, r in results])

        # Log-log fit for theta_norm
        if np.all(theta_norms > 0):
            log_X = np.log(Xs)
            log_theta = np.log(theta_norms)
            A = np.vstack([log_X, np.ones_like(log_X)]).T
            slope, _ = np.linalg.lstsq(A, log_theta, rcond=None)[0]
            console.print(f"[yellow]θ_norm scaling: θ ~ X^{slope:.3f}[/yellow]")

        # Log-log fit for S(X)
        if np.all(S_Xs > 0):
            log_S = np.log(S_Xs)
            slope_S, _ = np.linalg.lstsq(A, log_S, rcond=None)[0]
            console.print(f"[yellow]S(X) scaling: S ~ X^{slope_S:.3f}[/yellow]")
            console.print(f"[dim](HL predicts S(X) ~ X / (log X)²)[/dim]")

        console.print()

    # Interpretation
    console.print(Panel.fit(
        "[bold green]ИНТЕРПРЕТАЦИЯ B₂ v2:[/bold green]\n\n"
        "[cyan]θ_norm = ⟨T_P Φ,Φ⟩ / ‖Φ‖²:[/cyan]\n"
        "  • Это 'prime density' на twin-векторе\n"
        "  • Если θ_norm ~ const > 0: B₂ верна\n"
        "  • Если θ_norm → 0: twin-вклад исчезает\n\n"
        "[cyan]θ_arch = ⟨T_P Φ,Φ⟩ / ⟨T_A Φ,Φ⟩:[/cyan]\n"
        "  • Если > 1: prime доминирует над arch!\n"
        "  • Это ХОРОШО для twin-conjecture\n\n"
        "[cyan]S(X) = Σ Λ(p)Λ(p+2):[/cyan]\n"
        "  • HL: S(X) ~ 2C₂ X / (log X)² где C₂ ≈ 0.66\n"
        "  • Если S(X) → const: finite twins\n"
        "  • Если S(X) ~ X^α, α > 0: infinite twins\n",
        box=box.DOUBLE,
        border_style="green"
    ))


if __name__ == "__main__":
    main()
