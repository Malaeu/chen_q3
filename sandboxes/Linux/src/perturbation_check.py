#!/usr/bin/env python3
"""
Perturbation Check: G^prime vs G^lat
=====================================

Проверяем ключевую гипотезу:
  праймы в log-координатах ≈ равномерная решётка

Измеряем:
  ‖G^prime - G^lat‖_op → 0 при X → ∞ ?

Где:
  ξ_p = log(p)/(2π)  — координаты праймов
  ξ_n = n·Δ          — координаты решётки
  Δ = 1/log(X)       — шаг решётки (по плотности праймов)
"""

import numpy as np
from math import log, pi, sqrt, exp
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def sieve_primes(limit: int) -> list[int]:
    """Решето Эратосфена."""
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]


def G(delta: float, t: float) -> float:
    """Gaussian overlap."""
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def build_gram_matrix(positions: np.ndarray, t: float) -> np.ndarray:
    """Build Gram matrix G_{ij} = G(ξ_i - ξ_j)."""
    N = len(positions)
    G_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = positions[i] - positions[j]
            G_mat[i, j] = G(delta, t)
    return G_mat


def compare_prime_vs_lattice(X: int, t: float = 1.0):
    """
    Сравниваем G^prime и G^lat для праймов до X.

    Returns:
        dict с метриками сравнения
    """
    # Праймы до X
    primes = [p for p in sieve_primes(X) if p > 2]  # skip 2 for cleaner analysis
    N = len(primes)

    if N < 5:
        return None

    # Координаты праймов: ξ_p = log(p)/(2π)
    xi_prime = np.array([log(p) / (2 * pi) for p in primes])

    # Идеальная решётка с шагом Δ = 1/log(X)
    # Центрируем на том же интервале
    xi_min, xi_max = xi_prime.min(), xi_prime.max()
    Delta = 1 / log(X)  # шаг по плотности праймов

    # Строим решётку покрывающую тот же интервал
    n_start = int(xi_min / Delta)
    n_end = int(xi_max / Delta) + 1
    N_lat = n_end - n_start

    # Для fair comparison берём столько же точек
    # Интерполируем решётку на N точек
    xi_lattice = np.linspace(xi_min, xi_max, N)

    # Gram matrices
    G_prime = build_gram_matrix(xi_prime, t)
    G_lattice = build_gram_matrix(xi_lattice, t)

    # Operator norm difference: ‖G^prime - G^lat‖_op = max singular value
    diff = G_prime - G_lattice
    op_norm = np.linalg.norm(diff, ord=2)  # spectral norm

    # Frobenius norm (for comparison)
    frob_norm = np.linalg.norm(diff, ord='fro')

    # Relative error
    G_prime_norm = np.linalg.norm(G_prime, ord=2)
    rel_error = op_norm / G_prime_norm if G_prime_norm > 0 else 0

    # Position deviation: max|ξ_p - ξ_n| / Δ
    # Map each prime to nearest lattice point
    deviations = []
    for xi in xi_prime:
        nearest_lat = xi_lattice[np.argmin(np.abs(xi_lattice - xi))]
        deviations.append(abs(xi - nearest_lat))
    max_dev = max(deviations)
    mean_dev = np.mean(deviations)

    # Effective Δ (average spacing between primes in log-scale)
    prime_spacings = np.diff(xi_prime)
    effective_delta = np.mean(prime_spacings)

    return {
        'X': X,
        'N_primes': N,
        'Delta': Delta,
        'effective_delta': effective_delta,
        'op_norm': op_norm,
        'frob_norm': frob_norm,
        'rel_error': rel_error,
        'max_dev': max_dev,
        'mean_dev': mean_dev,
        'max_dev_over_delta': max_dev / Delta,
    }


def main():
    console.print(Panel.fit(
        "[bold cyan]PERTURBATION CHECK: G^prime vs G^lat[/bold cyan]\n"
        "[dim]Проверяем: ‖G^prime - G^lat‖_op → 0 ?[/dim]",
        box=box.DOUBLE
    ))

    t = 1.0  # heat parameter

    # Scan over different X
    X_values = [100, 200, 500, 1000, 2000, 5000, 10000]

    table = Table(title="Perturbation Analysis", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("#primes", style="blue", justify="right")
    table.add_column("Δ=1/logX", style="green", justify="right")
    table.add_column("‖G^p-G^l‖_op", style="yellow", justify="right")
    table.add_column("rel_error", style="magenta", justify="right")
    table.add_column("max|ξ_p-ξ_n|/Δ", style="red", justify="right")

    results = []
    for X in X_values:
        res = compare_prime_vs_lattice(X, t)
        if res:
            results.append(res)
            table.add_row(
                str(X),
                str(res['N_primes']),
                f"{res['Delta']:.4f}",
                f"{res['op_norm']:.4f}",
                f"{res['rel_error']:.6f}",
                f"{res['max_dev_over_delta']:.4f}"
            )

    console.print(table)

    # Analysis
    console.print("\n" + "="*60)
    console.print("[bold green]АНАЛИЗ РЕЗУЛЬТАТОВ:[/bold green]\n")

    # Check if op_norm decreases
    op_norms = [r['op_norm'] for r in results]
    rel_errors = [r['rel_error'] for r in results]

    # Fit power law: op_norm ~ X^α
    log_X = np.log([r['X'] for r in results])
    log_op = np.log(op_norms)
    alpha, intercept = np.polyfit(log_X, log_op, 1)

    console.print(f"[cyan]Operator norm scaling:[/cyan]")
    console.print(f"  ‖G^p - G^l‖_op ~ X^{alpha:.3f}")

    if alpha > 0:
        console.print(f"  [yellow]⚠️ Op norm РАСТЁТ с X (α = {alpha:.3f} > 0)[/yellow]")
    else:
        console.print(f"  [green]✓ Op norm ПАДАЕТ с X (α = {alpha:.3f} < 0)[/green]")

    # Check relative error
    log_rel = np.log(rel_errors)
    alpha_rel, _ = np.polyfit(log_X, log_rel, 1)

    console.print(f"\n[cyan]Relative error scaling:[/cyan]")
    console.print(f"  rel_error ~ X^{alpha_rel:.3f}")

    if alpha_rel < 0:
        console.print(f"  [green]✓ Relative error ПАДАЕТ![/green]")
    else:
        console.print(f"  [yellow]⚠️ Relative error не падает...[/yellow]")

    # Position deviation analysis
    max_devs = [r['max_dev_over_delta'] for r in results]
    console.print(f"\n[cyan]Position deviation (max|ξ_p - ξ_n|/Δ):[/cyan]")
    console.print(f"  Range: {min(max_devs):.4f} to {max(max_devs):.4f}")

    if max(max_devs) < 1.0:
        console.print(f"  [green]✓ Праймы укладываются в решётку (dev/Δ < 1)[/green]")
    else:
        console.print(f"  [yellow]⚠️ Праймы выходят за пределы ячейки решётки[/yellow]")

    # Verdict
    console.print("\n" + "="*60)

    if alpha_rel < -0.1:
        console.print(Panel.fit(
            "[bold green]✓ PERTURBATION ПОДТВЕРЖДЕНА![/bold green]\n\n"
            f"• Relative error ~ X^{alpha_rel:.3f} → 0\n"
            "• Праймы действительно ≈ решётка в log-координатах\n"
            "• Perturbation lemma правдоподобна!",
            box=box.DOUBLE,
            border_style="green"
        ))
    else:
        console.print(Panel.fit(
            "[bold yellow]⚠️ ТРЕБУЕТСЯ ДОПОЛНИТЕЛЬНЫЙ АНАЛИЗ[/bold yellow]\n\n"
            f"• Scaling не однозначный (α_rel = {alpha_rel:.3f})\n"
            "• Возможно нужна другая нормализация\n"
            "• Или рассматривать только twin-конус",
            box=box.DOUBLE,
            border_style="yellow"
        ))

    return results


if __name__ == "__main__":
    main()
