#!/usr/bin/env python3
"""
Perturbation Check: TWIN CONE VERSION
======================================

Сравниваем E_comm и E_lat для:
1. Реальных праймов (twin pairs)
2. Идеальной решётки (twin-like spacing)

Ключевой вопрос:
  c₁^prime / c₁^lat ≈ 1 при X → ∞ ?
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


def get_twin_primes(limit: int) -> list[int]:
    """Возвращает праймы p где p и p+2 оба простые."""
    primes_set = set(sieve_primes(limit + 2))
    return [p for p in primes_set if p + 2 in primes_set and p <= limit]


def G(delta: float, t: float) -> float:
    """Gaussian overlap."""
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def compute_energies(positions: np.ndarray, t: float) -> dict:
    """
    Вычисляем E_lat и E_comm для данных позиций.

    Returns:
        dict с E_lat, E_comm, ratio
    """
    N = len(positions)
    if N < 2:
        return None

    # Build Gram matrix
    G_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = positions[i] - positions[j]
            G_mat[i, j] = G(delta, t)

    # Build Xi matrix: ⟨ξ·k_i, k_j⟩ = (ξ_i + ξ_j)/2 · G_ij
    Xi_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

    # Test vector: uniform on cone (λ = 1)
    lam = np.ones(N)

    # E_lat = ‖G·λ‖²
    inner_prods = G_mat @ lam
    E_lat = np.sum(inner_prods**2)

    # E_comm = cᵀ G c where c = ξ⊙(Gλ) - Ξλ
    xi_inner_prods = Xi_mat @ lam
    c_coeffs = positions * inner_prods - xi_inner_prods
    E_comm = c_coeffs @ G_mat @ c_coeffs

    # Ratio
    ratio = E_comm / E_lat if E_lat > 1e-15 else 0

    return {
        'N': N,
        'E_lat': E_lat,
        'E_comm': E_comm,
        'ratio': ratio,
    }


def compare_twins_vs_lattice(X: int, t: float = 1.0):
    """
    Сравниваем:
    1. Twin primes в log-координатах
    2. Идеальная решётка с тем же spacing
    """
    # Twin primes
    twins = get_twin_primes(X)
    if len(twins) < 5:
        return None

    # Координаты twins: ξ_p = log(p)/(2π)
    xi_twins = np.array([log(p) / (2 * pi) for p in twins])

    # Идеальная решётка с тем же числом точек и тем же интервалом
    xi_min, xi_max = xi_twins.min(), xi_twins.max()
    xi_lattice = np.linspace(xi_min, xi_max, len(twins))

    # Compute energies for both
    res_twins = compute_energies(xi_twins, t)
    res_lattice = compute_energies(xi_lattice, t)

    if res_twins is None or res_lattice is None:
        return None

    # Position deviation analysis
    # For each twin, find closest lattice point
    deviations = []
    Delta = (xi_max - xi_min) / (len(twins) - 1) if len(twins) > 1 else 1
    for xi in xi_twins:
        nearest = xi_lattice[np.argmin(np.abs(xi_lattice - xi))]
        deviations.append(abs(xi - nearest) / Delta)
    max_dev = max(deviations)
    mean_dev = np.mean(deviations)

    return {
        'X': X,
        'N_twins': len(twins),
        'Delta': Delta,
        'E_lat_twins': res_twins['E_lat'],
        'E_comm_twins': res_twins['E_comm'],
        'c_twins': res_twins['ratio'],
        'E_lat_lattice': res_lattice['E_lat'],
        'E_comm_lattice': res_lattice['E_comm'],
        'c_lattice': res_lattice['ratio'],
        'c_ratio': res_twins['ratio'] / res_lattice['ratio'] if res_lattice['ratio'] > 0 else 0,
        'max_dev': max_dev,
        'mean_dev': mean_dev,
    }


def main():
    console.print(Panel.fit(
        "[bold cyan]PERTURBATION: TWIN CONE[/bold cyan]\n"
        "[dim]Сравниваем c₁^twins vs c₁^lattice[/dim]",
        box=box.DOUBLE
    ))

    t = 1.0

    X_values = [100, 200, 500, 1000, 2000, 5000, 10000, 20000]

    table = Table(title="Twin Cone Perturbation", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("#twins", style="blue", justify="right")
    table.add_column("c_twins", style="green", justify="right")
    table.add_column("c_lattice", style="yellow", justify="right")
    table.add_column("c_twins/c_lat", style="magenta", justify="right")
    table.add_column("max_dev/Δ", style="red", justify="right")

    results = []
    for X in X_values:
        res = compare_twins_vs_lattice(X, t)
        if res:
            results.append(res)
            table.add_row(
                str(X),
                str(res['N_twins']),
                f"{res['c_twins']:.4f}",
                f"{res['c_lattice']:.4f}",
                f"{res['c_ratio']:.4f}",
                f"{res['max_dev']:.4f}"
            )

    console.print(table)

    # Analysis
    console.print("\n" + "="*60)
    console.print("[bold green]АНАЛИЗ:[/bold green]\n")

    c_ratios = [r['c_ratio'] for r in results]
    c_twins = [r['c_twins'] for r in results]
    c_lattice = [r['c_lattice'] for r in results]
    max_devs = [r['max_dev'] for r in results]

    console.print(f"[cyan]c_twins range:[/cyan] {min(c_twins):.4f} to {max(c_twins):.4f}")
    console.print(f"[cyan]c_lattice range:[/cyan] {min(c_lattice):.4f} to {max(c_lattice):.4f}")
    console.print(f"[cyan]c_twins/c_lattice:[/cyan] {min(c_ratios):.4f} to {max(c_ratios):.4f}")
    console.print(f"[cyan]max_dev/Δ:[/cyan] {min(max_devs):.4f} to {max(max_devs):.4f}")

    # Key check: is c_twins ≥ c_lattice * (1 - ε)?
    min_ratio = min(c_ratios)

    console.print("\n" + "="*60)

    if min_ratio > 0.5:
        console.print(Panel.fit(
            f"[bold green]✓ PERTURBATION РАБОТАЕТ![/bold green]\n\n"
            f"• c_twins / c_lattice ≥ {min_ratio:.4f}\n"
            f"• Twins наследуют B₁ от решётки!\n"
            f"• c₁^prime ≥ {min_ratio:.2f} · c₁^lat\n\n"
            f"[dim]Это значит:[/dim]\n"
            f"  Model B₁(lattice) ⟹ B₁(prime) × {min_ratio:.2f}",
            box=box.DOUBLE,
            border_style="green"
        ))
    elif min_ratio > 0.1:
        console.print(Panel.fit(
            f"[bold yellow]⚠️ ЧАСТИЧНЫЙ УСПЕХ[/bold yellow]\n\n"
            f"• c_twins / c_lattice ≥ {min_ratio:.4f}\n"
            f"• Есть потеря, но c > 0 сохраняется",
            box=box.DOUBLE,
            border_style="yellow"
        ))
    else:
        console.print(Panel.fit(
            f"[bold red]✗ ПРОБЛЕМА[/bold red]\n\n"
            f"• c_twins / c_lattice = {min_ratio:.4f}\n"
            f"• Слишком большая потеря!",
            box=box.DOUBLE,
            border_style="red"
        ))

    # Check stability of c_twins
    console.print("\n[yellow]Стабильность c_twins при X → ∞:[/yellow]")
    for r in results[-4:]:
        console.print(f"  X={r['X']:5d}: c_twins = {r['c_twins']:.4f}")

    # Check if c_twins stabilizes
    last_4 = [r['c_twins'] for r in results[-4:]]
    variance = np.var(last_4)
    mean_c = np.mean(last_4)

    console.print(f"\n  Mean c_twins (last 4): {mean_c:.4f}")
    console.print(f"  Variance: {variance:.6f}")

    if variance < 0.01:
        console.print(f"  [green]✓ c_twins стабильна![/green]")
    else:
        console.print(f"  [yellow]⚠️ c_twins ещё не стабилизировалась[/yellow]")

    return results


if __name__ == "__main__":
    main()
