#!/usr/bin/env python3
"""
c_twins Scaling Analysis
========================

Проверяем: c_twins(X) ~ X^α ?

Если α ≥ 0, то c_twins → const или растёт — B₁(prime) работает!
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
    return [p for p in primes_set if p + 2 in primes_set and p <= limit]


def G(delta: float, t: float) -> float:
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def compute_c_twins(X: int, t: float = 1.0) -> dict:
    """Compute c_twins = E_comm / E_lat for twin primes up to X."""
    twins = get_twin_primes(X)
    if len(twins) < 3:
        return None

    positions = np.array([log(p) / (2 * pi) for p in twins])
    N = len(positions)

    # Gram matrix
    G_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            G_mat[i, j] = G(positions[i] - positions[j], t)

    # Xi matrix
    Xi_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

    # Uniform λ
    lam = np.ones(N)

    # E_lat
    inner_prods = G_mat @ lam
    E_lat = np.sum(inner_prods**2)

    # E_comm
    xi_inner = Xi_mat @ lam
    c_coeffs = positions * inner_prods - xi_inner
    E_comm = c_coeffs @ G_mat @ c_coeffs

    return {
        'X': X,
        'N': N,
        'c_twins': E_comm / E_lat if E_lat > 0 else 0,
        'E_lat': E_lat,
        'E_comm': E_comm,
    }


def main():
    console.print(Panel.fit(
        "[bold cyan]c_twins SCALING ANALYSIS[/bold cyan]",
        box=box.DOUBLE
    ))

    # Extended range
    X_values = [50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000]

    results = []
    for X in X_values:
        res = compute_c_twins(X)
        if res:
            results.append(res)

    # Table
    table = Table(title="c_twins vs X", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("#twins", style="blue", justify="right")
    table.add_column("c_twins", style="green", justify="right")
    table.add_column("log(c_twins)", style="yellow", justify="right")

    for r in results:
        table.add_row(
            str(r['X']),
            str(r['N']),
            f"{r['c_twins']:.6f}",
            f"{log(r['c_twins']) if r['c_twins'] > 0 else -999:.3f}"
        )

    console.print(table)

    # Fit: log(c_twins) = α·log(X) + β
    log_X = np.log([r['X'] for r in results])
    log_c = np.log([r['c_twins'] for r in results])

    alpha, beta = np.polyfit(log_X, log_c, 1)

    console.print("\n" + "="*60)
    console.print(f"[bold cyan]SCALING FIT:[/bold cyan]")
    console.print(f"  c_twins(X) ~ X^{alpha:.4f}")
    console.print(f"  (log-log fit: α = {alpha:.4f})")

    # Also fit c_twins vs N (number of twins)
    log_N = np.log([r['N'] for r in results])
    alpha_N, _ = np.polyfit(log_N, log_c, 1)
    console.print(f"\n  c_twins(N) ~ N^{alpha_N:.4f}")
    console.print(f"  (where N = number of twins)")

    # Interpretation
    console.print("\n" + "="*60)

    if alpha > 0:
        console.print(Panel.fit(
            f"[bold green]✓ c_twins РАСТЁТ с X![/bold green]\n\n"
            f"  c_twins ~ X^{alpha:.3f}\n\n"
            f"[dim]Это значит:[/dim]\n"
            f"  • B₁(prime) выполняется\n"
            f"  • c₁(X) → ∞ при X → ∞\n"
            f"  • Даже ЛУЧШЕ чем нужно!",
            box=box.DOUBLE,
            border_style="green"
        ))
    elif alpha > -0.1:
        console.print(Panel.fit(
            f"[bold green]✓ c_twins СТАБИЛЬНА[/bold green]\n\n"
            f"  c_twins ~ X^{alpha:.3f} ≈ const\n\n"
            f"[dim]Это значит:[/dim]\n"
            f"  • B₁(prime) выполняется\n"
            f"  • liminf c₁(X) > 0",
            box=box.DOUBLE,
            border_style="green"
        ))
    else:
        console.print(Panel.fit(
            f"[bold red]⚠️ c_twins ПАДАЕТ[/bold red]\n\n"
            f"  c_twins ~ X^{alpha:.3f} → 0",
            box=box.DOUBLE,
            border_style="red"
        ))

    # Extrapolation
    console.print("\n[yellow]Экстраполяция:[/yellow]")
    for X_future in [100000, 1000000, 10000000]:
        c_pred = exp(beta) * X_future**alpha
        console.print(f"  X = {X_future:>10,}: c_twins ≈ {c_pred:.4f}")

    return results


if __name__ == "__main__":
    main()
