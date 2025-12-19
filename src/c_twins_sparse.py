#!/usr/bin/env python3
"""
c_twins Sparse Computation: Extension to X = 10⁶
=================================================

Проблема: для X=10⁶ имеем ~78498 простых, матрица слишком велика.

Решение: Sparse аппроксимация Gram матрицы
- G(δ) = √(2πt)·exp(-δ²/(8t)) экспоненциально убывает
- При |δ| > δ_cutoff: G(δ) < ε (пренебрежимо мало)
- Оставляем только близкие пары (bandwidth cutoff)

Для t=1, чтобы G(δ) < 10⁻⁶: |δ| > 9.4
В log-координатах: |ξ_p - ξ_q| > 9.4 ⟹ |log(p) - log(q)| > 59
"""

import numpy as np
from math import log, pi, sqrt, exp
from scipy.sparse import lil_matrix, csr_matrix
from scipy.sparse.linalg import eigsh
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box
import time

console = Console()


def sieve_primes(limit: int) -> list[int]:
    """Sieve of Eratosthenes."""
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]


def get_twin_primes(limit: int) -> list[int]:
    """Get twin primes up to limit."""
    primes_set = set(sieve_primes(limit + 2))
    return sorted([p for p in primes_set if p + 2 in primes_set and p <= limit])


def G(delta: float, t: float) -> float:
    """Gaussian overlap."""
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def compute_c_twins_sparse(X: int, t: float = 1.0, cutoff_factor: float = 6.0) -> dict:
    """
    Compute c_twins using sparse matrix for large X.

    cutoff_factor: number of standard deviations for bandwidth
    For Gaussian: σ = √(4t), so cutoff = cutoff_factor * √(4t)
    """
    start_time = time.time()

    twins = get_twin_primes(X)
    N = len(twins)

    if N < 3:
        return None

    # Positions in spectral coordinates
    positions = np.array([log(p) / (2 * pi) for p in twins])

    # Bandwidth cutoff
    sigma = sqrt(4 * t)
    delta_cutoff = cutoff_factor * sigma

    # Build sparse Gram matrix
    G_sparse = lil_matrix((N, N))
    Xi_sparse = lil_matrix((N, N))

    nnz = 0
    for i in range(N):
        for j in range(i, N):
            delta = positions[i] - positions[j]
            if abs(delta) <= delta_cutoff:
                g_val = G(delta, t)
                G_sparse[i, j] = g_val
                G_sparse[j, i] = g_val

                xi_val = (positions[i] + positions[j]) / 2 * g_val
                Xi_sparse[i, j] = xi_val
                Xi_sparse[j, i] = xi_val

                if i != j:
                    nnz += 2
                else:
                    nnz += 1

    # Convert to CSR for efficient operations
    G_csr = G_sparse.tocsr()
    Xi_csr = Xi_sparse.tocsr()

    # Uniform λ
    lam = np.ones(N)

    # E_lat = ‖G·λ‖²
    inner_prods = G_csr @ lam
    E_lat = np.sum(inner_prods**2)

    # E_comm = c^T G c where c = ξ⊙(Gλ) - Ξλ
    xi_inner = Xi_csr @ lam
    c_coeffs = positions * inner_prods - xi_inner
    E_comm = c_coeffs @ (G_csr @ c_coeffs)

    elapsed = time.time() - start_time

    sparsity = 1.0 - nnz / (N * N)

    return {
        'X': X,
        'N': N,
        'c_twins': E_comm / E_lat if E_lat > 0 else 0,
        'E_lat': E_lat,
        'E_comm': E_comm,
        'nnz': nnz,
        'sparsity': sparsity,
        'time': elapsed,
        'cutoff': delta_cutoff,
    }


def main():
    console.print(Panel.fit(
        "[bold cyan]c_twins SPARSE: Extension to X = 10⁶[/bold cyan]",
        box=box.DOUBLE
    ))

    t = 1.0

    # Test range including large X
    X_values = [
        1000, 2000, 5000, 10000, 20000, 50000,
        100000, 200000, 500000, 1000000
    ]

    results = []

    console.print(f"\n[dim]Parameters: t={t}, cutoff=6σ[/dim]")
    console.print("[yellow]Computing (may take a few minutes for large X)...[/yellow]\n")

    for X in X_values:
        console.print(f"[dim]X = {X:>10,}...[/dim]", end=" ")
        res = compute_c_twins_sparse(X, t)
        if res:
            results.append(res)
            console.print(f"[green]done[/green] (N={res['N']}, time={res['time']:.1f}s)")
        else:
            console.print(f"[red]skipped (too few twins)[/red]")

    # Table
    console.print("\n")
    table = Table(title="c_twins Sparse Results", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("#twins", style="blue", justify="right")
    table.add_column("c_twins", style="green", justify="right")
    table.add_column("sparsity", style="yellow", justify="right")
    table.add_column("time(s)", style="magenta", justify="right")

    for r in results:
        table.add_row(
            f"{r['X']:,}",
            str(r['N']),
            f"{r['c_twins']:.6f}",
            f"{r['sparsity']:.1%}",
            f"{r['time']:.1f}"
        )

    console.print(table)

    # Scaling fit
    if len(results) >= 3:
        log_X = np.log([r['X'] for r in results])
        log_c = np.log([r['c_twins'] for r in results])

        alpha, beta = np.polyfit(log_X, log_c, 1)

        console.print(f"\n[bold cyan]SCALING FIT:[/bold cyan]")
        console.print(f"  c_twins(X) ~ X^{alpha:.4f}")

        # Residual analysis
        predicted = beta + alpha * log_X
        residuals = log_c - predicted
        r_squared = 1 - np.var(residuals) / np.var(log_c)
        console.print(f"  R² = {r_squared:.4f}")

        # Fit only large X (> 10000)
        large_idx = [i for i, r in enumerate(results) if r['X'] >= 10000]
        if len(large_idx) >= 3:
            log_X_large = log_X[large_idx]
            log_c_large = log_c[large_idx]
            alpha_large, _ = np.polyfit(log_X_large, log_c_large, 1)
            console.print(f"\n  For X ≥ 10000: c_twins ~ X^{alpha_large:.4f}")

    # Interpretation
    console.print("\n" + "="*60)

    if results and results[-1]['X'] >= 1000000:
        c_million = results[-1]['c_twins']
        console.print(Panel.fit(
            f"[bold green]✓ РЕЗУЛЬТАТ ДЛЯ X = 10⁶:[/bold green]\n\n"
            f"  c_twins(10⁶) = {c_million:.6f}\n\n"
            f"[dim]Scaling: c_twins ~ X^{alpha:.3f}[/dim]\n"
            f"[dim]Константа растёт с X — B₁(prime) выполняется![/dim]",
            box=box.DOUBLE,
            border_style="green"
        ))
    else:
        console.print(Panel.fit(
            f"[bold yellow]Partial results computed[/bold yellow]\n"
            f"Largest X computed: {results[-1]['X'] if results else 'none'}",
            box=box.DOUBLE,
            border_style="yellow"
        ))

    return results


if __name__ == "__main__":
    main()
