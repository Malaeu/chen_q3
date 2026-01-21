#!/usr/bin/env python3
"""
Kernel Analysis: Исследование ker(M) для twin-матрицы
=====================================================

КРИТИЧЕСКИЙ ВОПРОС:
  Можно ли доказать ker(M) = {0} из арифметических свойств twins?

МАТРИЦА:
  M_pq = (ξ_q - ξ_p) · G²(ξ_p - ξ_q)

  где ξ_p = log(p)/(2π), G(δ) = √(2πt)·exp(-δ²/(8t))

ЭКСПЕРИМЕНТЫ:
  1. min eigenvalue M при разных X
  2. Сравнение: twins vs uniform grid vs random
  3. Scaling: λ_min(M) ~ X^?
  4. Анализ структуры ядра (если найдётся)
"""

import numpy as np
from math import log, pi, sqrt, exp
from scipy.linalg import eigh
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
    """Gaussian kernel."""
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def build_M_matrix(positions: np.ndarray, t: float) -> np.ndarray:
    """
    Build M_pq = (ξ_q - ξ_p) · G²(ξ_p - ξ_q)

    Note: M is antisymmetric in (ξ_q - ξ_p) but G² is symmetric,
    so M is antisymmetric overall!
    """
    N = len(positions)
    M = np.zeros((N, N))

    for i in range(N):
        for j in range(N):
            delta = positions[j] - positions[i]
            G_val = G(delta, t)
            M[i, j] = delta * G_val**2

    return M


def build_E_comm_matrix(positions: np.ndarray, t: float) -> np.ndarray:
    """
    Build the actual E_comm quadratic form matrix.

    E_comm(λ) = λᵀ Q λ  where Q is the proper commutator Gram matrix.

    From commutator_exact_formula.py:
    A_pq = (ξ_q - ξ_p)/2 · (G²)_pq

    E_comm = cᵀ G c  where c = ξ⊙(Gλ) - Ξλ

    Expanding: Q = (diag(ξ)G - Ξ)ᵀ G (diag(ξ)G - Ξ)
    """
    N = len(positions)

    # Build G matrix
    G_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = positions[i] - positions[j]
            G_mat[i, j] = G(delta, t)

    # Build Ξ matrix: Ξ_ij = (ξ_i + ξ_j)/2 · G_ij
    Xi_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

    # Q = (diag(ξ)G - Ξ)ᵀ G (diag(ξ)G - Ξ)
    xi_diag = np.diag(positions)
    B = xi_diag @ G_mat - Xi_mat  # B_ij = ξ_i·G_ij - (ξ_i+ξ_j)/2·G_ij = (ξ_i-ξ_j)/2·G_ij

    Q = B.T @ G_mat @ B

    return Q


def analyze_matrix(positions: np.ndarray, t: float, name: str) -> dict:
    """Analyze M matrix for given positions."""
    M = build_M_matrix(positions, t)
    Q = build_E_comm_matrix(positions, t)

    # M eigenvalues (antisymmetric → imaginary eigenvalues)
    M_eigvals = np.linalg.eigvals(M)
    M_eigvals_imag = np.sort(np.abs(M_eigvals.imag))

    # Q eigenvalues (symmetric, positive semidefinite)
    Q_eigvals = np.linalg.eigvalsh(Q)
    Q_eigvals = np.sort(Q_eigvals)

    # Check symmetry of Q
    Q_sym_error = np.max(np.abs(Q - Q.T))

    # Min positive eigenvalue (for kernel analysis)
    pos_eigvals = Q_eigvals[Q_eigvals > 1e-10]
    min_pos_eigval = pos_eigvals[0] if len(pos_eigvals) > 0 else 0

    # Number of "zero" eigenvalues (kernel dimension)
    kernel_dim = np.sum(Q_eigvals < 1e-10)

    # Condition number
    if min_pos_eigval > 0:
        cond_number = Q_eigvals[-1] / min_pos_eigval
    else:
        cond_number = float('inf')

    return {
        'name': name,
        'N': len(positions),
        'min_eigval': Q_eigvals[0],
        'min_pos_eigval': min_pos_eigval,
        'max_eigval': Q_eigvals[-1],
        'kernel_dim': kernel_dim,
        'cond_number': cond_number,
        'Q_sym_error': Q_sym_error,
        'M_min_imag': M_eigvals_imag[0] if len(M_eigvals_imag) > 0 else 0,
    }


def generate_positions(N: int, mode: str, X: int = None) -> np.ndarray:
    """Generate positions for different point sets."""
    if mode == 'twins':
        twins = get_twin_primes(X)[:N]
        return np.array([log(p) / (2 * pi) for p in twins])
    elif mode == 'uniform':
        # Uniform grid matching twin range
        twins = get_twin_primes(X)[:N]
        xi_min = log(twins[0]) / (2 * pi)
        xi_max = log(twins[-1]) / (2 * pi)
        return np.linspace(xi_min, xi_max, N)
    elif mode == 'random':
        twins = get_twin_primes(X)[:N]
        xi_min = log(twins[0]) / (2 * pi)
        xi_max = log(twins[-1]) / (2 * pi)
        np.random.seed(42)
        return np.sort(np.random.uniform(xi_min, xi_max, N))
    else:
        raise ValueError(f"Unknown mode: {mode}")


def main():
    console.print(Panel.fit(
        "[bold cyan]KERNEL ANALYSIS[/bold cyan]\n"
        "[dim]Исследование ker(M) для twin-матрицы[/dim]",
        box=box.DOUBLE
    ))

    t = 1.0
    X_values = [500, 1000, 2000, 5000, 10000]

    results_twins = []
    results_uniform = []
    results_random = []

    for X in X_values:
        twins = get_twin_primes(X)
        N = len(twins)

        if N < 5:
            continue

        console.print(f"\n[yellow]X = {X}, N = {N}[/yellow]")

        # Twin positions
        pos_twins = generate_positions(N, 'twins', X)
        res_twins = analyze_matrix(pos_twins, t, f'twins_{X}')
        results_twins.append(res_twins)

        # Uniform grid
        pos_uniform = generate_positions(N, 'uniform', X)
        res_uniform = analyze_matrix(pos_uniform, t, f'uniform_{X}')
        results_uniform.append(res_uniform)

        # Random positions
        pos_random = generate_positions(N, 'random', X)
        res_random = analyze_matrix(pos_random, t, f'random_{X}')
        results_random.append(res_random)

        console.print(f"  [dim]twins:   λ_min = {res_twins['min_eigval']:.2e}, ker_dim = {res_twins['kernel_dim']}[/dim]")
        console.print(f"  [dim]uniform: λ_min = {res_uniform['min_eigval']:.2e}, ker_dim = {res_uniform['kernel_dim']}[/dim]")
        console.print(f"  [dim]random:  λ_min = {res_random['min_eigval']:.2e}, ker_dim = {res_random['kernel_dim']}[/dim]")

    # Summary table
    console.print("\n")
    table = Table(title="Kernel Analysis: λ_min(Q) for E_comm", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("N", style="blue", justify="right")
    table.add_column("λ_min (twins)", style="green", justify="right")
    table.add_column("λ_min (uniform)", style="yellow", justify="right")
    table.add_column("λ_min (random)", style="magenta", justify="right")
    table.add_column("ker_dim", style="red", justify="center")

    for rt, ru, rr in zip(results_twins, results_uniform, results_random):
        table.add_row(
            rt['name'].split('_')[1],
            str(rt['N']),
            f"{rt['min_eigval']:.2e}",
            f"{ru['min_eigval']:.2e}",
            f"{rr['min_eigval']:.2e}",
            str(rt['kernel_dim'])
        )

    console.print(table)

    # Scaling analysis
    if len(results_twins) >= 3:
        console.print("\n[bold cyan]SCALING ANALYSIS:[/bold cyan]\n")

        # For twins
        N_vals = np.array([r['N'] for r in results_twins])
        min_eigvals = np.array([r['min_eigval'] for r in results_twins])

        # Filter positive eigenvalues
        mask = min_eigvals > 1e-15
        if np.sum(mask) >= 3:
            log_N = np.log(N_vals[mask])
            log_eigval = np.log(min_eigvals[mask])

            alpha, _ = np.polyfit(log_N, log_eigval, 1)

            console.print(f"  [cyan]Twins: λ_min ~ N^{{{alpha:.3f}}}[/cyan]")

        # For uniform
        min_eigvals_u = np.array([r['min_eigval'] for r in results_uniform])
        mask_u = min_eigvals_u > 1e-15
        if np.sum(mask_u) >= 3:
            log_eigval_u = np.log(min_eigvals_u[mask_u])
            alpha_u, _ = np.polyfit(log_N[mask_u], log_eigval_u, 1)
            console.print(f"  [yellow]Uniform: λ_min ~ N^{{{alpha_u:.3f}}}[/yellow]")

        # For random
        min_eigvals_r = np.array([r['min_eigval'] for r in results_random])
        mask_r = min_eigvals_r > 1e-15
        if np.sum(mask_r) >= 3:
            log_eigval_r = np.log(min_eigvals_r[mask_r])
            alpha_r, _ = np.polyfit(log_N[mask_r], log_eigval_r, 1)
            console.print(f"  [magenta]Random: λ_min ~ N^{{{alpha_r:.3f}}}[/magenta]")

    # Conclusion
    console.print("\n" + "="*60)

    all_kernel_zero = all(r['kernel_dim'] == 0 for r in results_twins)
    all_min_pos = all(r['min_eigval'] > 0 for r in results_twins)

    if all_kernel_zero and all_min_pos:
        console.print(Panel.fit(
            "[bold green]✓ ker(Q) = {0} ДЛЯ ВСЕХ X![/bold green]\n\n"
            "Нет нетривиального ядра.\n"
            "min λ(Q) > 0 для всех проверенных X.\n\n"
            "[yellow]⟹ Irregular Gaps Hypothesis ПОДТВЕРЖДЕНА численно![/yellow]",
            box=box.DOUBLE,
            border_style="green"
        ))
    else:
        console.print(Panel.fit(
            "[bold red]⚠ Найдено нетривиальное ядро![/bold red]\n\n"
            f"ker_dim > 0 для некоторых X.\n"
            "Требуется дополнительный анализ.",
            box=box.DOUBLE,
            border_style="red"
        ))

    return results_twins, results_uniform, results_random


if __name__ == "__main__":
    main()
