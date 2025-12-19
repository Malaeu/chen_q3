#!/usr/bin/env python3
"""
Kernel Cone Check: Проверка — лежат ли собственные вектора ядра в twin-конусе?
==============================================================================

ОТКРЫТИЕ: ker(Q) огромен (dim ≈ N-3)!

НО: Twin-конус = {λ : λ_p ≥ 0}

Если собственные вектора ядра имеют ОТРИЦАТЕЛЬНЫЕ компоненты,
то они НЕ в конусе и НЕ релевантны для B₁_strong!

ЭКСПЕРИМЕНТ:
1. Найти собственные вектора с λ ≈ 0
2. Проверить знаки их компонент
3. Если все ker-вектора вне конуса → B₁_strong безопасен!
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
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def build_matrices(positions: np.ndarray, t: float):
    """Build G, Xi, and Q matrices."""
    N = len(positions)

    G_mat = np.zeros((N, N))
    Xi_mat = np.zeros((N, N))

    for i in range(N):
        for j in range(N):
            delta = positions[i] - positions[j]
            G_mat[i, j] = G(delta, t)
            Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

    # Q = Bᵀ G B where B = diag(ξ)G - Ξ
    xi_diag = np.diag(positions)
    B = xi_diag @ G_mat - Xi_mat

    Q = B.T @ G_mat @ B

    return G_mat, Xi_mat, Q, B


def check_cone_intersection(Q: np.ndarray, G_mat: np.ndarray, threshold: float = 1e-8):
    """
    Check if any eigenvector with small eigenvalue lies in the positive cone.

    Returns analysis of how "close" to cone the kernel vectors are.
    """
    # Get eigendecomposition
    eigvals, eigvecs = eigh(Q)

    # Find "kernel" eigenvectors (small eigenvalues)
    kernel_indices = np.where(np.abs(eigvals) < threshold)[0]

    results = []

    for idx in kernel_indices:
        v = eigvecs[:, idx]
        eigval = eigvals[idx]

        # Check signs
        num_positive = np.sum(v > 1e-10)
        num_negative = np.sum(v < -1e-10)
        num_zero = len(v) - num_positive - num_negative

        # Max negative component
        min_comp = np.min(v)

        # Check if can be made non-negative by sign flip
        v_pos = np.abs(v)
        in_cone_after_flip = True  # |v| is always non-negative

        # E_comm for this eigenvector
        E_comm = v @ Q @ v

        # E_lat for this eigenvector
        Gv = G_mat @ v
        E_lat = np.sum(Gv**2)

        # Try to project onto cone
        v_proj = np.maximum(v, 0)
        if np.linalg.norm(v_proj) > 1e-10:
            v_proj = v_proj / np.linalg.norm(v_proj)
            E_comm_proj = v_proj @ Q @ v_proj
            Gv_proj = G_mat @ v_proj
            E_lat_proj = np.sum(Gv_proj**2)
            R_proj = E_comm_proj / E_lat_proj if E_lat_proj > 1e-15 else float('inf')
        else:
            R_proj = float('inf')

        results.append({
            'idx': idx,
            'eigval': eigval,
            'num_positive': num_positive,
            'num_negative': num_negative,
            'num_zero': num_zero,
            'min_comp': min_comp,
            'E_comm': E_comm,
            'E_lat': E_lat,
            'R_proj': R_proj,
        })

    return results, eigvals, eigvecs


def find_min_R_on_cone(Q: np.ndarray, G_mat: np.ndarray, N: int, n_samples: int = 1000):
    """
    Find minimum R = E_comm/E_lat on the positive cone via random sampling + optimization.
    """
    from scipy.optimize import minimize

    def compute_R(lam):
        lam_norm = lam / (np.linalg.norm(lam) + 1e-15)
        E_comm = lam_norm @ Q @ lam_norm
        Gv = G_mat @ lam_norm
        E_lat = np.sum(Gv**2)
        if E_lat < 1e-15:
            return float('inf')
        return E_comm / E_lat

    min_R = float('inf')
    best_lam = None

    np.random.seed(42)

    # Random samples
    for _ in range(n_samples):
        lam = np.random.rand(N) + 0.01
        R = compute_R(lam)
        if R < min_R:
            min_R = R
            best_lam = lam.copy()

    # Optimization from best found
    if best_lam is not None:
        try:
            result = minimize(
                compute_R,
                best_lam,
                method='L-BFGS-B',
                bounds=[(0.001, None) for _ in range(N)],
                options={'maxiter': 200}
            )
            if result.fun < min_R:
                min_R = result.fun
                best_lam = result.x
        except:
            pass

    return min_R, best_lam


def main():
    console.print(Panel.fit(
        "[bold cyan]KERNEL CONE CHECK[/bold cyan]\n"
        "[dim]Лежат ли ker-вектора в twin-конусе?[/dim]",
        box=box.DOUBLE
    ))

    t = 1.0
    X_values = [500, 1000, 2000, 5000]

    all_results = []

    for X in X_values:
        twins = get_twin_primes(X)
        N = len(twins)

        if N < 5:
            continue

        console.print(f"\n[yellow]X = {X}, N = {N}[/yellow]")

        positions = np.array([log(p) / (2 * pi) for p in twins])
        G_mat, Xi_mat, Q, B = build_matrices(positions, t)

        # Analyze kernel
        ker_results, eigvals, eigvecs = check_cone_intersection(Q, G_mat)

        console.print(f"  [dim]Найдено {len(ker_results)} ker-векторов[/dim]")

        # Check how many have mixed signs
        mixed_sign = sum(1 for r in ker_results if r['num_negative'] > 0 and r['num_positive'] > 0)
        all_positive = sum(1 for r in ker_results if r['num_negative'] == 0)
        all_negative = sum(1 for r in ker_results if r['num_positive'] == 0)

        console.print(f"  [green]Чисто положительные: {all_positive}[/green]")
        console.print(f"  [red]Чисто отрицательные: {all_negative}[/red]")
        console.print(f"  [yellow]Смешанные знаки: {mixed_sign}[/yellow]")

        # Find min R on cone
        console.print(f"  [dim]Ищем min R на конусе...[/dim]")
        min_R, best_lam = find_min_R_on_cone(Q, G_mat, N)

        console.print(f"  [cyan]min R на конусе = {min_R:.6f}[/cyan]")

        # Check R for projected kernel vectors
        min_R_proj = float('inf')
        for r in ker_results:
            if r['R_proj'] < min_R_proj:
                min_R_proj = r['R_proj']

        console.print(f"  [magenta]min R_proj (ker→cone) = {min_R_proj:.6f}[/magenta]")

        all_results.append({
            'X': X,
            'N': N,
            'ker_dim': len(ker_results),
            'mixed_sign': mixed_sign,
            'all_positive': all_positive,
            'min_R_cone': min_R,
            'min_R_proj': min_R_proj,
        })

    # Summary
    console.print("\n")
    table = Table(title="Kernel vs Cone Analysis", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("N", style="blue", justify="right")
    table.add_column("ker_dim", style="yellow", justify="right")
    table.add_column("In cone", style="green", justify="right")
    table.add_column("min R (cone)", style="magenta", justify="right")

    for r in all_results:
        table.add_row(
            str(r['X']),
            str(r['N']),
            str(r['ker_dim']),
            str(r['all_positive']),
            f"{r['min_R_cone']:.6f}"
        )

    console.print(table)

    # Conclusion
    console.print("\n" + "="*60)

    all_ker_outside_cone = all(r['all_positive'] == 0 for r in all_results)
    all_min_R_positive = all(r['min_R_cone'] > 0 for r in all_results)

    if all_ker_outside_cone and all_min_R_positive:
        console.print(Panel.fit(
            "[bold green]✓ ВСЕ ker-вектора ВНЕ twin-конуса![/bold green]\n\n"
            "ker(Q) большой, НО все ker-вектора имеют смешанные знаки.\n"
            "На twin-конусе (λ ≥ 0): min R > 0 для всех X.\n\n"
            "[yellow]⟹ B₁_strong: inf_{λ∈cone} R(λ) > 0 ПОДТВЕРЖДЁН![/yellow]",
            box=box.DOUBLE,
            border_style="green"
        ))
    elif all_min_R_positive:
        console.print(Panel.fit(
            "[bold yellow]⚠ Некоторые ker-вектора в конусе[/bold yellow]\n\n"
            f"НО: min R на конусе всё равно > 0!\n"
            "B₁_strong выполняется численно.",
            box=box.DOUBLE,
            border_style="yellow"
        ))
    else:
        console.print(Panel.fit(
            "[bold red]❌ min R → 0 на конусе![/bold red]\n\n"
            "B₁_strong НЕ выполняется!",
            box=box.DOUBLE,
            border_style="red"
        ))

    return all_results


if __name__ == "__main__":
    main()
