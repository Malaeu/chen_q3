#!/usr/bin/env python3
"""
Rayleigh Minimum Scan: поиск минимума c₁(X) по разным λ
========================================================

КРИТИКА СОВЕТНИКА:
  "Geometric B₁" в формулировке "∃ Aₚq≠0 ⟹ E_comm(λ)>0" — НЕВЕРНА!
  λ может лежать в ker(A).

  Нужно проверить: насколько МАЛЕНЬКИМ может быть
  R(λ) = E_comm(λ) / E_lat(λ) для разных λ?

ЭКСПЕРИМЕНТ:
  1. Uniform: λ = (1, 1, ..., 1)
  2. Von Mangoldt: λ_p = Λ(p)/√p
  3. Random positive
  4. Concentrated (на кучке twins)
  5. Попытка минимизации — gradient descent на λ

Если min_λ R(λ) → 0 при X → ∞, то B₁_weak нарушается!
"""

import numpy as np
from math import log, pi, sqrt, exp
from scipy.optimize import minimize
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


def compute_ratio(lam: np.ndarray, G_mat: np.ndarray, Xi_mat: np.ndarray,
                  positions: np.ndarray) -> float:
    """
    Compute R(λ) = E_comm(λ) / E_lat(λ)

    E_lat = ‖Gλ‖²
    E_comm = c^T G c  where c = ξ⊙(Gλ) - Ξλ
    """
    # Normalize λ to avoid trivial zero
    lam_norm = lam / (np.linalg.norm(lam) + 1e-15)

    Glam = G_mat @ lam_norm
    E_lat = np.sum(Glam**2)

    if E_lat < 1e-15:
        return float('inf')

    Xi_lam = Xi_mat @ lam_norm
    c = positions * Glam - Xi_lam
    E_comm = c @ G_mat @ c

    return E_comm / E_lat


def build_matrices(twins: list[int], t: float):
    """Build G and Ξ matrices."""
    N = len(twins)
    positions = np.array([log(p) / (2 * pi) for p in twins])

    G_mat = np.zeros((N, N))
    Xi_mat = np.zeros((N, N))

    for i in range(N):
        for j in range(N):
            delta = positions[i] - positions[j]
            G_mat[i, j] = G(delta, t)
            Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

    return G_mat, Xi_mat, positions


def generate_lambda_vectors(N: int, twins: list[int], num_random: int = 5):
    """Generate different λ vectors to test."""
    vectors = {}

    # 1. Uniform
    vectors['uniform'] = np.ones(N)

    # 2. Von Mangoldt: Λ(p)/√p = log(p)/√p
    vectors['von_mangoldt'] = np.array([log(p) / sqrt(p) for p in twins])

    # 3. Λ(p)·Λ(p+2) = log(p)·log(p+2) (standard twin weight)
    vectors['twin_weight'] = np.array([log(p) * log(p + 2) for p in twins])

    # 4. Concentrated on first few
    concentrated = np.zeros(N)
    concentrated[:min(5, N)] = 1.0
    vectors['concentrated_start'] = concentrated

    # 5. Concentrated on middle
    mid = N // 2
    concentrated_mid = np.zeros(N)
    concentrated_mid[max(0, mid-2):min(N, mid+3)] = 1.0
    vectors['concentrated_mid'] = concentrated_mid

    # 6. Alternating signs (but keep positive for cone)
    vectors['alternating'] = np.array([1.0 if i % 2 == 0 else 0.5 for i in range(N)])

    # 7. Random positive
    np.random.seed(42)
    for i in range(num_random):
        vectors[f'random_{i}'] = np.abs(np.random.randn(N)) + 0.1

    return vectors


def find_minimum_ratio(G_mat: np.ndarray, Xi_mat: np.ndarray,
                       positions: np.ndarray, N: int) -> tuple:
    """
    Try to find λ that minimizes R(λ) = E_comm/E_lat

    Uses gradient descent from multiple starting points.
    Constrained to λ ≥ 0 (cone constraint).
    """

    def objective(lam):
        return compute_ratio(lam, G_mat, Xi_mat, positions)

    best_ratio = float('inf')
    best_lam = None

    # Try from different starting points
    np.random.seed(123)

    starting_points = [
        np.ones(N),  # uniform
        np.random.rand(N) + 0.1,
        np.linspace(0.1, 1, N),
        np.exp(-np.arange(N) / N),
    ]

    for i in range(5):
        starting_points.append(np.random.rand(N) + 0.01)

    for start in starting_points:
        try:
            # L-BFGS-B with bounds λ ≥ 0
            result = minimize(
                objective,
                start,
                method='L-BFGS-B',
                bounds=[(0.01, None) for _ in range(N)],  # λ > 0
                options={'maxiter': 100}
            )

            if result.fun < best_ratio:
                best_ratio = result.fun
                best_lam = result.x
        except:
            pass

    return best_ratio, best_lam


def main():
    console.print(Panel.fit(
        "[bold cyan]RAYLEIGH MINIMUM SCAN[/bold cyan]\n"
        "[dim]Проверка: может ли min R(λ) → 0?[/dim]",
        box=box.DOUBLE
    ))

    t = 1.0
    X_values = [100, 500, 1000, 2000, 5000, 10000]

    results = []

    for X in X_values:
        console.print(f"\n[yellow]X = {X}[/yellow]")

        twins = get_twin_primes(X)
        N = len(twins)

        if N < 5:
            console.print("[red]Too few twins, skipping[/red]")
            continue

        G_mat, Xi_mat, positions = build_matrices(twins, t)
        lambdas = generate_lambda_vectors(N, twins)

        # Compute ratios for all λ
        ratios = {}
        for name, lam in lambdas.items():
            ratios[name] = compute_ratio(lam, G_mat, Xi_mat, positions)

        # Find minimum via optimization
        console.print(f"[dim]  Optimizing for minimum...[/dim]")
        min_ratio_opt, _ = find_minimum_ratio(G_mat, Xi_mat, positions, N)

        # Collect results
        result = {
            'X': X,
            'N': N,
            'ratios': ratios,
            'min_opt': min_ratio_opt,
            'min_tested': min(ratios.values()),
            'max_tested': max(ratios.values()),
        }
        results.append(result)

        # Print summary for this X
        table = Table(title=f"R(λ) = E_comm/E_lat for X={X} (N={N})", box=box.SIMPLE)
        table.add_column("λ type", style="cyan")
        table.add_column("R(λ)", style="green", justify="right")

        sorted_ratios = sorted(ratios.items(), key=lambda x: x[1])
        for name, ratio in sorted_ratios[:8]:  # top 8 smallest
            table.add_row(name, f"{ratio:.6f}")

        table.add_row("---", "---")
        table.add_row("[bold]MIN (optimized)[/bold]", f"[bold]{min_ratio_opt:.6f}[/bold]")

        console.print(table)

    # Final analysis
    console.print("\n" + "="*60)
    console.print("\n[bold yellow]SCALING OF MINIMUM R(λ)[/bold yellow]\n")

    table = Table(title="Minimum Rayleigh Ratio vs X", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("N", style="blue", justify="right")
    table.add_column("min R (tested)", style="green", justify="right")
    table.add_column("min R (optimized)", style="yellow", justify="right")
    table.add_column("max R", style="magenta", justify="right")

    for r in results:
        table.add_row(
            str(r['X']),
            str(r['N']),
            f"{r['min_tested']:.6f}",
            f"{r['min_opt']:.6f}",
            f"{r['max_tested']:.4f}"
        )

    console.print(table)

    # Fit scaling
    if len(results) >= 3:
        log_X = np.log([r['X'] for r in results])
        log_min = np.log([r['min_opt'] for r in results])

        alpha, _ = np.polyfit(log_X, log_min, 1)

        console.print(f"\n[cyan]SCALING: min R(λ) ~ X^{{{alpha:.3f}}}[/cyan]")

        if alpha < -0.1:
            console.print(Panel.fit(
                f"[bold red]⚠️ ОПАСНОСТЬ: min R(λ) падает как X^{{{alpha:.2f}}}![/bold red]\n\n"
                "Это значит есть λ которые приближаются к ядру A!\n"
                "B₁_weak может нарушаться при X → ∞.",
                box=box.DOUBLE,
                border_style="red"
            ))
        elif alpha > 0.1:
            console.print(Panel.fit(
                f"[bold green]✓ min R(λ) РАСТЁТ как X^{{{alpha:.2f}}}![/bold green]\n\n"
                "Даже худший λ даёт положительный R!\n"
                "B₁_weak безопасен.",
                box=box.DOUBLE,
                border_style="green"
            ))
        else:
            console.print(Panel.fit(
                f"[bold yellow]min R(λ) ~ const (X^{{{alpha:.2f}}})[/bold yellow]\n\n"
                "Минимум примерно постоянный.\n"
                "B₁_weak выполняется с фиксированной константой.",
                box=box.DOUBLE,
                border_style="yellow"
            ))

    return results


if __name__ == "__main__":
    main()
