#!/usr/bin/env python3
"""
Критический вопрос 1: Связь E_comm ↔ E_dir
==========================================

ЦЕЛЬ: Проверить тождество
  E_comm = |[T_lat, Ξ]Φ|² = Σ_{n,m} P_{nm} (λ_n - λ_m)² · f(ξ_n, ξ_m)

для некоторой функции f и весов P_{nm} ∝ G_{nm}².

АНАЛИТИЧЕСКИЙ ВЫВОД:

Коммутатор [T_lat, Ξ]Φ для Φ = Σ_n λ_n k_n:

[T_lat, Ξ]Φ = T_lat(ΞΦ) - Ξ(T_lat Φ)

где ΞΦ = ξ·Φ (умножение на координату).

В базисе {k_n}:
  T_lat(ΞΦ) = Σ_n ⟨ΞΦ, k_n⟩ k_n = Σ_n (Ξ·λ)_n k_n

где Ξ_nm = ⟨ξ·k_m, k_n⟩ = (ξ_n + ξ_m)/2 · G_nm

Тогда:
  c_n := ξ_n·(G·λ)_n - (Ξ·λ)_n
       = ξ_n Σ_m G_nm λ_m - Σ_m (ξ_n+ξ_m)/2 · G_nm λ_m
       = (1/2) Σ_m G_nm (ξ_n - ξ_m) λ_m

И E_comm = c^T G c = Σ_{n,p} c_n G_{np} c_p

Подставляем:
  E_comm = (1/4) Σ_{n,p} G_{np} [Σ_m G_nm(ξ_n-ξ_m)λ_m] [Σ_q G_{pq}(ξ_p-ξ_q)λ_q]

ЭТО 4-ИНДЕКСНАЯ СУММА! Не очевидно как свести к Dirichlet.

ПРОВЕРИМ ЧИСЛЕННО: соотношение E_comm / E_dir для разных λ.
"""

import numpy as np
from math import log, pi, sqrt, exp
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def G(delta: float, t: float) -> float:
    """Gaussian overlap."""
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def compute_all_energies(N: int, Delta: float, t: float):
    """
    Compute E_lat, E_comm, E_dir for various λ vectors.
    Check if E_comm ∝ E_dir.
    """
    # Build matrices
    positions = np.array([n * Delta for n in range(N)])

    G_mat = np.zeros((N, N))
    Xi_mat = np.zeros((N, N))
    for n in range(N):
        for m in range(N):
            delta = positions[n] - positions[m]
            G_mat[n, m] = G(delta, t)
            Xi_mat[n, m] = (positions[n] + positions[m]) / 2 * G_mat[n, m]

    # Transition matrix for Dirichlet form
    row_sums = G_mat.sum(axis=1)
    P = G_mat / row_sums[:, np.newaxis]

    def compute_E_lat(lam):
        """E_lat = ‖G·λ‖²"""
        Glam = G_mat @ lam
        return np.sum(Glam**2)

    def compute_E_comm(lam):
        """E_comm = c^T G c where c = ξ⊙(Gλ) - Ξλ"""
        Glam = G_mat @ lam
        Xi_lam = Xi_mat @ lam
        c = positions * Glam - Xi_lam
        return c @ G_mat @ c

    def compute_E_dir(lam):
        """E_dir = (1/2) Σ_{n,m} P_{nm} (λ_n - λ_m)²"""
        E = 0.0
        for n in range(N):
            for m in range(N):
                E += P[n, m] * (lam[n] - lam[m])**2
        return 0.5 * E

    def compute_E_dir_weighted(lam, weight_func):
        """E_dir_weighted = (1/2) Σ_{n,m} W_{nm} (λ_n - λ_m)²"""
        E = 0.0
        for n in range(N):
            for m in range(N):
                W = weight_func(positions[n], positions[m], G_mat[n, m])
                E += W * (lam[n] - lam[m])**2
        return 0.5 * E

    # Test vectors
    results = []

    test_cases = {
        'linear': np.array([n - N/2 for n in range(N)]),
        'alternating': np.array([(-1)**n for n in range(N)], dtype=float),
        'quadratic': np.array([(n - N/2)**2 for n in range(N)]),
        'random1': None,
        'random2': None,
        'peak': np.zeros(N),
        'twin': np.zeros(N),
    }

    test_cases['peak'][N//2] = 1.0
    test_cases['twin'][N//2] = 1.0
    test_cases['twin'][N//2 + 1] = 1.0

    np.random.seed(42)
    test_cases['random1'] = np.random.randn(N)
    test_cases['random2'] = np.random.randn(N)

    # Make mean-zero
    for name, lam in test_cases.items():
        lam = lam - np.mean(lam)
        test_cases[name] = lam

    for name, lam in test_cases.items():
        E_lat = compute_E_lat(lam)
        E_comm = compute_E_comm(lam)
        E_dir = compute_E_dir(lam)

        # Try weighted Dirichlet with different weights
        # W1: P_{nm} · |ξ_n - ξ_m|²
        E_dir_w1 = compute_E_dir_weighted(lam, lambda x, y, g: P[int(x/Delta), int(y/Delta)] * (x-y)**2)

        # W2: G_{nm}² · |ξ_n - ξ_m|²
        E_dir_w2 = compute_E_dir_weighted(lam, lambda x, y, g: g**2 * (x-y)**2)

        # W3: G_{nm} · |ξ_n - ξ_m|²
        E_dir_w3 = compute_E_dir_weighted(lam, lambda x, y, g: g * (x-y)**2)

        results.append({
            'name': name,
            'E_lat': E_lat,
            'E_comm': E_comm,
            'E_dir': E_dir,
            'E_dir_w2': E_dir_w2,
            'E_dir_w3': E_dir_w3,
            'ratio_comm_dir': E_comm / E_dir if E_dir > 1e-15 else 0,
            'ratio_comm_w2': E_comm / E_dir_w2 if E_dir_w2 > 1e-15 else 0,
            'ratio_comm_w3': E_comm / E_dir_w3 if E_dir_w3 > 1e-15 else 0,
        })

    return results, G_mat, P


def main():
    console.print(Panel.fit(
        "[bold cyan]КРИТИЧЕСКИЙ ВОПРОС 1:[/bold cyan]\n"
        "[dim]Связь E_comm ↔ E_dir[/dim]",
        box=box.DOUBLE
    ))

    N = 20
    Delta = 0.5
    t = 1.0

    console.print(f"\n[dim]Parameters: N={N}, Δ={Delta}, t={t}[/dim]\n")

    results, G_mat, P = compute_all_energies(N, Delta, t)

    # Table 1: Basic ratios
    table = Table(title="E_comm vs E_dir", box=box.DOUBLE)
    table.add_column("λ type", style="cyan")
    table.add_column("E_comm", style="green", justify="right")
    table.add_column("E_dir", style="blue", justify="right")
    table.add_column("E_comm/E_dir", style="yellow", justify="right")

    for r in results:
        table.add_row(
            r['name'],
            f"{r['E_comm']:.4e}",
            f"{r['E_dir']:.4e}",
            f"{r['ratio_comm_dir']:.4f}"
        )

    console.print(table)

    # Check if ratio is constant
    ratios = [r['ratio_comm_dir'] for r in results if r['ratio_comm_dir'] > 0]
    ratio_min = min(ratios)
    ratio_max = max(ratios)
    ratio_cv = np.std(ratios) / np.mean(ratios)  # coefficient of variation

    console.print(f"\n[yellow]E_comm/E_dir analysis:[/yellow]")
    console.print(f"  min = {ratio_min:.4f}")
    console.print(f"  max = {ratio_max:.4f}")
    console.print(f"  CV (coef of variation) = {ratio_cv:.4f}")

    if ratio_cv < 0.1:
        console.print(f"  [green]✓ Ratio is approximately CONSTANT! E_comm ≈ {np.mean(ratios):.4f} · E_dir[/green]")
    else:
        console.print(f"  [red]✗ Ratio varies significantly (CV = {ratio_cv:.2f})[/red]")

    # Table 2: Weighted Dirichlet forms
    console.print("\n" + "="*60)
    table2 = Table(title="E_comm vs Weighted Dirichlet Forms", box=box.DOUBLE)
    table2.add_column("λ type", style="cyan")
    table2.add_column("E_comm/E_dir_w2", style="green", justify="right")
    table2.add_column("E_comm/E_dir_w3", style="blue", justify="right")

    for r in results:
        table2.add_row(
            r['name'],
            f"{r['ratio_comm_w2']:.6f}",
            f"{r['ratio_comm_w3']:.6f}"
        )

    console.print(table2)

    # Check w2 and w3
    ratios_w2 = [r['ratio_comm_w2'] for r in results if r['ratio_comm_w2'] > 0]
    ratios_w3 = [r['ratio_comm_w3'] for r in results if r['ratio_comm_w3'] > 0]

    cv_w2 = np.std(ratios_w2) / np.mean(ratios_w2)
    cv_w3 = np.std(ratios_w3) / np.mean(ratios_w3)

    console.print(f"\n[yellow]Weighted Dirichlet analysis:[/yellow]")
    console.print(f"  E_dir_w2 = (1/2)Sum G^2 |xi_n-xi_m|^2 (lam_n-lam_m)^2")
    console.print(f"    CV = {cv_w2:.4f}, mean ratio = {np.mean(ratios_w2):.6f}")

    console.print(f"  E_dir_w3 = (1/2)Sum G |xi_n-xi_m|^2 (lam_n-lam_m)^2")
    console.print(f"    CV = {cv_w3:.4f}, mean ratio = {np.mean(ratios_w3):.6f}")

    # Find the best weighted Dirichlet
    best_cv = min(cv_w2, cv_w3, ratio_cv)
    if best_cv == ratio_cv:
        best_name = "E_dir (standard)"
    elif best_cv == cv_w2:
        best_name = "E_dir_w2 (G² weighted)"
    else:
        best_name = "E_dir_w3 (G weighted)"

    console.print(f"\n[green]Best match: {best_name} with CV = {best_cv:.4f}[/green]")

    # Final verdict
    console.print("\n" + "="*60)

    if best_cv < 0.2:
        console.print(Panel.fit(
            f"[bold green]✓ СВЯЗЬ НАЙДЕНА![/bold green]\n\n"
            f"E_comm ∝ E_dir с коэффициентом вариации {best_cv:.2%}\n\n"
            f"Это даёт:\n"
            f"  CD(κ,∞) → Пуанкаре: E_dir ≥ κ·Var\n"
            f"  ⇒ E_comm ≥ c·E_dir ≥ c·κ·Var\n"
            f"  ⇒ Model B₁ следует из CD!",
            box=box.DOUBLE,
            border_style="green"
        ))
    else:
        console.print(Panel.fit(
            f"[bold yellow]⚠️ СВЯЗЬ НЕ ПРЯМАЯ[/bold yellow]\n\n"
            f"E_comm и E_dir НЕ пропорциональны напрямую.\n"
            f"CV = {best_cv:.2%} слишком высокий.\n\n"
            f"Но возможно существует более сложная связь\n"
            f"через операторные неравенства.",
            box=box.DOUBLE,
            border_style="yellow"
        ))

    return results


if __name__ == "__main__":
    main()
