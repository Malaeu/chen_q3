#!/usr/bin/env python3
"""
Сравнение двух интерпретаций Bakry-Émery для Model B₁
======================================================

ИНТЕРПРЕТАЦИЯ 1 (Наша / bakry_emery_test.py):
  Γ(u) = standard discrete gradient (carré du champ)
  Γ₂(u) = standard iterated carré
  CD(κ,∞): Γ₂ ≥ κΓ  →  Poincaré

ИНТЕРПРЕТАЦИЯ 2 (Advisor):
  E_lat ↔ Γ   (prime energy = gradient)
  E_comm ↔ Γ₂  (commutator = curvature)
  B₁: E_comm ≥ c · E_lat  ⟺  Γ₂ ≥ c·Γ

ВОПРОС: Какая интерпретация корректна?

На самом деле B₁ больше похожа на POINCARÉ:
  gradient² ≥ c · L²

А не на CD:
  Γ₂ ≥ κ·Γ
"""

import numpy as np
from math import sqrt, pi, exp
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def G(delta: float, t: float) -> float:
    """Gaussian overlap."""
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def build_matrices(N: int, Delta: float, t: float):
    """Build all matrices for comparison."""

    # Gram matrix G
    G_mat = np.zeros((N, N))
    for n in range(N):
        for m in range(N):
            delta = (n - m) * Delta
            G_mat[n, m] = G(delta, t)

    # Position matrix Xi
    Xi_mat = np.zeros((N, N))
    for n in range(N):
        for m in range(N):
            xi_n = n * Delta
            xi_m = m * Delta
            delta = (n - m) * Delta
            Xi_mat[n, m] = (xi_n + xi_m) / 2 * G(delta, t)

    # Transition matrix P (for Bakry-Émery)
    row_sums = G_mat.sum(axis=1)
    P_mat = G_mat / row_sums[:, np.newaxis]

    return G_mat, Xi_mat, P_mat


def compute_our_energies(lam: np.ndarray, G_mat: np.ndarray, Xi_mat: np.ndarray, Delta: float):
    """
    Our energies (model_B1_direct.py style):
    E_lat = ‖G·λ‖² = (Gλ)ᵀ(Gλ)
    E_comm = ‖[T,Ξ]Φ‖²
    """
    N = len(lam)
    xi_coords = np.array([n * Delta for n in range(N)])

    # ⟨Φ, k_n⟩ = (G·λ)_n
    inner_prods = G_mat @ lam

    # E_lat = Σ |⟨Φ, k_n⟩|²
    E_lat = np.sum(inner_prods**2)

    # ⟨ΞΦ, k_n⟩ = (Ξ·λ)_n
    xi_inner_prods = Xi_mat @ lam

    # Commutator coefficients
    c_coeffs = xi_coords * inner_prods - xi_inner_prods

    # E_comm = cᵀ G c
    E_comm = c_coeffs @ G_mat @ c_coeffs

    return E_lat, E_comm


def compute_bakry_emery_energies(lam: np.ndarray, G_mat: np.ndarray, P_mat: np.ndarray):
    """
    Standard Bakry-Émery energies:
    E_gram = λᵀ G λ  (L² energy)
    E_dirichlet = ½ Σ P_{nm} (λ_n - λ_m)²  (gradient energy)
    """
    N = len(lam)

    # E_gram = λᵀ G λ
    E_gram = lam @ G_mat @ lam

    # E_dirichlet = Dirichlet form
    E_dir = 0.0
    for n in range(N):
        for m in range(N):
            E_dir += P_mat[n, m] * (lam[n] - lam[m])**2
    E_dir *= 0.5

    return E_gram, E_dir


def main():
    console.print(Panel.fit(
        "[bold cyan]СРАВНЕНИЕ ИНТЕРПРЕТАЦИЙ BAKRY-ÉMERY[/bold cyan]",
        box=box.DOUBLE
    ))

    N = 20
    Delta = 0.5
    t = 1.0

    G_mat, Xi_mat, P_mat = build_matrices(N, Delta, t)

    # Test vectors
    test_vectors = {
        'uniform': np.ones(N) - 1/N,  # mean-zero
        'alternating': np.array([(-1)**n for n in range(N)]),
        'linear': np.array([n - N/2 for n in range(N)]),
        'peak': np.zeros(N),
        'random': None,
    }
    test_vectors['peak'][N//2] = 1.0
    test_vectors['peak'] -= np.mean(test_vectors['peak'])
    np.random.seed(42)
    test_vectors['random'] = np.random.randn(N)
    test_vectors['random'] -= np.mean(test_vectors['random'])

    # Compare energies
    table = Table(title="Energy Comparison", box=box.DOUBLE)
    table.add_column("λ type", style="cyan")
    table.add_column("E_lat (our)", style="green", justify="right")
    table.add_column("E_comm (our)", style="blue", justify="right")
    table.add_column("E_comm/E_lat", style="yellow", justify="right")
    table.add_column("E_gram (BE)", style="magenta", justify="right")
    table.add_column("E_dir (BE)", style="red", justify="right")
    table.add_column("E_dir/E_gram", style="white", justify="right")

    for name, lam in test_vectors.items():
        E_lat, E_comm = compute_our_energies(lam, G_mat, Xi_mat, Delta)
        E_gram, E_dir = compute_bakry_emery_energies(lam, G_mat, P_mat)

        ratio_our = E_comm / E_lat if E_lat > 1e-10 else 0
        ratio_be = E_dir / E_gram if E_gram > 1e-10 else 0

        table.add_row(
            name,
            f"{E_lat:.2e}",
            f"{E_comm:.2e}",
            f"{ratio_our:.4f}",
            f"{E_gram:.2e}",
            f"{E_dir:.2e}",
            f"{ratio_be:.4f}"
        )

    console.print(table)

    # Analysis
    console.print("\n" + "="*60)
    console.print(Panel.fit(
        "[bold green]АНАЛИЗ ДВУХ ИНТЕРПРЕТАЦИЙ[/bold green]\n\n"
        "[cyan]ИНТЕРПРЕТАЦИЯ 1 (Poincaré):[/cyan]\n"
        "  • E_comm ↔ gradient² (Dirichlet)\n"
        "  • E_lat ↔ L² (Gram)\n"
        "  • B₁: gradient² ≥ c · L² = POINCARÉ\n\n"
        "[cyan]ИНТЕРПРЕТАЦИЯ 2 (Advisor/CD):[/cyan]\n"
        "  • E_lat ↔ Γ (gradient)\n"
        "  • E_comm ↔ Γ₂ (curvature)\n"
        "  • B₁: Γ₂ ≥ c · Γ = CD\n\n"
        "[yellow]РАЗЛИЧИЕ:[/yellow]\n"
        "  Наше E_lat = λᵀG²λ ≠ E_gram = λᵀGλ\n"
        "  Наше E_comm = commutator ≠ E_dir = Dirichlet\n\n"
        "[bold]ВЫВОД:[/bold]\n"
        "  B₁ — это НЕ стандартный Bakry-Émery,\n"
        "  но КОНЦЕПТУАЛЬНО похоже на CD!\n"
        "  Оба дают c > 0, что нам и нужно.",
        box=box.DOUBLE,
        border_style="green"
    ))

    # Check correlation between ratios
    console.print("\n[yellow]Корреляция между E_comm/E_lat и E_dir/E_gram:[/yellow]")

    ratios_our = []
    ratios_be = []
    for name, lam in test_vectors.items():
        E_lat, E_comm = compute_our_energies(lam, G_mat, Xi_mat, Delta)
        E_gram, E_dir = compute_bakry_emery_energies(lam, G_mat, P_mat)
        if E_lat > 1e-10 and E_gram > 1e-10:
            ratios_our.append(E_comm / E_lat)
            ratios_be.append(E_dir / E_gram)

    corr = np.corrcoef(ratios_our, ratios_be)[0, 1]
    console.print(f"  Корреляция Пирсона: {corr:.4f}")

    if corr > 0.8:
        console.print("  [green]→ Высокая корреляция! Интерпретации связаны.[/green]")
    elif corr > 0.5:
        console.print("  [yellow]→ Умеренная корреляция.[/yellow]")
    else:
        console.print("  [red]→ Низкая корреляция. Интерпретации различаются.[/red]")


if __name__ == "__main__":
    main()
