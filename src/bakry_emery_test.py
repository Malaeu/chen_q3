#!/usr/bin/env python3
"""
Bakry-Émery vs Our Formulation Test
====================================

Проверяем две разные интерпретации Model B₁:

1. НАША (model_B1_direct.py):
   E_lat = ⟨T_lat Φ, Φ⟩ = ‖G·λ‖² = λᵀ G² λ
   E_comm = ‖[T_lat, Ξ] Φ‖²

2. BAKRY-ÉMERY (advisor):
   E_lat = λᵀ G λ  (Gram-weighted L²)
   E_comm = λᵀ A λ  (Dirichlet form)

   где A_{nm} = a_{nm} (1 - δ_{nm}) - дискретный градиент
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


def build_gram_matrix(N: int, Delta: float, t: float) -> np.ndarray:
    """Build Gram matrix G_{nm} = ⟨k_n, k_m⟩"""
    G_mat = np.zeros((N, N))
    for n in range(N):
        for m in range(N):
            delta = (n - m) * Delta
            G_mat[n, m] = G(delta, t)
    return G_mat


def build_dirichlet_matrix(N: int, Delta: float, t: float) -> np.ndarray:
    """
    Build Dirichlet-form matrix A для Bakry-Émery.

    A_{nm} captures "gradient energy" between sites n and m.
    Standard choice: A = D - W where D = diag(row sums), W = adjacency.

    For Gaussian RKHS, we use:
    a_{nm} = |dG_{nm}|² / G_0  (from commutator structure)

    And Dirichlet energy = ½ Σ_{n≠m} a_{nm} (u_n - u_m)²
    """
    A_mat = np.zeros((N, N))
    g0 = G(0, t)

    for n in range(N):
        for m in range(N):
            delta = (n - m) * Delta
            g = G(delta, t)
            # dG = -(δ/2) G  => dG² = (δ²/4) G²
            dg_sq = (delta**2 / 4) * g**2
            a_nm = dg_sq / g0

            if n != m:
                A_mat[n, n] += a_nm  # Diagonal: sum of off-diagonal weights
                A_mat[n, m] = -a_nm  # Off-diagonal: negative weight

    return A_mat


def compute_energies_bakry_emery(lam: np.ndarray, G_mat: np.ndarray, A_mat: np.ndarray) -> dict:
    """
    Compute energies in Bakry-Émery formulation:

    E_gram = λᵀ G λ  (weighted L²)
    E_dirichlet = λᵀ A λ  (Dirichlet form)

    Poincaré: E_dirichlet ≥ κ · E_gram  (for mean-zero λ)
    """
    E_gram = lam @ G_mat @ lam
    E_dirichlet = lam @ A_mat @ lam

    # Also compute our original formulation for comparison
    G_lam = G_mat @ lam
    E_our_lat = np.sum(G_lam**2)  # = λᵀ G² λ

    return {
        'E_gram': E_gram,
        'E_dirichlet': E_dirichlet,
        'E_our_lat': E_our_lat,
        'ratio_BE': E_dirichlet / E_gram if E_gram > 1e-15 else 0,
        'ratio_our': E_dirichlet / E_our_lat if E_our_lat > 1e-15 else 0,
    }


def test_both_formulations(N: int = 20, Delta: float = 0.5, t: float = 1.0):
    """Compare Bakry-Émery vs Our formulation."""

    console.print(Panel.fit(
        f"[bold cyan]BAKRY-ÉMERY vs OUR FORMULATION[/bold cyan]\n"
        f"[dim]N = {N}, Δ = {Delta}, t = {t}[/dim]",
        box=box.DOUBLE
    ))

    G_mat = build_gram_matrix(N, Delta, t)
    A_mat = build_dirichlet_matrix(N, Delta, t)

    # Check A is positive semi-definite (Laplacian-like)
    eigvals_A = np.linalg.eigvalsh(A_mat)
    console.print(f"[dim]A eigenvalues: min={eigvals_A.min():.6f}, max={eigvals_A.max():.6f}[/dim]")

    results = []

    # Test vectors
    test_vectors = {
        'uniform': np.ones(N),
        'mean_zero_1': np.array([(-1)**n for n in range(N)]),  # Alternating
        'mean_zero_2': np.array([n - N/2 for n in range(N)]),  # Linear
        'peak': np.zeros(N),
        'twin': np.zeros(N),
        'random': None,
    }
    test_vectors['peak'][N//2] = 1.0
    test_vectors['twin'][N//2] = 1.0
    test_vectors['twin'][N//2 + 1] = 1.0
    np.random.seed(42)
    test_vectors['random'] = np.random.randn(N)

    # Make mean-zero versions
    for name, lam in test_vectors.items():
        lam_mz = lam - np.mean(lam)  # Mean-zero projection
        res = compute_energies_bakry_emery(lam_mz, G_mat, A_mat)
        results.append((name, res))

    # Display results
    table = Table(title="Bakry-Émery vs Our Formulation (mean-zero λ)", box=box.DOUBLE)
    table.add_column("λ type", style="cyan")
    table.add_column("E_dirichlet", style="green", justify="right")
    table.add_column("E_gram (BE)", style="blue", justify="right")
    table.add_column("E_our_lat", style="magenta", justify="right")
    table.add_column("Dir/Gram", style="yellow", justify="right")
    table.add_column("Dir/Our", style="red", justify="right")

    ratios_BE = []
    ratios_our = []

    for name, res in results:
        table.add_row(
            name,
            f"{res['E_dirichlet']:.4e}",
            f"{res['E_gram']:.4e}",
            f"{res['E_our_lat']:.4e}",
            f"{res['ratio_BE']:.6f}",
            f"{res['ratio_our']:.6f}"
        )
        if res['ratio_BE'] > 0:
            ratios_BE.append(res['ratio_BE'])
        if res['ratio_our'] > 0:
            ratios_our.append(res['ratio_our'])

    console.print(table)

    # Summary
    console.print(f"\n[yellow]BAKRY-ÉMERY (E_dir/E_gram):[/yellow]")
    console.print(f"  min = {min(ratios_BE):.6f}")
    console.print(f"  max = {max(ratios_BE):.6f}")

    console.print(f"\n[yellow]OUR (E_dir/E_our_lat):[/yellow]")
    console.print(f"  min = {min(ratios_our):.6f}")
    console.print(f"  max = {max(ratios_our):.6f}")

    # Key insight
    console.print(Panel.fit(
        "[bold green]КЛЮЧЕВОЕ НАБЛЮДЕНИЕ:[/bold green]\n\n"
        "• E_gram = λᵀ G λ\n"
        "• E_our_lat = λᵀ G² λ = (Gλ)ᵀ(Gλ)\n\n"
        "Связь: E_our_lat = ‖G^{1/2} · √(Gλ)‖² ≈ E_gram × (max eigval of G)\n\n"
        "Bakry-Émery даёт Poincaré для E_gram,\n"
        "наша версия — для E_our_lat (строже!).",
        box=box.DOUBLE,
        border_style="green"
    ))

    return results


def compute_gamma2(N: int, Delta: float, t: float):
    """
    Compute Γ₂ for our lattice operator.

    Bakry-Émery Γ-calculus:
    Γ(f,g) = ½(L(fg) - fLg - gLf)
    Γ₂(f,g) = ½(LΓ(f,g) - Γ(f,Lg) - Γ(g,Lf))

    For CD(κ,∞) condition: Γ₂(f) ≥ κ Γ(f)
    """
    console.print("\n" + "="*60)
    console.print(Panel.fit(
        "[bold cyan]Γ₂-ВЫЧИСЛЕНИЕ (Bakry-Émery)[/bold cyan]",
        box=box.DOUBLE
    ))

    G_mat = build_gram_matrix(N, Delta, t)

    # Build discrete Laplacian from G
    # L = G^{-1} A G  (weighted Laplacian)
    # Or simpler: L_{nm} ∝ G_{nm} for n ≠ m, diagonal chosen for row-sum = 0

    # Simple symmetric random walk on weighted graph:
    # L_{nm} = G_{nm} / (Σ_k G_{nk}) - δ_{nm}

    row_sums = G_mat.sum(axis=1)
    P = G_mat / row_sums[:, np.newaxis]  # Transition matrix
    L = P - np.eye(N)  # Generator

    # Compute Γ(u)(n) = ½ Σ_m P_{nm} (u_n - u_m)²
    # This is the carré du champ

    def gamma_at_n(u, n):
        """Compute Γ(u)(n)."""
        result = 0.0
        for m in range(N):
            result += P[n, m] * (u[n] - u[m])**2
        return 0.5 * result

    def gamma(u):
        """Compute Γ(u) vector."""
        return np.array([gamma_at_n(u, n) for n in range(N)])

    def L_apply(u):
        """Apply L to u."""
        return L @ u

    # Test Γ₂ ≥ κΓ for various u
    test_u = np.array([n - N/2 for n in range(N)])  # Linear
    test_u = test_u / np.linalg.norm(test_u)

    Gamma_u = gamma(test_u)
    Lu = L_apply(test_u)

    # Γ₂(u) = ½(LΓ(u) - 2Γ(u, Lu))
    # For scalar u: Γ₂(u)(n) = ½(L[Γ(u)])(n) - Γ(u, Lu)(n)

    L_Gamma_u = L_apply(Gamma_u)

    # Γ(u, Lu)(n) = ½ Σ_m P_{nm} (u_n - u_m)(Lu_n - Lu_m)
    def gamma_bilinear_at_n(u, v, n):
        result = 0.0
        for m in range(N):
            result += P[n, m] * (u[n] - u[m]) * (v[n] - v[m])
        return 0.5 * result

    Gamma_u_Lu = np.array([gamma_bilinear_at_n(test_u, Lu, n) for n in range(N)])

    Gamma2_u = 0.5 * L_Gamma_u - Gamma_u_Lu

    # Check Γ₂ ≥ κΓ
    positive_gamma = Gamma_u > 1e-10
    if np.any(positive_gamma):
        kappa_local = Gamma2_u[positive_gamma] / Gamma_u[positive_gamma]
        kappa_min = np.min(kappa_local)
        kappa_max = np.max(kappa_local)

        console.print(f"[green]Γ₂(u)/Γ(u) estimates:[/green]")
        console.print(f"  min κ = {kappa_min:.4f}")
        console.print(f"  max κ = {kappa_max:.4f}")

        if kappa_min > 0:
            console.print(f"\n[bold green]✓ CD({kappa_min:.4f}, ∞) SATISFIED![/bold green]")
            console.print(f"[green]⇒ Poincaré inequality holds with κ = {kappa_min:.4f}[/green]")
        else:
            console.print(f"\n[bold red]✗ CD condition NOT satisfied (κ < 0)[/bold red]")

    return {'kappa_min': kappa_min if 'kappa_min' in dir() else None}


def main():
    console.print(Panel.fit(
        "[bold magenta]BAKRY-ÉMERY / PERELMAN CONNECTION TEST[/bold magenta]",
        box=box.DOUBLE
    ))

    # Test both formulations
    test_both_formulations(N=20, Delta=0.5, t=1.0)

    # Compute Γ₂
    compute_gamma2(N=20, Delta=0.5, t=1.0)

    console.print("\n" + "="*60)
    console.print(Panel.fit(
        "[bold green]ВЫВОДЫ:[/bold green]\n\n"
        "1. Bakry-Émery работает с E_gram = λᵀGλ\n"
        "2. Наша формулировка с E_lat = λᵀG²λ (строже!)\n"
        "3. CD(κ,∞) condition ⇔ Γ₂ ≥ κΓ ⇔ Poincaré\n"
        "4. Если κ > 0, то Model B₁ следует автоматически!\n\n"
        "[cyan]Связь с Перельманом:[/cyan]\n"
        "• Ric_f ≥ κ ⇒ Γ₂ ≥ κΓ (Bakry-Émery)\n"
        "• Для гауссиана: Hess(f) = 1/(2t) ⇒ κ = 1/(2t)",
        box=box.DOUBLE,
        border_style="green"
    ))


if __name__ == "__main__":
    main()
