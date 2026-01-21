#!/usr/bin/env python3
"""
Q3-Atom Phase 1: Galerkin Approximation with Proper Normalization

Правильная реализация:
1. Базис: f_k(ξ) = 1/√(2B) exp(i k π ξ / B) на [-B, B]
2. T_A через интеграл a*(ξ) с дигаммой
3. T_P с весами 2 log(p) / √p
4. Нормировка 1/(2B) для обоих операторов
"""

import numpy as np
from scipy.special import digamma
import matplotlib.pyplot as plt
from rich.console import Console
from rich.panel import Panel
from rich import box

console = Console()


def get_primes(n: int) -> list[int]:
    """Решето Эратосфена"""
    sieve = [True] * (n + 1)
    for x in range(2, int(n**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n + 1, x):
                sieve[i] = False
    return [x for x in range(2, n + 1) if sieve[x]]


def a_star(xi: float | np.ndarray) -> float | np.ndarray:
    """
    Архимедова плотность a*(ξ) = 2π(log π - Re ψ(1/4 + iπξ))
    """
    z = 0.25 + 1j * np.pi * xi
    return 2 * np.pi * (np.log(np.pi) - np.real(digamma(z)))


def compute_energy_matrices(M: int, B: float):
    """
    Строит матрицы T_A и T_P в Galerkin базисе

    Базис: f_k(ξ) = 1/√(2B) exp(i k π ξ / B), k = 0..M-1
    Ортонормален на [-B, B]

    T_A[j,k] = 1/(2B) ∫ a*(ξ) exp(i(j-k)πξ/B) dξ
    T_P[j,k] = 1/(2B) Σ_p w_p exp(i(j-k)πξ_p/B)
    """
    # 1. Archimedean Matrix (Toeplitz)
    console.print("[cyan]Computing Fourier coefficients for T_A...[/cyan]")

    xi_grid = np.linspace(-B, B, 5000)
    dxi = xi_grid[1] - xi_grid[0]
    densities = a_star(xi_grid)

    coeffs = []
    for d in range(M):
        # Косинус из-за симметрии a*(ξ)
        integrand = densities * np.cos(d * np.pi * xi_grid / B)
        val = (1.0 / (2.0 * B)) * np.trapezoid(integrand, dx=dxi)
        coeffs.append(val)

    mat_A = np.zeros((M, M))
    for r in range(M):
        for c in range(M):
            mat_A[r, c] = coeffs[abs(r - c)]

    # 2. Prime Matrix
    max_n = int(np.exp(2 * np.pi * B))
    primes = get_primes(max_n)
    console.print(f"[yellow]Primes up to {max_n}: {len(primes)}[/yellow]")

    # T_P is TOEPLITZ! Optimize: compute M coefficients, not M^2
    # P_coeffs[d] = 1/(2B) * Σ_p w_p exp(i d π ξ_p / B), d = 0..M-1
    # Then mat_P[r,c] = P_coeffs[|r-c|] (symmetric real part)

    P_coeffs = np.zeros(M, dtype=complex)
    primes_in_band = 0

    # Filter primes in bandwidth first
    xi_all = np.log(np.array(primes, dtype=float)) / (2 * np.pi)
    mask = np.abs(xi_all) <= B
    primes_in = np.array(primes)[mask]
    xi_in = xi_all[mask]
    primes_in_band = len(primes_in)

    console.print(f"[yellow]Primes in bandwidth [-{B}, {B}]: {primes_in_band}[/yellow]")

    # Vectorized computation of weights
    w_all = 2 * np.log(primes_in) / np.sqrt(primes_in)

    # Compute Toeplitz coefficients
    console.print("[cyan]Computing T_P Toeplitz coefficients...[/cyan]")
    for d in range(M):
        phases = d * np.pi * xi_in / B
        P_coeffs[d] = (1.0 / (2.0 * B)) * np.sum(w_all * np.exp(1j * phases))

    # Build Toeplitz matrix (Hermitian)
    mat_P = np.zeros((M, M), dtype=complex)
    for r in range(M):
        for c in range(M):
            diff = abs(r - c)
            if r >= c:
                mat_P[r, c] = P_coeffs[diff]
            else:
                mat_P[r, c] = np.conj(P_coeffs[diff])

    return mat_A, mat_P, primes_in_band


def run_phase1(B: float = 2.5, M: int = 60, plot: bool = True, save_plot: str = None):
    """
    Phase 1: Проверка положительности H = T_A - T_P
    """
    console.print(Panel.fit("[bold cyan]Q3-ATOM PHASE 1: GALERKIN TEST[/bold cyan]", box=box.DOUBLE))
    console.print(f"[dim]Parameters: B={B}, M={M}[/dim]")
    console.print()

    # Строим матрицы
    T_A, T_P, n_primes = compute_energy_matrices(M, B)

    # H = T_A - T_P
    console.print("[cyan]Computing H = T_A - T_P...[/cyan]")
    H = T_A - T_P

    # Проверка эрмитовости
    herm_err = np.max(np.abs(H - H.conj().T))
    console.print(f"[dim]Hermitian check: max|H - H†| = {herm_err:.2e}[/dim]")

    # Спектр
    console.print("[cyan]Diagonalizing H...[/cyan]")
    evals = np.linalg.eigvalsh(H)
    sorted_evals = np.sort(evals)
    min_eval = sorted_evals[0]

    # Результат
    console.print()
    if min_eval >= 0:
        console.print(
            Panel.fit(
                f"[bold green]✓ STABLE: E_min = {min_eval:.6f}[/bold green]\n"
                f"[green]Q(Φ) ≥ 0 on this subspace![/green]\n"
                f"[green]RH Compatible within Galerkin approximation[/green]",
                box=box.DOUBLE,
                border_style="green",
            )
        )
    elif min_eval > -0.01:
        console.print(
            Panel.fit(
                f"[bold yellow]~ MARGINAL: E_min = {min_eval:.6f}[/bold yellow]\n"
                f"[yellow]Nearly positive (numerical noise?)[/yellow]",
                box=box.DOUBLE,
                border_style="yellow",
            )
        )
    else:
        console.print(
            Panel.fit(
                f"[bold red]✗ UNSTABLE: E_min = {min_eval:.6f}[/bold red]\n"
                f"[red]Q(Φ) < 0 detected[/red]",
                box=box.DOUBLE,
                border_style="red",
            )
        )

    # Известные нули дзеты
    gamma_known = [
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    ]

    if plot:
        fig, axes = plt.subplots(1, 2, figsize=(14, 5))

        # 1. Спектр H
        ax1 = axes[0]
        ax1.bar(range(len(sorted_evals)), sorted_evals, color='skyblue', edgecolor='navy', alpha=0.8)
        ax1.axhline(0, color='red', linestyle='--', linewidth=2, label='Zero Energy')
        ax1.set_title(f"Spectrum of H = T_A - T_P\nE_min = {min_eval:.4f}, Primes: {n_primes}", fontsize=12)
        ax1.set_xlabel("Mode Index")
        ax1.set_ylabel("Eigenvalue")
        ax1.legend()
        ax1.grid(True, alpha=0.3)

        # 2. Level Spacings
        ax2 = axes[1]
        spacings = np.diff(sorted_evals)
        # Фильтруем очень маленькие
        spacings = spacings[spacings > 1e-6]

        if len(spacings) > 0:
            norm_spacings = spacings / np.mean(spacings)
            g_spacings = np.diff(gamma_known)
            g_norm = g_spacings / np.mean(g_spacings)

            n_show = min(20, len(norm_spacings))
            ax2.plot(norm_spacings[:n_show], 'o-', markersize=6, label='H Spacings', color='steelblue')
            ax2.plot(g_norm, 's--', markersize=6, label='Riemann Zeros', color='darkorange')
            ax2.axhline(1, color='gray', linestyle=':', alpha=0.5)
            ax2.set_title("Normalized Level Spacings", fontsize=12)
            ax2.set_xlabel("Index")
            ax2.set_ylabel("s / ⟨s⟩")
            ax2.legend()
            ax2.grid(True, alpha=0.3)

        plt.tight_layout()

        if save_plot:
            plt.savefig(save_plot, dpi=150, bbox_inches='tight')
            console.print(f"[green]Plot saved: {save_plot}[/green]")

        plt.show()

    return {
        "min_eval": min_eval,
        "eigenvalues": sorted_evals,
        "H": H,
        "T_A": T_A,
        "T_P": T_P,
        "n_primes": n_primes,
    }


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Q3-Atom Phase 1: Galerkin Test")
    parser.add_argument("-B", type=float, default=2.5, help="Bandwidth (default: 2.5)")
    parser.add_argument("-M", type=int, default=60, help="Matrix size (default: 60)")
    parser.add_argument("--no-plot", action="store_true", help="Disable plot")
    parser.add_argument("-o", "--output", type=str, help="Save plot to file")

    args = parser.parse_args()

    run_phase1(B=args.B, M=args.M, plot=not args.no_plot, save_plot=args.output)
