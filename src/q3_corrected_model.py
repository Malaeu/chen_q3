#!/usr/bin/env python3
"""
Q3 Corrected Model: Proper Archimedes Density

Исправления по сравнению с toy model:
1. a*(ξ) = 2π(log π - Re ψ(1/4 + iπξ)) — настоящая архимедова плотность
2. Вес простых: 2 log(p) / √p (множитель 2)
3. Toeplitz структура через интегрирование коэффициентов Фурье
"""

import numpy as np
from scipy.special import digamma
from scipy.linalg import expm
import matplotlib.pyplot as plt
from rich.console import Console
from rich.table import Table
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
    Архимедова плотность из Q3 (T0 нормировка)
    a*(ξ) = 2π(log π - Re ψ(1/4 + iπξ))

    где ψ — дигамма-функция (логарифмическая производная Γ)
    """
    z = 0.25 + 1j * np.pi * xi
    return 2 * np.pi * (np.log(np.pi) - np.real(digamma(z)))


def Phi_Fejer_heat(xi: float | np.ndarray, B: float, t: float) -> float | np.ndarray:
    """
    Тест-функция: Fejér kernel × Heat kernel

    Φ(ξ) = (1 - |ξ|/B)_+ × exp(-4π²t ξ²)

    - Fejér обеспечивает компактный носитель [-B, B]
    - Heat обеспечивает гладкость и регуляризацию
    """
    fejer = np.maximum(0, 1 - np.abs(xi) / B)
    heat = np.exp(-4 * np.pi**2 * t * xi**2)
    return fejer * heat


def compute_Ak(k: int, B: float, t: float, num_points: int = 2000) -> float:
    """
    Коэффициенты Фурье для Toeplitz матрицы T_A

    A_k = ∫ a*(ξ) × Φ(ξ) × cos(k ξ) dξ
    """
    xi_grid = np.linspace(-B, B, num_points)
    dxi = xi_grid[1] - xi_grid[0]

    integrand = a_star(xi_grid) * Phi_Fejer_heat(xi_grid, B, t) * np.cos(k * xi_grid)
    return np.trapezoid(integrand, dx=dxi)


def build_toeplitz_T_A(M: int, B: float, t: float) -> np.ndarray:
    """
    Строит Toeplitz матрицу T_A размера M×M

    T_A[i,j] = A_{|i-j|}
    """
    console.print("[cyan]Computing Fourier coefficients A_k...[/cyan]")
    A_coeffs = [compute_Ak(k, B, t) for k in range(M)]

    T_A = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            T_A[i, j] = A_coeffs[abs(i - j)]

    return T_A, A_coeffs


def build_prime_operator_T_P(
    M: int, B: float, t: float, K: float
) -> tuple[np.ndarray, list[int]]:
    """
    Строит прайм-оператор T_P

    T_P = Σ_p w_Q(p) × Φ(ξ_p) × |cos(k ξ_p)⟩⟨cos(j ξ_p)|

    где:
    - ξ_p = log(p) / (2π)  — позиция простого на спектральной оси
    - w_Q(p) = 2 log(p) / √p  — вес из явной формулы
    """
    # Простые в компакте: p ≤ exp(2π K)
    max_prime = int(np.exp(2 * np.pi * K)) + 10
    primes = get_primes(max_prime)

    # Фильтруем простые по компакту
    primes_in_compact = []
    for p in primes:
        xi_p = np.log(p) / (2 * np.pi)
        if np.abs(xi_p) <= K:
            primes_in_compact.append(p)

    console.print(f"[yellow]Primes in compact [-{K}, {K}]: {len(primes_in_compact)}[/yellow]")

    T_P = np.zeros((M, M))
    for p in primes_in_compact:
        xi_p = np.log(p) / (2 * np.pi)

        # Вес: w_Q(p) = 2 Λ(p) / √p = 2 log(p) / √p
        w_p = 2 * np.log(p) / np.sqrt(p)

        # Значение тест-функции в точке простого
        phi_p = Phi_Fejer_heat(xi_p, B, t)

        # Rank-1 update через косинусы (реальный базис)
        cos_vec = np.array([np.cos(k * xi_p) for k in range(M)])
        T_P += w_p * phi_p * np.outer(cos_vec, cos_vec)

    return T_P, primes_in_compact


def run_q3_corrected(
    K: float = 1.0,
    M: int = 50,
    t_heat: float = 0.1,
    B: float = 1.0,
    plot: bool = True,
    save_plot: str = None,
):
    """
    Запуск исправленной Q3 модели

    Args:
        K: Размер компакта [-K, K] на спектральной оси
        M: Размер Toeplitz матрицы
        t_heat: Heat параметр (регуляризация)
        B: Bandwidth для Fejér kernel
        plot: Показывать графики
        save_plot: Путь для сохранения
    """
    console.print(Panel.fit("[bold cyan]Q3 CORRECTED MODEL[/bold cyan]", box=box.DOUBLE))

    # Параметры
    table = Table(title="Parameters", box=box.ROUNDED)
    table.add_column("Parameter", style="cyan")
    table.add_column("Value", style="green")
    table.add_row("K (compact size)", str(K))
    table.add_row("M (matrix size)", str(M))
    table.add_row("t_heat", str(t_heat))
    table.add_row("B (Fejér bandwidth)", str(B))
    console.print(table)

    # 1. Строим T_A
    console.print("\n[bold]Building Archimedes operator T_A...[/bold]")
    T_A, A_coeffs = build_toeplitz_T_A(M, B, t_heat)

    # 2. Строим T_P
    console.print("\n[bold]Building Prime operator T_P...[/bold]")
    T_P, primes_used = build_prime_operator_T_P(M, B, t_heat, K)

    # 3. Гамильтониан
    console.print("\n[bold]Computing H = T_A - T_P...[/bold]")
    H = T_A - T_P

    # Проверка симметричности
    sym_error = np.max(np.abs(H - H.T))
    console.print(f"[dim]Symmetry check: max|H - H^T| = {sym_error:.2e}[/dim]")

    # 4. Спектр
    console.print("[bold]Diagonalizing H...[/bold]")
    eigenvalues = np.linalg.eigvalsh(H)
    eigenvalues_sorted = np.sort(eigenvalues)

    # 5. Результаты
    console.print("\n")
    results_table = Table(title="SPECTRAL RESULTS", box=box.DOUBLE)
    results_table.add_column("Metric", style="cyan")
    results_table.add_column("Value", style="yellow")

    results_table.add_row("Min eigenvalue", f"{eigenvalues_sorted[0]:.6f}")
    results_table.add_row("Max eigenvalue", f"{eigenvalues_sorted[-1]:.6f}")
    results_table.add_row("Mean eigenvalue", f"{np.mean(eigenvalues):.6f}")
    results_table.add_row("N(λ < 0)", str(np.sum(eigenvalues < 0)))
    console.print(results_table)

    # Вердикт
    console.print("\n")
    if eigenvalues_sorted[0] >= 0:
        console.print(
            Panel.fit(
                "[bold green]Q(Φ) ≥ 0 ON THIS COMPACT![/bold green]\n"
                "[green]Weil criterion satisfied for test function Φ[/green]",
                box=box.DOUBLE,
                border_style="green",
            )
        )
    elif eigenvalues_sorted[0] > -0.01:
        console.print(
            Panel.fit(
                "[bold yellow]MARGINALLY POSITIVE[/bold yellow]\n"
                f"[yellow]Min = {eigenvalues_sorted[0]:.6f} (numerical noise?)[/yellow]",
                box=box.DOUBLE,
                border_style="yellow",
            )
        )
    else:
        console.print(
            Panel.fit(
                "[bold red]Q(Φ) < 0 DETECTED[/bold red]\n"
                f"[red]Min eigenvalue = {eigenvalues_sorted[0]:.6f}[/red]\n"
                "[red]Either RH fails or test function needs adjustment[/red]",
                box=box.DOUBLE,
                border_style="red",
            )
        )

    # 6. Сравнение с нулями дзеты
    # Первые 20 известных нулей (мнимые части)
    gamma_known = [
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
        52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
        67.079811, 69.546402, 72.067158, 75.704691, 77.144840
    ]

    if plot:
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))

        # 1. Архимедова плотность a*(ξ)
        ax1 = axes[0, 0]
        xi_plot = np.linspace(-2, 2, 500)
        ax1.plot(xi_plot, a_star(xi_plot), 'b-', lw=2)
        ax1.axhline(y=0, color='r', linestyle='--', alpha=0.5)
        ax1.set_xlabel('ξ')
        ax1.set_ylabel('a*(ξ)')
        ax1.set_title('Archimedes Density a*(ξ) = 2π(log π - Re ψ(1/4 + iπξ))')
        ax1.grid(True, alpha=0.3)

        # 2. Спектр H
        ax2 = axes[0, 1]
        ax2.hist(eigenvalues_sorted, bins=30, alpha=0.7, color='steelblue', edgecolor='black')
        ax2.axvline(x=0, color='r', linestyle='--', lw=2, label='Zero line')
        ax2.set_xlabel('Eigenvalue')
        ax2.set_ylabel('Count')
        ax2.set_title('Spectrum of H = T_A - T_P')
        ax2.legend()
        ax2.grid(True, alpha=0.3)

        # 3. Коэффициенты Фурье A_k
        ax3 = axes[1, 0]
        ax3.plot(A_coeffs, 'o-', markersize=4)
        ax3.set_xlabel('k')
        ax3.set_ylabel('A_k')
        ax3.set_title('Fourier Coefficients of a*(ξ)Φ(ξ)')
        ax3.grid(True, alpha=0.3)

        # 4. Level spacings сравнение
        ax4 = axes[1, 1]
        n_compare = min(20, len(eigenvalues_sorted))
        spacings_H = np.diff(eigenvalues_sorted[:n_compare])
        spacings_gamma = np.diff(gamma_known[:n_compare])

        if len(spacings_H) > 0 and np.mean(spacings_H) != 0:
            ax4.plot(spacings_H / np.mean(spacings_H), 'o-', label='H spacings (normalized)', alpha=0.8)
        if len(spacings_gamma) > 0:
            ax4.plot(spacings_gamma / np.mean(spacings_gamma), 's-', label='ζ zeros spacings (normalized)', alpha=0.8)
        ax4.set_xlabel('Index')
        ax4.set_ylabel('Normalized spacing')
        ax4.set_title('Level Spacing Comparison')
        ax4.legend()
        ax4.grid(True, alpha=0.3)

        plt.tight_layout()

        if save_plot:
            plt.savefig(save_plot, dpi=150, bbox_inches='tight')
            console.print(f"[green]Plot saved: {save_plot}[/green]")

        plt.show()

    return {
        "eigenvalues": eigenvalues_sorted,
        "H": H,
        "T_A": T_A,
        "T_P": T_P,
        "primes": primes_used,
        "A_coeffs": A_coeffs,
    }


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Q3 Corrected Model")
    parser.add_argument("-K", type=float, default=1.0, help="Compact size (default: 1.0)")
    parser.add_argument("-M", type=int, default=50, help="Matrix size (default: 50)")
    parser.add_argument("-t", "--t-heat", type=float, default=0.1, help="Heat parameter")
    parser.add_argument("-B", type=float, default=1.0, help="Fejér bandwidth")
    parser.add_argument("--no-plot", action="store_true", help="Disable plots")
    parser.add_argument("-o", "--output", type=str, help="Save plot to file")

    args = parser.parse_args()

    run_q3_corrected(
        K=args.K,
        M=args.M,
        t_heat=args.t_heat,
        B=args.B,
        plot=not args.no_plot,
        save_plot=args.output,
    )
