#!/usr/bin/env python3
"""
Q3-Atom Toy Model: Spectral Test for Riemann Hypothesis

Строим оператор H = T_A - T_P в тригонометрическом базисе.
- T_A: "Кинетическая энергия" (Архимедов член) - диагональная, растет как log|k|
- T_P: "Потенциал простых" - сумма проекторов, пытается уронить энергию

Если min(eigenvalues) >= 0 => модель стабильна (RH compatible)
Если min < 0 => "атом развалился", нужна перенормировка
"""

import numpy as np
import matplotlib.pyplot as plt
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def get_primes(n: int) -> list[int]:
    """Решето Эратосфена до n"""
    sieve = [True] * (n + 1)
    for x in range(2, int(n**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n + 1, x):
                sieve[i] = False
    return [x for x in range(2, n + 1) if sieve[x]]


def build_archimedes_matrix(ks: np.ndarray, L: float, alpha: float = 1.0, mode: str = "log") -> np.ndarray:
    """
    Матрица Архимеда (T_A) - "стабилизатор"
    Диагональная в Фурье-пространстве

    Modes:
        - "log": W(k) ~ alpha * log(|k| + const)  -- явная формула Вейля
        - "quadratic": W(k) ~ alpha * k^2         -- свободная частица
        - "linear": W(k) ~ alpha * |k|            -- релятивистская
    """
    if mode == "log":
        W_k = alpha * 2 * np.pi * np.log(np.abs(ks) + 2.0)
    elif mode == "quadratic":
        W_k = alpha * (ks ** 2)
    elif mode == "linear":
        W_k = alpha * np.abs(ks)
    else:
        raise ValueError(f"Unknown mode: {mode}")
    return np.diag(W_k)


def build_prime_matrix(
    ks: np.ndarray, primes: list[int], L: float, T_scale: float
) -> np.ndarray:
    """
    Матрица Простых (T_P) - "потенциал"
    T_P[j,k] = sum( Lambda(p)/sqrt(p) * exp(i(j-k) * theta_p) )
    """
    D = len(ks)
    T_P = np.zeros((D, D), dtype=complex)

    for p in primes:
        # Заряд ядра: Lambda(p)/sqrt(p) = log(p)/sqrt(p)
        charge = np.log(p) / np.sqrt(p)

        # Позиция на окружности
        theta_p = (T_scale * np.log(p)) % L

        # Rank-1 update: v_p = exp(i * k * theta_p)
        vec = np.exp(1j * ks * theta_p)
        T_P += charge * np.outer(vec, vec.conj())

    return T_P


def analyze_spectrum(evals: np.ndarray) -> dict:
    """Анализ спектра"""
    # Spacings между соседними уровнями
    sorted_evals = np.sort(evals)
    spacings = np.diff(sorted_evals)

    # Нормализуем spacings на среднее
    mean_spacing = np.mean(spacings)
    normalized_spacings = spacings / mean_spacing if mean_spacing > 0 else spacings

    return {
        "min": np.min(evals),
        "max": np.max(evals),
        "mean": np.mean(evals),
        "std": np.std(evals),
        "n_negative": np.sum(evals < 0),
        "spacings": normalized_spacings,
        "mean_spacing": mean_spacing,
    }


def plot_results(evals: np.ndarray, T_P: np.ndarray, stats: dict, save_path: str = None):
    """Визуализация результатов"""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # 1. Гистограмма спектра
    ax1 = axes[0, 0]
    ax1.hist(evals, bins=40, alpha=0.7, color="steelblue", edgecolor="black")
    ax1.axvline(x=0, color="red", linestyle="--", linewidth=2, label="Zero line")
    ax1.set_title("Spectrum of H = T_A - T_P", fontsize=12)
    ax1.set_xlabel("Energy Levels")
    ax1.set_ylabel("Count")
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # 2. Level spacings (для проверки GUE)
    ax2 = axes[0, 1]
    spacings = stats["spacings"]
    ax2.hist(spacings, bins=30, alpha=0.7, color="darkgreen", edgecolor="black", density=True)

    # Теоретическая кривая Wigner (GUE)
    s = np.linspace(0, 4, 100)
    wigner = (32 / np.pi**2) * s**2 * np.exp(-4 * s**2 / np.pi)
    ax2.plot(s, wigner, "r-", linewidth=2, label="Wigner (GUE)")

    # Poisson для сравнения
    poisson = np.exp(-s)
    ax2.plot(s, poisson, "b--", linewidth=2, label="Poisson (integrable)")

    ax2.set_title("Level Spacing Distribution", fontsize=12)
    ax2.set_xlabel("Normalized spacing s")
    ax2.set_ylabel("P(s)")
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(0, 4)

    # 3. Диагональ T_P (потенциал простых)
    ax3 = axes[1, 0]
    diag_T_P = np.diag(T_P).real
    ax3.plot(diag_T_P, color="purple", linewidth=1)
    ax3.set_title("Diagonal of Prime Matrix T_P (Real part)", fontsize=12)
    ax3.set_xlabel("Index k")
    ax3.set_ylabel("T_P[k,k]")
    ax3.grid(True, alpha=0.3)

    # 4. Cumulative spectrum
    ax4 = axes[1, 1]
    sorted_evals = np.sort(evals)
    ax4.plot(sorted_evals, range(len(sorted_evals)), color="darkorange", linewidth=1.5)
    ax4.axvline(x=0, color="red", linestyle="--", linewidth=2)
    ax4.set_title("Cumulative Eigenvalue Distribution", fontsize=12)
    ax4.set_xlabel("Eigenvalue")
    ax4.set_ylabel("N(E) - counting function")
    ax4.grid(True, alpha=0.3)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        console.print(f"[green]Plot saved to: {save_path}[/green]")

    plt.show()


def run_q3_atom_model(
    M: int = 100,
    N_max: int = 500,
    L: float = 2 * np.pi,
    T_scale: float = 1.0,
    alpha: float = 1.0,
    mode: str = "log",
    plot: bool = True,
    save_plot: str = None,
):
    """
    Запуск Q3-Atom модели

    Args:
        M: Размер базиса (матрица будет 2M+1 x 2M+1)
        N_max: Максимальное число для перебора простых
        L: Длина окружности
        T_scale: Масштаб (связь log p с углом)
        alpha: Коэффициент усиления T_A (стабилизатора)
        mode: Тип кинетической энергии: "log", "quadratic", "linear"
        plot: Показывать графики
        save_plot: Путь для сохранения графика
    """
    console.print(Panel.fit("[bold cyan]Q3-ATOM TOY MODEL[/bold cyan]", box=box.DOUBLE))

    # Параметры
    table = Table(title="Parameters", box=box.ROUNDED)
    table.add_column("Parameter", style="cyan")
    table.add_column("Value", style="green")
    table.add_row("M (basis size)", str(M))
    table.add_row("Matrix dimension", str(2 * M + 1))
    table.add_row("N_max (prime limit)", str(N_max))
    table.add_row("L (circle length)", f"{L:.4f}")
    table.add_row("T_scale", str(T_scale))
    table.add_row("alpha (T_A strength)", str(alpha))
    table.add_row("mode (kinetic type)", mode)
    console.print(table)

    # 1. Готовим простые числа
    primes = get_primes(N_max)
    console.print(f"\n[yellow]Found {len(primes)} primes up to {N_max}[/yellow]")

    # Диапазон индексов k: -M ... M
    ks = np.arange(-M, M + 1)
    D = len(ks)

    # 2. Строим матрицы
    console.print(f"\n[cyan]Building Archimedes matrix T_A ({D}x{D}) [mode={mode}, alpha={alpha}]...[/cyan]")
    T_A = build_archimedes_matrix(ks, L, alpha=alpha, mode=mode)

    console.print(f"[cyan]Building Prime matrix T_P ({D}x{D}) from {len(primes)} primes...[/cyan]")
    T_P = build_prime_matrix(ks, primes, L, T_scale)

    # 3. Гамильтониан
    console.print("[cyan]Computing Hamiltonian H = T_A - T_P...[/cyan]")
    H = T_A - T_P

    # Проверка эрмитовости
    hermitian_error = np.max(np.abs(H - H.conj().T))
    console.print(f"[dim]Hermitian check: max|H - H†| = {hermitian_error:.2e}[/dim]")

    # 4. Диагонализация
    console.print("[cyan]Diagonalizing H (eigvalsh for Hermitian)...[/cyan]")
    evals = np.linalg.eigvalsh(H)

    # 5. Анализ
    stats = analyze_spectrum(evals)

    # Результаты
    console.print("\n")
    results_table = Table(title="SPECTRAL RESULTS", box=box.DOUBLE)
    results_table.add_column("Metric", style="cyan")
    results_table.add_column("Value", style="yellow")

    results_table.add_row("Min eigenvalue", f"{stats['min']:.6f}")
    results_table.add_row("Max eigenvalue", f"{stats['max']:.6f}")
    results_table.add_row("Mean eigenvalue", f"{stats['mean']:.6f}")
    results_table.add_row("Std deviation", f"{stats['std']:.6f}")
    results_table.add_row("N(lambda < 0)", str(stats["n_negative"]))
    results_table.add_row("Mean level spacing", f"{stats['mean_spacing']:.6f}")

    console.print(results_table)

    # Вердикт
    console.print("\n")
    if stats["min"] >= 0:
        console.print(
            Panel.fit(
                "[bold green]STATUS: STABLE[/bold green]\n"
                "[green]All eigenvalues >= 0[/green]\n"
                "[green]RH Compatible within this toy model![/green]",
                box=box.DOUBLE,
                border_style="green",
            )
        )
    elif stats["min"] > -0.1:
        console.print(
            Panel.fit(
                "[bold yellow]STATUS: MARGINALLY STABLE[/bold yellow]\n"
                f"[yellow]Min eigenvalue = {stats['min']:.6f}[/yellow]\n"
                "[yellow]Small negative values - may need parameter tuning[/yellow]",
                box=box.DOUBLE,
                border_style="yellow",
            )
        )
    else:
        console.print(
            Panel.fit(
                "[bold red]STATUS: UNSTABLE[/bold red]\n"
                f"[red]Min eigenvalue = {stats['min']:.6f}[/red]\n"
                "[red]'Atom collapsed' - needs renormalization or stronger T_A[/red]",
                box=box.DOUBLE,
                border_style="red",
            )
        )

    # Графики
    if plot:
        plot_results(evals, T_P, stats, save_plot)

    return {
        "eigenvalues": evals,
        "stats": stats,
        "H": H,
        "T_A": T_A,
        "T_P": T_P,
        "primes": primes,
    }


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Q3-Atom Toy Model")
    parser.add_argument("-M", type=int, default=100, help="Basis size (default: 100)")
    parser.add_argument("-N", "--n-max", type=int, default=500, help="Prime limit (default: 500)")
    parser.add_argument("-T", "--t-scale", type=float, default=1.0, help="T_scale parameter")
    parser.add_argument("-a", "--alpha", type=float, default=1.0, help="T_A strength multiplier (default: 1.0)")
    parser.add_argument("--mode", choices=["log", "quadratic", "linear"], default="log", help="Kinetic term type")
    parser.add_argument("--no-plot", action="store_true", help="Disable plots")
    parser.add_argument("-o", "--output", type=str, help="Save plot to file")

    args = parser.parse_args()

    run_q3_atom_model(
        M=args.M,
        N_max=args.n_max,
        T_scale=args.t_scale,
        alpha=args.alpha,
        mode=args.mode,
        plot=not args.no_plot,
        save_plot=args.output,
    )
