#!/usr/bin/env python3
"""
Q3 Alpha Scaling Analysis
=========================
Проверка стабильности показателя степени α при разных K.

Ключевой вопрос: α(K) → ? при K → ∞
- Если α стабилен → сильный аргумент за ∞ близнецов
- Если α растёт → нужно больше данных
"""

import numpy as np
from scipy.special import digamma
from scipy.linalg import expm
from scipy.integrate import quad
import matplotlib.pyplot as plt
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box
import time

console = Console()


def a_star(xi):
    z = 0.25 + 1j * np.pi * xi
    return 2 * np.pi * (np.log(np.pi) - np.real(digamma(z)))


def Phi_Fejer_heat(xi, B, t):
    xi = np.asarray(xi)
    result = np.zeros_like(xi, dtype=float)
    mask = np.abs(xi) <= B
    if np.any(mask):
        fejer = np.maximum(0, 1 - np.abs(xi[mask]) / B)
        heat = np.exp(-4 * np.pi**2 * t * xi[mask]**2)
        result[mask] = fejer * heat
    return result


def sieve_primes(n_max):
    if n_max < 2:
        return []
    sieve = [True] * (n_max + 1)
    sieve[0] = sieve[1] = False
    for x in range(2, int(n_max**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n_max + 1, x):
                sieve[i] = False
    return [x for x in range(2, n_max + 1) if sieve[x]]


def compute_Ak_fast(k, B, t, xi_grid, a_vals, phi_vals, dxi):
    """Быстрое вычисление A_k через предвычисленные значения."""
    integrand = a_vals * phi_vals * np.cos(k * xi_grid)
    return np.trapezoid(integrand, dx=dxi)


def build_H_and_V_optimized(K, M, t_heat):
    """
    Оптимизированная сборка H и V.
    Возвращает A², V и метаданные.
    """
    B = K

    # Предвычисляем a*(ξ) и Φ(ξ) на сетке
    N_grid = 2000
    xi_grid = np.linspace(-B, B, N_grid)
    dxi = xi_grid[1] - xi_grid[0]
    a_vals = a_star(xi_grid)
    phi_vals = Phi_Fejer_heat(xi_grid, B, t_heat)

    # T_A (Toeplitz)
    A_coeffs = [compute_Ak_fast(k, B, t_heat, xi_grid, a_vals, phi_vals, dxi) for k in range(M)]
    T_A = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            T_A[i, j] = A_coeffs[abs(i - j)]

    # Простые и близнецы
    n_max = int(np.exp(2 * np.pi * K)) + 1
    primes = sieve_primes(min(n_max, 10_000_000))  # Ограничиваем для памяти

    primes_in_compact = []
    for p in primes:
        xi_p = np.log(p) / (2 * np.pi)
        if abs(xi_p) <= K:
            primes_in_compact.append(p)

    # T_P
    T_P = np.zeros((M, M))
    for p in primes_in_compact:
        xi_p = np.log(p) / (2 * np.pi)
        w_p = 2 * np.log(p) / np.sqrt(p)
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t_heat)[0]
        cos_vec = np.array([np.cos(k * xi_p) for k in range(M)])
        T_P += w_p * phi_p * np.outer(cos_vec, cos_vec)

    H = T_A - T_P

    # Близнецы
    prime_set = set(primes_in_compact)
    twins = [(p, p+2) for p in primes_in_compact if p+2 in prime_set]

    # A² = H⊗I + I⊗H
    I = np.eye(M)
    A2 = np.kron(H, I) + np.kron(I, H)

    # V для близнецов
    V = np.zeros((M * M, M * M))
    for p, q in twins:
        xi_p = np.log(p) / (2 * np.pi)
        xi_q = np.log(q) / (2 * np.pi)
        w_p = 2 * np.log(p) / np.sqrt(p)
        w_q = 2 * np.log(q) / np.sqrt(q)
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t_heat)[0]
        phi_q = Phi_Fejer_heat(np.array([xi_q]), B, t_heat)[0]
        v_p = np.array([np.cos(k * xi_p) for k in range(M)])
        v_q = np.array([np.cos(k * xi_q) for k in range(M)])
        v_pq = np.kron(v_p, v_q)
        V += w_p * w_q * phi_p * phi_q * np.outer(v_pq, v_pq)

    return {
        'H': H,
        'A2': A2,
        'V': V,
        'n_primes': len(primes_in_compact),
        'n_twins': len(twins),
        'twins': twins[:10],  # первые 10 для отображения
    }


def compute_alpha(A2, V, tau_range):
    """Вычисляет показатель α из heat trace."""
    traces = []
    for tau in tau_range:
        heat = expm(-tau * A2)
        tr = np.trace(heat @ V)
        traces.append(abs(tr))

    # Fit на хвосте
    mask = np.array(tau_range) >= 1.0
    if np.sum(mask) < 2:
        mask = np.ones(len(tau_range), dtype=bool)

    log_tau = np.log(np.array(tau_range)[mask])
    log_tr = np.log(np.array(traces)[mask] + 1e-20)

    slope, intercept = np.polyfit(log_tau, log_tr, 1)
    alpha = -slope

    return alpha, traces


def run_alpha_scaling(K_values, M=15, t_heat=3.0):
    """Анализ α(K) для разных K."""
    console.print(Panel.fit(
        "[bold cyan]Q3 ALPHA SCALING ANALYSIS[/bold cyan]\n"
        "[dim]Проверка: α(K) → ? при K → ∞[/dim]",
        box=box.DOUBLE
    ))

    tau_range = [0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0]

    results = []

    for K in K_values:
        console.print(f"\n[bold yellow]═══ K = {K} ═══[/bold yellow]")

        start = time.time()

        try:
            data = build_H_and_V_optimized(K, M, t_heat)
        except MemoryError:
            console.print(f"[red]MemoryError при K={K}. Пропускаем.[/red]")
            continue

        build_time = time.time() - start

        console.print(f"  Простых: {data['n_primes']}, Близнецов: {data['n_twins']}")
        console.print(f"  Матрица A²: {data['A2'].shape}, время сборки: {build_time:.1f}s")

        if data['n_twins'] < 2:
            console.print(f"  [red]Мало близнецов, пропускаем[/red]")
            continue

        # Вычисляем α
        start = time.time()
        alpha, traces = compute_alpha(data['A2'], data['V'], tau_range)
        compute_time = time.time() - start

        min_ev_H = np.min(np.linalg.eigvalsh(data['H']))

        console.print(f"  min λ(H) = {min_ev_H:.2e}")
        console.print(f"  [green]α = {alpha:.3f}[/green], время: {compute_time:.1f}s")

        results.append({
            'K': K,
            'n_primes': data['n_primes'],
            'n_twins': data['n_twins'],
            'alpha': alpha,
            'min_ev_H': min_ev_H,
            'traces': traces,
        })

    # Сводная таблица
    console.print("\n")
    table = Table(title="α(K) SCALING RESULTS", box=box.DOUBLE)
    table.add_column("K", style="cyan")
    table.add_column("Primes", style="yellow")
    table.add_column("Twins", style="yellow")
    table.add_column("α", style="green")
    table.add_column("min λ(H)", style="magenta")

    for r in results:
        table.add_row(
            f"{r['K']:.1f}",
            str(r['n_primes']),
            str(r['n_twins']),
            f"{r['alpha']:.3f}",
            f"{r['min_ev_H']:.2e}"
        )

    console.print(table)

    # Анализ тренда α(K)
    if len(results) >= 3:
        Ks = np.array([r['K'] for r in results])
        alphas = np.array([r['alpha'] for r in results])

        # Линейный fit
        slope, intercept = np.polyfit(Ks, alphas, 1)

        console.print("\n")
        if abs(slope) < 0.1:
            console.print(Panel.fit(
                f"[bold green]α СТАБИЛЕН![/bold green]\n\n"
                f"α ≈ {np.mean(alphas):.2f} ± {np.std(alphas):.2f}\n"
                f"Тренд: {slope:+.3f} per K unit\n\n"
                f"[green]→ Сильный аргумент за бесконечность близнецов![/green]",
                box=box.DOUBLE,
                border_style="green"
            ))
        elif slope > 0:
            console.print(Panel.fit(
                f"[bold yellow]α РАСТЁТ с K[/bold yellow]\n\n"
                f"Тренд: {slope:+.3f} per K unit\n\n"
                f"[yellow]Нужно больше данных при большем K[/yellow]",
                box=box.DOUBLE,
                border_style="yellow"
            ))
        else:
            console.print(Panel.fit(
                f"[bold green]α УМЕНЬШАЕТСЯ с K[/bold green]\n\n"
                f"Тренд: {slope:+.3f} per K unit\n\n"
                f"[green]→ Ещё сильнее за бесконечность близнецов![/green]",
                box=box.DOUBLE,
                border_style="green"
            ))

    # График
    if len(results) >= 2:
        fig, axes = plt.subplots(1, 2, figsize=(12, 5))

        # α vs K
        ax1 = axes[0]
        Ks = [r['K'] for r in results]
        alphas = [r['alpha'] for r in results]
        ax1.plot(Ks, alphas, 'o-', markersize=10, linewidth=2, color='steelblue')
        ax1.axhline(np.mean(alphas), color='red', linestyle='--', label=f'Mean α = {np.mean(alphas):.2f}')
        ax1.set_xlabel('K (compact size)', fontsize=12)
        ax1.set_ylabel('α (power law exponent)', fontsize=12)
        ax1.set_title('α(K) Scaling', fontsize=14)
        ax1.legend()
        ax1.grid(True, alpha=0.3)

        # Heat traces для разных K
        ax2 = axes[1]
        for r in results:
            ax2.semilogy(tau_range, r['traces'], 'o-', label=f"K={r['K']}")
        ax2.set_xlabel('τ', fontsize=12)
        ax2.set_ylabel('|Tr(e^{-τA²} V)|', fontsize=12)
        ax2.set_title('Heat Trace for Different K', fontsize=14)
        ax2.legend()
        ax2.grid(True, alpha=0.3)

        plt.tight_layout()
        plt.savefig('alpha_scaling.png', dpi=150, bbox_inches='tight')
        console.print("[green]Plot saved: alpha_scaling.png[/green]")
        plt.show()

    return results


if __name__ == "__main__":
    # Тестируем K = 0.5, 0.7, 1.0, 1.2, 1.5
    # Для K > 1.5 нужна большая память
    K_values = [0.5, 0.7, 1.0, 1.2, 1.5]

    run_alpha_scaling(K_values, M=15, t_heat=3.0)
