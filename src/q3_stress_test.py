#!/usr/bin/env python3
"""
Q3 STRESS TEST: K=2.0, K=2.5
============================
Финальный рывок: проверка стабильности α при большом K.
"""

import numpy as np
from scipy.special import digamma
from scipy.linalg import expm
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
    """Решето Эратосфена с ограничением памяти."""
    n_max = min(n_max, 50_000_000)  # Лимит 50M
    if n_max < 2:
        return []
    sieve = [True] * (n_max + 1)
    sieve[0] = sieve[1] = False
    for x in range(2, int(n_max**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n_max + 1, x):
                sieve[i] = False
    return [x for x in range(2, n_max + 1) if sieve[x]]


def stress_test(K, M, t_heat, tau_range):
    """Полный стресс-тест для заданного K."""
    console.print(f"\n[bold magenta]{'='*50}[/bold magenta]")
    console.print(f"[bold magenta]STRESS TEST: K = {K}, M = {M}[/bold magenta]")
    console.print(f"[bold magenta]{'='*50}[/bold magenta]")

    B = K
    start_total = time.time()

    # 1. Предвычисляем a*(ξ) и Φ(ξ)
    console.print("[cyan]1. Предвычисление сетки...[/cyan]")
    N_grid = 3000
    xi_grid = np.linspace(-B, B, N_grid)
    dxi = xi_grid[1] - xi_grid[0]
    a_vals = a_star(xi_grid)
    phi_vals = Phi_Fejer_heat(xi_grid, B, t_heat)

    # 2. T_A (Toeplitz)
    console.print("[cyan]2. Вычисление T_A...[/cyan]")
    A_coeffs = []
    for k in range(M):
        integrand = a_vals * phi_vals * np.cos(k * xi_grid)
        A_coeffs.append(np.trapezoid(integrand, dx=dxi))

    T_A = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            T_A[i, j] = A_coeffs[abs(i - j)]

    # 3. Простые
    console.print("[cyan]3. Генерация простых...[/cyan]")
    n_max = int(np.exp(2 * np.pi * K)) + 1
    console.print(f"   [dim]n_max = {n_max:,}[/dim]")

    primes = sieve_primes(n_max)
    console.print(f"   [dim]Всего простых: {len(primes):,}[/dim]")

    # Фильтруем по компакту
    primes_in_compact = []
    for p in primes:
        xi_p = np.log(p) / (2 * np.pi)
        if abs(xi_p) <= K:
            primes_in_compact.append(p)

    console.print(f"   [yellow]В компакте: {len(primes_in_compact):,}[/yellow]")

    # Близнецы
    prime_set = set(primes_in_compact)
    twins = [(p, p+2) for p in primes_in_compact if p+2 in prime_set]
    console.print(f"   [yellow]Близнецов: {len(twins):,}[/yellow]")

    if len(twins) < 3:
        console.print("[red]Слишком мало близнецов![/red]")
        return None

    # 4. T_P
    console.print("[cyan]4. Вычисление T_P...[/cyan]")
    T_P = np.zeros((M, M))
    for p in primes_in_compact:
        xi_p = np.log(p) / (2 * np.pi)
        w_p = 2 * np.log(p) / np.sqrt(p)
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t_heat)[0]
        cos_vec = np.array([np.cos(k * xi_p) for k in range(M)])
        T_P += w_p * phi_p * np.outer(cos_vec, cos_vec)

    H = T_A - T_P
    min_ev_H = np.min(np.linalg.eigvalsh(H))
    console.print(f"   [green]min λ(H) = {min_ev_H:.2e}[/green]")

    # 5. A² = H⊗I + I⊗H
    console.print("[cyan]5. Построение A² (тензор)...[/cyan]")
    I = np.eye(M)
    A2 = np.kron(H, I) + np.kron(I, H)
    console.print(f"   [dim]Размер A²: {A2.shape}[/dim]")

    # 6. V для близнецов
    console.print("[cyan]6. Построение V (близнецы)...[/cyan]")
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

    # 7. Heat trace
    console.print("[cyan]7. Вычисление heat trace...[/cyan]")
    traces = []
    for tau in tau_range:
        heat = expm(-tau * A2)
        tr = abs(np.trace(heat @ V))
        traces.append(tr)
        console.print(f"   [dim]τ = {tau:5.2f}: Tr = {tr:.4e}[/dim]")

    # 8. Fit α
    console.print("[cyan]8. Fitting α...[/cyan]")

    # На всём диапазоне
    log_tau = np.log(tau_range)
    log_tr = np.log(np.array(traces) + 1e-30)
    slope_all, intercept_all = np.polyfit(log_tau, log_tr, 1)
    alpha_all = -slope_all

    # R² для степенного
    pred = slope_all * log_tau + intercept_all
    ss_res = np.sum((log_tr - pred)**2)
    ss_tot = np.sum((log_tr - np.mean(log_tr))**2)
    r2_power = 1 - ss_res / ss_tot

    # На хвосте (τ ≥ 1)
    mask = np.array(tau_range) >= 1.0
    if np.sum(mask) >= 2:
        slope_tail, _ = np.polyfit(log_tau[mask], log_tr[mask], 1)
        alpha_tail = -slope_tail
    else:
        alpha_tail = alpha_all

    total_time = time.time() - start_total

    # Результаты
    console.print("\n")
    table = Table(title=f"RESULTS K={K}", box=box.DOUBLE)
    table.add_column("Metric", style="cyan")
    table.add_column("Value", style="yellow")

    table.add_row("Primes in compact", f"{len(primes_in_compact):,}")
    table.add_row("Twin pairs", f"{len(twins):,}")
    table.add_row("min λ(H)", f"{min_ev_H:.2e}")
    table.add_row("α (full range)", f"{alpha_all:.3f}")
    table.add_row("α (tail τ≥1)", f"{alpha_tail:.3f}")
    table.add_row("R² (power law)", f"{r2_power:.4f}")
    table.add_row("Total time", f"{total_time:.1f}s")

    console.print(table)

    return {
        'K': K,
        'n_primes': len(primes_in_compact),
        'n_twins': len(twins),
        'min_ev_H': min_ev_H,
        'alpha_all': alpha_all,
        'alpha_tail': alpha_tail,
        'r2': r2_power,
        'tau': tau_range,
        'traces': traces,
    }


def main():
    console.print(Panel.fit(
        "[bold red]Q3 STRESS TEST[/bold red]\n"
        "[dim]Финальная проверка: K = 2.0, 2.5[/dim]",
        box=box.DOUBLE,
        border_style="red"
    ))

    # Расширенный диапазон τ для лучшего fit
    tau_range = np.array([0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0])

    results = []

    # K = 1.5 (baseline)
    r = stress_test(K=1.5, M=18, t_heat=3.0, tau_range=tau_range)
    if r:
        results.append(r)

    # K = 2.0
    r = stress_test(K=2.0, M=18, t_heat=3.0, tau_range=tau_range)
    if r:
        results.append(r)

    # K = 2.5 (hardcore)
    r = stress_test(K=2.5, M=15, t_heat=3.0, tau_range=tau_range)
    if r:
        results.append(r)

    # Сводка
    console.print("\n")
    console.print(Panel.fit("[bold cyan]ФИНАЛЬНАЯ СВОДКА[/bold cyan]", box=box.DOUBLE))

    table = Table(title="α(K) STRESS TEST RESULTS", box=box.DOUBLE)
    table.add_column("K", style="cyan")
    table.add_column("Twins", style="yellow")
    table.add_column("α (full)", style="green")
    table.add_column("α (tail)", style="green")
    table.add_column("R²", style="magenta")

    for r in results:
        table.add_row(
            f"{r['K']:.1f}",
            f"{r['n_twins']:,}",
            f"{r['alpha_all']:.3f}",
            f"{r['alpha_tail']:.3f}",
            f"{r['r2']:.4f}"
        )

    console.print(table)

    # Тренд
    if len(results) >= 2:
        Ks = np.array([r['K'] for r in results])
        alphas = np.array([r['alpha_tail'] for r in results])

        slope, _ = np.polyfit(Ks, alphas, 1)

        console.print("\n")
        if slope < -0.05:
            verdict = "[bold green]α УМЕНЬШАЕТСЯ → ∞ близнецов![/bold green]"
            color = "green"
        elif abs(slope) < 0.05:
            verdict = "[bold green]α СТАБИЛЕН → ∞ близнецов![/bold green]"
            color = "green"
        else:
            verdict = "[bold yellow]α растёт — нужно больше данных[/bold yellow]"
            color = "yellow"

        console.print(Panel.fit(
            f"{verdict}\n\n"
            f"Тренд: dα/dK = {slope:+.3f}\n"
            f"α(K=1.5) = {results[0]['alpha_tail']:.3f}\n"
            f"α(K=2.5) = {results[-1]['alpha_tail']:.3f}",
            box=box.DOUBLE,
            border_style=color
        ))

    # График
    if len(results) >= 2:
        fig, axes = plt.subplots(1, 2, figsize=(14, 5))

        # Log-log plot
        ax1 = axes[0]
        for r in results:
            ax1.loglog(r['tau'], r['traces'], 'o-', label=f"K={r['K']}, α={r['alpha_tail']:.2f}")

        ax1.set_xlabel('τ', fontsize=12)
        ax1.set_ylabel('Tr(e^{-τA²} V)', fontsize=12)
        ax1.set_title('Log-Log Heat Trace (линейность = степенной закон)', fontsize=14)
        ax1.legend()
        ax1.grid(True, alpha=0.3, which='both')

        # α vs K
        ax2 = axes[1]
        Ks = [r['K'] for r in results]
        alphas_tail = [r['alpha_tail'] for r in results]
        ax2.plot(Ks, alphas_tail, 'o-', markersize=12, linewidth=3, color='steelblue')
        ax2.axhline(1.0, color='red', linestyle='--', alpha=0.5, label='α=1 (критическое)')
        ax2.set_xlabel('K (compact size)', fontsize=12)
        ax2.set_ylabel('α (power exponent)', fontsize=12)
        ax2.set_title('α(K) Scaling — Стресс-тест', fontsize=14)
        ax2.legend()
        ax2.grid(True, alpha=0.3)

        plt.tight_layout()
        plt.savefig('stress_test_results.png', dpi=150, bbox_inches='tight')
        console.print("[green]Plot saved: stress_test_results.png[/green]")
        plt.show()

    return results


if __name__ == "__main__":
    main()
