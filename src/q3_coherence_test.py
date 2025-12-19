#!/usr/bin/env python3
"""
Q3 COHERENCE TEST: Резонанс Вейля
=================================

ГИПОТЕЗА: Векторы близнецов коллинеарны → когерентное сложение.

Тесты:
1. ||Ψ||² где Ψ = Σ w_i v_i (взвешенная сумма)
2. Как ||Ψ||² масштабируется с K?
   - Если ~ N² → когерентность (лазер)
   - Если ~ N → random walk (лампочка)
3. ⟨Ψ|H|Ψ⟩ — энергия когерентного состояния
"""

import numpy as np
from scipy.special import digamma
from scipy.stats import linregress
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

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
    n_max = min(n_max, 50_000_000)
    if n_max < 2:
        return []
    sieve = [True] * (n_max + 1)
    sieve[0] = sieve[1] = False
    for x in range(2, int(n_max**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n_max + 1, x):
                sieve[i] = False
    return [x for x in range(2, n_max + 1) if sieve[x]]


def coherence_test(K, M=18, t_heat=3.0):
    """Тест когерентности для заданного K."""
    B = K

    # Build H
    N_grid = 2000
    xi_grid = np.linspace(-B, B, N_grid)
    dxi = xi_grid[1] - xi_grid[0]
    a_vals = a_star(xi_grid)
    phi_vals = Phi_Fejer_heat(xi_grid, B, t_heat)

    A_coeffs = [np.trapezoid(a_vals * phi_vals * np.cos(k * xi_grid), dx=dxi) for k in range(M)]
    T_A = np.array([[A_coeffs[abs(i-j)] for j in range(M)] for i in range(M)])

    n_max = int(np.exp(2 * np.pi * K)) + 1
    primes = sieve_primes(n_max)
    primes_in = [p for p in primes if abs(np.log(p)/(2*np.pi)) <= K]

    T_P = np.zeros((M, M))
    for p in primes_in:
        xi_p = np.log(p) / (2 * np.pi)
        w_p = 2 * np.log(p) / np.sqrt(p)
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t_heat)[0]
        cos_vec = np.array([np.cos(k * xi_p) for k in range(M)])
        T_P += w_p * phi_p * np.outer(cos_vec, cos_vec)

    H = T_A - T_P

    # Близнецы
    prime_set = set(primes_in)
    twins = [(p, p+2) for p in primes_in if p+2 in prime_set]
    n_twins = len(twins)

    if n_twins < 2:
        return None

    # Строим когерентное состояние Ψ = Σ w_i (v_p ⊗ v_q)
    # В двухчастичном пространстве M²
    Psi = np.zeros(M * M)

    # Также строим невзвешенную сумму для сравнения
    Psi_unweighted = np.zeros(M * M)

    # Сумма весов
    total_weight = 0

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

        weight = np.sqrt(w_p * w_q * phi_p * phi_q)
        Psi += weight * v_pq
        Psi_unweighted += v_pq
        total_weight += weight

    # Нормы
    norm_Psi_sq = np.dot(Psi, Psi)
    norm_unweighted_sq = np.dot(Psi_unweighted, Psi_unweighted)

    # Энергия ⟨Ψ|A²|Ψ⟩ где A² = H⊗I + I⊗H
    I = np.eye(M)
    A2 = np.kron(H, I) + np.kron(I, H)

    energy = np.dot(Psi, A2 @ Psi) / norm_Psi_sq

    # Также проверим проекцию на нулевое пространство A²
    eigs_A2, U = np.linalg.eigh(A2)
    mask_null = np.abs(eigs_A2) < 1e-8

    # Проекция Ψ на нулевое пространство
    Psi_proj = U.T @ Psi
    proj_null = np.sum(Psi_proj[mask_null]**2) / norm_Psi_sq

    return {
        'K': K,
        'n_twins': n_twins,
        'norm_Psi_sq': norm_Psi_sq,
        'norm_unweighted_sq': norm_unweighted_sq,
        'total_weight': total_weight,
        'energy': energy,
        'proj_null': proj_null,
    }


def main():
    console.print(Panel.fit(
        "[bold magenta]Q3 COHERENCE TEST[/bold magenta]\n"
        "[dim]Резонанс Вейля: когерентность vs random walk[/dim]",
        box=box.DOUBLE
    ))

    M = 18
    t_heat = 3.0
    K_values = [0.5, 0.7, 1.0, 1.2, 1.5, 1.8, 2.0, 2.3]

    results = []
    for K in K_values:
        res = coherence_test(K, M, t_heat)
        if res:
            results.append(res)
            console.print(f"K={K}: twins={res['n_twins']}, ||Ψ||²={res['norm_Psi_sq']:.4e}, E={res['energy']:.4e}")

    if len(results) < 3:
        console.print("[red]Недостаточно данных[/red]")
        return

    # Таблица результатов
    console.print("\n")
    table = Table(title="COHERENCE TEST RESULTS", box=box.DOUBLE)
    table.add_column("K", style="cyan")
    table.add_column("Twins", style="yellow")
    table.add_column("||Ψ||²", style="green")
    table.add_column("Σw", style="blue")
    table.add_column("⟨E⟩", style="magenta")
    table.add_column("Proj(null)", style="red")

    for r in results:
        table.add_row(
            f"{r['K']:.1f}",
            f"{r['n_twins']}",
            f"{r['norm_Psi_sq']:.4e}",
            f"{r['total_weight']:.4e}",
            f"{r['energy']:.4e}",
            f"{r['proj_null']:.4f}"
        )

    console.print(table)

    # Анализ скейлинга
    console.print("\n[bold cyan]АНАЛИЗ СКЕЙЛИНГА[/bold cyan]\n")

    twins = np.array([r['n_twins'] for r in results])
    norms = np.array([r['norm_Psi_sq'] for r in results])
    weights = np.array([r['total_weight'] for r in results])

    # ||Ψ||² vs N
    log_twins = np.log(twins)
    log_norms = np.log(norms)

    slope, intercept, r, p, se = linregress(log_twins, log_norms)
    console.print(f"||Ψ||² ~ N^γ:")
    console.print(f"  γ = {slope:.3f} ± {se:.3f}")
    console.print(f"  R² = {r**2:.4f}")
    console.print()

    if slope > 1.5:
        console.print("[bold green]γ > 1.5 → КОГЕРЕНТНОСТЬ! Лазер![/bold green]")
    elif slope > 0.8:
        console.print("[yellow]γ ≈ 1 → Линейный рост (Random Walk)[/yellow]")
    else:
        console.print("[red]γ < 1 → Насыщение (субдиффузия)[/red]")

    console.print()

    # Σw vs N
    log_weights = np.log(weights)
    slope_w, _, r_w, _, se_w = linregress(log_twins, log_weights)
    console.print(f"Σw ~ N^δ:")
    console.print(f"  δ = {slope_w:.3f} ± {se_w:.3f}")
    console.print(f"  R² = {r_w**2:.4f}")
    console.print()

    # Энергия
    energies = np.array([r['energy'] for r in results])
    console.print(f"Энергия ⟨Ψ|A²|Ψ⟩/||Ψ||²:")
    console.print(f"  Диапазон: {np.min(energies):.4e} — {np.max(energies):.4e}")
    console.print(f"  Тренд с K: {'↓' if energies[-1] < energies[0] else '↑'}")
    console.print()

    # Проекция на нулевое пространство
    projs = np.array([r['proj_null'] for r in results])
    console.print(f"Проекция на null(A²):")
    console.print(f"  Диапазон: {np.min(projs):.4f} — {np.max(projs):.4f}")
    console.print()

    # Финальный вердикт
    console.print("\n")
    if slope > 1.5:
        verdict = (
            "[bold green]КОГЕРЕНТНОСТЬ ОБНАРУЖЕНА![/bold green]\n\n"
            f"||Ψ||² ~ N^{slope:.2f} → сверхлинейный рост\n"
            "Близнецы складываются конструктивно!\n\n"
            "[green]Это СИЛЬНЫЙ аргумент за бесконечность близнецов.[/green]"
        )
        color = "green"
    elif slope > 0.8:
        verdict = (
            "[yellow]RANDOM WALK[/yellow]\n\n"
            f"||Ψ||² ~ N^{slope:.2f} → линейный рост\n"
            "Близнецы складываются случайно.\n\n"
            "[yellow]Нет когерентности, но и нет затухания.[/yellow]"
        )
        color = "yellow"
    else:
        verdict = (
            "[red]НАСЫЩЕНИЕ[/red]\n\n"
            f"||Ψ||² ~ N^{slope:.2f} → субдиффузия\n"
            "Близнецы не накапливаются.\n\n"
            "[red]Требуется другой подход.[/red]"
        )
        color = "red"

    console.print(Panel.fit(verdict, box=box.DOUBLE, border_style=color))

    return results


if __name__ == "__main__":
    main()
