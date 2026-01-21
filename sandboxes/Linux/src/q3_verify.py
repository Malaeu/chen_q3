#!/usr/bin/env python3
"""
Q3 Verification: H = T_A - T_P >= 0
===================================
Независимая проверка критерия Вейля для RH.

Ключевая формула для T_P:
    T_P = Σ_p w(p) × Φ(ξ_p) × |cos_p⟩⟨cos_p|

Важно: Φ(ξ_p) включено! Это убивает вклад далёких простых.
"""

import numpy as np
from scipy.special import digamma
from scipy.integrate import quad
import matplotlib.pyplot as plt
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def a_star(xi):
    """
    Архимедова плотность.
    a*(ξ) = 2π(log π - Re ψ(1/4 + iπξ))
    """
    z = 0.25 + 1j * np.pi * xi
    return 2 * np.pi * (np.log(np.pi) - np.real(digamma(z)))


def Phi_Fejer_heat(xi, B, t):
    """
    Тест-функция Fejér × heat.
    Φ_{B,t}(ξ) = (1 - |ξ|/B)_+ × exp(-4π²t ξ²)
    """
    xi = np.asarray(xi)
    result = np.zeros_like(xi, dtype=float)
    mask = np.abs(xi) <= B
    if np.any(mask):
        fejer = np.maximum(0, 1 - np.abs(xi[mask]) / B)
        heat = np.exp(-4 * np.pi**2 * t * xi[mask]**2)
        result[mask] = fejer * heat
    return result


def sieve_primes(n_max):
    """Решето Эратосфена."""
    if n_max < 2:
        return []
    sieve = [True] * (n_max + 1)
    sieve[0] = sieve[1] = False
    for x in range(2, int(n_max**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n_max + 1, x):
                sieve[i] = False
    return [x for x in range(2, n_max + 1) if sieve[x]]


def compute_Ak(k, B, t):
    """
    Коэффициент Фурье для Toeplitz-матрицы.
    A_k = ∫ a*(ξ) Φ_{B,t}(ξ) cos(kξ) dξ
    """
    def integrand(xi):
        phi_val = Phi_Fejer_heat(np.array([xi]), B, t)[0]
        return a_star(xi) * phi_val * np.cos(k * xi)

    result, _ = quad(integrand, -B, B, limit=100)
    return result


def build_H(K, M, t):
    """
    Строит гамильтониан H = T_A - T_P.

    КРИТИЧНО: T_P включает Φ(ξ_p) — значение тест-функции в точке простого!

    Параметры:
        K: компакт [-K, K]
        M: размер матрицы
        t: heat-параметр

    Возвращает:
        H: матрица M×M
        n_primes: число простых в компакте
    """
    B = K  # bandwidth = K

    # 1. Находим простые в компакте
    n_max = int(np.exp(2 * np.pi * K)) + 1
    primes = sieve_primes(n_max)

    nodes = []
    weights = []
    for p in primes:
        xi_p = np.log(p) / (2 * np.pi)
        if np.abs(xi_p) <= K:
            nodes.append(xi_p)
            weights.append(2 * np.log(p) / np.sqrt(p))  # 2Λ(p)/√p per ТЗ

    nodes = np.array(nodes)
    weights = np.array(weights)

    # 2. Строим T_A (Toeplitz)
    A_coeffs = [compute_Ak(k, B, t) for k in range(M)]
    T_A = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            T_A[i, j] = A_coeffs[abs(i - j)]

    # 3. Строим T_P (сумма rank-1) — ВКЛЮЧАЯ Φ(ξ_p)!
    T_P = np.zeros((M, M))
    for idx in range(len(nodes)):
        xi_p = nodes[idx]
        w_p = weights[idx]

        # КРИТИЧНО: значение тест-функции в точке простого!
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t)[0]

        # Вектор косинусов
        cos_vec = np.array([np.cos(k * xi_p) for k in range(M)])

        # Rank-1 update: T_P += w_p × φ(ξ_p) × |cos_vec⟩⟨cos_vec|
        T_P += w_p * phi_p * np.outer(cos_vec, cos_vec)

    # 4. Гамильтониан
    H = T_A - T_P

    return H, len(nodes), T_A, T_P


def main():
    console.print(Panel.fit("[bold cyan]Q3 VERIFICATION: H = T_A - T_P ≥ 0[/bold cyan]", box=box.DOUBLE))

    # Тест 1: Проверка a*(0)
    console.print("\n[bold]Тест 1: Проверка архимедовой плотности[/bold]")
    a0 = a_star(0)
    console.print(f"  a*(0) = {a0:.4f}")
    console.print(f"  Ожидается: ≈ 33.75")
    status = "✓ OK" if 33 < a0 < 35 else "✗ ОШИБКА"
    console.print(f"  Статус: {status}")

    # Тест 2: K = 0.5, t = 5.0
    console.print("\n[bold]Тест 2: K = 0.5, M = 30, t = 5.0[/bold]")
    H, n_primes, T_A, T_P = build_H(K=0.5, M=30, t=5.0)
    eigs = np.linalg.eigvalsh(H)
    min_ev = np.min(eigs)
    console.print(f"  Простых в компакте: {n_primes}")
    console.print(f"  Trace(T_A) = {np.trace(T_A):.4f}")
    console.print(f"  Trace(T_P) = {np.trace(T_P):.4f}")
    console.print(f"  min λ(H) = {min_ev:.2e}")
    status = "[green]✓ ДА[/green]" if min_ev >= -1e-9 else "[red]✗ НЕТ[/red]"
    console.print(f"  H ≥ 0: {status}")

    # Тест 3: K = 1.0, t = 5.0
    console.print("\n[bold]Тест 3: K = 1.0, M = 40, t = 5.0[/bold]")
    H, n_primes, T_A, T_P = build_H(K=1.0, M=40, t=5.0)
    eigs = np.linalg.eigvalsh(H)
    min_ev = np.min(eigs)
    console.print(f"  Простых в компакте: {n_primes}")
    console.print(f"  Trace(T_A) = {np.trace(T_A):.4f}")
    console.print(f"  Trace(T_P) = {np.trace(T_P):.4f}")
    console.print(f"  min λ(H) = {min_ev:.2e}")
    status = "[green]✓ ДА[/green]" if min_ev >= -1e-9 else "[red]✗ НЕТ[/red]"
    console.print(f"  H ≥ 0: {status}")

    # Тест 4: Сканирование по t
    console.print("\n[bold]Тест 4: Сканирование по t (K = 0.5)[/bold]")

    table = Table(title="min λ(H) vs t", box=box.ROUNDED)
    table.add_column("t", style="cyan")
    table.add_column("min λ(H)", style="yellow")
    table.add_column("H ≥ 0?", style="green")

    results = []
    for t in [0.5, 1.0, 1.5, 2.0, 3.0, 5.0]:
        H, _, _, _ = build_H(K=0.5, M=30, t=t)
        min_ev = np.min(np.linalg.eigvalsh(H))
        status = "✓" if min_ev >= -1e-9 else "✗"
        table.add_row(f"{t:.1f}", f"{min_ev:+.2e}", status)
        results.append((t, min_ev))

    console.print(table)

    # Итог
    console.print()
    console.print(
        Panel.fit(
            "[bold green]ИТОГ:[/bold green]\n\n"
            "Если min λ(H) ≈ 0 при t ≥ 2,\n"
            "это численное подтверждение критерия Вейля:\n\n"
            "    Q(Φ) ≥ 0  для тест-функций на компакте [-K, K]\n\n"
            "По критерию Вейля это согласуется с RH.",
            box=box.DOUBLE,
        )
    )

    return results


if __name__ == "__main__":
    main()
