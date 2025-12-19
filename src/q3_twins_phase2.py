#!/usr/bin/env python3
"""
Q3 Phase 2: Twin Primes via Two-Particle Operator
==================================================

Двухчастичный гамильтониан для близнецов:
    A^(2) = A ⊗ I + I ⊗ A + V_int

где V_h ~ δ(ξ_2 - ξ_1 - h) — член взаимодействия.

Критерий бесконечности близнецов:
    Tr(e^{-tA^(2)} V_h) ↛ 0  при t → ∞
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

console = Console()


# ============================================================
# PHASE 1 FUNCTIONS (копируем из q3_verify.py)
# ============================================================

def a_star(xi):
    """Архимедова плотность a*(ξ) = 2π(log π - Re ψ(1/4 + iπξ))"""
    z = 0.25 + 1j * np.pi * xi
    return 2 * np.pi * (np.log(np.pi) - np.real(digamma(z)))


def Phi_Fejer_heat(xi, B, t):
    """Тест-функция Φ_{B,t}(ξ) = (1 - |ξ|/B)_+ × exp(-4π²t ξ²)"""
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
    """Коэффициент Фурье A_k = ∫ a*(ξ) Φ(ξ) cos(kξ) dξ"""
    def integrand(xi):
        phi_val = Phi_Fejer_heat(np.array([xi]), B, t)[0]
        return a_star(xi) * phi_val * np.cos(k * xi)
    result, _ = quad(integrand, -B, B, limit=100)
    return result


def build_single_particle_H(K, M, t):
    """
    Строит одночастичный H = T_A - T_P из Фазы 1.
    Возвращает H и список простых в компакте.
    """
    B = K
    n_max = int(np.exp(2 * np.pi * K)) + 1
    primes = sieve_primes(n_max)

    # Простые в компакте
    primes_in_compact = []
    for p in primes:
        xi_p = np.log(p) / (2 * np.pi)
        if np.abs(xi_p) <= K:
            primes_in_compact.append(p)

    # T_A (Toeplitz)
    A_coeffs = [compute_Ak(k, B, t) for k in range(M)]
    T_A = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            T_A[i, j] = A_coeffs[abs(i - j)]

    # T_P
    T_P = np.zeros((M, M))
    for p in primes_in_compact:
        xi_p = np.log(p) / (2 * np.pi)
        w_p = 2 * np.log(p) / np.sqrt(p)
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t)[0]
        cos_vec = np.array([np.cos(k * xi_p) for k in range(M)])
        T_P += w_p * phi_p * np.outer(cos_vec, cos_vec)

    H = T_A - T_P
    return H, primes_in_compact


# ============================================================
# PHASE 2: TWO-PARTICLE OPERATOR
# ============================================================

def build_two_particle_A(H1):
    """
    Строит двухчастичный оператор:
    A^(2) = H ⊗ I + I ⊗ H

    Размерность: M² × M²
    """
    M = H1.shape[0]
    I = np.eye(M)

    # Тензорные произведения
    A2 = np.kron(H1, I) + np.kron(I, H1)

    return A2


def find_twin_primes(primes):
    """Находит пары близнецов (p, p+2) в списке простых."""
    prime_set = set(primes)
    twins = []
    for p in primes:
        if p + 2 in prime_set:
            twins.append((p, p + 2))
    return twins


def build_twin_interaction_V(M, K, t, gap=2):
    """
    Строит оператор взаимодействия V_h для близнецов.

    V проецирует на состояния где две частицы находятся
    на позициях простых-близнецов (p, p+gap).

    В базисе |k,l⟩ = e_k ⊗ e_l:
    V = Σ_{twins} w(p)w(q) Φ(ξ_p)Φ(ξ_q) |v_p ⊗ v_q⟩⟨v_p ⊗ v_q|
    """
    B = K
    n_max = int(np.exp(2 * np.pi * K)) + 1
    primes = sieve_primes(n_max)

    # Фильтруем по компакту
    primes_in_compact = []
    for p in primes:
        xi_p = np.log(p) / (2 * np.pi)
        if np.abs(xi_p) <= K:
            primes_in_compact.append(p)

    # Находим близнецов
    twins = find_twin_primes(primes_in_compact)
    console.print(f"[yellow]Близнецов в компакте [-{K}, {K}]: {len(twins)}[/yellow]")

    # Строим V как сумму проекторов на пары близнецов
    V = np.zeros((M * M, M * M))

    for p, q in twins:  # q = p + gap
        xi_p = np.log(p) / (2 * np.pi)
        xi_q = np.log(q) / (2 * np.pi)

        # Веса
        w_p = 2 * np.log(p) / np.sqrt(p)
        w_q = 2 * np.log(q) / np.sqrt(q)

        # Значения тест-функции
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t)[0]
        phi_q = Phi_Fejer_heat(np.array([xi_q]), B, t)[0]

        # Косинусные векторы
        v_p = np.array([np.cos(k * xi_p) for k in range(M)])
        v_q = np.array([np.cos(k * xi_q) for k in range(M)])

        # Тензорный вектор |v_p ⊗ v_q⟩
        v_pq = np.kron(v_p, v_q)

        # Rank-1 вклад
        weight = w_p * w_q * phi_p * phi_q
        V += weight * np.outer(v_pq, v_pq)

    return V, twins


def compute_heat_trace(A2, V, t_values):
    """
    Вычисляет Tr(e^{-tA^(2)} V) для разных t.

    Это ключевая величина: если не затухает при t→∞,
    то близнецов бесконечно много.
    """
    results = []

    for t in t_values:
        # e^{-tA^(2)}
        heat_kernel = expm(-t * A2)

        # Tr(e^{-tA} V) = Tr(V e^{-tA})
        trace_val = np.trace(heat_kernel @ V)

        results.append((t, trace_val))
        console.print(f"[dim]t = {t:.2f}: Tr(e^{{-tA²}} V) = {trace_val:.6e}[/dim]")

    return results


def run_phase2(K=0.5, M=15, t_heat=3.0, plot=True):
    """
    Запуск Фазы 2: Близнецы.

    ВНИМАНИЕ: M должен быть небольшим (10-20), т.к.
    двухчастичная матрица имеет размер M² × M²!
    """
    console.print(Panel.fit(
        "[bold magenta]Q3 PHASE 2: TWIN PRIMES[/bold magenta]\n"
        "[dim]A^(2) = A ⊗ I + I ⊗ A + V_twins[/dim]",
        box=box.DOUBLE
    ))

    console.print(f"\n[cyan]Параметры: K={K}, M={M}, t_heat={t_heat}[/cyan]")
    console.print(f"[cyan]Размер двухчастичной матрицы: {M}² × {M}² = {M**2} × {M**2}[/cyan]")

    # 1. Строим одночастичный H
    console.print("\n[bold]1. Строим одночастичный H = T_A - T_P...[/bold]")
    H1, primes = build_single_particle_H(K, M, t_heat)

    min_ev_H1 = np.min(np.linalg.eigvalsh(H1))
    console.print(f"   Простых в компакте: {len(primes)}")
    console.print(f"   min λ(H₁) = {min_ev_H1:.2e}")

    # 2. Строим двухчастичный A^(2)
    console.print("\n[bold]2. Строим A^(2) = H ⊗ I + I ⊗ H...[/bold]")
    A2 = build_two_particle_A(H1)
    console.print(f"   Размер A²: {A2.shape}")

    # 3. Строим V для близнецов
    console.print("\n[bold]3. Строим V_twins (оператор взаимодействия)...[/bold]")
    V, twins = build_twin_interaction_V(M, K, t_heat, gap=2)

    if len(twins) == 0:
        console.print("[red]Нет близнецов в компакте! Увеличь K.[/red]")
        return None

    console.print(f"   Близнецы: {twins[:5]}{'...' if len(twins) > 5 else ''}")
    console.print(f"   ||V||_F = {np.linalg.norm(V, 'fro'):.4f}")

    # 4. Вычисляем heat trace
    console.print("\n[bold]4. Вычисляем Tr(e^{-τA²} V) для разных τ...[/bold]")
    tau_values = [0.01, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0]
    traces = compute_heat_trace(A2, V, tau_values)

    # 5. Результаты
    console.print("\n")
    table = Table(title="Heat Trace для близнецов", box=box.DOUBLE)
    table.add_column("τ", style="cyan")
    table.add_column("Tr(e^{-τA²} V)", style="yellow")
    table.add_column("Затухание?", style="green")

    for i, (tau, tr) in enumerate(traces):
        decay = "—"
        if i > 0:
            ratio = abs(tr / traces[i-1][1]) if traces[i-1][1] != 0 else 0
            if ratio < 0.5:
                decay = "↓↓ быстро"
            elif ratio < 0.9:
                decay = "↓ медленно"
            else:
                decay = "≈ стабильно"
        table.add_row(f"{tau:.2f}", f"{tr:.6e}", decay)

    console.print(table)

    # 6. Вердикт
    first_trace = traces[0][1]
    last_trace = traces[-1][1]
    ratio = abs(last_trace / first_trace) if first_trace != 0 else 0

    console.print("\n")
    if ratio > 0.1:
        console.print(Panel.fit(
            f"[bold green]Tr(e^{{-τA²}} V) НЕ ЗАТУХАЕТ![/bold green]\n\n"
            f"Отношение последний/первый: {ratio:.2%}\n\n"
            f"[green]→ Это согласуется с гипотезой о бесконечности близнецов![/green]",
            box=box.DOUBLE,
            border_style="green"
        ))
    else:
        console.print(Panel.fit(
            f"[bold yellow]Tr(e^{{-τA²}} V) затухает[/bold yellow]\n\n"
            f"Отношение: {ratio:.2%}\n\n"
            f"[yellow]Нужно больше данных (увеличить K, M)[/yellow]",
            box=box.DOUBLE,
            border_style="yellow"
        ))

    if plot:
        fig, axes = plt.subplots(1, 2, figsize=(12, 5))

        # 1. Heat trace vs τ
        ax1 = axes[0]
        taus = [t for t, _ in traces]
        vals = [v for _, v in traces]
        ax1.semilogy(taus, np.abs(vals), 'o-', markersize=8, linewidth=2)
        ax1.set_xlabel('τ')
        ax1.set_ylabel('|Tr(e^{-τA²} V)|')
        ax1.set_title('Heat Trace для близнецов')
        ax1.grid(True, alpha=0.3)

        # 2. Спектр A^(2)
        ax2 = axes[1]
        eigs_A2 = np.linalg.eigvalsh(A2)
        ax2.hist(eigs_A2, bins=30, alpha=0.7, color='steelblue', edgecolor='black')
        ax2.axvline(0, color='red', linestyle='--', linewidth=2)
        ax2.set_xlabel('Eigenvalue')
        ax2.set_ylabel('Count')
        ax2.set_title(f'Спектр A² = H⊗I + I⊗H\nmin = {np.min(eigs_A2):.4f}')
        ax2.grid(True, alpha=0.3)

        plt.tight_layout()
        plt.savefig('twins_phase2.png', dpi=150, bbox_inches='tight')
        console.print("[green]Plot saved: twins_phase2.png[/green]")
        plt.show()

    return {
        'H1': H1,
        'A2': A2,
        'V': V,
        'twins': twins,
        'traces': traces,
    }


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Q3 Phase 2: Twin Primes")
    parser.add_argument("-K", type=float, default=0.5, help="Compact size")
    parser.add_argument("-M", type=int, default=15, help="Matrix size (keep small!)")
    parser.add_argument("-t", type=float, default=3.0, help="Heat parameter")
    parser.add_argument("--no-plot", action="store_true", help="Disable plots")

    args = parser.parse_args()

    run_phase2(K=args.K, M=args.M, t_heat=args.t, plot=not args.no_plot)
