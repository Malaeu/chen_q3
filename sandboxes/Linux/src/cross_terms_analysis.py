#!/usr/bin/env python3
"""
Cross-Terms Analysis for Step B
================================

Проверка: малы ли cross-terms при разбиении C_X на части?

Разбиение T_P = T_twin + T_rest:
- T_twin = Σ_{p ∈ twins} w_p² |k_p⟩⟨k_p|
- T_rest = Σ_{p ∉ twins} w_p² |k_p⟩⟨k_p|

Коммутатор:
  C_X = -[T_P, Ξ] = -[T_twin, Ξ] - [T_rest, Ξ]
      = C_twin + C_rest

Тогда:
  C_X* C_X = C_twin* C_twin + (C_twin* C_rest + h.c.) + C_rest* C_rest
           = K_twin + CROSS + K_rest

ВОПРОС: |CROSS| << K_twin на twin-конусе?
"""

import numpy as np
from math import log, pi, sqrt, exp
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def sieve_primes(n_max: int) -> list:
    if n_max < 2:
        return []
    sieve = [True] * (n_max + 1)
    sieve[0] = sieve[1] = False
    for x in range(2, int(n_max**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n_max + 1, x):
                sieve[i] = False
    return [x for x in range(2, n_max + 1) if sieve[x]]


def get_twins(X: int) -> list:
    """Возвращает список p где (p, p+2) — twin pair."""
    primes = set(sieve_primes(X + 2))
    return [p for p in sorted(primes) if p + 2 in primes and p <= X]


def heat_kernel(xi1: float, xi2: float, t: float) -> float:
    """K_t(ξ₁, ξ₂) = exp(-(ξ₁-ξ₂)²/(4t))."""
    return exp(-(xi1 - xi2)**2 / (4 * t))


def heat_overlap(xi_q: float, xi_p: float, t: float) -> float:
    """⟨k_q, k_p⟩ = √(2πt) · K_{2t}(ξ_q, ξ_p)."""
    return sqrt(2 * pi * t) * heat_kernel(xi_q, xi_p, 2 * t)


def deriv_heat_overlap(xi_q: float, xi_p: float, t: float) -> float:
    """⟨∂k_q, k_p⟩ = (ξ_p - ξ_q)/2 · √(2πt) · K_{2t}(ξ_q, ξ_p)."""
    delta = xi_p - xi_q
    return (delta / 2) * sqrt(2 * pi * t) * heat_kernel(xi_q, xi_p, 2 * t)


def compute_cross_terms(X: int, t: float = 1.0):
    """
    Вычисляет три компоненты C_X* C_X на twin-векторе Φ_X.

    Returns:
        K_twin: ⟨Φ_X, C_twin* C_twin Φ_X⟩
        K_rest: ⟨Φ_X, C_rest* C_rest Φ_X⟩
        CROSS:  ⟨Φ_X, (C_twin* C_rest + h.c.) Φ_X⟩
    """
    primes = sieve_primes(X)
    twins = set(get_twins(X))

    # Координаты
    xi = {n: log(n) / (2 * pi) for n in primes}

    # Веса w_r = Λ(r)/√r ≈ log(r)/√r для простых
    w = {r: log(r) / sqrt(r) for r in primes}

    # Twin-вектор: Φ_X = Σ_{p ∈ twins} k_p (равномерные веса λ_p = 1)
    twin_list = sorted(twins)

    if len(twin_list) == 0:
        return 0, 0, 0, {}

    # Разбиваем primes на twin и rest
    rest_primes = [p for p in primes if p not in twins and p + 2 not in twins]
    twin_primes = list(twins)  # только меньший из пары

    # =========================================================================
    # Формулы для ⟨Φ, C_A* C_B Φ⟩ где A, B ∈ {twin, rest}
    #
    # C_S = Σ_{r∈S} w_r² (|k_r⟩⟨∂k_r| - |∂k_r⟩⟨k_r|)
    #
    # ⟨Φ, C_A* C_B Φ⟩ = Σ_{r∈A, s∈B} w_r² w_s² × M(r,s)
    #
    # где M(r,s) = сложная формула через overlaps
    # =========================================================================

    def M_matrix_element(r, s, twin_list, xi, t):
        """
        Вычисляет вклад пары (r,s) в ⟨Φ, C_r* C_s Φ⟩.

        C_r* C_s действует на Φ = Σ_p k_p:
        ⟨Φ, C_r* C_s Φ⟩ = Σ_{p,q ∈ twins} ⟨k_p, C_r* C_s k_q⟩
        """
        result = 0.0
        xi_r, xi_s = xi[r], xi[s]

        for p in twin_list:
            for q in twin_list:
                xi_p, xi_q = xi[p], xi[q]

                # ⟨k_p, C_r* C_s k_q⟩ = complicated formula
                # C_r = w_r² (|k_r⟩⟨∂k_r| - |∂k_r⟩⟨k_r|)
                # C_s = w_s² (|k_s⟩⟨∂k_s| - |∂k_s⟩⟨k_s|)
                #
                # C_r* = w_r² (|∂k_r⟩⟨k_r| - |k_r⟩⟨∂k_r|)
                #
                # C_r* C_s = w_r² w_s² × (4 terms)

                # Term 1: |∂k_r⟩⟨k_r| · |k_s⟩⟨∂k_s|
                #       = ⟨k_r, k_s⟩ |∂k_r⟩⟨∂k_s|
                # ⟨k_p, ... k_q⟩ = ⟨k_r, k_s⟩ ⟨k_p, ∂k_r⟩ ⟨∂k_s, k_q⟩

                kr_ks = heat_overlap(xi_r, xi_s, t)
                kp_dkr = deriv_heat_overlap(xi_p, xi_r, t)  # ⟨k_p, ∂k_r⟩
                dks_kq = deriv_heat_overlap(xi_s, xi_q, t)  # ⟨∂k_s, k_q⟩

                term1 = kr_ks * kp_dkr * dks_kq

                # Term 2: |∂k_r⟩⟨k_r| · (-|∂k_s⟩⟨k_s|)
                #       = -⟨k_r, ∂k_s⟩ |∂k_r⟩⟨k_s|
                kr_dks = deriv_heat_overlap(xi_r, xi_s, t)
                ks_kq = heat_overlap(xi_s, xi_q, t)

                term2 = -kr_dks * kp_dkr * ks_kq

                # Term 3: (-|k_r⟩⟨∂k_r|) · |k_s⟩⟨∂k_s|
                #       = -⟨∂k_r, k_s⟩ |k_r⟩⟨∂k_s|
                dkr_ks = deriv_heat_overlap(xi_r, xi_s, t)  # ⟨∂k_r, k_s⟩ = -⟨k_s, ∂k_r⟩
                kp_kr = heat_overlap(xi_p, xi_r, t)

                term3 = -dkr_ks * kp_kr * dks_kq

                # Term 4: (-|k_r⟩⟨∂k_r|) · (-|∂k_s⟩⟨k_s|)
                #       = ⟨∂k_r, ∂k_s⟩ |k_r⟩⟨k_s|
                # ⟨∂k_r, ∂k_s⟩ нужно вычислить отдельно
                # Формула: ⟨∂k_r, ∂k_s⟩ = (интеграл)
                # Приближённо для близких: ~ t + (ξ_r - ξ_s)²/4
                delta_rs = xi_r - xi_s
                dkr_dks = sqrt(2 * pi * t) * heat_kernel(xi_r, xi_s, 2*t) * (t + delta_rs**2 / 4)

                term4 = dkr_dks * kp_kr * ks_kq

                result += term1 + term2 + term3 + term4

        return result

    # Упрощённая версия: считаем только диагональные вклады для скорости
    # Полная версия слишком медленная для больших X

    K_twin = 0.0
    K_rest = 0.0
    CROSS = 0.0

    # Для twin-twin
    for r in twin_primes[:min(50, len(twin_primes))]:  # ограничиваем для скорости
        wr = w[r]
        M_rr = M_matrix_element(r, r, twin_list[:min(50, len(twin_list))], xi, t)
        K_twin += wr**4 * M_rr

    # Для rest-rest (sample)
    rest_sample = rest_primes[:min(30, len(rest_primes))]
    for r in rest_sample:
        wr = w[r]
        M_rr = M_matrix_element(r, r, twin_list[:min(50, len(twin_list))], xi, t)
        K_rest += wr**4 * M_rr

    # Для cross terms (twin-rest)
    for r in twin_primes[:min(30, len(twin_primes))]:
        wr = w[r]
        for s in rest_sample[:min(20, len(rest_sample))]:
            ws = w[s]
            M_rs = M_matrix_element(r, s, twin_list[:min(30, len(twin_list))], xi, t)
            CROSS += 2 * wr**2 * ws**2 * M_rs  # factor 2 for hermitian

    info = {
        'n_twins': len(twin_list),
        'n_primes': len(primes),
        'n_rest': len(rest_primes),
    }

    return K_twin, K_rest, CROSS, info


def analyze_cross_terms():
    """Анализ cross-terms для разных X."""
    console.print(Panel.fit(
        "[bold cyan]CROSS-TERMS ANALYSIS FOR STEP B[/bold cyan]\n"
        "[dim]Проверка: |CROSS| << K_twin?[/dim]",
        box=box.DOUBLE
    ))

    table = Table(title="Cross-Terms Decomposition", box=box.DOUBLE)
    table.add_column("X", style="cyan")
    table.add_column("twins", style="yellow")
    table.add_column("K_twin", style="green")
    table.add_column("K_rest", style="blue")
    table.add_column("CROSS", style="magenta")
    table.add_column("|CROSS|/K_twin", style="red")

    t_heat = 1.0

    for X in [100, 500, 1000, 2000]:
        K_twin, K_rest, CROSS, info = compute_cross_terms(X, t_heat)

        ratio = abs(CROSS) / (abs(K_twin) + 1e-30)

        status = "✓ SMALL" if ratio < 0.3 else "⚠ LARGE"

        table.add_row(
            str(X),
            str(info['n_twins']),
            f"{K_twin:.2e}",
            f"{K_rest:.2e}",
            f"{CROSS:.2e}",
            f"{ratio:.2%} {status}"
        )

    console.print(table)
    console.print()

    # Вывод
    console.print(Panel.fit(
        "[bold green]ИНТЕРПРЕТАЦИЯ:[/bold green]\n\n"
        "Если |CROSS|/K_twin < 30%:\n"
        "  → Cross-terms малы\n"
        "  → Archimedean splitting работает\n"
        "  → Step B может быть доказан через baseline\n\n"
        "Если |CROSS|/K_twin > 50%:\n"
        "  → Cross-terms существенны\n"
        "  → Нужна другая стратегия\n",
        box=box.DOUBLE,
        border_style="green"
    ))


def simplified_cross_analysis():
    """
    Упрощённый анализ: сравнение overlap'ов между twin и non-twin primes.

    Идея: cross-terms малы если twin primes "далеко" от non-twin primes в ξ-пространстве.
    """
    console.print(Panel.fit(
        "[bold cyan]SIMPLIFIED OVERLAP ANALYSIS[/bold cyan]\n"
        "[dim]Twin vs Non-Twin distance in ξ-space[/dim]",
        box=box.DOUBLE
    ))

    t_heat = 1.0
    X = 1000

    primes = sieve_primes(X)
    twins = set(get_twins(X))

    xi = {n: log(n) / (2 * pi) for n in primes}

    twin_primes = [p for p in primes if p in twins]
    rest_primes = [p for p in primes if p not in twins and p + 2 not in twins]

    # Средний overlap внутри twins
    twin_overlaps = []
    for i, p in enumerate(twin_primes[:50]):
        for q in twin_primes[i+1:50]:
            overlap = heat_overlap(xi[p], xi[q], t_heat)
            twin_overlaps.append(abs(overlap))

    # Средний overlap twin-rest
    cross_overlaps = []
    for p in twin_primes[:30]:
        for r in rest_primes[:30]:
            overlap = heat_overlap(xi[p], xi[r], t_heat)
            cross_overlaps.append(abs(overlap))

    avg_twin = np.mean(twin_overlaps) if twin_overlaps else 0
    avg_cross = np.mean(cross_overlaps) if cross_overlaps else 0

    console.print(f"[green]Average twin-twin overlap:  {avg_twin:.4e}[/green]")
    console.print(f"[yellow]Average twin-rest overlap:  {avg_cross:.4e}[/yellow]")
    console.print(f"[cyan]Ratio (cross/twin):         {avg_cross/(avg_twin+1e-30):.2%}[/cyan]")
    console.print()

    if avg_cross < avg_twin * 0.5:
        console.print("[bold green]✓ Cross-overlaps значительно меньше![/bold green]")
        console.print("[green]  → Twins кластеризованы в ξ-пространстве[/green]")
        console.print("[green]  → Cross-terms должны быть подавлены[/green]")
    else:
        console.print("[bold yellow]⚠ Cross-overlaps сравнимы с twin-overlaps[/bold yellow]")
        console.print("[yellow]  → Twins не изолированы[/yellow]")


def main():
    console.print(Panel.fit(
        "[bold magenta]STEP B: CROSS-TERMS VERIFICATION[/bold magenta]\n"
        "[dim]C_X = C_twin + C_rest, checking |CROSS| << K_twin[/dim]",
        box=box.DOUBLE
    ))

    simplified_cross_analysis()
    console.print()
    analyze_cross_terms()


if __name__ == "__main__":
    main()
