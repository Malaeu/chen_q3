#!/usr/bin/env python3
"""
Анализ цикличности Target Theorem
==================================

КЛЮЧЕВОЙ ВОПРОС:
  Может ли Q3 gap κ(X) сломать цикличность?

ЯВНАЯ ФОРМУЛА Q_X:
  Q_X = E_comm = λᵀ A λ
  где A_pq = (ξ_q - ξ_p)/2 · (G²)_pq

ДВА СЦЕНАРИЯ:
  1. Twins конечны → что с Q_X, E_lat, κ(X)?
  2. Twins бесконечны → проверка consistency

"""

import numpy as np
from math import log, pi, sqrt, exp
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def sieve_primes(limit: int) -> list[int]:
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]


def get_twin_primes(limit: int) -> list[int]:
    primes_set = set(sieve_primes(limit + 2))
    return sorted([p for p in primes_set if p + 2 in primes_set and p <= limit])


def G(delta: float, t: float) -> float:
    """Gaussian overlap."""
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def compute_QX_explicit(X: int, t: float = 1.0) -> dict:
    """
    Вычислить Q_X = E_comm явно.

    Q_X = λᵀ A λ  где A_pq = (ξ_q - ξ_p)/2 · (G²)_pq
    """
    twins = get_twin_primes(X)
    N = len(twins)

    if N < 2:
        return None

    # Позиции и веса
    xi = np.array([log(p) / (2 * pi) for p in twins])
    lam = np.array([log(p) * log(p + 2) for p in twins])  # Λ(p)·Λ(p+2)

    # Gram матрица G
    G_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = xi[i] - xi[j]
            G_mat[i, j] = G(delta, t)

    # G² матрица
    G2 = G_mat @ G_mat

    # Матрица коммутатора A_pq = (ξ_q - ξ_p)/2 · (G²)_pq
    A = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            A[i, j] = (xi[j] - xi[i]) / 2 * G2[i, j]

    # Ξ матрица: Ξ_ij = (ξ_i + ξ_j)/2 · G_ij
    Xi_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            Xi_mat[i, j] = (xi[i] + xi[j]) / 2 * G_mat[i, j]

    # E_lat = ‖G·λ‖² = λᵀ G² λ
    Glam = G_mat @ lam
    E_lat = np.sum(Glam**2)

    # E_comm через коммутаторную форму: c^T G c
    # где c = ξ⊙(Gλ) - Ξλ
    xi_Glam = xi * Glam  # поэлементно
    Xi_lam = Xi_mat @ lam
    c = xi_Glam - Xi_lam
    E_comm = c @ G_mat @ c

    # Альтернативно через A: Q_X ≈ λᵀ (A^T G A) λ? Нет, сложнее.
    # Проверим прямое: E_comm / E_lat = c_twins

    # ‖Φ‖² = λᵀ G λ
    norm_sq = lam @ G_mat @ lam

    # ⟨T_P Φ, Φ⟩ = E_lat (по определению)

    return {
        'X': X,
        'N': N,
        'Q_X': E_comm,
        'E_lat': E_lat,
        'E_comm': E_comm,
        'c_twins': E_comm / E_lat if E_lat > 1e-15 else 0,
        'norm_sq': norm_sq,
        'lam_sum': np.sum(lam),
        'xi_max': xi[-1],
        'xi_min': xi[0],
    }


def simulate_finite_twins(P_star: int, X_max: int, t: float = 1.0):
    """
    Сценарий: twins конечны с максимальным P*.

    Для X > P*:
    - T(X) = const = T(P*)
    - Φ_X = Φ_∞ = фиксирован
    - Q_X = const

    Проверим сходимость.
    """
    twins_full = get_twin_primes(P_star)
    N = len(twins_full)

    if N < 2:
        return None

    # Фиксированные позиции и веса (как при P*)
    xi = np.array([log(p) / (2 * pi) for p in twins_full])
    lam = np.array([log(p) * log(p + 2) for p in twins_full])

    # G и Ξ матрицы фиксированы
    G_mat = np.zeros((N, N))
    Xi_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = xi[i] - xi[j]
            G_mat[i, j] = G(delta, t)
            Xi_mat[i, j] = (xi[i] + xi[j]) / 2 * G_mat[i, j]

    # Фиксированный E_comm и E_lat
    Glam = G_mat @ lam
    E_lat_fixed = np.sum(Glam**2)

    xi_Glam = xi * Glam
    Xi_lam = Xi_mat @ lam
    c = xi_Glam - Xi_lam
    E_comm_fixed = c @ G_mat @ c

    # Для X >> P*, всё остаётся константой!
    results = {
        'P_star': P_star,
        'N_twins': N,
        'E_lat_infty': E_lat_fixed,
        'E_comm_infty': E_comm_fixed,
        'Q_X_infty': E_comm_fixed,
        'c_twins_infty': E_comm_fixed / E_lat_fixed,
    }

    return results


def analyze_H_X_on_fixed_Phi(P_star: int, X_values: list[int], t: float = 1.0):
    """
    Проверить: как ⟨H_X Φ_∞, Φ_∞⟩ ведёт себя при X → ∞
    если Φ_∞ фиксирован (twins конечны).

    H_X = T_A - T_P

    Ключ: сходится ли ⟨T_P Φ_∞, Φ_∞⟩ при X → ∞?
    """
    twins = get_twin_primes(P_star)
    N = len(twins)

    if N < 2:
        return None

    # Фиксированные ξ и λ
    xi_twins = np.array([log(p) / (2 * pi) for p in twins])
    lam = np.array([log(p) * log(p + 2) for p in twins])

    # Φ_∞ = Σ_p λ_p k_p (функция в RKHS)
    # Но нам нужно ⟨T_P^{(X)} Φ_∞, Φ_∞⟩

    # T_P^{(X)} Φ = Σ_{n≤X, n prime} w_n ⟨Φ, k_n⟩ k_n
    # где w_n = Λ(n)/√n = log(n)/√n

    # ⟨T_P^{(X)} Φ_∞, Φ_∞⟩ = Σ_{n≤X} w_n |⟨Φ_∞, k_n⟩|²

    # ⟨Φ_∞, k_n⟩ = Σ_p λ_p ⟨k_p, k_n⟩ = Σ_p λ_p G(ξ_p - ξ_n)

    results = []

    for X in X_values:
        primes_X = sieve_primes(X)

        # ξ_n для всех primes до X
        xi_primes = np.array([log(n) / (2 * pi) for n in primes_X])
        w_primes = np.array([log(n) / sqrt(n) for n in primes_X])  # Λ(n)/√n

        # ⟨Φ_∞, k_n⟩ для каждого prime n
        inner_prods = np.zeros(len(primes_X))
        for i, (n, xi_n) in enumerate(zip(primes_X, xi_primes)):
            # ⟨Φ_∞, k_n⟩ = Σ_p λ_p G(ξ_p - ξ_n)
            for xi_p, lam_p in zip(xi_twins, lam):
                delta = xi_p - xi_n
                inner_prods[i] += lam_p * G(delta, t)

        # ⟨T_P^{(X)} Φ_∞, Φ_∞⟩ = Σ_n w_n |⟨Φ_∞, k_n⟩|²
        T_P_energy = np.sum(w_primes * inner_prods**2)

        results.append({
            'X': X,
            'num_primes': len(primes_X),
            'T_P_energy': T_P_energy,
        })

    return results


def main():
    console.print(Panel.fit(
        "[bold cyan]АНАЛИЗ ЦИКЛИЧНОСТИ TARGET THEOREM[/bold cyan]\n"
        "[dim]Может ли Q3 gap κ(X) сломать цикличность?[/dim]",
        box=box.DOUBLE
    ))

    t = 1.0

    # ЧАСТЬ 1: Явная формула Q_X
    console.print("\n[bold yellow]1. ЯВНАЯ ФОРМУЛА Q_X[/bold yellow]\n")

    X_values = [100, 500, 1000, 2000, 5000, 10000, 20000]

    table = Table(title="Q_X = E_comm явно", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("N", style="blue", justify="right")
    table.add_column("Q_X = E_comm", style="green", justify="right")
    table.add_column("E_lat", style="yellow", justify="right")
    table.add_column("c_twins", style="magenta", justify="right")
    table.add_column("‖Φ‖²", style="red", justify="right")

    Q_X_data = []
    for X in X_values:
        res = compute_QX_explicit(X, t)
        if res:
            Q_X_data.append(res)
            table.add_row(
                str(X),
                str(res['N']),
                f"{res['Q_X']:.2e}",
                f"{res['E_lat']:.2e}",
                f"{res['c_twins']:.4f}",
                f"{res['norm_sq']:.2e}"
            )

    console.print(table)

    # Scaling fit
    if len(Q_X_data) >= 3:
        log_X = np.log([r['X'] for r in Q_X_data])
        log_QX = np.log([r['Q_X'] for r in Q_X_data])
        log_Elat = np.log([r['E_lat'] for r in Q_X_data])
        log_norm = np.log([r['norm_sq'] for r in Q_X_data])

        alpha_QX, _ = np.polyfit(log_X, log_QX, 1)
        alpha_Elat, _ = np.polyfit(log_X, log_Elat, 1)
        alpha_norm, _ = np.polyfit(log_X, log_norm, 1)

        console.print(f"\n[green]SCALING:[/green]")
        console.print(f"  Q_X ~ X^{alpha_QX:.3f}")
        console.print(f"  E_lat ~ X^{alpha_Elat:.3f}")
        console.print(f"  ‖Φ‖² ~ X^{alpha_norm:.3f}")

    # ЧАСТЬ 2: Сценарий "twins конечны"
    console.print("\n" + "="*60)
    console.print("\n[bold yellow]2. СЦЕНАРИЙ: TWINS КОНЕЧНЫ (P* = 1000)[/bold yellow]\n")

    P_star = 1000
    finite_res = simulate_finite_twins(P_star, 100000, t)

    if finite_res:
        console.print(f"Максимальный twin prime: P* = {P_star}")
        console.print(f"Число twins: {finite_res['N_twins']}")
        console.print(f"\nПри X → ∞ (twins конечны):")
        console.print(f"  Q_X → Q_∞ = {finite_res['Q_X_infty']:.4e}")
        console.print(f"  E_lat → E_lat_∞ = {finite_res['E_lat_infty']:.4e}")
        console.print(f"  c_twins → c_∞ = {finite_res['c_twins_infty']:.4f}")

    # ЧАСТЬ 3: Сходимость ⟨T_P Φ_∞, Φ_∞⟩
    console.print("\n" + "="*60)
    console.print("\n[bold yellow]3. СХОДИМОСТЬ ⟨T_P^{(X)} Φ_∞, Φ_∞⟩[/bold yellow]\n")

    console.print(f"[dim]Если twins конечны с P* = {P_star}, Φ_∞ фиксирован.[/dim]")
    console.print("[dim]Проверяем: сходится ли ⟨T_P^{(X)} Φ_∞, Φ_∞⟩ при X → ∞?[/dim]\n")

    X_test = [1000, 2000, 5000, 10000, 20000, 50000]
    convergence = analyze_H_X_on_fixed_Phi(P_star, X_test, t)

    if convergence:
        table2 = Table(title=f"⟨T_P^(X) Φ_∞, Φ_∞⟩ для P* = {P_star}", box=box.DOUBLE)
        table2.add_column("X", style="cyan", justify="right")
        table2.add_column("#primes", style="blue", justify="right")
        table2.add_column("⟨T_P Φ_∞, Φ_∞⟩", style="green", justify="right")
        table2.add_column("Δ from prev", style="yellow", justify="right")

        prev_val = None
        for r in convergence:
            delta = "-"
            if prev_val is not None:
                delta = f"{(r['T_P_energy'] - prev_val) / prev_val * 100:.2f}%"
            table2.add_row(
                str(r['X']),
                str(r['num_primes']),
                f"{r['T_P_energy']:.4e}",
                delta
            )
            prev_val = r['T_P_energy']

        console.print(table2)

        # Проверка сходимости
        if len(convergence) >= 2:
            last_delta = (convergence[-1]['T_P_energy'] - convergence[-2]['T_P_energy'])
            rel_delta = last_delta / convergence[-2]['T_P_energy']

            if abs(rel_delta) < 0.01:
                console.print(f"\n[green]✓ СХОДИМОСТЬ: |Δ| = {abs(rel_delta)*100:.2f}% < 1%[/green]")
                console.print("[green]  ⟨T_P Φ_∞, Φ_∞⟩ → const при X → ∞ (для фикс. Φ_∞)[/green]")
            else:
                console.print(f"\n[yellow]⚠ Медленная сходимость: |Δ| = {abs(rel_delta)*100:.2f}%[/yellow]")

    # ЧАСТЬ 4: Выводы о цикличности
    console.print("\n" + "="*60)
    console.print("\n[bold yellow]4. АНАЛИЗ ЦИКЛИЧНОСТИ[/bold yellow]\n")

    console.print("""
[cyan]ЕСЛИ TWINS КОНЕЧНЫ (T(X) → T_∞ = const):[/cyan]

  1. Φ_X → Φ_∞ = фиксирован

  2. Q_X = E_comm → Q_∞ = const
     (матрицы G, A, Ξ фиксированы)

  3. E_lat = ⟨T_P Φ, Φ⟩ → E_lat_∞ = const
     (из-за Gaussian decay: ⟨k_p, k_n⟩ → 0 при |ξ_p - ξ_n| → ∞)

  4. c_twins = Q_X / E_lat → c_∞ = const > 0

  5. Target Inequality: Q_X ≥ κ(X) · K_H
     → const ≥ κ(X) · const
     → κ(X) ОГРАНИЧЕН СВЕРХУ!

[red]КРИТИЧЕСКАЯ ТОЧКА:[/red]
  Q3 gap κ(X) НЕ МОЖЕТ расти без ограничения
  при фиксированном Φ_∞!

  Потому что ⟨H_X Φ_∞, Φ_∞⟩ → const.

[yellow]ВЫВОД О ЦИКЛИЧНОСТИ:[/yellow]
  Target Theorem НЕ РАБОТАЕТ если полагаться на рост κ(X).

  κ(X) из Q3 определяется спектром H_X,
  но на ФИКСИРОВАННОМ векторе Φ_∞ энергия сходится.

  ⟹ Нужен ДРУГОЙ источник роста для противоречия!
""")

    # ЧАСТЬ 5: Возможные выходы
    console.print("\n" + "="*60)
    console.print("\n[bold yellow]5. ВОЗМОЖНЫЕ ВЫХОДЫ ИЗ ЦИКЛИЧНОСТИ[/bold yellow]\n")

    console.print("""
[green]ВАРИАНТ A: Арифметический lower bound[/green]
  Доказать: если twins конечны ⟹ Q_X = Ω(X^ε)

  Это number theory про S(X) = Σ Λ(n)Λ(n+2).
  Сложность: ~0.95 (как сама twin conjecture)

[green]ВАРИАНТ B: Q3 как spectral multiplier[/green]
  Может быть Q3 даёт не просто gap, а СТРУКТУРУ оператора,
  которая несовместима с конечными twins?

  Нужно: глубже понять что именно Q3 утверждает.

[green]ВАРИАНТ C: Альтернативный норма/энергия[/green]
  Использовать не ‖Φ‖² или ⟨H_X Φ, Φ⟩,
  а другую величину которая РАСТЁТ при конечных twins.

  Например: ⟨T_A Φ, Φ⟩ растёт? (arch-энергия)

[green]ВАРИАНТ D: Отказ от proof by contradiction[/green]
  Вместо "twins конечны ⟹ противоречие"
  Прямое: "Q3 structure ⟹ twins бесконечны"

  Это требует совсем другой стратегии.
""")

    return {
        'Q_X_data': Q_X_data,
        'finite_res': finite_res,
        'convergence': convergence,
    }


if __name__ == "__main__":
    main()
