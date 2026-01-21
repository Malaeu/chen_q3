#!/usr/bin/env python3
"""
B₁ Precise Check: Что именно требует B₁(prime)?
================================================

ФОРМУЛИРОВКА B₁(prime):
  ‖[T_P, Ξ] Φ‖² ≥ c₁ · ⟨T_P Φ, Φ⟩

ВОПРОС: Как эти величины ведут себя при конечных twins?

Ключевое различие:
  - [T_P^{(X)}, Ξ] — коммутатор с оператором на ВСЕХ primes до X
  - Φ = Σ_p λ_p k_p — вектор только на TWINS (фиксирован при конечных)

При X → ∞:
  - T_P^{(X)} включает больше primes
  - ‖[T_P^{(X)}, Ξ] Φ_∞‖² может расти!
  - ⟨T_P^{(X)} Φ_∞, Φ_∞⟩ растёт (как показано)

Вопрос: c₁(X) = ‖[T_P, Ξ] Φ‖² / ⟨T_P Φ, Φ⟩ — растёт, падает, или const?
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


def compute_full_commutator_norm(
    xi_twins: np.ndarray,
    lam: np.ndarray,
    X: int,
    t: float
) -> dict:
    """
    Compute ‖[T_P^{(X)}, Ξ] Φ_∞‖² где Φ_∞ = Σ_p λ_p k_p (только twins).

    [T_P, Ξ] f = T_P(Ξf) - Ξ(T_P f)

    Для f = Φ_∞:
      T_P(Ξ Φ_∞) = Σ_n w_n ⟨Ξ Φ_∞, k_n⟩ k_n
      Ξ(T_P Φ_∞) = ξ · T_P Φ_∞

      [T_P, Ξ] Φ_∞ = Σ_n w_n [⟨Ξ Φ_∞, k_n⟩ - ξ_n ⟨Φ_∞, k_n⟩] k_n

    где ⟨Ξ Φ_∞, k_n⟩ = Σ_p λ_p ⟨ξ k_p, k_n⟩ = Σ_p λ_p Ξ_{pn}
    и Ξ_{pn} = (ξ_p + ξ_n)/2 · G(ξ_p - ξ_n)

    ‖[T_P, Ξ] Φ_∞‖² = Σ_n w_n [c_n]² где c_n = ⟨Ξ Φ_∞, k_n⟩ - ξ_n ⟨Φ_∞, k_n⟩
    """
    primes = sieve_primes(X)
    num_primes = len(primes)
    num_twins = len(xi_twins)

    # ξ и w для всех primes
    xi_primes = np.array([log(p) / (2 * pi) for p in primes])
    w_primes = np.array([log(p) / sqrt(p) for p in primes])

    # ⟨Φ_∞, k_n⟩ для каждого prime n
    inner_prods = np.zeros(num_primes)
    for i, xi_n in enumerate(xi_primes):
        for xi_p, lam_p in zip(xi_twins, lam):
            delta = xi_p - xi_n
            inner_prods[i] += lam_p * G(delta, t)

    # ⟨Ξ Φ_∞, k_n⟩ для каждого prime n
    xi_inner_prods = np.zeros(num_primes)
    for i, xi_n in enumerate(xi_primes):
        for xi_p, lam_p in zip(xi_twins, lam):
            delta = xi_p - xi_n
            Xi_pn = (xi_p + xi_n) / 2 * G(delta, t)
            xi_inner_prods[i] += lam_p * Xi_pn

    # c_n = ⟨Ξ Φ_∞, k_n⟩ - ξ_n ⟨Φ_∞, k_n⟩
    c_coeffs = xi_inner_prods - xi_primes * inner_prods

    # ‖[T_P, Ξ] Φ_∞‖² = Σ_n w_n c_n² (грубая аппроксимация)
    # Точнее: нужно ⟨[T_P,Ξ]Φ, [T_P,Ξ]Φ⟩ = Σ_{n,m} w_n w_m c_n c_m ⟨k_n, k_m⟩
    # Для простоты возьмём диагональ:
    comm_norm_sq_diag = np.sum(w_primes * c_coeffs**2)

    # Полная норма (с off-diagonal):
    comm_norm_sq_full = 0.0
    for i in range(num_primes):
        for j in range(num_primes):
            delta = xi_primes[i] - xi_primes[j]
            G_ij = G(delta, t)
            comm_norm_sq_full += w_primes[i] * w_primes[j] * c_coeffs[i] * c_coeffs[j] * G_ij

    # ⟨T_P Φ_∞, Φ_∞⟩ = Σ_n w_n |⟨Φ_∞, k_n⟩|²
    T_P_energy = np.sum(w_primes * inner_prods**2)

    # c₁(X) = ‖[T_P, Ξ] Φ‖² / ⟨T_P Φ, Φ⟩
    c1_diag = comm_norm_sq_diag / T_P_energy if T_P_energy > 1e-15 else 0
    c1_full = comm_norm_sq_full / T_P_energy if T_P_energy > 1e-15 else 0

    return {
        'X': X,
        'num_primes': num_primes,
        'comm_norm_sq_diag': comm_norm_sq_diag,
        'comm_norm_sq_full': comm_norm_sq_full,
        'T_P_energy': T_P_energy,
        'c1_diag': c1_diag,
        'c1_full': c1_full,
    }


def main():
    console.print(Panel.fit(
        "[bold cyan]B₁ PRECISE CHECK[/bold cyan]\n"
        "[dim]c₁(X) = ‖[T_P^{(X)}, Ξ] Φ_∞‖² / ⟨T_P^{(X)} Φ_∞, Φ_∞⟩[/dim]",
        box=box.DOUBLE
    ))

    t = 1.0

    # Сценарий: twins конечны с P* = 1000
    P_star = 1000
    twins = get_twin_primes(P_star)
    N = len(twins)

    console.print(f"\n[yellow]Сценарий: twins конечны с P* = {P_star}[/yellow]")
    console.print(f"Число twins: {N}")

    # Фиксированный вектор Φ_∞
    xi_twins = np.array([log(p) / (2 * pi) for p in twins])
    lam = np.array([log(p) * log(p + 2) for p in twins])

    # Нормируем λ
    lam = lam / np.linalg.norm(lam)

    console.print(f"‖λ‖ = 1.0 (нормировано)\n")

    # Тестируем при разных X
    X_values = [1000, 1500, 2000, 3000, 5000]

    console.print("[dim]Вычисление full commutator norm (O(#primes²))...[/dim]\n")

    results = []

    for X in X_values:
        console.print(f"[dim]X = {X}...[/dim]", end=" ")
        res = compute_full_commutator_norm(xi_twins, lam, X, t)
        results.append(res)
        console.print(f"[green]done[/green] (#primes = {res['num_primes']})")

    # Таблица
    console.print("\n")
    table = Table(title="c₁(X) при фиксированном Φ_∞", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("#primes", style="blue", justify="right")
    table.add_column("‖[T_P,Ξ]Φ‖²", style="green", justify="right")
    table.add_column("⟨T_P Φ, Φ⟩", style="yellow", justify="right")
    table.add_column("c₁(X)", style="magenta", justify="right")

    for r in results:
        table.add_row(
            str(r['X']),
            str(r['num_primes']),
            f"{r['comm_norm_sq_full']:.4e}",
            f"{r['T_P_energy']:.4e}",
            f"{r['c1_full']:.6f}"
        )

    console.print(table)

    # Scaling analysis
    if len(results) >= 3:
        log_X = np.log([r['X'] for r in results])
        log_c1 = np.log([r['c1_full'] for r in results])
        log_comm = np.log([r['comm_norm_sq_full'] for r in results])
        log_T_P = np.log([r['T_P_energy'] for r in results])

        alpha_c1, _ = np.polyfit(log_X, log_c1, 1)
        alpha_comm, _ = np.polyfit(log_X, log_comm, 1)
        alpha_T_P, _ = np.polyfit(log_X, log_T_P, 1)

        console.print(f"\n[bold cyan]SCALING:[/bold cyan]")
        console.print(f"  ‖[T_P,Ξ]Φ_∞‖² ~ X^{alpha_comm:.3f}")
        console.print(f"  ⟨T_P Φ_∞, Φ_∞⟩ ~ X^{alpha_T_P:.3f}")
        console.print(f"  c₁(X) ~ X^{alpha_c1:.3f}")

        console.print("\n" + "="*60)

        if alpha_c1 < -0.1:
            console.print(Panel.fit(
                f"[bold red]❌ c₁(X) → 0 как X^{{{alpha_c1:.2f}}}![/bold red]\n\n"
                f"При конечных twins:\n"
                f"  ‖[T_P,Ξ]Φ‖² растёт как X^{{{alpha_comm:.2f}}}\n"
                f"  ⟨T_P Φ, Φ⟩ растёт как X^{{{alpha_T_P:.2f}}}\n"
                f"  c₁ = ratio → 0\n\n"
                f"[yellow]Если B₁(prime) требует c₁ ≥ c₀ > 0,\n"
                f"то конечные twins НАРУШАЮТ B₁(prime)![/yellow]\n\n"
                f"[green]⟹ B₁(prime) + Q3 ⟹ twins бесконечны![/green]",
                box=box.DOUBLE,
                border_style="red"
            ))
        elif alpha_c1 > 0.1:
            console.print(Panel.fit(
                f"[bold green]✓ c₁(X) → ∞ как X^{{{alpha_c1:.2f}}}![/bold green]\n\n"
                f"c₁ растёт — B₁ НЕ нарушается.\n"
                f"Нет противоречия через B₁.",
                box=box.DOUBLE,
                border_style="green"
            ))
        else:
            console.print(Panel.fit(
                f"[bold yellow]⚠ c₁(X) ≈ const (X^{{{alpha_c1:.2f}}})[/bold yellow]\n\n"
                f"c₁ примерно константа.\n"
                f"B₁ выполняется, но без роста.",
                box=box.DOUBLE,
                border_style="yellow"
            ))

    return results


if __name__ == "__main__":
    main()
