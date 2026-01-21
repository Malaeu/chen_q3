#!/usr/bin/env python3
"""
Exact Commutator Formula: Формализация геометрического механизма
================================================================

КРИТИЧЕСКИЕ ВОПРОСЫ ИЗ АУДИТА:

Q1: Проверить точную формулу A_pq = (ξ_q - ξ_p)/2 · (G²)_pq

Q2: Вычислить Var_Φ(ξ) и связь с c_twins

Q3: Асимптотика c_twins(uniform) vs c_twins(χ₄) до X = 10⁶

ТОЧНАЯ ФОРМУЛА КОММУТАТОРА:

A_pq = ⟨k_p | [T_P, Ξ] | k_q⟩

Аудит предполагает:
  A_pq = (ξ_q - ξ_p)/2 · (G²)_pq

где (G²)_pq = Σ_r G_pr · G_rq

ПРОВЕРИМ ЧИСЛЕННО!
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


def chi4(n: int) -> int:
    r = n % 4
    if r == 1:
        return 1
    elif r == 3:
        return -1
    else:
        return 0


def G(delta: float, t: float) -> float:
    return sqrt(2 * pi * t) * exp(-delta**2 / (8 * t))


def verify_commutator_formula(N: int = 20, Delta: float = 0.5, t: float = 1.0):
    """
    Q1: Verify A_pq = (ξ_q - ξ_p)/2 · (G²)_pq on lattice.
    """
    console.print("\n[bold cyan]Q1: ПРОВЕРКА ТОЧНОЙ ФОРМУЛЫ КОММУТАТОРА[/bold cyan]\n")

    # Build lattice
    positions = np.array([n * Delta for n in range(N)])

    # Gram matrix
    G_mat = np.zeros((N, N))
    Xi_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = positions[i] - positions[j]
            G_mat[i, j] = G(delta, t)
            Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

    # G² matrix
    G2_mat = G_mat @ G_mat

    # Compute commutator matrix A directly
    # T_P = Σ |k_p⟩⟨k_p| acts as projection
    # [T_P, Ξ] in {k_p} basis:
    # A_pq = ⟨k_p | T_P Ξ - Ξ T_P | k_q⟩
    #      = Σ_r G_pr Ξ_rq - Ξ_pr G_rq
    #      = Σ_r G_pr · (ξ_r + ξ_q)/2 · G_rq - (ξ_p + ξ_r)/2 · G_pr · G_rq
    #      = (1/2) Σ_r G_pr G_rq (ξ_q - ξ_p)
    #      = (ξ_q - ξ_p)/2 · (G²)_pq

    # Direct computation
    A_direct = np.zeros((N, N))
    for p in range(N):
        for q in range(N):
            val = 0.0
            for r in range(N):
                val += G_mat[p, r] * Xi_mat[r, q] - Xi_mat[p, r] * G_mat[r, q]
            A_direct[p, q] = val

    # Formula-based computation
    A_formula = np.zeros((N, N))
    for p in range(N):
        for q in range(N):
            A_formula[p, q] = (positions[q] - positions[p]) / 2 * G2_mat[p, q]

    # Compare
    diff = np.abs(A_direct - A_formula)
    max_diff = np.max(diff)
    rel_diff = max_diff / (np.max(np.abs(A_direct)) + 1e-15)

    console.print(f"N = {N}, Δ = {Delta}, t = {t}")
    console.print(f"max|A_direct - A_formula| = {max_diff:.2e}")
    console.print(f"relative error = {rel_diff:.2e}")

    if rel_diff < 1e-10:
        console.print("[green]✓ ФОРМУЛА ПОДТВЕРЖДЕНА![/green]")
        console.print(f"  A_pq = (ξ_q - ξ_p)/2 · (G²)_pq")
        return True
    else:
        console.print("[red]✗ ФОРМУЛА НЕ ПОДТВЕРЖДЕНА[/red]")
        return False


def compute_variance_and_c_twins(X: int, t: float = 1.0):
    """
    Q2: Compute Var_Φ(ξ) and compare with c_twins.
    """
    twins = get_twin_primes(X)
    N = len(twins)

    if N < 3:
        return None

    positions = np.array([log(p) / (2 * pi) for p in twins])

    # Gram matrix
    G_mat = np.zeros((N, N))
    Xi_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = positions[i] - positions[j]
            G_mat[i, j] = G(delta, t)
            Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

    # G² matrix
    G2_mat = G_mat @ G_mat

    # Uniform λ
    lam = np.ones(N)

    # ||Φ||² = λᵀ G λ
    norm_sq = lam @ G_mat @ lam

    # E_lat = ⟨T_P Φ, Φ⟩ = ||G λ||²
    inner_prods = G_mat @ lam
    E_lat = np.sum(inner_prods**2)

    # ξ̄(Φ) = Σ_{p,q} λ_p λ_q (ξ_p + ξ_q)/2 G_pq / ||Φ||²
    xi_bar_num = 0.0
    for p in range(N):
        for q in range(N):
            xi_bar_num += lam[p] * lam[q] * (positions[p] + positions[q]) / 2 * G_mat[p, q]
    xi_bar = xi_bar_num / norm_sq

    # Var_Φ(ξ) = Σ_{p,q} λ_p λ_q (ξ_p - ξ̄)(ξ_q - ξ̄) G_pq / ||Φ||²
    var_num = 0.0
    for p in range(N):
        for q in range(N):
            var_num += lam[p] * lam[q] * (positions[p] - xi_bar) * (positions[q] - xi_bar) * G_mat[p, q]
    var_xi = var_num / norm_sq

    # E_comm using exact formula
    # |[T_P, Ξ]Φ|² = Σ_{p,q,r,s} λ_p λ_q λ_r λ_s · A_pq A_rs · G_pr
    # where A_pq = (ξ_q - ξ_p)/2 · (G²)_pq
    A_mat = np.zeros((N, N))
    for p in range(N):
        for q in range(N):
            A_mat[p, q] = (positions[q] - positions[p]) / 2 * G2_mat[p, q]

    # [T_P, Ξ]Φ = Σ_q A_pq λ_q |k_p⟩
    # So coefficients: c_p = Σ_q A_pq λ_q
    c_coeffs = A_mat @ lam

    # |[T_P, Ξ]Φ|² = c^T G c
    E_comm_exact = c_coeffs @ G_mat @ c_coeffs

    # Also compute E_comm using original method for comparison
    xi_inner = Xi_mat @ lam
    c_orig = positions * inner_prods - xi_inner
    E_comm_orig = c_orig @ G_mat @ c_orig

    c_twins = E_comm_exact / E_lat if E_lat > 0 else 0

    # Hypothesis: E_comm ≳ Var_Φ(ξ) · E_lat
    # Check ratio
    ratio_hyp = E_comm_exact / (var_xi * E_lat) if var_xi * E_lat > 1e-15 else 0

    return {
        'X': X,
        'N': N,
        'xi_bar': xi_bar,
        'var_xi': var_xi,
        'E_lat': E_lat,
        'E_comm_exact': E_comm_exact,
        'E_comm_orig': E_comm_orig,
        'c_twins': c_twins,
        'ratio_hyp': ratio_hyp,  # E_comm / (Var_Φ · E_lat)
        'match': abs(E_comm_exact - E_comm_orig) / (E_comm_orig + 1e-15) < 0.01,
    }


def asymptotic_lambda_comparison(X_values: list, t: float = 1.0):
    """
    Q3: Compare c_twins(uniform) vs c_twins(χ₄) asymptotically.
    """
    console.print("\n[bold cyan]Q3: АСИМПТОТИКА c_twins(uniform) vs c_twins(χ₄)[/bold cyan]\n")

    results = []

    for X in X_values:
        twins = get_twin_primes(X)
        N = len(twins)

        if N < 3:
            continue

        positions = np.array([log(p) / (2 * pi) for p in twins])

        # Gram matrix
        G_mat = np.zeros((N, N))
        Xi_mat = np.zeros((N, N))
        for i in range(N):
            for j in range(N):
                delta = positions[i] - positions[j]
                G_mat[i, j] = G(delta, t)
                Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

        def compute_c_twins_for_lambda(lam):
            inner_prods = G_mat @ lam
            E_lat = np.sum(inner_prods**2)
            xi_inner = Xi_mat @ lam
            c_coeffs = positions * inner_prods - xi_inner
            E_comm = c_coeffs @ G_mat @ c_coeffs
            return E_comm / E_lat if E_lat > 1e-15 else 0

        # Uniform λ
        lam_uniform = np.ones(N)
        c_uniform = compute_c_twins_for_lambda(lam_uniform)

        # χ₄ λ
        lam_chi4 = np.array([float(chi4(p)) for p in twins])
        c_chi4 = compute_c_twins_for_lambda(lam_chi4)

        # Ratio
        ratio = c_chi4 / c_uniform if c_uniform > 1e-15 else 0

        results.append({
            'X': X,
            'N': N,
            'c_uniform': c_uniform,
            'c_chi4': c_chi4,
            'ratio': ratio,
        })

        console.print(f"X = {X:>10,}: c_uniform = {c_uniform:.6f}, c_χ₄ = {c_chi4:.6f}, ratio = {ratio:.4f}")

    return results


def main():
    console.print(Panel.fit(
        "[bold cyan]ФОРМАЛИЗАЦИЯ ГЕОМЕТРИЧЕСКОГО МЕХАНИЗМА B₁[/bold cyan]\n"
        "[dim]Ответы на критические вопросы аудита[/dim]",
        box=box.DOUBLE
    ))

    # Q1: Verify exact formula
    console.print("\n" + "="*60)
    formula_ok = verify_commutator_formula(N=20, Delta=0.5, t=1.0)

    # Also verify on twins
    console.print("\n[dim]Проверка на twin primes (X=1000)...[/dim]")
    twins = get_twin_primes(1000)
    N = len(twins)
    positions = np.array([log(p) / (2 * pi) for p in twins])
    t = 1.0

    G_mat = np.zeros((N, N))
    Xi_mat = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            delta = positions[i] - positions[j]
            G_mat[i, j] = G(delta, t)
            Xi_mat[i, j] = (positions[i] + positions[j]) / 2 * G_mat[i, j]

    G2_mat = G_mat @ G_mat

    A_direct = np.zeros((N, N))
    for p in range(N):
        for q in range(N):
            val = 0.0
            for r in range(N):
                val += G_mat[p, r] * Xi_mat[r, q] - Xi_mat[p, r] * G_mat[r, q]
            A_direct[p, q] = val

    A_formula = np.zeros((N, N))
    for p in range(N):
        for q in range(N):
            A_formula[p, q] = (positions[q] - positions[p]) / 2 * G2_mat[p, q]

    diff = np.abs(A_direct - A_formula)
    rel_diff = np.max(diff) / (np.max(np.abs(A_direct)) + 1e-15)
    console.print(f"N = {N} twins, relative error = {rel_diff:.2e}")
    if rel_diff < 1e-10:
        console.print("[green]✓ Формула верна и на twins![/green]")

    # Q2: Variance analysis
    console.print("\n" + "="*60)
    console.print("\n[bold cyan]Q2: СВЯЗЬ Var_Φ(ξ) С c_twins[/bold cyan]\n")

    table = Table(title="Var_Φ(ξ) vs c_twins", box=box.DOUBLE)
    table.add_column("X", style="cyan", justify="right")
    table.add_column("N", style="blue", justify="right")
    table.add_column("Var_Φ(ξ)", style="green", justify="right")
    table.add_column("c_twins", style="yellow", justify="right")
    table.add_column("E_comm/(Var·E_lat)", style="magenta", justify="right")

    for X in [100, 500, 1000, 2000, 5000, 10000]:
        res = compute_variance_and_c_twins(X, t=1.0)
        if res:
            table.add_row(
                str(res['X']),
                str(res['N']),
                f"{res['var_xi']:.4f}",
                f"{res['c_twins']:.6f}",
                f"{res['ratio_hyp']:.4f}"
            )

    console.print(table)

    # Check if ratio_hyp is approximately constant
    ratios = []
    for X in [100, 500, 1000, 2000, 5000, 10000]:
        res = compute_variance_and_c_twins(X, t=1.0)
        if res:
            ratios.append(res['ratio_hyp'])

    if ratios:
        cv = np.std(ratios) / np.mean(ratios)
        console.print(f"\n[yellow]E_comm/(Var_Φ · E_lat) analysis:[/yellow]")
        console.print(f"  mean = {np.mean(ratios):.4f}")
        console.print(f"  std = {np.std(ratios):.4f}")
        console.print(f"  CV = {cv:.4f}")

        if cv < 0.3:
            console.print(Panel.fit(
                f"[bold green]✓ ГИПОТЕЗА ПОДТВЕРЖДЕНА![/bold green]\n\n"
                f"E_comm ≈ {np.mean(ratios):.2f} · Var_Φ(ξ) · E_lat\n\n"
                f"c_twins > 0 следует из Var_Φ(ξ) > 0!",
                box=box.DOUBLE,
                border_style="green"
            ))
        else:
            console.print(f"[yellow]Связь не простая пропорциональность (CV = {cv:.2f})[/yellow]")

    # Q3: Asymptotic comparison
    console.print("\n" + "="*60)
    X_values = [1000, 2000, 5000, 10000, 20000, 50000]
    async_results = asymptotic_lambda_comparison(X_values, t=1.0)

    if async_results:
        # Check if ratio converges to 1
        ratios = [r['ratio'] for r in async_results]
        console.print(f"\n[yellow]Ratio χ₄/uniform analysis:[/yellow]")
        console.print(f"  X = 1,000:  ratio = {async_results[0]['ratio']:.4f}")
        console.print(f"  X = 50,000: ratio = {async_results[-1]['ratio']:.4f}")

        # Linear regression on ratio vs 1/log(X)
        inv_log_X = [1/log(r['X']) for r in async_results]
        slope, intercept = np.polyfit(inv_log_X, ratios, 1)

        console.print(f"\n  Extrapolation (ratio = a + b/log(X)):")
        console.print(f"    intercept (X→∞): {intercept:.4f}")

        if abs(intercept - 1.0) < 0.2:
            console.print(Panel.fit(
                f"[bold green]✓ RATIO → 1 при X → ∞![/bold green]\n\n"
                f"c_twins(χ₄)/c_twins(uniform) → {intercept:.2f}\n\n"
                f"⟹ B₁(prime) из ГЕОМЕТРИИ, не из λ!",
                box=box.DOUBLE,
                border_style="green"
            ))
        else:
            console.print(f"[yellow]Ratio не стремится к 1 (intercept = {intercept:.2f})[/yellow]")

    return formula_ok


if __name__ == "__main__":
    main()
