#!/usr/bin/env python3
"""
Спектральный анализ симметризованного оператора B.

B = i·[F, U₂]·χ₄ + (i·[F, U₂]·χ₄)†

Теорема:
  ⟨g_X, B g_X⟩ = 4·S₂(X)  (вещественное!)

Вопрос: λ_min(B|_{prime}) > 0?
Если да — это FORCING для S₂ → ∞!
"""

import numpy as np
from sympy import isprime, primerange
from rich.console import Console
from rich.table import Table
import scipy.linalg as la

console = Console()

def chi4(n: int) -> int:
    """Характер χ_4 mod 4"""
    if n % 2 == 0:
        return 0
    elif n % 4 == 1:
        return 1
    else:
        return -1

def e(x: float) -> complex:
    """e(x) = exp(2πix)"""
    return np.exp(2j * np.pi * x)

def von_mangoldt(n: int) -> float:
    """Λ(n) = log p if n = p^k, else 0"""
    if n < 2:
        return 0.0
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            k = 0
            m = n
            while m % p == 0:
                m //= p
                k += 1
            if m == 1:
                return np.log(p)
            else:
                return 0.0
    return np.log(n)

def get_primes(X: int) -> list:
    """Список простых до X"""
    return list(primerange(2, X + 1))

def get_twins(X: int) -> list:
    """Список младших элементов twin pairs до X"""
    twins = []
    for p in primerange(3, X):
        if isprime(p + 2) and p + 2 <= X:
            twins.append(p)
    return twins

def compute_S2(X: int) -> float:
    """S₂(X) = Σ Λ(p)Λ(p+2) для twin pairs"""
    twins = get_twins(X)
    S2 = sum(von_mangoldt(p) * von_mangoldt(p + 2) for p in twins)
    return S2

def build_B_matrix_on_primes(X: int) -> np.ndarray:
    """
    Строит матрицу B на подпространстве простых чисел.

    B = i·[F, U₂]·χ₄ + h.c.

    [F, U₂]·χ₄ |n⟩ = -2·χ₄(n)·e(n/4) |n+2⟩

    На prime-basis {|p⟩}:
    B_{p,q} = ⟨p| B |q⟩
    """
    primes = get_primes(X)
    N = len(primes)
    prime_to_idx = {p: i for i, p in enumerate(primes)}

    # Матрица A = i·[F, U₂]·χ₄
    A = np.zeros((N, N), dtype=complex)

    for j, q in enumerate(primes):
        # A |q⟩ = i · (-2·χ₄(q)·e(q/4)) |q+2⟩
        coeff = 1j * (-2) * chi4(q) * e(q / 4)
        target = q + 2
        if target in prime_to_idx:
            i = prime_to_idx[target]
            A[i, j] = coeff

    # B = A + A†
    B = A + A.conj().T

    return B, primes

def verify_expectation(X: int):
    """
    Проверка: ⟨g_X, B g_X⟩ = 4·S₂(X)
    """
    B, primes = build_B_matrix_on_primes(X)

    # g_X = Σ_p Λ(p) |p⟩
    g = np.array([von_mangoldt(p) for p in primes])

    # ⟨g, B g⟩
    expectation = np.real(g @ B @ g)

    # 4·S₂
    S2 = compute_S2(X)
    theory = 4 * S2

    return expectation, theory, S2

def analyze_spectrum(X: int):
    """
    Спектральный анализ B на prime-подпространстве.
    """
    B, primes = build_B_matrix_on_primes(X)

    # Eigenvalues
    eigenvalues = la.eigvalsh(B)  # B эрмитова

    lambda_min = eigenvalues[0]
    lambda_max = eigenvalues[-1]

    # Норма g
    g = np.array([von_mangoldt(p) for p in primes])
    g_norm_sq = np.sum(g**2)

    # ⟨g, B g⟩
    expectation = np.real(g @ B @ g)

    return {
        'eigenvalues': eigenvalues,
        'lambda_min': lambda_min,
        'lambda_max': lambda_max,
        'g_norm_sq': g_norm_sq,
        'expectation': expectation,
        'num_primes': len(primes)
    }

def main():
    console.print("\n[bold cyan]═══ SPECTRAL ANALYSIS OF B OPERATOR ═══[/bold cyan]\n")
    console.print("[yellow]B = i·[F, U₂]·χ₄ + h.c.[/yellow]\n")

    # Часть 1: Проверка ⟨g, B g⟩ = 4·S₂
    console.print("[bold green]ЧАСТЬ 1: Проверка expectation value[/bold green]\n")

    table1 = Table(title="⟨g_X, B g_X⟩ vs 4·S₂(X)")
    table1.add_column("X", style="cyan")
    table1.add_column("⟨g, B g⟩", style="yellow")
    table1.add_column("4·S₂(X)", style="magenta")
    table1.add_column("Ratio", style="green")
    table1.add_column("Match", style="blue")

    for X in [100, 200, 500, 1000]:
        exp, theory, S2 = verify_expectation(X)
        ratio = exp / theory if theory != 0 else 0
        match = "✅" if abs(ratio - 1) < 0.01 else "❌"
        table1.add_row(
            str(X),
            f"{exp:.2f}",
            f"{theory:.2f}",
            f"{ratio:.6f}",
            match
        )

    console.print(table1)

    # Часть 2: Спектральный анализ
    console.print("\n[bold green]ЧАСТЬ 2: Спектральный анализ B[/bold green]\n")

    table2 = Table(title="Eigenvalues of B on prime subspace")
    table2.add_column("X", style="cyan")
    table2.add_column("# primes", style="green")
    table2.add_column("λ_min", style="red")
    table2.add_column("λ_max", style="blue")
    table2.add_column("||g||²", style="yellow")
    table2.add_column("⟨g,Bg⟩/||g||²", style="magenta")

    X_values = [50, 100, 200, 500, 1000, 2000]

    results = []
    for X in X_values:
        res = analyze_spectrum(X)
        results.append(res)

        rayleigh = res['expectation'] / res['g_norm_sq'] if res['g_norm_sq'] > 0 else 0

        table2.add_row(
            str(X),
            str(res['num_primes']),
            f"{res['lambda_min']:.4f}",
            f"{res['lambda_max']:.4f}",
            f"{res['g_norm_sq']:.2f}",
            f"{rayleigh:.4f}"
        )

    console.print(table2)

    # Часть 3: Анализ λ_min
    console.print("\n[bold green]ЧАСТЬ 3: Анализ λ_min(B)[/bold green]\n")

    table3 = Table(title="λ_min scaling")
    table3.add_column("X", style="cyan")
    table3.add_column("λ_min", style="red")
    table3.add_column("λ_min > 0?", style="green")
    table3.add_column("# negative eigs", style="yellow")

    for X, res in zip(X_values, results):
        num_neg = np.sum(res['eigenvalues'] < -1e-10)
        is_pos = "✅" if res['lambda_min'] > -1e-10 else "❌"
        table3.add_row(
            str(X),
            f"{res['lambda_min']:.6f}",
            is_pos,
            str(num_neg)
        )

    console.print(table3)

    # Часть 4: Вывод
    console.print("\n[bold cyan]═══ ВЫВОД ═══[/bold cyan]")

    # Проверим знак λ_min
    last_res = results[-1]
    if last_res['lambda_min'] > 1e-10:
        console.print("""
[green]✅ λ_min(B) > 0 на prime-подпространстве![/green]

Это значит:
  ⟨g, B g⟩ ≥ λ_min · ||g||²
  4·S₂ ≥ λ_min · ||g||²
  S₂ ≥ (λ_min/4) · ||g||²

Если λ_min = const > 0, а ||g||² ~ X·log(X),
то S₂ → ∞ — это FORCING!
""")
    elif last_res['lambda_min'] < -1e-10:
        console.print("""
[red]❌ λ_min(B) < 0 — B НЕ положительно определена![/red]

Это означает что B ≥ 0 НЕ выполняется.
Нужен другой подход для forcing.
""")
    else:
        console.print("""
[yellow]⚠️ λ_min(B) ≈ 0 — B положительно полуопределена[/yellow]

Есть нулевые собственные значения.
Нужно понять структуру ядра ker(B).
""")

    # Дополнительный анализ: распределение eigenvalues
    console.print("\n[bold green]ЧАСТЬ 4: Распределение eigenvalues[/bold green]\n")

    res = analyze_spectrum(1000)
    eigs = res['eigenvalues']

    console.print(f"X = 1000, всего {len(eigs)} eigenvalues:")
    console.print(f"  Положительных: {np.sum(eigs > 1e-10)}")
    console.print(f"  Около нуля: {np.sum(np.abs(eigs) < 1e-10)}")
    console.print(f"  Отрицательных: {np.sum(eigs < -1e-10)}")
    console.print(f"  λ_min = {eigs[0]:.6f}")
    console.print(f"  λ_max = {eigs[-1]:.6f}")

    # Гистограмма eigenvalues
    console.print(f"\n  5 smallest: {eigs[:5]}")
    console.print(f"  5 largest: {eigs[-5:]}")

if __name__ == "__main__":
    main()
