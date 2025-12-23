#!/usr/bin/env python3
"""
🔬 ln(p) PHASE TEST
Проверка фазового блуждания с ln(p) - прямая связь с простыми!
"""
import math
import numpy as np
from rich.console import Console
from rich.table import Table
from rich.panel import Panel

console = Console()

def sieve(n):
    is_prime = [True] * (n + 1)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(n**0.5) + 1):
        if is_prime[p]:
            for i in range(p*p, n + 1, p):
                is_prime[i] = False
    return [i for i in range(2, n + 1) if is_prime[i]]

def phase_sum_ln(primes, mode="ln_p"):
    """
    Разные варианты фазового блуждания с ln:
    - "ln_p": фаза = 2π·ln(p)
    - "p_ln_p": фаза = 2π·p·ln(p)
    - "ln_p_over_p": фаза = 2π·ln(p)/p
    - "sqrt_p": фаза = 2π·√p
    """
    x, y = 0.0, 0.0
    for p in primes:
        if mode == "ln_p":
            angle = 2 * math.pi * math.log(p)
        elif mode == "p_ln_p":
            angle = 2 * math.pi * p * math.log(p)
        elif mode == "ln_p_over_p":
            angle = 2 * math.pi * math.log(p) / p
        elif mode == "sqrt_p":
            angle = 2 * math.pi * math.sqrt(p)
        elif mode == "p_over_ln_p":
            angle = 2 * math.pi * p / math.log(p)
        elif mode == "chebyshev":
            # θ(p) = ln(p), сумма по простым
            angle = 2 * math.pi * math.log(p)
        else:
            angle = 2 * math.pi * p * mode  # mode как α
        x += math.cos(angle)
        y += math.sin(angle)
    return complex(x, y)

def test_ln_variants():
    """Тест разных вариантов с ln"""

    console.print(Panel.fit(
        "🔬 [bold cyan]ln(p) PHASE WALK TEST[/]\n"
        "Прямая связь между фазами и логарифмами простых",
        border_style="cyan"
    ))

    N_values = [5000, 10000, 20000, 50000, 100000, 200000]
    all_primes = sieve(max(N_values))

    modes = [
        ("ln(p)", "ln_p", "Фаза = 2π·ln(p)"),
        ("p·ln(p)", "p_ln_p", "Фаза = 2π·p·ln(p)"),
        ("√p", "sqrt_p", "Фаза = 2π·√p"),
        ("p/ln(p)", "p_over_ln_p", "Фаза = 2π·p/ln(p)"),
    ]

    console.print("\n[bold yellow]Сравнение разных функций фазы:[/]\n")

    for name, mode, desc in modes:
        console.print(f"[cyan]{name}[/]: {desc}")

        table = Table(title=f"|S| для фазы = {name}")
        table.add_column("N", style="cyan")
        table.add_column("# простых", style="dim")
        table.add_column("|S|", style="yellow")
        table.add_column("|S|/√n", style="green")
        table.add_column("|S|/n", style="magenta")

        S_values = []
        n_values = []

        for N in N_values:
            primes_N = [p for p in all_primes if p <= N]
            n = len(primes_N)
            S = abs(phase_sum_ln(primes_N, mode))

            S_values.append(S)
            n_values.append(n)

            table.add_row(
                str(N),
                str(n),
                f"{S:.2f}",
                f"{S/math.sqrt(n):.4f}",
                f"{S/n:.6f}"
            )

        console.print(table)

        # Fit power law
        log_n = np.log(n_values)
        log_S = np.log(S_values)
        beta = np.polyfit(log_n, log_S, 1)[0]
        console.print(f"[bold]β (экспонента): {beta:.4f}[/]")

        if beta < 0.3:
            console.print("[green]→ СИЛЬНОЕ подавление![/]")
        elif beta < 0.5:
            console.print("[yellow]→ Подавление (Q3?)[/]")
        elif beta < 0.7:
            console.print("[white]→ Random walk[/]")
        else:
            console.print("[red]→ Резонанс[/]")

        console.print()

    # Специальный тест: сравнение с Чебышёвым
    console.print(Panel.fit(
        "[bold cyan]🎯 СВЯЗЬ С ФУНКЦИЕЙ ЧЕБЫШЁВА[/]\n\n"
        "θ(x) = Σ ln(p) для p ≤ x\n"
        "ψ(x) = Σ ln(p) для p^k ≤ x\n\n"
        "Наш тест: S = Σ e^(2πi·ln(p))\n"
        "Это как 'осциллирующая' версия θ(x)!",
        border_style="yellow"
    ))

    # Явная формула связи
    console.print("\n[bold yellow]Явная формула (Riemann-von Mangoldt):[/]")
    console.print("ψ(x) = x - Σ x^ρ/ρ - ln(2π) - ½ln(1-x⁻²)")
    console.print("       ^     ^")
    console.print("   главный  осцилляции от нулей ζ(s)")
    console.print("    член")
    console.print()
    console.print("[bold green]Наше S = Σ e^(2πi·ln(p)) — это Фурье-образ этих осцилляций![/]")

def compare_with_standard():
    """Сравнение ln(p) с обычным α·p"""

    console.print(Panel.fit(
        "📊 [bold cyan]СРАВНЕНИЕ: ln(p) vs α·p[/]",
        border_style="cyan"
    ))

    N = 100000
    primes = sieve(N)
    n = len(primes)
    sqrt_n = math.sqrt(n)

    comparisons = [
        ("ln(p)", "ln_p"),
        ("e·p", math.e),
        ("π·p", math.pi),
        ("√2·p", math.sqrt(2)),
        ("(1/e)·p", 1/math.e),
    ]

    table = Table(title="Сравнение разных фазовых функций")
    table.add_column("Фаза", style="cyan")
    table.add_column("|S|", style="yellow")
    table.add_column("|S|/√n", style="green")
    table.add_column("Ранг", style="bold")

    results = []
    for name, mode in comparisons:
        if isinstance(mode, str):
            S = abs(phase_sum_ln(primes, mode))
        else:
            S = abs(phase_sum_ln(primes, mode))
        results.append((name, S, S/sqrt_n))

    # Сортируем по |S|/√n
    results.sort(key=lambda x: x[2])

    for i, (name, S, metric) in enumerate(results):
        table.add_row(name, f"{S:.2f}", f"{metric:.4f}", f"#{i+1}")

    console.print(table)

    console.print(Panel.fit(
        "[bold green]🎯 ВЫВОД:[/]\n\n"
        "Если ln(p) даёт меньший |S|/√n чем e·p,\n"
        "то есть ГЛУБОКАЯ связь между:\n"
        "• Логарифмами простых чисел\n"
        "• Числом e\n"
        "• Распределением фаз\n\n"
        "Это может быть ключом к Q3!",
        border_style="green"
    ))

if __name__ == "__main__":
    test_ln_variants()
    console.print("\n" + "="*60 + "\n")
    compare_with_standard()
