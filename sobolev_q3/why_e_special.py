#!/usr/bin/env python3
"""
🔬 WHY IS e SPECIAL?
Почему α = e даёт β ≈ 0.009 (почти константный |S|)?
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

def phase_sum(primes, alpha):
    x, y = 0.0, 0.0
    for p in primes:
        angle = 2 * math.pi * p * alpha
        x += math.cos(angle)
        y += math.sin(angle)
    return complex(x, y)

def phase_distribution(primes, alpha, bins=36):
    """Распределение фаз {p·α mod 1} по секторам окружности"""
    phases = [(p * alpha) % 1 for p in primes]
    hist, _ = np.histogram(phases, bins=bins, range=(0, 1))
    return hist

def test_e_mystery():
    """Детальный анализ почему e особенное"""

    console.print(Panel.fit(
        "🔬 [bold cyan]ПОЧЕМУ e ДАЁТ β ≈ 0?[/]\n"
        "Исследуем аномалию числа Эйлера",
        border_style="cyan"
    ))

    N = 100000
    primes = sieve(N)
    n = len(primes)
    sqrt_n = math.sqrt(n)

    console.print(f"[dim]Простых до {N}: {n}[/]\n")

    # 1. Сравним e с родственными константами
    console.print("[bold yellow]1️⃣ Сравнение e с родственными константами:[/]\n")

    related_alphas = [
        ("e", math.e),
        ("e - 2", math.e - 2),           # дробная часть e
        ("e²", math.e ** 2),
        ("e³", math.e ** 3),
        ("√e", math.sqrt(math.e)),
        ("1/e", 1/math.e),
        ("ln(2)", math.log(2)),
        ("ln(3)", math.log(3)),
        ("ln(π)", math.log(math.pi)),
        ("e·π", math.e * math.pi),
        ("e/π", math.e / math.pi),
        ("e + π", math.e + math.pi),
    ]

    table = Table(title="Родственники e")
    table.add_column("α", style="cyan")
    table.add_column("Значение", style="dim")
    table.add_column("|S|", style="yellow")
    table.add_column("|S|/√N", style="green")

    for name, alpha in related_alphas:
        S = phase_sum(primes, alpha)
        table.add_row(
            name,
            f"{alpha:.6f}",
            f"{abs(S):.2f}",
            f"{abs(S)/sqrt_n:.4f}"
        )

    console.print(table)

    # 2. Проверим распределение фаз
    console.print("\n[bold yellow]2️⃣ Распределение фаз {p·α mod 1}:[/]\n")

    test_alphas = [
        ("e", math.e),
        ("π", math.pi),
        ("√2", math.sqrt(2)),
        ("φ (golden)", (math.sqrt(5)+1)/2),
    ]

    for name, alpha in test_alphas:
        dist = phase_distribution(primes, alpha, bins=12)
        expected = n / 12  # равномерное распределение

        # Дисперсия от равномерного
        variance = np.var(dist)
        chi_sq = sum((d - expected)**2 / expected for d in dist)

        console.print(f"[cyan]{name}[/]: variance={variance:.1f}, χ²={chi_sq:.2f}")
        console.print(f"  Распределение: {list(dist)}")
        console.print()

    # 3. Цепные дроби
    console.print("[bold yellow]3️⃣ Цепные дроби (ключ к загадке!):[/]\n")

    def continued_fraction(x, n_terms=15):
        """Вычислить цепную дробь"""
        cf = []
        for _ in range(n_terms):
            cf.append(int(x))
            x = x - int(x)
            if x < 1e-10:
                break
            x = 1/x
        return cf

    cf_alphas = [
        ("e", math.e),
        ("π", math.pi),
        ("√2", math.sqrt(2)),
        ("φ", (math.sqrt(5)+1)/2),
        ("e²", math.e**2),
    ]

    for name, alpha in cf_alphas:
        cf = continued_fraction(alpha)
        console.print(f"[cyan]{name}[/] = {cf}")

    console.print("\n[bold magenta]📊 ПАТТЕРН e:[/]")
    console.print("e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, ...]")
    console.print("Паттерн: [2; 1, 2k, 1, 1, 2(k+1), 1, ...]")
    console.print("Это РЕГУЛЯРНЫЙ паттерн! Редкость среди трансцендентных чисел.")

    # 4. Проверка на разных N
    console.print("\n[bold yellow]4️⃣ |S(e)| при разных N:[/]\n")

    N_values = [1000, 2000, 5000, 10000, 20000, 50000, 100000, 200000]
    all_primes = sieve(max(N_values))

    table2 = Table(title="|S(e)| vs N")
    table2.add_column("N", style="cyan")
    table2.add_column("# простых", style="dim")
    table2.add_column("|S(e)|", style="yellow")
    table2.add_column("|S(e)|/√n", style="green")
    table2.add_column("|S(π)|/√n", style="red")

    for N in N_values:
        primes_N = [p for p in all_primes if p <= N]
        n = len(primes_N)
        S_e = abs(phase_sum(primes_N, math.e))
        S_pi = abs(phase_sum(primes_N, math.pi))

        table2.add_row(
            str(N),
            str(n),
            f"{S_e:.2f}",
            f"{S_e/math.sqrt(n):.4f}",
            f"{S_pi/math.sqrt(n):.4f}"
        )

    console.print(table2)

    # 5. Гипотеза
    console.print(Panel.fit(
        "[bold cyan]🎯 ГИПОТЕЗА: Почему e особенное?[/]\n\n"
        "1. [yellow]Цепная дробь e имеет РЕГУЛЯРНЫЙ паттерн[/]\n"
        "   e = [2; 1,2,1, 1,4,1, 1,6,1, ...]\n"
        "   Это редкость! π, √2, φ имеют хаотичные CF.\n\n"
        "2. [yellow]Связь с ln и простыми[/]\n"
        "   π(x) ~ x/ln(x), где ln = log_e\n"
        "   Может быть скрытый резонанс/антирезонанс?\n\n"
        "3. [yellow]Теорема Виноградова-Коробова[/]\n"
        "   Для 'хорошо приближаемых' α отмена лучше.\n"
        "   Регулярная CF e может давать оптимальную отмену!\n\n"
        "4. [red]Нужна проверка![/]\n"
        "   Это может быть статфлуктуация на малых N.",
        border_style="green"
    ))

if __name__ == "__main__":
    test_e_mystery()
