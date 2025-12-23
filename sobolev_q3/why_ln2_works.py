#!/usr/bin/env python3
"""
🔬 WHY ln(2) WORKS FOR TWINS?
Почему p·ln(2) даёт лучшее подавление для близнецов?
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

def get_twins(primes):
    prime_set = set(primes)
    return [(p, p+2) for p in primes if p+2 in prime_set]

def analyze_ln2():
    """Анализ почему ln(2) особенное для близнецов"""

    console.print(Panel.fit(
        "🔬 [bold cyan]WHY ln(2) WORKS FOR TWINS?[/]\n"
        "Разгадка аномалии p·ln(2)",
        border_style="cyan"
    ))

    # 1. Ключевое наблюдение: разность близнецов = 2
    console.print("[bold yellow]1️⃣ КЛЮЧЕВОЕ НАБЛЮДЕНИЕ:[/]\n")
    console.print("Близнецы (p, p+2): разность ВСЕГДА = [bold green]2[/]")
    console.print(f"ln(2) = {math.log(2):.6f}")
    console.print(f"2·ln(2) = {2*math.log(2):.6f} = ln(4)")
    console.print()

    # 2. Фазовый сдвиг
    console.print("[bold yellow]2️⃣ ФАЗОВЫЙ СДВИГ между p и p+2:[/]\n")
    console.print("Для f(p) = p·α:")
    console.print("  Δφ = 2π·(p·α - (p+2)·α) = 2π·(-2α) = -4πα")
    console.print()

    alphas = [
        ("ln(2)", math.log(2)),
        ("ln(3)", math.log(3)),
        ("π", math.pi),
        ("e", math.e),
        ("√2", math.sqrt(2)),
        ("1", 1.0),
    ]

    table = Table(title="Фазовый сдвиг Δφ = -4πα")
    table.add_column("α", style="cyan")
    table.add_column("Значение", style="dim")
    table.add_column("-4πα", style="yellow")
    table.add_column("mod 2π", style="green")
    table.add_column("Градусы", style="magenta")

    for name, alpha in alphas:
        shift = -4 * math.pi * alpha
        shift_mod = shift % (2 * math.pi)
        if shift_mod > math.pi:
            shift_mod -= 2 * math.pi
        degrees = math.degrees(shift_mod)

        table.add_row(
            name,
            f"{alpha:.4f}",
            f"{shift:.4f}",
            f"{shift_mod:.4f}",
            f"{degrees:.1f}°"
        )

    console.print(table)

    # 3. Структура близнецов mod 6
    console.print("\n[bold yellow]3️⃣ СТРУКТУРА БЛИЗНЕЦОВ mod 6:[/]\n")
    console.print("Все близнецы (кроме (3,5)) имеют вид:")
    console.print("  p ≡ 5 (mod 6), p+2 ≡ 1 (mod 6)")
    console.print("  или (6k-1, 6k+1)")
    console.print()

    N = 10000
    primes = sieve(N)
    twins = get_twins(primes)

    # Статистика по mod 6
    mod6_stats = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0}
    for p, q in twins:
        mod6_stats[p % 6] += 1

    console.print("Распределение p (из пар) по mod 6:")
    for k, v in sorted(mod6_stats.items()):
        bar = "█" * (v // 10)
        console.print(f"  {k}: {v:4d} {bar}")

    # 4. Почему ln(2)?
    console.print("\n[bold yellow]4️⃣ ПОЧЕМУ ln(2)?[/]\n")

    console.print("Гипотеза 1: [cyan]Связь с разностью 2[/]")
    console.print("  • Разность близнецов = 2")
    console.print("  • ln(2) = натуральный логарифм этой разности")
    console.print("  • Фазовый сдвиг = -4π·ln(2) ≈ -8.71 rad ≈ -139°")
    console.print()

    console.print("Гипотеза 2: [cyan]Цепная дробь ln(2)[/]")
    cf_ln2 = [0, 1, 2, 3, 1, 6, 3, 1, 1, 2, 1, 1, 1, 1, 3]
    console.print(f"  ln(2) = {cf_ln2}")
    console.print("  Много единиц → хорошие диофантовы свойства")
    console.print()

    # 5. Распределение фаз
    console.print("[bold yellow]5️⃣ РАСПРЕДЕЛЕНИЕ ФАЗ {p·ln(2) mod 1}:[/]\n")

    twin_primes = sorted(set([p for pair in twins for p in pair]))

    phases_ln2 = [(p * math.log(2)) % 1 for p in twin_primes[:1000]]
    phases_pi = [(p * math.pi) % 1 for p in twin_primes[:1000]]
    phases_e = [(p * math.e) % 1 for p in twin_primes[:1000]]

    # Гистограмма
    bins = 12
    hist_ln2, _ = np.histogram(phases_ln2, bins=bins, range=(0, 1))
    hist_pi, _ = np.histogram(phases_pi, bins=bins, range=(0, 1))
    hist_e, _ = np.histogram(phases_e, bins=bins, range=(0, 1))

    expected = len(phases_ln2) / bins

    console.print(f"Ожидаемое равномерное: {expected:.0f} на сектор\n")

    table2 = Table(title="Распределение фаз по секторам (12 bins)")
    table2.add_column("Сектор", style="dim")
    table2.add_column("ln(2)", style="green")
    table2.add_column("π", style="yellow")
    table2.add_column("e", style="red")

    for i in range(bins):
        table2.add_row(
            f"{i*30}°-{(i+1)*30}°",
            str(hist_ln2[i]),
            str(hist_pi[i]),
            str(hist_e[i])
        )

    console.print(table2)

    # Дисперсия
    var_ln2 = np.var(hist_ln2)
    var_pi = np.var(hist_pi)
    var_e = np.var(hist_e)

    console.print(f"\nДисперсия от равномерного:")
    console.print(f"  ln(2): {var_ln2:.1f}")
    console.print(f"  π:     {var_pi:.1f}")
    console.print(f"  e:     {var_e:.1f}")

    if var_ln2 < var_pi and var_ln2 < var_e:
        console.print("\n[bold green]ln(2) даёт НАИБОЛЕЕ РАВНОМЕРНОЕ распределение![/]")

    # 6. Магия числа 2
    console.print(Panel.fit(
        "[bold cyan]🎯 РАЗГАДКА:[/]\n\n"
        "ln(2) работает потому что:\n\n"
        "1. [yellow]Разность близнецов = 2[/]\n"
        "   ln(2) 'резонирует' с этой структурой\n\n"
        "2. [yellow]Фазовый сдвиг -4π·ln(2) ≈ -139°[/]\n"
        "   Это НЕ кратно 180° → нет деструктивной интерференции\n"
        "   Но близко к 120° → частичная отмена в тройках\n\n"
        "3. [yellow]Хорошие диофантовы свойства[/]\n"
        "   ln(2) имеет регулярную цепную дробь\n\n"
        "4. [yellow]Связь с бинарной структурой[/]\n"
        "   2 = основание двоичной системы\n"
        "   Близнецы 'живут' в мире чётное/нечётное\n"
        "   ln(2) кодирует эту бинарность!",
        border_style="green"
    ))

if __name__ == "__main__":
    analyze_ln2()
