#!/usr/bin/env python3
"""
🔬 Q3 NUMERICAL TEST
Проверка: подавляет ли спектральный зазор Minor arcs?

Классическая оценка: |S(α)| ~ √N (random walk)
С Q3:                |S(α)| ~ N^(1/2 - ε) или log(N)?

Если Q3 работает - Minor arcs должны расти МЕДЛЕННЕЕ чем √N!
"""
import math
import numpy as np
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.progress import track

console = Console()

def sieve(n):
    """Решето Эратосфена"""
    is_prime = [True] * (n + 1)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(n**0.5) + 1):
        if is_prime[p]:
            for i in range(p*p, n + 1, p):
                is_prime[i] = False
    return [i for i in range(2, n + 1) if is_prime[i]]

def phase_sum(primes, alpha):
    """S(α) = Σ e^(2πi·p·α)"""
    x, y = 0.0, 0.0
    for p in primes:
        angle = 2 * math.pi * p * alpha
        x += math.cos(angle)
        y += math.sin(angle)
    return abs(complex(x, y))

def fit_power_law(Ns, values):
    """Fit |S| ~ N^β, return β"""
    log_N = np.log(Ns)
    log_V = np.log(values)
    # Linear regression: log(V) = β * log(N) + c
    coeffs = np.polyfit(log_N, log_V, 1)
    return coeffs[0]  # β

def test_minor_arc_scaling():
    """
    Главный тест: как |S(α)| масштабируется с N на Minor arcs?

    Если β < 0.5 → Q3 работает! (подавление сильнее чем random walk)
    Если β ≈ 0.5 → классика (random walk)
    Если β > 0.5 → аномалия
    """
    console.print(Panel.fit(
        "🔬 [bold cyan]Q3 MINOR ARC SCALING TEST[/]\n"
        "Проверяем: |S(α)| ~ N^β\n"
        "β < 0.5 → Q3 работает!\n"
        "β ≈ 0.5 → random walk (классика)\n"
        "β > 0.5 → резонанс",
        border_style="cyan"
    ))

    # Иррациональные α для Minor arcs
    minor_alphas = [
        ("√2", math.sqrt(2)),
        ("√3", math.sqrt(3)),
        ("√5", math.sqrt(5)),
        ("π", math.pi),
        ("e", math.e),
        ("1/π", 1/math.pi),
        ("1/e", 1/math.e),
        ("(√5-1)/2 (φ)", (math.sqrt(5)-1)/2),  # golden ratio
        ("ln(2)", math.log(2)),
        ("π²/10", math.pi**2/10),
    ]

    # Major arcs для сравнения
    major_alphas = [
        ("1/2", 0.5),
        ("1/3", 1/3),
        ("1/4", 0.25),
        ("1/5", 0.2),
        ("1/6", 1/6),
    ]

    # Разные размеры N
    N_values = [5000, 10000, 20000, 50000, 100000, 200000]

    console.print(f"\n[dim]Генерация простых до {max(N_values)}...[/]")
    all_primes = sieve(max(N_values))
    console.print(f"[green]✓ Всего простых: {len(all_primes)}[/]\n")

    # Результаты
    results = {}

    console.print("[bold yellow]Тестирование Minor Arcs (иррациональные α):[/]\n")

    for name, alpha in track(minor_alphas, description="Minor arcs..."):
        S_values = []
        primes_counts = []

        for N in N_values:
            primes_up_to_N = [p for p in all_primes if p <= N]
            n = len(primes_up_to_N)
            S = phase_sum(primes_up_to_N, alpha)
            S_values.append(S)
            primes_counts.append(n)

        # Fit power law
        beta = fit_power_law(np.array(primes_counts), np.array(S_values))
        results[name] = {
            'type': 'minor',
            'alpha': alpha,
            'beta': beta,
            'S_values': S_values,
            'N_values': primes_counts
        }

    console.print("\n[bold yellow]Тестирование Major Arcs (рациональные α):[/]\n")

    for name, alpha in track(major_alphas, description="Major arcs..."):
        S_values = []
        primes_counts = []

        for N in N_values:
            primes_up_to_N = [p for p in all_primes if p <= N]
            n = len(primes_up_to_N)
            S = phase_sum(primes_up_to_N, alpha)
            S_values.append(S)
            primes_counts.append(n)

        beta = fit_power_law(np.array(primes_counts), np.array(S_values))
        results[name] = {
            'type': 'major',
            'alpha': alpha,
            'beta': beta,
            'S_values': S_values,
            'N_values': primes_counts
        }

    # Таблица результатов
    console.print("\n")
    table = Table(title="🔬 РЕЗУЛЬТАТЫ: |S(α)| ~ N^β")
    table.add_column("α", style="cyan")
    table.add_column("Тип", style="yellow")
    table.add_column("β (экспонента)", style="bold")
    table.add_column("Интерпретация", style="green")
    table.add_column("|S|/√N при N=200k", style="magenta")

    minor_betas = []
    major_betas = []

    for name, data in sorted(results.items(), key=lambda x: x[1]['beta']):
        beta = data['beta']
        arc_type = "Minor" if data['type'] == 'minor' else "Major"

        # Интерпретация
        if beta < 0.4:
            interp = "🟢 СИЛЬНОЕ подавление!"
        elif beta < 0.5:
            interp = "🟡 Подавление (Q3?)"
        elif beta < 0.6:
            interp = "⚪ Random walk"
        else:
            interp = "🔴 Резонанс"

        # |S|/√N при максимальном N
        last_S = data['S_values'][-1]
        last_N = data['N_values'][-1]
        metric = last_S / math.sqrt(last_N)

        table.add_row(
            name,
            arc_type,
            f"{beta:.4f}",
            interp,
            f"{metric:.2f}"
        )

        if data['type'] == 'minor':
            minor_betas.append(beta)
        else:
            major_betas.append(beta)

    console.print(table)

    # Статистика
    avg_minor = np.mean(minor_betas)
    avg_major = np.mean(major_betas)

    console.print(Panel.fit(
        f"[bold cyan]📊 СТАТИСТИКА:[/]\n\n"
        f"Средний β для Minor arcs: [bold green]{avg_minor:.4f}[/]\n"
        f"Средний β для Major arcs: [bold red]{avg_major:.4f}[/]\n\n"
        f"[bold yellow]ВЫВОД:[/]\n"
        f"{'🟢 Q3 РАБОТАЕТ!' if avg_minor < 0.5 else '⚪ Random walk (β ≈ 0.5)'}\n"
        f"Minor arcs растут как N^{avg_minor:.3f} вместо N^0.5",
        border_style="green" if avg_minor < 0.5 else "yellow"
    ))

    # Детальный анализ лучших кандидатов
    console.print("\n[bold cyan]🎯 ЛУЧШИЕ КАНДИДАТЫ ДЛЯ Q3:[/]")
    sorted_minor = sorted([(k, v) for k, v in results.items() if v['type'] == 'minor'],
                          key=lambda x: x[1]['beta'])

    for name, data in sorted_minor[:3]:
        console.print(f"  • {name}: β = {data['beta']:.4f}")

    return results

def twin_prime_correlation_test():
    """
    Тест для близнецов: коррелированы ли фазы p и p+2?
    """
    console.print(Panel.fit(
        "👯 [bold cyan]TWIN PRIME CORRELATION TEST[/]\n"
        "Проверяем корреляцию фаз между p и p+2",
        border_style="cyan"
    ))

    N = 100000
    primes = sieve(N)
    prime_set = set(primes)
    twins = [(p, p+2) for p in primes if p+2 in prime_set]

    console.print(f"[green]✓ Пар близнецов: {len(twins)}[/]\n")

    # Для разных α измеряем корреляцию
    test_alphas = [
        ("1/π (minor)", 1/math.pi),
        ("√2 (minor)", math.sqrt(2)),
        ("1/6 (major)", 1/6),
        ("1/4 (major)", 0.25),
    ]

    table = Table(title="Корреляция фаз p ↔ p+2")
    table.add_column("α", style="cyan")
    table.add_column("Тип", style="yellow")
    table.add_column("Корреляция", style="green")
    table.add_column("Фазовый сдвиг", style="magenta")

    for name, alpha in test_alphas:
        # Корреляция: Re(Σ e^(2πi·p·α) · conj(e^(2πi·(p+2)·α)))
        # = Re(Σ e^(-2πi·2·α)) = N_twins · cos(4πα)

        correlation = 0
        for p, q in twins:
            phase_p = 2 * math.pi * p * alpha
            phase_q = 2 * math.pi * q * alpha
            # conj(e^(iφ)) = e^(-iφ)
            correlation += math.cos(phase_p - phase_q)

        correlation /= len(twins)  # нормируем
        phase_shift = (2 * alpha) % 1

        arc_type = "Minor" if "minor" in name else "Major"

        table.add_row(
            name.split()[0],
            arc_type,
            f"{correlation:.4f}",
            f"{phase_shift:.4f} ({phase_shift*360:.1f}°)"
        )

    console.print(table)

    console.print("\n[bold yellow]📊 Интерпретация:[/]")
    console.print("• Корреляция ≈ 1: фазы совпадают (конструктивная интерференция)")
    console.print("• Корреляция ≈ -1: фазы противоположны (деструктивная)")
    console.print("• Корреляция ≈ 0: фазы независимы")

def main():
    console.print(Panel.fit(
        "[bold cyan]🔬 Q3 NUMERICAL VERIFICATION[/]\n"
        "Численная проверка спектрального зазора\n"
        "для атаки на Twin Prime Conjecture",
        border_style="cyan"
    ))

    # Главный тест
    results = test_minor_arc_scaling()

    console.print("\n" + "="*60 + "\n")

    # Тест корреляции близнецов
    twin_prime_correlation_test()

    console.print(Panel.fit(
        "[bold green]✅ ЧИСЛЕННАЯ ПРОВЕРКА ЗАВЕРШЕНА[/]\n\n"
        "Если β < 0.5 на Minor arcs → Q3 подавление работает!\n"
        "Это даёт надежду на атаку Twin Prime через метод кругов.",
        border_style="green"
    ))

if __name__ == "__main__":
    main()
