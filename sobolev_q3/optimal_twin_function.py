#!/usr/bin/env python3
"""
🔬 OPTIMAL PHASE FUNCTION FOR TWIN PRIMES
Поиск функции f(p) которая даёт максимальное подавление для близнецов
"""
import math
import numpy as np
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.progress import track

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

def phase_sum(numbers, func):
    """S = Σ e^(2πi·f(n))"""
    x, y = 0.0, 0.0
    for n in numbers:
        try:
            val = func(n)
            angle = 2 * math.pi * val
            x += math.cos(angle)
            y += math.sin(angle)
        except:
            pass
    return complex(x, y)

def fit_beta(primes_list, func):
    """Fit |S| ~ N^β for different N cutoffs"""
    N_values = [5000, 10000, 20000, 50000, 100000]
    S_vals = []
    n_vals = []

    for N in N_values:
        primes_N = [p for p in primes_list if p <= N]
        if len(primes_N) < 10:
            continue
        S = abs(phase_sum(primes_N, func))
        if S > 0:
            S_vals.append(S)
            n_vals.append(len(primes_N))

    if len(S_vals) < 3:
        return float('inf')

    try:
        beta = np.polyfit(np.log(n_vals), np.log(S_vals), 1)[0]
        return beta
    except:
        return float('inf')

def search_optimal():
    """Поиск оптимальной функции"""

    console.print(Panel.fit(
        "🔬 [bold cyan]OPTIMAL PHASE FUNCTION SEARCH[/]\n"
        "Ищем f(p) которая даёт минимальный β для близнецов",
        border_style="cyan"
    ))

    N = 200000
    all_primes = sieve(N)
    twins = get_twins(all_primes)
    twin_primes = sorted(set([p for pair in twins for p in pair]))

    console.print(f"[dim]Простых: {len(all_primes)}, Twin primes: {len(twin_primes)}[/]\n")

    # Кандидаты функций
    candidates = [
        # Базовые
        ("p", lambda p: p),
        ("p²", lambda p: p*p),
        ("√p", lambda p: math.sqrt(p)),
        ("ln(p)", lambda p: math.log(p)),
        ("p·ln(p)", lambda p: p * math.log(p)),

        # Константы
        ("p·e", lambda p: p * math.e),
        ("p·π", lambda p: p * math.pi),
        ("p·φ", lambda p: p * (1 + math.sqrt(5))/2),
        ("p·√2", lambda p: p * math.sqrt(2)),
        ("p·√3", lambda p: p * math.sqrt(3)),

        # Обратные
        ("p/ln(p)", lambda p: p / math.log(p)),
        ("p/√p", lambda p: p / math.sqrt(p)),
        ("ln(p)/p", lambda p: math.log(p) / p),

        # Комбинации с ln
        ("p·ln²(p)", lambda p: p * math.log(p)**2),
        ("p·√ln(p)", lambda p: p * math.sqrt(math.log(p))),
        ("p/ln²(p)", lambda p: p / math.log(p)**2),
        ("√(p·ln(p))", lambda p: math.sqrt(p * math.log(p))),
        ("p·ln(ln(p))", lambda p: p * math.log(math.log(p)) if p > 3 else 0),

        # Степени
        ("p^1.5", lambda p: p**1.5),
        ("p^0.75", lambda p: p**0.75),
        ("p^0.5·ln(p)", lambda p: math.sqrt(p) * math.log(p)),

        # Экзотические
        ("p·e^(-1/p)", lambda p: p * math.exp(-1/p)),
        ("p·(1-1/ln(p))", lambda p: p * (1 - 1/math.log(p)) if p > 3 else p),
        ("p²/ln(p)", lambda p: p*p / math.log(p)),
        ("sin(p)", lambda p: math.sin(p)),
        ("p·sin(1/p)", lambda p: p * math.sin(1/p)),

        # Связанные с простыми
        ("p·π(p)", lambda p: p * sum(1 for q in all_primes if q <= p)),  # медленно
        ("p·ln(p)·ln(ln(p))", lambda p: p * math.log(p) * math.log(math.log(p)) if p > 10 else 0),

        # Рациональные приближения π
        ("p·22/7", lambda p: p * 22/7),
        ("p·355/113", lambda p: p * 355/113),

        # Другие константы
        ("p·ln(2)", lambda p: p * math.log(2)),
        ("p·ln(3)", lambda p: p * math.log(3)),
        ("p/e", lambda p: p / math.e),
        ("p/π", lambda p: p / math.pi),

        # Гармонические
        ("p·H_p", lambda p: p * sum(1/k for k in range(1, min(int(p), 100)+1))),
    ]

    # Тестируем каждую функцию
    console.print("[bold yellow]Тестирование функций...[/]\n")

    results = []

    for name, func in track(candidates, description="Testing..."):
        try:
            # Для близнецов
            S_twin = abs(phase_sum(twin_primes, func))
            metric_twin = S_twin / math.sqrt(len(twin_primes))

            # Для всех простых (для сравнения)
            S_all = abs(phase_sum(all_primes[:10000], func))  # только первые 10k для скорости
            metric_all = S_all / math.sqrt(10000)

            # Ratio
            ratio = metric_twin / metric_all if metric_all > 0.01 else float('inf')

            # Beta для близнецов
            beta = fit_beta(twin_primes, func)

            results.append({
                'name': name,
                'metric_twin': metric_twin,
                'metric_all': metric_all,
                'ratio': ratio,
                'beta': beta
            })
        except Exception as e:
            pass

    # Сортируем по метрике для близнецов
    results.sort(key=lambda x: x['metric_twin'])

    # Таблица топ-20 по |S|/√N
    console.print("\n[bold green]🏆 ТОП-20 по минимальному |S|/√N для близнецов:[/]\n")

    table = Table(title="Лучшие функции для Twin Primes")
    table.add_column("#", style="dim")
    table.add_column("f(p)", style="cyan")
    table.add_column("|S|/√N twin", style="green")
    table.add_column("|S|/√N all", style="yellow")
    table.add_column("Ratio", style="magenta")
    table.add_column("β twin", style="bold")

    for i, r in enumerate(results[:20]):
        beta_str = f"{r['beta']:.3f}" if r['beta'] != float('inf') else "—"
        ratio_str = f"{r['ratio']:.2f}x" if r['ratio'] != float('inf') else "—"

        table.add_row(
            str(i+1),
            r['name'],
            f"{r['metric_twin']:.4f}",
            f"{r['metric_all']:.4f}",
            ratio_str,
            beta_str
        )

    console.print(table)

    # Сортируем по β
    results_beta = sorted([r for r in results if r['beta'] != float('inf')], key=lambda x: x['beta'])

    console.print("\n[bold green]🏆 ТОП-10 по минимальному β для близнецов:[/]\n")

    table2 = Table(title="Лучшие функции по экспоненте β")
    table2.add_column("#", style="dim")
    table2.add_column("f(p)", style="cyan")
    table2.add_column("β twin", style="green")
    table2.add_column("|S|/√N", style="yellow")

    for i, r in enumerate(results_beta[:10]):
        table2.add_row(
            str(i+1),
            r['name'],
            f"{r['beta']:.4f}",
            f"{r['metric_twin']:.4f}"
        )

    console.print(table2)

    # Победитель
    winner = results[0]
    winner_beta = results_beta[0] if results_beta else None

    console.print(Panel.fit(
        f"[bold green]🥇 ПОБЕДИТЕЛЬ по |S|/√N:[/]\n"
        f"   {winner['name']}\n"
        f"   |S|/√N = {winner['metric_twin']:.4f}\n\n"
        f"[bold cyan]🥇 ПОБЕДИТЕЛЬ по β:[/]\n"
        f"   {winner_beta['name'] if winner_beta else '—'}\n"
        f"   β = {winner_beta['beta']:.4f if winner_beta else 0:.4f}",
        border_style="green"
    ))

    return results

if __name__ == "__main__":
    results = search_optimal()
