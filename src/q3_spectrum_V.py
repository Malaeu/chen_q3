#!/usr/bin/env python3
"""
Q3 Spectrum Analysis: Eigenvalues of V_K
=========================================
Шаг 1: Вычисляем спектр V_K напрямую.
Проверяем: λ_n(V) ~ n^{-β} и связь β с α.

Если Tr(e^{-τA²}V) ~ τ^{-α}, то по Tauberian:
- Спектр V должен иметь определённую структуру
- λ_n ~ n^{-1/α} или похожий power law
"""

import numpy as np
from scipy.special import digamma
from scipy.linalg import expm
from scipy.stats import linregress
import matplotlib.pyplot as plt
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich import box

console = Console()


def a_star(xi):
    z = 0.25 + 1j * np.pi * xi
    return 2 * np.pi * (np.log(np.pi) - np.real(digamma(z)))


def Phi_Fejer_heat(xi, B, t):
    xi = np.asarray(xi)
    result = np.zeros_like(xi, dtype=float)
    mask = np.abs(xi) <= B
    if np.any(mask):
        fejer = np.maximum(0, 1 - np.abs(xi[mask]) / B)
        heat = np.exp(-4 * np.pi**2 * t * xi[mask]**2)
        result[mask] = fejer * heat
    return result


def sieve_primes(n_max):
    n_max = min(n_max, 50_000_000)
    if n_max < 2:
        return []
    sieve = [True] * (n_max + 1)
    sieve[0] = sieve[1] = False
    for x in range(2, int(n_max**0.5) + 1):
        if sieve[x]:
            for i in range(x * x, n_max + 1, x):
                sieve[i] = False
    return [x for x in range(2, n_max + 1) if sieve[x]]


def build_operators(K, M, t_heat):
    """Строит H, A², V и возвращает всё."""
    B = K

    # Grid для T_A
    N_grid = 3000
    xi_grid = np.linspace(-B, B, N_grid)
    dxi = xi_grid[1] - xi_grid[0]
    a_vals = a_star(xi_grid)
    phi_vals = Phi_Fejer_heat(xi_grid, B, t_heat)

    # T_A (Toeplitz)
    A_coeffs = []
    for k in range(M):
        integrand = a_vals * phi_vals * np.cos(k * xi_grid)
        A_coeffs.append(np.trapezoid(integrand, dx=dxi))

    T_A = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            T_A[i, j] = A_coeffs[abs(i - j)]

    # Простые
    n_max = int(np.exp(2 * np.pi * K)) + 1
    primes = sieve_primes(n_max)

    primes_in_compact = []
    for p in primes:
        xi_p = np.log(p) / (2 * np.pi)
        if abs(xi_p) <= K:
            primes_in_compact.append(p)

    # T_P
    T_P = np.zeros((M, M))
    for p in primes_in_compact:
        xi_p = np.log(p) / (2 * np.pi)
        w_p = 2 * np.log(p) / np.sqrt(p)
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t_heat)[0]
        cos_vec = np.array([np.cos(k * xi_p) for k in range(M)])
        T_P += w_p * phi_p * np.outer(cos_vec, cos_vec)

    H = T_A - T_P

    # Близнецы
    prime_set = set(primes_in_compact)
    twins = [(p, p+2) for p in primes_in_compact if p+2 in prime_set]

    # A² = H⊗I + I⊗H
    I = np.eye(M)
    A2 = np.kron(H, I) + np.kron(I, H)

    # V для близнецов
    V = np.zeros((M * M, M * M))
    for p, q in twins:
        xi_p = np.log(p) / (2 * np.pi)
        xi_q = np.log(q) / (2 * np.pi)
        w_p = 2 * np.log(p) / np.sqrt(p)
        w_q = 2 * np.log(q) / np.sqrt(q)
        phi_p = Phi_Fejer_heat(np.array([xi_p]), B, t_heat)[0]
        phi_q = Phi_Fejer_heat(np.array([xi_q]), B, t_heat)[0]
        v_p = np.array([np.cos(k * xi_p) for k in range(M)])
        v_q = np.array([np.cos(k * xi_q) for k in range(M)])
        v_pq = np.kron(v_p, v_q)
        V += w_p * w_q * phi_p * phi_q * np.outer(v_pq, v_pq)

    return {
        'H': H,
        'A2': A2,
        'V': V,
        'n_primes': len(primes_in_compact),
        'n_twins': len(twins),
    }


def analyze_V_spectrum(K, M=18, t_heat=3.0):
    """Анализ спектра V_K."""
    console.print(f"\n[bold cyan]═══ Спектр V для K = {K} ═══[/bold cyan]")

    data = build_operators(K, M, t_heat)
    V = data['V']

    console.print(f"  Близнецов: {data['n_twins']}")
    console.print(f"  Размер V: {V.shape}")

    # Собственные значения V
    eigs_V = np.linalg.eigvalsh(V)
    eigs_V = np.sort(eigs_V)[::-1]  # По убыванию

    # Отбрасываем почти нулевые
    threshold = 1e-12 * np.max(np.abs(eigs_V))
    eigs_pos = eigs_V[eigs_V > threshold]

    console.print(f"  Ненулевых λ(V): {len(eigs_pos)}")
    console.print(f"  max λ(V) = {eigs_pos[0]:.4e}")
    console.print(f"  min λ(V) = {eigs_pos[-1]:.4e}" if len(eigs_pos) > 0 else "")

    # Ранг V = число близнецов (каждый добавляет rank-1)
    console.print(f"  rank(V) ≈ {np.sum(eigs_V > threshold)} (ожидаем ≤ {data['n_twins']})")

    # Power-law fit: λ_n ~ n^{-β}
    if len(eigs_pos) >= 5:
        n_vals = np.arange(1, len(eigs_pos) + 1)
        log_n = np.log(n_vals)
        log_lambda = np.log(eigs_pos)

        # Fit на всех
        slope, intercept, r, p, se = linregress(log_n, log_lambda)
        beta = -slope

        console.print(f"  [green]λ_n ~ n^{{-β}}: β = {beta:.3f} ± {se:.3f}, R² = {r**2:.4f}[/green]")
    else:
        beta = None
        console.print(f"  [yellow]Мало данных для fit[/yellow]")

    return {
        'K': K,
        'n_twins': data['n_twins'],
        'eigs_V': eigs_pos,
        'beta': beta,
        'A2': data['A2'],
        'V': V,
    }


def compute_alpha_from_heat(A2, V, tau_range):
    """Вычисляет α из heat trace."""
    traces = []
    for tau in tau_range:
        heat = expm(-tau * A2)
        tr = abs(np.trace(heat @ V))
        traces.append(tr)

    # Fit на хвосте τ ≥ 1
    mask = np.array(tau_range) >= 1.0
    if np.sum(mask) >= 2:
        log_tau = np.log(np.array(tau_range)[mask])
        log_tr = np.log(np.array(traces)[mask] + 1e-30)
        slope, intercept, r, p, se = linregress(log_tau, log_tr)
        alpha = -slope
        r2 = r**2
    else:
        alpha = None
        r2 = None

    return alpha, r2, traces


def main():
    console.print(Panel.fit(
        "[bold magenta]Q3: СПЕКТР V_K И СВЯЗЬ С α[/bold magenta]\n"
        "[dim]Проверяем: λ_n(V) ~ n^{-β} и β ↔ α[/dim]",
        box=box.DOUBLE
    ))

    M = 18
    t_heat = 3.0
    K_values = [0.5, 1.0, 1.5, 2.0]
    tau_range = np.array([0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0])

    results = []

    for K in K_values:
        res = analyze_V_spectrum(K, M, t_heat)

        if res['n_twins'] >= 3:
            # Вычисляем α
            alpha, r2, traces = compute_alpha_from_heat(res['A2'], res['V'], tau_range)
            res['alpha'] = alpha
            res['r2'] = r2
            res['traces'] = traces

            if alpha is not None:
                console.print(f"  [cyan]α (heat trace) = {alpha:.3f}, R² = {r2:.4f}[/cyan]")

                # Теоретическая связь: если Tr ~ τ^{-α}, спектр V ~ n^{-1/α}
                if res['beta'] is not None:
                    expected_beta = 1.0 / alpha if alpha > 0 else None
                    console.print(f"  [dim]Теория: β = 1/α = {expected_beta:.3f}[/dim]" if expected_beta else "")
                    console.print(f"  [dim]Факт: β = {res['beta']:.3f}[/dim]")

        results.append(res)

    # Сводная таблица
    console.print("\n")
    table = Table(title="СПЕКТР V_K: β vs 1/α", box=box.DOUBLE)
    table.add_column("K", style="cyan")
    table.add_column("Twins", style="yellow")
    table.add_column("β (λ_n ~ n^{-β})", style="green")
    table.add_column("α (Tr ~ τ^{-α})", style="magenta")
    table.add_column("1/α (теория)", style="blue")
    table.add_column("β - 1/α", style="red")

    for r in results:
        if r.get('alpha') and r.get('beta'):
            inv_alpha = 1.0 / r['alpha']
            diff = r['beta'] - inv_alpha
            table.add_row(
                f"{r['K']:.1f}",
                str(r['n_twins']),
                f"{r['beta']:.3f}",
                f"{r['alpha']:.3f}",
                f"{inv_alpha:.3f}",
                f"{diff:+.3f}"
            )
        elif r.get('alpha'):
            table.add_row(
                f"{r['K']:.1f}",
                str(r['n_twins']),
                "—",
                f"{r['alpha']:.3f}",
                f"{1.0/r['alpha']:.3f}",
                "—"
            )
        else:
            table.add_row(
                f"{r['K']:.1f}",
                str(r['n_twins']),
                "—",
                "—",
                "—",
                "—"
            )

    console.print(table)

    # Интерпретация
    console.print("\n")

    # Проверяем согласованность
    betas = [r['beta'] for r in results if r.get('beta')]
    alphas = [r['alpha'] for r in results if r.get('alpha')]

    if len(betas) >= 2 and len(alphas) >= 2:
        mean_beta = np.mean(betas)
        mean_alpha = np.mean(alphas)
        inv_alpha = 1.0 / mean_alpha

        if abs(mean_beta - inv_alpha) < 0.5:
            verdict = "[green]β ≈ 1/α — согласуется с Tauberian теоремой![/green]"
        else:
            verdict = "[yellow]β ≠ 1/α — нужен дополнительный анализ[/yellow]"

        console.print(Panel.fit(
            f"{verdict}\n\n"
            f"Средний β = {mean_beta:.3f}\n"
            f"Средний α = {mean_alpha:.3f}\n"
            f"1/α = {inv_alpha:.3f}",
            box=box.DOUBLE
        ))

    # Графики
    if len(results) >= 2:
        fig, axes = plt.subplots(1, 3, figsize=(15, 5))

        # 1. Спектр V (log-log)
        ax1 = axes[0]
        for r in results:
            if len(r['eigs_V']) >= 3:
                n = np.arange(1, len(r['eigs_V']) + 1)
                ax1.loglog(n, r['eigs_V'], 'o-', label=f"K={r['K']}, β={r['beta']:.2f}" if r['beta'] else f"K={r['K']}")
        ax1.set_xlabel('n (eigenvalue index)')
        ax1.set_ylabel('λ_n(V)')
        ax1.set_title('Eigenvalues of V: λ_n vs n')
        ax1.legend()
        ax1.grid(True, alpha=0.3, which='both')

        # 2. Heat trace
        ax2 = axes[1]
        for r in results:
            if r.get('traces'):
                ax2.loglog(tau_range, r['traces'], 'o-',
                          label=f"K={r['K']}, α={r['alpha']:.2f}" if r['alpha'] else f"K={r['K']}")
        ax2.set_xlabel('τ')
        ax2.set_ylabel('Tr(e^{-τA²}V)')
        ax2.set_title('Heat Trace: Tr ~ τ^{-α}')
        ax2.legend()
        ax2.grid(True, alpha=0.3, which='both')

        # 3. β vs 1/α
        ax3 = axes[2]
        betas = [r['beta'] for r in results if r.get('beta') and r.get('alpha')]
        inv_alphas = [1.0/r['alpha'] for r in results if r.get('beta') and r.get('alpha')]
        Ks = [r['K'] for r in results if r.get('beta') and r.get('alpha')]

        if len(betas) >= 2:
            ax3.scatter(inv_alphas, betas, s=100, c=Ks, cmap='viridis')
            ax3.plot([0, max(inv_alphas)*1.2], [0, max(inv_alphas)*1.2], 'r--', label='β = 1/α')
            ax3.set_xlabel('1/α (from heat trace)')
            ax3.set_ylabel('β (from eigenvalue spectrum)')
            ax3.set_title('Tauberian Check: β vs 1/α')
            ax3.legend()
            ax3.grid(True, alpha=0.3)
            cbar = plt.colorbar(ax3.collections[0], ax=ax3, label='K')

        plt.tight_layout()
        plt.savefig('spectrum_V_analysis.png', dpi=150, bbox_inches='tight')
        console.print("[green]Plot saved: spectrum_V_analysis.png[/green]")
        plt.show()

    return results


if __name__ == "__main__":
    main()
