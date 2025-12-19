#!/usr/bin/env python3
"""
Fourier analysis of Λ(n) and connection to twins.

Key insight: S₂(X) = ⟨Λ, T₂Λ⟩ = (1/N) Σ |Λ̂(ξ)|² · e^{4πiξ}

Questions:
1. How does |Λ̂(0.5)|² grow with X?
2. Is there a peak at ξ = 0.5 (period 2)?
3. Does this connect to χ₄?
"""

import numpy as np
from rich.console import Console
from rich.table import Table

def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True

def primerange(a, b):
    return [p for p in range(a, b) if is_prime(p)]

console = Console()

def von_mangoldt(n: int) -> float:
    """von Mangoldt function Λ(n)"""
    if n < 2:
        return 0.0
    for p in range(2, int(n**0.5) + 2):
        if n % p == 0:
            k = 0
            m = n
            while m % p == 0:
                m //= p
                k += 1
            if m == 1:
                return np.log(p)
            return 0.0
    return np.log(n)  # n is prime

def compute_lambda_fourier(X: int):
    """Compute Λ(n) for n ≤ X and its DFT."""
    # Build Λ vector
    Lambda = np.array([von_mangoldt(n) for n in range(1, X+1)])

    # DFT
    Lambda_hat = np.fft.fft(Lambda)

    # Frequencies (normalized to [0, 1))
    freqs = np.fft.fftfreq(X)

    return Lambda, Lambda_hat, freqs

def analyze_fourier_structure(X: int):
    """Analyze the Fourier structure at various X."""
    Lambda, Lambda_hat, freqs = compute_lambda_fourier(X)

    # Power spectrum
    power = np.abs(Lambda_hat)**2

    # Find key frequencies
    idx_0 = 0  # ξ = 0
    idx_half = X // 2  # ξ = 0.5

    # For ξ = 0.5, need to handle even/odd X
    if X % 2 == 0:
        power_half = power[idx_half]
    else:
        # Interpolate or use closest
        power_half = power[X//2]

    power_0 = power[0]

    # S₂ via Parseval
    N = X
    phase = np.exp(4j * np.pi * freqs)
    S2_fourier = np.real(np.sum(power * phase)) / N

    # S₂ direct
    S2_direct = sum(von_mangoldt(n) * von_mangoldt(n+2) for n in range(1, X-1))

    # Phase correlation
    phase_corr = np.real(np.sum(power * np.cos(4 * np.pi * freqs))) / np.sum(power)

    return {
        'X': X,
        'power_0': power_0,
        'power_half': power_half,
        'ratio': power_half / power_0 if power_0 > 0 else 0,
        'S2_fourier': S2_fourier,
        'S2_direct': S2_direct,
        'phase_corr': phase_corr,
        'sum_Lambda': np.sum(Lambda),
        'num_primes': sum(1 for p in primerange(2, X+1))
    }

def main():
    console.print("\n[bold cyan]═══ FOURIER ANALYSIS OF Λ(n) ═══[/bold cyan]\n")

    # Test various X values
    X_values = [100, 500, 1000, 2000, 5000, 10000]

    results = []
    for X in X_values:
        console.print(f"[yellow]Computing X = {X}...[/yellow]")
        r = analyze_fourier_structure(X)
        results.append(r)

    # Table 1: Power spectrum at key frequencies
    console.print("\n[bold green]Table 1: Power Spectrum |Λ̂(ξ)|² at Key Frequencies[/bold green]\n")

    table = Table()
    table.add_column("X", justify="right")
    table.add_column("|Λ̂(0)|²", justify="right")
    table.add_column("|Λ̂(0.5)|²", justify="right")
    table.add_column("Ratio 0.5/0", justify="right")
    table.add_column("Phase Corr", justify="right")

    for r in results:
        table.add_row(
            str(r['X']),
            f"{r['power_0']:.2e}",
            f"{r['power_half']:.2e}",
            f"{r['ratio']:.4f}",
            f"{r['phase_corr']:.4f}"
        )

    console.print(table)

    # Table 2: S₂ verification
    console.print("\n[bold green]Table 2: S₂ via Parseval vs Direct[/bold green]\n")

    table2 = Table()
    table2.add_column("X", justify="right")
    table2.add_column("S₂ (Fourier)", justify="right")
    table2.add_column("S₂ (Direct)", justify="right")
    table2.add_column("Diff", justify="right")

    for r in results:
        diff = abs(r['S2_fourier'] - r['S2_direct'])
        table2.add_row(
            str(r['X']),
            f"{r['S2_fourier']:.2f}",
            f"{r['S2_direct']:.2f}",
            f"{diff:.2e}"
        )

    console.print(table2)

    # Power law fit for |Λ̂(0.5)|²
    console.print("\n[bold green]Power Law Fits[/bold green]\n")

    X_arr = np.array([r['X'] for r in results])
    power_half_arr = np.array([r['power_half'] for r in results])
    power_0_arr = np.array([r['power_0'] for r in results])

    # Fit |Λ̂(0.5)|² ~ X^α
    log_X = np.log(X_arr)
    log_p_half = np.log(power_half_arr)
    log_p_0 = np.log(power_0_arr)

    slope_half, intercept_half = np.polyfit(log_X, log_p_half, 1)
    slope_0, intercept_0 = np.polyfit(log_X, log_p_0, 1)

    console.print(f"|Λ̂(0)|²    ~ X^{slope_0:.3f}  (expect ~2 since Σ Λ ~ X)")
    console.print(f"|Λ̂(0.5)|²  ~ X^{slope_half:.3f}")
    console.print(f"Ratio      ~ X^{slope_half - slope_0:.3f}")

    # χ₄ connection
    console.print("\n[bold cyan]═══ χ₄ CONNECTION ═══[/bold cyan]\n")
    console.print("χ₄ is the non-principal character mod 4:")
    console.print("  χ₄(1) = 1, χ₄(3) = -1, χ₄(2) = χ₄(4) = 0")
    console.print("\nFor primes p > 2: χ₄(p) = (-1)^{(p-1)/2}")
    console.print("  p ≡ 1 (mod 4) ⟹ χ₄(p) = +1")
    console.print("  p ≡ 3 (mod 4) ⟹ χ₄(p) = -1")
    console.print("\nξ = 0.5 corresponds to period 2 oscillation!")
    console.print("This connects to alternating structure: (-1)^n")

    # Check χ₄ weighted sum
    console.print("\n[bold green]χ₄ Weighted Λ Sum[/bold green]\n")

    X = 10000
    Lambda, Lambda_hat, freqs = compute_lambda_fourier(X)

    # χ₄ for n = 1, 2, ..., X
    chi4 = np.array([0 if n % 2 == 0 else (1 if n % 4 == 1 else -1) for n in range(1, X+1)])

    sum_Lambda = np.sum(Lambda)
    sum_chi4_Lambda = np.sum(chi4 * Lambda)

    console.print(f"Σ Λ(n)           = {sum_Lambda:.2f} (~ X = {X})")
    console.print(f"Σ χ₄(n)·Λ(n)     = {sum_chi4_Lambda:.2f}")
    console.print(f"Ratio χ₄/plain   = {sum_chi4_Lambda/sum_Lambda:.4f}")

    # Connection: Λ̂(0.5) relates to χ₄ twist?
    # e^{πin} = (-1)^n relates to χ₄ for odd n
    Lambda_hat_half = Lambda_hat[X//2]
    console.print(f"\nΛ̂(0.5) = {Lambda_hat_half:.2f}")
    console.print(f"|Λ̂(0.5)| = {np.abs(Lambda_hat_half):.2f}")

    # The key insight
    console.print("\n[bold red]═══ KEY INSIGHT ═══[/bold red]\n")
    console.print("S₂ = Σ Λ(n)Λ(n+2) gets contribution from:")
    console.print("  1. DC term |Λ̂(0)|² (main mass)")
    console.print("  2. Period-2 term |Λ̂(0.5)|² · e^{2πi·0.5·2} = |Λ̂(0.5)|² · (-1)")
    console.print("\nWait, e^{4πi·0.5} = e^{2πi} = +1, so period-2 ADDS!")
    console.print("\nThis means twins benefit from BOTH ξ=0 and ξ=0.5 contributions!")


if __name__ == "__main__":
    main()
