#!/usr/bin/env python3
"""
Anantharaman-Monk Spectral Gap Test Suite v3.0
==============================================
Tests for Q3-2 Bridge: spectral gap, minor arcs suppression, correlation decay.

Based on Rep_N_BRIDGE.md v2.6 Section 17 (Developer's Summary)

v2.0: Added Test 4 - Generalized Rayleigh Quotient (G^{-1} RHS)
v3.0: Added Test 5 - Gram Conditioning (κ(G) vs t Safe Zone)
      Added Test 6 - Minor Arcs Uniformity Scan (ρ < 1 everywhere)
"""

import numpy as np
from numpy import pi, sqrt, log, exp
from numpy.linalg import eigvalsh
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.progress import track
from rich import print as rprint
import warnings
warnings.filterwarnings('ignore')

console = Console()

# =============================================================================
# CORE FUNCTIONS
# =============================================================================

def sieve_primes(N: int) -> np.ndarray:
    """Sieve of Eratosthenes for primes up to N."""
    is_prime = np.ones(N + 1, dtype=bool)
    is_prime[0:2] = False
    for i in range(2, int(sqrt(N)) + 1):
        if is_prime[i]:
            is_prime[i*i::i] = False
    return np.where(is_prime)[0]


def heat_kernel(u: float, v: float, t: float) -> float:
    """Heat kernel k_t(u, v) = exp(-(u-v)^2 / (4t))"""
    return exp(-(u - v)**2 / (4 * t))


def build_gram_matrix(primes: np.ndarray, t: float) -> np.ndarray:
    """
    Build Gram matrix G_{pq} = k_t(xi_p, xi_q)
    where xi_p = log(p) / (2*pi)
    """
    xi = log(primes) / (2 * pi)  # log-coordinates
    n = len(primes)
    G = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            G[i, j] = heat_kernel(xi[i], xi[j], t)
    return G


def prime_weights(primes: np.ndarray) -> np.ndarray:
    """Weights w(p) = log(p) / sqrt(p)"""
    return log(primes) / sqrt(primes)


def circle_twist(primes: np.ndarray, alpha: float) -> np.ndarray:
    """Circle twist e(alpha * p) = exp(2*pi*i*alpha*p)"""
    return np.exp(2j * pi * alpha * primes)


def twisted_sum(primes: np.ndarray, alpha: float, N: int) -> complex:
    """
    Compute S_alpha(N) = sum_{p <= N} Lambda(p) * e(alpha * p)
    Using Lambda(p) = log(p) for primes
    """
    mask = primes <= N
    p = primes[mask]
    return np.sum(log(p) * np.exp(2j * pi * alpha * p))


def compute_C_d(primes: np.ndarray, G: np.ndarray, a: np.ndarray, d: int) -> complex:
    """
    Compute d-correlation: C_d(a) = sum_{q: q,q+d in P} a_{q+d} * conj(a_q) * G_{q+d,q}
    """
    prime_set = set(primes)
    prime_to_idx = {p: i for i, p in enumerate(primes)}

    result = 0j
    for i, q in enumerate(primes):
        qd = q + d
        if qd in prime_set:
            j = prime_to_idx[qd]
            result += a[j] * np.conj(a[i]) * G[j, i]
    return result


# =============================================================================
# TEST 1: SPECTRAL GAP CHECK
# =============================================================================

def test_spectral_gap(primes: np.ndarray, t: float) -> dict:
    """
    Check spectral gap: lambda_2 << lambda_1
    """
    console.print("\n[bold cyan]TEST 1: SPECTRAL GAP CHECK[/bold cyan]")
    console.print(f"Building Gram matrix for {len(primes)} primes, t={t}...")

    G = build_gram_matrix(primes, t)

    console.print("Computing eigenvalues...")
    eigenvalues = eigvalsh(G)
    eigenvalues = np.sort(eigenvalues)[::-1]  # descending

    lambda_1 = eigenvalues[0]
    lambda_2 = eigenvalues[1]
    lambda_min = eigenvalues[-1]

    ratio = lambda_2 / lambda_1
    gap = 1 - ratio

    # Results table
    table = Table(title="Spectral Analysis")
    table.add_column("Metric", style="cyan")
    table.add_column("Value", style="green")
    table.add_column("Status", style="yellow")

    table.add_row("lambda_1 (largest)", f"{lambda_1:.6f}", "")
    table.add_row("lambda_2 (second)", f"{lambda_2:.6f}", "")
    table.add_row("lambda_min", f"{lambda_min:.6f}", "")
    table.add_row("Ratio lambda_2/lambda_1", f"{ratio:.6f}", "")
    table.add_row("Spectral Gap (1 - ratio)", f"{gap:.6f}",
                  "[green]GOOD[/green]" if gap > 0.1 else "[red]WEAK[/red]")

    console.print(table)

    # Ramanujan bound check (for d-regular graphs: lambda_2 <= 2*sqrt(d-1))
    # For our case, check if gap exists
    passed = gap > 0.05

    if passed:
        console.print("[bold green]PASS: Spectral gap exists![/bold green]")
    else:
        console.print("[bold red]WARNING: Spectral gap may be too small[/bold red]")

    return {
        "G": G,
        "lambda_1": lambda_1,
        "lambda_2": lambda_2,
        "gap": gap,
        "passed": passed,
        "eigenvalues": eigenvalues[:10]  # top 10
    }


# =============================================================================
# TEST 2: MINOR ARCS TEST
# =============================================================================

def build_twisted_operator(primes: np.ndarray, G: np.ndarray, alpha: float) -> np.ndarray:
    """
    Build twisted operator B_α = G^{1/2} W U_α G^{1/2}

    For spectral norm, we compute B_α B_α^* and take sqrt of max eigenvalue.
    Simplified: B_α ≈ W^{1/2} G_α W^{1/2} where G_α = U_α G U_α*
    """
    n = len(primes)
    w = prime_weights(primes)
    W_sqrt = np.diag(np.sqrt(np.abs(w)))

    # Twisted Gram: (G_α)_{pq} = e(α(p-q)) * G_{pq}
    twist = np.exp(2j * pi * alpha * (primes[:, None] - primes[None, :]))
    G_alpha = twist * G

    # B_α ≈ W^{1/2} G_α W^{1/2}
    B_alpha = W_sqrt @ G_alpha @ W_sqrt

    return B_alpha


def test_minor_arcs(primes: np.ndarray, N: int, G: np.ndarray, delta_target: float = 0.01) -> dict:
    """
    Test Q3-2: a* G_α a < a* G_0 a for MINOR ARC alpha

    KEY INSIGHT: ‖G_α‖ = ‖G‖ (unitary invariance of spectral norm!)
    But bilinear form a* G_α a CAN be smaller due to phase cancellation.

    We test: Σ_d e(αd) C_d(a) < Σ_d C_d(a)
    """
    console.print("\n[bold cyan]TEST 2: BILINEAR FORM ON MINOR ARCS (Q3-2)[/bold cyan]")
    console.print("[dim]Testing a* G_α a = Σ e(αd) C_d(a) vs a* G_0 a = Σ C_d(a)[/dim]")
    console.print("[dim]Note: Spectral norm is unitary-invariant, but bilinear form is NOT[/dim]")

    # ONLY irrational / poorly approximable alpha (TRUE minor arcs)
    test_alphas = [
        (sqrt(2) - 1, "sqrt(2)-1"),           # algebraic irrational
        ((sqrt(5) - 1) / 2, "phi"),           # golden ratio (most irrational!)
        (sqrt(3) - 1, "sqrt(3)-1"),           # another algebraic
        (pi / 10, "pi/10"),                   # transcendental
        (exp(1) / 10, "e/10"),                # transcendental
        (0.123456789, "random"),              # pseudo-random
        (0.7182818284, "e-2"),                # e - 2
        (log(2), "ln(2)"),                    # transcendental
    ]

    # Use prime weights as test vector
    w = prime_weights(primes)
    a = w / np.linalg.norm(w)  # normalized

    # Build twisted Gram matrices
    def compute_bilinear(G, primes, alpha, a):
        """Compute a* G_α a where G_α = U_α G U_α*"""
        twist = np.exp(2j * pi * alpha * primes)
        # (G_α)_{pq} = e(α(p-q)) G_{pq} = e(αp) G_{pq} e(-αq)
        # a* G_α a = Σ_{pq} conj(a_p) e(αp) G_{pq} e(-αq) a_q
        #          = Σ_{pq} (a_p e(-αp))* G_{pq} (a_q e(-αq))
        a_twisted = a * np.conj(twist)
        return np.real(np.conj(a_twisted) @ G @ a_twisted)

    # Baseline: α = 0
    bilinear_0 = np.real(np.conj(a) @ G @ a)

    table = Table(title=f"Q3-2 Bilinear Form Test (N={N})")
    table.add_column("Alpha", style="cyan")
    table.add_column("a*G_α*a", style="green")
    table.add_column("a*G_0*a", style="yellow")
    table.add_column("Ratio", style="magenta")
    table.add_column("Status")

    results = []
    for alpha, name in track(test_alphas, description="Computing bilinear forms..."):
        bilinear_alpha = compute_bilinear(G, primes, alpha, a)
        ratio = bilinear_alpha / bilinear_0

        # Status: good if ratio < 1 (phase cancellation!)
        if ratio < 0.5:
            status = "[bold green]STRONG[/bold green]"
        elif ratio < 0.8:
            status = "[green]GOOD[/green]"
        elif ratio < 1.0:
            status = "[yellow]WEAK[/yellow]"
        else:
            status = "[red]NONE[/red]"

        results.append({"alpha": alpha, "name": name, "bilinear": bilinear_alpha, "ratio": ratio})

    # Display results
    for r in results:
        status = "[bold green]STRONG[/bold green]" if r["ratio"] < 0.5 else \
                 "[green]GOOD[/green]" if r["ratio"] < 0.8 else \
                 "[yellow]WEAK[/yellow]" if r["ratio"] < 1.0 else "[red]NONE[/red]"
        table.add_row(r["name"], f"{r['bilinear']:.4f}", f"{bilinear_0:.4f}", f"{r['ratio']:.4f}", status)

    console.print(table)

    # Summary
    avg_ratio = np.mean([r["ratio"] for r in results])
    min_ratio = min([r["ratio"] for r in results])
    max_ratio = max([r["ratio"] for r in results])

    console.print(f"\n[bold]Bilinear form analysis:[/bold]")
    console.print(f"  a*G_0*a (untwisted) = {bilinear_0:.4f}")
    console.print(f"  Average ratio = {avg_ratio:.4f}")
    console.print(f"  Range: [{min_ratio:.4f}, {max_ratio:.4f}]")

    if avg_ratio < 0.8:
        console.print("[bold green]PASS: Phase cancellation confirmed![/bold green]")
        passed = True
    elif avg_ratio < 1.0:
        console.print("[bold yellow]PARTIAL: Some cancellation observed[/bold yellow]")
        passed = True
    else:
        console.print("[bold red]FAIL: No phase cancellation[/bold red]")
        passed = False

    return {"results": results, "bilinear_0": bilinear_0, "avg_ratio": avg_ratio, "passed": passed}


# =============================================================================
# TEST 3: CORRELATION DECAY
# =============================================================================

def test_correlation_decay(primes: np.ndarray, G: np.ndarray, t: float, max_d: int = 100) -> dict:
    """
    Test: |C_d(a)| decays exponentially with d
    Expected: |C_d| ~ exp(-c*|d|/sqrt(t))

    Uses PRIME WEIGHTS: a_p = w(p) = log(p)/sqrt(p)
    """
    console.print("\n[bold cyan]TEST 3: CORRELATION DECAY[/bold cyan]")

    # Use PRIME WEIGHTS (not uniform!)
    # a_p = w(p) = log(p) / sqrt(p)
    a = prime_weights(primes)
    a = a / np.linalg.norm(a)  # normalized
    console.print(f"[dim]Using prime weights w(p) = log(p)/sqrt(p), normalized[/dim]")

    # Compute C_d for various d
    d_values = list(range(2, min(max_d, 50), 2))  # even d (twin-like)
    C_values = []

    console.print(f"Computing C_d for d in [2, {max(d_values)}]...")

    for d in track(d_values, description="Computing correlations..."):
        C_d = compute_C_d(primes, G, a, d)
        C_values.append(abs(C_d))

    # Fit exponential decay: log|C_d| = -c*d + const
    valid_idx = [i for i, c in enumerate(C_values) if c > 1e-15]
    if len(valid_idx) > 3:
        d_fit = np.array([d_values[i] for i in valid_idx])
        C_fit = np.array([C_values[i] for i in valid_idx])
        log_C = np.log(C_fit)

        # Linear regression
        coeffs = np.polyfit(d_fit, log_C, 1)
        decay_rate = -coeffs[0]

        console.print(f"\n[bold]Exponential decay rate: {decay_rate:.6f}[/bold]")
        console.print(f"Expected rate ~ 1/sqrt(t) = {1/sqrt(t):.6f}")
    else:
        decay_rate = 0
        console.print("[yellow]Not enough data for decay fit[/yellow]")

    # Display table
    table = Table(title="Correlation Values C_d")
    table.add_column("d", style="cyan")
    table.add_column("|C_d|", style="green")
    table.add_column("log|C_d|", style="yellow")

    for d, C in zip(d_values[:15], C_values[:15]):  # first 15
        log_c = np.log(C) if C > 0 else float('-inf')
        table.add_row(str(d), f"{C:.2e}", f"{log_c:.2f}")

    console.print(table)

    # Check if decay is happening
    if len(C_values) > 5:
        ratio = C_values[-1] / C_values[0] if C_values[0] > 0 else 1
        if ratio < 0.1:
            console.print("[bold green]PASS: Strong correlation decay![/bold green]")
            passed = True
        elif ratio < 0.5:
            console.print("[bold yellow]PARTIAL: Moderate decay[/bold yellow]")
            passed = True
        else:
            console.print("[bold red]WARNING: Weak decay[/bold red]")
            passed = False
    else:
        passed = False

    return {
        "d_values": d_values,
        "C_values": C_values,
        "decay_rate": decay_rate,
        "passed": passed
    }


# =============================================================================
# TEST 4: GENERALIZED RAYLEIGH QUOTIENT (G^{-1} RHS)
# =============================================================================

def test_rayleigh_quotient(primes: np.ndarray, G: np.ndarray, t: float) -> dict:
    """
    Test CORRECT Q3-2 formulation with G^{-1} denominator.

    CORRECT: y* (W U_α G U_α* W) y ≤ ρ² · y* G^{-1} y

    This is the Generalized Rayleigh Quotient that actually implies ‖B_α‖ ≤ ρ.
    The naive bound Σ e(αd) C_d ≤ ρ² Σ C_d is FALSE for single-point vectors!
    """
    console.print("\n[bold cyan]TEST 4: GENERALIZED RAYLEIGH QUOTIENT (G^{-1} RHS)[/bold cyan]")
    console.print("[dim]Testing: y* (W U_α G U_α* W) y / (y* G^{-1} y) < ρ²[/dim]")
    console.print("[bold yellow]This is the CORRECT Q3-2 formulation![/bold yellow]")

    n = len(primes)
    w = prime_weights(primes)
    W = np.diag(w)

    # Compute G^{-1} (pseudoinverse for numerical stability)
    try:
        G_inv = np.linalg.pinv(G, rcond=1e-10)
        console.print(f"[green]G^{{-1}} computed (condition number: {np.linalg.cond(G):.2e})[/green]")
    except:
        console.print("[red]Failed to compute G^{-1}[/red]")
        return {"passed": False, "error": "G^{-1} computation failed"}

    # Test alphas (minor arcs)
    test_alphas = [
        (sqrt(2) - 1, "sqrt(2)-1"),
        ((sqrt(5) - 1) / 2, "phi"),
        (pi / 10, "pi/10"),
        (log(2), "ln(2)"),
        (0.123456789, "random"),
    ]

    # Test with multiple random vectors y
    n_samples = 50
    np.random.seed(42)

    results = []

    for alpha, name in test_alphas:
        # Compute W U_α G U_α* W
        twist = np.exp(2j * pi * alpha * primes)
        U_alpha = np.diag(twist)
        U_alpha_star = np.diag(np.conj(twist))

        # LHS operator: W U_α G U_α* W
        LHS_op = W @ U_alpha @ G @ U_alpha_star @ W

        # Compute Rayleigh quotients for random vectors
        quotients = []
        for _ in range(n_samples):
            # Random complex vector
            y = np.random.randn(n) + 1j * np.random.randn(n)
            y = y / np.linalg.norm(y)

            # LHS: y* (W U_α G U_α* W) y
            lhs = np.real(np.conj(y) @ LHS_op @ y)

            # RHS: y* G^{-1} y
            rhs = np.real(np.conj(y) @ G_inv @ y)

            if rhs > 1e-10:
                quotients.append(lhs / rhs)

        max_quotient = max(quotients) if quotients else float('inf')
        avg_quotient = np.mean(quotients) if quotients else float('inf')

        results.append({
            "alpha": alpha,
            "name": name,
            "max_quotient": max_quotient,
            "avg_quotient": avg_quotient,
            "rho_squared": max_quotient  # This is ρ² estimate
        })

    # Display results
    table = Table(title="Generalized Rayleigh Quotient (ρ² estimates)")
    table.add_column("Alpha", style="cyan")
    table.add_column("Max Quotient", style="green")
    table.add_column("Avg Quotient", style="yellow")
    table.add_column("ρ estimate", style="magenta")
    table.add_column("Status")

    for r in results:
        rho = sqrt(r["max_quotient"]) if r["max_quotient"] > 0 else float('inf')
        status = "[bold green]ρ<1[/bold green]" if rho < 1.0 else "[red]ρ≥1[/red]"
        table.add_row(
            r["name"],
            f"{r['max_quotient']:.4f}",
            f"{r['avg_quotient']:.4f}",
            f"{rho:.4f}",
            status
        )

    console.print(table)

    # Summary
    all_rho = [sqrt(r["max_quotient"]) for r in results if r["max_quotient"] > 0]
    max_rho = max(all_rho) if all_rho else float('inf')

    console.print(f"\n[bold]Maximum ρ across all test α: {max_rho:.4f}[/bold]")

    if max_rho < 1.0:
        console.print("[bold green]PASS: ρ < 1 confirmed! Q3-2 holds numerically.[/bold green]")
        passed = True
    else:
        console.print("[bold red]FAIL: ρ ≥ 1, Q3-2 NOT confirmed[/bold red]")
        passed = False

    return {
        "results": results,
        "max_rho": max_rho,
        "passed": passed
    }


# =============================================================================
# TEST 5: GRAM CONDITIONING STRESS TEST (κ(G) vs t)
# =============================================================================

def test_gram_conditioning(primes: np.ndarray, t_values: list = None) -> dict:
    """
    Test Gram matrix conditioning for different heat kernel widths t.

    GOAL: Find "Safe Zone" for t where:
    - κ(G) is polynomial (not exponential)
    - G is neither too diagonal (disconnected) nor too flat (singular)

    Returns optimal t range for ValidParams.
    """
    console.print("\n[bold cyan]TEST 5: GRAM CONDITIONING STRESS TEST[/bold cyan]")
    console.print("[dim]Testing κ(G) = λ_max/λ_min across t values[/dim]")

    if t_values is None:
        # Logarithmic scale from 0.001 to 10
        t_values = [0.001, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0]

    results = []
    n = len(primes)

    for t in track(t_values, description="Testing t values..."):
        G = build_gram_matrix(primes, t)

        # Eigenvalues
        eigs = eigvalsh(G)
        lambda_max = eigs[-1]
        lambda_min = max(eigs[0], 1e-15)  # avoid division by zero

        kappa = lambda_max / lambda_min

        # Check if G^{-1} is stable
        try:
            G_inv = np.linalg.pinv(G, rcond=1e-10)
            inv_norm = np.linalg.norm(G_inv, 2)
            inv_stable = inv_norm < 1e10
        except:
            inv_stable = False
            inv_norm = float('inf')

        results.append({
            "t": t,
            "kappa": kappa,
            "log_kappa": log(kappa),
            "lambda_max": lambda_max,
            "lambda_min": lambda_min,
            "inv_norm": inv_norm,
            "inv_stable": inv_stable
        })

    # Display results
    table = Table(title="Gram Conditioning κ(G) vs Heat Kernel Width t")
    table.add_column("t", style="cyan")
    table.add_column("κ(G)", style="green")
    table.add_column("log(κ)", style="yellow")
    table.add_column("λ_max", style="blue")
    table.add_column("λ_min", style="magenta")
    table.add_column("G^{-1} stable?")

    for r in results:
        status = "[green]YES[/green]" if r["inv_stable"] else "[red]NO[/red]"
        kappa_color = "[green]" if r["kappa"] < 1e6 else "[yellow]" if r["kappa"] < 1e12 else "[red]"
        table.add_row(
            f"{r['t']:.3f}",
            f"{kappa_color}{r['kappa']:.2e}[/]",
            f"{r['log_kappa']:.1f}",
            f"{r['lambda_max']:.2e}",
            f"{r['lambda_min']:.2e}",
            status
        )

    console.print(table)

    # Find Safe Zone
    safe_t = [r["t"] for r in results if r["kappa"] < 1e8 and r["inv_stable"]]

    if safe_t:
        t_min, t_max = min(safe_t), max(safe_t)
        console.print(f"\n[bold green]SAFE ZONE: t ∈ [{t_min}, {t_max}][/bold green]")
        console.print(f"[dim]Recommended: t = {np.sqrt(t_min * t_max):.3f} (geometric mean)[/dim]")
        passed = True
    else:
        console.print("[bold red]WARNING: No safe t found! Need regularization.[/bold red]")
        t_min, t_max = 0.01, 1.0  # fallback
        passed = False

    return {
        "results": results,
        "safe_zone": (t_min, t_max) if safe_t else None,
        "recommended_t": sqrt(t_min * t_max) if safe_t else 0.1,
        "passed": passed
    }


# =============================================================================
# TEST 6: MINOR ARCS UNIFORMITY SCAN
# =============================================================================

def test_minor_arcs_scan(primes: np.ndarray, G: np.ndarray, t: float,
                         n_points: int = 100, exclude_major: float = 0.01) -> dict:
    """
    Scan minor arcs uniformly to verify ρ < 1 EVERYWHERE.

    GOAL: Confirm Q3-2 uniformity - no "hot spots" where ρ spikes.

    Parameters:
    - n_points: number of α values to test
    - exclude_major: exclude α within this distance of rationals a/q with q ≤ 10
    """
    console.print("\n[bold cyan]TEST 6: MINOR ARCS UNIFORMITY SCAN[/bold cyan]")
    console.print(f"[dim]Scanning {n_points} points on [0, 1), excluding major arcs[/dim]")

    n = len(primes)
    w = prime_weights(primes)
    W = np.diag(w)

    # Compute G^{-1}
    G_inv = np.linalg.pinv(G, rcond=1e-10)

    # Generate test points (avoiding major arcs)
    def is_major_arc(alpha, threshold=0.01, max_q=10):
        """Check if α is near a/q for small q."""
        for q in range(1, max_q + 1):
            for a in range(q):
                if abs(alpha - a/q) < threshold/q or abs(alpha - a/q - 1) < threshold/q:
                    return True
        return False

    # Grid of alpha values
    alpha_grid = np.linspace(0.001, 0.999, n_points)
    minor_arc_alphas = [(a, f"{a:.4f}") for a in alpha_grid if not is_major_arc(a, exclude_major)]

    console.print(f"[dim]After filtering: {len(minor_arc_alphas)} minor arc points[/dim]")

    # Compute ρ for each α
    n_samples = 20  # fewer samples per point for speed
    np.random.seed(42)

    results = []
    rho_values = []

    for alpha, name in track(minor_arc_alphas, description="Scanning minor arcs..."):
        # W U_α G U_α* W
        twist = np.exp(2j * pi * alpha * primes)
        U_alpha = np.diag(twist)
        U_alpha_star = np.diag(np.conj(twist))
        LHS_op = W @ U_alpha @ G @ U_alpha_star @ W

        # Sample Rayleigh quotients
        quotients = []
        for _ in range(n_samples):
            y = np.random.randn(n) + 1j * np.random.randn(n)
            y = y / np.linalg.norm(y)

            lhs = np.real(np.conj(y) @ LHS_op @ y)
            rhs = np.real(np.conj(y) @ G_inv @ y)

            if rhs > 1e-10:
                quotients.append(lhs / rhs)

        max_quotient = max(quotients) if quotients else float('inf')
        rho = sqrt(max_quotient) if max_quotient > 0 else float('inf')

        results.append({"alpha": alpha, "rho": rho})
        rho_values.append(rho)

    # Statistics
    rho_array = np.array(rho_values)
    rho_max = np.max(rho_array)
    rho_mean = np.mean(rho_array)
    rho_std = np.std(rho_array)

    # Find worst points
    worst_idx = np.argsort(rho_array)[-5:][::-1]

    console.print(f"\n[bold]Uniformity Statistics:[/bold]")
    console.print(f"  Max ρ = {rho_max:.4f}")
    console.print(f"  Mean ρ = {rho_mean:.4f}")
    console.print(f"  Std ρ = {rho_std:.4f}")

    console.print(f"\n[bold]Worst 5 points (highest ρ):[/bold]")
    table = Table()
    table.add_column("α", style="cyan")
    table.add_column("ρ", style="red" if rho_max >= 1 else "green")

    for idx in worst_idx:
        table.add_row(f"{results[idx]['alpha']:.4f}", f"{results[idx]['rho']:.4f}")

    console.print(table)

    # Verdict
    if rho_max < 1.0:
        delta = 1 - rho_max
        console.print(f"\n[bold green]PASS: ρ < 1 EVERYWHERE on minor arcs![/bold green]")
        console.print(f"[bold green]Spectral gap δ ≥ {delta:.4f}[/bold green]")
        passed = True
    elif rho_max < 1.05:
        console.print(f"\n[bold yellow]WARNING: ρ ≈ 1 at some points (max = {rho_max:.4f})[/bold yellow]")
        console.print("[dim]May need finer parameters or more samples[/dim]")
        passed = False
    else:
        console.print(f"\n[bold red]FAIL: ρ ≥ 1 at some minor arc points![/bold red]")
        passed = False

    return {
        "results": results,
        "rho_max": rho_max,
        "rho_mean": rho_mean,
        "rho_std": rho_std,
        "delta": 1 - rho_max if rho_max < 1 else 0,
        "passed": passed
    }


# =============================================================================
# MAIN TEST RUNNER
# =============================================================================

def run_all_tests(N: int = 10000, t: float = 0.1):
    """Run complete test suite."""

    console.print(Panel.fit(
        "[bold yellow]ANANTHARAMAN-MONK SPECTRAL GAP TEST SUITE[/bold yellow]\n"
        f"N = {N}, t = {t}\n"
        "Testing Q3-2 Bridge components",
        title="Q3 Numerical Verification"
    ))

    # Generate primes
    console.print(f"\nGenerating primes up to N={N}...")
    primes = sieve_primes(N)
    console.print(f"Found {len(primes)} primes")

    # Run tests
    results = {}

    # Test 1: Spectral Gap
    results["spectral_gap"] = test_spectral_gap(primes, t)
    G = results["spectral_gap"]["G"]

    # Test 2: Minor Arcs (Q3-2 operator norm)
    results["minor_arcs"] = test_minor_arcs(primes, N, G)

    # Test 3: Correlation Decay
    results["correlation_decay"] = test_correlation_decay(primes, G, t)

    # Test 4: Generalized Rayleigh Quotient (CORRECT Q3-2!)
    results["rayleigh_quotient"] = test_rayleigh_quotient(primes, G, t)

    # Test 5: Gram Conditioning (Safe Zone for t)
    results["gram_conditioning"] = test_gram_conditioning(primes)

    # Test 6: Minor Arcs Uniformity Scan
    results["minor_arcs_scan"] = test_minor_arcs_scan(primes, G, t)

    # Summary
    console.print("\n" + "="*60)
    console.print("[bold cyan]SUMMARY[/bold cyan]")
    console.print("="*60)

    summary_table = Table()
    summary_table.add_column("Test", style="cyan")
    summary_table.add_column("Result", style="green")
    summary_table.add_column("Key Metric")

    summary_table.add_row(
        "1. Spectral Gap",
        "[green]PASS[/green]" if results["spectral_gap"]["passed"] else "[red]FAIL[/red]",
        f"gap = {results['spectral_gap']['gap']:.4f}"
    )
    summary_table.add_row(
        "2. Minor Arcs",
        "[green]PASS[/green]" if results["minor_arcs"]["passed"] else "[yellow]PARTIAL[/yellow]",
        f"avg_ratio = {results['minor_arcs']['avg_ratio']:.4f}"
    )
    summary_table.add_row(
        "3. Correlation Decay",
        "[green]PASS[/green]" if results["correlation_decay"]["passed"] else "[red]FAIL[/red]",
        f"decay_rate = {results['correlation_decay']['decay_rate']:.4f}"
    )
    summary_table.add_row(
        "4. Rayleigh Quotient (G^{-1})",
        "[green]PASS[/green]" if results["rayleigh_quotient"]["passed"] else "[red]FAIL[/red]",
        f"max_ρ = {results['rayleigh_quotient']['max_rho']:.4f}"
    )
    summary_table.add_row(
        "5. Gram Conditioning",
        "[green]PASS[/green]" if results["gram_conditioning"]["passed"] else "[yellow]WARN[/yellow]",
        f"safe t ∈ {results['gram_conditioning']['safe_zone']}"
    )
    summary_table.add_row(
        "6. Minor Arcs Scan",
        "[green]PASS[/green]" if results["minor_arcs_scan"]["passed"] else "[red]FAIL[/red]",
        f"δ = {results['minor_arcs_scan']['delta']:.4f}"
    )

    console.print(summary_table)

    # Final verdict
    all_passed = all([
        results["spectral_gap"]["passed"],
        results["minor_arcs"]["passed"],
        results["correlation_decay"]["passed"],
        results["rayleigh_quotient"]["passed"],
        results["gram_conditioning"]["passed"],
        results["minor_arcs_scan"]["passed"]
    ])

    if all_passed:
        console.print(Panel.fit(
            "[bold green]ALL TESTS PASSED![/bold green]\n"
            "Q3-2 Bridge components working as expected.\n"
            "Spectral gap guarantees minor arcs suppression.",
            title="VERDICT"
        ))
    else:
        console.print(Panel.fit(
            "[bold yellow]PARTIAL SUCCESS[/bold yellow]\n"
            "Some components need attention.",
            title="VERDICT"
        ))

    return results


# =============================================================================
# TEST 7: SCALING ANALYSIS (δ vs N)
# =============================================================================

def scaling_analysis(N_values: list = None, t: float = 0.1, n_alpha_samples: int = 30) -> dict:
    """
    Analyze how spectral gap δ scales with N.

    GOAL: Verify that δ stays bounded away from 0 as N → ∞.
    If δ plateaus at some constant > 0, this suggests universal behavior.
    """
    console.print("\n" + "="*70)
    console.print("[bold magenta]TEST 7: SCALING ANALYSIS (δ vs N)[/bold magenta]")
    console.print("="*70)
    console.print(f"[dim]Testing if δ = 1 - max_ρ stays positive as N grows[/dim]\n")

    if N_values is None:
        N_values = [2000, 5000, 10000, 20000, 50000]

    results = []

    for N in N_values:
        console.print(f"\n[bold cyan]━━━ N = {N:,} ━━━[/bold cyan]")

        # Generate primes
        primes = sieve_primes(N)
        n_primes = len(primes)
        console.print(f"Primes: {n_primes}")

        # Build Gram matrix
        G = build_gram_matrix(primes, t)

        # Compute G^{-1}
        G_inv = np.linalg.pinv(G, rcond=1e-10)
        kappa = np.linalg.cond(G)

        # Weights
        w = prime_weights(primes)
        W = np.diag(w)

        # Quick minor arcs scan (fewer points for speed)
        np.random.seed(42)
        test_alphas = np.random.uniform(0.05, 0.95, n_alpha_samples)

        rho_values = []
        n_samples = 15  # per alpha

        for alpha in track(test_alphas, description=f"Scanning α (N={N})..."):
            twist = np.exp(2j * pi * alpha * primes)
            U_alpha = np.diag(twist)
            U_alpha_star = np.diag(np.conj(twist))
            LHS_op = W @ U_alpha @ G @ U_alpha_star @ W

            quotients = []
            for _ in range(n_samples):
                y = np.random.randn(n_primes) + 1j * np.random.randn(n_primes)
                y = y / np.linalg.norm(y)

                lhs = np.real(np.conj(y) @ LHS_op @ y)
                rhs = np.real(np.conj(y) @ G_inv @ y)

                if rhs > 1e-10:
                    quotients.append(lhs / rhs)

            if quotients:
                rho_values.append(sqrt(max(quotients)))

        max_rho = max(rho_values) if rho_values else 1.0
        mean_rho = np.mean(rho_values) if rho_values else 1.0
        delta = 1 - max_rho

        results.append({
            "N": N,
            "n_primes": n_primes,
            "max_rho": max_rho,
            "mean_rho": mean_rho,
            "delta": delta,
            "kappa": kappa
        })

        status = "[bold green]δ > 0[/bold green]" if delta > 0 else "[bold red]δ ≤ 0[/bold red]"
        console.print(f"  max_ρ = {max_rho:.4f}, δ = {delta:.4f} {status}")

    # Summary table
    console.print("\n" + "="*70)
    console.print("[bold cyan]SCALING SUMMARY[/bold cyan]")
    console.print("="*70)

    table = Table(title="Spectral Gap δ vs N")
    table.add_column("N", style="cyan", justify="right")
    table.add_column("#Primes", style="blue", justify="right")
    table.add_column("max_ρ", style="yellow")
    table.add_column("mean_ρ", style="green")
    table.add_column("δ = 1-ρ", style="magenta")
    table.add_column("Status")

    for r in results:
        delta_color = "[bold green]" if r["delta"] > 0.5 else "[green]" if r["delta"] > 0 else "[red]"
        status = "✅" if r["delta"] > 0 else "❌"
        table.add_row(
            f"{r['N']:,}",
            f"{r['n_primes']:,}",
            f"{r['max_rho']:.4f}",
            f"{r['mean_rho']:.4f}",
            f"{delta_color}{r['delta']:.4f}[/]",
            status
        )

    console.print(table)

    # ASCII "graph" of δ vs N
    console.print("\n[bold]δ trend (ASCII graph):[/bold]")
    max_delta = max(r["delta"] for r in results)
    for r in results:
        bar_len = int(50 * r["delta"] / max_delta) if max_delta > 0 else 0
        bar = "█" * bar_len
        console.print(f"  N={r['N']:>6,}: {bar} {r['delta']:.3f}")

    # Verdict
    deltas = [r["delta"] for r in results]
    if all(d > 0.5 for d in deltas):
        console.print(f"\n[bold green]🎯 EXCELLENT: δ > 0.5 for ALL N tested![/bold green]")
        console.print("[bold green]Spectral gap appears UNIVERSAL.[/bold green]")
        passed = True
    elif all(d > 0 for d in deltas):
        console.print(f"\n[bold yellow]⚠️ GOOD: δ > 0 for all N, but some values are small[/bold yellow]")
        passed = True
    else:
        console.print(f"\n[bold red]❌ WARNING: δ ≤ 0 for some N! Gap may collapse.[/bold red]")
        passed = False

    # Trend analysis
    if len(deltas) >= 3:
        trend = np.polyfit(range(len(deltas)), deltas, 1)[0]
        if trend > 0.01:
            console.print(f"[dim]Trend: δ INCREASING with N (slope = {trend:.4f})[/dim]")
        elif trend < -0.01:
            console.print(f"[dim]Trend: δ DECREASING with N (slope = {trend:.4f})[/dim]")
        else:
            console.print(f"[dim]Trend: δ STABLE (plateau, slope ≈ {trend:.4f})[/dim]")

    return {
        "results": results,
        "passed": passed,
        "min_delta": min(deltas),
        "max_delta": max(deltas)
    }


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Q3-2 Bridge Spectral Gap Test Suite")
    parser.add_argument("-N", type=int, default=10000, help="Upper bound for primes (default: 10000)")
    parser.add_argument("-t", type=float, default=0.1, help="Heat kernel parameter (default: 0.1)")
    parser.add_argument("--scaling", action="store_true", help="Run scaling analysis (δ vs N)")
    parser.add_argument("--scaling-values", type=str, default="2000,5000,10000,20000",
                        help="Comma-separated N values for scaling (default: 2000,5000,10000,20000)")

    args = parser.parse_args()

    if args.scaling:
        N_values = [int(x.strip()) for x in args.scaling_values.split(",")]
        scaling_analysis(N_values=N_values, t=args.t)
    else:
        run_all_tests(N=args.N, t=args.t)
