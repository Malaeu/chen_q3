"""Off-diagonal decay analysis for H = T_A - T_P.

Goal: Check if |H_{kl}| ~ |ξ_k - ξ_l|^{-γ} for k ≠ l.
This is the key spectral property linking to Chen's score-based approach.

Usage:
    python -m src.off_diagonal_analysis
"""

from __future__ import annotations

import numpy as np
import matplotlib.pyplot as plt
from math import log, pi

from .hamiltonian import build_hamiltonian


def extract_off_diagonal(H: np.ndarray, xi: np.ndarray):
    """Extract off-diagonal elements and their ξ-distances.

    Returns:
        distances: |ξ_k - ξ_l| for all k < l
        magnitudes: |H_{kl}| for all k < l
    """
    M = H.shape[0]
    distances = []
    magnitudes = []

    for k in range(M):
        for l in range(k + 1, M):  # upper triangle only
            dist = abs(xi[k] - xi[l])
            mag = abs(H[k, l])
            if mag > 1e-15:  # skip numerical zeros
                distances.append(dist)
                magnitudes.append(mag)

    return np.array(distances), np.array(magnitudes)


def fit_power_law(distances: np.ndarray, magnitudes: np.ndarray,
                  min_dist: float = 0.1) -> tuple[float, float, float]:
    """Fit |H_{kl}| ~ C · |ξ_k - ξ_l|^{-γ} using log-log regression.

    Args:
        distances: |ξ_k - ξ_l| values
        magnitudes: |H_{kl}| values
        min_dist: minimum distance to include (avoid near-diagonal noise)

    Returns:
        gamma: power law exponent
        C: prefactor
        r2: R² coefficient
    """
    # Filter by minimum distance
    mask = distances > min_dist
    d = distances[mask]
    m = magnitudes[mask]

    if len(d) < 10:
        return np.nan, np.nan, np.nan

    # Log-log fit: log|H| = log(C) - γ·log|Δξ|
    log_d = np.log(d)
    log_m = np.log(m)

    # Linear regression
    A = np.vstack([log_d, np.ones_like(log_d)]).T
    result = np.linalg.lstsq(A, log_m, rcond=None)
    slope, intercept = result[0]

    gamma = -slope  # |H| ~ d^{-gamma}
    C = np.exp(intercept)

    # R² calculation
    y_pred = slope * log_d + intercept
    ss_res = np.sum((log_m - y_pred) ** 2)
    ss_tot = np.sum((log_m - np.mean(log_m)) ** 2)
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0

    return gamma, C, r2


def analyze_binned(distances: np.ndarray, magnitudes: np.ndarray,
                   n_bins: int = 20) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Bin data by distance and compute mean magnitude per bin.

    Returns:
        bin_centers, mean_mags, std_mags
    """
    min_d, max_d = distances.min(), distances.max()
    bins = np.linspace(min_d, max_d, n_bins + 1)
    bin_centers = 0.5 * (bins[:-1] + bins[1:])

    mean_mags = np.zeros(n_bins)
    std_mags = np.zeros(n_bins)

    for i in range(n_bins):
        mask = (distances >= bins[i]) & (distances < bins[i + 1])
        if mask.sum() > 0:
            mean_mags[i] = np.mean(magnitudes[mask])
            std_mags[i] = np.std(magnitudes[mask])

    # Remove empty bins
    nonzero = mean_mags > 0
    return bin_centers[nonzero], mean_mags[nonzero], std_mags[nonzero]


def run_analysis(K: float = 2.0, M: int = 256, X_max: int = 100_000,
                 t_sym: float = 1.0, plot: bool = True, save_fig: str | None = None):
    """Run full off-diagonal decay analysis.

    Returns:
        dict with gamma, C, r2, alpha_predicted, alpha_numerical
    """
    print(f"Building H with K={K}, M={M}, X_max={X_max:,}, t_sym={t_sym}")
    H, xi = build_hamiltonian(K, M, X_max, t_sym=t_sym)

    print("Extracting off-diagonal elements...")
    distances, magnitudes = extract_off_diagonal(H, xi)
    print(f"  Found {len(distances):,} non-zero off-diagonal pairs")

    # Stats
    print(f"  Distance range: [{distances.min():.4f}, {distances.max():.4f}]")
    print(f"  Magnitude range: [{magnitudes.min():.2e}, {magnitudes.max():.2e}]")

    # Fit power law
    print("\nFitting power law |H_{kl}| ~ C · |Δξ|^{-γ}...")
    gamma, C, r2 = fit_power_law(distances, magnitudes, min_dist=0.1)
    print(f"  γ = {gamma:.4f}")
    print(f"  C = {C:.4e}")
    print(f"  R² = {r2:.4f}")

    # Predict α from γ
    # From Chen analysis: α = 2 - 2γ
    alpha_predicted = 2 - 2 * gamma
    print(f"\nPredicted α = 2 - 2γ = {alpha_predicted:.4f}")
    print(f"Numerical α from experiments: ≈ 0.91")
    print(f"Discrepancy: {abs(alpha_predicted - 0.91):.4f}")

    if plot:
        fig, axes = plt.subplots(1, 2, figsize=(14, 5))

        # Left: scatter plot (log-log)
        ax1 = axes[0]
        ax1.scatter(distances, magnitudes, alpha=0.3, s=1, c='blue')
        ax1.set_xscale('log')
        ax1.set_yscale('log')
        ax1.set_xlabel('|ξ_k - ξ_l|', fontsize=12)
        ax1.set_ylabel('|H_{kl}|', fontsize=12)
        ax1.set_title(f'Off-diagonal decay (X={X_max:,})', fontsize=14)

        # Fit line
        d_fit = np.logspace(np.log10(0.1), np.log10(distances.max()), 100)
        m_fit = C * d_fit ** (-gamma)
        ax1.plot(d_fit, m_fit, 'r-', linewidth=2,
                 label=f'Fit: |H| ~ |Δξ|^{{-{gamma:.2f}}}')
        ax1.legend(fontsize=11)
        ax1.grid(True, alpha=0.3)

        # Right: binned mean with error bars
        ax2 = axes[1]
        bin_centers, mean_mags, std_mags = analyze_binned(distances, magnitudes)
        ax2.errorbar(bin_centers, mean_mags, yerr=std_mags,
                     fmt='o', capsize=3, markersize=6, color='blue')
        ax2.set_xscale('log')
        ax2.set_yscale('log')
        ax2.set_xlabel('|ξ_k - ξ_l|', fontsize=12)
        ax2.set_ylabel('⟨|H_{kl}|⟩ (binned mean)', fontsize=12)
        ax2.set_title(f'γ={gamma:.3f}, α_pred={alpha_predicted:.3f}, R²={r2:.3f}',
                      fontsize=14)

        # Fit line on binned
        ax2.plot(d_fit, m_fit, 'r-', linewidth=2, alpha=0.7)
        ax2.grid(True, alpha=0.3)

        plt.tight_layout()

        if save_fig:
            plt.savefig(save_fig, dpi=150, bbox_inches='tight')
            print(f"\nSaved figure to {save_fig}")
        plt.show()

    return {
        'gamma': gamma,
        'C': C,
        'r2': r2,
        'alpha_predicted': alpha_predicted,
        'alpha_numerical': 0.91,
        'n_pairs': len(distances),
        'X_max': X_max
    }


def sweep_X(X_list: list[int] = [10_000, 50_000, 100_000, 500_000],
            K: float = 2.0, M: int = 256, t_sym: float = 1.0):
    """Run analysis for multiple X values to check stability of γ."""
    results = []
    for X in X_list:
        print(f"\n{'='*60}")
        print(f"X = {X:,}")
        print('='*60)
        res = run_analysis(K=K, M=M, X_max=X, t_sym=t_sym, plot=False)
        results.append(res)

    print("\n" + "="*60)
    print("SUMMARY: γ vs X")
    print("="*60)
    print(f"{'X':>12} {'γ':>10} {'α_pred':>10} {'R²':>10}")
    print("-"*44)
    for r in results:
        print(f"{r['X_max']:>12,} {r['gamma']:>10.4f} {r['alpha_predicted']:>10.4f} {r['r2']:>10.4f}")

    # Average γ
    gammas = [r['gamma'] for r in results if not np.isnan(r['gamma'])]
    if gammas:
        gamma_mean = np.mean(gammas)
        gamma_std = np.std(gammas)
        print("-"*44)
        print(f"{'Mean':>12} {gamma_mean:>10.4f} {2 - 2*gamma_mean:>10.4f}")
        print(f"{'Std':>12} {gamma_std:>10.4f}")

    return results


def extract_off_diagonal_by_center(H: np.ndarray, xi: np.ndarray,
                                    center_lo: float, center_hi: float):
    """Extract off-diagonal elements within a center position range.

    Returns:
        distances: |ξ_k - ξ_l| for pairs with center in [center_lo, center_hi)
        magnitudes: |H_{kl}| for those pairs
    """
    M = H.shape[0]
    distances = []
    magnitudes = []

    for k in range(M):
        for l in range(k + 1, M):
            center = (xi[k] + xi[l]) / 2
            if center_lo <= center < center_hi:
                dist = abs(xi[k] - xi[l])
                mag = abs(H[k, l])
                if mag > 1e-15:
                    distances.append(dist)
                    magnitudes.append(mag)

    return np.array(distances), np.array(magnitudes)


def fit_gamma_in_region(H: np.ndarray, xi: np.ndarray,
                        center_lo: float, center_hi: float,
                        min_dist: float = 0.1) -> dict:
    """Fit γ in a specific center region (twin-region analysis).

    Returns:
        dict with gamma, C, r2, n_pairs, center_range
    """
    distances, magnitudes = extract_off_diagonal_by_center(
        H, xi, center_lo, center_hi)

    if len(distances) < 20:
        return {'gamma': np.nan, 'C': np.nan, 'r2': np.nan,
                'n_pairs': len(distances), 'center_range': (center_lo, center_hi)}

    gamma, C, r2 = fit_power_law(distances, magnitudes, min_dist=min_dist)

    return {
        'gamma': gamma,
        'C': C,
        'r2': r2,
        'n_pairs': len(distances),
        'center_range': (center_lo, center_hi),
        'alpha_pred': 2 - 2 * gamma if not np.isnan(gamma) else np.nan
    }


def parameter_sweep(K_list: list[float] = [1.5, 2.0, 2.5, 3.0],
                    M_list: list[int] = [128, 256, 384],
                    t_sym_list: list[float] = [0.5, 1.0, 1.5],
                    X_max: int = 100_000,
                    twin_center: tuple[float, float] = (0.0, 0.5),
                    save_csv: str | None = None):
    """Sweep over (K, M, t_sym) and measure γ_eff in twin region.

    Args:
        K_list: spectral window half-widths
        M_list: grid sizes
        t_sym_list: kernel scale values
        X_max: fixed prime cutoff
        twin_center: center region for twin-region analysis
        save_csv: optional path to save results

    Returns:
        list of dicts with all results
    """
    results = []
    total = len(K_list) * len(M_list) * len(t_sym_list)
    count = 0

    print("="*70)
    print("PARAMETER SWEEP: γ_eff STABILITY ANALYSIS")
    print("="*70)
    print(f"K values: {K_list}")
    print(f"M values: {M_list}")
    print(f"t_sym values: {t_sym_list}")
    print(f"Twin region: center ∈ {twin_center}")
    print(f"X_max = {X_max:,}")
    print(f"Total configurations: {total}")
    print("="*70)

    for K in K_list:
        for M in M_list:
            for t_sym in t_sym_list:
                count += 1
                print(f"\n[{count}/{total}] K={K}, M={M}, t_sym={t_sym}")

                try:
                    H, xi = build_hamiltonian(K, M, X_max, t_sym=t_sym)

                    # Global fit
                    distances, magnitudes = extract_off_diagonal(H, xi)
                    gamma_global, C_global, r2_global = fit_power_law(
                        distances, magnitudes, min_dist=0.1)

                    # Twin-region fit
                    twin_result = fit_gamma_in_region(
                        H, xi, twin_center[0], twin_center[1], min_dist=0.1)

                    result = {
                        'K': K,
                        'M': M,
                        't_sym': t_sym,
                        'X_max': X_max,
                        'gamma_global': gamma_global,
                        'r2_global': r2_global,
                        'gamma_twin': twin_result['gamma'],
                        'r2_twin': twin_result['r2'],
                        'n_pairs_twin': twin_result['n_pairs'],
                        'alpha_pred': twin_result['alpha_pred']
                    }
                    results.append(result)

                    print(f"  γ_global={gamma_global:.3f} (R²={r2_global:.3f})")
                    print(f"  γ_twin={twin_result['gamma']:.3f} (R²={twin_result['r2']:.3f})")
                    print(f"  α_pred={twin_result['alpha_pred']:.3f}")

                except Exception as e:
                    print(f"  ERROR: {e}")
                    results.append({
                        'K': K, 'M': M, 't_sym': t_sym, 'X_max': X_max,
                        'gamma_global': np.nan, 'r2_global': np.nan,
                        'gamma_twin': np.nan, 'r2_twin': np.nan,
                        'n_pairs_twin': 0, 'alpha_pred': np.nan
                    })

    # Summary table
    print("\n" + "="*70)
    print("SUMMARY TABLE")
    print("="*70)
    print(f"{'K':>6} {'M':>6} {'t_sym':>6} {'γ_twin':>8} {'R²_twin':>8} {'α_pred':>8}")
    print("-"*50)
    for r in results:
        if not np.isnan(r['gamma_twin']):
            print(f"{r['K']:>6.1f} {r['M']:>6d} {r['t_sym']:>6.1f} "
                  f"{r['gamma_twin']:>8.3f} {r['r2_twin']:>8.3f} {r['alpha_pred']:>8.3f}")

    # Statistics
    valid_gammas = [r['gamma_twin'] for r in results if not np.isnan(r['gamma_twin'])]
    if valid_gammas:
        print("-"*50)
        print(f"{'MEAN':>6} {' ':>6} {' ':>6} {np.mean(valid_gammas):>8.3f} "
              f"{' ':>8} {2 - 2*np.mean(valid_gammas):>8.3f}")
        print(f"{'STD':>6} {' ':>6} {' ':>6} {np.std(valid_gammas):>8.3f}")
        print(f"{'MIN':>6} {' ':>6} {' ':>6} {np.min(valid_gammas):>8.3f}")
        print(f"{'MAX':>6} {' ':>6} {' ':>6} {np.max(valid_gammas):>8.3f}")

    # Save to CSV if requested
    if save_csv:
        import csv
        with open(save_csv, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=results[0].keys())
            writer.writeheader()
            writer.writerows(results)
        print(f"\nSaved results to {save_csv}")

    return results


def plot_stability_analysis(results: list[dict], save_fig: str | None = None):
    """Visualize γ_eff stability across parameters."""
    import matplotlib.pyplot as plt

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Filter valid results
    valid = [r for r in results if not np.isnan(r['gamma_twin'])]
    if not valid:
        print("No valid results to plot!")
        return

    # 1. γ_twin vs K
    ax1 = axes[0, 0]
    K_vals = sorted(set(r['K'] for r in valid))
    for K in K_vals:
        gammas = [r['gamma_twin'] for r in valid if r['K'] == K]
        ax1.scatter([K]*len(gammas), gammas, s=50, alpha=0.7, label=f'K={K}')
    ax1.axhline(y=0.52, color='r', linestyle='--', label='Target γ=0.52')
    ax1.set_xlabel('K (spectral window)', fontsize=11)
    ax1.set_ylabel('γ_twin', fontsize=11)
    ax1.set_title('γ stability vs K', fontsize=12)
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # 2. γ_twin vs M
    ax2 = axes[0, 1]
    M_vals = sorted(set(r['M'] for r in valid))
    for M in M_vals:
        gammas = [r['gamma_twin'] for r in valid if r['M'] == M]
        ax2.scatter([M]*len(gammas), gammas, s=50, alpha=0.7, label=f'M={M}')
    ax2.axhline(y=0.52, color='r', linestyle='--', label='Target γ=0.52')
    ax2.set_xlabel('M (grid size)', fontsize=11)
    ax2.set_ylabel('γ_twin', fontsize=11)
    ax2.set_title('γ stability vs M', fontsize=12)
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # 3. γ_twin vs t_sym
    ax3 = axes[1, 0]
    t_vals = sorted(set(r['t_sym'] for r in valid))
    for t in t_vals:
        gammas = [r['gamma_twin'] for r in valid if r['t_sym'] == t]
        ax3.scatter([t]*len(gammas), gammas, s=50, alpha=0.7, label=f't={t}')
    ax3.axhline(y=0.52, color='r', linestyle='--', label='Target γ=0.52')
    ax3.set_xlabel('t_sym (kernel scale)', fontsize=11)
    ax3.set_ylabel('γ_twin', fontsize=11)
    ax3.set_title('γ stability vs t_sym', fontsize=12)
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    # 4. α_pred distribution
    ax4 = axes[1, 1]
    alphas = [r['alpha_pred'] for r in valid]
    ax4.hist(alphas, bins=15, edgecolor='black', alpha=0.7)
    ax4.axvline(x=0.91, color='r', linestyle='--', linewidth=2, label='α_num=0.91')
    ax4.axvline(x=np.mean(alphas), color='g', linestyle='-', linewidth=2,
                label=f'α_pred mean={np.mean(alphas):.3f}')
    ax4.set_xlabel('α_pred = 2 - 2γ', fontsize=11)
    ax4.set_ylabel('Count', fontsize=11)
    ax4.set_title('Distribution of predicted α', fontsize=12)
    ax4.legend()
    ax4.grid(True, alpha=0.3)

    plt.tight_layout()

    if save_fig:
        plt.savefig(save_fig, dpi=150, bbox_inches='tight')
        print(f"Saved figure to {save_fig}")
    plt.show()


def plot_heatmap_and_decay(K: float = 2.0, M: int = 256, X_max: int = 100_000,
                           t_sym: float = 1.0, save_fig: str | None = None):
    """Create comprehensive visualization: heatmap + decay plots."""
    import matplotlib.pyplot as plt
    from matplotlib.colors import LogNorm
    from matplotlib.patches import Rectangle

    H, xi = build_hamiltonian(K, M, X_max, t_sym=t_sym)

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # 1. Heatmap of |H|
    ax1 = axes[0, 0]
    H_abs = np.abs(H) + 1e-10  # avoid log(0)
    im = ax1.imshow(H_abs, norm=LogNorm(), cmap='viridis', aspect='auto')
    plt.colorbar(im, ax=ax1, label='|H_{kl}|')
    ax1.set_xlabel('l index', fontsize=11)
    ax1.set_ylabel('k index', fontsize=11)
    ax1.set_title(f'|H| heatmap (K={K}, M={M}, t_sym={t_sym})', fontsize=12)

    # Mark twin region (center ξ ∈ [0, 0.5])
    # Find indices where ξ ∈ [0, 0.5]
    twin_mask = (xi >= 0) & (xi <= 0.5)
    twin_indices = np.where(twin_mask)[0]
    if len(twin_indices) > 0:
        i_lo, i_hi = twin_indices[0], twin_indices[-1]
        rect = Rectangle((i_lo, i_lo), i_hi-i_lo, i_hi-i_lo,
                         fill=False, edgecolor='red', linewidth=2, linestyle='--')
        ax1.add_patch(rect)
        ax1.text(i_hi+5, i_lo, 'Twin region', color='red', fontsize=10)

    # 2. Global off-diagonal decay
    ax2 = axes[0, 1]
    distances, magnitudes = extract_off_diagonal(H, xi)
    ax2.scatter(distances, magnitudes, alpha=0.2, s=1, c='blue')
    ax2.set_xscale('log')
    ax2.set_yscale('log')
    gamma_g, C_g, r2_g = fit_power_law(distances, magnitudes, min_dist=0.1)
    d_fit = np.logspace(np.log10(0.1), np.log10(distances.max()), 100)
    ax2.plot(d_fit, C_g * d_fit**(-gamma_g), 'r-', linewidth=2,
             label=f'Global: γ={gamma_g:.2f}, R²={r2_g:.2f}')
    ax2.set_xlabel('|ξ_k - ξ_l|', fontsize=11)
    ax2.set_ylabel('|H_{kl}|', fontsize=11)
    ax2.set_title('Global off-diagonal decay', fontsize=12)
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # 3. Twin-region decay
    ax3 = axes[1, 0]
    d_twin, m_twin = extract_off_diagonal_by_center(H, xi, 0.0, 0.5)
    if len(d_twin) > 0:
        ax3.scatter(d_twin, m_twin, alpha=0.3, s=3, c='green')
        ax3.set_xscale('log')
        ax3.set_yscale('log')
        gamma_t, C_t, r2_t = fit_power_law(d_twin, m_twin, min_dist=0.1)
        if not np.isnan(gamma_t):
            d_fit = np.logspace(np.log10(0.1), np.log10(d_twin.max()), 100)
            ax3.plot(d_fit, C_t * d_fit**(-gamma_t), 'r-', linewidth=2,
                     label=f'Twin: γ={gamma_t:.2f}, R²={r2_t:.2f}')
        ax3.set_xlabel('|ξ_k - ξ_l|', fontsize=11)
        ax3.set_ylabel('|H_{kl}|', fontsize=11)
        ax3.set_title('Twin-region decay (center ∈ [0, 0.5])', fontsize=12)
        ax3.legend()
        ax3.grid(True, alpha=0.3)

    # 4. Summary statistics
    ax4 = axes[1, 1]
    ax4.axis('off')
    summary_text = f"""
    PARAMETER SUMMARY
    ─────────────────────
    K = {K}  (spectral window)
    M = {M}  (grid size)
    t_sym = {t_sym}  (kernel scale)
    X_max = {X_max:,}  (prime cutoff)

    GLOBAL FIT
    ─────────────────────
    γ_global = {gamma_g:.4f}
    R²_global = {r2_g:.4f}
    α_pred = {2 - 2*gamma_g:.4f}

    TWIN-REGION FIT
    ─────────────────────
    γ_twin = {gamma_t:.4f}
    R²_twin = {r2_t:.4f}
    α_pred = {2 - 2*gamma_t:.4f}

    COMPARISON
    ─────────────────────
    α_numerical = 0.91
    Δα = {abs(2 - 2*gamma_t - 0.91):.4f}
    Match: {'✓ GOOD' if abs(2 - 2*gamma_t - 0.91) < 0.1 else '✗ CHECK'}
    """
    ax4.text(0.1, 0.5, summary_text, fontsize=11, family='monospace',
             verticalalignment='center', transform=ax4.transAxes)

    plt.tight_layout()

    if save_fig:
        plt.savefig(save_fig, dpi=150, bbox_inches='tight')
        print(f"Saved figure to {save_fig}")
    plt.show()


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1 and sys.argv[1] == "sweep":
        # Full parameter sweep
        results = parameter_sweep(
            K_list=[1.5, 2.0, 2.5, 3.0],
            M_list=[128, 256, 384],
            t_sym_list=[0.5, 1.0, 1.5],
            X_max=100_000,
            twin_center=(0.0, 0.5),
            save_csv="output/gamma_stability_sweep.csv"
        )
        plot_stability_analysis(results, save_fig="output/gamma_stability.png")

    elif len(sys.argv) > 1 and sys.argv[1] == "viz":
        # Comprehensive visualization
        plot_heatmap_and_decay(K=2.0, M=256, X_max=100_000, t_sym=1.0,
                               save_fig="output/off_diagonal_comprehensive.png")

    else:
        # Default: single run
        print("="*60)
        print("OFF-DIAGONAL DECAY ANALYSIS")
        print("="*60)

        result = run_analysis(K=2.0, M=256, X_max=100_000, t_sym=1.0,
                              plot=True, save_fig="output/off_diagonal_decay.png")

        print("\n" + "="*60)
        print("VERIFICATION OF CHEN-Q3 CORRESPONDENCE")
        print("="*60)
        print(f"Measured γ = {result['gamma']:.4f}")
        print(f"Predicted α = 2 - 2γ = {result['alpha_predicted']:.4f}")
        print(f"Numerical α from commutator experiments: 0.91")
        print(f"Match: {'✓ GOOD' if abs(result['alpha_predicted'] - 0.91) < 0.2 else '✗ DISCREPANCY'}")
