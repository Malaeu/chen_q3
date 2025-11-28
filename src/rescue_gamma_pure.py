#!/usr/bin/env python3
"""
СПАСАТЕЛЬНАЯ МИССИЯ v2: Чистая Гамма-метрика без окна
Идея: Гамма сама себя обрезает экспоненциально, окно не нужно!
"""
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import gamma
import mpmath

def get_gamma_metric(xi, power=2):
    """
    |Γ(1/4 + iπξ)|^power
    """
    z = 0.25 + 1j * np.pi * xi
    val = np.abs(gamma(z))
    return val**power

def poisson_sum_gamma(theta, N_tails=20, power=2):
    """
    Сумма Пуассона для Гамма-метрики:
    P_Γ(θ) = Σ_n |Γ(1/4 + iπ(θ + 2πn))|^power

    Гамма сама обеспечивает сходимость за счет экспоненциального затухания!
    """
    result = 0.0
    for n in range(-N_tails, N_tails + 1):
        xi = theta + 2 * np.pi * n
        result += get_gamma_metric(xi, power)
    return result

def test_pure_gamma():
    """
    Тест чистой Гамма-периодизации без окна.
    """
    theta = np.linspace(-np.pi, np.pi, 2000)

    print("=" * 65)
    print("PURE GAMMA POISSON SUM (No Window)")
    print("P_Γ(θ) = Σ_n |Γ(1/4 + iπ(θ + 2πn))|²")
    print("=" * 65)

    # Compute P_Γ for all theta
    P_gamma = np.array([poisson_sum_gamma(t) for t in theta])

    floor_val = np.min(P_gamma)
    ceiling_val = np.max(P_gamma)

    print(f"\nFloor (Min):     {floor_val:.10f}")
    print(f"Ceiling (Max):   {ceiling_val:.10f}")
    print(f"Gap Ratio:       {floor_val/ceiling_val:.10f}")

    # Check where min/max occur
    idx_min = np.argmin(P_gamma)
    idx_max = np.argmax(P_gamma)
    print(f"\nMin at θ = {theta[idx_min]:.4f} (π = {theta[idx_min]/np.pi:.4f}π)")
    print(f"Max at θ = {theta[idx_max]:.4f} (π = {theta[idx_max]/np.pi:.4f}π)")

    return theta, P_gamma, floor_val, ceiling_val

# --- TEST ---
theta, P_gamma, floor_val, ceiling_val = test_pure_gamma()

# --- ТЕПЕРЬ ТЕСТ С ЧАСТОТНЫМ ОБРЕЗАНИЕМ ---
print("\n" + "=" * 65)
print("GAMMA WITH BANDWIDTH CUTOFF (Toeplitz Operator)")
print("=" * 65)

def test_gamma_with_bandwidth():
    """
    Теперь с обрезанием по bandwidth:
    P_Γ,B(θ) = Σ_{|n| ≤ N} |Γ(1/4 + iπ(θ + 2πn))|² · I(|θ + 2πn| ≤ B)

    Но вместо резкого обрезания - используем мягкое затухание.
    """
    theta = np.linspace(-np.pi, np.pi, 2000)
    B_values = [np.pi, 2*np.pi, 3*np.pi, 5*np.pi, 10*np.pi]

    results = []

    print(f"{'B/π':<10} | {'Floor':<15} | {'Ceiling':<15} | {'Ratio':<15}")
    print("-" * 60)

    for B in B_values:
        P_vals = np.zeros_like(theta)

        for n in range(-20, 21):
            xi = theta + 2 * np.pi * n

            # Гамма-метрика
            a_val = get_gamma_metric(xi, power=2)

            # Мягкое гауссово окно вместо резкого
            # w = exp(-(xi/B)^2) так что вклад плавно уменьшается
            w_val = np.exp(-(xi/B)**2)

            P_vals += a_val * w_val

        floor_v = np.min(P_vals)
        ceil_v = np.max(P_vals)
        ratio = floor_v / ceil_v if ceil_v > 0 else 0

        results.append((B/np.pi, floor_v, ceil_v, ratio))
        print(f"{B/np.pi:<10.1f} | {floor_v:<15.6f} | {ceil_v:<15.6f} | {ratio:<15.6f}")

    return results

results_bw = test_gamma_with_bandwidth()

# --- VISUALIZATION ---
plt.style.use('dark_background')
fig, axes = plt.subplots(2, 2, figsize=(14, 10))

# 1. Pure Gamma Poisson Sum
ax1 = axes[0, 0]
ax1.plot(theta, P_gamma, 'lime', linewidth=2)
ax1.axhline(floor_val, color='cyan', linestyle='--', alpha=0.7, label=f'Floor = {floor_val:.2e}')
ax1.axhline(ceiling_val, color='magenta', linestyle='--', alpha=0.7, label=f'Ceiling = {ceiling_val:.4f}')
ax1.set_xlabel(r'$\theta$')
ax1.set_ylabel(r'$P_\Gamma(\theta)$')
ax1.set_title(r'Pure Gamma Poisson Sum: $\sum_n |\Gamma(1/4 + i\pi(\theta + 2\pi n))|^2$')
ax1.legend()
ax1.grid(True, alpha=0.3)

# 2. Gamma function decay
ax2 = axes[0, 1]
xi_range = np.linspace(-10, 10, 500)
gamma_decay = [get_gamma_metric(x, 2) for x in xi_range]
ax2.plot(xi_range, gamma_decay, 'lime', linewidth=2)
ax2.axhline(0, color='white', linestyle='--', alpha=0.3)
ax2.set_xlabel(r'$\xi$')
ax2.set_ylabel(r'$|\Gamma(1/4 + i\pi\xi)|^2$')
ax2.set_title('Gamma Metric Decay (Always Positive!)')
ax2.set_yscale('log')
ax2.grid(True, alpha=0.3)

# 3. Floor vs Bandwidth
ax3 = axes[1, 0]
B_pi = [r[0] for r in results_bw]
floors = [r[1] for r in results_bw]
ceilings = [r[2] for r in results_bw]
ax3.plot(B_pi, floors, 'o-', color='lime', linewidth=2, markersize=8, label='Floor')
ax3.plot(B_pi, ceilings, 'o-', color='cyan', linewidth=2, markersize=8, label='Ceiling')
ax3.axhline(0, color='red', linestyle='--', alpha=0.5)
ax3.set_xlabel(r'Bandwidth $B/\pi$')
ax3.set_ylabel('Value')
ax3.set_title('Gamma Metric with Gaussian Window')
ax3.legend()
ax3.grid(True, alpha=0.3)

# 4. Ratio δ* vs Bandwidth
ax4 = axes[1, 1]
ratios = [r[3] for r in results_bw]
ax4.plot(B_pi, ratios, 'o-', color='yellow', linewidth=2, markersize=10)
ax4.set_xlabel(r'Bandwidth $B/\pi$')
ax4.set_ylabel(r'$\delta_* = Floor/Ceiling$')
ax4.set_title(r'Stability Ratio $\delta_*$ (Target: $\delta_* > 0$)')
ax4.grid(True, alpha=0.3)
ax4.set_ylim(0, 1)

plt.tight_layout()
plt.savefig('/Users/emalam/Downloads/rescue_gamma_pure.png', dpi=150)

# --- FINAL VERDICT ---
print("\n" + "=" * 65)
print("FINAL VERDICT")
print("=" * 65)

if floor_val > 1e-10:
    print(f"✅ PURE GAMMA: Floor = {floor_val:.2e} > 0")
else:
    print(f"⚠️  PURE GAMMA: Floor = {floor_val:.2e} ≈ 0 (numerical)")

best_result = max(results_bw, key=lambda x: x[3])
print(f"\n🏆 BEST BANDWIDTH: B = {best_result[0]:.1f}π")
print(f"   Floor = {best_result[1]:.6f}")
print(f"   Ceiling = {best_result[2]:.6f}")
print(f"   δ* = {best_result[3]:.6f}")

if best_result[3] > 0.01:
    print("\n🎉 ГАММА-МЕТРИКА РАБОТАЕТ! δ* > 0")
else:
    print("\n⚠️  δ* слишком мал, нужны дополнительные исследования")

print("\n✅ Saved: rescue_gamma_pure.png")
