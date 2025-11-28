#!/usr/bin/env python3
"""
СПАСАТЕЛЬНАЯ МИССИЯ: Гамма-метрика вместо Дигамма-яда
Гипотеза: |Γ(1/4 + iπξ)|² дает стабильный положительный пол
"""
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import gamma
import mpmath

def get_gamma_metric(xi, power=1):
    """
    Кандидат на "Правильный" Архимедов Символ.
    Основан на модуле Гамма-функции (Metric Factor).

    Варианты:
    power=1: |Gamma(1/4 + i*pi*xi)|
    power=2: |Gamma(1/4 + i*pi*xi)|^2  (Вес в L2 пространстве)
    """
    z = 0.25 + 1j * np.pi * xi
    val = np.abs(gamma(z))
    return val**power

def test_metric_stability(power_mode=2):
    """
    Проверяет, дает ли Гамма-метрика стабильный ПОЛОЖИТЕЛЬНЫЙ пол.
    """
    theta = np.linspace(-np.pi, np.pi, 2000)
    B_values = [0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 50.0]

    results_B = []
    results_Floor = []
    results_Ceiling = []

    print(f"TESTING GAMMA METRIC (Power={power_mode})")
    print(f"{'B':<10} | {'Floor (Min)':<15} | {'Ceiling (Max)':<15} | {'Gap Ratio':<15}")
    print("-" * 65)

    for B in B_values:
        P_A_vals = np.zeros_like(theta)

        # Суммируем достаточно хвостов (Гамма убывает быстро, 10 хватит)
        N_tails = 10

        for n in range(-N_tails, N_tails + 1):
            xi = theta + 2 * np.pi * n

            # 1. Metric Function (Gamma)
            a_val = get_gamma_metric(xi, power=power_mode)

            # 2. Window Function (Linear decay)
            w_val = np.maximum(0.0, 1.0 - np.abs(xi)/B)

            term = a_val * w_val
            P_A_vals += term

        floor_val = np.min(P_A_vals)
        ceiling_val = np.max(P_A_vals)

        results_B.append(B)
        results_Floor.append(floor_val)
        results_Ceiling.append(ceiling_val)

        gap = floor_val / ceiling_val if ceiling_val > 0 else 0
        print(f"{B:<10.1f} | {floor_val:<15.4f} | {ceiling_val:<15.4f} | {gap:<15.4f}")

    return results_B, results_Floor, results_Ceiling

# --- MAIN TEST ---
print("=" * 65)
print("RESCUE MISSION: GAMMA METRIC vs DIGAMMA POISON")
print("=" * 65)

# Test Power=2 (Squared Norm - most likely for Hilbert Space weight)
B_vals, floors, ceilings = test_metric_stability(power_mode=2)

# --- VISUALIZATION ---
plt.figure(figsize=(14, 6))
plt.style.use('dark_background')

# Left: Source Function Comparison
plt.subplot(1, 2, 1)
xi_plot = np.linspace(0, 5, 500)
gamma_vals = [get_gamma_metric(x, 2) for x in xi_plot]
digamma_vals = [np.log(np.pi) - float(mpmath.re(mpmath.psi(0, 0.25 + 1j*np.pi*x))) for x in xi_plot]

plt.plot(xi_plot, gamma_vals, 'lime', linewidth=2, label=r'Gamma Metric $|\Gamma|^2$ (Medicine)')
plt.plot(xi_plot, digamma_vals, 'red', linewidth=2, label=r'Digamma Trace $\log\pi - Re(\psi)$ (Poison)')
plt.axhline(0, color='white', linestyle='--', alpha=0.5)
plt.fill_between(xi_plot, digamma_vals, 0, where=np.array(digamma_vals) < 0,
                  color='red', alpha=0.3, label='Poison Zone')
plt.xlabel(r'$\xi$')
plt.ylabel('Value')
plt.title('Source Function Comparison: Gamma vs Digamma')
plt.legend(loc='upper right')
plt.grid(True, alpha=0.2)
plt.xlim(0, 5)

# Right: Spectral Stability
plt.subplot(1, 2, 2)
plt.plot(B_vals, floors, 'o-', color='lime', linewidth=2, markersize=8, label='Floor (Gamma Metric)')
plt.plot(B_vals, ceilings, 'o-', color='cyan', linewidth=2, markersize=8, label='Ceiling (Gamma Metric)')
plt.axhline(0, color='red', linestyle='--', alpha=0.5, label='Zero Line')
plt.xlabel('Bandwidth B')
plt.ylabel('Value')
plt.title('Spectral Stability with Gamma Metric')
plt.legend()
plt.grid(True, alpha=0.2)
plt.xscale('log')

plt.tight_layout()
plt.savefig('/Users/emalam/Downloads/rescue_archimedes.png', dpi=150)

# --- VERDICT ---
print("\n" + "=" * 65)
print("RESCUE MISSION VERDICT")
print("=" * 65)

positive_floors = sum(1 for f in floors if f > 0.001)
min_floor = min(floors)
max_ceiling = max(ceilings)

if positive_floors == len(floors) and min_floor > 0:
    print(f"✅ SUCCESS! ALL FLOORS POSITIVE!")
    print(f"   Min Floor = {min_floor:.6f}")
    print(f"   Max Ceiling = {max_ceiling:.6f}")
    print(f"   Stability Ratio δ* = {min_floor/max_ceiling:.6f}")
    print("\n🎉 ГАММА-МЕТРИКА СПАСАЕТ ДОКАЗАТЕЛЬСТВО!")
    print("   Замена: log(π) - Re(ψ) → |Γ(1/4 + iπξ)|²")
else:
    print(f"❌ PARTIAL SUCCESS: {positive_floors}/{len(floors)} positive floors")
    print(f"   Min Floor = {min_floor:.6f}")

print("\n✅ Saved: rescue_archimedes.png")
