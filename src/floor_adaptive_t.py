#!/usr/bin/env python3
"""
ТЕСТ: Адаптивное t для режима перекрытия окон
Идея: t = c / B^α чтобы окно расширялось с ростом B
"""
from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt
import mpmath

pi = np.pi
OUTPUT_DIR = Path(__file__).resolve().parent.parent / "output"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

def a_digamma(xi):
    """Реальная функция a(ξ) через дигамму"""
    z = 0.25 + 1j * pi * xi
    return np.log(pi) - float(mpmath.re(mpmath.psi(0, z)))

def compute_floor_ceiling(B, t_param):
    """
    Вычисляет Floor и Ceiling для данных B и t.
    g(ξ) = a(ξ) · W(ξ)
    W(ξ) = (1 - |ξ|/B) · exp(-4π²t·ξ²)
    """
    C_gauss = 4 * (pi**2) * t_param

    # Сканируем по ξ от 0 до B
    N_points = 500
    xi_vals = np.linspace(0, min(B, 5.0), N_points)  # ограничиваем до 5

    g_vals = []
    for xi in xi_vals:
        a_val = a_digamma(xi)
        tri = max(0.0, 1.0 - abs(xi)/B)
        gauss = np.exp(-C_gauss * xi**2)
        W = tri * gauss
        g = a_val * W
        g_vals.append(g)

    g_vals = np.array(g_vals)

    floor_val = np.min(g_vals)
    ceiling_val = np.max(g_vals)

    # Эффективная ширина окна (где gauss > 0.01)
    effective_width = np.sqrt(-np.log(0.01) / C_gauss) if C_gauss > 0 else np.inf

    return floor_val, ceiling_val, effective_width

# === РЕЖИМ 1: Фиксированное t (старый тест) ===
print("=" * 70)
print("РЕЖИМ 1: ФИКСИРОВАННОЕ t = 0.7 (старый тест)")
print("=" * 70)
print(f"{'B':<8} | {'t':<10} | {'Width':<10} | {'Floor':<12} | {'Ceiling':<12}")
print("-" * 70)

B_values = [0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 50.0]
for B in B_values:
    t_fixed = 0.7
    floor_v, ceil_v, width = compute_floor_ceiling(B, t_fixed)
    print(f"{B:<8.1f} | {t_fixed:<10.4f} | {width:<10.3f} | {floor_v:<12.6f} | {ceil_v:<12.6f}")

# === РЕЖИМ 2: Адаптивное t = c/B² ===
print("\n" + "=" * 70)
print("РЕЖИМ 2: АДАПТИВНОЕ t = 0.1 / B² (режим перекрытия)")
print("=" * 70)
print(f"{'B':<8} | {'t':<10} | {'Width':<10} | {'Floor':<12} | {'Ceiling':<12} | {'Gap':<10}")
print("-" * 70)

results_adaptive = []
for B in B_values:
    t_adaptive = 0.1 / (B**2)  # t уменьшается как 1/B²
    floor_v, ceil_v, width = compute_floor_ceiling(B, t_adaptive)
    gap = ceil_v - floor_v if floor_v > 0 else 0
    results_adaptive.append((B, t_adaptive, floor_v, ceil_v, width))
    print(f"{B:<8.1f} | {t_adaptive:<10.6f} | {width:<10.3f} | {floor_v:<12.6f} | {ceil_v:<12.6f} | {gap:<10.4f}")

# === РЕЖИМ 3: Адаптивное t = c/B (более мягкое) ===
print("\n" + "=" * 70)
print("РЕЖИМ 3: АДАПТИВНОЕ t = 0.5 / B (мягкое перекрытие)")
print("=" * 70)
print(f"{'B':<8} | {'t':<10} | {'Width':<10} | {'Floor':<12} | {'Ceiling':<12} | {'Gap':<10}")
print("-" * 70)

results_soft = []
for B in B_values:
    t_soft = 0.5 / B  # t уменьшается как 1/B
    floor_v, ceil_v, width = compute_floor_ceiling(B, t_soft)
    gap = ceil_v - floor_v if floor_v > 0 else 0
    results_soft.append((B, t_soft, floor_v, ceil_v, width))
    print(f"{B:<8.1f} | {t_soft:<10.6f} | {width:<10.3f} | {floor_v:<12.6f} | {ceil_v:<12.6f} | {gap:<10.4f}")

# === РЕЖИМ 4: Константная эффективная ширина ===
print("\n" + "=" * 70)
print("РЕЖИМ 4: КОНСТАНТНАЯ ШИРИНА = B (окно всегда покрывает период)")
print("=" * 70)
print(f"{'B':<8} | {'t':<10} | {'Width':<10} | {'Floor':<12} | {'Ceiling':<12} | {'Gap':<10}")
print("-" * 70)

# Хотим width ≈ B, т.е. sqrt(-ln(0.01)/(4π²t)) = B
# => t = -ln(0.01) / (4π² B²) ≈ 4.6 / (4π² B²) ≈ 0.117 / B²
results_const_width = []
for B in B_values:
    t_const = 0.117 / (B**2)  # обеспечивает width ≈ B
    floor_v, ceil_v, width = compute_floor_ceiling(B, t_const)
    gap = ceil_v - floor_v if floor_v > 0 else 0
    results_const_width.append((B, t_const, floor_v, ceil_v, width))
    print(f"{B:<8.1f} | {t_const:<10.6f} | {width:<10.3f} | {floor_v:<12.6f} | {ceil_v:<12.6f} | {gap:<10.4f}")

# === Визуализация ===
plt.style.use('dark_background')
fig, axes = plt.subplots(2, 2, figsize=(14, 10))

# График 1: Сравнение Floor для разных режимов
ax1 = axes[0, 0]
B_arr = np.array(B_values)
floors_fixed = [compute_floor_ceiling(B, 0.7)[0] for B in B_values]
floors_adaptive = [r[2] for r in results_adaptive]
floors_soft = [r[2] for r in results_soft]
floors_const = [r[2] for r in results_const_width]

ax1.plot(B_arr, floors_fixed, 'r-o', label='t=0.7 (fixed)', linewidth=2)
ax1.plot(B_arr, floors_adaptive, 'c-o', label='t=0.1/B² (adaptive)', linewidth=2)
ax1.plot(B_arr, floors_soft, '-o', color='lime', label='t=0.5/B (soft)', linewidth=2)
ax1.plot(B_arr, floors_const, 'm-o', label='t=0.117/B² (const width)', linewidth=2)
ax1.axhline(y=0, color='yellow', linestyle='--', alpha=0.5)
ax1.set_xlabel('Bandwidth B')
ax1.set_ylabel('Floor (Min g)')
ax1.set_title('Floor Comparison: Fixed vs Adaptive t')
ax1.legend()
ax1.grid(True, alpha=0.3)
ax1.set_xscale('log')

# График 2: Эффективная ширина окна
ax2 = axes[0, 1]
widths_fixed = [compute_floor_ceiling(B, 0.7)[2] for B in B_values]
widths_adaptive = [r[4] for r in results_adaptive]
widths_soft = [r[4] for r in results_soft]
widths_const = [r[4] for r in results_const_width]

ax2.plot(B_arr, widths_fixed, 'r-o', label='t=0.7 (fixed)', linewidth=2)
ax2.plot(B_arr, widths_adaptive, 'c-o', label='t=0.1/B²', linewidth=2)
ax2.plot(B_arr, widths_soft, '-o', color='lime', label='t=0.5/B', linewidth=2)
ax2.plot(B_arr, widths_const, 'm-o', label='t=0.117/B²', linewidth=2)
ax2.plot(B_arr, B_arr, 'w--', alpha=0.5, label='Width = B (ideal)')
ax2.set_xlabel('Bandwidth B')
ax2.set_ylabel('Effective Window Width')
ax2.set_title('Window Width: Need Width ~ B for Coverage')
ax2.legend()
ax2.grid(True, alpha=0.3)
ax2.set_xscale('log')
ax2.set_yscale('log')

# График 3: Функция g(ξ) для разных t при фиксированном B=5
ax3 = axes[1, 0]
B_demo = 5.0
xi_demo = np.linspace(0, B_demo, 200)

for t_val, label, color in [(0.7, 't=0.7', 'red'),
                             (0.1/25, 't=0.1/B²', 'cyan'),
                             (0.5/5, 't=0.5/B', 'lime')]:
    g_demo = []
    C_g = 4 * pi**2 * t_val
    for xi in xi_demo:
        a_v = a_digamma(xi)
        tri = max(0.0, 1.0 - abs(xi)/B_demo)
        gauss = np.exp(-C_g * xi**2)
        g_demo.append(a_v * tri * gauss)
    ax3.plot(xi_demo, g_demo, label=label, color=color, linewidth=2)

ax3.axhline(y=0, color='yellow', linestyle='--', alpha=0.5)
ax3.set_xlabel('ξ')
ax3.set_ylabel('g(ξ) = a(ξ)·W(ξ)')
ax3.set_title(f'Function g(ξ) for B={B_demo}: Different t Regimes')
ax3.legend()
ax3.grid(True, alpha=0.3)

# График 4: Gap (Ceiling - Floor) если Floor > 0
ax4 = axes[1, 1]
gaps_adaptive = [r[3] - r[2] if r[2] > 0 else 0 for r in results_adaptive]
gaps_soft = [r[3] - r[2] if r[2] > 0 else 0 for r in results_soft]
gaps_const = [r[3] - r[2] if r[2] > 0 else 0 for r in results_const_width]

ax4.bar(np.array(range(len(B_values)))-0.2, gaps_adaptive, 0.2, label='t=0.1/B²', color='cyan')
ax4.bar(np.array(range(len(B_values))), gaps_soft, 0.2, label='t=0.5/B', color='lime')
ax4.bar(np.array(range(len(B_values)))+0.2, gaps_const, 0.2, label='t=0.117/B²', color='magenta')
ax4.set_xticks(range(len(B_values)))
ax4.set_xticklabels([str(b) for b in B_values])
ax4.set_xlabel('Bandwidth B')
ax4.set_ylabel('Gap = Ceiling - Floor (if Floor > 0)')
ax4.set_title('Stability Gap for Adaptive t Regimes')
ax4.legend()
ax4.grid(True, alpha=0.3)

plt.tight_layout()
plot_path = OUTPUT_DIR / "floor_adaptive_comparison.png"
plt.savefig(plot_path, dpi=150)
print(f"\n✅ Saved: {plot_path}")

# === ФИНАЛЬНЫЙ ВЕРДИКТ ===
print("\n" + "=" * 70)
print("ФИНАЛЬНЫЙ ВЕРДИКТ")
print("=" * 70)

best_regime = None
for name, results in [("t=0.1/B²", results_adaptive),
                       ("t=0.5/B", results_soft),
                       ("t=0.117/B²", results_const_width)]:
    positive_floors = sum(1 for r in results if r[2] > 0.001)
    min_floor = min(r[2] for r in results)
    print(f"{name}: {positive_floors}/{len(results)} положительных полов, min Floor = {min_floor:.6f}")
    if positive_floors > 0 and (best_regime is None or min_floor > best_regime[1]):
        best_regime = (name, min_floor)

if best_regime:
    print(f"\n🏆 ЛУЧШИЙ РЕЖИМ: {best_regime[0]} с min Floor = {best_regime[1]:.6f}")
else:
    print("\n❌ ВСЕ РЕЖИМЫ ПРОВАЛИЛИСЬ - нужна другая стратегия")
