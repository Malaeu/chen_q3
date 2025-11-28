#!/usr/bin/env python3
"""
MERLIN KERNEL TEST: Поиск положительно-определённого ядра
Кандидаты:
1. Sinc kernel: sin(πξ)/(πξ)
2. Fejer kernel: (sin(Nξ/2)/sin(ξ/2))²/N
3. Poisson kernel: (1-r²)/(1-2r·cos(θ)+r²)
4. de la Vallée-Poussin
5. Gaussian kernel
6. Mellin-type kernel
"""
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import gamma
import mpmath

pi = np.pi

def sinc_kernel(xi, B=1.0):
    """
    Sinc kernel: sin(πBξ)/(πξ) - идеальный lowpass filter
    Положительная спектральная плотность в [-B, B]
    """
    xi = np.asarray(xi)
    result = np.where(np.abs(xi) < 1e-10, B, np.sin(pi * B * xi) / (pi * xi + 1e-20))
    return result

def fejer_kernel(xi, N=10):
    """
    Fejer kernel: положительно определённое!
    F_N(ξ) = (1/N) * (sin(Nξ/2) / sin(ξ/2))²
    """
    xi = np.asarray(xi)
    result = np.where(np.abs(xi) < 1e-10, N,
                      (np.sin(N * xi / 2) / (np.sin(xi / 2) + 1e-20))**2 / N)
    return result

def poisson_kernel(theta, r=0.9):
    """
    Poisson kernel: P_r(θ) = (1-r²)/(1-2r·cos(θ)+r²)
    Всегда положительно при 0 < r < 1!
    """
    return (1 - r**2) / (1 - 2*r*np.cos(theta) + r**2)

def gauss_kernel(xi, sigma=1.0):
    """
    Gaussian kernel: exp(-ξ²/(2σ²))
    Всегда положительно!
    """
    return np.exp(-xi**2 / (2 * sigma**2))

def mellin_kernel(xi, s=0.5):
    """
    Mellin-type kernel based on |ξ|^{-s}
    С регуляризацией для малых ξ
    """
    xi = np.asarray(xi)
    return 1.0 / (1.0 + np.abs(xi)**s)

def de_brange_kernel(xi, t=1.0):
    """
    de Branges-style kernel: основано на E(z) функции
    Упрощённая версия: exp(-t|ξ|) * cos(ξ)
    """
    xi = np.asarray(xi)
    return np.exp(-t * np.abs(xi)) * np.cos(xi)

def test_kernel_stability(kernel_func, kernel_name, B_values, **kwargs):
    """
    Тестирует ядро на положительность пола через периодизацию.
    """
    theta = np.linspace(-pi, pi, 2000)

    results = []

    print(f"\n{'='*60}")
    print(f"TESTING: {kernel_name}")
    print(f"{'='*60}")
    print(f"{'B':<10} | {'Floor':<15} | {'Ceiling':<15} | {'Ratio δ*':<15}")
    print("-" * 60)

    for B in B_values:
        P_vals = np.zeros_like(theta)

        # Сумма Пуассона
        N_tails = 20
        for n in range(-N_tails, N_tails + 1):
            xi = theta + 2 * pi * n

            # Применяем ядро
            if 'B' in kwargs or kernel_name in ['Sinc', 'Fejer']:
                k_val = kernel_func(xi, B)
            elif kernel_name == 'Poisson':
                # Для Пуассона B интерпретируем как r
                r = 1 - 1/B if B > 1 else 0.5
                k_val = kernel_func(xi, r)
            else:
                k_val = kernel_func(xi, **kwargs)

            # Окно для обрезания
            w_val = np.maximum(0.0, 1.0 - np.abs(xi)/(B * pi))

            P_vals += k_val * w_val

        floor_v = np.min(P_vals)
        ceil_v = np.max(P_vals)
        ratio = floor_v / ceil_v if ceil_v > 0 and floor_v > 0 else 0

        results.append((B, floor_v, ceil_v, ratio))
        print(f"{B:<10.1f} | {floor_v:<15.6f} | {ceil_v:<15.6f} | {ratio:<15.6f}")

    return results

# === MAIN TESTS ===
B_values = [1.0, 2.0, 5.0, 10.0, 20.0]

print("=" * 70)
print("MERLIN KERNEL SEARCH: Finding Positive-Definite Kernel")
print("=" * 70)

# Test different kernels
results_all = {}

# 1. Sinc kernel
results_all['Sinc'] = test_kernel_stability(sinc_kernel, 'Sinc', B_values)

# 2. Fejer kernel
results_all['Fejer'] = test_kernel_stability(fejer_kernel, 'Fejer', B_values)

# 3. Poisson kernel
results_all['Poisson'] = test_kernel_stability(poisson_kernel, 'Poisson', B_values)

# 4. Gaussian kernel
results_all['Gaussian'] = test_kernel_stability(gauss_kernel, 'Gaussian', B_values, sigma=1.0)

# 5. Mellin kernel
results_all['Mellin'] = test_kernel_stability(mellin_kernel, 'Mellin', B_values, s=0.5)

# === VISUALIZATION ===
plt.style.use('dark_background')
fig, axes = plt.subplots(2, 3, figsize=(16, 10))

kernel_names = ['Sinc', 'Fejer', 'Poisson', 'Gaussian', 'Mellin']
colors = ['cyan', 'lime', 'magenta', 'yellow', 'orange']

# Plot kernel shapes
ax_shape = axes[0, 0]
xi_plot = np.linspace(-5, 5, 500)
for name, color in zip(kernel_names[:4], colors[:4]):
    if name == 'Sinc':
        y = [sinc_kernel(x, 1.0) for x in xi_plot]
    elif name == 'Fejer':
        y = [fejer_kernel(x, 10) for x in xi_plot]
    elif name == 'Poisson':
        y = [poisson_kernel(x, 0.8) for x in xi_plot]
    elif name == 'Gaussian':
        y = [gauss_kernel(x, 1.0) for x in xi_plot]
    ax_shape.plot(xi_plot, y, color=color, label=name, linewidth=2)

ax_shape.axhline(0, color='red', linestyle='--', alpha=0.5)
ax_shape.set_xlabel(r'$\xi$')
ax_shape.set_ylabel('Kernel Value')
ax_shape.set_title('Kernel Shapes')
ax_shape.legend()
ax_shape.grid(True, alpha=0.3)
ax_shape.set_xlim(-5, 5)

# Plot Floor for each kernel
for idx, (name, color) in enumerate(zip(kernel_names, colors)):
    if idx < 5:
        ax = axes[(idx+1)//3, (idx+1)%3]
        results = results_all[name]
        B_arr = [r[0] for r in results]
        floors = [r[1] for r in results]
        ceilings = [r[2] for r in results]

        ax.plot(B_arr, floors, 'o-', color='lime', linewidth=2, label='Floor')
        ax.plot(B_arr, ceilings, 'o-', color='cyan', linewidth=2, label='Ceiling')
        ax.axhline(0, color='red', linestyle='--', alpha=0.5)
        ax.set_xlabel('B')
        ax.set_ylabel('Value')
        ax.set_title(f'{name} Kernel')
        ax.legend()
        ax.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('/Users/emalam/Downloads/merlin_kernel_test.png', dpi=150)

# === SUMMARY ===
print("\n" + "=" * 70)
print("SUMMARY: BEST KERNELS FOR POSITIVE FLOOR")
print("=" * 70)

for name in kernel_names:
    results = results_all[name]
    positive_count = sum(1 for r in results if r[1] > 0.001)
    max_ratio = max(r[3] for r in results)
    best_B = max(results, key=lambda x: x[3])

    status = "✅" if positive_count == len(results) else "⚠️" if positive_count > 0 else "❌"
    print(f"{status} {name:<12}: {positive_count}/{len(results)} positive, best δ* = {max_ratio:.4f} at B={best_B[0]}")

# Find the winner
winner = max(kernel_names, key=lambda n: max(r[3] for r in results_all[n]))
winner_ratio = max(r[3] for r in results_all[winner])

print(f"\n🏆 WINNER: {winner} kernel with δ* = {winner_ratio:.4f}")

if winner_ratio > 0.01:
    print("\n🎉 НАЙДЕНО ЯДРО С ПОЛОЖИТЕЛЬНЫМ ПОЛОМ!")
else:
    print("\n⚠️  Все ядра имеют слабый пол, нужны модификации")

print("\n✅ Saved: merlin_kernel_test.png")
