#!/usr/bin/env python3
"""
АНАЛИЗ: Где дигамма становится "ядовитой"?
Исследуем a(ξ) = log(π) - Re(ψ(1/4 + iπξ))
"""
import numpy as np
import matplotlib.pyplot as plt
import mpmath

pi = np.pi
log_pi = np.log(pi)

def a_digamma(xi):
    """a(ξ) = log(π) - Re(ψ(1/4 + iπξ))"""
    z = 0.25 + 1j * pi * xi
    re_psi = float(mpmath.re(mpmath.psi(0, z)))
    return log_pi - re_psi

def re_psi(xi):
    """Re(ψ(1/4 + iπξ))"""
    z = 0.25 + 1j * pi * xi
    return float(mpmath.re(mpmath.psi(0, z)))

# Сканируем ξ от 0 до 10
xi_range = np.linspace(0, 10, 500)

a_vals = [a_digamma(xi) for xi in xi_range]
psi_vals = [re_psi(xi) for xi in xi_range]

# Находим где a(ξ) меняет знак
zero_crossings = []
for i in range(len(a_vals)-1):
    if a_vals[i] * a_vals[i+1] < 0:
        # Линейная интерполяция
        xi_zero = xi_range[i] - a_vals[i] * (xi_range[i+1] - xi_range[i]) / (a_vals[i+1] - a_vals[i])
        zero_crossings.append(xi_zero)

print("=" * 60)
print("АНАЛИЗ ДИГАММЫ: a(ξ) = log(π) - Re(ψ(1/4 + iπξ))")
print("=" * 60)
print(f"log(π) = {log_pi:.6f}")
print(f"\nЗначения a(ξ) в ключевых точках:")
for xi_test in [0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0]:
    a_v = a_digamma(xi_test)
    psi_v = re_psi(xi_test)
    status = "✅ > 0" if a_v > 0 else "❌ < 0"
    print(f"  ξ = {xi_test:4.1f}: a(ξ) = {a_v:8.4f}, Re(ψ) = {psi_v:8.4f} {status}")

print(f"\n🔴 НУЛИ a(ξ) (где становится отрицательной):")
for zc in zero_crossings:
    print(f"  ξ ≈ {zc:.4f}")

print(f"\n📊 Статистика:")
print(f"  min a(ξ) в [0,10] = {min(a_vals):.4f} при ξ ≈ {xi_range[np.argmin(a_vals)]:.2f}")
print(f"  max a(ξ) в [0,10] = {max(a_vals):.4f} при ξ ≈ {xi_range[np.argmax(a_vals)]:.2f}")

# === Визуализация ===
plt.style.use('dark_background')
fig, axes = plt.subplots(2, 2, figsize=(14, 10))

# График 1: a(ξ) vs ξ
ax1 = axes[0, 0]
ax1.plot(xi_range, a_vals, 'cyan', linewidth=2, label='a(ξ) = log(π) - Re(ψ)')
ax1.axhline(y=0, color='red', linestyle='--', linewidth=1.5, label='Нулевая линия')
ax1.axhline(y=log_pi, color='yellow', linestyle=':', alpha=0.5, label=f'log(π) = {log_pi:.3f}')
for zc in zero_crossings[:3]:  # первые 3 нуля
    ax1.axvline(x=zc, color='magenta', linestyle='--', alpha=0.5)
    ax1.annotate(f'ξ={zc:.2f}', (zc, 0.5), color='magenta', fontsize=9)
ax1.fill_between(xi_range, a_vals, 0, where=np.array(a_vals) < 0,
                  color='red', alpha=0.3, label='Ядовитая зона')
ax1.set_xlabel('ξ')
ax1.set_ylabel('a(ξ)')
ax1.set_title('Функция a(ξ): Где она становится отрицательной?')
ax1.legend(loc='upper right')
ax1.grid(True, alpha=0.3)
ax1.set_xlim(0, 10)

# График 2: Re(ψ) vs ξ
ax2 = axes[0, 1]
ax2.plot(xi_range, psi_vals, 'lime', linewidth=2, label='Re(ψ(1/4 + iπξ))')
ax2.axhline(y=log_pi, color='yellow', linestyle='--', linewidth=1.5, label=f'log(π) = {log_pi:.3f}')
ax2.fill_between(xi_range, psi_vals, log_pi, where=np.array(psi_vals) > log_pi,
                  color='red', alpha=0.3, label='Re(ψ) > log(π) → a(ξ) < 0')
ax2.set_xlabel('ξ')
ax2.set_ylabel('Re(ψ)')
ax2.set_title('Дигамма Re(ψ): Где она превышает log(π)?')
ax2.legend(loc='upper right')
ax2.grid(True, alpha=0.3)
ax2.set_xlim(0, 10)

# График 3: Периодическая структура (ξ mod 1)
ax3 = axes[1, 0]
xi_fine = np.linspace(0, 5, 1000)
a_fine = [a_digamma(xi) for xi in xi_fine]
ax3.plot(xi_fine, a_fine, 'cyan', linewidth=1.5)
ax3.axhline(y=0, color='red', linestyle='--', linewidth=1)
ax3.set_xlabel('ξ')
ax3.set_ylabel('a(ξ)')
ax3.set_title('Детальная структура a(ξ) в [0, 5]')
ax3.grid(True, alpha=0.3)

# Добавляем вертикальные линии на целых ξ
for n in range(6):
    ax3.axvline(x=n, color='white', linestyle=':', alpha=0.3)

# График 4: Альтернативные конструкции
ax4 = axes[1, 1]

# Попробуем |a(ξ)|, exp(-|a(ξ)|), |Γ|² etc.
a_abs = [abs(a_digamma(xi)) for xi in xi_range]
a_exp = [np.exp(-abs(a_digamma(xi))) for xi in xi_range]

# |Γ(1/4 + iπξ)|²
def gamma_sq(xi):
    z = 0.25 + 1j * pi * xi
    g = mpmath.gamma(z)
    return float(abs(g)**2)

gamma_vals = [gamma_sq(xi) for xi in xi_range[:100]]  # только первые 100 для скорости

ax4.plot(xi_range, a_abs, 'cyan', linewidth=2, label='|a(ξ)|')
ax4.plot(xi_range, a_exp, 'lime', linewidth=2, label='exp(-|a(ξ)|)')
ax4.plot(xi_range[:100], np.array(gamma_vals)/max(gamma_vals), 'm', linewidth=2, label='|Γ|² (normalized)')
ax4.axhline(y=0, color='red', linestyle='--', alpha=0.5)
ax4.set_xlabel('ξ')
ax4.set_ylabel('Value')
ax4.set_title('Альтернативные конструкции (всегда ≥ 0)')
ax4.legend()
ax4.grid(True, alpha=0.3)
ax4.set_xlim(0, 10)

plt.tight_layout()
plt.savefig('/Users/emalam/Downloads/digamma_poison_analysis.png', dpi=150)
print("\n✅ Saved: digamma_poison_analysis.png")

# === ВЫВОД ===
print("\n" + "=" * 60)
print("ВЫВОД: ПОЧЕМУ a(ξ) НЕ МОЖЕТ ДАТЬ ПОЛОЖИТЕЛЬНЫЙ ПОЛ")
print("=" * 60)
print("""
ПРОБЛЕМА:
  a(ξ) = log(π) - Re(ψ(1/4 + iπξ))

  При ξ → ∞, Re(ψ) осциллирует около log(πξ) + O(1/ξ)
  Это означает Re(ψ) > log(π) для достаточно больших ξ
  → a(ξ) < 0 в этих областях

СЛЕДСТВИЕ:
  1. Узкое окно: не захватываем отрицательные области, но Floor = 0 (дыры)
  2. Широкое окно: захватываем отрицательные области, Floor < 0

  ЭТО ЛОВУШКА БЕЗ ВЫХОДА для функции a(ξ) в текущей форме.

ВОЗМОЖНЫЕ РЕШЕНИЯ:
  1. Использовать |a(ξ)|² вместо a(ξ)
  2. Использовать exp(a(ξ)) - всегда положительна
  3. Использовать |Γ(1/4 + iπξ)|² - квадрат модуля гамма-функции
  4. Пересмотреть исходную конструкцию Q3
""")
