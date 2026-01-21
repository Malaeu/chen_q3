#!/usr/bin/env python3.11
"""
Пример анализа выражения kernel A t x >= c * A * exp(-t/A)
с помощью norm_balancer.py

Это демонстрирует, как вывод транслируется в тактики Lean.
"""

import sympy as sp
from sympy import symbols, exp, sqrt, pi, integrate, oo
import numpy as np
from typing import Dict

# ============================================================================
# ОПРЕДЕЛЕНИЯ
# ============================================================================

# Переменные
A, t, x = symbols('A t x', real=True, positive=True)
c = symbols('c', real=True, positive=True)

# Типичное определение heat kernel
# kernel(A, t, x) = (1 / sqrt(4 * pi * A * t)) * exp(-x^2 / (4 * A * t))
kernel_expr = (1 / sp.sqrt(4 * sp.pi * A * t)) * sp.exp(-x**2 / (4 * A * t))

# Нижняя граница (упрощённая форма)
# P_lower_bound(A, t) = c * A * exp(-t/A)
lower_bound_expr = c * A * sp.exp(-t / A)

print("=" * 70)
print("АНАЛИЗ: kernel(A, t, x) vs c * A * exp(-t/A)")
print("=" * 70)
print()
print(f"kernel(A, t, x) = {kernel_expr}")
print(f"lower_bound(A, t) = {lower_bound_expr}")
print()

# ============================================================================
# ШАГ 1: ЧИСЛЕННЫЙ АНАЛИЗ
# ============================================================================

print("-" * 50)
print("ШАГ 1: ЧИСЛЕННЫЙ АНАЛИЗ (10,000 точек)")
print("-" * 50)

# Создаём вычисляемые функции
kernel_func = sp.lambdify([A, t, x], kernel_expr, 'numpy')

# Для интеграла kernel по x от 0 до ∞
# ∫ kernel dx = 1/2 (для heat kernel)
# Поэтому сравниваем интеграл с lower_bound

def integrated_kernel(A_val, t_val):
    """Интеграл kernel по x от 0 до ∞"""
    # Для heat kernel: ∫₀^∞ kernel dx = 1/2
    return 0.5

def lower_bound_func(A_val, t_val, c_val=0.5):
    """Нижняя граница"""
    return c_val * A_val * np.exp(-t_val / A_val)

# Генерируем тестовые точки
n_samples = 10000
A_vals = np.random.uniform(0.1, 10, n_samples)
t_vals = np.random.uniform(0.1, 10, n_samples)

# Вычисляем значения
lhs_vals = np.array([integrated_kernel(a, t) for a, t in zip(A_vals, t_vals)])
rhs_vals = np.array([lower_bound_func(a, t) for a, t in zip(A_vals, t_vals)])

# Статистика
print(f"LHS (∫ kernel dx): mean={np.mean(lhs_vals):.4f}, std={np.std(lhs_vals):.4f}")
print(f"RHS (c*A*exp(-t/A)): mean={np.mean(rhs_vals):.4f}, std={np.std(rhs_vals):.4f}")
print()

# Находим оптимальный коэффициент
k_optimal = np.sum(lhs_vals * rhs_vals) / np.sum(rhs_vals**2)
print(f"Оптимальный коэффициент k (LHS ≈ k * RHS): {k_optimal:.6f}")

# Отношения
with np.errstate(divide='ignore', invalid='ignore'):
    ratios = np.where(np.abs(rhs_vals) > 1e-10, lhs_vals / rhs_vals, np.nan)
ratios = ratios[np.isfinite(ratios)]

print(f"Минимальное отношение LHS/RHS: {np.min(ratios):.6f}")
print(f"Максимальное отношение LHS/RHS: {np.max(ratios):.6f}")
print(f"Медианное отношение: {np.median(ratios):.6f}")
print()

# Проверка неравенства
diff_vals = lhs_vals - rhs_vals
violations = np.sum(diff_vals < -1e-10)
print(f"Нарушений неравенства: {violations} из {n_samples}")
print(f"Минимальная разность (LHS - RHS): {np.min(diff_vals):.6f}")
print()

# ============================================================================
# ШАГ 2: ИНТЕРПРЕТАЦИЯ ДЛЯ LEAN
# ============================================================================

print("=" * 70)
print("ШАГ 2: ИНТЕРПРЕТАЦИЯ ДЛЯ LEAN")
print("=" * 70)
print()

# Анализируем k_optimal
print("АНАЛИЗ КОЭФФИЦИЕНТА k:")
print("-" * 50)

if k_optimal > 1:
    print(f"k = {k_optimal:.4f} > 1")
    print("→ LHS > RHS в большинстве случаев")
    print("→ Неравенство имеет 'запас прочности'")
    print()
    print("СТРАТЕГИЯ ДЛЯ LEAN:")
    print("  1. Доказать более сильное неравенство")
    print("  2. Использовать nlinarith с множителями")
elif k_optimal < 1:
    print(f"k = {k_optimal:.4f} < 1")
    print("→ LHS < RHS в среднем")
    print("→ Неравенство может быть НЕВЕРНЫМ или требует условий")
else:
    print(f"k ≈ 1")
    print("→ Стороны примерно равны")
    print("→ Ищите точное равенство или SOS-разложение")

print()

# ============================================================================
# ШАГ 3: ГЕНЕРАЦИЯ LEAN-КОДА
# ============================================================================

print("=" * 70)
print("ШАГ 3: ГЕНЕРАЦИЯ LEAN-КОДА")
print("=" * 70)
print()

# Определяем, какой тип доказательства нужен
if violations == 0 and np.min(ratios) >= 0.99:
    proof_type = "EQUALITY"
    print("ТИП: Вероятно, это РАВЕНСТВО (или очень близко к нему)")
elif violations == 0:
    proof_type = "INEQUALITY"
    print("ТИП: Это НЕРАВЕНСТВО (LHS >= RHS)")
else:
    proof_type = "CONDITIONAL"
    print("ТИП: УСЛОВНОЕ неравенство (требуются дополнительные гипотезы)")

print()
print("СГЕНЕРИРОВАННЫЙ LEAN-КОД:")
print("-" * 50)

if proof_type == "EQUALITY":
    lean_code = '''
/-- Интеграл heat kernel равен 1/2 -/
lemma integral_heat_kernel_eq_half (A t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    ∫ x in Set.Ioi 0, (1 / Real.sqrt (4 * Real.pi * A * t)) * 
      Real.exp (-(x^2) / (4 * A * t)) = 1/2 := by
  -- Стратегия: Использовать известный результат о гауссовом интеграле
  -- Gaussian integral: ∫₀^∞ exp(-a*x²) dx = sqrt(π/a) / 2
  have h_gaussian : ∫ x in Set.Ioi 0, Real.exp (-(x^2) / (4 * A * t)) = 
      Real.sqrt (Real.pi * A * t) := by
    -- Применяем формулу гауссова интеграла
    rw [MeasureTheory.integral_gaussian_Ioi]
    ring
  -- Подставляем и упрощаем
  rw [MeasureTheory.integral_mul_left]
  rw [h_gaussian]
  field_simp
  ring
'''
elif proof_type == "INEQUALITY":
    lean_code = f'''
/-- Нижняя граница для интеграла P_A -/
lemma P_A_lower_bound_match (A t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    P_A A t ≥ c * A * Real.exp (-t / A) := by
  -- Численный анализ показал: k_optimal = {k_optimal:.4f}
  -- min_ratio = {np.min(ratios):.4f}
  -- Это означает, что неравенство верно с запасом
  
  -- Стратегия 1: Прямое применение nlinarith
  unfold P_A
  -- Если не работает, декомпозируем:
  
  -- Стратегия 2: Использовать промежуточную лемму
  have h_key : ∫ x in Set.Ioi 0, kernel A t x ≥ c * A * Real.exp (-t / A) := by
    -- Применяем оценку интеграла снизу
    apply MeasureTheory.integral_mono_of_nonneg
    · intro x; positivity  -- kernel ≥ 0
    · intro x; sorry  -- Поточечная оценка kernel(x) ≥ ...
  exact h_key
'''
else:
    lean_code = f'''
/-- Условная нижняя граница для P_A -/
lemma P_A_lower_bound_match (A t : ℝ) (hA : 0 < A) (ht : 0 < t) 
    (h_cond : t ≤ A) :  -- Дополнительное условие!
    P_A A t ≥ c * A * Real.exp (-t / A) := by
  -- ВНИМАНИЕ: Численный анализ показал {violations} нарушений
  -- Неравенство верно только при дополнительных условиях
  
  -- Стратегия: Использовать условие h_cond
  have h1 : Real.exp (-t / A) ≥ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    linarith [div_le_one_of_le h_cond hA.le]
  sorry
'''

print(lean_code)

# ============================================================================
# ШАГ 4: РЕКОМЕНДАЦИИ ПО ТАКТИКАМ
# ============================================================================

print()
print("=" * 70)
print("ШАГ 4: РЕКОМЕНДАЦИИ ПО ТАКТИКАМ")
print("=" * 70)
print()

print("КАСКАД ТАКТИК ДЛЯ ДАННОГО СЛУЧАЯ:")
print("-" * 50)
print("""
1. rfl           -- Не сработает (это не определение)
2. simp          -- Попробовать раскрыть P_A, kernel
3. ring          -- Не сработает (есть exp, интегралы)
4. nlinarith     -- Может сработать с подсказками
5. positivity    -- Для доказательства ≥ 0
6. exact?        -- Поиск в библиотеке
7. apply?        -- Поиск применимых лемм

СПЕЦИФИЧНЫЕ ТАКТИКИ ДЛЯ ИНТЕГРАЛОВ:
- MeasureTheory.integral_mono
- MeasureTheory.integral_nonneg
- MeasureTheory.integral_gaussian_Ioi
- intervalIntegral.integral_comp_mul_right
""")

print()
print("ПОДСКАЗКИ ИЗ ЧИСЛЕННОГО АНАЛИЗА:")
print("-" * 50)
print(f"• k_optimal = {k_optimal:.4f}")
if k_optimal > 1.1:
    print(f"  → Умножьте RHS на {k_optimal:.2f} для усиления")
elif k_optimal < 0.9:
    print(f"  → Разделите LHS на {1/k_optimal:.2f} для ослабления")

print(f"• min_ratio = {np.min(ratios):.4f}")
if np.min(ratios) > 1:
    print(f"  → Неравенство строгое, можно усилить")
elif np.min(ratios) < 1:
    print(f"  → Неравенство 'на грани', проверьте граничные случаи")

print()
print("=" * 70)
print("ИТОГ: Используйте сгенерированный Lean-код как отправную точку")
print("=" * 70)
