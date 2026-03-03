"""
Norm Balancer: Алгоритм балансировки неравенств через нормализацию

Идея: Приводим обе стороны неравенства к единой норме и находим
коэффициенты балансировки, независимо от их рациональности.

Это как в химии — уравновешиваем реакцию, находя коэффициенты,
при которых атомы слева = атомы справа.
"""

import sympy as sp
from sympy import symbols, expand, Poly, sqrt, Rational
from scipy.optimize import minimize, linprog
import numpy as np
from typing import Tuple, List, Dict, Optional

# ============================================================================
# ЧАСТЬ 1: НОРМАЛИЗАЦИЯ
# ============================================================================

def extract_terms(expr, variables: List[sp.Symbol]) -> Dict[tuple, sp.Expr]:
    """
    Извлекает члены полинома и их коэффициенты.
    Возвращает словарь: {(степени переменных): коэффициент}
    """
    poly = Poly(expand(expr), *variables)
    terms = {}
    for monom, coeff in poly.as_dict().items():
        terms[monom] = coeff
    return terms


def l2_norm(terms: Dict[tuple, sp.Expr]) -> float:
    """
    Вычисляет L2-норму коэффициентов: sqrt(sum(c_i^2))
    """
    total = sum(float(c.evalf())**2 for c in terms.values())
    return np.sqrt(total)


def l1_norm(terms: Dict[tuple, sp.Expr]) -> float:
    """
    Вычисляет L1-норму коэффициентов: sum(|c_i|)
    """
    return sum(abs(float(c.evalf())) for c in terms.values())


def normalize_expression(expr, variables: List[sp.Symbol], norm_type: str = 'l2') -> Tuple[sp.Expr, float]:
    """
    Нормализует выражение, деля на его норму.
    Возвращает (нормализованное выражение, норма).
    """
    terms = extract_terms(expr, variables)
    
    if norm_type == 'l2':
        norm = l2_norm(terms)
    elif norm_type == 'l1':
        norm = l1_norm(terms)
    else:
        raise ValueError(f"Unknown norm type: {norm_type}")
    
    if norm == 0:
        return expr, 1.0
    
    normalized = expr / norm
    return normalized, norm


# ============================================================================
# ЧАСТЬ 2: БАЛАНСИРОВКА
# ============================================================================

def find_balance_coefficients(lhs_expr, rhs_expr, variables: List[sp.Symbol], 
                               n_samples: int = 10000) -> Dict[str, float]:
    """
    Находит коэффициенты λ₁, λ₂ такие, что λ₁ * LHS ≈ λ₂ * RHS
    в смысле минимизации разницы по множеству точек.
    
    Возвращает словарь с информацией о балансе.
    """
    # Создаём вычисляемые функции
    lhs_func = sp.lambdify(variables, lhs_expr, 'numpy')
    rhs_func = sp.lambdify(variables, rhs_expr, 'numpy')
    
    # Генерируем тестовые точки (положительные значения)
    test_points = np.random.rand(n_samples, len(variables)) * 10  # [0, 10]
    
    # Вычисляем значения на тестовых точках
    lhs_vals = np.array([lhs_func(*p) for p in test_points])
    rhs_vals = np.array([rhs_func(*p) for p in test_points])
    
    # Фильтруем точки, где оба значения определены и конечны
    valid_mask = np.isfinite(lhs_vals) & np.isfinite(rhs_vals)
    lhs_vals = lhs_vals[valid_mask]
    rhs_vals = rhs_vals[valid_mask]
    
    if len(lhs_vals) == 0:
        return {"error": "No valid points found"}
    
    # Метод 1: Находим отношение норм
    lhs_norm = np.sqrt(np.mean(lhs_vals**2))
    rhs_norm = np.sqrt(np.mean(rhs_vals**2))
    
    # Метод 2: Линейная регрессия LHS = k * RHS
    # Минимизируем ||LHS - k * RHS||²
    if np.sum(rhs_vals**2) > 1e-10:
        k_optimal = np.sum(lhs_vals * rhs_vals) / np.sum(rhs_vals**2)
    else:
        k_optimal = 1.0
    
    # Метод 3: Находим минимальный и максимальный разрыв
    with np.errstate(divide='ignore', invalid='ignore'):
        ratios = np.where(np.abs(rhs_vals) > 1e-10, lhs_vals / rhs_vals, np.nan)
    ratios = ratios[np.isfinite(ratios)]
    
    if len(ratios) > 0:
        min_ratio = np.min(ratios)
        max_ratio = np.max(ratios)
        median_ratio = np.median(ratios)
    else:
        min_ratio = max_ratio = median_ratio = np.nan
    
    # Анализ: проверяем, выполняется ли неравенство LHS >= RHS
    diff_vals = lhs_vals - rhs_vals
    min_diff = np.min(diff_vals)
    violations = np.sum(diff_vals < -1e-10)
    
    return {
        "lhs_l2_norm": lhs_norm,
        "rhs_l2_norm": rhs_norm,
        "norm_ratio": lhs_norm / rhs_norm if rhs_norm > 1e-10 else np.inf,
        "optimal_k": k_optimal,  # LHS ≈ k * RHS
        "min_ratio": min_ratio,  # min(LHS/RHS)
        "max_ratio": max_ratio,  # max(LHS/RHS)
        "median_ratio": median_ratio,
        "min_difference": min_diff,  # min(LHS - RHS)
        "violations": violations,  # сколько раз LHS < RHS
        "total_samples": len(lhs_vals),
        "inequality_likely_true": min_diff >= -1e-9
    }


def find_sos_decomposition_hint(expr, variables: List[sp.Symbol]) -> Optional[str]:
    """
    Пытается найти подсказку для SOS-разложения.
    Проверяет, можно ли представить выражение как сумму квадратов.
    """
    # Простая эвристика: проверяем, является ли выражение суммой квадратов
    expanded = expand(expr)
    
    # Пробуем разные комбинации квадратов разностей
    n = len(variables)
    hints = []
    
    # Проверяем квадраты разностей пар переменных
    for i in range(n):
        for j in range(i+1, n):
            diff_sq = (variables[i] - variables[j])**2
            # Проверяем, делится ли выражение на этот квадрат
            remainder = sp.simplify(expanded - diff_sq)
            if remainder == 0:
                hints.append(f"({variables[i]} - {variables[j]})²")
    
    # Проверяем квадраты отдельных переменных
    for var in variables:
        var_sq = var**2
        if sp.simplify(expanded - var_sq) == 0:
            hints.append(f"{var}²")
    
    if hints:
        return " + ".join(hints)
    
    return None


# ============================================================================
# ЧАСТЬ 3: ГЛАВНАЯ ФУНКЦИЯ АНАЛИЗА
# ============================================================================

def analyze_inequality(lhs_str: str, rhs_str: str, var_names: str = "a b c") -> Dict:
    """
    Полный анализ неравенства LHS >= RHS.
    
    Пример:
        analyze_inequality("a**2 + b**2 + c**2", "a*b + b*c + c*a")
    """
    # Создаём символы
    var_list = var_names.split()
    variables = [sp.Symbol(v, real=True) for v in var_list]
    
    # Создаём словарь для sympify, чтобы использовать наши символы
    local_dict = {v.name: v for v in variables}
    
    # Парсим выражения
    lhs_expr = sp.sympify(lhs_str, locals=local_dict)
    rhs_expr = sp.sympify(rhs_str, locals=local_dict)
    
    # Разность: f = LHS - RHS (должна быть >= 0)
    diff_expr = lhs_expr - rhs_expr
    
    print("=" * 60)
    print("АНАЛИЗ НЕРАВЕНСТВА")
    print("=" * 60)
    print(f"LHS: {lhs_expr}")
    print(f"RHS: {rhs_expr}")
    print(f"Разность (LHS - RHS): {expand(diff_expr)}")
    print()
    
    # Шаг 1: Нормализация
    print("-" * 40)
    print("ШАГ 1: НОРМАЛИЗАЦИЯ")
    print("-" * 40)
    
    lhs_normalized, lhs_norm = normalize_expression(lhs_expr, variables, 'l2')
    rhs_normalized, rhs_norm = normalize_expression(rhs_expr, variables, 'l2')
    
    print(f"L2-норма LHS: {lhs_norm:.6f}")
    print(f"L2-норма RHS: {rhs_norm:.6f}")
    print(f"Отношение норм: {lhs_norm/rhs_norm:.6f}")
    print()
    
    # Шаг 2: Балансировка
    print("-" * 40)
    print("ШАГ 2: БАЛАНСИРОВКА")
    print("-" * 40)
    
    balance = find_balance_coefficients(lhs_expr, rhs_expr, variables)
    
    print(f"Оптимальный коэффициент k (LHS ≈ k * RHS): {balance['optimal_k']:.6f}")
    print(f"Минимальное отношение LHS/RHS: {balance['min_ratio']:.6f}")
    print(f"Максимальное отношение LHS/RHS: {balance['max_ratio']:.6f}")
    print(f"Медианное отношение: {balance['median_ratio']:.6f}")
    print(f"Минимальная разность (LHS - RHS): {balance['min_difference']:.6f}")
    print(f"Нарушений неравенства: {balance['violations']} из {balance['total_samples']}")
    print()
    
    # Шаг 3: Вывод
    print("-" * 40)
    print("ШАГ 3: ЗАКЛЮЧЕНИЕ")
    print("-" * 40)
    
    if balance['inequality_likely_true']:
        print("✓ Неравенство LHS >= RHS, вероятно, ВЕРНО")
        print()
        
        # Анализ коэффициента
        k = balance['optimal_k']
        if abs(k - 1.0) < 0.01:
            print("  → Стороны примерно равны (k ≈ 1)")
            print("  → Ищите разложение на сумму квадратов")
        elif k > 1:
            print(f"  → LHS в среднем в {k:.2f} раз больше RHS")
            print("  → Неравенство имеет 'запас прочности'")
        else:
            print(f"  → LHS в среднем в {1/k:.2f} раз меньше RHS")
            print("  → Неравенство 'на грани', проверьте внимательно")
        
        # Подсказка для SOS
        sos_hint = find_sos_decomposition_hint(diff_expr, variables)
        if sos_hint:
            print(f"\n  → Подсказка SOS: {diff_expr} = {sos_hint}")
        else:
            print(f"\n  → Попробуйте разложить {expand(diff_expr)} на сумму квадратов")
            
    else:
        print("✗ Неравенство LHS >= RHS, вероятно, НЕВЕРНО")
        print(f"  → Найдены контрпримеры ({balance['violations']} штук)")
        print(f"  → Минимальная разность: {balance['min_difference']:.6f}")
    
    print()
    
    # Возвращаем все данные
    return {
        "lhs": str(lhs_expr),
        "rhs": str(rhs_expr),
        "diff": str(expand(diff_expr)),
        "lhs_norm": lhs_norm,
        "rhs_norm": rhs_norm,
        "balance": balance,
        "likely_true": balance['inequality_likely_true']
    }


# ============================================================================
# ПРИМЕР ИСПОЛЬЗОВАНИЯ
# ============================================================================

if __name__ == "__main__":
    # Пример 1: Классическое неравенство
    print("\n" + "=" * 70)
    print("ПРИМЕР 1: a² + b² + c² >= ab + bc + ca")
    print("=" * 70)
    analyze_inequality("a**2 + b**2 + c**2", "a*b + b*c + c*a")
    
    # Пример 2: AM-GM для двух переменных
    print("\n" + "=" * 70)
    print("ПРИМЕР 2: a² + b² >= 2*a*b (AM-GM)")
    print("=" * 70)
    analyze_inequality("a**2 + b**2", "2*a*b", "a b")
    
    # Пример 3: Неверное неравенство
    print("\n" + "=" * 70)
    print("ПРИМЕР 3: a + b >= a² + b² (НЕВЕРНО для больших значений)")
    print("=" * 70)
    analyze_inequality("a + b", "a**2 + b**2", "a b")
