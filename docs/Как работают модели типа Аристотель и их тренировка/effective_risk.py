#!/usr/bin/env python3.11
"""
effective_risk.py - Вычисление Effective Risk Score для разрешения парадокса
Risk Score vs Зависимости.

Формула:
    ERS(v) = R(v) + Σ_{u ∈ D*(v)} R(u) + (is_on_critical_path ? 100 : 0)

Где:
    - R(v) — "сырой" Risk Score леммы v
    - D*(v) — множество всех лемм, транзитивно зависящих от v
    - critical_path — путь с максимальной суммой рисков
"""

from typing import List, Dict, Set, Tuple
from collections import defaultdict
from dataclasses import dataclass


@dataclass
class LemmaRisk:
    """Данные о риске леммы."""
    name: str
    raw_risk: float
    inherited_risk: float
    effective_risk_score: float
    on_critical_path: bool
    num_dependents: int
    dependents: List[str]


def topological_sort(lemma_names: Set[str], graph: Dict[str, Set[str]]) -> List[str]:
    """
    Топологическая сортировка графа зависимостей.
    Возвращает список имён лемм в порядке от "листьев" к "корням".
    """
    # Находим входящую степень для каждого узла
    in_degree = {name: 0 for name in lemma_names}
    for from_lemma, to_lemmas in graph.items():
        for to_lemma in to_lemmas:
            if to_lemma in in_degree:
                in_degree[to_lemma] += 1
    
    # Алгоритм Кана
    queue = [name for name, degree in in_degree.items() if degree == 0]
    result = []
    
    while queue:
        node = queue.pop(0)
        result.append(node)
        
        for neighbor in graph.get(node, set()):
            if neighbor in in_degree:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)
    
    return result


def get_transitive_dependents(
    lemma_name: str, 
    graph: Dict[str, Set[str]], 
    memo: Dict[str, Set[str]] = None
) -> Set[str]:
    """
    Находит все леммы, которые транзитивно зависят от данной леммы.
    Использует мемоизацию для эффективности.
    """
    if memo is None:
        memo = {}
    
    if lemma_name in memo:
        return memo[lemma_name]
    
    dependents = set()
    direct_deps = graph.get(lemma_name, set())
    
    for dep in direct_deps:
        dependents.add(dep)
        dependents.update(get_transitive_dependents(dep, graph, memo))
    
    memo[lemma_name] = dependents
    return dependents


def find_critical_path(
    lemma_names: Set[str], 
    graph: Dict[str, Set[str]], 
    risk_scores: Dict[str, float]
) -> List[str]:
    """
    Находит критический путь — путь с максимальной суммой Risk Scores.
    Использует динамическое программирование.
    """
    # dp[v] = (максимальная сумма рисков от v до конца, следующий узел на пути)
    dp: Dict[str, Tuple[float, str]] = {}
    
    # Находим "листья" (узлы без исходящих рёбер)
    leaves = [name for name in lemma_names if not graph.get(name, set())]
    
    # Инициализация для листьев
    for leaf in leaves:
        dp[leaf] = (risk_scores.get(leaf, 0), None)
    
    # Топологическая сортировка
    topo_order = topological_sort(lemma_names, graph)
    
    # Обрабатываем в обратном топологическом порядке
    for name in reversed(topo_order):
        if name in dp:
            continue
        
        max_path_risk = 0.0
        next_node = None
        
        for neighbor in graph.get(name, set()):
            if neighbor in dp:
                neighbor_risk = dp[neighbor][0]
                if neighbor_risk > max_path_risk:
                    max_path_risk = neighbor_risk
                    next_node = neighbor
        
        dp[name] = (risk_scores.get(name, 0) + max_path_risk, next_node)
    
    # Находим начало критического пути (узел с максимальным dp)
    if not dp:
        return []
    
    start_node = max(dp.keys(), key=lambda x: dp[x][0])
    
    # Восстанавливаем путь
    critical_path = []
    current = start_node
    while current is not None:
        critical_path.append(current)
        current = dp[current][1]
    
    return critical_path


def calculate_effective_risk_score(
    lemma_name: str,
    graph: Dict[str, Set[str]],
    raw_risk_scores: Dict[str, float],
    critical_path: List[str],
    memo: Dict[str, Set[str]] = None
) -> LemmaRisk:
    """
    Вычисляет Effective Risk Score (ERS) для леммы.
    
    ERS(v) = R(v) + Σ_{u ∈ D*(v)} R(u) + (is_on_critical_path ? 100 : 0)
    
    Где D*(v) — множество всех лемм, транзитивно зависящих от v.
    """
    if memo is None:
        memo = {}
    
    raw_risk = raw_risk_scores.get(lemma_name, 0)
    
    # Получаем все транзитивные зависимости
    dependents = get_transitive_dependents(lemma_name, graph, memo)
    
    # Сумма рисков всех зависимых лемм
    inherited_risk = sum(raw_risk_scores.get(dep, 0) for dep in dependents)
    
    # Бонус за критический путь
    critical_path_bonus = 100 if lemma_name in critical_path else 0
    
    # Effective Risk Score
    ers = raw_risk + inherited_risk + critical_path_bonus
    
    return LemmaRisk(
        name=lemma_name,
        raw_risk=round(raw_risk, 1),
        inherited_risk=round(inherited_risk, 1),
        effective_risk_score=round(ers, 1),
        on_critical_path=lemma_name in critical_path,
        num_dependents=len(dependents),
        dependents=list(dependents)[:5]  # Первые 5 для краткости
    )


def generate_effective_execution_plan(
    lemma_names: List[str],
    graph: Dict[str, Set[str]],
    raw_risk_scores: Dict[str, float]
) -> List[LemmaRisk]:
    """
    Генерирует Execution Plan, отсортированный по убыванию Effective Risk Score.
    
    Стратегия: "Начинаем с самого хрупкого + блокирующего + учитываем зависимости"
    """
    lemma_set = set(lemma_names)
    
    # Находим критический путь
    critical_path = find_critical_path(lemma_set, graph, raw_risk_scores)
    
    # Вычисляем Effective Risk Score для каждой леммы
    memo = {}
    effective_scores = []
    for name in lemma_names:
        ers_data = calculate_effective_risk_score(
            name, graph, raw_risk_scores, critical_path, memo
        )
        effective_scores.append(ers_data)
    
    # Сортируем по убыванию Effective Risk Score
    return sorted(effective_scores, key=lambda x: x.effective_risk_score, reverse=True)


# =============================================================================
# ПРИМЕР ИСПОЛЬЗОВАНИЯ
# =============================================================================

if __name__ == "__main__":
    # Пример: 7 sorry-лемм из формализации гипотезы Римана
    lemmas = [
        "linearity_of_Q",
        "definitional_equality",
        "P_A_lower_bound_match",
        "integral_of_P_A_lower_bound",
        "monotonicity_of_prime_term",
        "tightness_of_prime_term_bound",
        "final_algebraic_combination"
    ]
    
    # Граф зависимостей: A → B означает "B зависит от A"
    graph = {
        "linearity_of_Q": {"final_algebraic_combination"},
        "definitional_equality": {"integral_of_P_A_lower_bound"},
        "P_A_lower_bound_match": {"integral_of_P_A_lower_bound"},
        "integral_of_P_A_lower_bound": {"final_algebraic_combination"},
        "monotonicity_of_prime_term": {"tightness_of_prime_term_bound"},
        "tightness_of_prime_term_bound": {"final_algebraic_combination"},
        "final_algebraic_combination": set()
    }
    
    # "Сырые" Risk Scores (из предыдущего анализа)
    raw_risk_scores = {
        "linearity_of_Q": 35.0,
        "definitional_equality": 25.0,
        "P_A_lower_bound_match": 45.3,
        "integral_of_P_A_lower_bound": 55.0,
        "monotonicity_of_prime_term": 40.0,
        "tightness_of_prime_term_bound": 38.0,
        "final_algebraic_combination": 60.0
    }
    
    # Генерируем план
    plan = generate_effective_execution_plan(lemmas, graph, raw_risk_scores)
    
    print("=" * 80)
    print("EXECUTION PLAN (отсортирован по Effective Risk Score)")
    print("=" * 80)
    print()
    print(f"{'#':<3} {'Лемма':<35} {'Raw':<8} {'Inherited':<10} {'ERS':<8} {'Critical'}")
    print("-" * 80)
    
    for i, item in enumerate(plan, 1):
        crit = "🔥 YES" if item.on_critical_path else "no"
        print(f"{i:<3} {item.name:<35} {item.raw_risk:<8} {item.inherited_risk:<10} {item.effective_risk_score:<8} {crit}")
    
    print()
    print("=" * 80)
    print("КРИТИЧЕСКИЙ ПУТЬ:")
    critical_path = find_critical_path(set(lemmas), graph, raw_risk_scores)
    print(" → ".join(critical_path))
