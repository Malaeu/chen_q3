#!/usr/bin/env python3.11
"""
sorry_system_analyzer.py - Анализатор системы sorry-лемм в Lean 4 проектах

Этот модуль рассматривает совокупность sorry-лемм как систему уравнений,
анализирует входы/выходы каждой леммы, строит граф зависимостей и
ищет связи между леммами для системного решения.

Использование:
    python3.11 sorry_system_analyzer.py /path/to/lean/project

Вывод:
    - sorry_graph.json: Граф зависимостей в формате JSON
    - sorry_system_report.md: Текстовый отчёт с анализом системы
"""

import re
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Set, Tuple, Optional
from pathlib import Path
from collections import defaultdict


@dataclass
class Variable:
    """Переменная в контексте леммы."""
    name: str
    type_str: str
    
    def __hash__(self):
        return hash((self.name, self.type_str))
    
    def __eq__(self, other):
        return self.name == other.name and self.type_str == other.type_str


@dataclass
class SorryLemma:
    """Представление sorry-леммы как узла в системе."""
    name: str
    file_path: str
    line_number: int
    
    # Входы и выходы
    inputs: List[Variable] = field(default_factory=list)  # Переменные и гипотезы
    output: str = ""  # Целевое утверждение (statement)
    
    # Семантический анализ
    relation_type: str = ""  # "equality", "inequality", "existence", "other"
    lhs: str = ""  # Левая часть (для equality/inequality)
    rhs: str = ""  # Правая часть (для equality/inequality)
    
    # Переменные, участвующие в стейтменте
    variables_in_statement: Set[str] = field(default_factory=set)


@dataclass
class DependencyEdge:
    """Ребро в графе зависимостей."""
    from_lemma: str
    to_lemma: str
    shared_variables: List[str]  # Общие переменные
    connection_type: str  # "type_match", "variable_flow", "hypothesis_use"


@dataclass
class SorrySystem:
    """Система sorry-лемм."""
    lemmas: List[SorryLemma] = field(default_factory=list)
    edges: List[DependencyEdge] = field(default_factory=list)
    
    # Анализ
    sequential_chains: List[List[str]] = field(default_factory=list)
    parallel_groups: List[List[str]] = field(default_factory=list)
    isolated_lemmas: List[str] = field(default_factory=list)


# =============================================================================
# ПАРСИНГ LEAN ФАЙЛОВ
# =============================================================================

# Паттерн для извлечения sorry-лемм
# Улучшенный паттерн:
# - Корректно обрабатывает множественные аргументы
# - Использует .+? (ленивый матч) для statement, чтобы захватить = в равенствах
LEMMA_PATTERN = re.compile(
    r"(?:lemma|theorem)\s+(?P<name>\w+)\s*"
    r"(?P<all_args>(?:\{[^}]*\}|\([^)]*\)|\[[^\]]*\])\s*)*"
    r":\s*(?P<statement>.+?)"
    r"\s*:=\s*(?:by\s+)?sorry",
    re.DOTALL
)

# Паттерн для извлечения аргументов
ARG_PATTERN = re.compile(r"\((?P<vars>[\w\s]+)\s*:\s*(?P<type>[^)]+)\)")

# Паттерны для определения типа отношения
# Важно: сначала проверяем неравенства, потом равенства
INEQUALITY_LE_PATTERN = re.compile(r"(.+?)\s*≤\s*(.+)")
INEQUALITY_GE_PATTERN = re.compile(r"(.+?)\s*≥\s*(.+)")
INEQUALITY_LT_PATTERN = re.compile(r"(.+?)\s*<\s*(.+)")
INEQUALITY_GT_PATTERN = re.compile(r"(.+?)\s*>\s*(.+)")
EQUALITY_PATTERN = re.compile(r"(.+?)\s*=\s*(.+)")


def extract_variables_from_type(type_str: str) -> Set[str]:
    """Извлекает имена переменных из типа."""
    # Простой подход: берём все идентификаторы
    return set(re.findall(r'\b([a-z_]\w*)\b', type_str))


def parse_lemma_args(args_str: str) -> List[Variable]:
    """Парсит аргументы леммы."""
    variables = []
    for match in ARG_PATTERN.finditer(args_str):
        var_names = match.group("vars").split()
        var_type = match.group("type").strip()
        for name in var_names:
            name = name.strip()
            if name:
                variables.append(Variable(name=name, type_str=var_type))
    return variables


def classify_statement(statement: str) -> Tuple[str, str, str]:
    """
    Классифицирует стейтмент леммы.
    
    Returns:
        (relation_type, lhs, rhs)
    """
    statement = statement.strip()
    
    # Сначала проверяем на неравенства (они более специфичны)
    for pattern, rel_type in [
        (INEQUALITY_LE_PATTERN, "inequality_le"),
        (INEQUALITY_GE_PATTERN, "inequality_ge"),
        (INEQUALITY_LT_PATTERN, "inequality_lt"),
        (INEQUALITY_GT_PATTERN, "inequality_gt"),
    ]:
        match = pattern.match(statement)
        if match:
            return (rel_type, match.group(1).strip(), match.group(2).strip())
    
    # Проверяем на равенство
    eq_match = EQUALITY_PATTERN.match(statement)
    if eq_match:
        return ("equality", eq_match.group(1).strip(), eq_match.group(2).strip())
    
    # Проверяем на существование
    if statement.startswith("∃") or "Exists" in statement:
        return ("existence", statement, "")
    
    return ("other", statement, "")


def parse_lean_file(file_path: Path) -> List[SorryLemma]:
    """Парсит Lean файл и извлекает sorry-леммы."""
    lemmas = []
    
    try:
        content = file_path.read_text(encoding='utf-8')
    except Exception as e:
        print(f"Ошибка чтения {file_path}: {e}", file=sys.stderr)
        return lemmas
    
    # Находим номера строк для каждой позиции
    line_starts = [0]
    for i, char in enumerate(content):
        if char == '\n':
            line_starts.append(i + 1)
    
    def pos_to_line(pos: int) -> int:
        for i, start in enumerate(line_starts):
            if start > pos:
                return i
        return len(line_starts)
    
    for match in LEMMA_PATTERN.finditer(content):
        name = match.group("name")
        # Извлекаем все аргументы из полного совпадения
        full_match = match.group(0)
        # Ищем все аргументы между именем и :
        args_start = full_match.find(name) + len(name)
        args_end = full_match.rfind(':')
        args_str = full_match[args_start:args_end] if args_end > args_start else ""
        statement = match.group("statement").strip()
        line_number = pos_to_line(match.start())
        
        # Парсим аргументы
        inputs = parse_lemma_args(args_str)
        
        # Классифицируем стейтмент
        relation_type, lhs, rhs = classify_statement(statement)
        
        # Извлекаем переменные из стейтмента
        vars_in_stmt = extract_variables_from_type(statement)
        
        lemma = SorryLemma(
            name=name,
            file_path=str(file_path),
            line_number=line_number,
            inputs=inputs,
            output=statement,
            relation_type=relation_type,
            lhs=lhs,
            rhs=rhs,
            variables_in_statement=vars_in_stmt
        )
        lemmas.append(lemma)
    
    return lemmas


def scan_project(project_path: Path) -> List[SorryLemma]:
    """Сканирует весь проект и извлекает sorry-леммы."""
    all_lemmas = []
    
    for lean_file in project_path.rglob("*.lean"):
        lemmas = parse_lean_file(lean_file)
        all_lemmas.extend(lemmas)
    
    return all_lemmas


# =============================================================================
# ПОСТРОЕНИЕ ГРАФА ЗАВИСИМОСТЕЙ
# =============================================================================

def find_dependencies(lemmas: List[SorryLemma]) -> List[DependencyEdge]:
    """Находит зависимости между леммами."""
    edges = []
    
    for i, lemma1 in enumerate(lemmas):
        for j, lemma2 in enumerate(lemmas):
            if i == j:
                continue
            
            # Проверяем, есть ли общие переменные
            vars1 = lemma1.variables_in_statement
            vars2 = lemma2.variables_in_statement
            shared = vars1 & vars2
            
            if shared:
                # Определяем тип связи
                connection_type = "variable_flow"
                
                # Если выход одной леммы может быть входом другой
                if lemma1.output and lemma1.output in str(lemma2.inputs):
                    connection_type = "hypothesis_use"
                
                # Если типы совпадают
                input_types2 = {v.type_str for v in lemma2.inputs}
                if lemma1.relation_type == "equality" and lemma1.output in input_types2:
                    connection_type = "type_match"
                
                edge = DependencyEdge(
                    from_lemma=lemma1.name,
                    to_lemma=lemma2.name,
                    shared_variables=list(shared),
                    connection_type=connection_type
                )
                edges.append(edge)
    
    return edges


def find_chains_and_groups(lemmas: List[SorryLemma], edges: List[DependencyEdge]) -> Tuple[List[List[str]], List[List[str]], List[str]]:
    """
    Анализирует граф и находит:
    - Последовательные цепочки
    - Параллельные группы
    - Изолированные леммы
    """
    # Строим граф
    graph = defaultdict(set)
    reverse_graph = defaultdict(set)
    all_lemma_names = {l.name for l in lemmas}
    
    for edge in edges:
        graph[edge.from_lemma].add(edge.to_lemma)
        reverse_graph[edge.to_lemma].add(edge.from_lemma)
    
    # Находим изолированные леммы
    connected = set()
    for edge in edges:
        connected.add(edge.from_lemma)
        connected.add(edge.to_lemma)
    isolated = list(all_lemma_names - connected)
    
    # Находим цепочки (простой DFS)
    chains = []
    visited = set()
    
    def dfs_chain(node: str, current_chain: List[str]):
        if node in visited:
            return
        visited.add(node)
        current_chain.append(node)
        
        for next_node in graph[node]:
            if next_node not in visited:
                dfs_chain(next_node, current_chain)
    
    # Начинаем с узлов без входящих рёбер
    start_nodes = all_lemma_names - set(reverse_graph.keys())
    for start in start_nodes:
        if start not in visited and start in graph:
            chain = []
            dfs_chain(start, chain)
            if len(chain) > 1:
                chains.append(chain)
    
    # Находим параллельные группы (леммы с одинаковыми входами)
    input_groups = defaultdict(list)
    for lemma in lemmas:
        input_key = tuple(sorted((v.name, v.type_str) for v in lemma.inputs))
        input_groups[input_key].append(lemma.name)
    
    parallel_groups = [group for group in input_groups.values() if len(group) > 1]
    
    return chains, parallel_groups, isolated


# =============================================================================
# АНАЛИЗ СИСТЕМЫ УРАВНЕНИЙ
# =============================================================================

def analyze_equation_system(lemmas: List[SorryLemma]) -> Dict:
    """Анализирует систему уравнений, образованную sorry-леммами."""
    analysis = {
        "total_lemmas": len(lemmas),
        "equalities": [],
        "inequalities": [],
        "existence_claims": [],
        "other": [],
        "variable_usage": defaultdict(list),
        "potential_substitutions": []
    }
    
    for lemma in lemmas:
        entry = {
            "name": lemma.name,
            "lhs": lemma.lhs,
            "rhs": lemma.rhs,
            "statement": lemma.output
        }
        
        if lemma.relation_type == "equality":
            analysis["equalities"].append(entry)
        elif lemma.relation_type.startswith("inequality"):
            analysis["inequalities"].append(entry)
        elif lemma.relation_type == "existence":
            analysis["existence_claims"].append(entry)
        else:
            analysis["other"].append(entry)
        
        # Отслеживаем использование переменных
        for var in lemma.variables_in_statement:
            analysis["variable_usage"][var].append(lemma.name)
    
    # Ищем потенциальные подстановки
    # Если у нас есть `a = b` и `b = c`, можно подставить
    for eq1 in analysis["equalities"]:
        for eq2 in analysis["equalities"]:
            if eq1["name"] != eq2["name"]:
                if eq1["rhs"] == eq2["lhs"]:
                    analysis["potential_substitutions"].append({
                        "from": eq1["name"],
                        "to": eq2["name"],
                        "chain": f"{eq1['lhs']} = {eq1['rhs']} = {eq2['rhs']}"
                    })
    
    return analysis


# =============================================================================
# ГЕНЕРАЦИЯ ОТЧЁТА
# =============================================================================

def calculate_complexity_score(statement):
    """Вычисляет оценку сложности утверждения."""
    score = 0
    # Тип утверждения
    if '=' in statement:
        score += 1
    elif '≤' in statement or '≥' in statement or '<' in statement or '>' in statement:
        score += 5

    # Количество переменных и операций
    variables = set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', statement))
    operations = len(re.findall(r'[+\-*/^√]', statement))
    score += len(variables)
    score += operations
    return score

def calculate_fundamentality_bonus(name):
    """Вычисляет бонус за фундаментальность леммы."""
    bonus_keywords = ['comm', 'assoc', 'nonneg', 'refl', 'symm', 'trans']
    if any(keyword in name for keyword in bonus_keywords):
        return -10
    return 0


# =============================================================================
# X-CRITICAL: АНАЛИЗ ХРУПКОСТИ И КРИТИЧЕСКОГО ПУТИ
# =============================================================================

def classify_blocker_type(lemma_name: str, graph, total_lemmas: int) -> Tuple[str, float]:
    """
    Классифицирует лемму по типу блокера.
    
    Returns:
        (blocker_type, blocker_score)
    """
    if lemma_name not in graph:
        return ("INDEPENDENT", 0.0)
    
    out_degree = graph.out_degree(lemma_name) if hasattr(graph, 'out_degree') else len(graph.get(lemma_name, []))
    
    # HARD BLOCKER: если от леммы зависит > 20% других лемм
    if total_lemmas > 0 and out_degree / total_lemmas > 0.2:
        return ("HARD_BLOCKER", 1.0)
    
    # SOFT BLOCKER: есть зависимости, но не критичные
    if out_degree > 0:
        return ("SOFT_BLOCKER", 0.4)
    
    return ("INDEPENDENT", 0.0)


def calculate_uncertainty(lemma: SorryLemma) -> float:
    """
    Оценивает неопределённость леммы (0-1).
    
    Критерии:
    - Нестандартные типы → +0.5
    - Аксиомы в зависимостях → +0.3
    - Отсутствие известных паттернов → +0.2
    """
    uncertainty = 0.0
    
    # Проверяем на нестандартные типы (не из mathlib)
    standard_types = ['Nat', 'Int', 'Real', 'Complex', 'Bool', 'Prop', 'Type', 'ℝ', 'ℕ', 'ℤ', 'ℂ']
    for var in lemma.inputs:
        if not any(std in var.type_str for std in standard_types):
            uncertainty += 0.5
            break
    
    # Проверяем на аксиомы
    if 'axiom' in lemma.name.lower() or 'Axiom' in lemma.output:
        uncertainty += 0.3
    
    # Проверяем на известные паттерны
    known_patterns = ['comm', 'assoc', 'nonneg', 'refl', 'symm', 'trans', 'add', 'mul', 'sub', 'div']
    if not any(pattern in lemma.name.lower() for pattern in known_patterns):
        uncertainty += 0.2
    
    return min(uncertainty, 1.0)


def calculate_risk_score(lemma: SorryLemma, graph, total_lemmas: int, max_complexity: float) -> Dict:
    """
    Вычисляет Risk Score (0-100) по формуле x-critical.
    
    risk = (complexity * 30) + (uncertainty * 30) + (blocker_type * 25) + (centrality * 15)
    """
    # 1. Complexity (0-1)
    raw_complexity = calculate_complexity_score(lemma.output)
    complexity = raw_complexity / max_complexity if max_complexity > 0 else 0
    
    # 2. Uncertainty (0-1)
    uncertainty = calculate_uncertainty(lemma)
    
    # 3. Blocker Type
    blocker_type, blocker_score = classify_blocker_type(lemma.name, graph, total_lemmas)
    
    # 4. Centrality (0-1)
    out_degree = 0
    if lemma.name in graph:
        out_degree = len(graph.get(lemma.name, [])) if isinstance(graph, dict) else graph.out_degree(lemma.name)
    centrality = out_degree / total_lemmas if total_lemmas > 0 else 0
    
    # Финальный Risk Score
    risk = (complexity * 30) + (uncertainty * 30) + (blocker_score * 25) + (centrality * 15)
    
    return {
        'name': lemma.name,
        'risk_score': round(risk, 1),
        'blocker_type': blocker_type,
        'complexity': round(complexity, 2),
        'uncertainty': round(uncertainty, 2),
        'centrality': round(centrality, 2),
        'statement': lemma.output[:60]
    }


def generate_execution_plan(lemmas: List[SorryLemma], graph, total_lemmas: int) -> List[Dict]:
    """
    Генерирует Execution Plan — список лемм, отсортированный по убыванию Risk Score.
    
    Стратегия: "Начинаем с самого хрупкого + блокирующего"
    """
    # Находим максимальную сложность для нормализации
    max_complexity = max(calculate_complexity_score(l.output) for l in lemmas) if lemmas else 1
    
    # Вычисляем Risk Score для каждой леммы
    risk_scores = [calculate_risk_score(l, graph, total_lemmas, max_complexity) for l in lemmas]
    
    # Сортируем по убыванию Risk Score
    return sorted(risk_scores, key=lambda x: x['risk_score'], reverse=True)

def prioritize_lemmas(lemmas: List[SorryLemma], graph) -> List[Dict]:
    """Приоритизирует леммы на основе взвешенной оценки."""
    scored_lemmas = []
    for lemma in lemmas:
        name = lemma.name
        statement = lemma.output
        
        # Оценка Зависимостей
        degree = len(graph.get(name, [])) if name in graph else 0
        dependency_score = degree * 10
        
        # Оценка Сложности
        complexity_score = calculate_complexity_score(statement)
        
        # Бонус за Фундаментальность
        fundamentality_bonus = calculate_fundamentality_bonus(name)
        
        total_score = dependency_score + complexity_score - fundamentality_bonus
        scored_lemmas.append({'name': name, 'score': total_score, 'statement': statement})
        
    return sorted(scored_lemmas, key=lambda x: x['score'])

def generate_report(system: SorrySystem, analysis: Dict, graph) -> str:
    """Генерирует текстовый отчёт о системе."""
    lines = [
        "# Отчёт: Система `sorry`-лемм как система уравнений",
        "",
        "---",
        "",
        "## 1. Обзор системы",
        "",
        f"**Всего лемм:** {analysis['total_lemmas']}",
        f"- Равенства: {len(analysis['equalities'])}",
        f"- Неравенства: {len(analysis['inequalities'])}",
        f"- Утверждения о существовании: {len(analysis['existence_claims'])}",
        f"- Прочее: {len(analysis['other'])}",
        "",
        "---",
        "",
        "## 2. Граф зависимостей",
        "",
    ]
    
    if system.sequential_chains:
        lines.append("### Последовательные цепочки (доказывать по порядку):")
        for i, chain in enumerate(system.sequential_chains, 1):
            lines.append(f"{i}. `{' → '.join(chain)}`")
        lines.append("")
    
    if system.parallel_groups:
        lines.append("### Параллельные группы (можно доказывать одновременно):")
        for i, group in enumerate(system.parallel_groups, 1):
            lines.append(f"{i}. `{', '.join(group)}`")
        lines.append("")
    
    if system.isolated_lemmas:
        lines.append("### Изолированные леммы (независимые):")
        lines.append(f"`{', '.join(system.isolated_lemmas)}`")
        lines.append("")

    # Добавляем раздел с приоритетами (старый метод)
    prioritized_list = prioritize_lemmas(system.lemmas, graph)
    lines.extend([
        "---",
        "",
        "## 3. Приоритетный список (простой метод)",
        "",
        "| Лемма | Оценка (меньше = лучше) | Утверждение |",
        "|---|---|---|"
    ])
    for item in prioritized_list:
        lines.append(f"| `{item['name']}` | {item['score']} | `{item['statement'][:60]}` |")
    lines.append("")
    
    # X-CRITICAL: Execution Plan с Risk Score
    execution_plan = generate_execution_plan(system.lemmas, graph, analysis['total_lemmas'])
    lines.extend([
        "---",
        "",
        "## 🚨 EXECUTION PLAN (x-critical)",
        "",
        "> **Стратегия:** Начинаем с самого хрупкого + блокирующего — если что-то сломается, узнаем сразу!",
        "",
        "### Формула риска:",
        "```",
        "risk = (complexity * 30) + (uncertainty * 30) + (blocker_type * 25) + (centrality * 15)",
        "```",
        "",
        "### Типы блокеров:",
        "| Тип | Значение |",
        "|---|---|",
        "| HARD_BLOCKER | Если упадёт — вся ветка мёртва |",
        "| SOFT_BLOCKER | Есть workaround |",
        "| INDEPENDENT | Можно параллелить |",
        "",
        "### План выполнения (отсортирован по убыванию Risk Score):",
        "",
        "| # | Лемма | Risk | Тип | Complexity | Uncertainty | Утверждение |",
        "|---|---|---|---|---|---|---|"
    ])
    for i, item in enumerate(execution_plan, 1):
        risk_emoji = "🔴" if item['risk_score'] > 50 else ("🟡" if item['risk_score'] > 25 else "🟢")
        lines.append(f"| {i} | `{item['name']}` | {risk_emoji} {item['risk_score']} | {item['blocker_type']} | {item['complexity']} | {item['uncertainty']} | `{item['statement']}` |")
    lines.append("")
    
    lines.extend([
        "---",
        "",
        "## 3. Система уравнений",
        "",
    ])
    
    if analysis["equalities"]:
        lines.append("### Равенства:")
        lines.append("| Лемма | LHS | RHS |")
        lines.append("|-------|-----|-----|")
        for eq in analysis["equalities"]:
            lines.append(f"| `{eq['name']}` | `{eq['lhs'][:30]}` | `{eq['rhs'][:30]}` |")
        lines.append("")
    
    if analysis["inequalities"]:
        lines.append("### Неравенства:")
        lines.append("| Лемма | LHS | RHS |")
        lines.append("|-------|-----|-----|")
        for ineq in analysis["inequalities"]:
            lines.append(f"| `{ineq['name']}` | `{ineq['lhs'][:30]}` | `{ineq['rhs'][:30]}` |")
        lines.append("")
    
    if analysis["potential_substitutions"]:
        lines.extend([
            "---",
            "",
            "## 4. Потенциальные подстановки",
            "",
            "Найдены цепочки равенств, которые можно объединить:",
            "",
        ])
        for sub in analysis["potential_substitutions"]:
            lines.append(f"- `{sub['from']}` → `{sub['to']}`: `{sub['chain']}`")
        lines.append("")
    
    lines.extend([
        "---",
        "",
        "## 5. Использование переменных",
        "",
        "Переменные, встречающиеся в нескольких леммах (потенциальные точки связи):",
        "",
    ])
    
    multi_use_vars = {var: lemmas for var, lemmas in analysis["variable_usage"].items() if len(lemmas) > 1}
    if multi_use_vars:
        for var, lemma_names in sorted(multi_use_vars.items(), key=lambda x: -len(x[1])):
            lines.append(f"- `{var}`: используется в {len(lemma_names)} леммах: `{', '.join(lemma_names)}`")
    else:
        lines.append("*Нет переменных, используемых в нескольких леммах.*")
    
    lines.extend([
        "",
        "---",
        "",
        "## 6. Рекомендации",
        "",
    ])
    
    if system.sequential_chains:
        lines.append("1. **Начните с начала цепочек:** Доказывайте леммы в порядке цепочек, так как каждая следующая может зависеть от предыдущей.")
    
    if system.parallel_groups:
        lines.append("2. **Параллельная работа:** Леммы в параллельных группах можно доказывать независимо друг от друга.")
    
    if analysis["potential_substitutions"]:
        lines.append("3. **Используйте подстановки:** Найденные цепочки равенств могут упростить доказательства через транзитивность.")
    
    if analysis["inequalities"]:
        lines.append("4. **Метод балансировки:** Для неравенств используйте `norm_balancer.py` для поиска коэффициентов.")
    
    return "\n".join(lines)


# =============================================================================
# CLI ИНТЕРФЕЙС
# =============================================================================

def main():
    """Точка входа для CLI."""
    if len(sys.argv) < 2:
        print("Использование: python3.11 sorry_system_analyzer.py /path/to/lean/project", file=sys.stderr)
        sys.exit(1)
    
    project_path = Path(sys.argv[1])
    
    if not project_path.exists():
        print(f"Ошибка: путь '{project_path}' не существует.", file=sys.stderr)
        sys.exit(1)
    
    print(f"Сканирование проекта: {project_path}", file=sys.stderr)
    
    # Сканируем проект
    lemmas = scan_project(project_path)
    print(f"Найдено {len(lemmas)} sorry-лемм.", file=sys.stderr)
    
    if not lemmas:
        print("Sorry-леммы не найдены.", file=sys.stderr)
        sys.exit(0)
    
    # Строим граф зависимостей
    edges = find_dependencies(lemmas)
    print(f"Найдено {len(edges)} связей между леммами.", file=sys.stderr)
    
    # Создаём граф для анализа
    graph = defaultdict(set)
    for edge in edges:
        graph[edge.from_lemma].add(edge.to_lemma)
    
    # Анализируем граф
    chains, parallel_groups, isolated = find_chains_and_groups(lemmas, edges)
    
    # Создаём систему
    system = SorrySystem(
        lemmas=lemmas,
        edges=edges,
        sequential_chains=chains,
        parallel_groups=parallel_groups,
        isolated_lemmas=isolated
    )
    
    # Анализируем систему уравнений
    analysis = analyze_equation_system(lemmas)
    
    # Генерируем отчёт
    report_content = generate_report(system, analysis, graph)
    
    # Сохраняем результаты
    output_dir = project_path if project_path.is_dir() else project_path.parent
    
    # JSON с графом
    graph_data = {
        "lemmas": [
            {
                "name": l.name,
                "file": l.file_path,
                "line": l.line_number,
                "inputs": [{"name": v.name, "type": v.type_str} for v in l.inputs],
                "output": l.output,
                "relation_type": l.relation_type,
                "lhs": l.lhs,
                "rhs": l.rhs
            }
            for l in lemmas
        ],
        "edges": [asdict(e) for e in edges],
        "analysis": {
            "sequential_chains": chains,
            "parallel_groups": parallel_groups,
            "isolated_lemmas": isolated
        }
    }
    
    graph_path = output_dir / "sorry_graph.json"
    graph_path.write_text(json.dumps(graph_data, indent=2, ensure_ascii=False))
    print(f"Граф сохранён: {graph_path}", file=sys.stderr)
    
    # Текстовый отчёт
    report_path = output_dir / "sorry_system_report.md"
    report_path.write_text(report_content)
    print(f"Отчёт сохранён: {report_path}", file=sys.stderr)
    
    # Выводим отчёт в stdout
    print(report_content)


if __name__ == "__main__":
    main()
