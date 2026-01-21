#!/usr/bin/env python3.11
"""
lean_error_parser.py - Парсер ошибок Lean 4 для автоматической генерации семантических sorry

Этот модуль парсит вывод `lake build` и генерирует семантически именованные леммы
на основе типа ошибки. Это ключевой компонент для автоматизации декомпозиции доказательств.

Использование:
    lake build 2> error.log
    python3.11 lean_error_parser.py error.log

Вывод:
    JSON-объект с предложением по созданию леммы.
"""

import re
import json
import sys
from dataclasses import dataclass, asdict
from typing import Optional, List, Tuple
from pathlib import Path


@dataclass
class LemmaSuggestion:
    """Структура для хранения предложения по созданию леммы."""
    error_type: str
    error_code: str
    file_path: str
    line_number: int
    column_number: int
    suggested_name: str
    suggested_statement: str
    full_lemma_code: str
    original_error: str
    resolution_hint: str


# =============================================================================
# РЕГУЛЯРНЫЕ ВЫРАЖЕНИЯ ДЛЯ ПАРСИНГА ОШИБОК LEAN 4
# =============================================================================

# Базовый паттерн для извлечения позиции ошибки
LOCATION_PATTERN = re.compile(
    r"(?P<file>[\w/\.\-]+\.lean):(?P<line>\d+):(?P<col>\d+):\s*error:\s*(?P<message>.*)",
    re.DOTALL
)

# Словарь паттернов для различных типов ошибок
ERROR_PATTERNS = {
    # -------------------------------------------------------------------------
    # Категория 1: Ошибки типов
    # -------------------------------------------------------------------------
    "type_mismatch": {
        "pattern": re.compile(
            r"type mismatch\n\s*(?P<term>.*?)\nhas type\n\s*(?P<actual_type>.*?)\nbut is expected to have type\n\s*(?P<expected_type>.*?)(?:\n|$)",
            re.DOTALL
        ),
        "prefix": "type_mismatch_of_",
        "hint": "Проверить типы, использовать `@` для явных аргументов, `show` для уточнения цели."
    },
    "app_type_mismatch": {
        "pattern": re.compile(
            r"application type mismatch\n\s*(?P<app>.*?)\nargument\n\s*(?P<arg>.*?)\nhas type\n\s*(?P<actual_type>.*?)\nbut is expected to have type\n\s*(?P<expected_type>.*?)(?:\n|$)",
            re.DOTALL
        ),
        "prefix": "app_mismatch_",
        "hint": "Проверить типы аргументов функции."
    },
    "kernel_type_mismatch": {
        "pattern": re.compile(r"\(kernel\) type mismatch"),
        "prefix": "kernel_type_",
        "hint": "Критическая ошибка. Пересмотреть доказательство с нуля."
    },
    
    # -------------------------------------------------------------------------
    # Категория 2: Синтез инстансов
    # -------------------------------------------------------------------------
    "synth_failed": {
        "pattern": re.compile(
            r"failed to synthesize(?: instance)?\n\s*(?P<typeclass>.*?)(?:\n|$)",
            re.DOTALL
        ),
        "prefix": "inst_synth_of_",
        "hint": "Добавить нужный `import`, определить инстанс вручную."
    },
    "ambiguous_inst": {
        "pattern": re.compile(r"ambiguous, possible interpretations"),
        "prefix": "ambig_inst_for_",
        "hint": "Указать инстанс явно: `(@operation _ _ inst ...)`"
    },
    
    # -------------------------------------------------------------------------
    # Категория 3: Унификация
    # -------------------------------------------------------------------------
    "unify_failed": {
        "pattern": re.compile(
            r"failed to unify\n\s*(?P<term1>.*?)\nwith\n\s*(?P<term2>.*?)(?:\n|$)",
            re.DOTALL
        ),
        "prefix": "unify_",
        "hint": "Проверить структуру выражений, унифицируемость."
    },
    "motive_not_correct": {
        "pattern": re.compile(r"motive is not type correct"),
        "prefix": "motive_",
        "hint": "Использовать `subst`, `conv`, `induction ... with ...`."
    },
    
    # -------------------------------------------------------------------------
    # Категория 4: Ошибки тактик
    # -------------------------------------------------------------------------
    "rfl_failed": {
        "pattern": re.compile(r"tactic 'rfl' failed"),
        "prefix": "rfl_",
        "hint": "Использовать `simp`, `ring` или `show`."
    },
    "simp_no_progress": {
        "pattern": re.compile(r"simp made no progress"),
        "prefix": "simp_",
        "hint": "Развернуть определения (`unfold`), добавить леммы в `simp`."
    },
    "ring_failed": {
        "pattern": re.compile(r"tactic 'ring' failed"),
        "prefix": "ring_",
        "hint": "Проверить структуру, использовать `ring_nf`."
    },
    "linarith_failed": {
        "pattern": re.compile(r"tactic 'linarith' failed"),
        "prefix": "linarith_",
        "hint": "Добавить гипотезы, проверить линейность, использовать `nlinarith`."
    },
    "nlinarith_failed": {
        "pattern": re.compile(r"tactic 'nlinarith' failed"),
        "prefix": "nlinarith_",
        "hint": "Упростить, разбить на подзадачи."
    },
    "omega_failed": {
        "pattern": re.compile(r"tactic 'omega' failed"),
        "prefix": "omega_",
        "hint": "Проверить типы (Nat/Int), убедиться в отсутствии нелинейности."
    },
    "rw_failed": {
        "pattern": re.compile(
            r"rewrite tactic failed.*?did not find instance of the pattern",
            re.DOTALL
        ),
        "prefix": "rw_",
        "hint": "Проверить, что лемма применима; использовать `conv` для перезаписи под биндерами."
    },
    "exact_failed": {
        "pattern": re.compile(r"tactic 'exact\??' failed"),
        "prefix": "exact_search_",
        "hint": "Проверить импорты, попробовать другие ключевые слова."
    },
    "assumption_failed": {
        "pattern": re.compile(r"tactic 'assumption' failed"),
        "prefix": "assumption_",
        "hint": "Проверить контекст."
    },
    "contradiction_failed": {
        "pattern": re.compile(r"tactic 'contradiction' failed"),
        "prefix": "contradiction_from_",
        "hint": "Найти или доказать противоречие."
    },
    "decide_failed": {
        "pattern": re.compile(r"tactic 'decide' failed"),
        "prefix": "decide_",
        "hint": "Проверить Decidable инстанс."
    },
    "norm_num_failed": {
        "pattern": re.compile(r"norm_num failed"),
        "prefix": "norm_num_",
        "hint": "Проверить структуру числового выражения."
    },
    "positivity_failed": {
        "pattern": re.compile(r"positivity failed"),
        "prefix": "positivity_",
        "hint": "Добавить гипотезы о знаках."
    },
    "polyrith_failed": {
        "pattern": re.compile(r"polyrith failed"),
        "prefix": "polyrith_",
        "hint": "Упростить выражение."
    },
    "aesop_failed": {
        "pattern": re.compile(r"aesop: failed"),
        "prefix": "aesop_",
        "hint": "Добавить подсказки."
    },
    
    # -------------------------------------------------------------------------
    # Категория 5: Идентификаторы
    # -------------------------------------------------------------------------
    "unknown_id": {
        "pattern": re.compile(r"unknown identifier '(?P<id>[^']+)'"),
        "prefix": "unknown_id_",
        "hint": "Проверить имя, добавить `import`."
    },
    "unknown_const": {
        "pattern": re.compile(r"unknown constant '(?P<const>[^']+)'"),
        "prefix": "unknown_const_",
        "hint": "Добавить импорт."
    },
    "ambiguous_id": {
        "pattern": re.compile(r"ambiguous identifier '(?P<id>[^']+)'"),
        "prefix": "ambig_id_",
        "hint": "Указать полное имя (namespace)."
    },
    
    # -------------------------------------------------------------------------
    # Категория 6: Ядро Lean
    # -------------------------------------------------------------------------
    "kernel_meta": {
        "pattern": re.compile(r"\(kernel\) declaration has metavariables"),
        "prefix": "kernel_meta_in_",
        "hint": "Найти и решить все `sorry` или `_`."
    },
    "kernel_unknown_const": {
        "pattern": re.compile(r"\(kernel\) unknown constant '(?P<const>[^']+)'"),
        "prefix": "kernel_unknown_const_",
        "hint": "Ошибка сборки или окружения."
    },
    
    # -------------------------------------------------------------------------
    # Категория 7: Прочее
    # -------------------------------------------------------------------------
    "max_rec_depth": {
        "pattern": re.compile(r"maximum recursion depth has been reached"),
        "prefix": "max_rec_depth_at_",
        "hint": "Увеличить лимит (`set_option maxRecDepth ...`) или переписать доказательство."
    },
    "synth_placeholder": {
        "pattern": re.compile(r"don't know how to synthesize placeholder"),
        "prefix": "synth_placeholder_for_",
        "hint": "Указать терм явно."
    },
    "unsolved_goals": {
        "pattern": re.compile(r"unsolved goals\n(?P<goals>.*?)(?:\n\n|$)", re.DOTALL),
        "prefix": "goal_",
        "hint": "Цель не закрыта. Продолжить доказательство."
    },
}


# =============================================================================
# ФУНКЦИИ ГЕНЕРАЦИИ ИМЁН
# =============================================================================

def sanitize_name(name: str) -> str:
    """Очищает строку для использования в качестве идентификатора Lean."""
    # Удаляем пробелы и специальные символы
    name = re.sub(r'[^\w]', '_', name)
    # Удаляем множественные подчёркивания
    name = re.sub(r'_+', '_', name)
    # Удаляем подчёркивания в начале и конце
    name = name.strip('_')
    # Ограничиваем длину
    if len(name) > 40:
        name = name[:40]
    return name.lower()


def extract_term_name(term: str) -> str:
    """Извлекает короткое имя из терма Lean."""
    # Удаляем пробелы и переносы строк
    term = term.strip().replace('\n', ' ')
    # Берём первое слово или функцию
    match = re.match(r'^(\w+)', term)
    if match:
        return match.group(1)
    return "expr"


def generate_name_for_type_mismatch(match: re.Match) -> Tuple[str, str]:
    """Генерирует имя и стейтмент для ошибки type_mismatch."""
    term = match.group("term").strip()
    actual = match.group("actual_type").strip()
    expected = match.group("expected_type").strip()
    
    term_name = extract_term_name(term)
    expected_name = extract_term_name(expected)
    
    name = f"type_mismatch_of_{sanitize_name(term_name)}_expected_{sanitize_name(expected_name)}"
    statement = f"({term}) = ({expected})"  # Упрощённый стейтмент
    
    return name, statement


def generate_name_for_synth_failed(match: re.Match) -> Tuple[str, str]:
    """Генерирует имя и стейтмент для ошибки synth_failed."""
    typeclass = match.group("typeclass").strip()
    tc_name = extract_term_name(typeclass)
    
    name = f"inst_synth_of_{sanitize_name(tc_name)}"
    statement = typeclass
    
    return name, statement


def generate_name_for_unify_failed(match: re.Match) -> Tuple[str, str]:
    """Генерирует имя и стейтмент для ошибки unify_failed."""
    term1 = match.group("term1").strip()
    term2 = match.group("term2").strip()
    
    t1_name = extract_term_name(term1)
    t2_name = extract_term_name(term2)
    
    name = f"unify_{sanitize_name(t1_name)}_with_{sanitize_name(t2_name)}"
    statement = f"({term1}) = ({term2})"
    
    return name, statement


def generate_name_for_unknown_id(match: re.Match) -> Tuple[str, str]:
    """Генерирует имя и стейтмент для ошибки unknown_id."""
    id_name = match.group("id").strip()
    
    name = f"unknown_id_{sanitize_name(id_name)}"
    statement = f"-- Определить {id_name}"
    
    return name, statement


def generate_name_for_unsolved_goals(match: re.Match) -> Tuple[str, str]:
    """Генерирует имя и стейтмент для unsolved_goals."""
    goals = match.group("goals").strip()
    
    # Ищем строку с ⊢ (turnstile) - это и есть цель
    goal_line = ""
    for line in goals.split('\n'):
        if '⊢' in line:
            goal_line = line.replace('⊢', '').strip()
            break
    
    if not goal_line:
        # Если не нашли ⊢, берём последнюю непустую строку
        lines = [l.strip() for l in goals.split('\n') if l.strip()]
        goal_line = lines[-1] if lines else "unknown_goal"
    
    goal_name = extract_term_name(goal_line)
    
    name = f"goal_{sanitize_name(goal_name)}"
    statement = goal_line
    
    return name, statement


def generate_name_generic(error_code: str, prefix: str, message: str) -> Tuple[str, str]:
    """Генерирует имя для ошибок без специфического парсинга."""
    # Извлекаем первые значимые слова из сообщения
    words = re.findall(r'\b\w+\b', message)[:3]
    suffix = '_'.join(sanitize_name(w) for w in words if len(w) > 2)
    
    name = f"{prefix}{suffix}" if suffix else f"{prefix}goal"
    statement = "-- TODO: определить стейтмент"
    
    return name, statement


# Маппинг error_code -> функция генерации
NAME_GENERATORS = {
    "type_mismatch": generate_name_for_type_mismatch,
    "synth_failed": generate_name_for_synth_failed,
    "unify_failed": generate_name_for_unify_failed,
    "unknown_id": generate_name_for_unknown_id,
    "unsolved_goals": generate_name_for_unsolved_goals,
}


# =============================================================================
# ОСНОВНАЯ ФУНКЦИЯ ПАРСИНГА
# =============================================================================

def parse_error(error_log: str) -> Optional[LemmaSuggestion]:
    """
    Парсит лог ошибок Lean и генерирует предложение по созданию леммы.
    
    Args:
        error_log: Полный вывод stderr от `lake build`.
    
    Returns:
        LemmaSuggestion или None, если ошибка не распознана.
    """
    # Извлекаем позицию ошибки
    location_match = LOCATION_PATTERN.search(error_log)
    if not location_match:
        return None
    
    file_path = location_match.group("file")
    line_number = int(location_match.group("line"))
    column_number = int(location_match.group("col"))
    message = location_match.group("message")
    
    # Ищем совпадение с известными паттернами ошибок
    for error_code, error_info in ERROR_PATTERNS.items():
        pattern = error_info["pattern"]
        match = pattern.search(message)
        
        if match:
            prefix = error_info["prefix"]
            hint = error_info["hint"]
            
            # Генерируем имя и стейтмент
            if error_code in NAME_GENERATORS:
                name, statement = NAME_GENERATORS[error_code](match)
            else:
                name, statement = generate_name_generic(error_code, prefix, message)
            
            # Формируем полный код леммы
            full_lemma = f"lemma {name} : {statement} := sorry"
            
            return LemmaSuggestion(
                error_type=error_code,
                error_code=error_code,
                file_path=file_path,
                line_number=line_number,
                column_number=column_number,
                suggested_name=name,
                suggested_statement=statement,
                full_lemma_code=full_lemma,
                original_error=message[:500],  # Ограничиваем длину
                resolution_hint=hint
            )
    
    # Если ни один паттерн не подошёл, возвращаем generic
    return LemmaSuggestion(
        error_type="unknown",
        error_code="unknown",
        file_path=file_path,
        line_number=line_number,
        column_number=column_number,
        suggested_name="unknown_error_lemma",
        suggested_statement="-- TODO: определить стейтмент",
        full_lemma_code="lemma unknown_error_lemma : sorry := sorry",
        original_error=message[:500],
        resolution_hint="Неизвестная ошибка. Проанализируйте вручную."
    )


def parse_multiple_errors(error_log: str) -> List[LemmaSuggestion]:
    """
    Парсит лог с несколькими ошибками.
    
    Args:
        error_log: Полный вывод stderr от `lake build`.
    
    Returns:
        Список LemmaSuggestion для каждой найденной ошибки.
    """
    suggestions = []
    
    # Разбиваем лог на отдельные ошибки по паттерну location
    error_blocks = re.split(r'(?=[\w/\.\-]+\.lean:\d+:\d+:\s*error:)', error_log)
    
    for block in error_blocks:
        if block.strip():
            suggestion = parse_error(block)
            if suggestion:
                suggestions.append(suggestion)
    
    return suggestions


# =============================================================================
# CLI ИНТЕРФЕЙС
# =============================================================================

def main():
    """Точка входа для CLI."""
    if len(sys.argv) < 2:
        print("Использование: python3.11 lean_error_parser.py <error.log>", file=sys.stderr)
        print("  или: lake build 2>&1 | python3.11 lean_error_parser.py -", file=sys.stderr)
        sys.exit(1)
    
    input_source = sys.argv[1]
    
    if input_source == "-":
        # Читаем из stdin
        error_log = sys.stdin.read()
    else:
        # Читаем из файла
        try:
            error_log = Path(input_source).read_text()
        except FileNotFoundError:
            print(f"Ошибка: файл '{input_source}' не найден.", file=sys.stderr)
            sys.exit(1)
    
    # Парсим ошибки
    suggestions = parse_multiple_errors(error_log)
    
    if not suggestions:
        print(json.dumps({"status": "no_errors", "message": "Ошибки не найдены или не распознаны."}))
    elif len(suggestions) == 1:
        print(json.dumps(asdict(suggestions[0]), indent=2, ensure_ascii=False))
    else:
        output = {
            "status": "multiple_errors",
            "count": len(suggestions),
            "suggestions": [asdict(s) for s in suggestions]
        }
        print(json.dumps(output, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
