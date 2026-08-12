#!/usr/bin/env python3
"""Собрать индекс Lean environment: имя → ELABORATED тип, аксиомы, адрес.

ЗАЧЕМ. Слой 1 конструктора. `atom_describe.py` читает исходный ТЕКСТ и потому не
видит переменных внешней `section`, неявных параметров, universe-параметров, посылок
typeclass после elaboration, вставленных приведений и раскрытых нотаций. Решать по
тексту о применимости теоремы нельзя. Источник истины — сам Lean.

КАК. Подставляет `import` собранных модулей в `EnvDump.lean` и запускает его через
`lake env lean`. Один прогон на всё дерево: окружение строится один раз.

ЧТО НЕ ДЕЛАЕТ. Не собирает Lean. Видит ТОЛЬКО то, что уже скомпилировано в
`.lake/build`, и говорит вслух, сколько модулей пропустил. Не судит применимость —
это индекс, а не comparator.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN_ROOT = REPO / "q3.lean.aristotle"
BUILD_LIB = LEAN_ROOT / ".lake/build/lib/lean"
TEMPLATE = HERE / "EnvDump.lean"

REQUIRED_RECORD_FIELDS = {
    "name", "kind", "type", "levelParams", "numBinders", "file", "line",
    "doc", "typeConsts", "axioms", "isPrivate", "isUnsafe",
}


def built_modules(prefix: str) -> list[str]:
    """Модули с готовым .olean. Только их можно импортировать без пересборки."""
    out = []
    for o in sorted(BUILD_LIB.rglob("*.olean")):
        mod = str(o.relative_to(BUILD_LIB).with_suffix("")).replace("/", ".")
        if mod.startswith(prefix):
            out.append(mod)
    return out


def source_modules(prefix: str) -> list[str]:
    """Модули, у которых есть исходник. Разница с `built_modules` — цена честности:
    индекс покрывает не дерево, а собранную его часть, и это надо печатать."""
    out = []
    root = LEAN_ROOT / prefix.replace(".", "/")
    base = prefix.split(".")[0]
    for f in sorted((LEAN_ROOT / base).rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        mod = str(f.relative_to(LEAN_ROOT).with_suffix("")).replace("/", ".")
        if mod.startswith(prefix):
            out.append(mod)
    return out


def source_backed_modules(built: list[str], sources: list[str]) \
        -> tuple[list[str], list[str], list[str]]:
    """Отделить текущие модули от сиротских `.olean`.

    Build-кэш переживает удаление исходника. Импортировать такую сироту нельзя:
    она уже не является декларацией текущего дерева и может конфликтовать с её
    канонической заменой. Возвращаем (импортировать, не собрано, сироты).
    """
    bset, sset = set(built), set(sources)
    return sorted(bset & sset), sorted(sset - bset), sorted(bset - sset)


def stale_source_modules(modules: list[str]) -> list[str]:
    """`.olean` старше своего `.lean` не описывает текущее исходное дерево."""
    out = []
    for mod in modules:
        rel = Path(*mod.split("."))
        source = LEAN_ROOT / rel.with_suffix(".lean")
        olean = BUILD_LIB / rel.with_suffix(".olean")
        if source.stat().st_mtime > olean.stat().st_mtime:
            out.append(mod)
    return out


def _validated_records(stdout: str) -> tuple[list[dict], list[str]]:
    """Разобрать JSONL Lean и отвергнуть частичный/неверный индекс."""
    records, diagnostics = [], []
    seen: set[str] = set()
    for line_no, line in enumerate(stdout.splitlines(), 1):
        if not line.startswith("{"):
            if line.strip():
                diagnostics.append(line)
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as exc:
            diagnostics.append(f"stdout:{line_no}: неверный JSON: {exc}")
            continue
        if not isinstance(record, dict):
            diagnostics.append(f"stdout:{line_no}: JSON-запись не объект")
            continue
        missing = REQUIRED_RECORD_FIELDS - record.keys()
        if missing:
            diagnostics.append(
                f"stdout:{line_no}: нет полей {', '.join(sorted(missing))}")
            continue
        name = record.get("name")
        if not isinstance(name, str) or not name:
            diagnostics.append(f"stdout:{line_no}: пустое/нестроковое имя")
            continue
        if name in seen:
            diagnostics.append(f"stdout:{line_no}: дубликат объявления {name}")
            continue
        seen.add(name)
        records.append(record)
    return records, diagnostics


def _write_jsonl_atomic(records: list[dict], out_path: Path) -> None:
    """Опубликовать только целиком проверенный derived-индекс."""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=out_path.parent,
            prefix=f".{out_path.name}.", suffix=".tmp", delete=False) as f:
        tmp = Path(f.name)
        for record in records:
            f.write(json.dumps(record, ensure_ascii=False, separators=(",", ":")))
            f.write("\n")
    os.replace(tmp, out_path)


def run(mods: list[str], prefixes: list[str],
        timeout: int) -> tuple[int, list[dict], str]:
    src = TEMPLATE.read_text(encoding="utf-8")
    assert "-- IMPORTS_PLACEHOLDER" in src, "в шаблоне нет метки импортов"
    imports = "\n".join(f"import {m}" for m in mods)
    src = src.replace("-- IMPORTS_PLACEHOLDER", imports)
    pref = ", ".join(f"`{p}" for p in prefixes)
    module_filter = ", ".join(f"`{m}" for m in mods)
    src = src.replace("dumpEnv [] []",
                      f"dumpEnv [{pref}] [{module_filter}]")

    with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=LEAN_ROOT,
            prefix="EnvDumpRun_", suffix=".lean", delete=False) as f:
        f.write(src)
        run_file = Path(f.name)
    try:
        r = subprocess.run(["lake", "env", "lean", run_file.name],
                           cwd=LEAN_ROOT, capture_output=True, text=True,
                           timeout=timeout)
    finally:
        run_file.unlink(missing_ok=True)

    # Lean шлёт и диагностику, и наш вывод в stdout. Даже если он успел напечатать
    # часть JSON до ошибки, такой индекс не публикуется.
    records, diagnostics = _validated_records(r.stdout)
    if r.stderr.strip():
        diagnostics.append(r.stderr.strip())
    code = r.returncode
    if not records:
        diagnostics.append("ноль объявлений — это отказ, а не пустой результат")
        code = code or 1
    if diagnostics and any("неверный JSON" in x or "нет полей" in x
                           or "дубликат объявления" in x
                           or "не объект" in x or "пустое/нестроковое" in x
                           for x in diagnostics):
        code = code or 1
    return code, records, "\n".join(diagnostics)


def module_selection(prefix: str, limit: int = 0) \
        -> tuple[list[str], list[str], list[str], list[str], list[str]]:
    """Freeze one honest import selection and all coverage-denominator classes."""
    built_all = built_modules(prefix)
    sources = source_modules(prefix)
    source_backed, never_built, orphaned = source_backed_modules(built_all, sources)
    stale = stale_source_modules(source_backed)
    selected = sorted(set(source_backed) - set(stale))
    if limit:
        selected = selected[:limit]
    return selected, sources, never_built, orphaned, stale


def module_state_fingerprint(prefix: str) -> tuple[tuple[str, int, int], ...]:
    """Detect a concurrent source/build rewrite even when module names stay equal."""
    rows = []
    source_root = LEAN_ROOT / prefix.split(".")[0]
    for path in sorted(source_root.rglob("*.lean")):
        mod = str(path.relative_to(LEAN_ROOT).with_suffix("")).replace("/", ".")
        if mod.startswith(prefix):
            stat = path.stat()
            rows.append((f"source:{mod}", stat.st_mtime_ns, stat.st_size))
    for path in sorted(BUILD_LIB.rglob("*.olean")):
        mod = str(path.relative_to(BUILD_LIB).with_suffix("")).replace("/", ".")
        if mod.startswith(prefix):
            stat = path.stat()
            rows.append((f"olean:{mod}", stat.st_mtime_ns, stat.st_size))
    return tuple(rows)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--prefix", default="Q3.Proofs.RouteB",
                    help="какие модули импортировать (по умолчанию RouteB)")
    ap.add_argument("--namespace", action="append", default=None,
                    help="опциональный повторяемый фильтр имён; по умолчанию все выбранные модули")
    ap.add_argument("--out", default=str(HERE / "env_index.jsonl"))
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--limit", type=int, default=0, help="взять первые N модулей")
    a = ap.parse_args()

    if not BUILD_LIB.is_dir():
        print(f"нет каталога сборки {BUILD_LIB} — сначала lake build", file=sys.stderr)
        return 2

    built, have_src, missing_modules, orphaned_oleans, stale_oleans = \
        module_selection(a.prefix, a.limit)
    before_state = module_state_fingerprint(a.prefix)
    if not built:
        print(f"под префиксом {a.prefix} нет ни одного собранного модуля", file=sys.stderr)
        return 2

    # ЗНАМЕНАТЕЛЬ ПОКРЫТИЯ. Зелёный отчёт по трети дерева читается как зелёный по
    # всему дереву. Печатаем обе величины ВСЕГДА, а не только когда всё сошлось.
    print(f"модулей с исходником       : {len(have_src)}")
    print(f"актуальных собранных       : {len(built)}")
    print(f"устаревших .olean исключено: {len(stale_oleans)}")
    for mod in stale_oleans[:10]:
        print(f"   устарел: {mod}")
    print(f"сиротских .olean исключено : {len(orphaned_oleans)}")
    for mod in orphaned_oleans[:10]:
        print(f"   сирота: {mod}")
    missing = len(have_src) - len(built)
    if missing > 0:
        print(f"НЕ ПОКРЫТО                 : {missing} — их объявлений в индексе НЕТ")
    if a.limit:
        print(f"лимит импорта              : {a.limit}")

    code, records, errs = run(built, a.namespace or [], a.timeout)
    n = len(records)
    if errs.strip():
        print("── диагностика Lean ──", file=sys.stderr)
        print(errs[:4000], file=sys.stderr)
    print(f"объявлений в индексе : {n}")
    print(f"файл                 : {a.out}")

    if code != 0:
        print("индекс не опубликован: Lean/JSON прогон не завершился чисто", file=sys.stderr)
        return code

    # Другая сессия могла собрать/удалить модуль во время долгого обхода. В этом
    # случае результат уже устарел до публикации: оставляем прежний индекс целым.
    after = module_selection(a.prefix, a.limit)
    if (after != (built, have_src, missing_modules, orphaned_oleans, stale_oleans)
            or module_state_fingerprint(a.prefix) != before_state):
        print("индекс не опубликован: набор .lean/.olean изменился во время прогона",
              file=sys.stderr)
        return 1
    _write_jsonl_atomic(records, Path(a.out))

    # сводка: на чём стоят доказательства
    std = {"propext", "Classical.choice", "Quot.sound"}
    dirty, sorried = [], []
    for d in records:
        extra = set(d["axioms"]) - std
        if "sorryAx" in extra:
            sorried.append(d["name"])
        elif extra:
            dirty.append((d["name"], sorted(extra)))
    print(f"на sorryAx           : {len(sorried)}")
    print(f"на прочих аксиомах   : {len(dirty)}")
    for nm in sorried[:10]:
        print(f"   sorry: {nm}")
    for nm, ax in dirty[:10]:
        print(f"   аксиомы: {nm} ← {', '.join(ax)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
