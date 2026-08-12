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
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN_ROOT = REPO / "q3.lean.aristotle"
BUILD_LIB = LEAN_ROOT / ".lake/build/lib/lean"
TEMPLATE = HERE / "EnvDump.lean"


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


def run(mods: list[str], prefixes: list[str], out_path: Path,
        timeout: int) -> tuple[int, str]:
    src = TEMPLATE.read_text(encoding="utf-8")
    assert "-- IMPORTS_PLACEHOLDER" in src, "в шаблоне нет метки импортов"
    imports = "\n".join(f"import {m}" for m in mods)
    src = src.replace("-- IMPORTS_PLACEHOLDER", imports)
    pref = ", ".join(f"`{p}" for p in prefixes)
    src = src.replace("dumpEnv [`Q3]", f"dumpEnv [{pref}]")

    run_file = LEAN_ROOT / "EnvDumpRun.lean"
    run_file.write_text(src, encoding="utf-8")
    try:
        r = subprocess.run(["lake", "env", "lean", run_file.name],
                           cwd=LEAN_ROOT, capture_output=True, text=True,
                           timeout=timeout)
    finally:
        run_file.unlink(missing_ok=True)

    # Lean шлёт и диагностику, и наш вывод в stdout. Разделяем по форме строки.
    recs, errs = [], []
    for line in r.stdout.split("\n"):
        (recs if line.startswith("{") else errs).append(line)
    out_path.write_text("\n".join(recs) + "\n", encoding="utf-8")
    return len(recs), "\n".join(x for x in errs + [r.stderr] if x.strip())


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--prefix", default="Q3.Proofs.RouteB",
                    help="какие модули импортировать (по умолчанию RouteB)")
    ap.add_argument("--namespace", action="append", default=None,
                    help="фильтр печатаемых имён; повторяемый (по умолчанию Q3)")
    ap.add_argument("--out", default=str(HERE / "env_index.jsonl"))
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--limit", type=int, default=0, help="взять первые N модулей")
    a = ap.parse_args()

    if not BUILD_LIB.is_dir():
        print(f"нет каталога сборки {BUILD_LIB} — сначала lake build", file=sys.stderr)
        return 2

    built = built_modules(a.prefix)
    have_src = source_modules(a.prefix)
    if a.limit:
        built = built[:a.limit]
    if not built:
        print(f"под префиксом {a.prefix} нет ни одного собранного модуля", file=sys.stderr)
        return 2

    # ЗНАМЕНАТЕЛЬ ПОКРЫТИЯ. Зелёный отчёт по трети дерева читается как зелёный по
    # всему дереву. Печатаем обе величины ВСЕГДА, а не только когда всё сошлось.
    print(f"модулей с исходником : {len(have_src)}")
    print(f"модулей собранных    : {len(built)}")
    missing = len(have_src) - len(built)
    if missing > 0:
        print(f"НЕ ПОКРЫТО           : {missing} — их объявлений в индексе НЕТ")

    n, errs = run(built, a.namespace or ["Q3"], Path(a.out), a.timeout)
    if errs.strip():
        print("── диагностика Lean ──", file=sys.stderr)
        print(errs[:4000], file=sys.stderr)
    print(f"объявлений в индексе : {n}")
    print(f"файл                 : {a.out}")

    if n == 0:
        print("ноль объявлений — это отказ, а не пустой результат", file=sys.stderr)
        return 1

    # сводка: на чём стоят доказательства
    std = {"propext", "Classical.choice", "Quot.sound"}
    dirty, sorried = [], []
    for line in Path(a.out).read_text(encoding="utf-8").split("\n"):
        if not line.startswith("{"):
            continue
        d = json.loads(line)
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
