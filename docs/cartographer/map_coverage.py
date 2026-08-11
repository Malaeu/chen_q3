#!/usr/bin/env python3
"""Приложение к карте: КАЖДЫЙ Lean-файл RouteB одной строкой, включая невидимые карте.

Зачем. `docs/routeB_bus/MAP.md` — рукописная карта маршрута, и она описывает узлы, а не
файлы. Замер 2026-08-11: из 204 файлов `Q3/Proofs/RouteB` карта упоминает 20. Остальные 184
не находятся обходом карты вообще — включая `CCMFiniteWeilBottomSpectral.lean`, где в тот же
день был построен заново мост `ker ↔ eigenspace`, стоявший восемью строками выше нужного
поставщика.

Это и есть механизм дублестроения: не забывчивость, а невидимость. Инструмент его не лечит —
он делает его **измеримым и просматриваемым**: приложение генерируется, карта остаётся
рукописной.

Дескриптор берётся, в порядке приоритета:
  1. первая строка docstring-шапки файла `/-! # ... -/` или `/-- ... -/`
  2. имя первой публичной теоремы
  3. `— нет описания —`  ← это долг, он виден в сводке

ЧТО ЭТОТ ИНСТРУМЕНТ НЕ ДЕЛАЕТ. Не решает, важен ли файл, и не правит `MAP.md`. Дескриптор —
пересказ автора, а не проверка: правило «рекомендуешь — открой file:line» действует.

Read-only по отношению к `MAP.md`; пишет только в `--out`.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
ROUTEB = REPO / "q3.lean.aristotle/Q3/Proofs/RouteB"
MAP = REPO / "docs/routeB_bus/MAP.md"

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(theorem|lemma|def|abbrev|structure)\s+([A-Za-z_][A-Za-z_0-9'.]*)")


def descriptor(path: Path) -> tuple[str, str]:
    """Вернуть (дескриптор, источник): шапка файла, иначе первая декларация, иначе долг."""
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").split("\n")
    except Exception:
        return "— файл не прочитан —", "ОШИБКА"

    # шапка `/-! # Заголовок` или `/-- текст`
    in_doc = False
    for ln in lines[:60]:
        s = ln.strip()
        if not in_doc and (s.startswith("/-!") or s.startswith("/--")):
            in_doc = True
            rest = s.lstrip("/-!").lstrip("/--").strip().lstrip("#").strip()
            if rest and not rest.startswith("-"):
                return rest[:110], "шапка"
            continue
        if in_doc:
            if s in ("-/", ""):
                if s == "-/":
                    in_doc = False
                continue
            t = s.lstrip("#").strip()
            if t and not t.startswith("Copyright") and not t.startswith("Released"):
                return t[:110], "шапка"
    for ln in lines:
        m = DECL.match(ln)
        if m:
            return f"первая декларация: `{m.group(2)}`", "декларация"
    return "— нет описания —", "ДОЛГ"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="docs/routeB_bus/MAP_COVERAGE.md")
    ap.add_argument("--stdout", action="store_true", help="печатать вместо записи")
    args = ap.parse_args()

    if not ROUTEB.is_dir():
        print(f"нет каталога {ROUTEB}", file=sys.stderr)
        return 2

    files = sorted(ROUTEB.rglob("*.lean"))   # rglob: подкаталоги (MuntzV3/…) тоже считаются
    map_text = MAP.read_text(encoding="utf-8", errors="replace") if MAP.is_file() else ""

    rows, debts, in_map = [], 0, 0
    for f in files:
        stem = f.stem
        rel = f.relative_to(ROUTEB).as_posix()[:-5]   # путь без .lean, для подкаталогов
        seen = re.search(rf"\b{re.escape(stem)}\b", map_text) is not None
        in_map += seen
        d, src = descriptor(f)
        debts += src == "ДОЛГ"
        try:
            n_sorry = subprocess.run(["rg", "-c", "sorry", str(f)], capture_output=True,
                                     text=True, timeout=20).stdout.strip()
        except Exception:
            n_sorry = ""
        rows.append((rel, "карта" if seen else "—", d, n_sorry or "0"))

    out = []
    out.append("# Приложение к карте: покрытие файлов RouteB")
    out.append("")
    out.append("**Генерируется.** Руками не править — правки затрутся. Источник:")
    out.append("`python3 docs/cartographer/map_coverage.py`. Рукописная карта — `MAP.md`, она")
    out.append("описывает узлы маршрута; это приложение описывает **файлы**, и оно полное.")
    out.append("")
    out.append(f"Всего файлов: **{len(files)}** · упомянуто в `MAP.md`: **{in_map}** · "
               f"вне карты: **{len(files) - in_map}** · без описания в шапке: **{debts}**")
    out.append("")
    out.append("«вне карты» не значит «лишний»: значит, что обходом карты файл не находится.")
    out.append("Именно так 2026-08-11 был построен заново мост `ker ↔ eigenspace`, стоявший в")
    out.append("`CCMFiniteWeilBottomSpectral.lean` восемью строками выше нужного поставщика.")
    out.append("")
    out.append("| файл | в карте | что это | `sorry` |")
    out.append("|---|---|---|---|")
    for stem, seen, d, ns in rows:
        out.append(f"| `{stem}` | {seen} | {d} | {ns} |")
    out.append("")
    out.append("Дескриптор — пересказ шапки, а не проверка содержимого. Перед употреблением "
               "открыть файл.")
    text = "\n".join(out) + "\n"

    if args.stdout:
        print(text)
    else:
        p = REPO / args.out
        p.write_text(text, encoding="utf-8")
        print(f"записано: {p}")
    print(f"файлов {len(files)} · в карте {in_map} · вне карты {len(files) - in_map} · "
          f"без описания {debts}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
