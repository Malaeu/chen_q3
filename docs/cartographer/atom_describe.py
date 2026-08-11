#!/usr/bin/env python3
"""Обогатить атомы описаниями: что каждый атом ЕСТЬ, а не только как он называется.

Шаг 1 конструктора (замысел владельца 2026-08-11): «декомпозировать Lean полностью до
атомов с описанием, что этот атом из себя представляет — с полным описанием».

Без описания атом — это строка. Строку нельзя ни сопоставить с чужой леммой, ни отдать
агенту как задание: `mul_nonneg` и `posIndexAbove` выглядят одинаково безлико. С сигнатурой
и докстрингом атом становится утверждением, о котором можно рассуждать.

Источники, в порядке приоритета:

  1. Mathlib на диске   `q3.lean.aristotle/.lake/packages/mathlib/Mathlib` (100 МБ)
  2. наше дерево        `q3.lean.aristotle/Q3` — для атомов, которые на деле наши
  3. чужое дерево       `--foreign` — их декларации, если атом определён у них

Для каждого атома извлекается: где объявлен (`file:line`), вид (`theorem`/`def`/…),
сигнатура до `:=`, докстринг `/-- … -/` над объявлением, и число мест употребления у нас.

Атомы, которые нигде не нашлись, помечаются `UNRESOLVED` — это либо тактики, либо
нотация, либо имя, разобранное неверно. Их список — самостоятельный результат: он
показывает, где наш разбор до атомов ещё дырявый.

ЧТО ЭТО НЕ ДЕЛАЕТ. Не решает, применим ли атом: докстринг — это пересказ автора, а не
проверка. Правило про суррогат по форме действует.

Read-only: пишет только в `--json`, если указан.
"""
from __future__ import annotations

import argparse
import json
import re
import sqlite3
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
DB = f"file:{REPO}/q3.lean.aristotle/aristotle_db/knowledge.db?mode=ro"
MATHLIB = REPO / "q3.lean.aristotle/.lake/packages/mathlib/Mathlib"
OURS = REPO / "q3.lean.aristotle/Q3"

KINDS = "theorem|lemma|def|structure|abbrev|instance|class|inductive"


def namespace_at(lines: list[str], line: int) -> str:
    """Восстановить namespace-стек над строкой: `namespace A` … `end A`, плюс `open`-независимо."""
    stack = []
    for k in range(line - 1):
        s = lines[k].strip()
        m = re.match(r"^namespace\s+([A-Za-z_][A-Za-z_0-9'\.]*)", s)
        if m:
            stack.extend(m.group(1).split("."))
            continue
        m = re.match(r"^end\s+([A-Za-z_][A-Za-z_0-9'\.]*)", s)
        if m and stack:
            for part in reversed(m.group(1).split(".")):
                if stack and stack[-1] == part:
                    stack.pop()
    return ".".join(stack)


def find_declaration(name: str, root: Path) -> dict | None:
    """Найти объявление ТОЧНО этого полного имени: базовое имя плюс совпадающий namespace.

    ПОПРАВКА 2026-08-11: первая версия искала по базовому имени с `-m 1` и брала первое
    попавшееся. Так `Real.pi` находился как `def pi` из `ContinuousMap` (произведение
    непрерывных отображений), а `Complex.exp` — как степенной ряд из `PowerSeries`.
    Инструмент, дающий правдоподобно неверный ответ, хуже отсутствующего: теперь для
    каждого кандидата восстанавливается namespace-стек и полное имя сверяется с искомым.
    """
    if not root.is_dir():
        return None
    base = name.split(".")[-1]
    want_ns = ".".join(name.split(".")[:-1])
    pat = rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*({KINDS})\s+{re.escape(base)}\b"
    try:
        r = subprocess.run(["rg", "-n", "--no-heading", pat, str(root)],
                           capture_output=True, text=True, timeout=180)
    except Exception:
        return None
    if r.returncode != 0 or not r.stdout.strip():
        return None

    cands = r.stdout.strip().split("\n")[:400]
    path = line = lines = None
    fallback = None
    for c in cands:
        try:
            path_s, line_s, _ = c.split(":", 2)
            cp, cl = Path(path_s), int(line_s)
            cls = cp.read_text(encoding="utf-8", errors="replace").split("\n")
        except Exception:
            continue
        ns = namespace_at(cls, cl)
        # объявление могло быть записано и полным именем: `theorem Real.pi ...`
        full_written = re.search(rf"({KINDS})\s+{re.escape(name)}\b", cls[cl - 1]) is not None
        if ns == want_ns or full_written or (not want_ns and not ns):
            path, line, lines = cp, cl, cls
            break
        if fallback is None:
            fallback = (cp, cl, cls, ns)
    if path is None:
        return None

    # сигнатура: от объявления до `:=` или `by`, максимум 25 строк
    sig, i = [], line - 1
    while i < min(line - 1 + 25, len(lines)):
        sig.append(lines[i].strip())
        if ":=" in lines[i] or re.search(r"\bby\b\s*$", lines[i]):
            break
        i += 1
    signature = " ".join(sig)
    cut = signature.find(":=")
    signature = (signature[:cut] if cut > 0 else signature).strip()

    # докстринг: блок /-- … -/ непосредственно над объявлением
    doc, j = [], line - 2
    if j >= 0 and lines[j].strip().endswith("-/"):
        while j >= 0:
            doc.insert(0, lines[j].strip())
            if lines[j].strip().startswith("/--"):
                break
            j -= 1
    docstring = " ".join(doc).replace("/--", "").replace("-/", "").strip()

    m = re.match(rf"\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*({KINDS})",
                 lines[line - 1])
    return {
        "kind_lean": m.group(1) if m else "?",
        "namespace": namespace_at(lines, line),
        "file": str(path.relative_to(REPO)) if str(path).startswith(str(REPO)) else str(path),
        "line": line,
        "signature": signature[:600],
        "docstring": docstring[:800],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=0, help="сколько атомов обработать (0 = все)")
    ap.add_argument("--kinds", default="",
                    help="только эти наши kind через запятую, напр. NONVANISHING,ANALYSIS,LINALG")
    ap.add_argument("--foreign", default="", help="корень чужого дерева, третий источник")
    ap.add_argument("--json", default="")
    args = ap.parse_args()

    con = sqlite3.connect(DB, uri=True)
    q = "select name, kind, n_files from atom"
    if args.kinds:
        ks = ",".join("'" + k.strip() + "'" for k in args.kinds.split(",") if k.strip())
        q += f" where kind in ({ks})"
    q += " order by n_files desc"
    if args.limit:
        q += f" limit {args.limit}"
    atoms = con.execute(q).fetchall()

    foreign = Path(args.foreign).expanduser().resolve() if args.foreign else None
    print(f"атомов к разбору: {len(atoms)}")
    print(f"источники: Mathlib {'есть' if MATHLIB.is_dir() else 'НЕТ'} · "
          f"наше дерево {'есть' if OURS.is_dir() else 'НЕТ'} · "
          f"чужое {'есть' if foreign and foreign.is_dir() else 'нет'}")
    print()

    out, stats = [], {"mathlib": 0, "ours": 0, "foreign": 0, "unresolved": 0}
    for idx, (name, kind, n_files) in enumerate(atoms, 1):
        rec = {"name": name, "our_kind": kind, "our_n_files": n_files}
        for src, root in (("mathlib", MATHLIB), ("ours", OURS),
                          ("foreign", foreign if foreign else Path("/nonexistent"))):
            d = find_declaration(name, root)
            if d:
                rec.update(d); rec["source"] = src; stats[src] += 1
                break
        else:
            rec["source"] = "UNRESOLVED"; stats["unresolved"] += 1
        out.append(rec)
        if sys.stdout.isatty() and idx % 10 == 0:
            frac = idx / len(atoms)
            bar = "#" * int(30 * frac) + "." * (30 - int(30 * frac))
            sys.stdout.write(f"\r[{bar}] {100*frac:5.1f}%  {name[:34]:<34}")
            sys.stdout.flush()
    if sys.stdout.isatty():
        print()

    print()
    print(f"  найдено в Mathlib   : {stats['mathlib']}")
    print(f"  найдено у нас       : {stats['ours']}")
    print(f"  найдено в чужом     : {stats['foreign']}")
    print(f"  НЕ РАЗРЕШЕНО        : {stats['unresolved']}   ← дыры нашего разбора до атомов")
    print()

    with_doc = [r for r in out if r.get("docstring")]
    print(f"  с докстрингом       : {len(with_doc)} из {len(out)}")
    print()
    print("── примеры разобранных атомов ──")
    for r in with_doc[:5]:
        print(f"  {r['name']}  [{r['our_kind']} · {r['source']}]")
        print(f"    {r['file']}:{r['line']}")
        if r.get("signature"):
            print(f"    сигнатура: {r['signature'][:110]}")
        print(f"    описание : {r['docstring'][:110]}")
        print()

    if args.json:
        Path(args.json).write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"JSON: {args.json}")

    print("Докстринг — пересказ автора, не проверка применимости. Перед употреблением "
          "открыть file:line.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
