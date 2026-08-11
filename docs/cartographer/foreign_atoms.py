#!/usr/bin/env python3
"""Связать чужое Lean-дерево с нашей базой атомов: что у них уже доказано на наших опорах.

Задача владельца: «не делать новые доказательства в Lean, если они уже есть». Для этого
нужно не сравнивать имена теорем (они разные), а сравнивать **атомы** — внешние леммы
Mathlib, на которые опирается доказательство. Если чужая лемма стоит на тех же атомах, что
и наш незакрытый шаг, она кандидат в поставщики.

Механика та же, что в `atoms.py`: взять тела доказательств, вычесть объекты, определённые
внутри самого дерева, остаток и есть атомы.

    свои(дерево)   = все имена, объявленные в дереве (theorem/lemma/def/...)
    атомы(дерево)  = имена, встречающиеся в телах, но не объявленные там

Выход — три множества:

    общие      атомы, на которые опираемся и мы, и они  → мост существует
    только их  атомы, которых у нас нет вовсе           → чего нам не хватает
    только наши                                          → чего нет у них

и, для общих, список их деклараций, использующих этот атом — то есть готовые утверждения,
стоящие на нашей же опоре.

ЧТО ЭТО НЕ ДЕЛАЕТ. Совпадение атомов не означает, что чужая лемма применима: у неё свои
гипотезы и свой предмет. Это **поиск кандидатов**, а не вывод. Каждый кандидат подлежит
чтению `file:line` перед употреблением — правило про суррогат по форме действует.

Read-only.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import sqlite3
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
DB = f"file:{REPO}/q3.lean.aristotle/aristotle_db/knowledge.db?mode=ro"

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|structure|abbrev|instance)\s+([A-Za-z_][A-Za-z_0-9'\.]*)")
IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9'\.]*")

# служебное, что не является атомом в нашем смысле
NOISE = {
    "theorem", "lemma", "def", "structure", "abbrev", "instance", "where", "by", "at",
    "with", "fun", "let", "have", "show", "from", "this", "if", "then", "else", "do",
    "match", "end", "namespace", "section", "variable", "open", "import", "set_option",
    "private", "protected", "noncomputable", "deriving", "extends", "in", "for",
}


def strip_comments(text: str) -> str:
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            depth += 1; i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1; i += 2
        else:
            if depth == 0:
                out.append(text[i])
            elif text[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def scan_tree(root: Path, skip: tuple[str, ...]):
    """Вернуть (свои имена, атом → {файлы}, декларация → (файл, строка))."""
    own, uses, decls = set(), collections.defaultdict(set), {}
    files = 0
    for p in sorted(root.rglob("*.lean")):
        if any(s in p.parts for s in skip):
            continue
        try:
            raw = p.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        files += 1
        lines = strip_comments(raw).split("\n")
        rel = str(p.relative_to(root))
        for i, ln in enumerate(lines):
            m = DECL.match(ln)
            if m:
                own.add(m.group(2))
                decls[m.group(2)] = (rel, i + 1)
        for ln in lines:
            for tok in IDENT.findall(ln):
                if tok not in NOISE:
                    uses[tok].add(rel)
    return own, uses, decls, files


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--foreign", required=True, help="корень чужого Lean-дерева")
    ap.add_argument("--skip", default=".lake,comparator", help="части пути через запятую")
    ap.add_argument("--top", type=int, default=25)
    ap.add_argument("--json", default="")
    args = ap.parse_args()

    froot = Path(args.foreign).expanduser().resolve()
    if not froot.is_dir():
        print(f"нет каталога: {froot}"); return 2
    skip = tuple(s for s in args.skip.split(",") if s)

    print(f"чужое дерево : {froot}")
    own, uses, decls, files = scan_tree(froot, skip)
    foreign_atoms = {a: fs for a, fs in uses.items() if a not in own}
    print(f"  файлов {files} · своих объявлений {len(own)} · атомов {len(foreign_atoms)}")

    con = sqlite3.connect(DB, uri=True)
    ours = {r[0] for r in con.execute("select name from atom")}
    ours_kind = dict(con.execute("select name, kind from atom"))
    ours_files = dict(con.execute("select name, n_files from atom"))
    print(f"наша база    : атомов {len(ours)}")
    print()

    common = sorted(set(foreign_atoms) & ours, key=lambda a: -ours_files.get(a, 0))
    only_theirs = sorted(set(foreign_atoms) - ours, key=lambda a: -len(foreign_atoms[a]))
    only_ours = sorted(ours - set(foreign_atoms))

    print(f"ОБЩИЕ АТОМЫ            {len(common)}   ← мост: их леммы стоят на наших опорах")
    print(f"ТОЛЬКО У НИХ           {len(only_theirs)}   ← опоры, которых мы не используем")
    print(f"ТОЛЬКО У НАС           {len(only_ours)}")
    print()

    print(f"── общие атомы, топ-{args.top} по нашему весу ──")
    print(f"  {'атом':<38} {'наш kind':<12} {'наших файлов':>12}  их файлов")
    for a in common[:args.top]:
        print(f"  {a[:38]:<38} {ours_kind.get(a,'?'):<12} {ours_files.get(a,0):>12}  "
              f"{len(foreign_atoms[a])}")

    print()
    print(f"── только у них, топ-{args.top} по их весу ──")
    for a in only_theirs[:args.top]:
        print(f"  {a[:52]:<52} {len(foreign_atoms[a])} файлов")

    if args.json:
        Path(args.json).write_text(json.dumps({
            "foreign_root": str(froot), "foreign_files": files,
            "foreign_own_decls": len(own), "foreign_atoms": len(foreign_atoms),
            "our_atoms": len(ours),
            "common": common, "only_theirs": only_theirs[:500], "only_ours": only_ours[:500],
            "common_detail": {a: {"our_kind": ours_kind.get(a), "our_files": ours_files.get(a),
                                  "their_files": sorted(foreign_atoms[a])[:20]} for a in common},
        }, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"\nJSON: {args.json}")

    print()
    print("Совпадение атомов — кандидат, не вывод: у чужой леммы свои гипотезы и свой")
    print("предмет. Перед употреблением открыть file:line и прочитать докстринг.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
