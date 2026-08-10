#!/usr/bin/env python3
"""
Картограф, фаза 1 — детерминированный инвентарь.

Собирает КАЖДУЮ теорему/лемму живого фронта с её полной сигнатурой,
сверяет с существующими каталогами и помечает сирот.

Ничего не пишет в репу. Выход — JSON рядом со скриптом.
Агентов не запускает: это фундамент, он обязан быть воспроизводимым.

Запуск:  python3 inventory.py [--root PATH] [--scope RouteB|all]
"""
import argparse
import json
import re
import sqlite3
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
OUT_DIR = Path(__file__).resolve().parent
MUSEUM = "PrimeCert"          # январская генерёнка — read-only музей

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|structure|abbrev|instance)\s+([A-Za-z_][A-Za-z_0-9'\.]*)")


def strip_comments(text: str) -> str:
    """Убрать -- и /- -/ , сохранив структуру строк."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            elif text[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def signature(lines, start):
    """Сигнатура = от объявления до ':=' или 'by', максимум 40 строк."""
    buf = []
    for k in range(start, min(start + 40, len(lines))):
        ln = lines[k]
        buf.append(ln.strip())
        if ":=" in ln or re.search(r"\bby\b\s*$", ln) or ln.rstrip().endswith("where"):
            break
    sig = " ".join(buf)
    cut = sig.find(":=")
    return (sig[:cut] if cut > 0 else sig).strip()


def scan(root: Path, scope: str):
    base = root / "q3.lean.aristotle" / "Q3"
    if scope == "RouteB":
        base = base / "Proofs" / "RouteB"
    found, files = [], 0
    paths = sorted(base.rglob("*.lean"))
    total = len(paths)
    for idx, p in enumerate(paths, 1):
        if MUSEUM in p.parts:
            continue
        if idx % 100 == 0 or idx == total:
            print(f"[{idx}/{total}] {idx*100//total}% | сканирую {p.name[:44]}", flush=True)
        try:
            raw = p.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        files += 1
        lines = strip_comments(raw).split("\n")
        for i, ln in enumerate(lines):
            m = DECL.match(ln)
            if not m:
                continue
            found.append({
                "kind": m.group(1),
                "name": m.group(2),
                "file": str(p.relative_to(root)),
                "line": i + 1,
                "signature": signature(lines, i),
            })
    return found, files


def catalogued_names(root: Path):
    """Имена, названные хоть в одном документе или в базе лемм."""
    named = set()
    doc_dirs = [root / "docs", root / "q3.lean.aristotle" / "ACTIVE"]
    blob = []
    for d in doc_dirs:
        if not d.exists():
            continue
        for p in d.rglob("*.md"):
            try:
                blob.append(p.read_text(encoding="utf-8", errors="replace"))
            except Exception:
                pass
    text = "\n".join(blob)

    db = root / "q3.lean.aristotle" / "aristotle_db" / "aristotle_proofs.db"
    in_db = set()
    if db.exists():
        con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
        in_db = {r[0] for r in con.execute("select name from lemmas") if r[0]}
        con.close()
    return text, in_db


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(REPO))
    ap.add_argument("--scope", default="RouteB", choices=["RouteB", "all"])
    args = ap.parse_args()
    root = Path(args.root)

    print(f"[1/3] Сканирую {args.scope} (музей {MUSEUM} исключён)", flush=True)
    decls, files = scan(root, args.scope)
    print(f"      найдено {len(decls)} объявлений в {files} файлах", flush=True)

    print("[2/3] Читаю существующие каталоги", flush=True)
    doc_text, in_db = catalogued_names(root)
    print(f"      база лемм: {len(in_db)} имён", flush=True)

    print("[3/3] Сверяю и помечаю сирот", flush=True)
    for d in decls:
        d["in_docs"] = d["name"] in doc_text
        d["in_lemma_db"] = d["name"] in in_db
        d["orphan"] = not (d["in_docs"] or d["in_lemma_db"])

    orphans = [d for d in decls if d["orphan"]]
    by_file = {}
    for d in orphans:
        by_file[d["file"]] = by_file.get(d["file"], 0) + 1

    result = {
        "scope": args.scope,
        "museum_excluded": MUSEUM,
        "files_scanned": files,
        "declarations": len(decls),
        "in_docs": sum(1 for d in decls if d["in_docs"]),
        "in_lemma_db": sum(1 for d in decls if d["in_lemma_db"]),
        "orphans": len(orphans),
        "orphan_files_top": sorted(by_file.items(), key=lambda x: -x[1])[:15],
        "items": decls,
    }
    out = OUT_DIR / f"inventory_{args.scope}.json"
    out.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")

    print()
    print(f"  объявлений:      {result['declarations']}")
    print(f"  названы в docs:  {result['in_docs']}")
    print(f"  есть в базе лемм:{result['in_lemma_db']}")
    print(f"  СИРОТ:           {result['orphans']}")
    print(f"  -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
