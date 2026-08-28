#!/usr/bin/env python3
"""
Картограф, фаза 1 — детерминированный инвентарь.

Собирает КАЖДОЕ объявление живого фронта с его полной сигнатурой и
сверяет с существующими каталогами. Историческое поле ``orphan`` означает
только «не названо в docs и не попало в индекс имён»; оно не означает, что
объявление не используется Lean-кодом.

Ничего не пишет в репу. Выход — JSON рядом со скриптом.
Агентов не запускает: это фундамент, он обязан быть воспроизводимым.

Запуск:  python3 inventory.py [--root PATH] [--scope RouteB|all]
"""
import argparse
import json
import os
import re
import sqlite3
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
OUT_DIR = Path(__file__).resolve().parent
MUSEUM = "PrimeCert"          # январская генерёнка — read-only музей
DOC_SOURCE_ROOTS = (Path("docs"), Path("q3.lean.aristotle/ACTIVE"))
DOC_EXACT_EXCLUDES = frozenset({
    Path("docs/routeB_bus/MAP_COVERAGE.md"),
    Path("docs/TOOLS.md"),
})
DOC_SUBTREE_EXCLUDES = (Path("docs/generated"),)
DOC_VOLATILE_COMPONENTS = frozenset({".lake"})

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


class DocumentationCorpusError(RuntimeError):
    """The documentation-coverage corpus cannot be classified safely."""


def _is_excluded_document(relative: Path) -> bool:
    if any(part in DOC_VOLATILE_COMPONENTS for part in relative.parts):
        return True
    if relative in DOC_EXACT_EXCLUDES:
        return True
    return any(
        relative == subtree or subtree in relative.parents
        for subtree in DOC_SUBTREE_EXCLUDES
    )


def documentation_files(root: Path) -> list[Path]:
    """Return deterministic, non-generated Markdown evidence without following dirs."""
    repo = root.resolve(strict=True)
    selected: list[Path] = []
    for source_relative in DOC_SOURCE_ROOTS:
        source = repo / source_relative
        if not source.exists():
            continue
        if source.is_symlink() or not source.is_dir():
            raise DocumentationCorpusError(f"invalid documentation source root: {source}")
        for dirpath, dirnames, filenames in os.walk(source, followlinks=False):
            directory = Path(dirpath)
            relative_directory = directory.relative_to(repo)
            dirnames[:] = sorted(
                name
                for name in dirnames
                if not (directory / name).is_symlink()
                and not _is_excluded_document(relative_directory / name)
            )
            for filename in sorted(filenames):
                if not filename.endswith(".md"):
                    continue
                path = directory / filename
                lexical_relative = path.relative_to(repo)
                if not path.is_symlink() and _is_excluded_document(lexical_relative):
                    continue
                try:
                    resolved = path.resolve(strict=True)
                    resolved_relative = resolved.relative_to(repo)
                except (OSError, ValueError) as exc:
                    raise DocumentationCorpusError(
                        f"broken or external documentation path: {path}"
                    ) from exc
                if _is_excluded_document(lexical_relative) or _is_excluded_document(
                    resolved_relative
                ):
                    continue
                if not resolved.is_file():
                    raise DocumentationCorpusError(f"documentation path is not a file: {path}")
                selected.append(path)
    return selected


def catalogued_names(root: Path):
    """Имена, названные в независимом документе или в базе лемм."""
    blob = []
    for path in documentation_files(root):
        try:
            blob.append(path.read_text(encoding="utf-8", errors="replace"))
        except OSError as exc:
            raise DocumentationCorpusError(f"cannot read documentation path: {path}") from exc
    text = "\n".join(blob)

    db = root / "q3.lean.aristotle" / "aristotle_db" / "aristotle_proofs.db"
    in_db = set()
    if db.exists():
        con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
        in_db = {r[0] for r in con.execute("select name from lemmas") if r[0]}
        con.close()
    return text, in_db


def build_inventory(root: Path, scope: str) -> dict:
    print(f"[1/3] Сканирую {scope} (музей {MUSEUM} исключён)", flush=True)
    decls, files = scan(root, scope)
    print(f"      найдено {len(decls)} объявлений в {files} файлах", flush=True)

    print("[2/3] Читаю существующие каталоги", flush=True)
    doc_text, in_db = catalogued_names(root)
    print(f"      база лемм: {len(in_db)} имён", flush=True)

    print("[3/3] Сверяю покрытие каталога имён", flush=True)
    for declaration in decls:
        declaration["in_docs"] = declaration["name"] in doc_text
        declaration["in_lemma_db"] = declaration["name"] in in_db
        declaration["orphan"] = not (
            declaration["in_docs"] or declaration["in_lemma_db"]
        )

    orphans = [declaration for declaration in decls if declaration["orphan"]]
    by_file = {}
    for declaration in orphans:
        by_file[declaration["file"]] = by_file.get(declaration["file"], 0) + 1

    return {
        "scope": scope,
        "museum_excluded": MUSEUM,
        "files_scanned": files,
        "declarations": len(decls),
        "in_docs": sum(1 for declaration in decls if declaration["in_docs"]),
        "in_lemma_db": sum(1 for declaration in decls if declaration["in_lemma_db"]),
        "orphans": len(orphans),
        "uncatalogued": len(orphans),
        "orphan_files_top": sorted(by_file.items(), key=lambda item: -item[1])[:15],
        "items": decls,
    }


def inventory_bytes(result: dict) -> bytes:
    return json.dumps(result, ensure_ascii=False, indent=2).encode("utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(REPO))
    ap.add_argument("--scope", default="RouteB", choices=["RouteB", "all"])
    args = ap.parse_args()
    root = Path(args.root)

    result = build_inventory(root, args.scope)
    out = OUT_DIR / f"inventory_{args.scope}.json"
    out.write_bytes(inventory_bytes(result))

    print()
    print(f"  объявлений:      {result['declarations']}")
    print(f"  названы в docs:  {result['in_docs']}")
    print(f"  есть в базе лемм:{result['in_lemma_db']}")
    print(f"  НЕ В КАТАЛОГЕ:   {result['uncatalogued']}")
    print(f"  -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
