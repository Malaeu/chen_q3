#!/usr/bin/env python3
"""Synchronize the live Route B declaration inventory into aristotle_proofs.db.

The original one-shot backfill skipped files that were already present in the
database.  Consequently, declarations added later to an existing Lean file were
invisible forever.  It also hard-coded the retired Linux checkout path.

This replacement is cross-machine and idempotent:

* ``--check`` is read-only and reports missing/stale declaration rows;
* ``--sync`` inserts current declarations, removes stale rows for current Route B
  documents, and canonicalizes those document paths relative to q3.lean.aristotle;
* it never claims Lean authority: the database remains a metadata index.
"""
from __future__ import annotations

import argparse
import importlib.util
import re
import sqlite3
import sys
from collections import defaultdict
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
Q3_ROOT = REPO / "q3.lean.aristotle"
DB = Q3_ROOT / "aristotle_db" / "aristotle_proofs.db"
INVENTORY_MODULE = REPO / "docs" / "cartographer" / "inventory.py"
ROUTEB_PREFIX = "Q3/Proofs/RouteB/"
INCOMPLETE = re.compile(r"\b(sorry|admit)\b")


def load_inventory_module():
    spec = importlib.util.spec_from_file_location("q3_cartographer_inventory", INVENTORY_MODULE)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {INVENTORY_MODULE}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def normalize_doc_path(raw: str) -> str:
    path = raw.replace("\\", "/")
    marker = "q3.lean.aristotle/"
    if marker in path:
        return path.split(marker, 1)[1]
    return path.lstrip("./")


def stable_doc_id(rel: str, existing_ids: set[str]) -> str:
    stem = Path(rel).stem
    candidate = stem
    if candidate not in existing_ids:
        return candidate
    parent = Path(rel).parent.name
    candidate = f"{stem}__{parent}"
    if candidate not in existing_ids:
        return candidate
    n = 2
    while f"{candidate}_{n}" in existing_ids:
        n += 1
    return f"{candidate}_{n}"


def declaration_status(path: Path, line: int, next_line: int | None) -> str:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    end = (next_line - 1) if next_line is not None else len(lines)
    body = "\n".join(lines[max(line - 1, 0):end])
    return "sorry" if INCOMPLETE.search(body) else "proven"


def current_declarations() -> tuple[dict[str, list[dict]], int]:
    inventory = load_inventory_module()
    declarations, files = inventory.scan(REPO, "RouteB")
    by_file: dict[str, list[dict]] = defaultdict(list)
    for item in declarations:
        rel = item["file"].split("q3.lean.aristotle/", 1)[1]
        by_file[rel].append(item)
    return dict(by_file), files


def inspect(conn: sqlite3.Connection, by_file: dict[str, list[dict]]) -> dict:
    docs = list(conn.execute("select doc_id, path, source from docs"))
    by_path: dict[str, list[tuple[str, str, str | None]]] = defaultdict(list)
    for row in docs:
        by_path[normalize_doc_path(row[1])].append(row)

    report = {
        "matched": {},
        "missing_docs": [],
        "ambiguous_docs": [],
        "missing_rows": [],
        "stale_rows": [],
    }
    for rel, items in sorted(by_file.items()):
        matches = by_path.get(rel, [])
        if not matches:
            report["missing_docs"].append(rel)
            continue
        if len(matches) != 1:
            report["ambiguous_docs"].append((rel, [row[0] for row in matches]))
            continue
        doc_id, _, source = matches[0]
        report["matched"][rel] = (doc_id, source)
        current = {item["name"] for item in items}
        indexed = {
            row[0]
            for row in conn.execute("select name from lemmas where doc_id = ?", (doc_id,))
        }
        report["missing_rows"].extend((rel, doc_id, name) for name in sorted(current - indexed))
        report["stale_rows"].extend((rel, doc_id, name) for name in sorted(indexed - current))
    return report


def print_report(report: dict, files: int, declarations: int) -> None:
    print(f"Route B files: {files}")
    print(f"Route B declarations: {declarations}")
    print(f"Matched document rows: {len(report['matched'])}")
    print(f"Missing document rows: {len(report['missing_docs'])}")
    print(f"Ambiguous document rows: {len(report['ambiguous_docs'])}")
    print(f"Missing declaration rows: {len(report['missing_rows'])}")
    print(f"Stale declaration rows: {len(report['stale_rows'])}")
    for rel in report["missing_docs"][:10]:
        print(f"  MISSING_DOC {rel}")
    for rel, ids in report["ambiguous_docs"][:10]:
        print(f"  AMBIGUOUS_DOC {rel}: {', '.join(ids)}")
    for rel, _, name in report["missing_rows"][:20]:
        print(f"  MISSING_DECL {rel}: {name}")
    for rel, _, name in report["stale_rows"][:20]:
        print(f"  STALE_DECL {rel}: {name}")


def sync(conn: sqlite3.Connection, by_file: dict[str, list[dict]], report: dict) -> tuple[int, int, int]:
    if report["ambiguous_docs"]:
        names = ", ".join(rel for rel, _ in report["ambiguous_docs"][:5])
        raise RuntimeError(f"refusing ambiguous document mapping: {names}")

    existing_ids = {row[0] for row in conn.execute("select doc_id from docs")}
    created_docs = 0
    inserted = 0
    removed = 0

    for rel in report["missing_docs"]:
        path = Q3_ROOT / rel
        doc_id = stable_doc_id(rel, existing_ids)
        existing_ids.add(doc_id)
        text = path.read_text(encoding="utf-8", errors="replace")
        status = "in_progress" if INCOMPLETE.search(text) else "proven"
        conn.execute(
            """
            insert into docs
              (doc_id, path, approach, priority, status, stage, source,
               aristotle_uuid, lines, size_bytes)
            values (?, ?, 'ROUTE_B', 'HIGH', ?, null, 'source_inventory',
                    null, ?, ?)
            """,
            (doc_id, rel, status, len(text.splitlines()), path.stat().st_size),
        )
        report["matched"][rel] = (doc_id, "source_inventory")
        created_docs += 1

    missing_by_doc = {(doc_id, name) for _, doc_id, name in report["missing_rows"]}
    for rel in report["missing_docs"]:
        doc_id = report["matched"][rel][0]
        missing_by_doc.update((doc_id, item["name"]) for item in by_file[rel])

    for rel, items in sorted(by_file.items()):
        doc_id, source = report["matched"][rel]
        path = Q3_ROOT / rel
        text = path.read_text(encoding="utf-8", errors="replace")
        doc_status = "in_progress" if INCOMPLETE.search(text) else "proven"
        conn.execute(
            """
            update docs set path = ?, lines = ?, size_bytes = ?, status = ?
            where doc_id = ?
            """,
            (rel, len(text.splitlines()), path.stat().st_size, doc_status, doc_id),
        )

        ordered = sorted(items, key=lambda item: item["line"])
        for index, item in enumerate(ordered):
            key = (doc_id, item["name"])
            if key not in missing_by_doc:
                continue
            next_line = ordered[index + 1]["line"] if index + 1 < len(ordered) else None
            status = declaration_status(path, item["line"], next_line)
            lemma_id = f"source__{doc_id}__{item['name']}"
            suffix = 2
            while conn.execute("select 1 from lemmas where lemma_id = ?", (lemma_id,)).fetchone():
                lemma_id = f"source__{doc_id}__{item['name']}__{suffix}"
                suffix += 1
            conn.execute(
                """
                insert into lemmas
                  (lemma_id, name, doc_id, status, priority, statement,
                   deps_json, notes, line_start, line_end)
                values (?, ?, ?, ?, 'HIGH', ?, '[]', ?, ?, ?)
                """,
                (
                    lemma_id,
                    item["name"],
                    doc_id,
                    status,
                    item["signature"][:500],
                    f"Source inventory sync; declaration kind={item['kind']}",
                    item["line"],
                    (next_line - 1) if next_line is not None else len(text.splitlines()),
                ),
            )
            inserted += 1

    for _, doc_id, name in report["stale_rows"]:
        removed += conn.execute(
            "delete from lemmas where doc_id = ? and name = ?", (doc_id, name)
        ).rowcount

    return created_docs, inserted, removed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="read-only drift check (default)")
    mode.add_argument("--sync", action="store_true", help="synchronize the tracked metadata index")
    args = parser.parse_args()

    by_file, files = current_declarations()
    declarations = sum(len(items) for items in by_file.values())
    uri = f"file:{DB}?mode={'rw' if args.sync else 'ro'}"
    conn = sqlite3.connect(uri, uri=True)
    try:
        report = inspect(conn, by_file)
        print_report(report, files, declarations)
        drift = bool(
            report["missing_docs"]
            or report["ambiguous_docs"]
            or report["missing_rows"]
            or report["stale_rows"]
        )
        if not args.sync:
            return 1 if drift else 0
        created_docs, inserted, removed = sync(conn, by_file, report)
        integrity = conn.execute("pragma integrity_check").fetchone()[0]
        if integrity != "ok":
            raise RuntimeError(f"integrity_check failed: {integrity}")
        conn.commit()
        print(
            f"SYNCED created_docs={created_docs} inserted={inserted} "
            f"removed_stale={removed} integrity={integrity}"
        )
        return 0
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


if __name__ == "__main__":
    sys.exit(main())
