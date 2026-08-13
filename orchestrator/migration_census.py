#!/usr/bin/env python3
"""Exact live-source versus knowledge.db migration census."""

from __future__ import annotations

import argparse
import json
import sqlite3
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import (  # noqa: E402
    kb_migrate_journal,
    kb_migrate_progress_log,
    kb_migrate_verdicts,
)

DEFAULT_DB = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"
INSIGHTS_SOURCE = kb_migrate_journal.SOURCE_FILE


def make_row(
    surface: str,
    source_ids: set[str],
    database_ids: set[str],
) -> dict[str, object]:
    unmigrated = sorted(source_ids - database_ids)
    return {
        "surface": surface,
        "source_rows": len(source_ids),
        "database_rows": len(database_ids),
        "unmigrated_rows": len(unmigrated),
        "unmigrated_ids": unmigrated,
    }


def _insights_row(conn: sqlite3.Connection) -> dict[str, object]:
    source_ids = {str(row["id"]) for row in kb_migrate_journal.parse()[0]}
    database_ids = {
        str(row[0])
        for row in conn.execute(
            "SELECT id FROM journal_entry WHERE source_file=?",
            (INSIGHTS_SOURCE,),
        )
    }
    return make_row("insights", source_ids, database_ids)


def _progress_row(conn: sqlite3.Connection) -> dict[str, object]:
    source_ids = {str(row["id"]) for row in kb_migrate_progress_log.parse_entries()}
    database_ids = {
        str(row[0])
        for row in conn.execute(
            "SELECT id FROM journal_entry WHERE source_file=?",
            (kb_migrate_progress_log.SOURCE_FILE,),
        )
    }
    return make_row("progress_log", source_ids, database_ids)


def _verdict_row(conn: sqlite3.Connection) -> dict[str, object]:
    source_ids: set[str] = set()
    for name, paths in sorted(kb_migrate_verdicts.collect_files().items()):
        canonical = paths[0]
        text = canonical.read_text(encoding="utf-8", errors="ignore")
        iteration = kb_migrate_verdicts.parse_iteration(text)
        verdict_kill, _subject = kb_migrate_verdicts.parse_verdict_kill(text)
        if iteration or verdict_kill:
            source_ids.add(canonical.relative_to(REPO).as_posix())

    database_ids = {
        str(row[0])
        for row in conn.execute(
            "SELECT DISTINCT source_file FROM kill WHERE source_file LIKE '%PROSHKA_%' "
            "UNION SELECT DISTINCT ref FROM kill_evidence "
            "WHERE kind IN ('verdict','verdict_copy')"
        )
    }
    database_ids &= source_ids
    return make_row("verdicts", source_ids, database_ids)


def census(db_path: Path = DEFAULT_DB) -> dict[str, object]:
    if not db_path.is_file():
        raise FileNotFoundError(db_path)
    conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
    try:
        rows = [_insights_row(conn), _progress_row(conn), _verdict_row(conn)]
    finally:
        conn.close()
    return {
        "schema": "q3_migration_census.v1",
        "status": "PASS" if all(row["unmigrated_rows"] == 0 for row in rows) else "DRIFT",
        "surfaces": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--db", type=Path, default=DEFAULT_DB)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    payload = census(args.db)
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        print("surface          source rows | database rows | unmigrated rows")
        print("-" * 67)
        for row in payload["surfaces"]:
            print(
                f"{row['surface']:<16} {row['source_rows']:>11} | "
                f"{row['database_rows']:>13} | {row['unmigrated_rows']:>15}"
            )
            for row_id in row["unmigrated_ids"][:10]:
                print(f"  - {row_id}")
            remaining = len(row["unmigrated_ids"]) - 10
            if remaining > 0:
                print(f"  ... and {remaining} more")
        print(f"status: {payload['status']}")
    return 1 if args.strict and payload["status"] != "PASS" else 0


if __name__ == "__main__":
    raise SystemExit(main())
