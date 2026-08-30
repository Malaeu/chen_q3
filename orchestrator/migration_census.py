#!/usr/bin/env python3
"""Exact live-source versus knowledge.db migration census."""

from __future__ import annotations

import argparse
import collections
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
    stale = sorted(database_ids - source_ids)
    return {
        "surface": surface,
        "source_rows": len(source_ids),
        "database_rows": len(database_ids),
        "unmigrated_rows": len(unmigrated),
        "unmigrated_ids": unmigrated,
        "stale_rows": len(stale),
        "stale_ids": stale,
    }


def make_count_row(
    surface: str,
    source: collections.Counter[str],
    database: collections.Counter[str],
) -> dict[str, object]:
    """Multiplicity-aware census row for sources with several semantic records."""
    missing = source - database
    stale = database - source
    expand = lambda counts: sorted(
        key if count == 1 else f"{key} (x{count})"
        for key, count in counts.items()
    )
    return {
        "surface": surface,
        "source_rows": sum(source.values()),
        "database_rows": sum(database.values()),
        "unmigrated_rows": sum(missing.values()),
        "unmigrated_ids": expand(missing),
        "stale_rows": sum(stale.values()),
        "stale_ids": expand(stale),
    }


def classify_verdict_surplus(
    source: collections.Counter[str],
    database: collections.Counter[str],
    live_names: set[str],
) -> tuple[collections.Counter[str], collections.Counter[str]]:
    """Split extra DB components into retained live-source history and true orphans."""
    retained: collections.Counter[str] = collections.Counter()
    vanished: collections.Counter[str] = collections.Counter()
    for key, count in (database - source).items():
        source_name = key.rsplit("::", 1)[0]
        (retained if source_name in live_names else vanished)[key] += count
    return retained, vanished


def _insights_rows(conn: sqlite3.Connection) -> list[dict[str, object]]:
    source = kb_migrate_journal.parse()[0]
    source_machine = {
        str(row["id"]) for row in source if str(row["id"]).startswith("INSIGHT_")
    }
    source_legacy = {str(row["id"]) for row in source} - source_machine
    database = {
        str(row[0]): str(row[1])
        for row in conn.execute(
            "SELECT id,kind FROM journal_entry WHERE source_file=?",
            (INSIGHTS_SOURCE,),
        )
    }
    database_machine = {
        row_id for row_id, kind in database.items()
        if row_id.startswith("INSIGHT_") and kind == "insight"
    }
    database_legacy = set(database) - database_machine
    return [
        make_row("insights_legacy", source_legacy, database_legacy),
        make_row("insights_machine", source_machine, database_machine),
    ]


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
    live_names = set(kb_migrate_verdicts.collect_files())
    source_ids: collections.Counter[str] = collections.Counter()
    for name, paths in sorted(kb_migrate_verdicts.collect_files().items()):
        canonical = paths[0]
        text = canonical.read_text(encoding="utf-8", errors="ignore")
        iteration = kb_migrate_verdicts.parse_iteration(text)
        verdict_kill, _subject = kb_migrate_verdicts.parse_verdict_kill(text)
        if iteration:
            source_ids[f"{canonical.name}::iteration"] += 1
        if verdict_kill:
            source_ids[f"{canonical.name}::kill"] += 1

    database_ids: collections.Counter[str] = collections.Counter()
    for source_file, status in conn.execute(
        "SELECT source_file,status FROM kill WHERE source_file IN "
        "(SELECT source_file FROM source_ledger WHERE note='wave 3 verdicts')"
    ):
        klass = "kill" if status == "killed" else "iteration"
        database_ids[f"{Path(str(source_file)).name}::{klass}"] += 1
    # Iterations reused from FAILED_STRATEGIES keep that canonical row and attach the
    # verdict as provenance instead of duplicating it under a verdict source_file.
    for ref, status in conn.execute(
        "SELECT DISTINCT e.ref,k.status FROM kill_evidence e "
        "JOIN kill k ON k.id=e.kill_id WHERE e.kind='verdict'"
    ):
        klass = "kill" if status == "killed" else "iteration"
        database_ids[f"{Path(str(ref)).name}::{klass}"] += 1
    row = make_count_row("verdicts", source_ids, database_ids)
    # The verdict parser is intentionally monotone and conservative: structured
    # components discovered by today's parser must exist in the database, while
    # older, explicitly adjudicated components from a still-live source are
    # retained as history.  They are not projection drift.  Only a row whose
    # source document itself vanished is stale.
    retained, vanished = classify_verdict_surplus(source_ids, database_ids, live_names)
    expand = lambda counts: sorted(
        key if count == 1 else f"{key} (x{count})"
        for key, count in counts.items()
    )
    row["stale_rows"] = sum(vanished.values())
    row["stale_ids"] = expand(vanished)
    row["retained_historical_rows"] = sum(retained.values())
    row["retained_historical_ids"] = expand(retained)
    return row


def census(db_path: Path = DEFAULT_DB) -> dict[str, object]:
    if not db_path.is_file():
        raise FileNotFoundError(db_path)
    conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
    try:
        rows = [*_insights_rows(conn), _progress_row(conn), _verdict_row(conn)]
    finally:
        conn.close()
    return {
        "schema": "q3_migration_census.v1",
        "status": "PASS" if all(
            row["unmigrated_rows"] == 0 and row["stale_rows"] == 0 for row in rows
        ) else "DRIFT",
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
        print("surface          source rows | database rows | unmigrated | stale")
        print("-" * 75)
        for row in payload["surfaces"]:
            print(
                f"{row['surface']:<16} {row['source_rows']:>11} | "
                f"{row['database_rows']:>13} | {row['unmigrated_rows']:>10} | "
                f"{row['stale_rows']:>5}"
            )
            for row_id in row["unmigrated_ids"][:10]:
                print(f"  - {row_id}")
            remaining = len(row["unmigrated_ids"]) - 10
            if remaining > 0:
                print(f"  ... and {remaining} more")
            for row_id in row["stale_ids"][:10]:
                print(f"  - stale database row: {row_id}")
            remaining_stale = len(row["stale_ids"]) - 10
            if remaining_stale > 0:
                print(f"  ... and {remaining_stale} more stale rows")
            retained = row.get("retained_historical_rows", 0)
            if retained:
                print(f"  - retained historical rows from live sources: {retained}")
        print(f"status: {payload['status']}")
    return 1 if args.strict and payload["status"] != "PASS" else 0


if __name__ == "__main__":
    raise SystemExit(main())
