#!/usr/bin/env python3
"""Project reviewed branch decisions from Progress_Log.md into knowledge.db.

The Markdown journal is canonical. This idempotent projection makes its eight-field
records available to kb.py, ask.sh, and Spine without turning raw event prose into a
second decision source.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sqlite3
from datetime import date
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SRC = REPO / "docs" / "Progress_Log.md"
DEFAULT_DB = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"
SOURCE_FILE = "docs/Progress_Log.md"

ENTRY_HEAD = re.compile(
    r"^##\s+(?P<date>\d{4}-\d{2}-\d{2})"
    r"(?:\s*→\s*\d{4}-\d{2}-\d{2})?\s+—\s+(?P<title>.+?)\s*$"
)
LEVEL_TWO_HEAD = re.compile(r"^##\s+.+$", re.MULTILINE)
FIELD = re.compile(
    r"^\*\*(?P<label>[^*\n]+):\*\*\s*(?P<value>.*?)"
    r"(?=^\*\*[^*\n]+:\*\*|^---\s*$|\Z)",
    re.MULTILINE | re.DOTALL,
)

REQUIRED_FIELDS = (
    "fork",
    "selected",
    "why",
    "rejected",
    "technique",
    "next",
    "addresses",
)


def _field_key(label: str) -> str | None:
    normalized = " ".join(label.split()).casefold()
    if normalized == "развилка":
        return "fork"
    if normalized == "выбрали":
        return "selected"
    if normalized == "почему":
        return "why"
    if normalized == "что отвергли и почему":
        return "rejected"
    if normalized.startswith("техника"):
        return "technique"
    if normalized == "следующий ход":
        return "next"
    if normalized == "адреса":
        return "addresses"
    if normalized == "чей вердикт и аргумент":
        return "external_verdict"
    return None


def _compact(value: str) -> str:
    return " ".join(value.split())


def parse_entries(path: Path = SRC) -> list[dict[str, str | None]]:
    text = path.read_text(encoding="utf-8")
    headings = list(LEVEL_TWO_HEAD.finditer(text))
    rows: list[dict[str, str | None]] = []
    seen_ids: set[str] = set()
    for index, heading in enumerate(headings):
        match = ENTRY_HEAD.match(heading.group(0))
        if not match:
            continue
        end = headings[index + 1].start() if index + 1 < len(headings) else len(text)
        chunk = text[heading.start():end].strip()
        fields: dict[str, str] = {}
        for field_match in FIELD.finditer(chunk):
            key = _field_key(field_match.group("label"))
            if key:
                fields[key] = _compact(field_match.group("value"))
        missing = [key for key in REQUIRED_FIELDS if not fields.get(key)]
        if missing:
            raise ValueError(
                f"Progress_Log entry {match.group('date')} {match.group('title')!r} "
                f"is missing fields: {', '.join(missing)}"
            )
        title = _compact(match.group("title"))
        digest = hashlib.sha256(chunk.encode("utf-8")).hexdigest()
        entry_id = (
            f"branch_{match.group('date')}_"
            f"{hashlib.sha256(title.encode('utf-8')).hexdigest()[:12]}"
        )
        if entry_id in seen_ids:
            raise ValueError(
                f"duplicate Progress_Log date/title identity: {match.group('date')} {title!r}"
            )
        seen_ids.add(entry_id)
        rows.append(
            {
                "id": entry_id,
                "date": match.group("date"),
                "kind": "branch_decision",
                "title": title,
                "workstream": None,
                "state": "recorded",
                "channel": "external" if fields.get("external_verdict") else "control-plane",
                "target": fields["fork"],
                "validation": fields["technique"],
                "artifact_sha": digest,
                "boundary": fields["rejected"],
                "next_target": fields["next"],
                "body": chunk,
                "source_file": SOURCE_FILE,
            }
        )
    if not rows:
        raise ValueError("Progress_Log contains no eight-field branch entries")
    return rows


JOURNAL_COLUMNS = (
    "id",
    "date",
    "kind",
    "title",
    "workstream",
    "state",
    "channel",
    "target",
    "validation",
    "artifact_sha",
    "boundary",
    "next_target",
    "body",
    "source_file",
)


def migrate(conn: sqlite3.Connection, rows: list[dict[str, str | None]]) -> None:
    columns = ",".join(JOURNAL_COLUMNS)
    placeholders = ",".join("?" for _ in JOURNAL_COLUMNS)
    updates = ",".join(
        f"{column}=excluded.{column}" for column in JOURNAL_COLUMNS if column != "id"
    )
    conn.executemany(
        f"INSERT INTO journal_entry ({columns}) VALUES ({placeholders}) "
        f"ON CONFLICT(id) DO UPDATE SET {updates}",
        [tuple(row[column] for column in JOURNAL_COLUMNS) for row in rows],
    )
    has_fts = conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='journal_fts'"
    ).fetchone()
    if has_fts:
        conn.execute("INSERT INTO journal_fts(journal_fts) VALUES('rebuild')")
    has_ledger = conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='source_ledger'"
    ).fetchone()
    if has_ledger:
        conn.execute(
            "INSERT INTO source_ledger (source_file, expected_rows, migrated_at, note) "
            "VALUES (?,?,?,?) ON CONFLICT(source_file) DO UPDATE SET "
            "expected_rows=excluded.expected_rows, migrated_at=excluded.migrated_at, "
            "note=excluded.note",
            (SOURCE_FILE, len(rows), date.today().isoformat(), "reviewed branch decisions"),
        )
    conn.commit()


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Project reviewed Progress_Log branch decisions into knowledge.db"
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--db", type=Path, default=DEFAULT_DB)
    args = parser.parse_args()

    rows = parse_entries()
    external = sum(row["channel"] == "external" for row in rows)
    print(
        f"parsed {len(rows)} branch decisions · external verdict rows {external} · "
        f"source {SOURCE_FILE}"
    )
    if args.dry_run:
        return 0
    if not args.db.is_file():
        raise SystemExit(f"knowledge.db not found: {args.db}")
    conn = sqlite3.connect(args.db)
    try:
        migrate(conn, rows)
    finally:
        conn.close()
    print(f"migrated {len(rows)} branch decisions into {args.db}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
