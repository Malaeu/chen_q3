#!/usr/bin/env python3
"""Wave 2, step 3: migrate the INSIGHTS.md journal into knowledge.db (~1800 entries).

Source: q3.lean.aristotle/docs/INSIGHTS.md — 50k lines, entries shaped
    ## KIND (DATE, TAG) -- TITLE

The TAG is a polluted dimension: it holds a workstream (Step33A.1-A), a state (checked,
in progress, blocker), or a channel (Lean, Generator, control-plane) — sometimes two at once.
Migrating it as one column would carry the defect into the database, so it is split into
`workstream` / `state` / `channel` here, with the raw tag never discarded (it stays inside
the stored body).

Recurring body bullets are lifted into their own columns because they are the queryable part:
`Target:`, the validation line (build job counts / q3_check / axiom triple), a file SHA-256,
`Boundary:` (the explicit non-claim — often the single most valuable line of an entry),
and `Next target:`.
"""

import argparse
import re
import sqlite3
import sys
from datetime import date
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kb  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "q3.lean.aristotle/docs/INSIGHTS.md"

COLUMNS = ("id", "date", "kind", "title", "workstream", "state", "channel", "target",
           "validation", "artifact_sha", "boundary", "next_target", "body", "source_file")
SOURCE_FILE = "q3.lean.aristotle/docs/INSIGHTS.md"

HEAD = re.compile(
    r"^##\s+(?P<kind>[A-Za-z][\w ]*?)\s*\((?P<date>\d{4}-\d\d-\d\d)"
    r"(?:,\s*(?P<tag>[^)]*))?\)\s*[-–—]{0,3}\s*(?P<title>.*)$")
BARE_DATE = re.compile(r"^##\s+(?P<date>\d{4}-\d\d-\d\d)\s*[-–—]{0,3}\s*(?P<title>.*)$")

# Vocabularies for splitting the polluted tag. Order matters: state wins over workstream when
# a tag carries both, because the workstream is usually recoverable from the title as well.
STATES = ("checked", "in progress", "closed node", "blocker", "final", "ok", "open",
          "proved", "rejected", "superseded", "source theorem found", "repaired",
          "not proved", "diagnostic", "planned", "done")
CHANNELS = ("lean/generator", "lean", "generator", "control-plane", "control plane",
            "aristotle", "codex", "paper")


def split_tag(tag):
    if not tag:
        return None, None, None
    raw = " ".join(tag.split())
    low = raw.lower()
    state = next((s for s in STATES if s in low), None)
    channel = next((c for c in CHANNELS if c in low), None)
    leftover = low
    for token in filter(None, (state, channel)):
        leftover = leftover.replace(token, " ")
    leftover = " ".join(leftover.replace(",", " ").split())
    workstream = raw if not (state or channel) else (leftover or None)
    return (workstream or None), state, channel


def field(body, *labels, limit=400):
    for lab in labels:
        m = re.search(rf"^\s*[-*]?\s*{lab}\s*:?\s*(.+?)(?=\n\s*[-*]\s*\w+\s*:|\n##|\Z)",
                      body, re.S | re.M | re.I)
        if m:
            return " ".join(m.group(1).split())[:limit]
    return None


def parse(path: Path = SRC):
    text = path.read_text(errors="ignore")
    chunks = re.split(r"\n(?=## )", text)
    rows, skipped = [], 0
    seen = {}
    # Canonical spelling per workstream: the file writes both "Step33A.1-A" and
    # "step33a.1-a", which would otherwise split one workstream into two buckets.
    canon_ws = {}
    for chunk in chunks:
        first, _, body = chunk.partition("\n")
        m = HEAD.match(first) or BARE_DATE.match(first)
        if not m:
            skipped += 1
            continue
        g = m.groupdict()
        date = g["date"]
        kind = (g.get("kind") or "entry").strip().lower()
        title = " ".join((g.get("title") or "").split()) or "(untitled)"
        workstream, state, channel = split_tag(g.get("tag"))
        if workstream:
            key = workstream.lower()
            workstream = canon_ws.setdefault(key, workstream)
        base = f"{date}_{kb.slugify(title, 48)}"
        seen[base] = seen.get(base, 0) + 1
        eid = base if seen[base] == 1 else f"{base}__{seen[base]}"
        rows.append({
            "id": eid, "date": date, "kind": kind, "title": title,
            "workstream": workstream, "state": state, "channel": channel,
            "target": field(body, "Exact target", "Target"),
            "validation": field(body, "Validation", "validation", limit=300)
                          or (field(body, r"direct Lean", limit=300)),
            "artifact_sha": (re.search(r"\b([0-9a-f]{64})\b", body).group(1)
                             if re.search(r"\b([0-9a-f]{64})\b", body) else None),
            "boundary": field(body, "Boundary", "Граница"),
            "next_target": field(body, "Next target", "Next .{0,12}target", "Next"),
            "body": body.strip(), "source_file": str(SRC.relative_to(REPO)),
        })
    return rows, skipped


def migrate(conn: sqlite3.Connection, rows: list[dict[str, object]]) -> None:
    """Replace only the canonical INSIGHTS projection and rebuild its FTS view."""
    conn.execute("DELETE FROM journal_entry WHERE source_file=?", (SOURCE_FILE,))
    conn.executemany(
        f"INSERT INTO journal_entry ({','.join(COLUMNS)}) "
        f"VALUES ({','.join('?' * len(COLUMNS))})",
        [tuple(row.get(column) for column in COLUMNS) for row in rows],
    )
    conn.execute("INSERT INTO journal_fts(journal_fts) VALUES('rebuild')")
    conn.execute(
        "INSERT INTO source_ledger (source_file, expected_rows, migrated_at, note) "
        "VALUES (?,?,?,?) ON CONFLICT(source_file) DO UPDATE SET "
        "expected_rows=excluded.expected_rows, migrated_at=excluded.migrated_at, "
        "note=excluded.note",
        (SOURCE_FILE, len(rows), date.today().isoformat(), "wave 2 journal exact projection"),
    )
    conn.commit()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    rows, skipped = parse()
    kinds, states, works = {}, {}, {}
    for r in rows:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
        if r["state"]:
            states[r["state"]] = states.get(r["state"], 0) + 1
        if r["workstream"]:
            works[r["workstream"]] = works.get(r["workstream"], 0) + 1
    print(f"parsed {len(rows)} entries · {skipped} non-entry headings skipped "
          f"(navigation blocks etc.)")
    print(f"dates {min(r['date'] for r in rows)} … {max(r['date'] for r in rows)}")
    print("top kinds     :", dict(sorted(kinds.items(), key=lambda x: -x[1])[:6]))
    print("top states    :", dict(sorted(states.items(), key=lambda x: -x[1])[:6]))
    print("top workstream:", dict(sorted(works.items(), key=lambda x: -x[1])[:5]))
    filled = {c: sum(1 for r in rows if r[c]) for c in
              ("target", "boundary", "validation", "artifact_sha", "next_target")}
    print("field coverage:", filled)
    if args.dry_run:
        return 0

    conn = kb.connect()
    migrate(conn, rows)
    print("migrated into", kb.DB_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
