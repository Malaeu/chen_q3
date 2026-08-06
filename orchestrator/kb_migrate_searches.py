#!/usr/bin/env python3
"""Wave 4: migrate the 60 oracle search cards into knowledge.db.

Why these and not the rest of the frozen contours: every other April-era folder was a
*format* we already had in better shape. These cards hold two things nothing else in the
project holds —

  1. an ADDRESS system tying a question to a node of the proof tree
     (main / ancestor / child / neighbour / normalized), and
  2. a TRAINED SEARCH VOCABULARY: 286 terms marked strong / empty / false_friend /
     opens_branch across 117 addresses.

The owner's original intent for them was "flags marking territory nobody has walked yet",
so that a non-trivial problem is never solved twice. The kill tables answer "what is dead";
these answer "where have we been, with which words, and what did it cost".

Source: q3.lean.aristotle/ACTIVE/pipeline/oracle_questions/2026_*.md (60 files, uniform
19-field YAML front matter — verified: every field present in all 60).

Usage:  ./orchestrator/kb_migrate_searches.py [--dry-run]
"""

import argparse
import re
import sys
from pathlib import Path

import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kb  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "q3.lean.aristotle/ACTIVE/pipeline/oracle_questions"

SESSION_COLS = ("id", "date", "main_address", "address_status", "status", "blocker",
                "raw_notation", "collections", "tags", "body_md", "source_file")
TERM_FIELDS = {"strong_terms": "strong", "empty_terms": "empty",
               "false_friend_terms": "false_friend", "opens_new_branch_terms": "opens_branch"}
ADDR_FIELDS = {"related_addresses": "related", "ancestor_addresses": "ancestor",
               "child_or_next_addresses": "child", "neighbor_addresses": "neighbor",
               "normalized_addresses": "normalized"}
LINK_FIELDS = {"insight_links": "insight", "request_nodes": "request_node"}


def as_list(v):
    if not v:
        return []
    return v if isinstance(v, list) else [v]


def parse_card(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    m = re.match(r"---\n(.*?)\n---\n(.*)", text, re.S)
    if not m:
        return None
    meta = yaml.safe_load(m.group(1)) or {}
    body = m.group(2).strip()
    sid = path.stem
    session = {
        "id": sid, "date": meta.get("date"), "main_address": meta.get("main_address"),
        "address_status": meta.get("address_status"), "status": meta.get("status"),
        "blocker": meta.get("blocker"),
        "raw_notation": meta.get("raw_address_notation"),
        "collections": ", ".join(as_list(meta.get("collections"))),
        "tags": ", ".join(as_list(meta.get("tags"))),
        "body_md": body, "source_file": str(path.relative_to(REPO)),
    }
    terms = [(sid, t, verdict)
             for field, verdict in TERM_FIELDS.items()
             for t in as_list(meta.get(field)) if t and t != "—"]
    addrs = [(sid, meta["main_address"], "main")] if meta.get("main_address") else []
    addrs += [(sid, a, role)
              for field, role in ADDR_FIELDS.items()
              for a in as_list(meta.get(field)) if a]
    links = [(sid, kind, r)
             for field, kind in LINK_FIELDS.items()
             for r in as_list(meta.get(field)) if r]
    return session, terms, addrs, links


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    sessions, terms, addrs, links, skipped = [], [], [], [], []
    for p in sorted(SRC.glob("2026_*.md")):
        parsed = parse_card(p)
        if not parsed:
            skipped.append(p.name)
            continue
        s, t, a, l = parsed
        sessions.append(s)
        terms += t
        addrs += a
        links += l

    verdicts = {}
    for _, _, v in terms:
        verdicts[v] = verdicts.get(v, 0) + 1
    uniq_terms = len({t for _, t, _ in terms})
    uniq_addr = len({a for _, a, _ in addrs})

    print(f"cards parsed      : {len(sessions)}   skipped: {len(skipped)}")
    print(f"terms             : {len(terms)} rows, {uniq_terms} distinct")
    for v, n in sorted(verdicts.items(), key=lambda x: -x[1]):
        print(f"    {v:14s} {n}")
    print(f"addresses         : {len(addrs)} rows, {uniq_addr} distinct nodes")
    print(f"links             : {len(links)}")
    dated = [s['date'] for s in sessions if s['date']]
    if dated:
        print(f"date range        : {min(dated)} … {max(dated)}")
    if args.dry_run:
        print("\nпримеры сильных терминов:")
        for _, t, v in terms[:6]:
            if v == "strong":
                print(f"    {t[:90]}")
        return 0

    conn = kb.connect()
    schema = (REPO / "q3.lean.aristotle/aristotle_db/search_schema.sql")
    if schema.exists():
        conn.executescript(schema.read_text(encoding="utf-8"))
    conn.executemany(
        f"INSERT OR REPLACE INTO search_session ({','.join(SESSION_COLS)}) "
        f"VALUES ({','.join('?' * len(SESSION_COLS))})",
        [tuple(s.get(c) for c in SESSION_COLS) for s in sessions])
    conn.executemany("INSERT OR REPLACE INTO search_term (session_id, term, verdict) "
                     "VALUES (?,?,?)", terms)
    conn.executemany("INSERT OR REPLACE INTO search_address (session_id, address, role) "
                     "VALUES (?,?,?)", addrs)
    conn.executemany("INSERT OR REPLACE INTO search_link (session_id, kind, ref) "
                     "VALUES (?,?,?)", links)
    conn.execute("INSERT INTO search_fts(search_fts) VALUES('delete-all')")
    conn.execute("INSERT INTO search_fts(rowid, blocker, body_md, main_address) "
                 "SELECT rowid, blocker, body_md, main_address FROM search_session")
    conn.execute(
        "INSERT OR REPLACE INTO source_ledger (source_file, expected_rows, migrated_at, note) "
        "VALUES (?,?,?,?)",
        (str(SRC.relative_to(REPO)), len(sessions), "2026-08-06",
         "wave 4: oracle search cards — address system + trained search vocabulary"))
    conn.commit()
    print("migrated into", kb.DB_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
