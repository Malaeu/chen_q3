#!/usr/bin/env python3
"""kb — the single entry point to knowledge.db ("have we already tried / killed this?").

Written 2026-08-05 after two near-duplications in one session. The knowledge existed, in
five different files with incompatible vocabularies; nothing could be asked in one query.

    ./orchestrator/kb.py search "Mplus"           # full-text over kills, aliases included
    ./orchestrator/kb.py show <id>                # one record with evidence and aliases
    ./orchestrator/kb.py list --unit-type wall    # filtered listing
    ./orchestrator/kb.py add --unit-type route --subject "..." --reason "..." [...]
    ./orchestrator/kb.py census                   # judge: frozen files vs rows in the DB
    ./orchestrator/kb.py export                   # regenerate the markdown view

Style follows q3.lean.aristotle/aristotle_db/parse_lean.py (plain parameterized SQL), but
deliberately avoids its two defects: no hardcoded provenance value, and one commit per
transaction instead of one per row.
"""

import argparse
import re
import sqlite3
import sys
import unicodedata
from datetime import date
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DB_PATH = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"
SCHEMA = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge_schema.sql"
VIEW_OUT = REPO / "docs" / "KILLS.md"

UNIT_TYPES = ("route", "object", "strategy", "wall", "criterion")
STATUSES = ("killed", "live", "repaired", "superseded", "standing")

KILL_COLUMNS = ("id", "unit_type", "subject", "status", "reason", "scope_negation",
                "rollback_target", "replacement", "forbidden_future_move", "stop_code",
                "track", "recorded_at", "source_file")


def connect(create: bool = False) -> sqlite3.Connection:
    if not DB_PATH.exists() and not create:
        sys.exit(f"knowledge.db not found at {DB_PATH} — run `kb.py init` first")
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def cmd_init(_args) -> int:
    conn = connect(create=True)
    conn.executescript(SCHEMA.read_text())
    conn.commit()
    tables = [r[0] for r in conn.execute(
        "SELECT name FROM sqlite_master WHERE type IN ('table','view') ORDER BY name")]
    print(f"initialised {DB_PATH}")
    print("tables:", ", ".join(tables))
    return 0


def slugify(text: str, maxlen: int = 60) -> str:
    # Fold accents first: without this "Müntz" becomes "M_NTZ" and a search for MUNTZ misses it.
    folded = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode()
    s = re.sub(r"[^A-Za-z0-9]+", "_", folded).strip("_").upper()
    return s[:maxlen] or "UNNAMED"


def insert_kills(conn, rows, evidence=(), aliases=()) -> int:
    """Bulk insert. One transaction, not one per row."""
    conn.executemany(
        f"INSERT OR REPLACE INTO kill ({','.join(KILL_COLUMNS)}) "
        f"VALUES ({','.join('?' * len(KILL_COLUMNS))})",
        [tuple(r.get(c) for c in KILL_COLUMNS) for r in rows])
    if evidence:
        conn.executemany(
            "INSERT OR REPLACE INTO kill_evidence (kill_id, kind, ref) VALUES (?,?,?)",
            list(evidence))
    if aliases:
        conn.executemany(
            "INSERT OR REPLACE INTO kill_alias (kill_id, alias, note) VALUES (?,?,?)",
            list(aliases))
    conn.commit()
    return len(rows)


def cmd_add(args) -> int:
    conn = connect()
    kid = args.id or slugify(args.subject)
    row = {
        "id": kid, "unit_type": args.unit_type, "subject": args.subject,
        "status": args.status, "reason": args.reason, "scope_negation": args.scope_negation,
        "rollback_target": args.rollback_target, "replacement": args.replacement,
        "forbidden_future_move": args.forbidden, "stop_code": args.stop_code,
        "track": args.track, "recorded_at": args.date or date.today().isoformat(),
        "source_file": args.source_file or "kb.py add",
    }
    if conn.execute("SELECT 1 FROM kill WHERE id=?", (kid,)).fetchone():
        sys.exit(f"id {kid!r} already exists — pass a distinct --id rather than overwriting")
    insert_kills(conn, [row],
                 evidence=[(kid, k, v) for k, v in (e.split("=", 1) for e in args.evidence)],
                 aliases=[(kid, a, "added via kb.py") for a in args.alias])
    print(f"added {kid}")
    return 0


def _render(conn, rows, verbose=False) -> None:
    for r in rows:
        head = f"[{r['unit_type']}/{r['status']}]"
        print(f"{head:22s} {r['id']}")
        print(f"   subject : {r['subject']}")
        if r["reason"]:
            print(f"   reason  : {(r['reason'] or '')[:200]}")
        for label, key in (("rollback", "rollback_target"), ("next", "replacement"),
                           ("forbidden", "forbidden_future_move"),
                           ("scope-not", "scope_negation"), ("stop", "stop_code")):
            if r[key]:
                print(f"   {label:8s}: {r[key][:200]}")
        if verbose:
            ev = conn.execute("SELECT kind, ref FROM kill_evidence WHERE kill_id=?",
                              (r["id"],)).fetchall()
            al = conn.execute("SELECT alias, note FROM kill_alias WHERE kill_id=?",
                              (r["id"],)).fetchall()
            for e in ev:
                print(f"   evidence: {e['kind']}={e['ref']}")
            for a in al:
                print(f"   alias   : {a['alias']}  ({a['note'] or ''})")
            print(f"   source  : {r['source_file']}  {r['recorded_at'] or ''}")
        print()


def cmd_search(args) -> int:
    conn = connect()
    q = " ".join(args.terms)
    # FTS first, then alias hits, then a LIKE fallback so partial identifiers still match.
    ids, seen = [], set()
    try:
        for r in conn.execute(
                "SELECT k.id FROM kill_fts f JOIN kill k ON k.rowid=f.rowid "
                "WHERE kill_fts MATCH ? ORDER BY rank", (q,)):
            if r["id"] not in seen:
                seen.add(r["id"])
                ids.append(r["id"])
    except sqlite3.OperationalError:
        pass  # unquoted FTS syntax (e.g. a bare '=') — fall through to LIKE
    like = f"%{q}%"
    for r in conn.execute(
            "SELECT DISTINCT k.id FROM kill k LEFT JOIN kill_alias a ON a.kill_id=k.id "
            "WHERE k.subject LIKE ? OR k.reason LIKE ? OR k.id LIKE ? OR a.alias LIKE ?",
            (like, like, like, like)):
        if r["id"] not in seen:
            seen.add(r["id"])
            ids.append(r["id"])
    if not ids:
        print(f"no hits for {q!r}")
        return 1
    rows = conn.execute(
        f"SELECT * FROM kill WHERE id IN ({','.join('?' * len(ids))})", ids).fetchall()
    order = {k: i for i, k in enumerate(ids)}
    rows.sort(key=lambda r: order[r["id"]])
    print(f"{len(rows)} hit(s) for {q!r}\n")
    _render(conn, rows, verbose=True)
    return 0


def _search_table(conn, table, fts, cols, q, label):
    """Search one wave-2 table via its FTS index, with a LIKE fallback."""
    out, seen = [], set()
    try:
        for r in conn.execute(
                f"SELECT t.* FROM {fts} f JOIN {table} t ON t.rowid=f.rowid "
                f"WHERE {fts} MATCH ? ORDER BY rank LIMIT 12", (q,)):
            key = r[0]
            if key not in seen:
                seen.add(key)
                out.append(r)
    except sqlite3.OperationalError:
        pass
    if not out:
        like = f"%{q}%"
        where = " OR ".join(f"{c} LIKE ?" for c in cols)
        out = conn.execute(f"SELECT * FROM {table} WHERE {where} LIMIT 12",
                           [like] * len(cols)).fetchall()
    return out


def cmd_search_all(args) -> int:
    """Search every layer of knowledge at once: kills, moves, journal, dossiers."""
    conn = connect()
    q = " ".join(args.terms)
    total = 0

    kills = conn.execute(
        "SELECT k.* FROM kill k LEFT JOIN kill_alias a ON a.kill_id=k.id "
        "WHERE k.subject LIKE ? OR k.reason LIKE ? OR k.id LIKE ? OR a.alias LIKE ? "
        "GROUP BY k.id LIMIT 12", [f"%{q}%"] * 4).fetchall()
    if kills:
        print(f"── KILLS ({len(kills)}) " + "─" * 40)
        for r in kills:
            print(f"  [{r['unit_type']}/{r['status']}] {r['id']}\n      {r['subject'][:100]}")
        total += len(kills)

    moves = _search_table(conn, "move", "move_fts",
                          ("name", "mechanism", "signature", "route_projection"), q, "MOVES")
    if moves:
        print(f"\n── MOVES ({len(moves)}) " + "─" * 40)
        for r in moves:
            print(f"  [{r['provenance_layer']}/{r['status']}] {r['id']}  {r['name'][:70]}")
            if r["signature"]:
                print(f"      when: {r['signature'][:110]}")
        total += len(moves)

    js = _search_table(conn, "journal_entry", "journal_fts",
                       ("title", "target", "boundary"), q, "JOURNAL")
    if js:
        print(f"\n── JOURNAL ({len(js)}) " + "─" * 38)
        for r in js:
            ws = f" [{r['workstream']}]" if r["workstream"] else ""
            print(f"  {r['date']} {r['kind']}{ws}  {r['title'][:80]}")
            if r["boundary"]:
                print(f"      boundary: {r['boundary'][:100]}")
        total += len(js)

    ds = _search_table(conn, "dossier", "dossier_fts",
                       ("title", "status_token", "verdict"), q, "DOSSIERS")
    if ds:
        print(f"\n── DOSSIERS ({len(ds)}) " + "─" * 37)
        for r in ds:
            print(f"  [{r['subtype']}] {r['slug'][:70]}")
            if r["status_token"]:
                print(f"      status: {r['status_token'][:100]}")
        total += len(ds)

    if not total:
        print(f"no hits for {q!r} in any layer")
        return 1
    print(f"\n{total} hit(s) across layers for {q!r}")
    return 0


def cmd_show(args) -> int:
    conn = connect()
    rows = conn.execute("SELECT * FROM kill WHERE id=?", (args.id,)).fetchall()
    if not rows:
        sys.exit(f"no record {args.id!r}")
    _render(conn, rows, verbose=True)
    return 0


def cmd_list(args) -> int:
    conn = connect()
    sql, params = "SELECT * FROM kill", []
    where = []
    if args.unit_type:
        where.append("unit_type=?")
        params.append(args.unit_type)
    if args.status:
        where.append("status=?")
        params.append(args.status)
    if args.track:
        where.append("track=?")
        params.append(args.track)
    if where:
        sql += " WHERE " + " AND ".join(where)
    sql += " ORDER BY unit_type, id"
    rows = conn.execute(sql, params).fetchall()
    print(f"{len(rows)} record(s)\n")
    _render(conn, rows, verbose=args.verbose)
    return 0


def cmd_census(args) -> int:
    """Judge of the organ: do the frozen files still agree with the DB?

    A database without a judge drifts — aristotle_proofs.db silently fell to 31% coverage
    exactly because nothing compared expected against actual.
    """
    conn = connect()
    print(f"{'source file':62s} {'expected':>9s} {'in db':>7s}  verdict")
    print("-" * 96)
    bad = 0
    for r in conn.execute("SELECT * FROM source_ledger ORDER BY source_file"):
        # A source may have landed in any layer — count them all, or the judge cries drift
        # over a perfectly migrated file just because it was not a kill.
        actual = sum(
            conn.execute(f"SELECT COUNT(*) FROM {t} WHERE source_file=?",
                         (r["source_file"],)).fetchone()[0]
            for t in ("kill", "move", "journal_entry", "dossier", "postmortem"))
        ok = actual == r["expected_rows"]
        bad += 0 if ok else 1
        print(f"{r['source_file'][:62]:62s} {r['expected_rows']:9d} {actual:7d}  "
              f"{'OK' if ok else 'DRIFT'}")
    print()
    for t in ("kill", "move", "journal_entry", "dossier", "postmortem", "link"):
        print(f"  {t:15s} {conn.execute(f'SELECT COUNT(*) FROM {t}').fetchone()[0]:6d}")
    print()
    total = conn.execute("SELECT COUNT(*) FROM kill").fetchone()[0]
    aliases = conn.execute("SELECT COUNT(*) FROM kill_alias").fetchone()[0]
    ev = conn.execute("SELECT COUNT(*) FROM kill_evidence").fetchone()[0]
    print("-" * 96)
    print(f"rows {total} · aliases {aliases} · evidence {ev} · drifting sources {bad}")
    return 1 if bad else 0


def cmd_export(_args) -> int:
    conn = connect()
    out = ["# KILLS.md — generated view of knowledge.db\n",
           "> **GENERATED FILE — do not edit by hand.** Regenerate with "
           "`./orchestrator/kb.py export`.\n",
           "> New entries go through `./orchestrator/kb.py add`, never by editing this file "
           "or the frozen source atlases.\n"]
    for unit in UNIT_TYPES:
        rows = conn.execute(
            "SELECT * FROM kill WHERE unit_type=? ORDER BY id", (unit,)).fetchall()
        if not rows:
            continue
        out.append(f"\n## {unit} ({len(rows)})\n")
        out.append("| id | subject | status | reason | rollback | next |")
        out.append("|---|---|---|---|---|---|")
        for r in rows:
            cells = [r["id"], r["subject"], r["status"], r["reason"] or "",
                     r["rollback_target"] or "", r["replacement"] or ""]
            cells = [str(c).replace("|", "\\|").replace("\n", " ")[:300] for c in cells]
            out.append("| " + " | ".join(cells) + " |")
    VIEW_OUT.write_text("\n".join(out) + "\n")
    print(f"wrote {VIEW_OUT}")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = p.add_subparsers(dest="cmd", required=True)

    sub.add_parser("init", help="create knowledge.db from the schema").set_defaults(fn=cmd_init)

    s = sub.add_parser("search", help="full-text search over kills and aliases")
    s.add_argument("terms", nargs="+")
    s.set_defaults(fn=cmd_search)

    s = sub.add_parser("ask", help="search ALL layers: kills, moves, journal, dossiers")
    s.add_argument("terms", nargs="+")
    s.set_defaults(fn=cmd_search_all)

    s = sub.add_parser("show", help="one record in full")
    s.add_argument("id")
    s.set_defaults(fn=cmd_show)

    s = sub.add_parser("list", help="filtered listing")
    s.add_argument("--unit-type", choices=UNIT_TYPES)
    s.add_argument("--status", choices=STATUSES)
    s.add_argument("--track")
    s.add_argument("-v", "--verbose", action="store_true")
    s.set_defaults(fn=cmd_list)

    s = sub.add_parser("add", help="record a new kill")
    s.add_argument("--id")
    s.add_argument("--unit-type", required=True, choices=UNIT_TYPES)
    s.add_argument("--subject", required=True)
    s.add_argument("--status", default="killed", choices=STATUSES)
    s.add_argument("--reason", required=True)
    s.add_argument("--scope-negation")
    s.add_argument("--rollback-target")
    s.add_argument("--replacement")
    s.add_argument("--forbidden", help="forbidden future move")
    s.add_argument("--stop-code")
    s.add_argument("--track")
    s.add_argument("--date")
    s.add_argument("--source-file")
    s.add_argument("--evidence", action="append", default=[], metavar="KIND=REF")
    s.add_argument("--alias", action="append", default=[])
    s.set_defaults(fn=cmd_add)

    sub.add_parser("census", help="compare frozen sources against the DB").set_defaults(
        fn=cmd_census)
    sub.add_parser("export", help="regenerate docs/KILLS.md").set_defaults(fn=cmd_export)

    args = p.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    raise SystemExit(main())
