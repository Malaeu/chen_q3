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
import os
import re
import sqlite3
import sys
import unicodedata
from datetime import date
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DB_PATH = Path(os.environ.get(
    "Q3_KNOWLEDGE_DB_PATH",
    str(REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"),
)).resolve()
SCHEMA = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge_schema.sql"
VIEW_OUT = REPO / "docs" / "KILLS.md"

UNIT_TYPES = ("route", "object", "strategy", "wall", "criterion")
STATUSES = ("killed", "live", "repaired", "superseded", "standing")

KILL_COLUMNS = ("id", "unit_type", "subject", "status", "reason", "scope_negation",
                "rollback_target", "replacement", "forbidden_future_move", "stop_code",
                "track", "recorded_at", "source_file")
EXPLORATION_CLOSE_STATES = ("selected", "killed", "terminal_stall")
EXPLORATION_LINK_RELATIONS = (
    "cites", "applies_move", "autopsy_of", "same_source", "supersedes",
)
LINK_TARGET_TABLES = {
    "kill": ("kill", "id"),
    "move": ("move", "id"),
    "journal_entry": ("journal_entry", "id"),
    "dossier": ("dossier", "slug"),
    "postmortem": ("postmortem", "id"),
}


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


def _parse_exploration_link(value: str) -> tuple[str, str, str, str | None]:
    parts = value.split(":", 3)
    if len(parts) < 3:
        raise ValueError("link must be TO_TYPE:TO_ID:RELATION[:NOTE]")
    to_type, to_id, relation = parts[:3]
    note = parts[3] if len(parts) == 4 else None
    if to_type not in LINK_TARGET_TABLES:
        raise ValueError(f"unsupported link target type: {to_type}")
    if relation not in EXPLORATION_LINK_RELATIONS:
        raise ValueError(f"unsupported exploration relation: {relation}")
    if not to_id:
        raise ValueError("link target id must be nonempty")
    return to_type, to_id, relation, note


def record_exploration_close(
    conn: sqlite3.Connection,
    *,
    entry_id: str,
    recorded_date: str,
    state: str,
    title: str,
    target: str,
    validation: str,
    artifact_sha: str,
    next_target: str,
    body: str,
    source_file: str,
    links: tuple[tuple[str, str, str, str | None], ...] = (),
) -> None:
    """Write one durable exploration closeout plus links in one transaction.

    This is deliberately not an event stream. It cannot overwrite a journal
    row, create kills/moves/walls, or persist speculative cycles.
    """
    if state not in EXPLORATION_CLOSE_STATES:
        raise ValueError(f"invalid exploration close state: {state}")
    if not re.fullmatch(r"[0-9a-f]{64}", artifact_sha):
        raise ValueError("artifact_sha must be a lowercase SHA-256")
    required_text = {
        "entry_id": entry_id,
        "recorded_date": recorded_date,
        "title": title,
        "target": target,
        "validation": validation,
        "next_target": next_target,
        "body": body,
        "source_file": source_file,
    }
    empty = [name for name, value in required_text.items() if not value.strip()]
    if empty:
        raise ValueError(f"empty exploration close fields: {', '.join(empty)}")

    try:
        conn.execute("BEGIN IMMEDIATE")
        for to_type, to_id, relation, _note in links:
            if to_type not in LINK_TARGET_TABLES or relation not in EXPLORATION_LINK_RELATIONS:
                raise ValueError("invalid exploration close link")
            table, key = LINK_TARGET_TABLES[to_type]
            if conn.execute(
                    f"SELECT 1 FROM {table} WHERE {key}=?", (to_id,)).fetchone() is None:
                raise ValueError(f"link target does not exist: {to_type}:{to_id}")
        cursor = conn.execute(
            "INSERT INTO journal_entry "
            "(id,date,kind,title,workstream,state,channel,target,validation,artifact_sha,"
            "boundary,next_target,body,source_file) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (
                entry_id, recorded_date, "exploration_close", title,
                "Q3 behavior control", state, "control-plane", target, validation,
                artifact_sha, "EXPERIMENTAL_NOT_PROMOTED", next_target, body, source_file,
            ),
        )
        conn.execute(
            "INSERT INTO journal_fts(rowid, title, body, target, boundary) "
            "VALUES (?,?,?,?,?)",
            (cursor.lastrowid, title, body, target, "EXPERIMENTAL_NOT_PROMOTED"),
        )
        conn.executemany(
            "INSERT INTO link (from_type,from_id,to_type,to_id,relation,note) "
            "VALUES ('journal_entry',?,?,?,?,?)",
            [(entry_id, to_type, to_id, relation, note)
             for to_type, to_id, relation, note in links],
        )
        conn.commit()
    except Exception:
        conn.rollback()
        raise


def cmd_record_exploration_close(args) -> int:
    conn: sqlite3.Connection | None = None
    try:
        links = tuple(_parse_exploration_link(value) for value in args.link)
        conn = connect()
        record_exploration_close(
            conn,
            entry_id=args.id,
            recorded_date=args.date or date.today().isoformat(),
            state=args.state,
            title=args.title,
            target=args.target,
            validation=args.validation,
            artifact_sha=args.artifact_sha,
            next_target=args.next_target,
            body=args.body,
            source_file=args.source_file,
            links=links,
        )
    except (sqlite3.Error, ValueError) as exc:
        print(f"EXPLORATION_CLOSE_ERROR: {exc}", file=sys.stderr)
        return 2
    finally:
        if conn is not None:
            conn.close()
    print(f"recorded exploration close {args.id} with {len(links)} link(s)")
    return 0


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

    # kill goes through its FTS index like every other layer.  It used to be the
    # one layer searched by LIKE '%<whole phrase>%', which meant a query whose
    # words were spread across a slug ("..._source_measure_transport") never
    # matched — the exact case this layer exists for.  Aliases and ids have no
    # FTS index, so they stay on LIKE and are merged in.
    kills, seen_kill = [], set()
    try:
        for r in conn.execute(
                "SELECT k.* FROM kill_fts f JOIN kill k ON k.rowid=f.rowid "
                "WHERE kill_fts MATCH ? ORDER BY rank LIMIT 12", (q,)):
            if r["id"] not in seen_kill:
                seen_kill.add(r["id"])
                kills.append(r)
    except sqlite3.OperationalError:
        pass
    for r in conn.execute(
            "SELECT k.* FROM kill k LEFT JOIN kill_alias a ON a.kill_id=k.id "
            "WHERE k.id LIKE ? OR a.alias LIKE ? GROUP BY k.id LIMIT 12",
            [f"%{q}%"] * 2):
        if r["id"] not in seen_kill:
            seen_kill.add(r["id"])
            kills.append(r)
    kills = kills[:12]
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


def cmd_excluded(args) -> int:
    """What was deliberately NOT migrated, and on what grounds.

    Exists so nobody repeats the archaeology: every excluded file carries the check that was
    actually run and the condition that would make it worth re-opening.
    """
    conn = connect()
    sql = "SELECT * FROM excluded_source"
    params = []
    if args.klass:
        sql += " WHERE klass=?"
        params.append(args.klass)
    sql += " ORDER BY klass, records DESC"
    rows = conn.execute(sql, params).fetchall()
    if not args.klass:
        print("classes:")
        for r in conn.execute("SELECT klass, COUNT(*), SUM(records) FROM excluded_source "
                              "GROUP BY klass ORDER BY 2 DESC"):
            print(f"  {r[0]:18s} {r[1]:4d} files  {r[2] or 0:8d} records")
        print(f"\n{len(rows)} excluded sources total. "
              f"Use --klass <name> for detail.\n")
        print("classes needing a human: " + ", ".join(
            k[0] for k in conn.execute(
                "SELECT DISTINCT klass FROM excluded_source "
                "WHERE klass IN ('unreviewed','pending_read')")))
        return 0
    for r in rows:
        print(f"  {r['path']}")
        print(f"     why      : {r['reason'][:150]}")
        print(f"     checked  : {(r['check_done'] or '')[:150]}")
        print(f"     revisit  : {(r['revisit_if'] or '')[:120]}")
    return 0


def cmd_flags(args) -> int:
    """Flags on the map: where we have already searched, with which words, at what cost.

    Migrated from the 60 oracle cards (wave 4). The point is not the answer but the record
    of the search: which terms were strong, which returned nothing, which looked right and
    led astray. Query by proof-tree address or by term.
    """
    conn = connect()
    q = " ".join(args.query) if args.query else None

    if args.vocab:
        print("VOCABULARY across all sessions\n")
        for verdict, label in (("strong", "СИЛЬНЫЕ (сработали)"),
                               ("opens_branch", "ОТКРЫВАЮТ ВЕТКУ"),
                               ("false_friend", "ЛОЖНЫЕ ДРУЗЬЯ (уводят)"),
                               ("empty", "ПУСТЫЕ (ничего не дали)")):
            rows = conn.execute(
                "SELECT term, COUNT(*) n FROM search_term WHERE verdict=? "
                "GROUP BY term ORDER BY n DESC, term LIMIT ?", (verdict, args.limit)).fetchall()
            if not rows:
                continue
            print(f"── {label} ({len(rows)} показано)")
            for r in rows:
                mark = f" ×{r['n']}" if r["n"] > 1 else ""
                print(f"     {r['term'][:104]}{mark}")
            print()
        return 0

    if not q:
        rows = conn.execute(
            "SELECT main_address, COUNT(*) n FROM search_session "
            "GROUP BY main_address ORDER BY n DESC, main_address").fetchall()
        print(f"{len(rows)} адресов с записанным поиском "
              f"(всего сессий {conn.execute('SELECT COUNT(*) FROM search_session').fetchone()[0]}):\n")
        for r in rows:
            print(f"  {r['main_address']:<44} {r['n']} сессий")
        print("\nkb.py flags <адрес|термин>   ·   kb.py flags --vocab")
        return 0

    like = f"%{q}%"
    ids = [r[0] for r in conn.execute(
        "SELECT DISTINCT s.id FROM search_session s "
        "LEFT JOIN search_address a ON a.session_id = s.id "
        "LEFT JOIN search_term t ON t.session_id = s.id "
        "WHERE s.main_address LIKE ? OR a.address LIKE ? OR t.term LIKE ? "
        "   OR s.blocker LIKE ? OR s.id LIKE ?",
        (like, like, like, like, like))]
    if not ids:
        print(f"нет записанного поиска по {q!r} — территория не хожена")
        return 1

    print(f"{len(ids)} сессий по {q!r}\n")
    for sid in ids:
        s_row = conn.execute("SELECT * FROM search_session WHERE id=?", (sid,)).fetchone()
        print(f"══ {s_row['main_address']}   [{s_row['status']}/{s_row['address_status']}]"
              f"   {s_row['date']}")
        if s_row["blocker"]:
            print(f"   блокер : {' '.join(s_row['blocker'].split())[:200]}")
        if s_row["collections"]:
            print(f"   искали в: {s_row['collections']}")
        for verdict, label in (("strong", "сильные "), ("opens_branch", "открыли "),
                               ("false_friend", "ЛОЖНЫЕ "), ("empty", "пусто   ")):
            terms = [r[0] for r in conn.execute(
                "SELECT term FROM search_term WHERE session_id=? AND verdict=?",
                (sid, verdict))]
            for t in terms:
                print(f"   {label}: {t[:110]}")
        nb = [r[0] for r in conn.execute(
            "SELECT DISTINCT address FROM search_address WHERE session_id=? AND role='neighbor'",
            (sid,))]
        if nb:
            print(f"   соседи : {', '.join(nb[:8])}")
        links = conn.execute(
            "SELECT kind, ref FROM search_link WHERE session_id=?", (sid,)).fetchall()
        for l in links:
            print(f"   {l['kind']:<7}: {l['ref']}")
        print(f"   карточка: {s_row['source_file']}")
        print()
    return 0


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

    s = sub.add_parser("excluded", help="what was NOT migrated and why")
    s.add_argument("--klass")
    s.set_defaults(fn=cmd_excluded)

    s = sub.add_parser(
        "record-exploration-close",
        help="transactionally write one validated exploration closeout and durable links",
    )
    s.add_argument("--id", required=True)
    s.add_argument("--date")
    s.add_argument("--state", required=True, choices=EXPLORATION_CLOSE_STATES)
    s.add_argument("--title", required=True)
    s.add_argument("--target", required=True, help="closed blocker id")
    s.add_argument("--validation", required=True,
                   help="validated progress-delta ids and verifiers")
    s.add_argument("--artifact-sha", required=True)
    s.add_argument("--next-target", required=True,
                   help="selected route or rollback target")
    s.add_argument("--body", required=True,
                   help="compact owner notice and operative result; no raw brainstorm")
    s.add_argument("--source-file", required=True)
    s.add_argument("--link", action="append", default=[],
                   metavar="TO_TYPE:TO_ID:RELATION[:NOTE]")
    s.set_defaults(fn=cmd_record_exploration_close)

    s = sub.add_parser(
        "flags", help="where we already searched: addresses, strong/false-friend terms")
    s.add_argument("query", nargs="*", help="адрес или термин; пусто = список адресов")
    s.add_argument("--vocab", action="store_true", help="весь накопленный словарь поиска")
    s.add_argument("--limit", type=int, default=25)
    s.set_defaults(fn=cmd_flags)

    sub.add_parser("census", help="compare frozen sources against the DB").set_defaults(
        fn=cmd_census)
    sub.add_parser("export", help="regenerate docs/KILLS.md").set_defaults(fn=cmd_export)

    args = p.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    raise SystemExit(main())
