#!/usr/bin/env python3
"""Wave 2, step 1: migrate the MOVE family into knowledge.db.

Sources (~25 records):
  docs/RH_TRICK_ATLAS.md                    11  moves imported from named external theorems
  q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md 12  field-free mechanisms (C01..C12)
  q3.lean.aristotle/TRICKS_LIBRARY.md         2  Lean-tactic flavoured tricks

THE CENTRAL DECISION: atlas and arsenal are NOT merged into shared rows.

The succession "arsenal supersedes atlas" is declared in docs/SYSTEM_SPEC_2026-08-05.md L100
but was never executed — zero cross-references in either direction, and only 2 of 23 cards
overlap thematically. Even those two extract DIFFERENT things from the same source: the atlas
transplants the theorem (construct a magic function saturating the LP bound), the arsenal
abstracts a field-free heuristic (the global functional forgot WHERE the mass lives).
Collapsing them would look like a 23→12 dedup and would in fact destroy knowledge.
So: one table, `provenance_layer` keeps them distinguishable, and their kinship is recorded
as `same_source` edges in `link` — plus one `supersedes` edge that records the DECLARED
succession as data, so nobody has to rediscover the intent from a spec line again.
"""

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kb  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
SRC_ARSENAL = REPO / "q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md"
SRC_ATLAS = REPO / "docs/RH_TRICK_ATLAS.md"
SRC_TRICKS = REPO / "q3.lean.aristotle/TRICKS_LIBRARY.md"

MOVE_COLUMNS = ("id", "name", "mechanism", "signature", "route_projection",
                "transfer_invariants", "dual_question", "failure_mode", "next_experiment",
                "status", "status_evidence", "origin_scheme", "provenance_layer",
                "source_ref", "source_file")

def normalise_status(raw: str):
    """Map free-text status prose onto one vocabulary, keeping the original as evidence.

    The sources say things like "applied pattern / hot candidate for stronger certificates",
    "parked candidate", "applied; plan B for `E5'`" — and the last arsenal card's STATUS even
    swallows the file's trailing comment block. Ordered checks, most specific first.
    """
    if not raw:
        return "untested", None
    text = " ".join(raw.split()).lower()
    verbatim = raw.strip() if len(text.split()) > 1 else None
    for needle, value in (("kill", "killed"), ("hot", "hot"), ("parked", "parked"),
                          ("applied", "applied"), ("candidate", "candidate"),
                          ("awaiting", "candidate"), ("untested", "untested")):
        if needle in text:
            return value, verbatim
    return "untested", verbatim


def rel(p: Path) -> str:
    return str(p.relative_to(REPO))


def norm(text) -> str:
    return " ".join(text.split()) if text else None


def parse_arsenal():
    text = SRC_ARSENAL.read_text()
    cards = re.split(r"\n(?=## C\d\d )", text)
    rows = []
    for chunk in cards:
        m = re.match(r"## (C\d\d)\s+(\S+)\s*(?:\[src:\s*(.+?)\])?\s*\n", chunk)
        if not m:
            continue
        cid, name, src = m.group(1), m.group(2), m.group(3)
        body = chunk[m.end():]
        # Fields are `LABEL: value`, value continues on indented lines.
        fields = {}
        for fm in re.finditer(
                r"^([A-Z_]+(?:\s*\(Прошка\))?):\s*(.*?)(?=\n[A-Z_]+(?:\s*\(Прошка\))?:|\Z)",
                body, re.S | re.M):
            fields[fm.group(1).split("(")[0].strip()] = norm(fm.group(2))
        status, status_verbatim = normalise_status(fields.get("STATUS"))
        rows.append({
            "id": cid, "name": name,
            "mechanism": fields.get("MECHANISM"), "signature": fields.get("SIGNATURE"),
            "route_projection": fields.get("ROUTE_B"),
            "transfer_invariants": fields.get("TRANSFER"),
            "dual_question": fields.get("DUAL"),
            "failure_mode": None, "next_experiment": None,
            "status": status, "status_evidence": status_verbatim,
            "origin_scheme": "corpus_chapter", "provenance_layer": "arsenal",
            "source_ref": src, "source_file": rel(SRC_ARSENAL),
        })
    return rows


def parse_atlas():
    text = SRC_ATLAS.read_text()
    cards = re.split(r"\n(?=## \d+\. )", text)
    rows = []
    for chunk in cards:
        m = re.match(r"## (\d+)\. (.+?)\n", chunk)
        if not m:
            continue
        num, heading = m.group(1), m.group(2).strip()
        body = chunk[m.end():]
        # Fields are `- Label:` followed by an indented block.
        fields = {}
        for fm in re.finditer(r"^- ([^:\n]+):\s*\n?(.*?)(?=\n- [^:\n]+:|\Z)", body, re.S | re.M):
            fields[fm.group(1).strip().lower()] = norm(fm.group(2))
        status, status_verbatim = normalise_status(fields.get("status"))
        mech = " | ".join(filter(None, [
            f"TRANSFORMED: {fields['transformed object']}" if fields.get("transformed object") else None,
            f"PRESERVED: {fields['preserved structure']}" if fields.get("preserved structure") else None]))
        route = " | ".join(filter(None, [
            fields.get("rh/q3 analogue"), fields.get("step33 or l3 use-case")]))
        rows.append({
            "id": f"ATLAS_{int(num):02d}", "name": fields.get("trick name") or heading,
            "mechanism": mech or None, "signature": fields.get("applicability signature"),
            "route_projection": route or None,
            "transfer_invariants": fields.get("dropped structure / danger"),
            "dual_question": None, "failure_mode": fields.get("failure mode"),
            "next_experiment": fields.get("concrete next experiment"),
            "status": status,
            "status_evidence": " | ".join(filter(None, [
                status_verbatim, fields.get("related local references")])) or None,
            "origin_scheme": "external_theorem", "provenance_layer": "atlas",
            "source_ref": fields.get("original theorem/problem"),
            "source_file": rel(SRC_ATLAS),
        })
    return rows


def parse_tricks():
    text = SRC_TRICKS.read_text()
    rows = []
    for i, m in enumerate(re.finditer(r"^### (#\w+): (.+?)\n(.*?)(?=\n### |\n## |\Z)",
                                      text, re.S | re.M), start=1):
        tag, title, body = m.group(1), m.group(2).strip(), m.group(3)

        def field(label):
            fm = re.search(rf"\*\*{label}:?\*\*\s*(.*?)(?=\n\*\*|\Z)", body, re.S)
            return norm(fm.group(1)) if fm else None

        rows.append({
            "id": f"TRICKLIB_{i:02d}", "name": title,
            "mechanism": field("Solution"), "signature": field("Problem"),
            "route_projection": field("Context"),
            "transfer_invariants": None, "dual_question": None,
            "failure_mode": "pitfall" if tag == "#pitfall" else None,
            "next_experiment": field("Update"),
            "status": "applied", "status_evidence": field("Files"),
            "origin_scheme": "lean_tactic", "provenance_layer": "tricks_library",
            "source_ref": tag, "source_file": rel(SRC_TRICKS),
        })
    return rows


# Kinship recorded as data, never by collapsing rows.
LINKS = [
    ("move", "C01", "move", "ATLAS_01", "same_source",
     "both come from E8 sphere packing / Cohn-Elkies LP, but extract different things: the "
     "atlas transplants the magic-function construction, the arsenal abstracts 'the global "
     "functional forgot WHERE the negative mass lives'"),
    ("move", "C02", "move", "ATLAS_02", "same_source",
     "both from CKMRV interpolation; arsenal keeps only the ideal-plus-remote-compensator shape"),
    ("move", "C10", "move", "ATLAS_07", "same_source",
     "both demand a constructed Gram/PSD object rather than a presumed sign (dual certificate)"),
    ("move", "C01", "move", "ATLAS_11", "same_source",
     "sign-uncertainty surcharge and sign-mass localization both price two-sided sign constraints"),
    ("move", "C05", "move", "ATLAS_05", "same_source",
     "margin ledger and disjoint-sum-not-product: ledgers combine by sum"),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    rows = []
    for label, fn in (("ARSENAL_CARDS_v1.md", parse_arsenal),
                      ("RH_TRICK_ATLAS.md", parse_atlas),
                      ("TRICKS_LIBRARY.md", parse_tricks)):
        got = fn()
        filled = sum(1 for r in got if r["signature"])
        print(f"{label:26s} {len(got):3d} moves  ({filled} with a signature)")
        rows += got

    ids = [r["id"] for r in rows]
    dupes = {i for i in ids if ids.count(i) > 1}
    if dupes:
        sys.exit(f"duplicate move ids: {sorted(dupes)}")

    known = set(ids)
    links = [l for l in LINKS if l[1] in known and l[3] in known]
    skipped = [l for l in LINKS if l not in links]
    for l in skipped:
        print(f"  [warn] link {l[1]} -> {l[3]} skipped (unknown id)")

    print(f"\ntotal {len(rows)} moves, {len(links)} same_source links")
    if args.dry_run:
        by_layer = {}
        for r in rows:
            by_layer[r["provenance_layer"]] = by_layer.get(r["provenance_layer"], 0) + 1
        print("by provenance_layer:", by_layer)
        missing = [r["id"] for r in rows if not r["mechanism"] and not r["signature"]]
        if missing:
            print("  [warn] no mechanism AND no signature parsed for:", missing)
        return 0

    conn = kb.connect()
    conn.executemany(
        f"INSERT OR REPLACE INTO move ({','.join(MOVE_COLUMNS)}) "
        f"VALUES ({','.join('?' * len(MOVE_COLUMNS))})",
        [tuple(r.get(c) for c in MOVE_COLUMNS) for r in rows])
    # FTS mirror (no triggers on move: the table is written only by migrators like this one).
    # An external-content FTS5 table must be cleared with its own 'delete-all' command;
    # a plain DELETE raises "database disk image is malformed" and rolls the batch back.
    conn.execute("INSERT INTO move_fts(move_fts) VALUES('delete-all')")
    conn.execute("INSERT INTO move_fts(rowid, name, mechanism, signature, route_projection, "
                 "failure_mode) SELECT rowid, name, mechanism, signature, route_projection, "
                 "failure_mode FROM move")
    conn.executemany(
        "INSERT OR REPLACE INTO link (from_type, from_id, to_type, to_id, relation, note) "
        "VALUES (?,?,?,?,?,?)", links)
    # The declared-but-never-executed succession, recorded once as data.
    conn.execute(
        "INSERT OR REPLACE INTO link (from_type, from_id, to_type, to_id, relation, note) "
        "VALUES ('move','ARSENAL_DECK','move','RH_TRICK_ATLAS','supersedes',?)",
        ("declared in docs/SYSTEM_SPEC_2026-08-05.md L100 as the live write-zone for new "
         "moves, but never executed: no card was migrated, renumbered or marked superseded, "
         "and only 2 of 23 cards overlap. Recorded so the intent is not rediscovered again.",))
    counts = {}
    for r in rows:
        counts[r["source_file"]] = counts.get(r["source_file"], 0) + 1
    conn.executemany(
        "INSERT OR REPLACE INTO source_ledger (source_file, expected_rows, migrated_at, note) "
        "VALUES (?,?,?,?)",
        [(sf, n, "2026-08-05", "wave 2 move migration") for sf, n in counts.items()])
    conn.commit()
    print("migrated into", kb.DB_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
