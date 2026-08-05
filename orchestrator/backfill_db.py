#!/usr/bin/env python3
"""Bulk-backfill aristotle_proofs.db with the RouteB / muntz_v3 files it never indexed.

Safety rules:
  * never touch an existing doc_id (insert_doc is INSERT OR REPLACE, so a collision would
    silently overwrite Codex's record) — collisions get a directory-qualified doc_id;
  * mark everything written here as source='backfill', because parse_lean.py hardcodes
    source='aristotle' and these files were not produced by Aristotle.
"""
import sqlite3
import sys
from pathlib import Path

ROOT = Path("/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle")
sys.path.insert(0, str(ROOT / "aristotle_db"))
import parse_lean  # noqa: E402

DB = ROOT / "aristotle_db" / "aristotle_proofs.db"
TARGETS = [
    (ROOT / "Q3/Proofs/RouteB", "ROUTE_B"),
    (ROOT / "ACTIVE/requests/routeB_lamport_rh_closure/muntz_v3/RequestProject", "MUNTZ_V3"),
]

con = sqlite3.connect(DB)
existing_paths = {r[0] for r in con.execute("select path from docs")}
existing_ids = {r[0] for r in con.execute("select doc_id from docs")}
con.close()


def already_indexed(f: Path) -> bool:
    rel = str(f.relative_to(ROOT))
    return any(rel.endswith(p) or p.endswith(rel) or f.name in p for p in existing_paths)


written, skipped, failed = [], 0, []
for root, approach in TARGETS:
    for f in sorted(root.rglob("*.lean")):
        if already_indexed(f):
            skipped += 1
            continue
        doc_id = f.stem
        if doc_id in existing_ids:
            doc_id = f"{f.stem}__{f.parent.name}"
        if doc_id in existing_ids:            # still colliding — refuse rather than overwrite
            failed.append((str(f), "doc_id collision"))
            continue
        try:
            n = parse_lean.import_lean_file(f, doc_id, approach, "HIGH", stage=None)
            existing_ids.add(doc_id)
            written.append((doc_id, n))
        except Exception as e:                # noqa: BLE001 — report, do not abort the batch
            failed.append((str(f), repr(e)[:120]))

# Honest attribution for everything this script wrote.
con = sqlite3.connect(DB)
con.executemany("update docs set source='backfill' where doc_id=?",
                [(d,) for d, _ in written])
con.commit()
docs = con.execute("select count(*) from docs").fetchone()[0]
lemmas = con.execute("select count(*) from lemmas").fetchone()[0]
con.close()

print(f"imported files : {len(written)}")
print(f"imported decls : {sum(n for _, n in written)}")
print(f"already indexed: {skipped}")
print(f"failed         : {len(failed)}")
for f, e in failed[:10]:
    print("   ", f, "->", e)
print(f"docs now       : {docs}")
print(f"lemmas now     : {lemmas}")
