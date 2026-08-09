#!/usr/bin/env python3
"""One-shot migration of the kill family into knowledge.db (wave 1).

Sources (37-ish records total, all frozen after this runs):
  1. ACTIVE/pipeline/FAILURE_ATLAS.json        5  killed objects, machine ids, Lean witnesses
  2. ACTIVE/FAILED_STRATEGIES.yaml             8  failed moves, escape operators, invariants
  3. ACTIVE/graphs/ROUTE_KILL_REGISTRY.md     15  killed routes + 1 live criterion (§ below)
  4. Q3_OBSTRUCTION_ATLAS.md                   8  standing walls
  5. docs/trackB/S5_FAILURE_ATLAS.md           1  killed lift, with the scope negation

Curation notes, so a later reader knows what was judgement and what was mechanical:
  * JSON and YAML map mechanically.
  * The registry TABLE maps mechanically; its prose §"Live kill criterion under watch"
    is ONE live criterion (PO3-square.2d3) with nine labelled refinements — migrated as a
    single record with the refinements as evidence, not sliced into nine fake criteria.
  * Walls and S5 are prose: fields were extracted by hand and are inlined below verbatim
    enough to be auditable against the frozen files.
  * Four cross-file overlaps are asserted explicitly in ALIASES with a reason each.

Usage:  ./orchestrator/kb_migrate_kills.py [--dry-run]
"""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kb  # noqa: E402  — reuse connect/insert_kills/slugify

REPO = Path(__file__).resolve().parent.parent
A = REPO / "q3.lean.aristotle"

SRC_JSON = A / "ACTIVE/pipeline/FAILURE_ATLAS.json"
SRC_YAML = A / "ACTIVE/FAILED_STRATEGIES.yaml"
SRC_REG = A / "ACTIVE/graphs/ROUTE_KILL_REGISTRY.md"
SRC_WALL = REPO / "Q3_OBSTRUCTION_ATLAS.md"
SRC_S5 = REPO / "docs/trackB/S5_FAILURE_ATLAS.md"

def rel(p: Path) -> str:
    return str(p.relative_to(REPO))

# The three source vocabularies were mutually incompatible; this is the single one.
STATUS_MAP = {
    "rejected": "killed", "repaired": "repaired", "fatal_archived": "killed",
    "active": "standing", "killed": "killed", "avoided": "standing",
    "superseded": "superseded", "live": "live",
}


def track_of(text: str) -> str:
    t = text.lower()
    if "routeb" in t or "route b" in t or "muntz" in t or "müntz" in t:
        return "RouteB"
    if "track b" in t or "trackb" in t or "b2b" in t:
        return "TrackB"
    if "step33" in t or "step32" in t or "psd" in t:
        return "PSD-pd"
    if "po2" in t or "po3" in t or "h-bridge" in t or "hbridge" in t:
        return "H-bridge"
    return "unspecified"


def from_json():
    doc = json.loads(SRC_JSON.read_text())
    generated = doc.get("generated_at")
    rows, ev = [], []
    for e in doc["entries"]:
        kid = e["id"]
        rows.append({
            "id": kid, "unit_type": "object", "subject": e.get("candidate", kid),
            "status": STATUS_MAP.get(e.get("status", ""), e.get("status")),
            "reason": e.get("failure"), "replacement": e.get("replacement"),
            "stop_code": e.get("stop_code"), "track": track_of(kid + " " + str(e)),
            "recorded_at": generated, "source_file": rel(SRC_JSON),
            "scope_negation": None, "rollback_target": None, "forbidden_future_move": None,
        })
        for key, kind in (("lean_decl", "lean_decl"), ("lean_file", "lean_file"),
                          ("source_file", "md"), ("contract_sha256", "contract_sha256"),
                          ("archived_contract", "md"), ("source_lines", "source_lines"),
                          ("failure_family", "failure_family"), ("victim_index", "victim_index"),
                          ("route_status", "route_status"), ("node_type", "node_type")):
            if e.get(key):
                ev.append((kid, kind, str(e[key])))
    return rows, ev


def from_yaml():
    import yaml
    doc = yaml.safe_load(SRC_YAML.read_text())
    updated = doc.get("updated")
    rows, ev = [], []
    for e in doc["entries"]:
        kid = kb.slugify(e["name"])
        codes = (e.get("evidence") or {}).get("failure_codes") or []
        reason = " | ".join(filter(None, [
            f"SYMPTOM: {e['symptom']}" if e.get("symptom") else None,
            f"CAUSE: {e['cause']}" if e.get("cause") else None,
            f"CONTEXT: {e['context']}" if e.get("context") else None]))
        replacement = " | ".join(filter(None, [
            f"ESCAPE: {e['escape_operator']}" if e.get("escape_operator") else None,
            e.get("next_action")]))
        rows.append({
            "id": kid, "unit_type": "strategy", "subject": e.get("failed_strategy", e["name"]),
            "status": STATUS_MAP.get(e.get("status", ""), e.get("status")),
            "reason": reason, "replacement": replacement,
            "forbidden_future_move": e.get("forbidden_future_move"),
            "stop_code": codes[0] if codes else None,
            "track": track_of(str(e)), "recorded_at": updated,
            "source_file": rel(SRC_YAML), "scope_negation": None, "rollback_target": None,
        })
        ev.append((kid, "yaml_name", e["name"]))
        if e.get("escape_operator"):
            ev.append((kid, "legacy_control_action", e["escape_operator"]))
        for f in (e.get("evidence") or {}).get("files") or []:
            ev.append((kid, "md", f))
        for c in codes[1:]:
            ev.append((kid, "failure_code", c))
        # Fields with no column of their own but too valuable to drop.
        for key, kind in (("invariant_learned", "invariant_learned"),
                          ("cognitive_operator_used", "cognitive_operator"),
                          ("new_gap_name", "new_gap")):
            if e.get(key):
                ev.append((kid, kind, e[key]))
    return rows, ev


def split_md_row(line: str) -> list[str]:
    """Split a markdown table row on real cell separators only.

    Two registry rows carry LaTeX like `\\exp(k|t|\\log|t|)` inside backticks — a naive
    split on '|' turns a 5-cell row into 9 or 13 and silently drops the record.
    """
    parts, buf, in_code = [], [], False
    for ch in line.strip().strip("|"):
        if ch == "`":
            in_code = not in_code
            buf.append(ch)
        elif ch == "|" and not in_code:
            parts.append("".join(buf).strip())
            buf = []
        else:
            buf.append(ch)
    parts.append("".join(buf).strip())
    return parts


def from_registry():
    text = SRC_REG.read_text()
    rows, ev = [], []

    # --- the table: | shape | status | reason | rollback | next |
    for line in text.splitlines():
        if not line.startswith("|") or re.match(r"^\|[\s:-]+\|", line):
            continue
        cells = split_md_row(line)
        if cells[0].lower().startswith("route / theorem"):
            continue                      # header row
        if len(cells) != 5:
            print(f"  [warn] registry row with {len(cells)} cells skipped: {line[:80]}")
            continue
        subject, status_raw, reason, rollback, nxt = cells
        kid = kb.slugify(re.sub(r"`", "", subject))
        status = "live" if status_raw.strip().lower() == "live" else "killed"
        rows.append({
            "id": kid, "unit_type": "route", "subject": subject.replace("`", ""),
            "status": status, "reason": reason, "rollback_target": rollback,
            "replacement": nxt, "track": track_of(subject + " " + reason),
            "recorded_at": None, "source_file": rel(SRC_REG),
            "scope_negation": None, "forbidden_future_move": None, "stop_code": None,
        })

    # --- the prose section: ONE live criterion with nine labelled refinements.
    sec = text.split("## Live kill criterion under watch", 1)
    if len(sec) == 2:
        body = sec[1].split("## Re-entry rule", 1)[0]
        shape = re.search(r"Route / theorem shape:\s*\n\s*\n?- (.+?)\n\n", body, re.S)
        obstruction = re.search(r"Exact obstruction:\s*\n\s*\n?(.+?)\n\n[A-Z]", body, re.S)
        kid = "PO3_SQUARE_2D3_ABSOLUTE_ROW_MASS_CONTROL"
        rows.append({
            "id": kid, "unit_type": "criterion",
            "subject": " ".join(shape.group(1).split()) if shape else
                       "PO3-square.2d3 absolute-row-mass-control",
            "status": "live",
            "reason": " ".join(obstruction.group(1).split())[:1500] if obstruction else
                      "see the frozen registry section",
            "replacement": None, "rollback_target": None, "scope_negation": None,
            "forbidden_future_move": None, "stop_code": None,
            "track": "H-bridge", "recorded_at": None, "source_file": rel(SRC_REG),
        })
        # Nine labelled refinements — kept as evidence so none is lost, none is invented.
        for label in ("Sharper split", "Latest correction", "Stable-projection refinement",
                      "Bounded-separated branch", "Orientation-safe endpoint-row limit",
                      "Endpoint orientation split",
                      "Fractional right-edge Vandermonde condition",
                      "Stable adaptive shifts reconciliation"):
            m = re.search(re.escape(label) + r":\s*\n(.+?)(?=\n[A-Z][a-z].*?:\s*\n|\Z)",
                          body, re.S)
            if m:
                ev.append((kid, "refinement", f"{label}: {' '.join(m.group(1).split())[:900]}"))
    return rows, ev


# --- Prose sources: fields extracted by hand from the frozen files (auditable verbatim).

WALLS = [
    ("MATRIX_IDENTIFICATION_WALL", "Matrix-identification wall",
     "Matrices A, P, Q must be identified as analytic Weil-form matrices on the centered "
     "B-spline packet basis; numerical tables alone are not enough.",
     "Reuse the closed matrix bridge instead of rebuilding it."),
    ("COORDINATE_WALL", "Coordinate wall",
     "Proving PSD directly in raw coordinates ignores a required Gram correction.",
     "Respect the certified basis and coefficient model already wired into Step32."),
    ("BOUNDARY_LEAKAGE_WALL", "Boundary leakage wall",
     "Boundary-null claims replaced by informal endpoint arguments do not hold.",
     "Pass boundary-null claims through the established boundary-row machinery."),
    ("PRIME_SIDE_WALL", "Prime-side wall",
     "A positive table or scalar mirror is not a proof of the imported prime form.",
     "The finite prime-side matrix P must come from the analytic/dictionary/hbox route."),
    ("STEP33_SCALAR_REPLAY_SWAMP_WALL", "Step33 scalar replay swamp wall",
     "Closing Step33A.1 by manually sweeping entries or scalar summands one by one does not "
     "converge; the (0,0) direct-profile support-zero certificate is only a pilot.",
     "Compress the prime profile by packet center difference, then by a compact-support live "
     "prime-shift filter; give hbox payloads only to live terms. If truncated-power summands "
     "create cancellation-heavy obligations, add a piecewise-polynomial/segment receiver."),
    ("P0_ENCLOSURE_WALL", "P0 enclosure wall",
     "P0 hbox fields cannot be filled by weakening the theorem statement or by asserting "
     "table equality without bounds.",
     "They must be real enclosure proofs for the analytic base entries."),
    ("FINITE_CERTIFICATE_WALL", "Finite-certificate wall",
     "Fake axioms, trusted payload shortcuts and generated declarations with holes are not "
     "admissible.",
     "Finite certificates must remain proof-side objects."),
    ("FINITE_TO_GLOBAL_WALL", "Finite-to-global wall",
     "Step32 closes a finite certified block; it does not by itself claim or prove global RH.",
     "Keep the finite/global boundary explicit."),
]

S5_ID = "TRACKB_S5_ZERO_SIDE_PSD_LIFT"


def from_prose():
    rows, ev = [], []
    for kid, name, reason, forbidden in WALLS:
        rows.append({
            "id": kid, "unit_type": "wall", "subject": name, "status": "standing",
            "reason": reason, "forbidden_future_move": forbidden, "replacement": None,
            "rollback_target": None, "scope_negation": None, "stop_code": None,
            "track": "PSD-pd", "recorded_at": "2026-05-26", "source_file": rel(SRC_WALL),
        })
    rows.append({
        "id": S5_ID, "unit_type": "object", "subject": "L = Mplus * F_v as the zero-side PSD lift",
        "status": "killed",
        "reason": "S4 planted detector valid; hat(L) has large negative values; L is not PSD "
                  "eligible; S5.1 shows the negative spectral mass is broad, not local.",
        "scope_negation": "kills the current lift only; does not kill all B2b; does not reopen "
                          "B2a; does not make S3 closure false.",
        "replacement": "hat(L_proj)=max(hat(L),0) repairs Fourier-side PSD but may destroy "
                       "physical edge-control and exceed the mu-budget through projection loss; "
                       "Route B deferred as expensive, not as impossible.",
        "forbidden_future_move": "Do not record the false reason 'spectral clipping kills "
                                 "Hermitian-square'.",
        "rollback_target": None, "stop_code": None, "track": "TrackB",
        "recorded_at": "2026-06-13", "source_file": rel(SRC_S5),
    })
    for ref in ("docs/trackB/S5_NEGATIVE_MASS_LEDGER.md",
                "docs/trackB/TRACKB_PRICE_TABLE.md",
                "docs/trackB/S4_ZERO_SIDE_ELIGIBILITY.md"):
        ev.append((S5_ID, "md", ref))
    return rows, ev


# The four cross-file overlaps found by the 2026-08-05 audit. Each alias is an assertion
# that two names denote ONE incident; the note records why.
ALIASES = [
    ("STEP33_SCALAR_REPLAY_SWAMP_WALL", "manual_row_by_row_scalar_replay",
     "same prohibition on Step33A.1 recorded twice: as a wall in the obstruction atlas and as "
     "a failed strategy in FAILED_STRATEGIES.yaml; only the YAML carried the failure code"),
    ("ROUTEB_ESTAR_MUNTZ_V1_RAW_ZETA_POLE_VALUE", "PL2_RawPoleMismatchExplicitWitness",
     "one file recorded the dead object (raw zeta-Mellin pole value), the other the dead move "
     "(resubmitting a closed supplier); same PL2 incident"),
    ("ROUTEB_ESTAR_MUNTZ_V1_RAW_ZETA_POLE_VALUE", "resubmit_already_closed_supplier_to_cloud",
     "strategy-side name of the same PL2 incident"),
    ("ROUTEB_PROJECTED_DENSITY_EXACT_FEJER", "G6_S2_FIXED_MUNTZ_WINDOW_AS_CANONICAL_PSTAR",
     "two kills on the same D0 Pstar family; the object-kill file even carried the route-level "
     "field route_status=PROJECTED_SIGN_KILLED"),
    (S5_ID, "S4 product lift",
     "TRACKB_PRICE_TABLE row for the same lift"),
    (S5_ID, "B2B_S4_FATAL_NOT_PSD_ELIGIBLE_FOR_CURRENT_LIFT",
     "price-table verdict code for the same lift"),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    batches = [("FAILURE_ATLAS.json", from_json), ("FAILED_STRATEGIES.yaml", from_yaml),
               ("ROUTE_KILL_REGISTRY.md", from_registry), ("prose walls + S5", from_prose)]
    all_rows, all_ev = [], []
    for label, fn in batches:
        rows, ev = fn()
        print(f"{label:28s} {len(rows):3d} rows, {len(ev):3d} evidence")
        all_rows += rows
        all_ev += ev

    ids = [r["id"] for r in all_rows]
    dupes = {i for i in ids if ids.count(i) > 1}
    if dupes:
        sys.exit(f"duplicate ids would overwrite each other: {sorted(dupes)}")

    known = set(ids)
    aliases = []
    for kid, alias, note in ALIASES:
        if kid not in known:
            print(f"  [warn] alias target {kid} not among migrated rows — skipped")
            continue
        aliases.append((kid, alias, note))

    print(f"\ntotal {len(all_rows)} rows, {len(all_ev)} evidence, {len(aliases)} aliases")
    if args.dry_run:
        by_type = {}
        for r in all_rows:
            by_type[r["unit_type"]] = by_type.get(r["unit_type"], 0) + 1
        print("by unit_type:", by_type)
        return 0

    conn = kb.connect()
    kb.insert_kills(conn, all_rows, evidence=all_ev, aliases=aliases)
    counts = {}
    for r in all_rows:
        counts[r["source_file"]] = counts.get(r["source_file"], 0) + 1
    conn.executemany(
        "INSERT OR REPLACE INTO source_ledger (source_file, expected_rows, migrated_at, note) "
        "VALUES (?,?,?,?)",
        [(sf, n, "2026-08-05", "wave 1 kill-family migration") for sf, n in counts.items()])
    conn.commit()
    print("migrated into", kb.DB_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
