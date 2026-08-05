#!/usr/bin/env python3
"""Record what was deliberately NOT migrated into knowledge.db, and on what grounds.

Owner's instruction (2026-08-05): "запомнить, чтобы потом не искать — а может там что-нибудь
путное есть". Without this table the exclusions live only in a chat message; in a month the
same 114 files get re-examined from scratch, possibly with a different conclusion.

Each row answers three questions a future reader will have:
  * why is this not in the base?
  * what was actually checked (not "it looked irrelevant")?
  * what would make it worth re-opening?

Run after a migration wave:  ./orchestrator/kb_register_excluded.py
Inspect:                     ./orchestrator/kb.py excluded [--klass step33]
"""

import csv
import re
import sqlite3
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kb  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
TODAY = "2026-08-05"

# (klass, reason, check_done, revisit_if)
RULES = [
    (re.compile(r"step33|PSD_STEP33", re.I), (
        "step33",
        "Completed PSD Step33 line — an execution log of a campaign that ended in June, not "
        "reusable knowledge.",
        "2026-08-05: grepped all 143,072 lines against every live front object — hTrial, "
        "prolate, Muntz, Galerkin, cofinal, H2a, SIMPLE_EVEN, centeredXi, kTrial, Montel: "
        "ZERO hits. The only 'Rminus' matches are rminus_mid / rminus_rad from interval "
        "arithmetic, not the Müntz tail Rminus h Λ s.",
        "A future front reuses PSD Step33 objects (entry-hbox certificates, scalar replay "
        "receivers) — then the execution log becomes relevant again.")),
    (re.compile(r"lake-manifest|/aristotle_output/|/out/|\.olean"), (
        "build_artifact",
        "Build output: Lake manifests and Aristotle run directories. Regenerable, keyed on "
        "file paths, carries no reason/rollback/replacement semantics.",
        "2026-08-05: census counted them as 'ledgers' only because JSON keys look like "
        "records; inspected — they are dependency manifests.",
        "Never — regenerate instead of reading.")),
    (re.compile(r"LAG_LEDGER|ledger_a|_CERT\b|TOOTH|\.csv$"), (
        "numeric",
        "Numeric experiment data (interval tables, tooth ledgers, certificate payloads). The "
        "conclusions drawn from them are already in journal_entry; the raw numbers are not "
        "knowledge but evidence.",
        "2026-08-05: sampled — rows are numeric payloads, no verdict fields.",
        "A certificate needs re-verification against its raw payload.")),
    (re.compile(r"PROTOKOLL|SESSION|chat_|conversations|legacy|archive|snapshot"), (
        "protocol",
        "Session protocols and chat exports. Narrative of how work happened, superseded by "
        "the journal entries and verdicts that came out of it.",
        "2026-08-05: these are per-session narratives; their durable content was already "
        "written into INSIGHTS.md and the bus at the time.",
        "Reconstructing why a decision was made when the journal entry is too terse.")),
    (re.compile(r"MANIFEST\.md|INDEX\.md|insights_index"), (
        "index",
        "Navigation indices over other files. The database replaces them: a SELECT is the "
        "index now.",
        "2026-08-05: MANIFEST.md is the goal/answer registry — its rows point at bus cards "
        "already covered by kill/journal rows.",
        "Cross-checking that no bus card was lost.")),
    (re.compile(r"MONITOR|loop_state|_STATE\.json|PHASE_MONITOR|SPINE_VIEW|TOOLS\.md|KILLS\.md"), (
        "state",
        "Regenerated state and generated views. Writing them into the base would store a "
        "snapshot of a derivative.",
        "2026-08-05: all are outputs of spine.py / tools_census.py / kb.py export.",
        "Never — regenerate.")),
    (re.compile(r"/links/|quillen_working_papers"), (
        "literature",
        "Bibliographic link dumps (Quillen working papers). Literature belongs in the "
        "litreview/Zotero contour, not in the reasoning base.",
        "2026-08-05: inspected — arrays of paper metadata, no project claims.",
        "A citation needs its provenance re-checked.")),
    (re.compile(r"Aristotle_models_training|claude_code_skills|Claude Code Skills"), (
        "external_docs",
        "Copies of external product documentation (Claude Code skills). Not project "
        "knowledge; upstream owns it and it rots here.",
        "2026-08-05: headers show a mirror of code.claude.com/docs.",
        "Never — read upstream.")),
    (re.compile(r"proshka_context|PROSHKA_CONTEXT|MEMORY_PACK|ENTRYPOINT|POLICY"), (
        "config_pack",
        "Channel configuration and context packs for Proshka, not adjudication content.",
        "2026-08-05: compared copies — ENTRYPOINT/POLICY differ only by a YAML frontmatter "
        "block; SYSTEM_PROMPT_v2 divergence was real and was fixed on 2026-08-05 (5d85dabf).",
        "A channel's behaviour changes and the prompt has to be re-audited.")),
    (re.compile(r"S5_NEGATIVE_MASS_LEDGER|TRACKB_PRICE_TABLE|S4_ZERO_SIDE_ELIGIBILITY"), (
        "already_evidence",
        "One of the four copies of the L = Mplus*F_v kill. The canonical row is "
        "TRACKB_S5_ZERO_SIDE_PSD_LIFT; this file is attached to it as evidence.",
        "2026-08-05: verified the kill is in the base with all copies as evidence refs.",
        "Never — query the kill row instead.")),
    (re.compile(r"^docs/mac_\d|_conversations|^## User"), (
        "chat_export",
        "Raw chat export. The durable content was written into INSIGHTS.md at the time.",
        "2026-08-05: file begins with repeated '## User' turns — a transcript, not a document.",
        "Reconstructing a decision whose journal entry is too terse.")),
    (re.compile(r"ROUTE_B_STATE|ROUTE_B_EXECUTION|STATE\.json|chain_status"), (
        "state",
        "Live route state, rewritten by the loop on every step. A snapshot in the base would "
        "be stale within hours.",
        "2026-08-05: routeb_status.py reads it directly; it is the current-step pointer.",
        "Never — read the live file.")),
    (re.compile(r"ACTIVE/insights\.md$"), (
        "symlink",
        "Symlink to q3.lean.aristotle/docs/INSIGHTS.md, which is already migrated (1784 "
        "journal entries).",
        "2026-08-05: `ls -la` confirms it is a symlink, not a copy.",
        "Never.")),
]


def classify(path: str):
    for rx, meta in RULES:
        if rx.search(path):
            return meta
    return None


def main() -> int:
    tsv = subprocess.run([str(REPO / "orchestrator" / "tools_census.py")],
                         capture_output=True, text=True, cwd=REPO).stdout
    rows = [r for r in csv.DictReader(tsv.splitlines(), delimiter="\t")
            if r.get("KIND") == "LEDGER"]

    conn = kb.connect()
    migrated = {r[0] for r in conn.execute("SELECT source_file FROM source_ledger")}
    pending = {r[0] for r in conn.execute(
        "SELECT source_file FROM source_ledger WHERE note LIKE 'PENDING%'")}

    out, unclassified = [], []
    for r in rows:
        p = r["PATH"]
        if p in migrated and p not in pending:
            continue
        if p in pending:
            out.append((p, "pending_read",
                        "Verdict mentions KILL/FATAL only in prose ('kill criterion', "
                        "'kill-pass', 'would kill') — no structured marker.",
                        "2026-08-05: parser found no PRIMARY:/SELECTED_RESULT:/FIELD: KILLED "
                        "form. Not migrated, so the table never asserts a claim nobody made.",
                        "A human reads it and decides what, if anything, was killed.",
                        TODAY, int(r["REFS"]) if r["REFS"].isdigit() else None))
            continue
        meta = classify(p)
        if meta:
            klass, reason, check, revisit = meta
            out.append((p, klass, reason, check, revisit, TODAY,
                        int(r["REFS"]) if r["REFS"].isdigit() else None))
        else:
            # Register even the un-reviewed remainder: the whole point of this table is that
            # nobody re-runs the archaeology. "Not looked at yet" is itself a finding.
            unclassified.append((p, r["REFS"], r["LAST"]))
            out.append((p, "unreviewed",
                        "Not yet examined — neither migrated nor ruled out.",
                        f"2026-08-05: census counted {r['REFS']} records, last touched "
                        f"{r['LAST']}. No content review performed.",
                        "Anyone with a spare hour; start with the largest and most recent.",
                        TODAY, int(r["REFS"]) if r["REFS"].isdigit() else None))

    conn.executemany(
        "INSERT OR REPLACE INTO excluded_source "
        "(path, klass, reason, check_done, revisit_if, verified_at, records) "
        "VALUES (?,?,?,?,?,?,?)", out)
    conn.commit()

    by = {}
    for row in out:
        by[row[1]] = by.get(row[1], 0) + 1
    print(f"registered {len(out)} excluded sources")
    for k, v in sorted(by.items(), key=lambda x: -x[1]):
        print(f"  {k:16s} {v:4d}")
    if unclassified:
        print(f"\nNOT classified ({len(unclassified)}) — these need a human look, "
              f"they are neither migrated nor explained:")
        for p, n, last in sorted(unclassified, key=lambda x: -int(x[1]))[:15]:
            print(f"   {n:>5} rec · {last} · {p[:74]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
