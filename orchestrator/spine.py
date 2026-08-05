#!/usr/bin/env python3
"""Knowledge Spine aggregator (adapter pattern, read-only over sources).

Collects every negative-knowledge / insight / strategy-memory surface of the
repo into ONE generated view: orchestrator/state/SPINE_VIEW.md.

Sources are never modified. Ownership zones stay intact: this script lives in
the conductor zone (orchestrator/) and only reads elsewhere.

Usage:
    ./orchestrator/spine.py            # write orchestrator/state/SPINE_VIEW.md
    ./orchestrator/spine.py --stdout   # print instead of writing
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import sqlite3
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
OUT = REPO / "orchestrator" / "state" / "SPINE_VIEW.md"
KNOWLEDGE_DB = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"

SOURCES = {
    "failure_atlas": REPO / "q3.lean.aristotle/ACTIVE/pipeline/FAILURE_ATLAS.json",
    "failed_strategies": REPO / "q3.lean.aristotle/ACTIVE/FAILED_STRATEGIES.yaml",
    "errors_destroyer": REPO / "q3.lean.aristotle/docs/ERRORS_DESTROYER.md",
    "s5_failure_atlas": REPO / "docs/trackB/S5_FAILURE_ATLAS.md",
    "obstruction_atlas": REPO / "Q3_OBSTRUCTION_ATLAS.md",
    "trick_atlas": REPO / "docs/RH_TRICK_ATLAS.md",
    "insights": REPO / "q3.lean.aristotle/docs/INSIGHTS.md",
    "cognitive_governor": REPO / "q3.lean.aristotle/ACTIVE/COGNITIVE_GOVERNOR.md",
    "bus_dir": REPO / "docs/routeB_bus",
}


def _git_date(path: Path) -> str:
    try:
        out = subprocess.run(
            ["git", "log", "-1", "--format=%cs", "--", str(path.relative_to(REPO))],
            cwd=REPO, capture_output=True, text=True, timeout=10,
        ).stdout.strip()
        return out or "untracked"
    except Exception:
        return "unknown"


def _freshness_table() -> list[str]:
    lines = ["| Source | Last commit |", "|---|---|"]
    for key, path in SOURCES.items():
        if key == "bus_dir":
            continue
        date = _git_date(path) if path.exists() else "MISSING"
        lines.append(f"| `{path.relative_to(REPO)}` | {date} |")
    return lines


def _kills_from_db() -> list[str]:
    """All kills from knowledge.db, grouped by unit type.

    Replaces the former `_object_kills()` (JSON) and `_strategy_kills()` (hand-rolled YAML
    regex). Those two rendered 13 of the family's 38 records; the walls of
    Q3_OBSTRUCTION_ATLAS.md and the S5 lift were imported in SOURCES but never displayed.
    """
    if not KNOWLEDGE_DB.exists():
        return ["(knowledge.db missing — run ./orchestrator/kb.py init && "
                "./orchestrator/kb_migrate_kills.py)"]
    conn = sqlite3.connect(f"file:{KNOWLEDGE_DB}?mode=ro", uri=True)
    conn.row_factory = sqlite3.Row
    lines: list[str] = []
    for (unit,) in conn.execute(
            "SELECT DISTINCT unit_type FROM kill ORDER BY unit_type"):
        rows = conn.execute(
            "SELECT id, subject, status, replacement, rollback_target, stop_code "
            "FROM kill WHERE unit_type=? ORDER BY id", (unit,)).fetchall()
        lines += [f"", f"**{unit}** ({len(rows)})", "",
                  "| id | subject | status | next / rollback |", "|---|---|---|---|"]
        for r in rows:
            nxt = r["replacement"] or r["rollback_target"] or ""
            nxt = (nxt[:87] + "...") if len(nxt) > 90 else nxt
            subj = (r["subject"] or "")[:70].replace("|", "\\|")
            lines.append(f"| {r['id']} | {subj} | {r['status']} | {nxt.replace('|', chr(92)+'|')} |")
    n = conn.execute("SELECT COUNT(*) FROM kill").fetchone()[0]
    a = conn.execute("SELECT COUNT(*) FROM kill_alias").fetchone()[0]
    conn.close()
    lines += ["", f"_{n} records, {a} cross-file aliases. Query: "
                  "`./orchestrator/kb.py search <term>`._"]
    return lines


def _bus_iteration_blocks() -> list[str]:
    """Harvest M3 strategy-memory YAML blocks from bus verdicts."""
    bus = SOURCES["bus_dir"]
    if not bus.is_dir():
        return ["(bus dir missing)"]
    rows: list[tuple[str, str, str, str]] = []
    for md in sorted(bus.glob("*.md")):
        text = md.read_text(encoding="utf-8", errors="replace")
        for m in re.finditer(r"^iteration:\n((?:[ \t]+\S.*\n?)+)", text, re.M):
            block = m.group(1)

            def field(name: str) -> str:
                fm = re.search(rf"{name}:\s*(.+)", block)
                return fm.group(1).strip() if fm else ""

            row = (md.name, field("target"), field("forbidden_future_move"),
                   field("new_gap_name"))
            if any("<" in v for v in row[1:]):  # skip prompt-template blocks
                continue
            rows.append(row)
    if not rows:
        return ["(no iteration blocks found on the bus)"]
    lines = ["| verdict file | target | forbidden_future_move | new_gap |",
             "|---|---|---|---|"]
    for f, t, fb, g in rows:
        lines.append(f"| {f} | {t} | {fb} | {g} |")
    return lines


def _process_errors() -> list[str]:
    path = SOURCES["errors_destroyer"]
    if not path.exists():
        return ["(ERRORS_DESTROYER.md missing)"]
    heads = re.findall(r"^## (Ошибка.*)$", path.read_text(encoding="utf-8"), re.M)
    return [f"- {h}" for h in heads] or ["(no recorded errors)"]


def _trick_cards() -> list[str]:
    path = SOURCES["trick_atlas"]
    if not path.exists():
        return ["(RH_TRICK_ATLAS.md missing)"]
    text = path.read_text(encoding="utf-8")
    lines = []
    for m in re.finditer(r"^##+ (\d+\..+)$", text, re.M):  # numbered cards only
        title = m.group(1).strip()
        tail = text[m.end():m.end() + 400]
        sm = re.search(r"`?Status`?\s*[:*]*\s*`?(applied|hot candidate|candidate|parked|awaiting-research)`?", tail)
        if sm:
            lines.append(f"- [{sm.group(1)}] {title}")
    return lines or ["(no cards with Status found)"]


def _recent_insights(n: int = 8) -> list[str]:
    path = SOURCES["insights"]
    if not path.exists():
        return ["(INSIGHTS.md missing)"]
    heads = []
    with path.open(encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("## ") and not line.startswith("## Навигация"):
                heads.append(line[3:].strip())
            if len(heads) >= n:
                break
    return [f"- {h}" for h in heads]


def _staleness_warnings() -> list[str]:
    warns = []
    gov = SOURCES["cognitive_governor"]
    if gov.exists():
        text = gov.read_text(encoding="utf-8")
        dm = re.search(r"date:\s*(\d{4}-\d{2}-\d{2})", text)
        if dm:
            age = (_dt.date.today() - _dt.date.fromisoformat(dm.group(1))).days
            if age > 14:
                warns.append(
                    f"- COGNITIVE_GOVERNOR.md is {age} days old "
                    f"({dm.group(1)}) and references a possibly retired front — regenerate."
                )
    fs = SOURCES["failed_strategies"]
    if fs.exists():
        um = re.search(r"updated:\s*(\d{4}-\d{2}-\d{2})", fs.read_text(encoding="utf-8"))
        if um:
            age = (_dt.date.today() - _dt.date.fromisoformat(um.group(1))).days
            if age > 14:
                warns.append(
                    f"- FAILED_STRATEGIES.yaml last updated {um.group(1)} "
                    f"({age} days) — bus iteration blocks after that date are NOT merged."
                )
    return warns or ["- none detected"]


def build() -> str:
    today = _dt.date.today().isoformat()
    parts = [
        "# SPINE VIEW — unified negative-knowledge / memory ledger",
        "",
        f"Generated: {today} by `orchestrator/spine.py`. DO NOT EDIT (regenerate instead).",
        "Adapter over existing sources; sources stay canonical, this file is a read view.",
        "",
        "## Staleness warnings",
        *_staleness_warnings(),
        "",
        "## Source freshness",
        *_freshness_table(),
        "",
        "## 1-2. Kills (knowledge.db: routes, objects, strategies, walls, criteria)",
        *_kills_from_db(),
        "",
        "## 3. Bus strategy memory (M3 iteration blocks in verdicts)",
        *_bus_iteration_blocks(),
        "",
        "## 4. Process errors (ERRORS_DESTROYER)",
        *_process_errors(),
        "",
        "## 5. Trick arsenal index (RH_TRICK_ATLAS, K9)",
        *_trick_cards(),
        "",
        "## 6. Recent insights (INSIGHTS.md head)",
        *_recent_insights(),
        "",
    ]
    return "\n".join(parts) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stdout", action="store_true")
    args = ap.parse_args()
    view = build()
    if args.stdout:
        sys.stdout.write(view)
    else:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(view, encoding="utf-8")
        print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
