#!/usr/bin/env python3
"""Unified phase close: derived repair, existing gates, blueprint, and debt."""

from __future__ import annotations

import argparse
import json
import sqlite3
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import dependency_registry  # noqa: E402
from specs_docs import session_close  # noqa: E402

DEFAULT_GATES = tuple(sorted((REPO / "scripts").glob("check_*.sh")))
DEFAULT_DB = REPO / "q3.lean.aristotle/aristotle_db/knowledge.db"


def run_gates(repo: Path, gates: list[Path]) -> list[tuple[str, int]]:
    results: list[tuple[str, int]] = []
    for gate in gates:
        proc = subprocess.run(["bash", str(gate)], cwd=repo)
        results.append((str(gate), proc.returncode))
        if proc.returncode != 0:
            break
    return results


def assembly_debt(db_path: Path) -> list[str]:
    if not db_path.is_file():
        return ["ASSEMBLY_DB_MISSING"]
    uri = f"file:{db_path}?mode=ro"
    try:
        with sqlite3.connect(uri, uri=True) as conn:
            rows = conn.execute(
                "SELECT chain, step, status FROM assembly WHERE status != 'READY' ORDER BY chain, step"
            ).fetchall()
    except sqlite3.Error as exc:
        return [f"ASSEMBLY_DB_INVALID:{exc}"]
    return [f"{chain}:{step}:{status}" for chain, step, status in rows]


def manual_debt(*, statuses: list[dependency_registry.ArtifactStatus], assembly: list[str], owned_paths: list[str], insight_receipt: str | None) -> dict[str, list[str]]:
    cards = [item.detail for item in statuses if item.artifact_id == "litreview-needs-cards" and item.status != "FRESH"]
    insight = [] if not owned_paths or insight_receipt else ["INSIGHT_REQUIRED_FOR_CHANGED_SCOPE"]
    return {"assembly_review_required": assembly, "insight_required": insight, "cards": cards}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--registry", type=Path, default=dependency_registry.DEFAULT_REGISTRY)
    parser.add_argument("--owned-path", action="append", default=[])
    parser.add_argument("--insight-receipt")
    parser.add_argument("--repair", action="store_true")
    parser.add_argument("--skip-gates", action="store_true")
    parser.add_argument("--gate", action="append", type=Path)
    parser.add_argument("--skip-blueprint", action="store_true")
    parser.add_argument("--db", type=Path, default=DEFAULT_DB)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    repo = args.root.resolve()
    try:
        executed, statuses = session_close.repair_derived(repo, args.registry.resolve(), repair=args.repair)
    except Exception as exc:
        print(exc, file=sys.stderr)
        return 2
    gates = [] if args.skip_gates else [path.resolve() for path in (args.gate or DEFAULT_GATES)]
    gate_results = run_gates(repo, gates)
    blueprint_rc: int | None = None
    if not args.skip_blueprint and (not gate_results or gate_results[-1][1] == 0):
        blueprint_rc = subprocess.run(
            [sys.executable, "docs/cartographer/blueprint_gen.py", "--check"], cwd=repo
        ).returncode
    debt = manual_debt(
        statuses=statuses,
        assembly=assembly_debt(args.db.resolve()),
        owned_paths=args.owned_path,
        insight_receipt=args.insight_receipt,
    )
    result = {
        "schema": "q3_phase_close.v1",
        "derived_executed": executed,
        "derived_status": [{"id": item.artifact_id, "status": item.status} for item in statuses],
        "gates": [{"path": path, "exit": code} for path, code in gate_results],
        "blueprint_exit": blueprint_rc,
        "manual_debt": debt,
        "commit_push_performed": False,
        "PX_RH_CLAIM": "NOT_MADE",
    }
    text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.json_out:
        session_close.atomic_write(args.json_out, text)
    else:
        print(text, end="")
    derived_bad = any(item.status != "FRESH" for item in statuses)
    gate_bad = any(code != 0 for _, code in gate_results)
    return 1 if derived_bad or gate_bad or blueprint_rc not in {None, 0} else 0


if __name__ == "__main__":
    raise SystemExit(main())
