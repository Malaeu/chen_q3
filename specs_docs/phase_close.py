#!/usr/bin/env python3
"""Unified phase close: derived repair, existing gates, blueprint, and debt."""

from __future__ import annotations

import argparse
from contextlib import closing
import json
import re
import sqlite3
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import dependency_registry  # noqa: E402
from specs_docs import session_close  # noqa: E402

CONTINUOUS_GATE_NAMES = (
    "check_arch_floor_quarantine.sh",
    "check_axioms.sh",
    "check_import_firewall.sh",
    "check_portability.sh",
    "check_root_artifacts.sh",
    "check_semantic_quarantine_history_successor.sh",
)
DEFAULT_GATES = tuple(REPO / "scripts" / name for name in CONTINUOUS_GATE_NAMES)
DEFAULT_DB = REPO / "q3.lean.aristotle/aristotle_db/knowledge.db"


def run_gates(repo: Path, gates: list[Path]) -> list[tuple[str, int]]:
    results: list[tuple[str, int]] = []
    for gate in gates:
        proc = subprocess.run(["bash", str(gate)], cwd=repo)
        results.append((str(gate), proc.returncode))
        if proc.returncode != 0:
            break
    return results


def assembly_debt(db_path: Path, *, chain: str | None = None) -> list[str]:
    if not db_path.is_file():
        return ["ASSEMBLY_DB_MISSING"]
    uri = f"file:{db_path}?mode=ro"
    try:
        with closing(sqlite3.connect(uri, uri=True)) as conn:
            if chain:
                rows = conn.execute(
                    "SELECT chain, step, status FROM assembly "
                    "WHERE status != 'READY' AND chain = ? ORDER BY chain, step",
                    (chain,),
                ).fetchall()
            else:
                rows = conn.execute(
                    "SELECT chain, step, status FROM assembly "
                    "WHERE status != 'READY' ORDER BY chain, step"
                ).fetchall()
    except sqlite3.Error as exc:
        return [f"ASSEMBLY_DB_INVALID:{exc}"]
    return [f"{chain}:{step}:{status}" for chain, step, status in rows]


def manual_debt(*, statuses: list[dependency_registry.ArtifactStatus], assembly: list[str], owned_paths: list[str], insight_receipt: str | None) -> dict[str, list[str]]:
    cards = [item.detail for item in statuses if item.artifact_id == "litreview-needs-cards" and item.status != "FRESH"]
    insight = [] if not owned_paths or insight_receipt else ["INSIGHT_REQUIRED_FOR_CHANGED_SCOPE"]
    return {"assembly_review_required": assembly, "insight_required": insight, "cards": cards}


def verdict_migration(repo: Path, *, repair: bool) -> dict[str, object]:
    command = [sys.executable, "orchestrator/kb_migrate_verdicts.py"]
    proc = subprocess.run(
        command if repair else [*command, "--dry-run"],
        cwd=repo,
        capture_output=True,
        text=True,
    )
    output = (proc.stdout + proc.stderr).strip()
    pending_text = output
    validation_exit = proc.returncode
    if repair and proc.returncode == 0:
        validation = subprocess.run(
            [*command, "--dry-run"], cwd=repo, capture_output=True, text=True
        )
        validation_exit = validation.returncode
        pending_text = (validation.stdout + validation.stderr).strip()
        output = output + "\n--- post-write dry-run ---\n" + pending_text
    pending = bool(re.search(r"(?:new strategy rows|new verdict-kill)[^\n]*:\s*[1-9]", pending_text))
    return {
        "mode": "write" if repair else "dry-run",
        "exit": validation_exit,
        "pending": pending,
        "output": output[-4000:],
    }


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
    parser.add_argument("--assembly-chain")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    repo = args.root.resolve()
    try:
        executed, statuses = session_close.repair_derived(
            repo, args.registry.resolve(), repair=args.repair, consumer="phase-close"
        )
    except Exception as exc:
        print(exc, file=sys.stderr)
        return 2
    gates = [] if args.skip_gates else [path.resolve() for path in (args.gate or DEFAULT_GATES)]
    gate_results = run_gates(repo, gates)
    gates_green = not any(code != 0 for _, code in gate_results)
    migration = {"mode": "skipped", "exit": None, "pending": False, "output": ""}
    publication_executed: list[str] = []
    publication_statuses: list[dependency_registry.ArtifactStatus] = []
    if gates_green:
        migration = verdict_migration(repo, repair=args.repair)
    if not args.skip_blueprint and gates_green and migration["exit"] == 0 and not migration["pending"]:
        publication_executed, publication_statuses = session_close.repair_derived(
            repo,
            args.registry.resolve(),
            repair=args.repair,
            consumer="phase-close-publication",
        )
    statuses.extend(publication_statuses)
    executed.extend(publication_executed)
    debt = manual_debt(
        statuses=statuses,
        assembly=assembly_debt(args.db.resolve(), chain=args.assembly_chain),
        owned_paths=args.owned_path,
        insight_receipt=args.insight_receipt,
    )
    result = {
        "schema": "q3_phase_close.v1",
        "derived_executed": executed,
        "derived_status": [{"id": item.artifact_id, "status": item.status} for item in statuses],
        "gates": [{"path": path, "exit": code} for path, code in gate_results],
        "verdict_migration": migration,
        "blueprint_exit": next(
            (0 if item.status in {"FRESH", "CURRENT_WORKTREE"} else 1
             for item in publication_statuses
             if item.artifact_id == "routeb-publication-blueprint"),
            None,
        ),
        "manual_debt": debt,
        "commit_push_performed": False,
        "PX_RH_CLAIM": "NOT_MADE",
    }
    text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.json_out:
        session_close.atomic_write(args.json_out, text)
    else:
        print(text, end="")
    derived_bad = any(item.status not in {"FRESH", "CURRENT_WORKTREE"} for item in statuses)
    gate_bad = any(code != 0 for _, code in gate_results)
    migration_bad = migration["exit"] not in {None, 0} or bool(migration["pending"])
    publication_missing = not args.skip_blueprint and gates_green and not publication_statuses
    return 1 if derived_bad or gate_bad or migration_bad or publication_missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
