#!/usr/bin/env python3
"""Fail-closed refresh for the complete Q3 observability sensor bundle."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

try:
    from orchestrator import observability
except ModuleNotFoundError:  # direct execution from orchestrator/
    import observability


REPO = Path(__file__).resolve().parents[1]
GRAPH_DIR = REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs"
STATE_DIR = REPO / "orchestrator" / "state"


def load_json(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def run(command: list[str]) -> None:
    proc = subprocess.run(command, cwd=REPO, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(
            f"sensor command failed ({proc.returncode}): {' '.join(command)}\n"
            f"{proc.stdout}{proc.stderr}"
        )
    if proc.stdout.strip():
        print(proc.stdout.strip())


def validate_bundle(work: Path) -> dict[str, Any]:
    deps = load_json(work / "DEPS_TREE_MAIN.json")
    sorry = load_json(work / "SORRY_FRONTIER.json")
    numeric = load_json(work / "NUMERIC_CHECKS_REPORT.json")
    taint = load_json(work / "TAINT_GRAPH.json")
    sources = load_json(work / "TAINT_SOURCES.json")
    proof = load_json(work / "PROOF_GRAPH.json")
    autopsy = load_json(work / "AUTOPSY_MAP.json")

    dependency_roots = [str(root["id"]) for root in deps.get("roots", [])]
    sorry_roots = [str(root["root_id"]) for root in sorry.get("root_closures", [])]
    taint_roots = [str(root["root_id"]) for root in taint.get("root_status", [])]
    proof_roots = [str(root["id"]) for root in proof.get("roots", [])]
    if not dependency_roots:
        raise ValueError("dependency supplier emitted no roots")
    if not (dependency_roots == sorry_roots == taint_roots == proof_roots):
        raise ValueError(
            "root identity mismatch: "
            f"deps={dependency_roots} sorry={sorry_roots} "
            f"taint={taint_roots} proof={proof_roots}"
        )

    included = int(sorry.get("scope", {}).get("included_files", -1))
    taint_nodes = len(taint.get("nodes", []))
    source_files = len(sources.get("roots_by_file", {}))
    if included < 0 or included != taint_nodes or taint_nodes != source_files:
        raise ValueError(
            f"file coverage mismatch: sorry={included} taint={taint_nodes} "
            f"taint_sources={source_files}"
        )
    if numeric.get("coverage_status") not in {"CONFIGURED", "EMPTY_CONFIG"}:
        raise ValueError(f"invalid numeric coverage: {numeric.get('coverage_status')}")
    if not numeric.get("boundary", {}).get("not_taint_input"):
        raise ValueError("numeric report lost evidence-only/not-taint boundary")
    if taint.get("semantics", {}).get("numeric_checks") != "EVIDENCE_ONLY_NOT_PROPAGATED":
        raise ValueError("taint graph attempts to promote numeric evidence")
    if not proof.get("boundary", {}).get("not_proof_verdict"):
        raise ValueError("proof projection lost non-authoritative boundary")
    if autopsy.get("authority") != "DERIVED_NONCANONICAL_OBSERVABILITY":
        raise ValueError("autopsy map lost observability boundary")
    if autopsy.get("schema") != "q3_autopsy_map.v1":
        raise ValueError("autopsy map schema mismatch")

    return {
        "roots": len(dependency_roots),
        "files": taint_nodes,
        "axiom_rows": sum(len(root.get("deps", [])) for root in deps["roots"]),
        "sorry_sites": int(sorry.get("total_sorries", 0)),
        "numeric_coverage": numeric["coverage_status"],
        "taint_sources": sum(
            1 for origins in sources["roots_by_file"].values() if origins
        ),
        "autopsy_events": len(autopsy.get("events", [])),
        "namewatch_candidates": len(autopsy.get("namewatch_candidates", [])),
    }


def atomic_publish(work: Path) -> None:
    targets = {
        "DEPS_TREE_MAIN.json": GRAPH_DIR / "DEPS_TREE_MAIN.json",
        "DEPS_TREE_MAIN.md": GRAPH_DIR / "DEPS_TREE_MAIN.md",
        "SORRY_FRONTIER.json": GRAPH_DIR / "SORRY_FRONTIER.json",
        "SORRY_FRONTIER.md": GRAPH_DIR / "SORRY_FRONTIER.md",
        "NUMERIC_CHECKS_REPORT.json": GRAPH_DIR / "NUMERIC_CHECKS_REPORT.json",
        "NUMERIC_CHECKS_REPORT.md": GRAPH_DIR / "NUMERIC_CHECKS_REPORT.md",
        "TAINT_GRAPH.json": GRAPH_DIR / "TAINT_GRAPH.json",
        "TAINT_GRAPH.md": GRAPH_DIR / "TAINT_GRAPH.md",
        "TAINT_SOURCES.json": GRAPH_DIR / "TAINT_SOURCES.json",
        "TAINT_SOURCES.md": GRAPH_DIR / "TAINT_SOURCES.md",
        "PROOF_GRAPH.json": GRAPH_DIR / "PROOF_GRAPH.json",
        "PROOF_GRAPH.md": GRAPH_DIR / "PROOF_GRAPH.md",
        "AUTOPSY_MAP.json": GRAPH_DIR / "AUTOPSY_MAP.json",
        "AUTOPSY_MAP.md": GRAPH_DIR / "AUTOPSY_MAP.md",
    }
    staged: list[tuple[Path, Path]] = []
    try:
        for name, target in targets.items():
            source = work / name
            if not source.is_file():
                raise FileNotFoundError(source)
            descriptor, temp_name = tempfile.mkstemp(
                prefix=f".{target.name}.", suffix=".pending", dir=target.parent
            )
            with os.fdopen(descriptor, "wb") as handle:
                handle.write(source.read_bytes())
                handle.flush()
                os.fsync(handle.fileno())
            pending = Path(temp_name)
            os.chmod(pending, 0o644)
            staged.append((pending, target))
        for pending, target in staged:
            os.replace(pending, target)
    finally:
        for pending, _target in staged:
            pending.unlink(missing_ok=True)


def generate_bundle(work: Path) -> dict[str, Any]:
    python = sys.executable
    run([
        python, "scripts/build_dependency_tree.py",
        "--out", str(work / "DEPS_TREE_MAIN.md"),
        "--json", str(work / "DEPS_TREE_MAIN.json"),
    ])
    run([
        python, "scripts/build_sorry_frontier.py",
        "--out", str(work / "SORRY_FRONTIER.md"),
        "--json", str(work / "SORRY_FRONTIER.json"),
    ])
    run([
        python, "scripts/numeric_sanity_check.py",
        "--out", str(work / "NUMERIC_CHECKS_REPORT.json"),
        "--md", str(work / "NUMERIC_CHECKS_REPORT.md"),
    ])
    run([
        python, "scripts/build_taint_graph.py",
        "--out", str(work / "TAINT_GRAPH.md"),
        "--json", str(work / "TAINT_GRAPH.json"),
        "--sources-out", str(work / "TAINT_SOURCES.md"),
        "--sources-json", str(work / "TAINT_SOURCES.json"),
        "--sorry", str(work / "SORRY_FRONTIER.json"),
        "--numeric", str(work / "NUMERIC_CHECKS_REPORT.json"),
    ])
    run([
        python, "scripts/build_proof_graph.py",
        "--deps", str(work / "DEPS_TREE_MAIN.json"),
        "--taint", str(work / "TAINT_GRAPH.json"),
        "--json", str(work / "PROOF_GRAPH.json"),
        "--out", str(work / "PROOF_GRAPH.md"),
    ])
    run([
        python, "scripts/build_autopsy_map.py",
        "--json", str(work / "AUTOPSY_MAP.json"),
        "--out", str(work / "AUTOPSY_MAP.md"),
    ])
    return validate_bundle(work)


def refresh(*, dry_run: bool = False) -> dict[str, Any]:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="sensor-refresh.", dir=STATE_DIR) as tmp:
        work = Path(tmp)
        result = generate_bundle(work)
        if dry_run:
            return result
        atomic_publish(work)
    observed = observability.rebuild_database()
    run([sys.executable, "orchestrator/spine.py", "--strict", "--reason", "sensor-refresh"])
    result.update({
        "stale_sources": observed["stale_sources"],
        "degraded_sources": observed["degraded_sources"],
        "snapshot": observed["snapshot"]["id"],
    })
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    refresh_parser = sub.add_parser("refresh")
    refresh_parser.add_argument("--dry-run", action="store_true")
    sub.add_parser("status")
    args = parser.parse_args()
    if args.command == "status":
        print("\n".join(observability.summary_lines()))
        return 0
    result = refresh(dry_run=args.dry_run)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
