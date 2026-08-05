#!/usr/bin/env python3
"""Build source-hole/import-boundary propagation for the active Q3 tree.

Numeric checks are attached as evidence only.  They never turn a Lean file into
BROKEN/DOOMED and never establish proof truth or a route kill.
"""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from collections import defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path

try:
    from scripts.q3_sensor_scan import scan_import_graph
except ModuleNotFoundError:  # direct execution from scripts/
    from q3_sensor_scan import scan_import_graph


ROOT = (Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle").resolve()
Q3_DIR = ROOT / "Q3"
ACTIVE_DIR = ROOT / "ACTIVE"


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def load_json(path: Path) -> dict[str, object]:
    if not path.is_file():
        raise FileNotFoundError(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def _numeric_map(report: dict[str, object]) -> dict[str, str]:
    result: dict[str, str] = {}
    for check in report.get("checks", []):
        check_id = check.get("id")
        if check_id:
            result[str(check_id)] = str(check.get("status") or "UNKNOWN").upper()
    return result


def build_payloads(
    *,
    q3_dir: Path = Q3_DIR,
    sorry_data: dict[str, object],
    numeric_data: dict[str, object],
    generated_at: str | None = None,
) -> tuple[dict[str, object], dict[str, object]]:
    generated_at = generated_at or now_utc()
    graph, unresolved = scan_import_graph(q3_dir)
    sorry_by_file = {
        str(item["file"]): [int(line) for line in item.get("lines", [])]
        for item in sorry_data.get("files", []) if item.get("file")
    }
    numeric = _numeric_map(numeric_data)
    unresolved_by_file: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in unresolved:
        unresolved_by_file[row["file"]].append(row)

    reverse: dict[str, list[str]] = defaultdict(list)
    remaining: dict[str, int] = {}
    for owner, node in graph.items():
        dependencies = list(node["dependencies"])
        remaining[owner] = len(dependencies)
        for dependency in dependencies:
            reverse[dependency].append(owner)

    taint_sources: dict[str, set[str]] = {}
    status: dict[str, str] = {}
    direct_status: dict[str, str] = {}
    queue: deque[str] = deque(sorted(owner for owner, count in remaining.items() if count == 0))
    processed: set[str] = set()
    while queue:
        owner = queue.popleft()
        processed.add(owner)
        direct_holes = sorry_by_file.get(owner, [])
        boundaries = unresolved_by_file.get(owner, [])
        sources: set[str] = set()
        for dependency in graph[owner]["dependencies"]:
            sources.update(taint_sources[dependency])
        if direct_holes:
            direct_status[owner] = "SORRY"
            sources.add(owner)
        elif boundaries:
            direct_status[owner] = "IMPORT_BOUNDARY"
            sources.update(f"IMPORT::{row['module']}" for row in boundaries)
        else:
            direct_status[owner] = "CLEAR"

        if direct_holes:
            status[owner] = "DIRECT_SORRY"
        elif boundaries:
            status[owner] = "IMPORT_BOUNDARY"
        elif sources:
            status[owner] = "TRANSITIVE_TAINT"
        else:
            status[owner] = "NO_OBSERVED_ISSUE"
        taint_sources[owner] = sources
        for dependent in reverse.get(owner, []):
            remaining[dependent] -= 1
            if remaining[dependent] == 0:
                queue.append(dependent)

    cyclic = sorted(set(graph) - processed)
    for owner in cyclic:
        direct_status[owner] = "IMPORT_CYCLE"
        status[owner] = "IMPORT_CYCLE"
        taint_sources[owner] = {"IMPORT_CYCLE"}

    root_memberships: dict[str, list[str]] = defaultdict(list)
    root_status: list[dict[str, object]] = []
    for closure in sorry_data.get("root_closures", []):
        root_id = str(closure["root_id"])
        members = [str(item["file"]) for item in closure.get("files", [])]
        for member in members:
            root_memberships[member].append(root_id)
        infected = sorted({source for member in members for source in taint_sources.get(member, set())})
        tainted_files = sum(1 for member in members if taint_sources.get(member))
        root_status.append({
            "root_id": root_id,
            "entry_file": closure.get("entry_file"),
            "closure_files": len(members),
            "tainted_files": tainted_files,
            "status": "TAINTED" if infected else "NO_OBSERVED_ISSUE",
            "taint_sources": infected,
        })

    nodes: list[dict[str, object]] = []
    for owner, node in sorted(graph.items()):
        numeric_status = numeric.get(owner) or numeric.get(str(node["module"])) or "NOT_CONFIGURED"
        boundaries = unresolved_by_file.get(owner, [])
        sources = sorted(taint_sources[owner])
        nodes.append({
            "id": owner,
            "module": node["module"],
            "dependencies": node["dependencies"],
            "sorries": sorry_by_file.get(owner, []),
            "numeric_check": numeric_status,
            "direct_status": direct_status[owner],
            "propagation_status": status[owner],
            "integrity_status": status[owner],
            "taint_sources": sources,
            "taint_predecessors": [
                dependency for dependency in node["dependencies"]
                if taint_sources.get(dependency)
            ],
            "taint_origin_count": len(sources),
            "root_ids": sorted(root_memberships.get(owner, [])),
            "unresolved_imports": boundaries,
            "intrinsic_risk": None,
            "risk_score": None,
            "risk_threshold": None,
            "risk_status": "NOT_APPLICABLE",
            "risk_exceeds": None,
            "is_doomed": False,
        })

    taint = {
        "schema_version": "2.0",
        "sensor_kind": "SOURCE_HOLE_AND_IMPORT_BOUNDARY_PROPAGATION",
        "generated_at": generated_at,
        "root": "Q3/",
        "semantics": {
            "numeric_checks": "EVIDENCE_ONLY_NOT_PROPAGATED",
            "no_observed_issue": "NOT_A_PROOF_VERDICT",
            "doomed": "DISABLED",
        },
        "scope": {
            "included_files": len(graph),
            "excluded_directories": ["Q3/Clean", "Q3/Archive"],
            "unresolved_internal_imports": unresolved,
            "import_cycles": cyclic,
        },
        "root_status": root_status,
        "nodes": nodes,
    }
    sources = {
        "schema_version": "2.0",
        "sensor_kind": "TAINT_ORIGIN_PROJECTION",
        "generated_at": generated_at,
        "root_dirty": sorted(sorry_by_file),
        "boundary_dirty": sorted(
            {f"IMPORT::{row['module']}" for row in unresolved}
        ),
        "roots_by_file": {
            owner: sorted(taint_sources[owner]) for owner in sorted(taint_sources)
        },
        "root_impacts": {
            row["root_id"]: row["taint_sources"] for row in root_status
        },
    }
    return taint, sources


def render_taint_markdown(data: dict[str, object]) -> str:
    counts: dict[str, int] = defaultdict(int)
    for node in data["nodes"]:
        counts[node["propagation_status"]] += 1
    lines = [
        f"# Taint Graph (auto) — {data['generated_at']}",
        "",
        "**Boundary:** source-hole/import-boundary observability; not proof truth.",
        "**Numeric checks:** evidence only, never propagated and never DOOMED.",
        "**Counts:** " + ", ".join(f"{key}={value}" for key, value in sorted(counts.items())),
        "",
        "## Root status",
    ]
    for root in data["root_status"]:
        lines.append(
            f"- `{root['root_id']}`: `{root['status']}`; "
            f"closure={root['closure_files']}; tainted_files={root['tainted_files']}"
        )
    lines += ["", "## Direct problems"]
    direct = [
        node for node in data["nodes"]
        if node["direct_status"] != "CLEAR"
    ]
    if not direct:
        lines.append("_None._")
    for node in direct:
        lines.append(f"- `{node['id']}`: `{node['direct_status']}`")
    return "\n".join(lines) + "\n"


def render_sources_markdown(data: dict[str, object]) -> str:
    dirty = [(file_name, roots) for file_name, roots in data["roots_by_file"].items() if roots]
    lines = [
        f"# Taint Sources (auto) — {data['generated_at']}",
        "",
        "**Purpose:** Transitive origin set for every file with observed contamination.",
        f"**Direct sorry files:** {len(data['root_dirty'])}",
        f"**Import boundaries:** {len(data['boundary_dirty'])}",
        f"**Affected files:** {len(dirty)}",
        "",
    ]
    for file_name, roots in dirty[:200]:
        lines.append(f"- `{file_name}` <- " + ", ".join(f"`{root}`" for root in roots))
    return "\n".join(lines) + "\n"


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temp_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    os.close(descriptor)
    temp_path = Path(temp_name)
    try:
        temp_path.write_text(content, encoding="utf-8")
        os.chmod(temp_path, 0o644)
        os.replace(temp_path, path)
    except Exception:
        temp_path.unlink(missing_ok=True)
        raise


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default=str(ACTIVE_DIR / "graphs" / "TAINT_GRAPH.md"))
    parser.add_argument("--json", default=str(ACTIVE_DIR / "graphs" / "TAINT_GRAPH.json"))
    parser.add_argument("--sources-out", default=str(ACTIVE_DIR / "graphs" / "TAINT_SOURCES.md"))
    parser.add_argument("--sources-json", default=str(ACTIVE_DIR / "graphs" / "TAINT_SOURCES.json"))
    parser.add_argument("--sorry", default=str(ACTIVE_DIR / "graphs" / "SORRY_FRONTIER.json"))
    parser.add_argument("--numeric", default=str(ACTIVE_DIR / "graphs" / "NUMERIC_CHECKS_REPORT.json"))
    args = parser.parse_args()

    sorry_data = load_json(Path(args.sorry))
    numeric_data = load_json(Path(args.numeric))
    taint, sources = build_payloads(sorry_data=sorry_data, numeric_data=numeric_data)
    atomic_write(Path(args.out), render_taint_markdown(taint))
    atomic_write(Path(args.json), json.dumps(taint, indent=2) + "\n")
    atomic_write(Path(args.sources_out), render_sources_markdown(sources))
    atomic_write(Path(args.sources_json), json.dumps(sources, indent=2) + "\n")
    print(
        f"Wrote {args.out}, {args.json}, {args.sources_out}, and {args.sources_json}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
