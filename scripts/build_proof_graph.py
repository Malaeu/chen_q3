#!/usr/bin/env python3
"""Build the compact root-to-axiom observability projection.

The historical name is retained for compatibility. This is deliberately not
the 3316-file import DAG (TAINT_GRAPH owns that). It answers: for each Lean
root printed by CheckAxioms, which standard/project axioms remain, where are
they declared, and what does the source sensor currently observe there?
"""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path


ROOT = (Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle").resolve()
ACTIVE_DIR = ROOT / "ACTIVE"

DEPS_JSON = ACTIVE_DIR / "graphs" / "DEPS_TREE_MAIN.json"
ALT_JSON = ACTIVE_DIR / "pipeline" / "ALTERNATIVE_PATHS.json"
TAINT_JSON = ACTIVE_DIR / "graphs" / "TAINT_GRAPH.json"
OUT_JSON = ACTIVE_DIR / "graphs" / "PROOF_GRAPH.json"
OUT_MD = ACTIVE_DIR / "graphs" / "PROOF_GRAPH.md"


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def load_json(path: Path) -> dict[str, object]:
    if not path.is_file():
        raise FileNotFoundError(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_payload(
    deps: dict[str, object],
    taint: dict[str, object],
    alternatives: dict[str, object],
    *,
    generated_at: str,
    input_hashes: dict[str, str] | None = None,
) -> dict[str, object]:
    taint_by_file = {str(node.get("id")): node for node in taint.get("nodes", [])}
    roots_in = deps.get("roots") or [{
        "id": str(deps.get("root") or "UNKNOWN_ROOT"),
        "deps": deps.get("deps", []),
    }]
    roots: list[dict[str, object]] = []
    flat_primary: list[dict[str, object]] = []
    for root_index, root in enumerate(roots_in):
        root_id = str(root.get("id") or "UNKNOWN_ROOT")
        nodes: list[dict[str, object]] = []
        for dep in root.get("deps", []):
            name = str(dep.get("name") or "")
            if not name:
                continue
            classification = str(dep.get("classification") or (
                "PROJECT_AXIOM" if dep.get("file") else "STANDARD_LEAN_AXIOM"
            ))
            source = taint_by_file.get(str(dep.get("file"))) if dep.get("file") else None
            node = {
                "id": name,
                "classification": classification,
                "mapping_status": dep.get("mapping_status", "UNKNOWN"),
                "status": classification,
                "file": dep.get("file"),
                "root_reachable": bool(
                    source and root_id in source.get("root_ids", [])
                ) if dep.get("file") else None,
                "direct_status": source.get("direct_status") if source else "NOT_APPLICABLE",
                "propagation_status": (
                    source.get("propagation_status") if source else "NOT_APPLICABLE"
                ),
                "integrity_status": (
                    source.get("integrity_status") if source else "NOT_APPLICABLE"
                ),
                "numeric_check": source.get("numeric_check") if source else "NOT_APPLICABLE",
                "risk_score": None,
                "risk_status": "NOT_APPLICABLE",
                "risk_exceeds": None,
                "is_doomed": False,
                "alternatives": alternatives.get(name, {}).get("alternatives", []),
            }
            nodes.append(node)
        project_axioms = sum(
            1 for node in nodes if node["classification"] == "PROJECT_AXIOM"
        )
        observed_problems = sum(
            1 for node in nodes
            if node["propagation_status"] not in {"NO_OBSERVED_ISSUE", "NOT_APPLICABLE"}
        )
        roots.append({
            "id": root_id,
            "status": (
                "SOURCE_SENSOR_ALERT" if observed_problems
                else "PROJECT_AXIOMS_PRESENT" if project_axioms
                else "STANDARD_AXIOMS_ONLY"
            ),
            "axiom_count": len(nodes),
            "project_axiom_count": project_axioms,
            "observed_problem_count": observed_problems,
            "nodes": nodes,
        })
        if root_index == 0:
            flat_primary = nodes

    return {
        "schema_version": "2.0",
        "sensor_kind": "ROOT_AXIOM_PROJECTION",
        "generated_at": generated_at,
        "root": roots[0]["id"] if roots else "UNKNOWN_ROOT",
        "nodes": flat_primary,
        "roots": roots,
        "inputs": input_hashes or {},
        "boundary": {
            "not_file_import_dag": True,
            "not_proof_verdict": True,
            "numeric_evidence_only": True,
        },
    }


def render_markdown(data: dict[str, object]) -> str:
    lines = [
        f"# Root Axiom Projection (auto) — {data['generated_at']}",
        "",
        "**Boundary:** compact root-to-axiom observability; not the file DAG and not proof truth.",
        "",
    ]
    for root in data["roots"]:
        lines += [
            f"## {root['id']}",
            f"- Status: `{root['status']}`",
            f"- Axioms: {root['axiom_count']} total; {root['project_axiom_count']} project",
            f"- Source-sensor problems: {root['observed_problem_count']}",
        ]
        for node in root["nodes"]:
            suffix = f" — `{node['file']}`" if node.get("file") else ""
            lines.append(
                f"  - `{node['id']}`: {node['classification']} / "
                f"{node['propagation_status']}{suffix}"
            )
            for alternative in node.get("alternatives", []):
                lines.append(
                    f"    - alternative `{alternative.get('id', 'unnamed')}`: "
                    f"{alternative.get('status', 'unknown')}"
                )
        lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--deps", default=str(DEPS_JSON))
    parser.add_argument("--taint", default=str(TAINT_JSON))
    parser.add_argument("--alternatives", default=str(ALT_JSON))
    parser.add_argument("--json", default=str(OUT_JSON))
    parser.add_argument("--out", default=str(OUT_MD))
    args = parser.parse_args()
    paths = {
        "dependency_tree": Path(args.deps),
        "taint_graph": Path(args.taint),
        "alternative_paths": Path(args.alternatives),
    }
    data = build_payload(
        load_json(paths["dependency_tree"]),
        load_json(paths["taint_graph"]),
        load_json(paths["alternative_paths"]),
        generated_at=now_utc(),
        input_hashes={name: sha256(path) for name, path in paths.items()},
    )
    out_path = Path(args.out)
    json_path = Path(args.json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(render_markdown(data), encoding="utf-8")
    json_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} and {json_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
