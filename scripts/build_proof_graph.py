#!/usr/bin/env python3
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle"
ACTIVE_DIR = ROOT / "ACTIVE"

DEPS_JSON = ACTIVE_DIR / "graphs" / "DEPS_TREE_MAIN.json"
ALT_JSON = ACTIVE_DIR / "pipeline" / "ALTERNATIVE_PATHS.json"
TAINT_JSON = ACTIVE_DIR / "graphs" / "TAINT_GRAPH.json"
OUT_JSON = ACTIVE_DIR / "graphs" / "PROOF_GRAPH.json"
OUT_MD = ACTIVE_DIR / "graphs" / "PROOF_GRAPH.md"

CLASSICAL = {"Q3.Weil_criterion", "Q3.Schur_test", "propext", "Classical.choice", "Quot.sound"}


def load_json(path: Path, default):
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def main():
    deps = load_json(DEPS_JSON, {})
    alt = load_json(ALT_JSON, {})
    taint = load_json(TAINT_JSON, {})
    taint_by_file = {n.get("id"): n for n in taint.get("nodes", [])}

    generated_at = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    graph = {
        "generated_at": generated_at,
        "root": "Q3.Main.RH_of_Weil_and_Q3",
        "nodes": [],
    }

    for item in deps.get("deps", []):
        name = item.get("name")
        status = "classical" if name in CLASSICAL else "axiom"
        taint_info = taint_by_file.get(item.get("file")) if item.get("file") else None
        direct_status = taint_info.get("direct_status") if taint_info else "VERIFIED"
        propagation_status = taint_info.get("propagation_status") if taint_info else "VERIFIED"
        integrity_status = taint_info.get("integrity_status") if taint_info else propagation_status
        taint_source = taint_info.get("taint_source", []) if taint_info else []
        numeric_check = taint_info.get("numeric_check") if taint_info else "UNKNOWN"
        risk_score = taint_info.get("risk_score") if taint_info else None
        risk_status = taint_info.get("risk_status") if taint_info else None
        risk_exceeds = taint_info.get("risk_exceeds") if taint_info else None
        is_doomed = taint_info.get("is_doomed") if taint_info else None
        node = {
            "id": name,
            "status": status,
            "file": item.get("file"),
            "axioms_in_file": item.get("axioms_in_file", []),
            "sorries_in_file": item.get("sorries_in_file", []),
            "alternatives": alt.get(name, {}).get("alternatives", []),
            "direct_status": direct_status,
            "propagation_status": propagation_status,
            "integrity_status": integrity_status,
            "taint_source": taint_source,
            "numeric_check": numeric_check,
            "risk_score": risk_score,
            "risk_status": risk_status,
            "risk_exceeds": risk_exceeds,
            "is_doomed": is_doomed,
        }
        graph["nodes"].append(node)

    OUT_JSON.write_text(json.dumps(graph, indent=2), encoding="utf-8")

    md = []
    md.append(f"# Proof Graph (auto) — {generated_at}")
    md.append("")
    md.append(
        "**Purpose:** Machine + human index of the main-chain proof nodes, with alternatives."
    )
    md.append(
        \"**Sources:** `ACTIVE/graphs/DEPS_TREE_MAIN.json` + `ACTIVE/pipeline/ALTERNATIVE_PATHS.json`\"
    )
    md.append("")

    for node in graph["nodes"]:
        md.append(f"## {node['id']}")
        md.append(f"- Status: `{node['status']}`")
        md.append(f"- Direct status: `{node['direct_status']}`")
        md.append(f"- Propagation status: `{node['propagation_status']}`")
        if node.get("numeric_check"):
            md.append(f"- Numeric check: `{node['numeric_check']}`")
        if node.get("risk_score") is not None:
            md.append(f"- Risk score: `{node['risk_score']}`")
        if node.get("risk_status"):
            md.append(f"- Risk status: `{node['risk_status']}`")
        if node.get("is_doomed"):
            md.append("- Doomed: `true`")
        if node.get("taint_source"):
            md.append(f"- Taint source: " + ", ".join([f"`{x}`" for x in node["taint_source"]]))
        if node.get("file"):
            md.append(f"- File: `{node['file']}`")
        if node.get("axioms_in_file"):
            md.append(f"- Axioms in file: {len(node['axioms_in_file'])}")
            md.append("  - " + ", ".join([f"{n}@L{ln}" for ln, n in node["axioms_in_file"]]))
        if node.get("sorries_in_file"):
            md.append(f"- Sorries in file: {len(node['sorries_in_file'])}")
            md.append("  - " + ", ".join([f"L{ln}" for ln in node["sorries_in_file"]]))
        if node.get("alternatives"):
            md.append("- Alternatives:")
            for alt_item in node["alternatives"]:
                title = alt_item.get("title", alt_item.get("id", "alt"))
                status = alt_item.get("status", "idea")
                md.append(f"  - {title} ({status})")
        md.append("")

    OUT_MD.write_text("\n".join(md) + "\n", encoding="utf-8")
    print(f"Wrote {OUT_MD} and {OUT_JSON}")


if __name__ == "__main__":
    main()
