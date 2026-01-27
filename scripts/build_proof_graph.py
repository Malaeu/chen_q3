#!/usr/bin/env python3
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle"
ACTIVE_DIR = ROOT / "ACTIVE"

DEPS_JSON = ACTIVE_DIR / "DEPS_TREE_MAIN.json"
ALT_JSON = ACTIVE_DIR / "ALTERNATIVE_PATHS.json"
OUT_JSON = ACTIVE_DIR / "PROOF_GRAPH.json"
OUT_MD = ACTIVE_DIR / "PROOF_GRAPH.md"

CLASSICAL = {"Q3.Weil_criterion", "Q3.Schur_test", "propext", "Classical.choice", "Quot.sound"}


def load_json(path: Path, default):
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def main():
    deps = load_json(DEPS_JSON, {})
    alt = load_json(ALT_JSON, {})

    generated_at = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    graph = {
        "generated_at": generated_at,
        "root": "Q3.Main.RH_of_Weil_and_Q3",
        "nodes": [],
    }

    for item in deps.get("deps", []):
        name = item.get("name")
        status = "classical" if name in CLASSICAL else "axiom"
        node = {
            "id": name,
            "status": status,
            "file": item.get("file"),
            "axioms_in_file": item.get("axioms_in_file", []),
            "sorries_in_file": item.get("sorries_in_file", []),
            "alternatives": alt.get(name, {}).get("alternatives", []),
        }
        graph["nodes"].append(node)

    OUT_JSON.write_text(json.dumps(graph, indent=2), encoding="utf-8")

    md = []
    md.append(f"# Proof Graph (auto) — {generated_at}")
    md.append("")
    md.append(
        "**Purpose:** Machine + human index of the main-chain proof nodes, with alternatives."
    )
    md.append("**Sources:** `ACTIVE/DEPS_TREE_MAIN.json` + `ACTIVE/ALTERNATIVE_PATHS.json`")
    md.append("")

    for node in graph["nodes"]:
        md.append(f"## {node['id']}")
        md.append(f"- Status: `{node['status']}`")
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
