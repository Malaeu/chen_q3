#!/usr/bin/env python3
import argparse
import json
from pathlib import Path
from difflib import SequenceMatcher

ROOT = Path(__file__).resolve().parents[2]
MAPS = ROOT / "external" / "maps"
INDEX = ROOT / "external" / "index.json"


def load_nodes(path):
    data = json.loads(Path(path).read_text())
    nodes = []
    for n in data.get("nodes", []):
        nodes.append({
            "id": n.get("id"),
            "title": n.get("title") or n.get("name") or "",
        })
    return nodes


def score(a, b):
    return SequenceMatcher(None, a.lower(), b.lower()).ratio()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--paper-id", required=True)
    ap.add_argument("--node-list", required=True, help="Path to dependency_graph.json")
    ap.add_argument("--paper-nodes", default=None, help="Optional JSON list of nodes from paper")
    ap.add_argument("--min-score", type=float, default=0.5)
    args = ap.parse_args()

    nodes = load_nodes(args.node_list)
    paper_nodes = []
    if args.paper_nodes:
        paper_nodes = json.loads(Path(args.paper_nodes).read_text())
    else:
        # fallback: use titles from index if available
        if INDEX.exists():
            idx = json.loads(INDEX.read_text())
            for r in idx.get("results", []):
                if r.get("id") == args.paper_id and r.get("title"):
                    paper_nodes = [{"id": r.get("id"), "title": r.get("title")}]
                    break

    matches = []
    for pn in paper_nodes:
        for n in nodes:
            s = score(pn.get("title", ""), n.get("title", ""))
            if s >= args.min_score:
                matches.append({
                    "paper_node": pn,
                    "our_node": n,
                    "score": s,
                })

    MAPS.mkdir(parents=True, exist_ok=True)
    out = MAPS / (args.paper_id.replace("/", "_") + ".json")
    out.write_text(json.dumps({
        "paper_id": args.paper_id,
        "matches": matches,
    }, indent=2, ensure_ascii=False))
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
