#!/usr/bin/env python3
import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def run(cmd):
    subprocess.check_call(cmd)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--query", action="append", default=[], help="Search query")
    ap.add_argument("--paper-id", default=None, help="Paper id for ingest/map/breakpoint")
    ap.add_argument("--pdf", default=None, help="PDF url for ingest")
    ap.add_argument("--node-list", default=None, help="dependency_graph.json")
    ap.add_argument("--min-score", type=float, default=0.5)
    ap.add_argument("--max", type=int, default=5)
    args = ap.parse_args()

    if args.query:
        for q in args.query:
            run(["python3", str(ROOT / "scripts" / "proof_compiler" / "search_external.py"), "--query", q, "--max", str(args.max)])

    if args.paper_id and args.pdf:
        run([
            "python3", str(ROOT / "scripts" / "proof_compiler" / "ingest_paper.py"),
            "--id", args.paper_id,
            "--pdf", args.pdf,
            "--source", "manual",
        ])

    if args.paper_id and args.node_list:
        run([
            "python3", str(ROOT / "scripts" / "proof_compiler" / "map_paper_nodes.py"),
            "--paper-id", args.paper_id,
            "--node-list", args.node_list,
            "--min-score", str(args.min_score),
        ])
        run([
            "python3", str(ROOT / "scripts" / "proof_compiler" / "breakpoint_report.py"),
            "--paper-id", args.paper_id,
        ])


if __name__ == "__main__":
    main()
