#!/usr/bin/env python3
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MAPS = ROOT / "external" / "maps"
BREAKS = ROOT / "external" / "breakpoints"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--paper-id", required=True)
    ap.add_argument("--status", default=None, help="Optional JSON with paper node statuses")
    args = ap.parse_args()

    map_path = MAPS / (args.paper_id.replace("/", "_") + ".json")
    if not map_path.exists():
        raise SystemExit(f"Missing map: {map_path}")

    mapping = json.loads(map_path.read_text())
    statuses = {}
    if args.status:
        statuses = json.loads(Path(args.status).read_text())

    lines = [f"# Breakpoint report: {args.paper_id}", ""]
    for m in mapping.get("matches", []):
        pn = m.get("paper_node", {})
        status = statuses.get(pn.get("id"), "unknown")
        lines.append(f"- {pn.get('title','?')} -> {m['our_node']['id']} (score={m['score']:.2f}) status={status}")

    BREAKS.mkdir(parents=True, exist_ok=True)
    out = BREAKS / (args.paper_id.replace("/", "_") + ".md")
    out.write_text("\n".join(lines))
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
