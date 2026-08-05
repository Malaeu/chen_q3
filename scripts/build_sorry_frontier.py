#!/usr/bin/env python3
"""Build the lightweight, root-aware Q3 sorry frontier."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

try:
    from scripts.q3_sensor_scan import dependency_closure, scan_import_graph, scan_sorry_sites
except ModuleNotFoundError:  # direct execution from scripts/
    from q3_sensor_scan import dependency_closure, scan_import_graph, scan_sorry_sites


ROOT = (Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle").resolve()
Q3_DIR = ROOT / "Q3"
ACTIVE_DIR = ROOT / "ACTIVE"

ROOT_ENTRIES = {
    "Q3.Main.RH_of_Weil_and_Q3": "Q3/Main.lean",
    "Q3.RH_of_shifted_atom_route": "Q3/Proofs/PaperMainlineAtomRoute.lean",
}


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def build_payload(q3_dir: Path = Q3_DIR, *, generated_at: str | None = None) -> dict[str, object]:
    sorry_files = scan_sorry_sites(q3_dir)
    graph, unresolved = scan_import_graph(q3_dir)
    closures: list[dict[str, object]] = []
    root_sets: dict[str, set[str]] = {}
    for root_id, entry_file in ROOT_ENTRIES.items():
        distances = dependency_closure(graph, entry_file)
        root_sets[root_id] = set(distances)
        closures.append({
            "root_id": root_id,
            "entry_file": entry_file,
            "file_count": len(distances),
            "files": [
                {"file": file_name, "depth": depth}
                for file_name, depth in sorted(distances.items())
            ],
        })

    for row in unresolved:
        row["root_ids"] = [
            root_id for root_id, members in root_sets.items() if row["file"] in members
        ]

    impacted = 0
    for item in sorry_files:
        roots = [root_id for root_id, members in root_sets.items() if item["file"] in members]
        item["root_ids"] = roots
        if roots:
            impacted += int(item["count"])

    return {
        "schema_version": "2.0",
        "sensor_kind": "LEAN_SORRY_FRONTIER",
        "generated_at": generated_at or now_utc(),
        "root": "Q3/",
        "scope": {
            "included_files": len(graph),
            "excluded_directories": ["Q3/Clean", "Q3/Archive"],
            "unresolved_internal_imports": unresolved,
        },
        "total_sorries": sum(int(item["count"]) for item in sorry_files),
        "root_impacted_sorries": impacted,
        "files": sorry_files,
        "root_closures": closures,
    }


def render_markdown(data: dict[str, object]) -> str:
    scope = data["scope"]
    lines = [
        f"# Sorry Frontier (auto) — {data['generated_at']}",
        "",
        "**Purpose:** Exact active `sorry` sites plus their membership in configured root closures.",
        "**Method:** ripgrep candidate selection, then comment/string-aware verification.",
        f"**Scope:** {scope['included_files']} Lean files; excludes `Q3/Clean` and `Q3/Archive`.",
        f"**Total active sorries:** {data['total_sorries']}",
        f"**Root-impacting sorries:** {data['root_impacted_sorries']}",
        "",
        "## Root closures",
    ]
    for closure in data["root_closures"]:
        lines.append(
            f"- `{closure['root_id']}` via `{closure['entry_file']}`: {closure['file_count']} files"
        )
    lines += ["", "## Active sites"]
    if not data["files"]:
        lines.append("_No active sorries found._")
    for item in data["files"]:
        roots = ", ".join(f"`{root}`" for root in item["root_ids"]) or "none"
        lines += [
            f"### {item['file']}",
            f"- Count: {item['count']}",
            "- Lines: " + ", ".join(f"L{line}" for line in item["lines"]),
            f"- Root impact: {roots}",
            "",
        ]
    unresolved = scope["unresolved_internal_imports"]
    lines += ["", "## Scanner diagnostics"]
    lines.append(f"- Unresolved internal imports: {len(unresolved)}")
    for row in unresolved[:20]:
        roots = ", ".join(row.get("root_ids", [])) or "none"
        lines.append(
            f"  - `{row['file']}` -> `{row['module']}`: {row['status']}; roots={roots}"
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default=str(ACTIVE_DIR / "graphs" / "SORRY_FRONTIER.md"))
    parser.add_argument("--json", default=str(ACTIVE_DIR / "graphs" / "SORRY_FRONTIER.json"))
    args = parser.parse_args()
    data = build_payload()
    blocking = [
        row for row in data["scope"]["unresolved_internal_imports"]
        if row.get("root_ids")
    ]
    if blocking:
        raise RuntimeError(
            "unresolved Q3 imports inside a live root closure: " + str(blocking[:20])
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
