#!/usr/bin/env python3
import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle"
Q3_DIR = ROOT / "Q3"
ACTIVE_DIR = ROOT / "ACTIVE"

SORRY_RE = re.compile(r"\bsorry\b")


def scan_file(path: Path) -> list[int]:
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return []
    lines = []
    for i, line in enumerate(text.splitlines(), start=1):
        if SORRY_RE.search(line):
            lines.append(i)
    return lines


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(ACTIVE_DIR / "SORRY_FRONTIER.md"))
    ap.add_argument("--json", default=str(ACTIVE_DIR / "SORRY_FRONTIER.json"))
    args = ap.parse_args()

    files = []
    total = 0
    for path in sorted(Q3_DIR.rglob("*.lean")):
        rel = path.relative_to(ROOT)
        lines = scan_file(path)
        if not lines:
            continue
        total += len(lines)
        files.append({"file": str(rel), "lines": lines, "count": len(lines)})

    generated_at = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    data = {
        "generated_at": generated_at,
        "root": "Q3/",
        "total_sorries": total,
        "files": files,
    }

    md_lines = []
    md_lines.append(f"# Sorry Frontier (auto) — {generated_at}")
    md_lines.append("")
    md_lines.append("**Purpose:** List every `sorry` occurrence in `Q3/` with file + line numbers.")
    md_lines.append("**Source:** regex scan of `Q3/**/*.lean`")
    md_lines.append("")
    md_lines.append(f"**Total sorries:** {total}")
    md_lines.append("")

    if not files:
        md_lines.append("_No sorries found._")
    else:
        for item in files:
            md_lines.append(f"## {item['file']}")
            md_lines.append(f"- Count: {item['count']}")
            md_lines.append("- Lines: " + ", ".join([f"L{ln}" for ln in item["lines"]]))
            md_lines.append("")

    Path(args.out).write_text("\n".join(md_lines) + "\n", encoding="utf-8")
    Path(args.json).write_text(json.dumps(data, indent=2), encoding="utf-8")
    print(f"Wrote {args.out} and {args.json}")


if __name__ == "__main__":
    main()
