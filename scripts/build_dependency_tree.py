#!/usr/bin/env python3
import argparse
import json
import os
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle"
Q3_DIR = ROOT / "Q3"
ACTIVE_DIR = ROOT / "ACTIVE"

AXIOM_RE = re.compile(r"^\s*axiom\s+(?P<name>[A-Za-z0-9_'.]+)")
SORRY_RE = re.compile(r"\bsorry\b")
IMPORT_RE = re.compile(r"^\s*import\s+(?P<mod>[A-Za-z0-9_.]+)")


def run_lean_check_axioms() -> list[str]:
    """Run Q3/CheckAxioms.lean and parse the axiom dependency list."""
    cmd = ["lake", "env", "lean", "Q3/CheckAxioms.lean"]
    proc = subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or proc.stdout.strip())
    # The last line has: "'Q3.Main.RH_of_Weil_and_Q3' depends on axioms: [..]"
    text = proc.stdout.strip().splitlines()
    dep_line = None
    for line in reversed(text):
        if "depends on axioms:" in line:
            dep_line = line
            break
    if dep_line is None:
        raise RuntimeError("Could not find dependency list in CheckAxioms output")
    # extract list inside brackets (may span multiple lines)
    idx = text.index(dep_line)
    tail = " ".join(text[idx:])  # flatten remaining lines
    start = tail.find("depends on axioms:")
    if start < 0:
        raise RuntimeError(f"Malformed dependency list line: {dep_line}")
    lb = tail.find("[", start)
    rb = tail.rfind("]")
    if lb < 0 or rb < 0 or rb <= lb:
        raise RuntimeError(f"Malformed dependency list line: {dep_line}")
    raw = tail[lb + 1 : rb]
    # split by commas, strip spaces/newlines
    deps = [x.strip() for x in raw.split(",") if x.strip()]
    return deps


def collect_axioms() -> dict[str, Path]:
    """Map axiom name -> file path where declared (first hit)."""
    ax_map: dict[str, Path] = {}
    for path in Q3_DIR.rglob("*.lean"):
        try:
            text = path.read_text(encoding="utf-8")
        except Exception:
            continue
        for line in text.splitlines():
            m = AXIOM_RE.match(line)
            if not m:
                continue
            name = m.group("name")
            if name not in ax_map:
                ax_map[name] = path
    return ax_map


def scan_file_for_sorries(path: Path) -> list[int]:
    """Return line numbers containing `sorry`."""
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return []
    lines = []
    for i, line in enumerate(text.splitlines(), start=1):
        if SORRY_RE.search(line):
            lines.append(i)
    return lines


def scan_file_for_axioms(path: Path) -> list[tuple[int, str]]:
    """Return (line, name) for axioms in file."""
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return []
    out = []
    for i, line in enumerate(text.splitlines(), start=1):
        m = AXIOM_RE.match(line)
        if m:
            out.append((i, m.group("name")))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(ACTIVE_DIR / "DEPS_TREE_MAIN.md"))
    ap.add_argument("--json", default=str(ACTIVE_DIR / "DEPS_TREE_MAIN.json"))
    args = ap.parse_args()

    deps = run_lean_check_axioms()
    ax_map = collect_axioms()

    data = {
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "root": "Q3.Main.RH_of_Weil_and_Q3",
        "deps": [],
    }

    md_lines = []
    md_lines.append(f"# Main Dependency Tree (auto) — {data['generated_at']}")
    md_lines.append("")
    md_lines.append(
        "**Purpose:** Full chain of *actual* axioms used by `Q3.Main.RH_of_Weil_and_Q3`, with file locations and local sub-axioms/sorries."
    )
    md_lines.append("**Source:** `lake env lean Q3/CheckAxioms.lean`")
    md_lines.append("")

    for dep in deps:
        item = {"name": dep, "file": None, "axioms_in_file": [], "sorries_in_file": []}
        # Normalize possible fully-qualified names from #print axioms
        lookup = dep
        if lookup.startswith("Q3."):
            lookup = lookup[len("Q3.") :]
        candidates = [lookup]
        if lookup.endswith("_axiom"):
            candidates.append(lookup.replace("_axiom", ""))
        if "." in lookup:
            candidates.append(lookup.split(".")[-1])
        # special mapping for legacy margin axiom (lives in BrangeCert_2046.lean)
        if lookup == "prime_cert_margin_on_Brange_axiom":
            candidates.append("prime_b_grid_val_le_margin")
        path = None
        for cand in candidates:
            if cand in ax_map:
                lookup = cand
                path = ax_map[cand]
                break
        if path is None:
            path = ax_map.get(lookup)
        if path:
            item["file"] = str(path.relative_to(ROOT))
            item["axioms_in_file"] = scan_file_for_axioms(path)
            item["sorries_in_file"] = scan_file_for_sorries(path)
        data["deps"].append(item)

        md_lines.append(f"## {dep}")
        if path:
            rel = path.relative_to(ROOT)
            md_lines.append(f"- File: `{rel}`")
            axioms_in_file = scan_file_for_axioms(path)
            sorries_in_file = scan_file_for_sorries(path)
            md_lines.append(f"- Axioms in file: {len(axioms_in_file)}")
            if axioms_in_file:
                md_lines.append(
                    "  - " + ", ".join([f"{name}@L{line}" for line, name in axioms_in_file])
                )
            md_lines.append(f"- Sorries in file: {len(sorries_in_file)}")
            if sorries_in_file:
                md_lines.append("  - " + ", ".join([f"L{ln}" for ln in sorries_in_file]))
        else:
            md_lines.append("- File: **not found** in Q3/ (maybe Mathlib)")
        md_lines.append("")

    # Write outputs
    out_path = Path(args.out)
    out_path.write_text("\n".join(md_lines) + "\n", encoding="utf-8")
    Path(args.json).write_text(json.dumps(data, indent=2), encoding="utf-8")

    print(f"Wrote {out_path} and {args.json}")


if __name__ == "__main__":
    main()
