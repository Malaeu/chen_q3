#!/usr/bin/env python3
"""Refresh Aristotle DB + status docs for core A3_FLOOR/Q3 files.

Usage:
  source .venv/bin/activate
  python full/q3.lean.aristotle/scripts/refresh_status.py [--check] [--only DOC_ID ...]

Notes:
- This script only manages the files listed in IMPORTS below.
- Add new items to IMPORTS when new core files appear.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DB_SCRIPT = ROOT / "aristotle_db" / "parse_lean.py"
STATUS_SCRIPT = ROOT / "scripts" / "update_status.py"

IMPORTS = [
    # (relative_path, doc_id, approach, priority)
    ("A3_FLOOR_v16_deriv_digamma_eq_trigamma.lean", "A3_FLOOR_v16", "NEW_KERNEL", "HIGH"),
    ("A3_FLOOR_v19_monotonicity.lean", "A3_FLOOR_v19", "NEW_KERNEL", "HIGH"),
    ("A3_FLOOR_v20_bounds_core.lean", "A3_FLOOR_v20_core", "NEW_KERNEL", "HIGH"),
    ("A3_FLOOR_v22_stage4_floor.lean", "A3_FLOOR_v22_stage4", "NEW_KERNEL", "HIGH"),
    ("A3_FLOOR_THEOREM.lean", "A3_FLOOR_THEOREM", "NEW_KERNEL", "HIGH"),
    ("Q3/DigammaRemainder.lean", "Q3_DigammaRemainder", "NEW_KERNEL", "HIGH"),
    ("Q3/DigammaSeries.lean", "Q3_DigammaSeries", "NEW_KERNEL", "MEDIUM"),
    ("Q3/AxiomsTheorems.lean", "Q3_AxiomsTheorems", "NEW_KERNEL", "LOW"),
]


def run(cmd: list[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=cwd, check=True)


def import_one(rel_path: str, doc_id: str, approach: str, priority: str) -> None:
    path = ROOT / rel_path
    if not path.exists():
        print(f"[skip] missing: {rel_path}")
        return
    run([sys.executable, str(DB_SCRIPT), "import", str(path), doc_id, approach, priority])


def lean_check(rel_path: str) -> None:
    path = ROOT / rel_path
    if not path.exists():
        print(f"[skip] missing: {rel_path}")
        return
    run(["lake", "env", "lean", rel_path], cwd=ROOT)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="run lake env lean on each file")
    parser.add_argument("--only", nargs="*", default=[], help="restrict to doc_id list")
    parser.add_argument("--list", action="store_true", help="list known doc_id values")
    args = parser.parse_args()

    if args.list:
        for _, doc_id, _, _ in IMPORTS:
            print(doc_id)
        return 0

    selected = IMPORTS
    if args.only:
        wanted = set(args.only)
        selected = [item for item in IMPORTS if item[1] in wanted]
        missing = wanted - {item[1] for item in selected}
        for doc_id in sorted(missing):
            print(f"[warn] unknown doc_id: {doc_id}")

    for rel_path, doc_id, approach, priority in selected:
        if args.check:
            lean_check(rel_path)
        import_one(rel_path, doc_id, approach, priority)

    run([sys.executable, str(STATUS_SCRIPT)])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
