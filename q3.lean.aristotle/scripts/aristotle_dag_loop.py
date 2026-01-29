#!/usr/bin/env python3
"""Generate a lightweight Aristotle queue from open axioms + sorries.

This script DOES NOT submit jobs. It only prepares:
  - ACTIVE/aristotle/ARISTOTLE_QUEUE.json + .md
  - per-task prompt + brief files in ACTIVE/aristotle/queue/

Usage:
  python full/q3.lean.aristotle/scripts/aristotle_dag_loop.py --refresh
  python full/q3.lean.aristotle/scripts/aristotle_dag_loop.py --print-next 5
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]  # full/q3.lean.aristotle
REPO_ROOT = ROOT.parents[1]  # repo root
ACTIVE_DIR = ROOT / "ACTIVE"
QUEUE_DIR = ACTIVE_DIR / "aristotle" / "queue"
QUEUE_JSON = ACTIVE_DIR / "aristotle" / "ARISTOTLE_QUEUE.json"
QUEUE_MD = ACTIVE_DIR / "aristotle" / "ARISTOTLE_QUEUE.md"
DEPS_JSON = ACTIVE_DIR / "graphs" / "DEPS_TREE_MAIN.json"

DEFAULT_IGNORE_AXIOMS = {
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Q3.Weil_criterion_tau0",
}

SORRY_RE = re.compile(r"\bsorry\b")
DECL_RE = re.compile(r"^\s*(theorem|lemma|def|example|instance|abbrev)\s+([A-Za-z0-9_'.]+)")


@dataclass
class SorryInfo:
    line: int
    decl: str | None


def run(cmd: list[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, cwd=cwd, check=True)


def refresh_deps() -> None:
    run([str(REPO_ROOT / "scripts" / "build_dependency_tree.py")], cwd=REPO_ROOT)
    run([str(REPO_ROOT / "scripts" / "build_proof_graph.py")], cwd=REPO_ROOT)


def strip_comments(lines: list[str]) -> list[str]:
    """Remove line/block comments while preserving line structure."""
    out_lines: list[str] = []
    depth = 0
    for line in lines:
        i = 0
        out = []
        while i < len(line):
            if depth == 0 and line[i : i + 2] == "--":
                break
            if line[i : i + 2] == "/-":
                depth += 1
                i += 2
                continue
            if depth > 0 and line[i : i + 2] == "-/":
                depth -= 1
                i += 2
                continue
            if depth == 0:
                out.append(line[i])
            i += 1
        out_lines.append("".join(out))
    return out_lines


def scan_sorries(path: Path) -> list[SorryInfo]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except Exception:
        return []
    stripped = strip_comments(lines)
    last_decl = None
    results: list[SorryInfo] = []
    for idx, line in enumerate(stripped, start=1):
        m = DECL_RE.match(line)
        if m:
            last_decl = m.group(2)
        if SORRY_RE.search(line):
            results.append(SorryInfo(line=idx, decl=last_decl))
    return results


def iter_lean_files(paths: Iterable[Path]) -> Iterable[Path]:
    for path in paths:
        if path.is_dir():
            yield from path.rglob("*.lean")
        elif path.suffix == ".lean":
            yield path


def slugify(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]+", "_", text).strip("_")


def load_deps() -> dict:
    if not DEPS_JSON.exists():
        return {}
    return json.loads(DEPS_JSON.read_text(encoding="utf-8"))


def build_queue(scan_paths: list[Path], ignore_axioms: set[str]) -> dict:
    deps = load_deps()
    tasks: list[dict] = []

    # Axiom tasks (main-chain only)
    for dep in deps.get("deps", []):
        name = dep.get("name")
        if not name or name in ignore_axioms:
            continue
        tasks.append(
            {
                "id": f"axiom::{name}",
                "type": "axiom",
                "name": name,
                "file": dep.get("file"),
                "priority": 1,
                "mode": "direct_english",
            }
        )

    # Sorry tasks (file-level)
    for path in iter_lean_files(scan_paths):
        sorries = scan_sorries(path)
        if not sorries:
            continue
        rel = path.relative_to(ROOT)
        tasks.append(
            {
                "id": f"sorry::{rel.as_posix()}",
                "type": "sorry_file",
                "file": str(rel),
                "priority": 2 if "Q3/Proofs" in rel.as_posix() else 3,
                "mode": "fill_sorries",
                "sorries": [{"line": s.line, "decl": s.decl} for s in sorries],
            }
        )

    tasks.sort(key=lambda x: (x["priority"], x["id"]))
    return {
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "root": "Q3.Main.RH_of_Weil_and_Q3",
        "tasks": tasks,
    }


def write_queue(queue: dict) -> None:
    QUEUE_DIR.mkdir(parents=True, exist_ok=True)
    QUEUE_JSON.write_text(json.dumps(queue, indent=2), encoding="utf-8")

    md: list[str] = []
    md.append(f"# Aristotle Queue (auto) - {queue['generated_at']}")
    md.append("")
    md.append("**Purpose:** Auto-generated queue for Aristotle runs (no submission).")
    md.append("**Source:** `ACTIVE/graphs/DEPS_TREE_MAIN.json` + sorry scan of Q3/ trees.")
    md.append("")

    for task in queue["tasks"]:
        md.append(f"## {task['id']}")
        md.append(f"- Type: `{task['type']}`")
        md.append(f"- Mode: `{task['mode']}`")
        md.append(f"- Priority: `{task['priority']}`")
        if task.get("name"):
            md.append(f"- Axiom: `{task['name']}`")
        if task.get("file"):
            md.append(f"- File: `{task['file']}`")
        if task.get("sorries"):
            md.append(f"- Sorries: {len(task['sorries'])}")
            md.append(
                "  - " + ", ".join([f"{s.get('decl', '?')}@L{s['line']}" for s in task["sorries"]])
            )
        md.append("")

    QUEUE_MD.write_text("\n".join(md) + "\n", encoding="utf-8")


def prompt_template(task: dict) -> str:
    if task["type"] == "axiom":
        lemma_name = task.get("name", "<axiom>")
        return f"""Task
Close the axiom `{lemma_name}` by replacing it with a theorem (no new axioms).

Hard constraints:
- Modify only the file that declares this axiom.
- Do NOT add new imports.
- Do NOT change definitions/structures.
- Stay within single-scale assumptions (no two-scale bridges).
- Use existing lemmas already imported.

Preferred tactics:
- Use `suffices` for goal reduction.
- Avoid `exact?` and heavy `aesop`.
- Prefer `simp`, `linarith`, `nlinarith`, `gcongr`, `positivity`.

If the statement is false or under-specified:
- Provide a concrete counterexample or a proof of the negation,
  and explain which assumption is missing.
"""

    # sorry-file task
    file_path = task.get("file", "<file>")
    decls = ", ".join([s.get("decl") or "?" for s in task.get("sorries", [])])
    return f"""Task
Fill the remaining `sorry` in file `{file_path}`.

Targets (nearest declarations):
- {decls if decls else "(unknown)"}

Hard constraints:
- Modify ONLY this file.
- Do NOT add new imports.
- Do NOT touch transitive dependencies.
- Do NOT change definitions/structures.
- Stay within single-scale assumptions (no two-scale bridges).

Preferred tactics:
- Use `suffices` for goal reduction.
- Avoid `exact?` and heavy `aesop`.
- Prefer `simp`, `linarith`, `nlinarith`, `gcongr`, `positivity`.

If the statement is false or under-specified:
- Provide a counterexample or a proof of the negation,
  and point to the missing assumption.
"""


def brief_template(task: dict) -> str:
    file_path = task.get("file", "<file>")
    if task["type"] == "axiom":
        lemma_name = task.get("name", "<axiom>")
        return f"""# NODE BRIEF - {lemma_name}

## Location
- File: `{file_path}`
- Declaration: `{lemma_name}`

## Goal (informal)
Replace axiom with theorem; no new axioms, no new imports.

## Fixed assumptions / invariants
- Single-scale mainline (t_critical).
- Avoid two-scale bridges.
- Use only already-imported lemmas.

## Preferred finish
- simp / linarith / nlinarith
- Avoid heavy `aesop` unless non-terminal
"""

    decls = "\n".join([f"- {s.get('decl', '?')} @ L{s['line']}" for s in task.get("sorries", [])])
    return f"""# NODE BRIEF - {file_path}

## Location
- File: `{file_path}`
- Sorries:
{decls if decls else "- (unknown)"}

## Goal (informal)
Fill all remaining `sorry` in this file without touching imports/defs.

## Fixed assumptions / invariants
- Single-scale mainline (t_critical).
- Avoid two-scale bridges.
- Use only already-imported lemmas.

## Preferred finish
- simp / linarith / nlinarith
- Avoid heavy `aesop` unless non-terminal
"""


def write_task_files(queue: dict) -> None:
    QUEUE_DIR.mkdir(parents=True, exist_ok=True)
    for task in queue["tasks"]:
        slug = slugify(task["id"])
        task_dir = QUEUE_DIR / slug
        task_dir.mkdir(parents=True, exist_ok=True)
        (task_dir / "PROMPT.txt").write_text(prompt_template(task), encoding="utf-8")
        (task_dir / "NODE_BRIEF.md").write_text(brief_template(task), encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--refresh", action="store_true", help="refresh deps/graph first")
    ap.add_argument(
        "--paths",
        nargs="*",
        default=[str(ROOT / "Q3")],
        help="paths to scan for sorries (default: Q3/)",
    )
    ap.add_argument(
        "--print-next",
        type=int,
        default=0,
        help="print next N tasks after generating queue",
    )
    args = ap.parse_args()

    if args.refresh:
        refresh_deps()

    scan_paths = [Path(p) for p in args.paths]
    queue = build_queue(scan_paths, DEFAULT_IGNORE_AXIOMS)
    write_queue(queue)
    write_task_files(queue)

    if args.print_next:
        for task in queue["tasks"][: args.print_next]:
            print(f"{task['id']} :: {task['type']} :: {task.get('file', '')}")
    else:
        print(f"Wrote {QUEUE_JSON} and {QUEUE_MD}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
