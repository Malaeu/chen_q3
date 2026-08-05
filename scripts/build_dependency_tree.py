#!/usr/bin/env python3
"""Build the Lean-checked axiom dependency inventory for the live Q3 roots.

Despite the historical filename, this is not the file-import DAG.  It records
every ``#print axioms`` result emitted by Q3/CheckAxioms.lean.  The JSON keeps a
backward-compatible primary ``root``/``deps`` pair and a lossless ``roots``
array so two theorem roots can never be silently conflated again.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

try:
    from scripts.q3_sensor_scan import (
        HEAVY_GENERATED_FAMILY,
        build_content_scan_plan,
        path_from_file_id,
        run_rg_on_files,
        scan_import_graph,
    )
except ModuleNotFoundError:  # direct execution from scripts/
    from q3_sensor_scan import (
        HEAVY_GENERATED_FAMILY,
        build_content_scan_plan,
        path_from_file_id,
        run_rg_on_files,
        scan_import_graph,
    )


ROOT = (Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle").resolve()
Q3_DIR = ROOT / "Q3"
ACTIVE_DIR = ROOT / "ACTIVE"

AXIOM_RE = re.compile(r"^\s*axiom\s+(?P<name>[A-Za-z0-9_'.]+)")
SORRY_RE = re.compile(r"\bsorry\b")
DEPENDENCY_BLOCK_RE = re.compile(
    r"'(?P<root>[^']+)'\s+depends on axioms:\s*\[(?P<axioms>.*?)\]",
    re.DOTALL,
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def parse_axiom_dependency_output(output: str) -> list[dict[str, object]]:
    """Parse all Lean ``#print axioms`` blocks without choosing a last line."""
    roots: list[dict[str, object]] = []
    seen: set[str] = set()
    for match in DEPENDENCY_BLOCK_RE.finditer(output):
        root = match.group("root").strip()
        if root in seen:
            raise ValueError(f"duplicate #print axioms root: {root}")
        seen.add(root)
        axioms = [item.strip() for item in match.group("axioms").split(",") if item.strip()]
        roots.append({"id": root, "axioms": axioms})
    if not roots:
        raise ValueError("no #print axioms dependency blocks found")
    return roots


def run_lean_check_axioms(check_file: str = "Q3/CheckAxioms.lean") -> tuple[list[dict[str, object]], str]:
    cmd = ["lake", "env", "lean", check_file]
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or proc.stdout.strip())
    return parse_axiom_dependency_output(proc.stdout), proc.stderr


def collect_axiom_candidates(
    q3_dir: Path = Q3_DIR,
) -> tuple[dict[str, list[Path]], dict[str, object]]:
    """Index axioms only in root/allowlist-protected or lightweight sources."""
    graph, _unresolved = scan_import_graph(q3_dir)
    scan_plan = build_content_scan_plan(q3_dir, graph)
    paths = [
        path_from_file_id(owner, q3_dir)
        for owner in scan_plan.content_scanned_file_ids
    ]
    output = run_rg_on_files(
        ["-n", "--no-heading", r"^\s*axiom\s+[A-Za-z0-9_'.]+"],
        paths,
    )
    candidates: dict[str, set[Path]] = defaultdict(set)
    for raw in output.splitlines():
        try:
            path_text, _line, source = raw.split(":", 2)
        except ValueError:
            continue
        match = AXIOM_RE.match(source)
        if not match:
            continue
        name = match.group("name")
        path = Path(path_text).resolve()
        candidates[name].add(path)
        candidates[name.split(".")[-1]].add(path)
    policy = {
        "policy": "ROOT_CLOSURE_PLUS_LIVE_SUPPLIER_ALLOWLIST",
        "heavy_generated_family": "/".join(HEAVY_GENERATED_FAMILY),
        "heavy_threshold_bytes": scan_plan.threshold_bytes,
        "content_scanned_files": len(scan_plan.content_scanned_file_ids),
        "content_scanned_bytes": scan_plan.content_scanned_bytes,
        "skipped_generated_files": len(scan_plan.skipped_generated_file_ids),
        "skipped_generated_bytes": scan_plan.skipped_generated_bytes,
        "allowlist_entries": list(scan_plan.allowlist_entries),
    }
    return {name: sorted(paths) for name, paths in candidates.items()}, policy


def strip_comments(lines: list[str]) -> list[str]:
    """Remove Lean comments while preserving line numbers."""
    out_lines: list[str] = []
    depth = 0
    for line in lines:
        i = 0
        out: list[str] = []
        while i < len(line):
            if depth == 0 and line[i:i + 2] == "--":
                break
            if line[i:i + 2] == "/-":
                depth += 1
                i += 2
                continue
            if depth > 0 and line[i:i + 2] == "-/":
                depth -= 1
                i += 2
                continue
            if depth == 0:
                out.append(line[i])
            i += 1
        out_lines.append("".join(out))
    return out_lines


def scan_file(path: Path) -> tuple[list[list[object]], list[int]]:
    text = path.read_text(encoding="utf-8")
    cleaned = strip_comments(text.splitlines())
    axioms: list[list[object]] = []
    sorries: list[int] = []
    for line_no, line in enumerate(cleaned, start=1):
        match = AXIOM_RE.match(line)
        if match:
            axioms.append([line_no, match.group("name")])
        if SORRY_RE.search(line):
            sorries.append(line_no)
    return axioms, sorries


def resolve_axiom(name: str, index: dict[str, list[Path]]) -> dict[str, object]:
    if name in STANDARD_AXIOMS:
        return {
            "name": name,
            "classification": "STANDARD_LEAN_AXIOM",
            "mapping_status": "STANDARD",
            "file": None,
            "source_candidates": [],
            "axioms_in_file": [],
            "sorries_in_file": [],
        }

    lookup_keys = [name, name.removeprefix("Q3."), name.split(".")[-1]]
    paths: set[Path] = set()
    for key in lookup_keys:
        paths.update(index.get(key, []))
    candidates = [str(path.relative_to(ROOT)) for path in sorted(paths)]
    if len(paths) != 1:
        return {
            "name": name,
            "classification": "PROJECT_AXIOM",
            "mapping_status": "NOT_FOUND" if not paths else "AMBIGUOUS",
            "file": None,
            "source_candidates": candidates,
            "axioms_in_file": [],
            "sorries_in_file": [],
        }

    path = next(iter(paths))
    axioms, sorries = scan_file(path)
    return {
        "name": name,
        "classification": "PROJECT_AXIOM",
        "mapping_status": "FOUND",
        "file": str(path.relative_to(ROOT)),
        "source_candidates": candidates,
        "axioms_in_file": axioms,
        "sorries_in_file": sorries,
    }


def build_payload(
    parsed_roots: list[dict[str, object]],
    *,
    generated_at: str,
    check_stderr: str,
) -> dict[str, object]:
    index, source_scan = collect_axiom_candidates()
    roots: list[dict[str, object]] = []
    for parsed in parsed_roots:
        root_id = str(parsed["id"])
        deps = [resolve_axiom(str(name), index) for name in parsed["axioms"]]
        roots.append({"id": root_id, "axiom_count": len(deps), "deps": deps})

    primary = roots[0]
    return {
        "schema_version": "2.0",
        "sensor_kind": "LEAN_PRINT_AXIOMS",
        "generated_at": generated_at,
        "check_file": "Q3/CheckAxioms.lean",
        "check_stderr_sha256": sha256_text(check_stderr),
        "source_scan": source_scan,
        "root": primary["id"],
        "deps": primary["deps"],
        "roots": roots,
    }


def render_markdown(data: dict[str, object]) -> str:
    lines = [
        f"# Lean Axiom Dependencies (auto) — {data['generated_at']}",
        "",
        "**Authority:** successful `lake env lean Q3/CheckAxioms.lean` output.",
        "**Boundary:** this is an axiom inventory, not the file-import DAG and not a proof verdict.",
        (
            "**Source scan:** dependency-aware; "
            f"{data['source_scan']['skipped_generated_files']} heavy generated non-root files "
            "were not content-scanned."
        ),
        "",
    ]
    for root in data["roots"]:
        lines += [f"## {root['id']}", f"- Axiom dependencies: {root['axiom_count']}"]
        for dep in root["deps"]:
            label = f"`{dep['name']}` — {dep['classification']} / {dep['mapping_status']}"
            if dep.get("file"):
                label += f" — `{dep['file']}`"
            lines.append(f"  - {label}")
            if dep.get("source_candidates") and dep["mapping_status"] != "FOUND":
                lines.append("    - Candidates: " + ", ".join(dep["source_candidates"]))
        lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default=str(ACTIVE_DIR / "graphs" / "DEPS_TREE_MAIN.md"))
    parser.add_argument("--json", default=str(ACTIVE_DIR / "graphs" / "DEPS_TREE_MAIN.json"))
    args = parser.parse_args()

    parsed, stderr = run_lean_check_axioms()
    data = build_payload(parsed, generated_at=now_utc(), check_stderr=stderr)
    unresolved = [
        (root["id"], dep["name"], dep["mapping_status"])
        for root in data["roots"]
        for dep in root["deps"]
        if dep["mapping_status"] not in {"FOUND", "STANDARD"}
    ]
    if unresolved:
        raise RuntimeError(f"unresolved project axiom declarations: {unresolved}")

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
