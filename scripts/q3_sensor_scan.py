#!/usr/bin/env python3
"""Fast shared source scanner for the Q3 observability generators.

The Q3 tree contains multi-megabyte generated Lean certificate files.  Python
must not read all 4.1 GiB merely to find a handful of ``sorry`` tokens or import
headers.  Ripgrep selects candidate files/lines; the exact Lean-aware pass is
then limited to those candidates or to the short module header.
"""

from __future__ import annotations

import itertools
import re
import subprocess
from collections import defaultdict, deque
from pathlib import Path


SORRY_RE = re.compile(r"\bsorry\b")
IMPORT_RE = re.compile(r"^\s*import\s+(?P<mods>.+)$")
DEFAULT_EXCLUDED_DIRS = frozenset({"Clean", "Archive"})


def relative_parts(path: Path, q3_dir: Path) -> tuple[str, ...]:
    return path.resolve().relative_to(q3_dir.resolve()).parts


def is_excluded(
    path: Path,
    q3_dir: Path,
    excluded_dirs: frozenset[str] = DEFAULT_EXCLUDED_DIRS,
) -> bool:
    parts = relative_parts(path, q3_dir)
    return bool(parts and parts[0] in excluded_dirs)


def file_id(path: Path, q3_dir: Path) -> str:
    return str(Path("Q3") / Path(*relative_parts(path, q3_dir)))


def module_name(path: Path, q3_dir: Path) -> str:
    rel = Path(*relative_parts(path, q3_dir)).with_suffix("")
    return ".".join(("Q3", *rel.parts))


def lean_files(q3_dir: Path) -> list[Path]:
    return [
        path for path in sorted(q3_dir.rglob("*.lean"))
        if not is_excluded(path, q3_dir)
    ]


def mask_comments_and_strings(lines: list[str]) -> list[str]:
    """Mask nested comments and strings while preserving line positions."""
    out_lines: list[str] = []
    comment_depth = 0
    in_string = False
    escaped = False
    for line in lines:
        index = 0
        out: list[str] = []
        while index < len(line):
            pair = line[index:index + 2]
            char = line[index]
            if comment_depth > 0:
                if pair == "/-":
                    comment_depth += 1
                    index += 2
                    continue
                if pair == "-/":
                    comment_depth -= 1
                    index += 2
                    continue
                index += 1
                continue
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
                index += 1
                continue
            if pair == "--":
                break
            if pair == "/-":
                comment_depth += 1
                index += 2
                continue
            if char == '"':
                in_string = True
                index += 1
                continue
            out.append(char)
            index += 1
        out_lines.append("".join(out))
    return out_lines


def _run_rg(args: list[str], search_root: Path) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(["rg", *args, str(search_root)], capture_output=True, text=True)
    if proc.returncode not in (0, 1):
        raise RuntimeError(proc.stderr.strip() or "ripgrep source scan failed")
    return proc


def scan_sorry_sites(q3_dir: Path) -> list[dict[str, object]]:
    proc = _run_rg(["-l", "--null", "--glob", "*.lean", r"\bsorry\b"], q3_dir)
    candidates = [Path(value) for value in proc.stdout.split("\0") if value]
    rows: list[dict[str, object]] = []
    for path in sorted(candidates):
        if is_excluded(path, q3_dir):
            continue
        text = path.read_text(encoding="utf-8")
        cleaned = mask_comments_and_strings(text.splitlines())
        lines = [
            line_no for line_no, source in enumerate(cleaned, start=1)
            if SORRY_RE.search(source)
        ]
        if lines:
            rows.append({"file": file_id(path, q3_dir), "lines": lines, "count": len(lines)})
    return rows


def scan_import_graph(q3_dir: Path) -> tuple[dict[str, dict[str, object]], list[dict[str, str]]]:
    files = lean_files(q3_dir)
    all_files = sorted(q3_dir.rglob("*.lean"))
    module_map = {module_name(path, q3_dir): file_id(path, q3_dir) for path in files}
    all_module_map = {module_name(path, q3_dir): file_id(path, q3_dir) for path in all_files}
    by_path: dict[Path, list[tuple[int, str]]] = defaultdict(list)
    proc = _run_rg(
        ["-n", "--no-heading", "--glob", "*.lean", r"^\s*import\s+"], q3_dir
    )
    for raw in proc.stdout.splitlines():
        try:
            path_text, line_text, source = raw.split(":", 2)
            path = Path(path_text)
            line_no = int(line_text)
        except (ValueError, TypeError):
            continue
        if not is_excluded(path, q3_dir):
            by_path[path.resolve()].append((line_no, source))

    graph: dict[str, dict[str, object]] = {}
    unresolved: list[dict[str, str]] = []
    for path in files:
        resolved = path.resolve()
        imports: list[str] = []
        candidates = by_path.get(resolved, [])
        if candidates:
            max_line = max(line_no for line_no, _source in candidates)
            with path.open(encoding="utf-8") as handle:
                prefix = list(itertools.islice(handle, max_line))
            cleaned = mask_comments_and_strings([line.rstrip("\n") for line in prefix])
            for line in cleaned:
                match = IMPORT_RE.match(line)
                if match:
                    imports.extend(match.group("mods").split())
        internal: list[str] = []
        owner = file_id(path, q3_dir)
        for imported_module in imports:
            dependency = module_map.get(imported_module)
            if dependency:
                internal.append(dependency)
            elif imported_module.startswith("Q3."):
                unresolved.append({
                    "file": owner,
                    "module": imported_module,
                    "status": (
                        "EXCLUDED_TARGET" if imported_module in all_module_map
                        else "MISSING_TARGET"
                    ),
                })
        graph[owner] = {
            "file": owner,
            "module": module_name(path, q3_dir),
            "dependencies": sorted(set(internal)),
        }
    return graph, sorted(unresolved, key=lambda row: (row["file"], row["module"]))


def dependency_closure(graph: dict[str, dict[str, object]], entry_file: str) -> dict[str, int]:
    if entry_file not in graph:
        raise ValueError(f"root entry file missing from import graph: {entry_file}")
    distances = {entry_file: 0}
    queue: deque[str] = deque([entry_file])
    while queue:
        current = queue.popleft()
        depth = distances[current]
        for dependency in graph[current]["dependencies"]:
            if dependency not in distances:
                distances[dependency] = depth + 1
                queue.append(dependency)
    return distances
