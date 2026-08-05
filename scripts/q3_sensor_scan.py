#!/usr/bin/env python3
"""Fast shared source scanner for the Q3 observability generators.

The Q3 tree contains multi-megabyte generated Lean certificate files.  Python
must not read all 4.1 GiB merely to find a handful of ``sorry`` tokens or import
headers.  Ripgrep selects candidate files/lines; the exact Lean-aware pass is
then limited to those candidates or to the short module header.
"""

from __future__ import annotations

import re
import subprocess
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator


SORRY_RE = re.compile(r"\bsorry\b")
IMPORT_RE = re.compile(r"^\s*import\s+(?P<mods>.+)$")
DEFAULT_EXCLUDED_DIRS = frozenset({"Clean", "Archive"})
HEAVY_GENERATED_THRESHOLD_BYTES = 1_000_000
HEAVY_GENERATED_FAMILY = ("Q3", "Proofs", "PrimeCert")
DEFAULT_ROOT_ENTRY_FILES = (
    "Q3/Main.lean",
    "Q3/Proofs/PaperMainlineAtomRoute.lean",
)
DEFAULT_LIVE_SUPPLIER_ALLOWLIST = (
    "Q3/Proofs/PrimeCert/Defs.lean",
    "Q3/Proofs/PrimeCert/IntervalLemmas.lean",
    "Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowBucket0Auto_0_249.lean",
    "Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowBucket0Auto_250_499.lean",
)


@dataclass(frozen=True)
class ContentScanPlan:
    """Dependency-aware full-content policy over a complete import graph."""

    content_scanned_file_ids: frozenset[str]
    skipped_generated_file_ids: frozenset[str]
    root_closure_file_ids: frozenset[str]
    allowlist_closure_file_ids: frozenset[str]
    allowlist_entries: tuple[str, ...]
    threshold_bytes: int
    content_scanned_bytes: int
    skipped_generated_bytes: int


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


def iter_masked_lines(lines: Iterable[str]) -> Iterator[str]:
    """Yield nested-comment/string-masked lines without buffering the file."""
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
        yield "".join(out)


def mask_comments_and_strings(lines: list[str]) -> list[str]:
    """Mask nested comments and strings while preserving line positions."""
    return list(iter_masked_lines(lines))


def _run_rg(args: list[str], search_root: Path) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(["rg", *args, str(search_root)], capture_output=True, text=True)
    if proc.returncode not in (0, 1):
        raise RuntimeError(proc.stderr.strip() or "ripgrep source scan failed")
    return proc


def run_rg_on_files(
    args: list[str], paths: Iterable[Path], *, batch_size: int = 128
) -> str:
    """Run ripgrep over explicit files in bounded command-line batches."""
    ordered = sorted({path.resolve() for path in paths})
    output: list[str] = []
    for start in range(0, len(ordered), batch_size):
        batch = ordered[start:start + batch_size]
        proc = subprocess.run(
            ["rg", *args, "--", *(str(path) for path in batch)],
            capture_output=True,
            text=True,
        )
        if proc.returncode not in (0, 1):
            raise RuntimeError(proc.stderr.strip() or "ripgrep source scan failed")
        output.append(proc.stdout)
    return "".join(output)


def path_from_file_id(file_name: str, q3_dir: Path) -> Path:
    parts = Path(file_name).parts
    if not parts or parts[0] != "Q3" or ".." in parts:
        raise ValueError(f"invalid Q3 file id: {file_name}")
    return q3_dir.joinpath(*parts[1:])


def scan_sorry_sites(
    q3_dir: Path,
    included_file_ids: Iterable[str] | None = None,
) -> list[dict[str, object]]:
    if included_file_ids is None:
        proc = _run_rg(["-l", "--null", "--glob", "*.lean", r"\bsorry\b"], q3_dir)
        candidate_text = proc.stdout
    else:
        paths = [path_from_file_id(file_name, q3_dir) for file_name in included_file_ids]
        missing = [path for path in paths if not path.is_file()]
        if missing:
            raise FileNotFoundError(missing[0])
        candidate_text = run_rg_on_files(["-l", "--null", r"\bsorry\b"], paths)
    candidates = [Path(value) for value in candidate_text.split("\0") if value]
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


def read_import_modules(path: Path) -> list[str]:
    """Read only a Lean module's import header, never its generated payload."""
    imports: list[str] = []
    with path.open(encoding="utf-8") as handle:
        for source in iter_masked_lines(handle):
            stripped = source.strip()
            if not stripped or stripped == "prelude":
                continue
            match = IMPORT_RE.match(source)
            if match:
                imports.extend(match.group("mods").split())
                continue
            break
    return imports


def scan_import_graph(q3_dir: Path) -> tuple[dict[str, dict[str, object]], list[dict[str, str]]]:
    files = lean_files(q3_dir)
    all_files = sorted(q3_dir.rglob("*.lean"))
    module_map = {module_name(path, q3_dir): file_id(path, q3_dir) for path in files}
    all_module_map = {module_name(path, q3_dir): file_id(path, q3_dir) for path in all_files}
    graph: dict[str, dict[str, object]] = {}
    unresolved: list[dict[str, str]] = []
    for path in files:
        imports = read_import_modules(path)
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


def _in_heavy_generated_family(file_name: str) -> bool:
    parts = Path(file_name).parts
    return parts[:len(HEAVY_GENERATED_FAMILY)] == HEAVY_GENERATED_FAMILY


def build_content_scan_plan(
    q3_dir: Path,
    graph: dict[str, dict[str, object]],
    *,
    root_entries: Iterable[str] = DEFAULT_ROOT_ENTRY_FILES,
    allowlist_entries: Iterable[str] = DEFAULT_LIVE_SUPPLIER_ALLOWLIST,
    threshold_bytes: int = HEAVY_GENERATED_THRESHOLD_BYTES,
) -> ContentScanPlan:
    """Skip only heavy non-root PrimeCert payloads; fail closed on bad pins."""
    if threshold_bytes < 1:
        raise ValueError("heavy generated threshold must be positive")
    roots = tuple(dict.fromkeys(root_entries))
    allowlist = tuple(dict.fromkeys(allowlist_entries))
    missing_roots = [entry for entry in roots if entry not in graph]
    missing_allowlist = [entry for entry in allowlist if entry not in graph]
    if missing_roots:
        raise ValueError(f"root entry missing from import graph: {missing_roots}")
    if missing_allowlist:
        raise ValueError(f"allowlist entry missing from import graph: {missing_allowlist}")

    root_closure = {
        member
        for entry in roots
        for member in dependency_closure(graph, entry)
    }
    allowlist_closure = {
        member
        for entry in allowlist
        for member in dependency_closure(graph, entry)
    }
    protected = root_closure | allowlist_closure
    sizes = {
        owner: path_from_file_id(owner, q3_dir).stat().st_size
        for owner in graph
    }
    heavy_generated = {
        owner for owner, size in sizes.items()
        if _in_heavy_generated_family(owner) and size >= threshold_bytes
    }
    skipped = heavy_generated - protected
    scanned = set(graph) - skipped
    if skipped & protected:
        raise AssertionError("dependency-aware content scan skipped a protected file")
    return ContentScanPlan(
        content_scanned_file_ids=frozenset(scanned),
        skipped_generated_file_ids=frozenset(skipped),
        root_closure_file_ids=frozenset(root_closure),
        allowlist_closure_file_ids=frozenset(allowlist_closure),
        allowlist_entries=allowlist,
        threshold_bytes=threshold_bytes,
        content_scanned_bytes=sum(sizes[owner] for owner in scanned),
        skipped_generated_bytes=sum(sizes[owner] for owner in skipped),
    )
