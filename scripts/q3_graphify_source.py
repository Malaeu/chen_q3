#!/usr/bin/env python3
"""Build a tracked Q3 source-reference graph for local Graphify analysis.

The graph records literal Lean imports, TeX includes, and Markdown links.  It
does not infer theorem dependencies or proof truth.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import posixpath
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path, PurePosixPath
from typing import Any
from urllib.parse import unquote

try:
    from scripts.q3_sensor_scan import read_import_modules
except ModuleNotFoundError:  # direct execution from scripts/
    from q3_sensor_scan import read_import_modules


BOUNDARY = "SOURCE_REFERENCE_GRAPH_NOT_PROOF_DEPENDENCY_GRAPH"
GRAPHIFY_VERSION = "0.9.92"
SOURCE_TYPES = {".lean": "lean", ".tex": "tex", ".md": "markdown"}
HISTORICAL_DIRS = {"archive", "archives", "historical", "history", "legacy", "attic", "retired"}
MAX_PRINTED_ROWS = 20

TEX_INCLUDE_RE = re.compile(r"\\(?P<command>input|include)\s*\{(?P<target>[^{}]+)\}")
MARKDOWN_INLINE_LINK_RE = re.compile(
    r"(?<!!)(?:\[[^\]\n]*\])\(\s*(?P<target><[^>\n]*>|(?:\\.|[^)\s])+)",
)
MARKDOWN_REFERENCE_DEF_RE = re.compile(
    r"^\s{0,3}\[[^\]\n]+\]:\s*(?P<target><[^>\n]*>|(?:\\.|[^\s])+)",
)
MARKDOWN_FENCE_RE = re.compile(r"^\s{0,3}(?P<fence>`{3,}|~{3,})")
LINE_SUFFIX_RE = re.compile(r"^(?P<path>.+):(?P<line>\d+)$")
LINE_FRAGMENT_RE = re.compile(r"^L(?P<line>\d+)(?:-L\d+)?$", re.IGNORECASE)
KNOWN_URL_SCHEME_RE = re.compile(r"^(?:https?|ftp|mailto|tel|data|javascript):", re.IGNORECASE)

PARSER_LIMITATIONS = [
    {
        "parser": "lean_imports",
        "limitation": (
            "Reads only Lean import headers with the shared nested-comment/string masker; "
            "does not parse declarations, theorem dependencies, or elaboration."
        ),
    },
    {
        "parser": "tex_includes",
        "limitation": (
            "Recognizes literal \\input{...} and \\include{...}; macro-expanded paths "
            "and other TeX package commands are not resolved."
        ),
    },
    {
        "parser": "markdown_links",
        "limitation": (
            "Recognizes common inline links and link definitions; raw HTML, nested link "
                "labels, and reference-style uses are not resolved. Indented code blocks are "
                "skipped; math written as link-like Markdown outside code can remain ambiguous."
        ),
    },
    {
        "parser": "source_scope",
        "limitation": (
            "Only Git-tracked .lean, .tex, and .md files become source nodes; external "
            "or out-of-scope targets remain unresolved references."
        ),
    },
]


class GraphifySourceError(RuntimeError):
    """Raised when the repository or output contract cannot be satisfied."""


def _git(root: Path, *args: str) -> bytes:
    proc = subprocess.run(
        ["git", "-C", str(root), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode:
        detail = proc.stderr.decode("utf-8", errors="replace").strip()
        raise GraphifySourceError(detail or f"git {' '.join(args)} failed")
    return proc.stdout


def repository_root(path: Path) -> Path:
    """Return the enclosing Git worktree root for ``path``."""
    try:
        value = _git(path.resolve(), "rev-parse", "--show-toplevel")
    except GraphifySourceError as exc:
        raise GraphifySourceError(f"not inside a Git worktree: {path}") from exc
    return Path(os.fsdecode(value.rstrip(b"\n"))).resolve()


def _tracked_paths(root: Path) -> list[str]:
    raw = _git(root, "ls-files", "--cached", "-z")
    return sorted({os.fsdecode(item) for item in raw.split(b"\0") if item})


def _dirty_tracked_paths(root: Path) -> list[str]:
    # Comparing the worktree to HEAD includes both staged and unstaged tracked edits.
    raw = _git(root, "diff", "--name-only", "--no-renames", "-z", "HEAD", "--")
    return sorted({os.fsdecode(item) for item in raw.split(b"\0") if item})


def _file_type(path: str) -> str | None:
    return SOURCE_TYPES.get(PurePosixPath(path).suffix.lower())


def _is_historical(path: str) -> bool:
    parts = PurePosixPath(path).parts[:-1]
    for part in parts:
        lower = part.lower()
        if lower in HISTORICAL_DIRS or lower.startswith(
            ("archive_", "archive-", "historical_", "legacy_")
        ):
            return True
    return False


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _lean_module_name(path: str) -> str:
    relative = PurePosixPath(path)
    parts = relative.parts
    if parts and parts[0] == "q3.lean.aristotle":
        parts = parts[1:]
    if not parts:
        return ""
    module_parts = list(PurePosixPath(*parts).with_suffix("").parts)
    return ".".join(module_parts)


def _external_module_node(module: str, *, local: bool) -> dict[str, Any]:
    status = "unresolved_local_module" if local else "external_unresolved"
    return {
        "id": ("unresolved-module::" if local else "external-module::") + module,
        "label": module,
        "file_type": "unresolved_module" if local else "external_module",
        "source_file": None,
        "resolution": status,
        "external": not local,
    }


def _strip_tex_comments(text: str) -> str:
    """Remove unescaped TeX comments while retaining line boundaries."""
    masked: list[str] = []
    for line in text.splitlines(keepends=True):
        cut = len(line)
        for index, char in enumerate(line):
            if char != "%":
                continue
            backslashes = 0
            cursor = index - 1
            while cursor >= 0 and line[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            if backslashes % 2 == 0:
                cut = index
                break
        masked.append(line[:cut] + ("\n" if line.endswith("\n") and cut < len(line) else ""))
    return "".join(masked)


def _markdown_lines(text: str) -> list[tuple[int, str]]:
    """Yield non-code Markdown lines with stable one-based line numbers."""
    result: list[tuple[int, str]] = []
    fence_char: str | None = None
    fence_size = 0
    for line_number, line in enumerate(text.splitlines(), start=1):
        match = MARKDOWN_FENCE_RE.match(line)
        if match:
            marker = match.group("fence")
            if fence_char is None:
                fence_char, fence_size = marker[0], len(marker)
            elif marker[0] == fence_char and len(marker) >= fence_size:
                fence_char, fence_size = None, 0
            continue
        if fence_char is not None:
            continue
        # Four-space/tab-indented blocks are Markdown code blocks. Skipping them
        # also avoids treating displayed mathematics such as `[x](1+u)` as a link.
        if line.startswith("\t") or line.startswith("    "):
            continue
        # Remove simple inline-code spans so code examples do not become links.
        cleaned = re.sub(r"`+[^`]*`+", "", line)
        result.append((line_number, cleaned))
    return result


def _normalize_repo_candidate(base: str, target: str, *, repo_absolute: bool) -> str | None:
    target = unquote(target.replace("\\ ", " "))
    if "\\" in target:
        target = target.replace("\\", "/")
    if repo_absolute:
        combined = target.lstrip("/")
    else:
        combined = posixpath.join(base, target)
    normalized = posixpath.normpath(combined)
    if normalized in {"", "."} or normalized == ".." or normalized.startswith("../"):
        return None
    return PurePosixPath(normalized).as_posix()


def _path_variants(path: str, *, add_tex_suffix: bool) -> list[str]:
    variants = [path]
    if add_tex_suffix and not PurePosixPath(path).suffix:
        variants.append(path + ".tex")
    return variants


def _resolve_source_target(
    root: Path,
    tracked_sources: set[str],
    target: str,
    *,
    source_file: str,
    document_roots: list[str] | None = None,
    add_tex_suffix: bool = False,
) -> dict[str, Any]:
    """Resolve a literal local reference against source-relative and document roots."""
    document_roots = document_roots or []
    raw_path = target
    path_and_query, _, fragment = raw_path.partition("#")
    queryless = path_and_query.split("?", 1)[0]
    line_number: int | None = None
    line_match = LINE_SUFFIX_RE.match(queryless)
    if line_match and ("/" in line_match.group("path") or "." in line_match.group("path")):
        queryless = line_match.group("path")
        line_number = int(line_match.group("line"))
    fragment_line = LINE_FRAGMENT_RE.match(fragment)
    line_anchor = fragment if fragment_line else None
    if line_number is None and fragment_line:
        line_number = int(fragment_line.group("line"))

    if not queryless and fragment:
        normalized = source_file
        return {
            "status": "resolved",
            "path": normalized,
            "resolution_base": "same_document",
            "line": line_number,
            "anchor": fragment,
            "line_anchor": line_anchor,
        }

    repo_absolute = queryless.startswith("/")
    bases: list[tuple[str, str]]
    if repo_absolute:
        bases = [("repository_absolute", "")]
    else:
        source_parent = PurePosixPath(source_file).parent.as_posix()
        if source_parent == ".":
            source_parent = ""
        bases = [("relative", source_parent)]
        bases.extend(("document_root", base) for base in document_roots)
        bases.append(("repository_root", ""))

    escaped = False
    document_matches: list[dict[str, Any]] = []
    for base_kind, base in bases:
        if base_kind == "repository_root" and document_matches:
            break
        normalized = _normalize_repo_candidate(base, queryless, repo_absolute=repo_absolute)
        if normalized is None:
            escaped = True
            continue
        for candidate in _path_variants(normalized, add_tex_suffix=add_tex_suffix):
            if candidate in tracked_sources:
                candidate_path = root / candidate
                if candidate_path.is_file() and not candidate_path.is_symlink():
                    result = {
                        "status": "resolved",
                        "path": candidate,
                        "resolution_base": base_kind,
                        "line": line_number,
                        "anchor": fragment or None,
                        "line_anchor": line_anchor,
                    }
                else:
                    result = {
                        "status": "tracked_target_missing_from_worktree",
                        "path": candidate,
                        "resolution_base": base_kind,
                        "line": line_number,
                        "anchor": fragment or None,
                        "line_anchor": line_anchor,
                    }
                if base_kind == "document_root":
                    document_matches.append(result)
                    continue
                return result
            if (root / candidate).is_file():
                result = {
                    "status": "target_outside_source_scope",
                    "path": candidate,
                    "resolution_base": base_kind,
                    "line": line_number,
                    "anchor": fragment or None,
                    "line_anchor": line_anchor,
                }
                if base_kind == "document_root":
                    document_matches.append(result)
                    continue
                return result
    if document_matches:
        distinct = {
            (str(row["status"]), str(row.get("path", ""))) for row in document_matches
        }
        if len(distinct) == 1:
            return document_matches[0]
        return {
            "status": "ambiguous_document_root_target",
            "path": queryless,
            "candidate_paths": sorted({path for _status, path in distinct}),
            "resolution_base": None,
            "line": line_number,
            "anchor": fragment or None,
            "line_anchor": line_anchor,
        }
    return {
        "status": "path_escapes_repository" if escaped else "broken_local_reference",
        "path": queryless,
        "resolution_base": None,
        "line": line_number,
        "anchor": fragment or None,
        "line_anchor": line_anchor,
    }


def _document_roots(tracked_sources: list[str]) -> list[str]:
    roots: list[str] = []
    for conventional in ("full", "paper_weil"):
        roots.append(conventional)
    roots.extend(
        PurePosixPath(path).parent.as_posix()
        for path in tracked_sources
        if PurePosixPath(path).name.lower() == "main.tex"
    )
    unique: list[str] = []
    for root in roots:
        normalized = "" if root == "." else root
        if normalized not in unique:
            unique.append(normalized)
    return unique


def _document_roots_for(source_file: str, roots: list[str]) -> list[str]:
    """Choose a TeX source's owning document root without crossing projects."""
    for conventional in ("full", "paper_weil"):
        if conventional in roots and (
            source_file == conventional or source_file.startswith(conventional + "/")
        ):
            return [conventional]
    main_roots = [root for root in roots if root not in {"", "full", "paper_weil"}]
    owners = [root for root in main_roots if source_file.startswith(root + "/")]
    if owners:
        return [max(owners, key=len)]
    return roots


def _add_link(links: list[dict[str, Any]], edge: dict[str, Any]) -> None:
    # These fields are required by Graphify 0.9.92. The relation itself remains
    # a literal source reference, not an inferred theorem/proof dependency.
    edge.setdefault("source_file", edge["source"])
    edge.setdefault("confidence", "EXTRACTED")
    edge.setdefault("confidence_score", 1.0)
    edge.setdefault("_origin", "literal_reference_scan")
    if edge.get("line") is not None:
        edge.setdefault("source_location", f"L{edge['line']}")
    links.append(edge)


def build_graph(root: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    """Build node-link graph and full coverage report from a Git worktree."""
    root = repository_root(root)
    head = os.fsdecode(_git(root, "rev-parse", "HEAD").strip())
    dirty_paths = _dirty_tracked_paths(root)
    dirty_set = set(dirty_paths)
    tracked_sources = [
        path for path in _tracked_paths(root) if _file_type(path) is not None
    ]
    tracked_set = set(tracked_sources)
    nodes: list[dict[str, Any]] = []
    source_records: list[dict[str, Any]] = []
    source_nodes: dict[str, dict[str, Any]] = {}
    parser_errors: list[dict[str, Any]] = []
    source_errors: list[dict[str, Any]] = []

    for relative in tracked_sources:
        file_type = _file_type(relative)
        assert file_type is not None
        absolute = root / relative
        symlink = absolute.is_symlink()
        present = absolute.is_file() and not symlink
        source_hash: str | None = None
        hash_kind = "working_tree_bytes"
        if present:
            try:
                source_hash = _sha256_file(absolute)
            except OSError as exc:
                source_errors.append({"path": relative, "stage": "hash", "error": str(exc)})
        elif symlink:
            # Hash the link text without following it; this is provenance, not file content.
            source_hash = hashlib.sha256(os.fsencode(os.readlink(absolute))).hexdigest()
            hash_kind = "symlink_target_text"
        historical = _is_historical(relative)
        node = {
            "id": relative,
            "label": PurePosixPath(relative).name,
            "file_type": file_type,
            "source_file": relative,
            "sha256": source_hash,
            "hash_kind": hash_kind if source_hash is not None else None,
            "historical": historical,
            "dirty": relative in dirty_set,
            "present_in_worktree": present,
            "worktree_state": "symlink" if symlink else "regular_file" if present else "missing",
        }
        nodes.append(node)
        source_nodes[relative] = node
        source_records.append({
            "path": relative,
            "file_type": file_type,
            "sha256": source_hash,
            "hash_kind": hash_kind if source_hash is not None else None,
            "historical": historical,
            "dirty": relative in dirty_set,
            "present_in_worktree": present,
            "worktree_state": "symlink" if symlink else "regular_file" if present else "missing",
        })

    module_to_paths: dict[str, list[str]] = defaultdict(list)
    for relative in tracked_sources:
        if _file_type(relative) == "lean":
            module = _lean_module_name(relative)
            if module:
                module_to_paths[module].append(relative)
    local_module_roots = {name.split(".", 1)[0] for name in module_to_paths}

    links: list[dict[str, Any]] = []
    unresolved: list[dict[str, Any]] = []
    external_nodes: dict[str, dict[str, Any]] = {}
    for relative in tracked_sources:
        node = source_nodes[relative]
        if not node["present_in_worktree"]:
            continue
        absolute = root / relative
        file_type = str(node["file_type"])
        if file_type == "lean":
            try:
                imports = read_import_modules(absolute)
            except (OSError, UnicodeError) as exc:
                parser_errors.append({"path": relative, "stage": "lean_imports", "error": str(exc)})
                continue
            for module in imports:
                matches = module_to_paths.get(module, [])
                if len(matches) == 1:
                    target = matches[0]
                    if source_nodes[target]["present_in_worktree"]:
                        _add_link(links, {
                            "source": relative,
                            "target": target,
                            "relation": "imports_module",
                            "module": module,
                        })
                    else:
                        unresolved.append({
                            "relation": "imports_module",
                            "source_file": relative,
                            "target": module,
                            "status": "tracked_module_missing_from_worktree",
                            "candidate_paths": matches,
                        })
                elif len(matches) > 1:
                    unresolved.append({
                        "relation": "imports_module",
                        "source_file": relative,
                        "target": module,
                        "status": "ambiguous_local_module",
                        "candidate_paths": sorted(matches),
                    })
                else:
                    local = (
                        module.split(".", 1)[0] in local_module_roots
                        or module.startswith("Q3.")
                    )
                    unresolved.append({
                        "relation": "imports_module",
                        "source_file": relative,
                        "target": module,
                        "status": "unresolved_local_module" if local else "external_unresolved",
                        "candidate_paths": [],
                    })
                    external_node = _external_module_node(module, local=local)
                    external_nodes[external_node["id"]] = external_node
                    _add_link(links, {
                        "source": relative,
                        "target": external_node["id"],
                        "relation": "imports_module",
                        "module": module,
                        "resolution": external_node["resolution"],
                    })
        elif file_type == "tex":
            try:
                text = absolute.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as exc:
                parser_errors.append({"path": relative, "stage": "tex_includes", "error": str(exc)})
                continue
            uncommented = _strip_tex_comments(text)
            roots = _document_roots(tracked_sources)
            roots = _document_roots_for(relative, roots)
            for match in TEX_INCLUDE_RE.finditer(uncommented):
                target = match.group("target").strip()
                line_number = uncommented.count("\n", 0, match.start()) + 1
                if re.search(r"\\[A-Za-z@]+", target):
                    unresolved.append({
                        "relation": "includes_tex",
                        "source_file": relative,
                        "target": target,
                        "line": line_number,
                        "target_line": None,
                        "status": "macro_computed_path",
                        "path": target,
                        "resolution_base": None,
                        "anchor": None,
                        "line_anchor": None,
                    })
                    continue
                resolution = _resolve_source_target(
                    root,
                    tracked_set,
                    target,
                    source_file=relative,
                    document_roots=roots,
                    add_tex_suffix=True,
                )
                if resolution["status"] == "resolved":
                    _add_link(links, {
                        "source": relative,
                        "target": resolution["path"],
                        "relation": "includes_tex",
                        "command": match.group("command"),
                        "line": line_number,
                        "resolution_base": resolution["resolution_base"],
                    })
                else:
                    unresolved.append({
                        "relation": "includes_tex",
                        "source_file": relative,
                        "target": target,
                        "line": line_number,
                        "target_line": resolution["line"],
                        "anchor": resolution["anchor"],
                        "line_anchor": resolution["line_anchor"],
                        **{
                            key: value for key, value in resolution.items()
                            if key not in {"line", "anchor", "line_anchor"}
                        },
                    })
        elif file_type == "markdown":
            try:
                text = absolute.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as exc:
                parser_errors.append({
                    "path": relative,
                    "stage": "markdown_links",
                    "error": str(exc),
                })
                continue
            for line_number, line in _markdown_lines(text):
                matches = list(MARKDOWN_INLINE_LINK_RE.finditer(line))
                definition = MARKDOWN_REFERENCE_DEF_RE.match(line)
                if definition:
                    matches.append(definition)
                for match in matches:
                    target = match.group("target").strip()
                    if target.startswith("<") and target.endswith(">"):
                        target = target[1:-1]
                    if KNOWN_URL_SCHEME_RE.match(target) or target.startswith("//"):
                        continue  # No network fetch; external links are outside this graph.
                    resolution = _resolve_source_target(
                        root,
                        tracked_set,
                        target,
                        source_file=relative,
                    )
                    if resolution["status"] == "resolved":
                        _add_link(links, {
                            "source": relative,
                            "target": resolution["path"],
                            "relation": "links_document",
                            "reference": target,
                            "line": line_number,
                            "anchor": resolution["anchor"],
                            "line_anchor": resolution["line_anchor"],
                            "target_line": resolution["line"],
                            "resolution_base": resolution["resolution_base"],
                        })
                    else:
                        unresolved.append({
                            "relation": "links_document",
                            "source_file": relative,
                            "target": target,
                            "line": line_number,
                            "target_line": resolution["line"],
                            "anchor": resolution["anchor"],
                            "line_anchor": resolution["line_anchor"],
                            **{
                                key: value for key, value in resolution.items()
                                if key not in {"line", "anchor", "line_anchor"}
                            },
                        })

    nodes.extend(external_nodes.values())
    nodes.sort(key=lambda item: str(item["id"]))
    links.sort(key=lambda item: (
        str(item.get("source", "")),
        str(item.get("target", "")),
        str(item.get("relation", "")),
        str(item.get("module", item.get("reference", ""))),
        int(item.get("line") or 0),
    ))
    unresolved.sort(key=lambda item: (
        str(item.get("source_file", "")),
        str(item.get("relation", "")),
        str(item.get("target", "")),
        int(item.get("line") or 0),
    ))
    by_type = Counter(str(row["file_type"]) for row in source_records)
    by_worktree_state = Counter(str(row["worktree_state"]) for row in source_records)
    relation_counts = Counter(str(edge["relation"]) for edge in links)
    unresolved_counts = Counter(str(row["relation"]) for row in unresolved)
    unique_source_target_pairs = {
        (str(edge["source"]), str(edge["target"])) for edge in links
    }
    graphify_projection = {
        "input_edge_records": len(links),
        "unique_directed_source_target_pairs": len(unique_source_target_pairs),
        "collapsed_parallel_edge_records": len(links) - len(unique_source_target_pairs),
        "note": (
            "Graphify 0.9.92 loads a simple graph and collapses repeated source-target "
            "pairs; this coverage report retains each parsed reference occurrence."
        ),
    }
    metadata = {
        "schema_version": 1,
        "graphify_version": GRAPHIFY_VERSION,
        "producer": "scripts/q3_graphify_source.py",
        "boundary": BOUNDARY,
        "head": head,
        "dirty_tracked_paths": dirty_paths,
        "tracked_source_count": len(source_records),
        "historical_source_count": sum(bool(row["historical"]) for row in source_records),
        "source_counts_by_type": dict(sorted(by_type.items())),
    }
    graph = {
        "directed": True,
        "multigraph": False,
        "graph": metadata,
        "nodes": nodes,
        "links": links,
        "hyperedges": [],
    }
    coverage = {
        "schema_version": 1,
        "boundary": BOUNDARY,
        "repository": {"head": head, "dirty_tracked_paths": dirty_paths},
        "counts": {
            "tracked_sources": len(source_records),
            "sources_by_type": dict(sorted(by_type.items())),
            "historical_sources": sum(bool(row["historical"]) for row in source_records),
            "missing_sources": by_worktree_state["missing"],
            "symlink_sources": by_worktree_state["symlink"],
            "unavailable_sources": by_worktree_state["missing"] + by_worktree_state["symlink"],
            "dirty_source_count": sum(bool(row["dirty"]) for row in source_records),
            "graph_nodes": len(nodes),
            "graph_edges": len(links),
            "edges_by_relation": dict(sorted(relation_counts.items())),
            "unresolved_references": len(unresolved),
            "unresolved_by_relation": dict(sorted(unresolved_counts.items())),
            "parser_errors": len(parser_errors),
            "source_errors": len(source_errors),
            "parser_limitations": len(PARSER_LIMITATIONS),
        },
        "graphify_projection": graphify_projection,
        "sources": source_records,
        "unresolved_references": unresolved,
        "parser_errors": parser_errors,
        "source_errors": source_errors,
        "parser_limitations": PARSER_LIMITATIONS,
    }
    return graph, coverage


def write_outputs(
    out_dir: Path,
    graph: dict[str, Any],
    coverage: dict[str, Any],
) -> tuple[Path, Path]:
    """Write both JSON outputs without replacing an existing file."""
    out_dir = out_dir.expanduser().resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    paths = (out_dir / "graph.json", out_dir / "coverage.json")
    existing = [path.name for path in paths if os.path.lexists(path)]
    if existing:
        raise GraphifySourceError("refusing to replace existing output(s): " + ", ".join(existing))
    payloads = (
        (paths[0], graph),
        (paths[1], coverage),
    )
    created: list[Path] = []
    try:
        for path, data in payloads:
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
            created.append(path)
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump(data, handle, ensure_ascii=False, indent=2, sort_keys=True)
                handle.write("\n")
    except Exception:
        for path in created:
            try:
                path.unlink()
            except OSError:
                pass
        raise
    return paths


def _print_summary(coverage: dict[str, Any], out_paths: tuple[Path, Path]) -> None:
    counts = coverage["counts"]
    print(f"graph: {out_paths[0]}")
    print(f"coverage: {out_paths[1]}")
    print(f"boundary: {BOUNDARY}")
    print(
        "tracked sources: "
        f"{counts['tracked_sources']} ({counts['sources_by_type']}); "
        f"historical={counts['historical_sources']}; "
        f"dirty tracked sources={counts['dirty_source_count']}"
    )
    print(
        f"edges={counts['graph_edges']}; unresolved references="
        f"{counts['unresolved_references']}; parser errors={counts['parser_errors']}"
    )
    for row in coverage["unresolved_references"][:MAX_PRINTED_ROWS]:
        print("unresolved: " + json.dumps(row, ensure_ascii=False, sort_keys=True))
    omitted = len(coverage["unresolved_references"]) - MAX_PRINTED_ROWS
    if omitted > 0:
        print(f"... {omitted} more unresolved references are in coverage.json")
    for row in coverage["parser_limitations"][:MAX_PRINTED_ROWS]:
        print(f"parser limitation [{row['parser']}]: {row['limitation']}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        required=True,
        help="explicit directory for new graph.json and coverage.json outputs",
    )
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[1]
    try:
        graph, coverage = build_graph(root)
        out_paths = write_outputs(args.out, graph, coverage)
    except (GraphifySourceError, OSError, ValueError) as exc:
        print(f"q3_graphify_source: {exc}", file=sys.stderr)
        return 2
    _print_summary(coverage, out_paths)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
