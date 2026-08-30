#!/usr/bin/env python3
"""Canonical curated-source selection and deterministic q3_docs identity."""

from __future__ import annotations

import fnmatch
import hashlib
import json
import platform
import sqlite3
from collections import Counter
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
MAX_SEMANTIC_LEAN_BYTES = 20_000

DIRECT_FILES = (
    "SESSION_ENTRY.md",
    "IMPLEMENTATION_PLAN.md",
    "docs/CODEX_CONTROL.md",
    "docs/GENEALOGY.md",
    "docs/Progress_Log.md",
    "docs/routeB_bus/RESEARCH_DEPENDENCY_CLASSIFICATION.md",
    "docs/RECORDING_RULES.md",
    "docs/GLOSSARY.md",
    "docs/cartographer/TOOLS.yaml",
    "orchestrator/KNOWLEDGE_SPINE.md",
    "orchestrator/AUTOPSY_SCHEMA.md",
    "orchestrator/SENSOR_CONTRACTS.md",
    "q3.lean.aristotle/FORMALIZATION_STATS.md",
    "q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md",
    "q3.lean.aristotle/PROJECT_ORCHESTRATOR.md",
    "q3.lean.aristotle/PROJECT_WORKFLOW.md",
    "q3.lean.aristotle/docs/AXIOM_CLOSURE_ANALYSIS.md",
    "q3.lean.aristotle/docs/CHAIN_STATUS.md",
    "q3.lean.aristotle/docs/ERRORS_DESTROYER.md",
    "q3.lean.aristotle/docs/INSIGHTS.md",
    "q3.lean.aristotle/docs/LATEX_PROOF_GAP_ANALYSIS.md",
    "q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md",
    "q3.lean.aristotle/docs/PROJECT_SPECS.md",
    "q3.lean.aristotle/docs/Q3_PDF_STRUCTURE.md",
    "q3.lean.aristotle/docs/struktura_q3_with_mapping_toLEAN.md",
    "full/RH_Q3.tex",
)

GLOB_PATTERNS = (
    "docs/routeB_bus/**/*.md",
    "q3.lean.aristotle/docs/insights/**/*.md",
    "q3.lean.aristotle/docs/reviewed_notes/**/*.md",
    "q3.lean.aristotle/ACTIVE/**/*.md",
    "full/sections/**/*.tex",
    "full/appendix/*.tex",
    "q3.lean.aristotle/Q3/**/*.lean",
)

REVIEWED_NOTES_PREFIX = "q3.lean.aristotle/docs/reviewed_notes/"
REVIEWED_SAFE_MARKER = "- safe for embeddings: `yes`"

EXCLUDE_PATTERNS = (
    "**/.lake/**",
    "q3.lean.aristotle/**/.lake/**",
    "q3.lean.aristotle/docs/legacy/**",
    "q3.lean.aristotle/docs/ChatGPT_*.md",
    "q3.lean.aristotle/docs/incoming_notes/**",
    "q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_QUEUE.md",
    "q3.lean.aristotle/ACTIVE/aristotle/proshka_context_single_scale.md",
    "q3.lean.aristotle/ACTIVE/aristotle/queue/**",
    "q3.lean.aristotle/ACTIVE/pipeline/oracle_questions/**",
    "q3.lean.aristotle/ACTIVE/refs/legacy_two_scale_index.md",
    # Dormant/stale control surfaces are evidence, not current semantic authority.
    "q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md",
    "q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/**",
    "q3.lean.aristotle/ACTIVE/pipeline/PROBLEM_SOLVER_PROMPT_RU.md",
    "q3.lean.aristotle/ACTIVE/COGNITIVE_GOVERNOR.md",
    "q3.lean.aristotle/ACTIVE/requests/**/_backups/**",
    "q3.lean.aristotle/ACTIVE/requests/**/raw/**",
    "q3.lean.aristotle/Q3/Archive/**",
    "q3.lean.aristotle/Q3/Clean/**",
    "q3.lean.aristotle/Q3/Proofs/PrimeCert/**",
)


def matches_any(rel: str, patterns: tuple[str, ...] = EXCLUDE_PATTERNS) -> bool:
    normalized = rel.replace("\\", "/")
    return any(fnmatch.fnmatch(normalized, pattern) for pattern in patterns)


def reviewed_note_is_safe(path: Path, rel: str) -> bool:
    normalized = rel.replace("\\", "/")
    if not normalized.startswith(REVIEWED_NOTES_PREFIX):
        return True
    if path.name in {"README.md", "TEMPLATE.md"}:
        return False
    return REVIEWED_SAFE_MARKER in path.read_text(encoding="utf-8")


def collect_sources(repo_root: Path = REPO_ROOT) -> list[Path]:
    seen: set[str] = set()
    files: list[Path] = []

    for rel in DIRECT_FILES:
        path = repo_root / rel
        if (
            path.is_file()
            and rel not in seen
            and not matches_any(rel)
            and reviewed_note_is_safe(path, rel)
        ):
            seen.add(rel)
            files.append(path)

    for pattern in GLOB_PATTERNS:
        for path in sorted(repo_root.glob(pattern)):
            if not path.is_file():
                continue
            rel = path.relative_to(repo_root).as_posix()
            if rel in seen or matches_any(rel) or not reviewed_note_is_safe(path, rel):
                continue
            if path.suffix == ".lean" and path.stat().st_size > MAX_SEMANTIC_LEAN_BYTES:
                continue
            seen.add(rel)
            files.append(path)

    return sorted(files, key=lambda path: path.relative_to(repo_root).as_posix())


def corpus_hash(files: list[Path], repo_root: Path = REPO_ROOT) -> str:
    """Hash framed repo-relative paths and bytes, independent of mtimes/order."""
    digest = hashlib.sha256()
    for path in sorted(files, key=lambda item: item.relative_to(repo_root).as_posix()):
        rel = path.relative_to(repo_root).as_posix().encode("utf-8")
        body = path.read_bytes()
        digest.update(len(rel).to_bytes(8, "big"))
        digest.update(rel)
        digest.update(len(body).to_bytes(8, "big"))
        digest.update(body)
    return digest.hexdigest()


def corpus_snapshot(
    repo_root: Path = REPO_ROOT,
    files: list[Path] | None = None,
) -> dict[str, object]:
    selected = collect_sources(repo_root) if files is None else files
    suffixes = Counter(path.suffix.lower() or "<none>" for path in selected)
    known = {".md", ".lean", ".tex", ".yaml", ".yml"}
    breakdown = {
        "markdown": suffixes[".md"],
        "lean": suffixes[".lean"],
        "tex": suffixes[".tex"],
        "yaml": suffixes[".yaml"] + suffixes[".yml"],
        "other": sum(count for suffix, count in suffixes.items() if suffix not in known),
    }
    return {
        "schema": "q3_docs_corpus.v1",
        "sha256": corpus_hash(selected, repo_root),
        "file_count": len(selected),
        "expected_collection_file_count": len(selected) + 1,
        "total_bytes": sum(path.stat().st_size for path in selected),
        "breakdown": breakdown,
    }


def semantic_machine_id() -> str:
    machine_id_path = Path("/etc/machine-id")
    durable = (
        machine_id_path.read_text(encoding="utf-8").strip()
        if machine_id_path.is_file()
        else platform.node()
    )
    return hashlib.sha256(durable.encode("utf-8")).hexdigest()


def qmd_index_probe(
    *,
    collection: str = "q3_docs",
    config_path: Path | None = None,
    index_path: Path | None = None,
) -> dict[str, object]:
    config = config_path or Path.home() / ".config" / "qmd" / "index.yml"
    index = index_path or Path.home() / ".cache" / "qmd" / "index.sqlite"
    if not config.is_file() or not index.is_file():
        raise RuntimeError("qmd config or index.sqlite is missing")
    payload = yaml.safe_load(config.read_text(encoding="utf-8")) or {}
    collections = payload.get("collections")
    row = collections.get(collection) if isinstance(collections, dict) else None
    if not isinstance(row, dict) or not row.get("path"):
        raise RuntimeError(f"qmd collection is missing from config: {collection}")
    stat = index.stat()
    identity_body = json.dumps(
        {
            "machine_id": semantic_machine_id(),
            "index_path": str(index.resolve()),
            "device": stat.st_dev,
            "inode": stat.st_ino,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    conn = sqlite3.connect(f"file:{index}?mode=ro", uri=True)
    try:
        file_count = int(
            conn.execute(
                "SELECT COUNT(*) FROM documents WHERE collection=? AND active=1",
                (collection,),
            ).fetchone()[0]
        )
    finally:
        conn.close()
    return {
        "identity": hashlib.sha256(identity_body).hexdigest(),
        "index_path": str(index.resolve()),
        "collection_root": str(Path(str(row["path"])).expanduser().resolve()),
        "collection_mask": str(row.get("pattern") or row.get("mask") or ""),
        "collection_file_count": file_count,
    }
