#!/usr/bin/env python3
from __future__ import annotations

import argparse
import fnmatch
import os
import shutil
import subprocess
import sys
from collections import Counter
from datetime import datetime
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
Q3_ROOT = REPO_ROOT / "q3.lean.aristotle"
CACHE_ROOT = Q3_ROOT / ".qmd_cache"
COLLECTION = "q3_docs"

DIRECT_FILES = [
    "SESSION_ENTRY.md",
    "IMPLEMENTATION_PLAN.md",
    "q3.lean.aristotle/CLAUDE.md",
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
]

GLOB_PATTERNS = [
    "q3.lean.aristotle/docs/insights/**/*.md",
    "q3.lean.aristotle/docs/reviewed_notes/**/*.md",
    "q3.lean.aristotle/ACTIVE/**/*.md",
    "full/sections/**/*.tex",
    "full/appendix/*.tex",
    "q3.lean.aristotle/Q3/**/*.lean",
]

REVIEWED_NOTES_PREFIX = "q3.lean.aristotle/docs/reviewed_notes/"
REVIEWED_SAFE_MARKER = "- safe for embeddings: `yes`"

EXCLUDE_PATTERNS = [
    "q3.lean.aristotle/docs/legacy/**",
    "q3.lean.aristotle/docs/ChatGPT_*.md",
    "q3.lean.aristotle/docs/incoming_notes/**",
    "q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_QUEUE.md",
    "q3.lean.aristotle/ACTIVE/aristotle/proshka_context_single_scale.md",
    "q3.lean.aristotle/ACTIVE/aristotle/queue/**",
    "q3.lean.aristotle/ACTIVE/refs/legacy_two_scale_index.md",
    "q3.lean.aristotle/ACTIVE/requests/**",
    "q3.lean.aristotle/Q3/Archive/**",
    "q3.lean.aristotle/Q3/Clean/**",
    "q3.lean.aristotle/Q3/Proofs/PrimeCert/**",
]

ROOT_SCRIPTS = REPO_ROOT / "scripts"
if str(ROOT_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(ROOT_SCRIPTS))

from qmd_ops import cleanup_stale_stage_dirs, qmd_lock, run_qmd  # noqa: E402


def resolve_qmd() -> str:
    found = shutil.which("qmd")
    if found:
        return found
    bun_qmd = Path.home() / ".bun" / "bin" / "qmd"
    if bun_qmd.exists():
        return str(bun_qmd)
    raise SystemExit("qmd not found on PATH and ~/.bun/bin/qmd is missing")


def matches_any(rel: str, patterns: list[str]) -> bool:
    rel = rel.replace("\\", "/")
    return any(fnmatch.fnmatch(rel, pattern) for pattern in patterns)


def reviewed_note_is_safe(path: Path, rel: str) -> bool:
    rel = rel.replace("\\", "/")
    if not rel.startswith(REVIEWED_NOTES_PREFIX):
        return True
    if path.name in {"README.md", "TEMPLATE.md"}:
        return False
    text = path.read_text(encoding="utf-8")
    return REVIEWED_SAFE_MARKER in text


def collect_sources() -> list[Path]:
    seen: set[str] = set()
    files: list[Path] = []

    for rel in DIRECT_FILES:
        path = REPO_ROOT / rel
        if (
            path.is_file()
            and rel not in seen
            and not matches_any(rel, EXCLUDE_PATTERNS)
            and reviewed_note_is_safe(path, rel)
        ):
            seen.add(rel)
            files.append(path)

    for pattern in GLOB_PATTERNS:
        for path in sorted(REPO_ROOT.glob(pattern)):
            if not path.is_file():
                continue
            rel = str(path.relative_to(REPO_ROOT))
            if rel in seen or matches_any(rel, EXCLUDE_PATTERNS) or not reviewed_note_is_safe(path, rel):
                continue
            seen.add(rel)
            files.append(path)

    return files


def stage_root_for_run() -> Path:
    stamp = datetime.now().astimezone().strftime("%Y%m%d_%H%M%S_%f")
    return CACHE_ROOT / f"q3_docs_stage_{stamp}_{os.getpid()}"


def build_stage(stage_root: Path, files: list[Path]) -> Counter:
    if stage_root.exists():
        shutil.rmtree(stage_root)
    stage_root.mkdir(parents=True, exist_ok=True)

    counts: Counter[str] = Counter()
    for src in files:
        rel = src.relative_to(REPO_ROOT)
        dst = stage_root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        counts[src.suffix or "<none>"] += 1

    manifest = stage_root / "_manifest.md"
    lines = [
        "# q3_docs manifest",
        "",
        f"Generated: {datetime.now().astimezone().isoformat(timespec='seconds')}",
        f"Collection: `{COLLECTION}`",
        f"Repo root: `{REPO_ROOT}`",
        f"Stage root: `{stage_root}`",
        "",
        "Curated scope:",
        "",
        "- current control and workflow docs,",
        "- active manuscript TeX,",
        "- live Q3 Lean files excluding `Archive`, `Clean`, and heavy `PrimeCert` shards,",
        "- only reviewed notes marked `safe for embeddings: yes` are promoted from `docs/reviewed_notes/`,",
        "- raw inbox notes, extracted zip payloads, and archived sources under `docs/incoming_notes/` are excluded until distilled,",
        "- no transcript dumps or old queue artifacts.",
        "",
        f"Total files: `{len(files)}`",
        f"Markdown: `{counts['.md']}`",
        f"TeX: `{counts['.tex']}`",
        f"Lean: `{counts['.lean']}`",
        "",
    ]
    manifest.write_text("\n".join(lines), encoding="utf-8")
    return counts


def run(cmd: list[str], cwd: Path | None = None) -> str:
    try:
        return run_qmd(cmd, cwd=cwd)
    except RuntimeError as exc:
        raise SystemExit(str(exc)) from exc


def rebuild_collection(qmd: str, stage_root: Path, embed: bool) -> None:
    with qmd_lock("refresh_q3_docs"):
        listing = run([qmd, "collection", "list"])
        if f"{COLLECTION} (qmd://{COLLECTION}/)" in listing:
            run([qmd, "collection", "remove", COLLECTION])

        run([qmd, "collection", "add", str(stage_root), "--name", COLLECTION, "--mask", "**/*"])
        if embed:
            run([qmd, "embed", "-f"])
        run([qmd, "cleanup"])


def main() -> int:
    ap = argparse.ArgumentParser(description="Rebuild curated q3_docs qmd collection")
    ap.add_argument("--no-embed", action="store_true", help="rebuild collection without qmd embed -f")
    ap.add_argument("--print-files", action="store_true", help="print included files")
    args = ap.parse_args()

    qmd = resolve_qmd()
    files = collect_sources()
    CACHE_ROOT.mkdir(parents=True, exist_ok=True)
    cleanup_stale_stage_dirs(CACHE_ROOT)
    stage_root = stage_root_for_run()

    try:
        counts = build_stage(stage_root, files)

        if args.print_files:
            for path in files:
                print(path.relative_to(REPO_ROOT))

        print(
            f"Prepared {len(files)} files for {COLLECTION}: "
            f"{counts['.md']} md, {counts['.tex']} tex, {counts['.lean']} lean"
        )
        rebuild_collection(qmd=qmd, stage_root=stage_root, embed=not args.no_embed)
        with qmd_lock("refresh_q3_docs_status"):
            print(run([qmd, "status"]).strip())
    finally:
        if stage_root.exists():
            shutil.rmtree(stage_root, ignore_errors=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
