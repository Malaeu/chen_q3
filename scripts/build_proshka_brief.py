#!/usr/bin/env python3
"""Build a Proshka context pack from the Q3 repo.

This script is link-first but can inline key files for a single packed brief.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import os
import pathlib
import subprocess
import sys
from typing import Iterable, List, Optional, Set, Tuple


def _run(cmd: List[str], cwd: pathlib.Path) -> str:
    proc = subprocess.run(
        cmd, cwd=str(cwd), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
    )
    if proc.returncode != 0:
        raise RuntimeError(f"Command failed: {' '.join(cmd)}\n{proc.stderr.strip()}")
    return proc.stdout


def _repo_root(start: Optional[pathlib.Path]) -> pathlib.Path:
    if start is None:
        start = pathlib.Path.cwd()
    try:
        out = _run(["git", "rev-parse", "--show-toplevel"], cwd=start).strip()
        if out:
            return pathlib.Path(out)
    except Exception:
        pass
    return start.resolve()


def _read_text(path: pathlib.Path, max_lines: int) -> str:
    try:
        data = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        data = path.read_text(encoding="latin-1")
    lines = data.splitlines()
    if max_lines > 0 and len(lines) > max_lines:
        lines = lines[:max_lines] + [f"... [truncated {len(lines) - max_lines} lines]"]
    return "\n".join(lines)


def _emit_section(out: List[str], title: str, body: str) -> None:
    out.append("\n" + "#" * 2 + " " + title)
    out.append(body.rstrip())


def _expand_globs(repo: pathlib.Path, globs: Iterable[str]) -> List[pathlib.Path]:
    paths: List[pathlib.Path] = []
    for g in globs:
        for p in repo.glob(g):
            if p.is_file():
                paths.append(p)
    return paths


def _unique(paths: Iterable[pathlib.Path]) -> List[pathlib.Path]:
    seen: Set[pathlib.Path] = set()
    out: List[pathlib.Path] = []
    for p in paths:
        rp = p.resolve()
        if rp not in seen:
            seen.add(rp)
            out.append(p)
    return out


def _git_log(repo: pathlib.Path, max_commits: int, rev_range: Optional[str]) -> str:
    if rev_range:
        cmd = ["git", "log", "--oneline", rev_range]
    else:
        cmd = ["git", "log", "--oneline", f"-n{max_commits}"]
    return _run(cmd, cwd=repo)


def _git_diff(repo: pathlib.Path, rev_range: Optional[str], max_lines: int, context: int) -> str:
    cmd = ["git", "diff", f"-U{context}"]
    if rev_range:
        cmd.append(rev_range)
    out = _run(cmd, cwd=repo)
    lines = out.splitlines()
    if max_lines > 0 and len(lines) > max_lines:
        lines = lines[:max_lines] + [f"... [truncated {len(lines) - max_lines} lines]"]
    return "\n".join(lines)


def _default_includes(repo: pathlib.Path) -> List[pathlib.Path]:
    base = repo / "full" / "q3.lean.aristotle"
    return [
        base / "ACTIVE" / "KNOWLEDGE_BASE.md",
        base / "ACTIVE" / "chain_status.md",
        base / "ACTIVE" / "orchestrator.md",
        base / "ACTIVE" / "SPECS_INDEX.md",
        base / "ACTIVE" / "Q3_BLOCK_MAP.md",
        base / "ACTIVE" / "PROBLEM_SOLVER_PROMPT_RU.md",
        base / "PROSHKA_REQUEST_4.md",
        base / "docs" / "PROJECT_SPECS.md",
        base / "docs" / "insights" / "rh_q3_invariants_contract_2026_01_16.md",
        base / "docs" / "INSIGHTS.md",
        base / "docs" / "insights" / "INDEX.md",
        base / "Q3" / "Axioms.lean",
        base / "Q3" / "Proofs" / "ShiftedWindows.lean",
        base / "Q3" / "Proofs" / "P_A_Toeplitz_bridge_defs.lean",
        base / "Q3" / "Proofs" / "P_A_Toeplitz_bridge.lean",
        base / "Q3" / "Proofs" / "Rayleigh_basis0_of_A3.lean",
        base / "Q3" / "Proofs" / "RKHS_cap_rayleigh.lean",
        base / "Q3" / "Proofs" / "T_P_comp_utils.lean",
    ]


def _parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Build Proshka context pack")
    ap.add_argument("--repo", default=None, help="Repository root (auto-detected if omitted)")
    ap.add_argument("--out", default=None, help="Output path (stdout if omitted)")
    ap.add_argument(
        "--mode", default="full", choices=["tight", "normal", "full"], help="Recall profile"
    )
    ap.add_argument("--range", dest="rev_range", default=None, help="Git range REV..REV")
    ap.add_argument("--max-commits", type=int, default=None, help="Max commits for git log")
    ap.add_argument("--include-file", action="append", default=[], help="Repeatable file include")
    ap.add_argument("--include-glob", action="append", default=[], help="Repeatable glob include")
    ap.add_argument(
        "--max-file-lines", type=int, default=None, help="Line cap per file (0 = no cap)"
    )
    ap.add_argument("--include-diff", action="store_true", help="Include git diff")
    ap.add_argument("--no-diff", action="store_true", help="Disable git diff")
    ap.add_argument("--max-diff-lines", type=int, default=None, help="Line cap for diff")
    ap.add_argument("--diff-context", type=int, default=None, help="Diff context lines")
    ap.add_argument(
        "--no-default-files", action="store_true", help="Do not include default file list"
    )
    return ap.parse_args()


def main() -> int:
    args = _parse_args()
    repo = _repo_root(pathlib.Path(args.repo) if args.repo else None)

    if args.mode == "tight":
        max_commits = 10
        max_file_lines = 200
        max_diff_lines = 0
        diff_context = 3
    elif args.mode == "normal":
        max_commits = 20
        max_file_lines = 400
        max_diff_lines = 800
        diff_context = 3
    else:
        max_commits = 40
        max_file_lines = 800
        max_diff_lines = 2000
        diff_context = 3

    if args.max_commits is not None:
        max_commits = args.max_commits
    if args.max_file_lines is not None:
        max_file_lines = args.max_file_lines
    if args.max_diff_lines is not None:
        max_diff_lines = args.max_diff_lines
    if args.diff_context is not None:
        diff_context = args.diff_context

    include_diff = args.include_diff and not args.no_diff

    out: List[str] = []
    header = [
        "# PROSHKA CONTEXT PACK",
        f"Generated: {_dt.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        f"Repo: {repo}",
        "",
        "This pack is intended for Proshka. It inlines key files and recent git context.",
    ]
    out.append("\n".join(header))

    # Git status/log
    try:
        status = _run(["git", "status", "-sb"], cwd=repo)
    except Exception as e:
        status = f"[git status unavailable] {e}"
    _emit_section(out, "Git status", status)

    try:
        log = _git_log(repo, max_commits=max_commits, rev_range=args.rev_range)
    except Exception as e:
        log = f"[git log unavailable] {e}"
    _emit_section(out, "Git log", log)

    if include_diff:
        try:
            diff = _git_diff(
                repo, rev_range=args.rev_range, max_lines=max_diff_lines, context=diff_context
            )
        except Exception as e:
            diff = f"[git diff unavailable] {e}"
        _emit_section(out, "Git diff", diff)

    # Files
    files: List[pathlib.Path] = []
    if not args.no_default_files:
        files.extend(_default_includes(repo))
    for f in args.include_file:
        files.append((repo / f).resolve() if not os.path.isabs(f) else pathlib.Path(f))
    files.extend(_expand_globs(repo, args.include_glob))
    files = _unique([p for p in files if p.exists()])

    for path in files:
        rel = path.relative_to(repo) if path.is_relative_to(repo) else path
        body = _read_text(path, max_lines=max_file_lines)
        _emit_section(out, f"File: {rel}", body)

    result = "\n\n".join(out).rstrip() + "\n"
    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(result, encoding="utf-8")
    else:
        sys.stdout.write(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
