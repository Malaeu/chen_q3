#!/usr/bin/env python3
from __future__ import annotations

import shutil
import os
import subprocess
import sys
from datetime import datetime
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
Q3_ROOT = REPO_ROOT / "q3.lean.aristotle"
CACHE_ROOT = Q3_ROOT / ".qmd_cache"
VENDOR_ROOT = REPO_ROOT / "archive" / "subprojects" / "erdos-minimum-overlap"
COLLECTION = "erdos_minimum_overlap"
STABLE_STAGE_ROOT = CACHE_ROOT / "erdos_overlap_current"

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


def run_git(args: list[str], cwd: Path) -> str:
    proc = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise SystemExit(proc.stderr.strip() or proc.stdout.strip())
    return proc.stdout.strip()


def stage_root_for_run() -> Path:
    stamp = datetime.now().astimezone().strftime("%Y%m%d_%H%M%S_%f")
    return CACHE_ROOT / f"erdos_overlap_stage_{stamp}"


def ensure_vendor_clone() -> None:
    if not VENDOR_ROOT.exists():
        raise SystemExit(
            f"Vendor repo missing: {VENDOR_ROOT}\n"
            "Clone it first: git clone https://github.com/togethercomputer/erdos-minimum-overlap "
            "archive/subprojects/erdos-minimum-overlap"
        )


def copy_file(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def build_stage(stage_root: Path) -> tuple[int, str]:
    if stage_root.exists():
        shutil.rmtree(stage_root)
    stage_root.mkdir(parents=True, exist_ok=True)

    copied = 0
    for rel in ["README.md"]:
        src = VENDOR_ROOT / rel
        if src.is_file():
            copy_file(src, stage_root / rel)
            copied += 1

    solutions_dir = VENDOR_ROOT / "solutions"
    for src in sorted(solutions_dir.glob("*.py")):
        copy_file(src, stage_root / "solutions" / src.name)
        copied += 1

    commit = run_git(["git", "rev-parse", "HEAD"], cwd=VENDOR_ROOT)
    manifest = stage_root / "_manifest.md"
    manifest.write_text(
        "\n".join(
            [
                "# erdos_minimum_overlap collection manifest",
                "",
                f"Generated: {datetime.now().astimezone().isoformat(timespec='seconds')}",
                f"Vendor root: `{VENDOR_ROOT}`",
                f"Vendor commit: `{commit}`",
                "",
                "Scope:",
                "",
                "- `README.md`",
                "- `solutions/*.py`",
                "",
                "This collection is an external AI-math artifact corpus, not a theorem prover.",
                "It is useful as methodological context and retrieval memory, not as a direct",
                "replacement for Aristotle or Lean-facing proof synthesis.",
                "",
                f"Copied files: `{copied}`",
                "",
            ]
        ),
        encoding="utf-8",
    )
    return copied + 1, commit


def rebuild_collection(qmd: str, stage_root: Path) -> None:
    with qmd_lock("refresh_erdos_overlap"):
        listing = run_qmd([qmd, "collection", "list"])
        if f"{COLLECTION} (qmd://{COLLECTION}/)" in listing:
            run_qmd([qmd, "collection", "remove", COLLECTION])
        run_qmd([qmd, "collection", "add", str(stage_root), "--name", COLLECTION, "--mask", "**/*"])
        # Never use -f here: it recomputes every hash in every QMD collection and
        # turned a six-file optional corpus refresh into a multi-day CPU job.
        run_qmd([qmd, "embed"], timeout_s=1800.0)
        run_qmd([qmd, "cleanup"])


def promote_stage(pending: Path) -> Path:
    if STABLE_STAGE_ROOT.exists():
        shutil.rmtree(STABLE_STAGE_ROOT)
    os.replace(pending, STABLE_STAGE_ROOT)
    return STABLE_STAGE_ROOT


def main() -> int:
    ensure_vendor_clone()
    qmd = resolve_qmd()
    CACHE_ROOT.mkdir(parents=True, exist_ok=True)
    cleanup_stale_stage_dirs(CACHE_ROOT, prefix="erdos_overlap_stage")
    stage_root = stage_root_for_run()
    try:
        count, commit = build_stage(stage_root)
        print(f"Prepared {count} files for {COLLECTION} from commit {commit[:12]}")
        stable_stage = promote_stage(stage_root)
        rebuild_collection(qmd=qmd, stage_root=stable_stage)
        with qmd_lock("refresh_erdos_overlap_status"):
            print(run_qmd([qmd, "status"]).strip())
    finally:
        if stage_root.exists():
            shutil.rmtree(stage_root, ignore_errors=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
