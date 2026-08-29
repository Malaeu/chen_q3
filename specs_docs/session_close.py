#!/usr/bin/env python3
"""Incremental Q3 session close: repair derived artifacts, verify, and report debt."""

from __future__ import annotations

import argparse
import datetime as dt
import os
import subprocess
import sys
import tempfile
from dataclasses import replace
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import dependency_registry  # noqa: E402


def repair_derived(
    repo: Path,
    registry_path: Path,
    *,
    repair: bool,
    consumer: str = "session-close",
) -> tuple[list[str], list[dependency_registry.ArtifactStatus]]:
    rows = [
        row for row in dependency_registry.load_registry(registry_path)
        if dependency_registry.applies_to(row, consumer)
    ]
    executed: list[str] = []
    for row in rows:
        state = dependency_registry.evaluate(repo, row)
        command = row.get("repair_command")
        if state.status in {"STALE", "MISSING"} and state.repairable and command and repair:
            proc = subprocess.run([str(part) for part in command], cwd=repo)
            if proc.returncode != 0:
                raise RuntimeError(f"DERIVED_REPAIR_FAILED:{row['id']}:{proc.returncode}")
            dependency_registry.record_current_worktree(repo, row)
            executed.append(row["id"])
    final = []
    for row in rows:
        state = dependency_registry.evaluate(repo, row)
        if row["id"] in executed and state.status == "STALE":
            state = replace(
                state,
                status="CURRENT_WORKTREE",
                detail="generator succeeded for current uncommitted inputs",
                repairable=False,
            )
        final.append(state)
    return executed, final


def dirty_split(repo: Path, owned_paths: list[str]) -> tuple[list[str], list[str]]:
    lines = subprocess.run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        cwd=repo, check=True, capture_output=True, text=True,
    ).stdout.splitlines()
    receipt_prefix = dependency_registry.RECEIPT_DIR.as_posix().rstrip("/") + "/"
    paths = [
        line[3:] for line in lines
        if len(line) > 3 and not line[3:].startswith(receipt_prefix)
    ]
    owned: list[str] = []
    foreign: list[str] = []
    for path in paths:
        if any(path == prefix or path.startswith(prefix.rstrip("/") + "/") for prefix in owned_paths):
            owned.append(path)
        else:
            foreign.append(path)
    return sorted(owned), sorted(foreign)


def verify_owned_lean(repo: Path, owned: list[str], *, run_kernel: bool) -> list[str]:
    lean = [path for path in owned if path.endswith(".lean") and path.startswith("q3.lean.aristotle/")]
    if lean and not run_kernel:
        raise RuntimeError("KERNEL_GATE_REQUIRED:" + ",".join(lean))
    checked: list[str] = []
    for path in lean:
        proc = subprocess.run(["bash", "scripts/q3_check.sh", path], cwd=repo)
        if proc.returncode != 0:
            raise RuntimeError(f"KERNEL_GATE_FAILED:{path}:{proc.returncode}")
        checked.append(path)
    return checked


def render_protocol(*, head: str, executed: list[str], statuses: list[dependency_registry.ArtifactStatus], owned: list[str], foreign: list[str], checked: list[str]) -> str:
    stamp = dt.datetime.now(dt.timezone.utc).isoformat()
    lines = [
        "# SESSION PROTOCOL — GENERATED SKELETON",
        "",
        f"Generated: {stamp}",
        f"HEAD: `{head}`",
        "",
        "## Derived repairs",
        "",
        *(f"- `{item}`" for item in executed),
        *( ["- none"] if not executed else [] ),
        "",
        "## Derived status",
        "",
        *(f"- `{item.artifact_id}`: `{item.status}` — {item.detail}" for item in statuses),
        "",
        "## Kernel checked",
        "",
        *(f"- `{item}`" for item in checked),
        *( ["- none"] if not checked else [] ),
        "",
        "## Owned dirty paths",
        "",
        *(f"- `{item}`" for item in owned),
        *( ["- none"] if not owned else [] ),
        "",
        "## Foreign dirty paths — preserved, not blockers",
        "",
        *(f"- `{item}`" for item in foreign),
        *( ["- none"] if not foreign else [] ),
        "",
        "## Manual closeout",
        "",
        "- CLOSES: TODO",
        "- OPENS: TODO",
        "- assembly debt: TODO",
        "- insight: TODO",
        "- commit/push: not performed by this tool",
        "- PX_RH_CLAIM: NOT_MADE",
        "",
    ]
    return "\n".join(lines)


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--registry", type=Path, default=dependency_registry.DEFAULT_REGISTRY)
    parser.add_argument("--owned-path", action="append", default=[])
    parser.add_argument("--repair", action="store_true")
    parser.add_argument("--run-kernel", action="store_true")
    parser.add_argument("--protocol-out", type=Path)
    args = parser.parse_args()
    repo = args.root.resolve()
    try:
        executed, statuses = repair_derived(repo, args.registry.resolve(), repair=args.repair)
        owned, foreign = dirty_split(repo, args.owned_path)
        checked = verify_owned_lean(repo, owned, run_kernel=args.run_kernel)
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, capture_output=True, text=True).stdout.strip()
        protocol = render_protocol(head=head, executed=executed, statuses=statuses, owned=owned, foreign=foreign, checked=checked)
        if args.protocol_out:
            atomic_write(args.protocol_out, protocol)
        else:
            print(protocol, end="")
    except (RuntimeError, dependency_registry.DependencyRegistryError, subprocess.CalledProcessError) as exc:
        print(exc)
        return 2
    residual = [item for item in statuses if item.status not in {"FRESH", "CURRENT_WORKTREE"}]
    return 1 if residual else 0


if __name__ == "__main__":
    raise SystemExit(main())
