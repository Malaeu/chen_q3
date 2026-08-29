#!/usr/bin/env python3
"""Proof-grade staleness evaluator shared by start, close, and phase-close."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import yaml

REPO = Path(__file__).resolve().parents[1]
DEFAULT_REGISTRY = REPO / "docs/cartographer/DERIVED_ARTIFACTS.yaml"
RECEIPT_DIR = Path("q3.lean.aristotle/.qmd_cache/workflow_derived_receipts")


class DependencyRegistryError(RuntimeError):
    pass


@dataclass(frozen=True)
class ArtifactStatus:
    artifact_id: str
    status: str
    dirty_inputs: tuple[str, ...]
    dirty_outputs: tuple[str, ...]
    detail: str
    repairable: bool


def applies_to(row: dict[str, Any], consumer: str | None) -> bool:
    consumers = row.get("consumers", ["session-start", "session-close", "phase-close", "workflow-plan"])
    if not isinstance(consumers, list) or not all(isinstance(item, str) for item in consumers):
        raise DependencyRegistryError("DERIVED_ARTIFACT_CONSUMERS_INVALID")
    return consumer is None or consumer in consumers


def _git(repo: Path, *args: str, check: bool = True) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=repo, capture_output=True, text=True
    )
    if check and proc.returncode != 0:
        raise DependencyRegistryError(proc.stderr.strip() or "git command failed")
    return proc.stdout


def load_registry(path: Path = DEFAULT_REGISTRY) -> list[dict[str, Any]]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (OSError, yaml.YAMLError) as exc:
        raise DependencyRegistryError(str(exc)) from exc
    if not isinstance(data, dict) or data.get("schema") != "q3_derived_artifact_registry.v1":
        raise DependencyRegistryError("DERIVED_ARTIFACT_REGISTRY_INVALID")
    rows = data.get("artifacts")
    if not isinstance(rows, list) or not rows:
        raise DependencyRegistryError("DERIVED_ARTIFACT_REGISTRY_EMPTY")
    seen: set[str] = set()
    for row in rows:
        required = {"id", "detector", "inputs", "outputs", "authority", "cost_tier"}
        if not isinstance(row, dict) or not required.issubset(row):
            raise DependencyRegistryError("DERIVED_ARTIFACT_ROW_INVALID")
        if row["id"] in seen:
            raise DependencyRegistryError("DERIVED_ARTIFACT_ID_DUPLICATE")
        applies_to(row, None)
        seen.add(row["id"])
    return rows


def _pathspecs(row: dict[str, Any]) -> list[str]:
    specs: list[str] = []
    for value in row["inputs"]:
        spec = str(value)
        specs.append(f":(glob){spec}" if any(char in spec for char in "*?[") else spec)
    return specs


def _matched_files(repo: Path, patterns: list[object]) -> list[Path]:
    matched: set[Path] = set()
    for value in patterns:
        pattern = str(value)
        candidates = repo.glob(pattern) if any(char in pattern for char in "*?[") else [repo / pattern]
        matched.update(path for path in candidates if path.is_file())
    return sorted(matched, key=lambda path: path.relative_to(repo).as_posix())


def _paths_digest(repo: Path, patterns: list[object]) -> tuple[str, dict[str, str]]:
    digest = hashlib.sha256()
    rows: dict[str, str] = {}
    for path in _matched_files(repo, patterns):
        relative = path.relative_to(repo).as_posix()
        payload = path.read_bytes()
        item_digest = hashlib.sha256(payload).hexdigest()
        rows[relative] = item_digest
        digest.update(relative.encode())
        digest.update(b"\0")
        digest.update(item_digest.encode())
        digest.update(b"\n")
    return digest.hexdigest(), rows


def _receipt_path(repo: Path, artifact_id: str) -> Path:
    return repo / RECEIPT_DIR / f"{artifact_id}.json"


def record_current_worktree(repo: Path, row: dict[str, Any]) -> None:
    input_digest, inputs = _paths_digest(repo, row["inputs"])
    output_digest, outputs = _paths_digest(repo, row["outputs"])
    payload = {
        "schema": "q3_derived_worktree_receipt.v1",
        "artifact_id": row["id"],
        "input_sha256": input_digest,
        "output_sha256": output_digest,
        "inputs": inputs,
        "outputs": outputs,
        "repair_command": row.get("repair_command"),
    }
    path = _receipt_path(repo, row["id"])
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, ensure_ascii=False, indent=2, sort_keys=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def _current_worktree_receipt_matches(repo: Path, row: dict[str, Any]) -> bool:
    path = _receipt_path(repo, row["id"])
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if payload.get("schema") != "q3_derived_worktree_receipt.v1" or payload.get("artifact_id") != row["id"]:
        return False
    input_digest, inputs = _paths_digest(repo, row["inputs"])
    output_digest, outputs = _paths_digest(repo, row["outputs"])
    return (
        payload.get("input_sha256") == input_digest
        and payload.get("output_sha256") == output_digest
        and payload.get("inputs") == inputs
        and payload.get("outputs") == outputs
        and payload.get("repair_command") == row.get("repair_command")
    )


def _git_derivation(repo: Path, row: dict[str, Any]) -> ArtifactStatus:
    outputs = [str(value) for value in row["outputs"]]
    missing = [path for path in outputs if not (repo / path).is_file()]
    if missing:
        return ArtifactStatus(row["id"], "MISSING", (), tuple(missing), "output missing", True)
    commits = []
    for output in outputs:
        commit = _git(repo, "log", "-1", "--format=%H", "--", output).strip()
        if not commit:
            return ArtifactStatus(
                row["id"], "UNTRACKED_OUTPUT", (), (output,), "no committed output baseline", True
            )
        commits.append(commit)
    # The oldest output baseline is the only safe common baseline.
    baseline = min(commits, key=lambda commit: int(_git(repo, "rev-list", "--count", commit).strip()))
    specs = _pathspecs(row)
    committed = tuple(
        line for line in _git(repo, "diff", "--name-only", baseline, "HEAD", "--", *specs).splitlines()
        if line
    )
    dirty = tuple(
        line[3:] for line in _git(
            repo, "status", "--porcelain=v1", "--untracked-files=all", "--", *specs
        ).splitlines() if len(line) > 3
    )
    dirty_outputs = tuple(
        line[3:] for line in _git(
            repo, "status", "--porcelain=v1", "--untracked-files=all", "--", *outputs
        ).splitlines() if len(line) > 3
    )
    changed = tuple(sorted(set(committed + dirty)))
    if changed:
        if _current_worktree_receipt_matches(repo, row):
            return ArtifactStatus(
                row["id"],
                "CURRENT_WORKTREE",
                changed,
                dirty_outputs,
                "generator receipt matches current input and output bytes",
                False,
            )
        return ArtifactStatus(row["id"], "STALE", changed, dirty_outputs, f"inputs changed since {baseline[:12]}", True)
    if dirty_outputs:
        return ArtifactStatus(row["id"], "DIRTY_OUTPUT", (), dirty_outputs, "output differs from committed baseline", False)
    return ArtifactStatus(row["id"], "FRESH", (), (), f"inputs unchanged since {baseline[:12]}", False)


def _needs_cards(repo: Path, row: dict[str, Any]) -> ArtifactStatus:
    refs = repo / "docs/routeB_bus/litreview/REFERENCES.md"
    if not refs.is_file():
        return ArtifactStatus(row["id"], "MISSING", (), (str(refs.relative_to(repo)),), "REFERENCES missing", False)
    contradictions: list[str] = []
    manual: list[str] = []
    for number, line in enumerate(refs.read_text(encoding="utf-8").splitlines(), 1):
        if "NEEDS_CARDS" not in line:
            continue
        candidates = re.findall(r"`([^`]*_USAGE_CARDS\.md)`", line)
        existing = [name for name in candidates if (refs.parent / Path(name).name).is_file()]
        if existing:
            contradictions.append(f"REFERENCES.md:{number}:{existing[0]}")
        else:
            manual.append(f"REFERENCES.md:{number}")
    if contradictions:
        return ArtifactStatus(row["id"], "STALE", tuple(contradictions), (), "NEEDS_CARDS names an existing card", False)
    if manual:
        return ArtifactStatus(row["id"], "MANUAL_DEBT", tuple(manual), (), "NEEDS_CARDS lacks an exact existing card binding", False)
    return ArtifactStatus(row["id"], "FRESH", (), (), "no unresolved NEEDS_CARDS rows", False)


def _command_check(repo: Path, row: dict[str, Any]) -> ArtifactStatus:
    command = row.get("check_command")
    if not isinstance(command, list) or not command or not all(isinstance(item, str) for item in command):
        raise DependencyRegistryError("DERIVED_ARTIFACT_CHECK_COMMAND_INVALID")
    proc = subprocess.run(command, cwd=repo, capture_output=True, text=True)
    detail = (proc.stderr.strip() or proc.stdout.strip() or f"exit={proc.returncode}")[-2000:]
    if proc.returncode == 0:
        return ArtifactStatus(row["id"], "FRESH", (), (), detail, False)
    repair_exit_codes = row.get("repair_exit_codes", [1])
    if (
        not isinstance(repair_exit_codes, list)
        or not all(isinstance(item, int) for item in repair_exit_codes)
    ):
        raise DependencyRegistryError("DERIVED_ARTIFACT_REPAIR_EXIT_CODES_INVALID")
    if proc.returncode in repair_exit_codes:
        return ArtifactStatus(row["id"], "STALE", (), tuple(str(item) for item in row["outputs"]), detail, bool(row.get("repair_command")))
    return ArtifactStatus(row["id"], "CHECK_FAILED", (), tuple(str(item) for item in row["outputs"]), detail, False)


def evaluate(repo: Path, row: dict[str, Any]) -> ArtifactStatus:
    if row["detector"] == "GIT_DERIVATION":
        return _git_derivation(repo, row)
    if row["detector"] == "NEEDS_CARDS_CONSISTENCY":
        return _needs_cards(repo, row)
    if row["detector"] == "COMMAND_CHECK":
        return _command_check(repo, row)
    raise DependencyRegistryError(f"DERIVED_ARTIFACT_DETECTOR_UNKNOWN:{row['detector']}")


def statuses(
    repo: Path = REPO,
    registry: Path = DEFAULT_REGISTRY,
    *,
    consumer: str | None = None,
) -> list[ArtifactStatus]:
    return [evaluate(repo, row) for row in load_registry(registry) if applies_to(row, consumer)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["status", "affected-by"])
    parser.add_argument("value", nargs="?")
    parser.add_argument("--artifact")
    parser.add_argument("--consumer")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    args = parser.parse_args()
    try:
        rows = load_registry(args.registry)
        if args.command == "affected-by":
            if not args.value:
                raise DependencyRegistryError("affected-by requires a path")
            selected = [row["id"] for row in rows if any(Path(args.value).match(spec) for spec in row["inputs"])]
            print(json.dumps(selected) if args.json else "\n".join(selected))
            return 0
        selected_rows = [
            row for row in rows
            if (not args.artifact or row["id"] == args.artifact) and applies_to(row, args.consumer)
        ]
        if args.artifact and not selected_rows:
            raise DependencyRegistryError("DERIVED_ARTIFACT_UNKNOWN")
        result = [evaluate(args.root.resolve(), row) for row in selected_rows]
    except DependencyRegistryError as exc:
        print(exc, file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps([asdict(item) for item in result], ensure_ascii=False, indent=2))
    else:
        for item in result:
            suffix = ",".join(item.dirty_inputs) if item.dirty_inputs else item.detail
            print(f"{item.artifact_id}\t{item.status}\t{suffix}")
    return 1 if any(item.status not in {"FRESH", "CURRENT_WORKTREE"} for item in result) else 0


if __name__ == "__main__":
    raise SystemExit(main())
