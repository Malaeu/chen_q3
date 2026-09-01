#!/usr/bin/env python3
"""Pure Control-v10 startup selection and a non-authoritative v9 shadow view.

The shadow builder is deliberately incapable of authorizing execution.  It
reads only repository files and local git metadata; it does not call any
session, control-plane, briefing, lease, or dispatch runtime.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import stat
import subprocess
from dataclasses import asdict, dataclass, replace
from pathlib import Path, PurePosixPath
from typing import Any, BinaryIO

import yaml

from orchestrator.routeb_goal_state import (
    PAUSED_STATUSES,
    STATUS_RE,
    goal_machine_header_text,
    load_unique_yaml,
)

CONTROL_REL = PurePosixPath("docs/CODEX_CONTROL.md")
BUS_REL = PurePosixPath("docs/routeB_bus")
CURRENT_REL = PurePosixPath("docs/Codex/CURRENT.md")
EXECUTION_STATE_REL = PurePosixPath(
    "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/"
    "ROUTE_B_EXECUTION_STATE.json"
)
CONTROL_FENCE_RE = re.compile(
    r"```(?:yaml|yml)\s*\n(.*?)```", re.DOTALL | re.IGNORECASE
)
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
GOAL_FILE_RE = re.compile(r"^(?P<goal_id>\d{3}[A-Za-z]*)_.+\.goal\.md$")
ANSWER_FILE_RE = re.compile(r"^(?P<goal_id>\d{3}[A-Za-z]*)_.+\.answer\.md$")
OPEN_STATUS = "OPEN"
TERMINAL_GOAL_STATUSES = frozenset({"CLOSED", "CLOSED_PHASE0"})
CURRENT_INACTIVE_STATUSES = frozenset({"CLOSED", "EMPTY"})
SHADOW_MODE = "SHADOW_NOT_AUTHORITY"
HONESTY_STATE = "CHALLENGER_NOT_RH"
FROZEN_V9_BASELINE = "8bddaa6faf35e093f0a8459d15381c4c6d27305e"


class StartupRuntimeError(ValueError):
    """Battle-control validation error; shadow construction does not raise it."""

    def __init__(self, code: str, detail: str = "") -> None:
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class ControlIdentity:
    sha256: str
    version: int
    status: str
    honesty_state: str | None
    owner_only_boundary: str | None


@dataclass(frozen=True)
class ShadowGoalSelection:
    """Pure selection result before git/control context is attached."""

    selected_goal: str | None
    exact_node_pin: str | None
    exact_source_pin: str | None
    exact_theorem_pin: str | None
    exact_consumer_pin: str | None
    fatal_errors: tuple[str, ...]
    warnings: tuple[str, ...]
    next_action: str


@dataclass(frozen=True)
class StartupSnapshot:
    schema: str
    mode: str
    control_sha256: str | None
    control_version: int | None
    control_status: str | None
    git_head: str | None
    git_origin_head: str | None
    git_tree: str | None
    git_dirty: bool
    selected_goal: str | None
    honesty_state: str
    exact_node_pin: str | None
    exact_source_pin: str | None
    exact_theorem_pin: str | None
    exact_consumer_pin: str | None
    fatal_errors: tuple[str, ...]
    blocked_features: tuple[str, ...]
    warnings: tuple[str, ...]
    next_action: str
    run_authorized: bool

    def to_dict(self) -> dict[str, object]:
        """Return an asdict-compatible payload for workflow rendering."""

        return asdict(self)


@dataclass(frozen=True)
class _GitObservation:
    head: str | None
    origin_head: str | None
    tree: str | None
    branch: str | None
    upstream: str | None
    dirty_paths: tuple[str, ...]
    unmerged_paths: tuple[str, ...]
    status_sha256: str | None
    errors: tuple[str, ...]


@dataclass(frozen=True)
class _PathFingerprint:
    components: tuple[tuple[int, int, int, int, int], ...]
    content_sha256: str | None
    git_blob_sha1: str | None
    git_blob_sha256: str | None


@dataclass
class _WriterLockGuard:
    path: Path | None
    handle: BinaryIO | None
    initial_identity: tuple[int, int, int, int, int] | None

    def recheck(self) -> str | None:
        if self.path is None:
            return "FATAL:WRITER_LOCK_IDENTITY_INVALID"
        try:
            observed = _stat_identity(os.lstat(self.path))
        except FileNotFoundError:
            observed = None
        except OSError as exc:
            return f"FATAL:WRITER_LOCK_UNAVAILABLE:{exc}"
        if observed != self.initial_identity:
            return "FATAL:WRITER_LOCK_IDENTITY_CHANGED"
        if self.handle is not None:
            try:
                held = _stat_identity(os.fstat(self.handle.fileno()))
            except OSError as exc:
                return f"FATAL:WRITER_LOCK_UNAVAILABLE:{exc}"
            if held != self.initial_identity:
                return "FATAL:WRITER_LOCK_IDENTITY_CHANGED"
        return None

    def close(self) -> None:
        if self.handle is not None:
            try:
                fcntl.flock(self.handle.fileno(), fcntl.LOCK_UN)
            finally:
                self.handle.close()


@dataclass(frozen=True)
class _SelectionContext:
    selection: ShadowGoalSelection
    source_path: str | None
    final_tree: str | None
    final_origin: str | None
    errors: tuple[str, ...]
    fingerprints: tuple[tuple[PurePosixPath, _PathFingerprint], ...]


def _repo_file(repo: Path, relative: PurePosixPath) -> Path:
    return repo / Path(*relative.parts)


def _stat_identity(value: os.stat_result) -> tuple[int, int, int, int, int]:
    return (
        value.st_dev,
        value.st_ino,
        value.st_mode,
        value.st_mtime_ns,
        value.st_size,
    )


def _path_fingerprint(repo: Path, relative: PurePosixPath) -> _PathFingerprint:
    """Fingerprint one lexical path without following symlink components."""

    if relative.is_absolute() or ".." in relative.parts:
        raise StartupRuntimeError("STARTUP_PATH_INVALID", relative.as_posix())
    directory_flags = os.O_RDONLY | os.O_DIRECTORY
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    try:
        directory_fd = os.open(repo, directory_flags | nofollow)
    except OSError as exc:
        raise StartupRuntimeError("STARTUP_PATH_INVALID", str(exc)) from exc
    identities: list[tuple[int, int, int, int, int]] = []
    final_fd: int | None = None
    try:
        for index, part in enumerate(relative.parts):
            is_final = index == len(relative.parts) - 1
            flags = os.O_RDONLY | nofollow
            if not is_final:
                flags |= os.O_DIRECTORY
            try:
                lexical_stat = os.stat(
                    part, dir_fd=directory_fd, follow_symlinks=False
                )
                if stat.S_ISLNK(lexical_stat.st_mode):
                    raise StartupRuntimeError(
                        "STARTUP_SYMLINK_COMPONENT", relative.as_posix()
                    )
                opened = os.open(part, flags, dir_fd=directory_fd)
            except StartupRuntimeError:
                raise
            except OSError as exc:
                raise StartupRuntimeError(
                    "STARTUP_PATH_INVALID", relative.as_posix()
                ) from exc
            identity = _stat_identity(os.fstat(opened))
            if identity != _stat_identity(lexical_stat):
                os.close(opened)
                raise StartupRuntimeError(
                    "STARTUP_PATH_CONCURRENT_MUTATION", relative.as_posix()
                )
            identities.append(identity)
            if is_final:
                final_fd = opened
            else:
                os.close(directory_fd)
                directory_fd = opened
        if final_fd is None:
            raise StartupRuntimeError("STARTUP_PATH_INVALID", relative.as_posix())
        final_stat = os.fstat(final_fd)
        digest: str | None = None
        git_blob_sha1: str | None = None
        git_blob_sha256: str | None = None
        if stat.S_ISREG(final_stat.st_mode):
            header = f"blob {final_stat.st_size}\0".encode("ascii")
            hasher = hashlib.sha256()
            git_sha1_hasher = hashlib.sha1(header)
            git_sha256_hasher = hashlib.sha256(header)
            while chunk := os.read(final_fd, 1024 * 1024):
                hasher.update(chunk)
                git_sha1_hasher.update(chunk)
                git_sha256_hasher.update(chunk)
            digest = hasher.hexdigest()
            git_blob_sha1 = git_sha1_hasher.hexdigest()
            git_blob_sha256 = git_sha256_hasher.hexdigest()
            if _stat_identity(os.fstat(final_fd)) != identities[-1]:
                raise StartupRuntimeError(
                    "STARTUP_PATH_CONCURRENT_MUTATION", relative.as_posix()
                )
        return _PathFingerprint(
            tuple(identities), digest, git_blob_sha1, git_blob_sha256
        )
    finally:
        if final_fd is not None:
            os.close(final_fd)
        os.close(directory_fd)


def _recheck_fingerprints(
    repo: Path,
    fingerprints: tuple[tuple[PurePosixPath, _PathFingerprint], ...],
) -> tuple[str, ...]:
    errors: list[str] = []
    for relative, expected in fingerprints:
        try:
            observed = _path_fingerprint(repo, relative)
        except StartupRuntimeError:
            errors.append(f"STARTUP_PATH_CONCURRENT_MUTATION:{relative.as_posix()}")
            continue
        if observed != expected:
            errors.append(f"STARTUP_PATH_CONCURRENT_MUTATION:{relative.as_posix()}")
    return tuple(errors)


def _has_symlink_component(repo: Path, relative: PurePosixPath) -> bool:
    current = repo
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            return True
    return False


def _fingerprint_matches_git_blob(
    fingerprint: _PathFingerprint | None, blob_oid: str | None
) -> bool:
    return (
        fingerprint is not None
        and blob_oid is not None
        and blob_oid in {fingerprint.git_blob_sha1, fingerprint.git_blob_sha256}
    )


def _control_identity(control_path: Path) -> ControlIdentity:
    try:
        raw = control_path.read_bytes()
        text = raw.decode("utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise StartupRuntimeError("STARTUP_CONTROL_INVALID", str(exc)) from exc
    matches = [
        body
        for body in CONTROL_FENCE_RE.findall(text)
        if re.search(r"(?m)^CONTROL_ID\s*:", body)
    ]
    if len(matches) != 1:
        raise StartupRuntimeError(
            "STARTUP_CONTROL_INVALID",
            f"expected exactly one control machine header, found {len(matches)}",
        )
    try:
        header = load_unique_yaml(matches[0])
    except yaml.YAMLError as exc:
        raise StartupRuntimeError("STARTUP_CONTROL_INVALID", str(exc)) from exc
    if not isinstance(header, dict):
        raise StartupRuntimeError("STARTUP_CONTROL_INVALID", "machine header is not a mapping")
    version = header.get("CONTROL_VERSION")
    status = header.get("STATUS")
    if (
        header.get("CONTROL_ID") != "Q3_EXECUTOR_CONTROL"
        or not isinstance(version, int)
        or isinstance(version, bool)
        or not isinstance(status, str)
        or not status
    ):
        raise StartupRuntimeError(
            "STARTUP_CONTROL_INVALID", "identity, version, or status is invalid"
        )
    return ControlIdentity(
        sha256=hashlib.sha256(raw).hexdigest(),
        version=version,
        status=status,
        honesty_state=(
            header.get("HONESTY_STATE")
            if isinstance(header.get("HONESTY_STATE"), str)
            else None
        ),
        owner_only_boundary=(
            header.get("OWNER_ONLY_BOUNDARY")
            if isinstance(header.get("OWNER_ONLY_BOUNDARY"), str)
            else None
        ),
    )


def _validate_battle_v10_identity(identity: ControlIdentity) -> ControlIdentity:
    if (
        identity.version != 10
        or identity.status != "ACTIVE"
        or identity.honesty_state != HONESTY_STATE
        or identity.owner_only_boundary != "PX_RH_CLAIM"
    ):
        raise StartupRuntimeError(
            "BATTLE_V10_CONTROL_INVALID",
            "expected ACTIVE v10 with CHALLENGER_NOT_RH and owner-only PX_RH_CLAIM",
        )
    return identity


def validate_battle_v10_control(repo: Path) -> ControlIdentity:
    """Validate the future battle control with one control-file parse."""

    identity = _control_identity(_repo_file(repo.resolve(), CONTROL_REL))
    return _validate_battle_v10_identity(identity)


def _canonical_relative(repo: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(repo.resolve()).as_posix()
    except ValueError as exc:
        raise StartupRuntimeError(
            "STARTUP_PATH_INVALID", f"outside repository: {path}"
        ) from exc


def _lexical_relative(repo: Path, path: Path) -> PurePosixPath:
    try:
        return PurePosixPath(path.absolute().relative_to(repo.absolute()).as_posix())
    except ValueError as exc:
        raise StartupRuntimeError("STARTUP_PATH_INVALID", str(path)) from exc


def _first_string(mapping: dict[str, Any], keys: tuple[str, ...]) -> str | None:
    for key in keys:
        value = mapping.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return None


def _pins(mapping: dict[str, Any]) -> tuple[str | None, str | None, str | None, str | None]:
    node = _first_string(mapping, ("EXACT_NODE", "NODE", "target_id"))
    source = _first_string(
        mapping,
        ("EXACT_SOURCE_PIN", "SOURCE_PIN", "source_commit", "SOURCE", "source"),
    )
    theorem = _first_string(
        mapping,
        ("EXACT_THEOREM", "THEOREM", "THEOREM_ID", "declaration"),
    )
    consumer = _first_string(
        mapping,
        ("EXACT_CONSUMER", "TERMINAL_CONSUMER", "CONSUMER", "terminal_consumer"),
    )
    return node, source, theorem, consumer


def _goal_header(path: Path) -> dict[str, Any]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise StartupRuntimeError("STARTUP_GOAL_HEADER_INVALID", f"{path}: {exc}") from exc
    header = goal_machine_header_text(text)
    if header is None:
        raise StartupRuntimeError(
            "STARTUP_GOAL_HEADER_INVALID", f"missing or malformed header: {path}"
        )
    return header


def _goal_id(path: Path, header: dict[str, Any]) -> str:
    match = GOAL_FILE_RE.fullmatch(path.name)
    value = header.get("GOAL")
    if match is None or not isinstance(value, str):
        raise StartupRuntimeError(
            "STARTUP_GOAL_IDENTITY_MISMATCH", f"invalid identity: {path}"
        )
    file_goal_id = match.group("goal_id")
    if value != file_goal_id:
        raise StartupRuntimeError(
            "STARTUP_GOAL_IDENTITY_MISMATCH",
            f"machine GOAL {value!r} disagrees with {path.name!r}",
        )
    return file_goal_id


def _answer_result_present(header: dict[str, Any]) -> bool:
    keys = (
        "EXACT_RESULT",
        "RESULT",
        "VERDICT",
        "PRIMARY",
        "PRIMARY_VERDICT",
        "SUCCESS",
        "STOP",
        "FAILURE_CODE",
    )
    return any(
        isinstance(header.get(key), str)
        and header[key].strip()
        and header[key].strip().lower() != "null"
        for key in keys
    )


def _validate_answer(goal_id: str, answer_path: Path) -> None:
    try:
        header = _goal_header(answer_path)
    except StartupRuntimeError as exc:
        raise StartupRuntimeError("STARTUP_ANSWER_INVALID", str(exc)) from exc
    match = ANSWER_FILE_RE.fullmatch(answer_path.name)
    answer_goal = header.get("GOAL")
    if (
        match is None
        or match.group("goal_id") != goal_id
        or answer_goal != goal_id
        or header.get("STATUS") not in TERMINAL_GOAL_STATUSES
        or not _answer_result_present(header)
    ):
        raise StartupRuntimeError(
            "STARTUP_ANSWER_INVALID", f"identity, status, or result invalid: {answer_path}"
        )


def _current_mapping(
    current_path: Path, *, expected: _PathFingerprint | None = None
) -> dict[str, Any]:
    try:
        raw = current_path.read_bytes()
        text = raw.decode("utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", f"{current_path}: {exc}") from exc
    if expected is not None and hashlib.sha256(raw).hexdigest() != expected.content_sha256:
        raise StartupRuntimeError(
            "STARTUP_PATH_CONCURRENT_MUTATION", str(current_path)
        )
    match = CONTROL_FENCE_RE.search(text)
    if match is None:
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", "machine header missing")
    try:
        payload = load_unique_yaml(match.group(1))
    except yaml.YAMLError as exc:
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", str(exc)) from exc
    if not isinstance(payload, dict):
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", "header is not a mapping")
    return payload


def _active_current_selection(
    repo: Path,
    current_path: Path,
    current_fingerprint: _PathFingerprint,
) -> tuple[
    ShadowGoalSelection,
    tuple[PurePosixPath, _PathFingerprint] | None,
]:
    if _has_symlink_component(repo, CURRENT_REL):
        raise StartupRuntimeError("STARTUP_SYMLINK_COMPONENT", CURRENT_REL.as_posix())
    payload = _current_mapping(current_path, expected=current_fingerprint)
    status = payload.get("status")
    if status in CURRENT_INACTIVE_STATUSES:
        return (
            ShadowGoalSelection(
                selected_goal=None,
                exact_node_pin=None,
                exact_source_pin=None,
                exact_theorem_pin=None,
                exact_consumer_pin=None,
                fatal_errors=(),
                warnings=(f"CURRENT_{status}_IGNORED",),
                next_action="SHADOW_STOP_NO_GOAL",
            ),
            None,
        )
    if status != "ACTIVE":
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", f"unknown status {status!r}")
    task_value = payload.get("task_file")
    if not isinstance(task_value, str) or not task_value:
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", "ACTIVE task_file missing")
    task_rel = PurePosixPath(task_value)
    if (
        task_rel.is_absolute()
        or ".." in task_rel.parts
        or "\\" in task_value
        or task_rel.as_posix() != task_value
    ):
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", "task_file is not canonical")
    task_path = _repo_file(repo, task_rel)
    if _has_symlink_component(repo, task_rel):
        raise StartupRuntimeError("STARTUP_SYMLINK_COMPONENT", task_rel.as_posix())
    if not task_path.is_file() or not task_path.resolve().is_relative_to(repo.resolve()):
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", "task_file is missing")
    source_commit = payload.get("source_commit")
    if not isinstance(source_commit, str) or COMMIT_RE.fullmatch(source_commit) is None:
        raise StartupRuntimeError("STARTUP_CURRENT_INVALID", "source_commit is invalid")
    task_fingerprint = _path_fingerprint(repo, task_rel)
    task_header = _current_mapping(task_path, expected=task_fingerprint)
    node, _source, theorem, consumer = _pins(task_header)
    missing_exact_pins = any(pin is None for pin in (node, theorem, consumer))
    return (
        ShadowGoalSelection(
            selected_goal=task_rel.as_posix(),
            exact_node_pin=node,
            exact_source_pin=source_commit,
            exact_theorem_pin=theorem,
            exact_consumer_pin=consumer,
            fatal_errors=("STARTUP_EXACT_PINS_MISSING",) if missing_exact_pins else (),
            warnings=("CURRENT_ACTIVE_FALLBACK_WITHOUT_OPEN_BUS_GOAL",),
            next_action=(
                "STOP_FAIL_CLOSED"
                if missing_exact_pins
                else "SHADOW_INSPECT_SELECTED_GOAL"
            ),
        ),
        (task_rel, task_fingerprint),
    )


def _historical_baseline_is_ancestor(repo: Path) -> bool:
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", FROZEN_V9_BASELINE, "HEAD"],
        cwd=repo,
        check=False,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return ancestor.returncode == 0


def _physical_bus_paths(
    repo: Path, git_state: _GitObservation
) -> tuple[tuple[Path, ...], tuple[Path, ...]]:
    bus = _repo_file(repo, BUS_REL)
    goal_names: set[str] = set()
    answer_names: set[str] = set()
    physical_symlinks: list[str] = []

    def fail_walk(error: OSError) -> None:
        raise StartupRuntimeError("STARTUP_BUS_SCAN_UNAVAILABLE", str(error))

    for directory, dirnames, filenames in os.walk(
        bus, followlinks=False, onerror=fail_walk
    ):
        base = Path(directory)
        for name in tuple(dirnames):
            candidate = base / name
            relative = _lexical_relative(repo, candidate).as_posix()
            if candidate.is_symlink():
                physical_symlinks.append(relative)
                continue
            if name.endswith(".goal.md"):
                goal_names.add(relative)
            elif name.endswith(".answer.md"):
                answer_names.add(relative)
        for name in filenames:
            if not name.endswith((".goal.md", ".answer.md")):
                continue
            candidate = base / name
            relative = _lexical_relative(repo, candidate).as_posix()
            if candidate.is_symlink():
                physical_symlinks.append(relative)
                continue
            if name.endswith(".goal.md"):
                goal_names.add(relative)
            else:
                answer_names.add(relative)

    if git_state.head is None:
        if physical_symlinks:
            raise StartupRuntimeError(
                "STARTUP_SYMLINK_COMPONENT", physical_symlinks[0]
            )
        return (
            tuple(
                _repo_file(repo, PurePosixPath(name))
                for name in sorted(goal_names)
            ),
            tuple(
                _repo_file(repo, PurePosixPath(name))
                for name in sorted(answer_names)
            ),
        )
    tracked = subprocess.run(
        [
            "git",
            "ls-files",
            "-z",
            "--stage",
            "--",
            BUS_REL.as_posix(),
        ],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if tracked.returncode != 0:
        raise StartupRuntimeError("STARTUP_BUS_INDEX_UNAVAILABLE")
    for item in tracked.stdout.split(b"\0"):
        if not item:
            continue
        metadata, separator, raw_path = item.partition(b"\t")
        fields = metadata.split()
        if not separator or len(fields) != 3:
            raise StartupRuntimeError("STARTUP_BUS_INDEX_UNAVAILABLE")
        path = raw_path.decode("utf-8", errors="surrogateescape")
        if fields[0] == b"120000":
            raise StartupRuntimeError("STARTUP_TRACKED_BUS_SYMLINK", path)
        if path.endswith(".goal.md"):
            goal_names.add(path)
        elif path.endswith(".answer.md"):
            answer_names.add(path)
    if physical_symlinks:
        raise StartupRuntimeError("STARTUP_SYMLINK_COMPONENT", physical_symlinks[0])
    return (
        tuple(
            _repo_file(repo, PurePosixPath(name)) for name in sorted(goal_names)
        ),
        tuple(
            _repo_file(repo, PurePosixPath(name)) for name in sorted(answer_names)
        ),
    )


def _shadow_selection_context(repo: Path, git_state: _GitObservation) -> _SelectionContext:
    bus = _repo_file(repo, BUS_REL)
    empty = ShadowGoalSelection(
        None, None, None, None, None, (), (), "STOP_FAIL_CLOSED"
    )
    if _has_symlink_component(repo, BUS_REL) or not bus.is_dir():
        return _SelectionContext(
            replace(empty, fatal_errors=("STARTUP_BUS_MISSING",)),
            None,
            None,
            None,
            (),
            (),
        )
    try:
        goal_paths, answer_paths = _physical_bus_paths(repo, git_state)
    except StartupRuntimeError as exc:
        return _SelectionContext(
            replace(empty, fatal_errors=(str(exc),)),
            None,
            None,
            None,
            (),
            (),
        )

    open_goals: list[tuple[Path, dict[str, Any], _PathFingerprint | None]] = []
    answered: list[tuple[Path, Path]] = []
    orphan_answers: list[Path] = []
    fatal: list[str] = []
    warnings: list[str] = []
    fingerprints: list[tuple[PurePosixPath, _PathFingerprint]] = []
    expected_answers = {
        goal_path.with_name(
            goal_path.name.removesuffix(".goal.md") + ".answer.md"
        )
        for goal_path in goal_paths
    }
    for answer_path in answer_paths:
        answer_rel = _lexical_relative(repo, answer_path)
        if _has_symlink_component(repo, answer_rel):
            fatal.append(f"STARTUP_SYMLINK_COMPONENT:{answer_rel.as_posix()}")
            continue
        orphan = answer_path not in expected_answers
        if not answer_path.is_file():
            if orphan:
                fatal.append(f"STARTUP_ANSWER_ORPHAN:{answer_rel.as_posix()}")
            fatal.append(f"STARTUP_ANSWER_INVALID:{answer_rel.as_posix()}")
            continue
        try:
            fingerprints.append(
                (answer_rel, _path_fingerprint(repo, answer_rel))
            )
        except StartupRuntimeError as exc:
            fatal.append(str(exc))
            continue
        if orphan:
            orphan_answers.append(answer_path)
    for goal_path in goal_paths:
        goal_rel = _lexical_relative(repo, goal_path)
        answer_path = goal_path.with_name(
            goal_path.name.removesuffix(".goal.md") + ".answer.md"
        )
        answer_rel = _lexical_relative(repo, answer_path)
        if _has_symlink_component(repo, goal_rel) or _has_symlink_component(
            repo, answer_rel
        ):
            fatal.append(f"STARTUP_SYMLINK_COMPONENT:{goal_rel.as_posix()}")
            continue
        if not goal_path.is_file():
            fatal.append(f"STARTUP_GOAL_INVALID:{goal_rel.as_posix()}")
            continue
        try:
            fingerprint = _path_fingerprint(repo, goal_rel)
            fingerprints.append((goal_rel, fingerprint))
        except StartupRuntimeError as exc:
            fatal.append(str(exc))
            continue
        if answer_path.exists():
            if not answer_path.is_file():
                fatal.append(f"STARTUP_ANSWER_INVALID:{answer_rel.as_posix()}")
            else:
                answered.append((goal_path, answer_path))
            continue
        try:
            header = _goal_header(goal_path)
            goal_id = _goal_id(goal_path, header)
        except StartupRuntimeError as exc:
            fatal.append(str(exc))
            continue
        status = header.get("STATUS")
        if not isinstance(status, str) or STATUS_RE.fullmatch(status) is None:
            fatal.append(f"STARTUP_GOAL_HEADER_INVALID: STATUS missing: {goal_path}")
        elif status == OPEN_STATUS:
            open_goals.append((goal_path, header, fingerprint))
        elif status in PAUSED_STATUSES:
            warnings.append(f"PAUSED_RESTORABLE_EXCLUDED:{goal_rel.as_posix()}")
        elif status in TERMINAL_GOAL_STATUSES:
            fatal.append(f"STARTUP_ANSWER_MISSING:{goal_rel.as_posix()}")
        else:
            fatal.append(f"STARTUP_UNKNOWN_GOAL_STATUS:{status}:{goal_rel.as_posix()}")
    if len(open_goals) > 1:
        labels = ",".join(_canonical_relative(repo, item[0]) for item in open_goals)
        fatal.append(f"STARTUP_AMBIGUOUS_OPEN_GOALS:{labels}")

    selected_header: dict[str, Any] | None = None
    if len(open_goals) == 1:
        selected_path, selected_header, _selected_fingerprint = open_goals[0]
        node, _source, theorem, consumer = _pins(selected_header)
        source_pin = _first_string(selected_header, ("SOURCE_PIN",))
        selection = ShadowGoalSelection(
            _canonical_relative(repo, selected_path),
            node,
            source_pin,
            theorem,
            consumer,
            (),
            tuple(warnings),
            "SHADOW_INSPECT_SELECTED_GOAL",
        )
    elif fatal:
        selection = replace(
            empty, fatal_errors=tuple(fatal), warnings=tuple(warnings)
        )
    else:
        current_path = _repo_file(repo, CURRENT_REL)
        try:
            current_fingerprint = _path_fingerprint(repo, CURRENT_REL)
            selection, task_fingerprint = _active_current_selection(
                repo, current_path, current_fingerprint
            )
            fingerprints.append((CURRENT_REL, current_fingerprint))
            if task_fingerprint is not None:
                fingerprints.append(task_fingerprint)
            selection = replace(
                selection, warnings=tuple(warnings) + selection.warnings
            )
        except StartupRuntimeError as exc:
            selection = replace(
                empty, fatal_errors=(str(exc),), warnings=tuple(warnings)
            )

    source_path: str | None = None
    source_pin: str | None = None
    if selected_header is not None:
        raw_source = selected_header.get("SOURCE")
        source_path = raw_source if isinstance(raw_source, str) else None
        raw_pin = selected_header.get("SOURCE_PIN")
        source_pin = raw_pin if isinstance(raw_pin, str) else None
        if source_path is not None:
            source_rel = PurePosixPath(source_path)
            if (
                source_rel.is_absolute()
                or ".." in source_rel.parts
                or "\\" in source_path
                or source_rel.as_posix() != source_path
            ):
                fatal.append("STARTUP_SOURCE_PIN_INVALID")
            else:
                try:
                    fingerprints.append(
                        (source_rel, _path_fingerprint(repo, source_rel))
                    )
                except StartupRuntimeError as exc:
                    fatal.append(str(exc))

    specs: list[str] = []
    fingerprint_by_path = {relative.as_posix(): value for relative, value in fingerprints}
    upstream = git_state.upstream or (
        f"origin/{git_state.branch}" if git_state.branch else "origin/HEAD"
    )
    identity_specs = ("HEAD", "HEAD^{tree}", upstream)
    if git_state.head is not None:
        specs.extend(identity_specs)
        if CURRENT_REL.as_posix() in fingerprint_by_path:
            specs.append(f"HEAD:{CURRENT_REL.as_posix()}")
        if answered or orphan_answers:
            if not _historical_baseline_is_ancestor(repo):
                fatal.append("STARTUP_HISTORICAL_BASELINE_INVALID")
            for goal_path, answer_path in answered:
                for path in (goal_path, answer_path):
                    relative = _lexical_relative(repo, path).as_posix()
                    specs.extend(
                        (f"{FROZEN_V9_BASELINE}:{relative}", f"HEAD:{relative}")
                    )
            for answer_path in orphan_answers:
                relative = _lexical_relative(repo, answer_path).as_posix()
                specs.extend(
                    (f"{FROZEN_V9_BASELINE}:{relative}", f"HEAD:{relative}")
                )
        if selection.selected_goal and selection.selected_goal.startswith(
            f"{BUS_REL.as_posix()}/"
        ):
            specs.append(f"HEAD:{selection.selected_goal}")
            if source_path is not None and source_pin is not None:
                specs.extend(
                    (
                        f"HEAD:{source_path}",
                        source_pin,
                        f"{source_pin}:{source_path}",
                    )
                )
        elif (
            selection.selected_goal
            and selection.selected_goal.startswith("docs/Codex/")
            and selection.exact_source_pin
        ):
            specs.extend(
                (
                    f"HEAD:{selection.selected_goal}",
                    selection.exact_source_pin,
                    f"{selection.exact_source_pin}:{selection.selected_goal}",
                )
            )
    checked = _batch_check(repo, tuple(dict.fromkeys(specs))) if specs else {}

    for answer_path in orphan_answers:
        answer_rel = _lexical_relative(repo, answer_path).as_posix()
        baseline_answer = checked.get(f"{FROZEN_V9_BASELINE}:{answer_rel}")
        head_answer = checked.get(f"HEAD:{answer_rel}")
        unchanged_historical = (
            git_state.head is not None
            and baseline_answer is not None
            and head_answer is not None
            and baseline_answer[0] == head_answer[0]
            and _fingerprint_matches_git_blob(
                fingerprint_by_path.get(answer_rel), head_answer[0]
            )
            and answer_rel not in git_state.dirty_paths
        )
        if unchanged_historical:
            continue
        fatal.append(f"STARTUP_ANSWER_ORPHAN:{answer_rel}")
        match = ANSWER_FILE_RE.fullmatch(answer_path.name)
        try:
            _validate_answer(match.group("goal_id") if match else "", answer_path)
        except StartupRuntimeError as exc:
            fatal.append(str(exc))

    for goal_path, answer_path in answered:
        goal_rel = _lexical_relative(repo, goal_path).as_posix()
        answer_rel = _lexical_relative(repo, answer_path).as_posix()
        unchanged = False
        if git_state.head is not None:
            base_goal = checked.get(f"{FROZEN_V9_BASELINE}:{goal_rel}")
            head_goal = checked.get(f"HEAD:{goal_rel}")
            base_answer = checked.get(f"{FROZEN_V9_BASELINE}:{answer_rel}")
            head_answer = checked.get(f"HEAD:{answer_rel}")
            unchanged = (
                base_goal is not None
                and head_goal is not None
                and base_answer is not None
                and head_answer is not None
                and base_goal[0] == head_goal[0]
                and base_answer[0] == head_answer[0]
                and _fingerprint_matches_git_blob(
                    fingerprint_by_path.get(goal_rel), head_goal[0]
                )
                and _fingerprint_matches_git_blob(
                    fingerprint_by_path.get(answer_rel), head_answer[0]
                )
                and goal_rel not in git_state.dirty_paths
                and answer_rel not in git_state.dirty_paths
            )
        if unchanged:
            continue
        try:
            header = _goal_header(goal_path)
            goal_id = _goal_id(goal_path, header)
            status = header.get("STATUS")
            if status in PAUSED_STATUSES:
                raise StartupRuntimeError(
                    "STARTUP_ANSWER_INVALID", f"paused goal has answer: {goal_rel}"
                )
            if status not in ({OPEN_STATUS} | TERMINAL_GOAL_STATUSES):
                raise StartupRuntimeError(
                    "STARTUP_UNKNOWN_GOAL_STATUS", f"{status}:{goal_rel}"
                )
            _validate_answer(goal_id, answer_path)
        except StartupRuntimeError as exc:
            fatal.append(str(exc))

    final_tree = None
    final_origin = None
    if checked:
        head_object = checked.get(identity_specs[0])
        tree_object = checked.get(identity_specs[1])
        origin_object = checked.get(identity_specs[2])
        final_head = head_object[0] if head_object else None
        final_tree = tree_object[0] if tree_object else None
        final_origin = origin_object[0] if origin_object else None
        if final_head != git_state.head:
            fatal.append("STARTUP_GIT_CONCURRENT_MUTATION")
    if (
        git_state.head is not None
        and selection.selected_goal is not None
        and selection.selected_goal.startswith(f"{BUS_REL.as_posix()}/")
    ):
        selected_head = checked.get(f"HEAD:{selection.selected_goal}")
        if selected_head is None or not _fingerprint_matches_git_blob(
            fingerprint_by_path.get(selection.selected_goal), selected_head[0]
        ):
            fatal.append("STARTUP_GOAL_BLOB_DRIFT")
        if source_path is not None or source_pin is not None:
            if (
                source_path is None
                or source_pin is None
                or COMMIT_RE.fullmatch(source_pin) is None
                and re.fullmatch(r"[0-9a-f]{40,64}", source_pin) is None
            ):
                fatal.append("STARTUP_SOURCE_PIN_INVALID")
            else:
                head_source = checked.get(f"HEAD:{source_path}")
                pin_object = checked.get(source_pin)
                pinned_source = checked.get(f"{source_pin}:{source_path}")
                head_blob = head_source[0] if head_source else None
                if pin_object is None:
                    fatal.append("STARTUP_SOURCE_PIN_INVALID")
                elif pin_object[1] == "blob":
                    if pin_object[0] != head_blob:
                        fatal.append("STARTUP_SOURCE_BLOB_DRIFT")
                elif pin_object[1] == "commit":
                    if pinned_source is None:
                        fatal.append("STARTUP_SOURCE_COMMIT_PIN_DRIFT")
                    elif pinned_source[0] != head_blob:
                        fatal.append("STARTUP_SOURCE_BLOB_DRIFT")
                else:
                    fatal.append("STARTUP_SOURCE_PIN_INVALID")
    elif (
        git_state.head is not None
        and selection.selected_goal is not None
        and selection.selected_goal.startswith("docs/Codex/")
    ):
        source_commit = selection.exact_source_pin
        head_task = checked.get(f"HEAD:{selection.selected_goal}")
        source_object = checked.get(source_commit or "")
        source_task = checked.get(f"{source_commit}:{selection.selected_goal}")
        task_fingerprint = fingerprint_by_path.get(selection.selected_goal)
        if not _fingerprint_matches_git_blob(
            task_fingerprint, head_task[0] if head_task else None
        ) or not _fingerprint_matches_git_blob(
            task_fingerprint, source_task[0] if source_task else None
        ):
            fatal.append("STARTUP_CURRENT_TASK_WORKTREE_DRIFT")
        if (
            source_object is None
            or source_object[1] != "commit"
            or head_task is None
            or source_task is None
            or head_task[0] != source_task[0]
        ):
            fatal.append("STARTUP_CURRENT_SOURCE_COMMIT_DRIFT")

    if (
        git_state.head is not None
        and CURRENT_REL.as_posix() in fingerprint_by_path
    ):
        head_current = checked.get(f"HEAD:{CURRENT_REL.as_posix()}")
        if not _fingerprint_matches_git_blob(
            fingerprint_by_path[CURRENT_REL.as_posix()],
            head_current[0] if head_current else None,
        ):
            fatal.append("STARTUP_CURRENT_BLOB_DRIFT")

    fatal.extend(selection.fatal_errors)
    selection = replace(
        selection,
        fatal_errors=tuple(fatal),
        next_action="STOP_FAIL_CLOSED" if fatal else selection.next_action,
    )
    return _SelectionContext(
        selection,
        source_path,
        final_tree,
        final_origin,
        (),
        tuple(fingerprints),
    )


def select_v10_shadow_goal(
    repo: Path, *, git_state: _GitObservation | None = None
) -> ShadowGoalSelection:
    """Select exactly one global OPEN physical goal, without numeric authority."""

    repo = repo.resolve()
    observed = git_state if git_state is not None else _git_observation(repo)
    return _shadow_selection_context(repo, observed).selection


def _git_observation(repo: Path) -> _GitObservation:
    status = subprocess.run(
        [
            "git",
            "status",
            "--porcelain=v2",
            "-z",
            "--branch",
            "--untracked-files=all",
            "--ignored=traditional",
        ],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if status.returncode != 0:
        return _GitObservation(
            None,
            None,
            None,
            None,
            None,
            (),
            (),
            None,
            ("STARTUP_GIT_STATE_UNAVAILABLE",),
        )
    records = status.stdout.split(b"\0")
    head: str | None = None
    branch: str | None = None
    upstream: str | None = None
    dirty: list[str] = []
    unmerged: list[str] = []

    def decode(raw: bytes) -> str:
        return raw.decode("utf-8", errors="surrogateescape")

    index = 0
    while index < len(records):
        record = records[index]
        index += 1
        if not record:
            continue
        if record.startswith(b"# branch.oid "):
            value = decode(record.removeprefix(b"# branch.oid "))
            head = value if COMMIT_RE.fullmatch(value) else None
        elif record.startswith(b"# branch.head "):
            branch = decode(record.removeprefix(b"# branch.head "))
        elif record.startswith(b"# branch.upstream "):
            upstream = decode(record.removeprefix(b"# branch.upstream "))
        elif record.startswith(b"? "):
            dirty.append(decode(record[2:]))
        elif record.startswith(b"! "):
            ignored = decode(record[2:])
            if ignored.startswith(f"{BUS_REL.as_posix()}/"):
                dirty.append(ignored)
        elif record.startswith(b"1 "):
            dirty.append(decode(record.split(b" ", 8)[-1]))
        elif record.startswith(b"2 "):
            dirty.append(decode(record.split(b" ", 9)[-1]))
            if index < len(records) and records[index]:
                dirty.append(decode(records[index]))
                index += 1
        elif record.startswith(b"u "):
            path = decode(record.split(b" ", 10)[-1])
            dirty.append(path)
            unmerged.append(path)
    errors = () if head else ("STARTUP_GIT_STATE_UNAVAILABLE",)
    if unmerged:
        errors += ("STARTUP_GIT_UNMERGED:" + ",".join(unmerged[:8]),)
    return _GitObservation(
        head,
        None,
        None,
        branch,
        upstream,
        tuple(dirty),
        tuple(unmerged),
        hashlib.sha256(status.stdout).hexdigest(),
        errors,
    )


def _batch_check(repo: Path, specs: tuple[str, ...]) -> dict[str, tuple[str, str] | None]:
    result = subprocess.run(
        ["git", "cat-file", "--batch-check", "-Z"],
        cwd=repo,
        check=False,
        input=b"".join(
            spec.encode("utf-8", errors="surrogateescape") + b"\0" for spec in specs
        ),
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    records = result.stdout.split(b"\0")
    checked: dict[str, tuple[str, str] | None] = {}
    for index, spec in enumerate(specs):
        fields = records[index].rsplit(b" ", 2) if index < len(records) else []
        checked[spec] = (
            (fields[0].decode("ascii"), fields[1].decode("ascii"))
            if len(fields) == 3
            and fields[1] in {b"blob", b"commit", b"tree", b"tag"}
            else None
        )
    return checked


def _is_owned(path: str, owned_paths: tuple[str, ...]) -> bool:
    candidate = PurePosixPath(path)
    for value in owned_paths:
        owned = PurePosixPath(value)
        if candidate == owned or owned in candidate.parents:
            return True
    return False


def _load_unique_json(path: Path) -> dict[str, Any]:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate key {key!r}")
            result[key] = value
        return result

    try:
        payload = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=unique_object
        )
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        raise StartupRuntimeError("STARTUP_STATE_INVALID", f"{path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise StartupRuntimeError("STARTUP_STATE_INVALID", "top level is not a mapping")
    return payload


def _compact_messages(messages: list[str], *, limit: int = 12) -> tuple[str, ...]:
    unique = tuple(dict.fromkeys(messages))
    if len(unique) <= limit:
        return unique
    omitted = len(unique) - limit
    return unique[:limit] + (f"STARTUP_DIAGNOSTICS_OMITTED:{omitted}",)


def _git_common_dir(repo: Path) -> Path:
    dotgit = repo / ".git"
    if dotgit.is_symlink():
        raise StartupRuntimeError("WRITER_LOCK_IDENTITY_INVALID", ".git is symlink")
    if dotgit.is_dir():
        git_dir = dotgit
    elif dotgit.is_file():
        try:
            marker = dotgit.read_text(encoding="utf-8").strip()
        except (OSError, UnicodeDecodeError) as exc:
            raise StartupRuntimeError("WRITER_LOCK_IDENTITY_INVALID", str(exc)) from exc
        prefix = "gitdir: "
        if not marker.startswith(prefix) or "\n" in marker:
            raise StartupRuntimeError("WRITER_LOCK_IDENTITY_INVALID", "invalid .git file")
        candidate = Path(marker.removeprefix(prefix))
        git_dir = candidate if candidate.is_absolute() else repo / candidate
    else:
        raise StartupRuntimeError("WRITER_LOCK_IDENTITY_INVALID", ".git missing")
    git_dir = git_dir.resolve()
    commondir_file = git_dir / "commondir"
    if not commondir_file.exists():
        return git_dir
    if commondir_file.is_symlink():
        raise StartupRuntimeError(
            "WRITER_LOCK_IDENTITY_INVALID", "commondir is symlink"
        )
    try:
        marker = commondir_file.read_text(encoding="utf-8").strip()
    except (OSError, UnicodeDecodeError) as exc:
        raise StartupRuntimeError("WRITER_LOCK_IDENTITY_INVALID", str(exc)) from exc
    if not marker or "\n" in marker:
        raise StartupRuntimeError("WRITER_LOCK_IDENTITY_INVALID", "invalid commondir")
    candidate = Path(marker)
    common_dir = candidate if candidate.is_absolute() else git_dir / candidate
    return common_dir.resolve()


def _acquire_writer_lock(repo: Path) -> tuple[_WriterLockGuard, str | None]:
    try:
        common_dir = _git_common_dir(repo)
    except StartupRuntimeError as exc:
        return _WriterLockGuard(None, None, None), f"FATAL:{exc}"
    lock_path = common_dir / "q3-three-body.writer.lock"
    try:
        initial = _stat_identity(os.lstat(lock_path))
    except FileNotFoundError:
        return (
            _WriterLockGuard(lock_path, None, None),
            "FATAL:WRITER_LOCK_UNAVAILABLE:missing",
        )
    except OSError as exc:
        return _WriterLockGuard(lock_path, None, None), f"FATAL:WRITER_LOCK_UNAVAILABLE:{exc}"
    if stat.S_ISLNK(initial[2]) or not stat.S_ISREG(initial[2]):
        return (
            _WriterLockGuard(lock_path, None, initial),
            "FATAL:WRITER_LOCK_IDENTITY_INVALID",
        )
    try:
        descriptor = os.open(lock_path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
        handle = os.fdopen(descriptor, "rb", closefd=True)
        if _stat_identity(os.fstat(handle.fileno())) != initial:
            handle.close()
            return (
                _WriterLockGuard(lock_path, None, initial),
                "FATAL:WRITER_LOCK_IDENTITY_CHANGED",
            )
        fcntl.flock(handle.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB)
    except BlockingIOError:
        if "handle" in locals():
            handle.close()
        return _WriterLockGuard(lock_path, None, initial), "FATAL:WRITER_LOCK_COLLISION"
    except OSError as exc:
        if "handle" in locals():
            handle.close()
        return (
            _WriterLockGuard(lock_path, None, initial),
            f"FATAL:WRITER_LOCK_UNAVAILABLE:{exc}",
        )
    return _WriterLockGuard(lock_path, handle, initial), None


def _state_pins_and_errors(
    repo: Path, selected_goal: str | None, selected_physical: str | None
) -> tuple[str | None, str | None, tuple[str, ...]]:
    if _has_symlink_component(repo, EXECUTION_STATE_REL):
        return None, None, ("STARTUP_SYMLINK_COMPONENT:execution-state",)
    try:
        state = _load_unique_json(_repo_file(repo, EXECUTION_STATE_REL))
        architecture = state["architecture"]
        current = state["current"]
        if not isinstance(architecture, dict) or not isinstance(current, dict):
            raise KeyError("architecture/current")
    except (KeyError, TypeError, StartupRuntimeError) as exc:
        return None, None, (f"STARTUP_STATE_INVALID:{exc}",)
    errors: list[str] = []
    if (
        architecture.get("route_b_rh_status") != "NOT_RH"
        or current.get("route_promotion") is not False
        or current.get("rh_claimed") is not False
    ):
        errors.append("STARTUP_HONESTY_STATE_DRIFT")
    selected_state_path = current.get("selected_bus_goal_path")
    if selected_physical is not None:
        match = GOAL_FILE_RE.fullmatch(Path(selected_physical).name)
        expected_id = match.group("goal_id")[:3] if match else None
        if (
            current.get("selected_bus_goal_path") != selected_physical
            or current.get("selected_bus_goal_nnn") != expected_id
        ):
            errors.append("STARTUP_SELECTOR_STATE_DRIFT")
    elif selected_state_path not in {None, ""}:
        errors.append("STARTUP_SELECTOR_STATE_DRIFT")
    theorem_pin: str | None = None
    consumer_pin: str | None = None
    history = state.get("terminal_history")
    operational = state.get("operational_status")
    if (
        state.get("schema_version") == "route_b_execution_state.v3_live_bus"
        and isinstance(history, dict)
        and isinstance(operational, str)
    ):
        normalized = operational.lower()
        matching_keys = sorted(
            key
            for key in history
            if isinstance(key, str) and normalized.startswith(key.lower())
        )
        if len(matching_keys) == 1:
            entry = history[matching_keys[0]]
            if isinstance(entry, dict) and isinstance(entry.get("exact_consumer"), str):
                consumer_pin = entry["exact_consumer"]
    return theorem_pin, consumer_pin, tuple(errors)


def _relevant_dirty(path: str, *, selected: str | None, source: str | None) -> bool:
    exact = {
        CONTROL_REL.as_posix(),
        CURRENT_REL.as_posix(),
        EXECUTION_STATE_REL.as_posix(),
        selected,
        source,
    }
    dirty_bus_lifecycle = path.startswith(f"{BUS_REL.as_posix()}/") and path.endswith(
        (".goal.md", ".answer.md")
    )
    return path in exact or dirty_bus_lifecycle


def _bus_symlink_errors(repo: Path, dirty_paths: tuple[str, ...]) -> tuple[str, ...]:
    errors: list[str] = []
    prefix = f"{BUS_REL.as_posix()}/"
    for path in dirty_paths:
        if not path.startswith(prefix):
            continue
        relative = PurePosixPath(path)
        if _has_symlink_component(repo, relative):
            errors.append(f"STARTUP_SYMLINK_COMPONENT:{path}")
    return tuple(errors)


def build_shadow_snapshot(
    repo: Path, owned_paths: tuple[str, ...] = ()
) -> StartupSnapshot:
    """Build one immutable v9-based observation that can never authorize run."""

    repo = repo.resolve()
    fatal: list[str] = []
    warnings: list[str] = []
    guard, lock_error = _acquire_writer_lock(repo)
    if lock_error:
        fatal.append(lock_error)
    fingerprints: list[tuple[PurePosixPath, _PathFingerprint]] = []
    try:
        try:
            control_fingerprint = _path_fingerprint(repo, CONTROL_REL)
            fingerprints.append((CONTROL_REL, control_fingerprint))
        except StartupRuntimeError as exc:
            fatal.append(str(exc))
        try:
            control = _control_identity(_repo_file(repo, CONTROL_REL))
        except StartupRuntimeError as exc:
            control = None
            fatal.append(str(exc))
        else:
            if control.status != "ACTIVE":
                fatal.append(f"STARTUP_CONTROL_NOT_ACTIVE:{control.status}")
            if control.version == 9:
                warnings.append("CONTROL_V9_SHADOW_BASELINE")
            elif control.version == 10:
                try:
                    _validate_battle_v10_identity(control)
                except StartupRuntimeError as exc:
                    fatal.append(str(exc))
            else:
                fatal.append(f"STARTUP_CONTROL_VERSION_INVALID:{control.version}")

        git_state = _git_observation(repo)
        fatal.extend(git_state.errors)
        fatal.extend(_bus_symlink_errors(repo, git_state.dirty_paths))
        context = _shadow_selection_context(repo, git_state)
        selection = context.selection
        fatal.extend(selection.fatal_errors)
        fatal.extend(context.errors)
        warnings.extend(selection.warnings)
        fingerprints.extend(context.fingerprints)
        source_path = context.source_path
        final_tree = context.final_tree
        final_origin = context.final_origin
        selected_physical = (
            selection.selected_goal
            if selection.selected_goal is not None
            and selection.selected_goal.startswith(f"{BUS_REL.as_posix()}/")
            else None
        )
        if selection.selected_goal is not None:
            if selected_physical is None and not selection.selected_goal.startswith(
                "docs/Codex/"
            ):
                fatal.append("STARTUP_SELECTED_GOAL_PATH_INVALID")

        try:
            state_fingerprint = _path_fingerprint(repo, EXECUTION_STATE_REL)
            fingerprints.append((EXECUTION_STATE_REL, state_fingerprint))
        except StartupRuntimeError as exc:
            fatal.append(str(exc))
        state_theorem, state_consumer, state_errors = _state_pins_and_errors(
            repo, selection.selected_goal, selected_physical
        )
        fatal.extend(state_errors)
        exact_theorem = selection.exact_theorem_pin or state_theorem
        exact_consumer = selection.exact_consumer_pin or state_consumer
        if selection.selected_goal is not None and any(
            pin is None
            for pin in (selection.exact_node_pin, selection.exact_source_pin)
        ):
            fatal.append("STARTUP_EXACT_PINS_MISSING")
        blocked_features: list[str] = []
        if selection.selected_goal is not None and exact_theorem is None:
            blocked_features.append("BLOCKED_FEATURE:EXACT_THEOREM_EDGE_UNSELECTED")
        if selection.selected_goal is not None and exact_consumer is None:
            blocked_features.append("BLOCKED_FEATURE:EXACT_CONSUMER_EDGE_UNSELECTED")
        blocked_features.extend(("RUN", "DISPATCH", "MINT", "STATE_WRITE"))

        if git_state.dirty_paths:
            relevant = tuple(
                path
                for path in git_state.dirty_paths
                if _relevant_dirty(
                    path, selected=selection.selected_goal, source=source_path
                )
            )
            foreign = tuple(
                path for path in git_state.dirty_paths if not _is_owned(path, owned_paths)
            )
            warnings.append("GIT_WORKTREE_DIRTY")
            if relevant:
                fatal.append("STARTUP_RELEVANT_DIRTY_PATHS:" + ",".join(relevant[:8]))
            if foreign:
                warnings.append("GIT_FOREIGN_DIRTY_PATHS_PRESENT")
            elif owned_paths:
                warnings.append("GIT_DIRTY_PATHS_WITHIN_OWNED_SCOPE")

        current_task_binding: tuple[PurePosixPath, _PathFingerprint] | None = None
        if selection.selected_goal is not None and selection.selected_goal.startswith(
            "docs/Codex/"
        ):
            current_task_rel = PurePosixPath(selection.selected_goal)
            current_task_binding = next(
                (
                    binding
                    for binding in fingerprints
                    if binding[0] == current_task_rel
                ),
                None,
            )
        ordinary_fingerprints = tuple(
            binding for binding in fingerprints if binding != current_task_binding
        )
        fatal.extend(_recheck_fingerprints(repo, ordinary_fingerprints))
        if current_task_binding is not None:
            current_task_rel, expected_task = current_task_binding
            try:
                observed_task = _path_fingerprint(repo, current_task_rel)
            except StartupRuntimeError:
                observed_task = None
            if observed_task != expected_task:
                fatal.append("STARTUP_CURRENT_TASK_WORKTREE_DRIFT")
        final_git = _git_observation(repo)
        if (
            final_git.status_sha256 != git_state.status_sha256
            or final_git.head != git_state.head
            or final_git.branch != git_state.branch
            or final_git.upstream != git_state.upstream
            or final_git.dirty_paths != git_state.dirty_paths
            or final_git.unmerged_paths != git_state.unmerged_paths
        ):
            fatal.append("STARTUP_GIT_CONCURRENT_MUTATION")
        fatal.extend(final_git.errors)
        lock_recheck = guard.recheck()
        if lock_recheck:
            fatal.append(lock_recheck)
        if final_origin is None:
            warnings.append("GIT_ORIGIN_HEAD_UNAVAILABLE")
        elif git_state.head is not None and final_origin != git_state.head:
            warnings.append("GIT_HEAD_ORIGIN_DRIFT")

        next_action = selection.next_action
        if any(item.startswith("BLOCKED_FEATURE:") for item in blocked_features):
            next_action = "SHADOW_BLOCKED_EXACT_EDGE_SELECTION"
        if fatal:
            next_action = "STOP_FAIL_CLOSED"

        snapshot = StartupSnapshot(
            schema="q3_startup_snapshot.v10.shadow.v1",
            mode=SHADOW_MODE,
            control_sha256=control.sha256 if control else None,
            control_version=control.version if control else None,
            control_status=control.status if control else None,
            git_head=git_state.head,
            git_origin_head=final_origin,
            git_tree=final_tree,
            git_dirty=bool(git_state.dirty_paths),
            selected_goal=selection.selected_goal,
            honesty_state=HONESTY_STATE,
            exact_node_pin=selection.exact_node_pin,
            exact_source_pin=selection.exact_source_pin,
            exact_theorem_pin=exact_theorem,
            exact_consumer_pin=exact_consumer,
            fatal_errors=_compact_messages(fatal),
            blocked_features=tuple(blocked_features),
            warnings=_compact_messages(warnings),
            next_action=next_action,
            run_authorized=False,
        )
    finally:
        guard.close()
    return snapshot
