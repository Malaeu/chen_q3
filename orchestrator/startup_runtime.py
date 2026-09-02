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
from contextlib import contextmanager
from dataclasses import asdict, dataclass, replace
from pathlib import Path, PurePosixPath
from typing import Any, BinaryIO, Iterator

import yaml

from orchestrator.routeb_goal_state import (
    MACHINE_HEADER_RE,
    PAUSED_STATUSES,
    STATUS_RE,
    goal_machine_header_text,
    load_unique_yaml,
)

CONTROL_REL = PurePosixPath("docs/CODEX_CONTROL.md")
BUS_REL = PurePosixPath("docs/routeB_bus")
CURRENT_REL = PurePosixPath("docs/Codex/CURRENT.md")
EXECUTION_STATE_REL = PurePosixPath(
    "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
)
CHANNEL_RUNTIME_REL = PurePosixPath("orchestrator/state/CHANNEL_RUNTIME.json")
TOOL_MANIFEST_REL = PurePosixPath("docs/cartographer/TOOLS.yaml")
CONTROL_FENCE_RE = re.compile(r"```(?:yaml|yml)\s*\n(.*?)```", re.DOTALL | re.IGNORECASE)
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
GOAL_FILE_RE = re.compile(r"^(?P<goal_id>\d{3}[A-Za-z]*)_.+\.goal\.md$")
OPEN_STATUS = "OPEN"
TERMINAL_GOAL_STATUSES = frozenset({"CLOSED", "CLOSED_PHASE0"})
CURRENT_INACTIVE_STATUSES = frozenset({"CLOSED", "EMPTY"})
KNOWN_GOAL_STATUSES = frozenset({OPEN_STATUS, *PAUSED_STATUSES, *TERMINAL_GOAL_STATUSES})
YAML_NULL_SPELLINGS = frozenset({"~", "null"})
SHADOW_MODE = "SHADOW_NOT_AUTHORITY"
AUTHORITATIVE_MODE = "PRODUCTION_V10_READ_ONLY"
SHADOW_SCHEMA = "q3_startup_snapshot.v10.shadow.v1"
AUTHORITATIVE_SCHEMA = "q3_startup_snapshot.v10.v1"
HONESTY_STATE = "CHALLENGER_NOT_RH"
HISTORICAL_PAIRED_BASELINE_COMMIT = "8bddaa6faf35e093f0a8459d15381c4c6d27305e"
# Frozen content identities for the only structured paired v9 goals production
# may treat as history.  Both halves are bound because the answer is what makes
# an otherwise OPEN goal historical rather than executable.
HISTORICAL_STRUCTURED_PAIRED_GOALS = {
    PurePosixPath("docs/routeB_bus/056_k8_muntz_v3_slot_s2_bridge.goal.md"): (
        "PHASE0_INTERFACE_AUDIT",
        "44234adc9766f05b8f528c826e9cd8db66bf315d",
        "bfc419d53b09fb827e783fd35299588683199327",
    ),
    PurePosixPath("docs/routeB_bus/056a_k8_xw8_prolate_ktrial_provenance.goal.md"): (
        "OPEN",
        "6d9a4ca65dc0483250d57728e625599fcd709670",
        "5fafdf3c6a27eb8924d89068de812f4b8e5dd199",
    ),
    PurePosixPath("docs/routeB_bus/056b_muntz_v3_production_export_closure_audit.goal.md"): (
        "OPEN",
        "e364322ac3abd7ff7f3b8d8be7c224f54683604f",
        "40f4ba2bc92df2c1d4a4c50c10ee9c267a161533",
    ),
    PurePosixPath("docs/routeB_bus/056c_muntz_v3_production_core_batch_a.goal.md"): (
        "OPEN",
        "8a77ed29bc9b84aff9ecb80a858e06047ebd1e4b",
        "2c6b838d419bacbe8b1ca773c8ac9afe699b566c",
    ),
    PurePosixPath("docs/routeB_bus/056d_muntz_v3_production_supplier_batch_b.goal.md"): (
        "OPEN",
        "7294b95ffd831818b56af11dc7e11c6e5247df73",
        "415b3eb485d418068b8d022c88d6c3ccce5e8bea",
    ),
    PurePosixPath("docs/routeB_bus/056e_muntz_v3_production_supplier_batch_c.goal.md"): (
        "OPEN",
        "75760779788251a126d156c0a087bb1f5c676f56",
        "d8818bc9e7fe3d37fc3f101ebe31bd18a1dc1f85",
    ),
    PurePosixPath("docs/routeB_bus/056f_muntz_v3_production_supplier_batch_d.goal.md"): (
        "OPEN",
        "36a07aeed73b865ff702c3890d533e9fe335f1c2",
        "71c9e94b9c04288b26ba43f6d9bf3ac81c0914ad",
    ),
    PurePosixPath("docs/routeB_bus/056g_muntz_v3_production_supplier_batch_e.goal.md"): (
        "OPEN",
        "5fb12efd7a263178f86f7b21a901ac2b00117256",
        "744115d00dc881d532925925506da286ed1aee22",
    ),
    PurePosixPath("docs/routeB_bus/056h_muntz_v3_production_supplier_batch_f.goal.md"): (
        "OPEN",
        "e90f065c27b90b5eb05c3ed1c2c4f43cd78ee318",
        "52fd50d27b69ad0d4584a12bbf9ac059929477c7",
    ),
    PurePosixPath("docs/routeB_bus/056i_muntz_v3_production_receiver_batch_g.goal.md"): (
        "OPEN",
        "acbea2ceadc4509713be374c86adf1cf7ee00d9b",
        "9280155986b61a592d53910dd3902447d2074b9f",
    ),
    PurePosixPath("docs/routeB_bus/056j_d0pstar_muntz_centered_coordinate_lock.goal.md"): (
        "OPEN",
        "f720d2d6d7b958104378bf2ec0e2a904d03fd19d",
        "e1f68240b9a56cecc806d870aba2718535c09c46",
    ),
    PurePosixPath("docs/routeB_bus/056k_d0pstar_muntz_galerkin_residual_contract.goal.md"): (
        "OPEN",
        "56182f3e4b8a5065189650cc5a7c0e5197a97170",
        "11547ef881c9668a651d94f46fd096b362f2f37c",
    ),
    PurePosixPath("docs/routeB_bus/056l_d0_log_window_measure_transport.goal.md"): (
        "OPEN",
        "f0e59dacfe12a8dc8d2aea4a60a84dda55cfd4e5",
        "e9a326f35f5e8859a9004cbb5cfbeaea53ede9c1",
    ),
    PurePosixPath("docs/routeB_bus/056m_d0_finite_projection_reconstruction.goal.md"): (
        "OPEN",
        "753cc29abcf49b02cfe21b75de43d496f0c3a117",
        "264acd0877ffbf8bba4e06999016e9a63078a996",
    ),
    PurePosixPath("docs/routeB_bus/056n_d0_selected_projected_mellin_coordinate.goal.md"): (
        "OPEN",
        "1b7236908048aebdbac96c09c8937028ec8058f7",
        "2b68e4555cf8142c5cb1251b13888d1ec0a782e7",
    ),
    PurePosixPath("docs/routeB_bus/056o_d0_full_mellin_gwin_crosswalk.goal.md"): (
        "OPEN",
        "472d1645c42ca4f9a017312e71adbf8c68f4264f",
        "4d1aedacd8c49fc58e4068eae0bfd0905ccdd67f",
    ),
    PurePosixPath("docs/routeB_bus/056p_d0_residual_mellin_linearity_contract.goal.md"): (
        "OPEN",
        "e0ddc665bb87f12ed4ab052ec5945f928fc2a277",
        "2bdf6664b26553e274e80a204e49c88d75802cd0",
    ),
    PurePosixPath("docs/routeB_bus/056q_d0_selected_residual_l2_decay_receiver.goal.md"): (
        "OPEN",
        "a73caea869ff0db0729298655c4bdadc3c52ea6b",
        "6be0e7f91f5b7302eca5589ef8615a4609020640",
    ),
    PurePosixPath("docs/routeB_bus/056r_d0_prolate_source_n_coherence_repair.goal.md"): (
        "OPEN",
        "573e6a61bcf7dbe5af733d72f6f2da7511623093",
        "2bad786d1f2d5c14234ba7a9f078e258bef8f44a",
    ),
    PurePosixPath("docs/routeB_bus/056s_d0_generic_hilbert_basis_weighted_tail.goal.md"): (
        "OPEN",
        "f32ab49acaac4085501e0806cc6742882df0650f",
        "a7eaeece21c6cde27cf29bbab4d22b190adbc4b8",
    ),
    PurePosixPath("docs/routeB_bus/056t_d0_log_window_v_n_m_completeness_bridge.goal.md"): (
        "OPEN",
        "33e6efe16a8e8ab682c2ba15e00397805eb1ace9",
        "7f3facdfabeeea9252db924f734f7a3c3a06f2b5",
    ),
    PurePosixPath("docs/routeB_bus/056u_d0_selected_physical_fourier_energy_receiver.goal.md"): (
        "OPEN",
        "a30ada1acc73610dacb2250086aa0e787d82beef",
        "12c94ac7329ecdac276041f2fc3ee12922009604",
    ),
}
BUS_DIRECT_ENTRY_LIMIT = 4096
GIT_STATUS_PATHS = (
    CONTROL_REL.as_posix(),
    CURRENT_REL.as_posix(),
    EXECUTION_STATE_REL.as_posix(),
    CHANNEL_RUNTIME_REL.as_posix(),
    TOOL_MANIFEST_REL.as_posix(),
)


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
    state_selected_goal: str | None
    source_path: str | None
    final_tree: str | None
    final_origin: str | None
    control_head_blob: str | None
    state_head_blob: str | None
    errors: tuple[str, ...]
    fingerprints: tuple[tuple[PurePosixPath, _PathFingerprint], ...]
    bus_manifest_sha256: str | None
    owned_uncommitted_source_candidate: bool = False


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
                lexical_stat = os.stat(part, dir_fd=directory_fd, follow_symlinks=False)
                if stat.S_ISLNK(lexical_stat.st_mode):
                    raise StartupRuntimeError("STARTUP_SYMLINK_COMPONENT", relative.as_posix())
                opened = os.open(part, flags, dir_fd=directory_fd)
            except StartupRuntimeError:
                raise
            except OSError as exc:
                raise StartupRuntimeError("STARTUP_PATH_INVALID", relative.as_posix()) from exc
            identity = _stat_identity(os.fstat(opened))
            if identity != _stat_identity(lexical_stat):
                os.close(opened)
                raise StartupRuntimeError("STARTUP_PATH_CONCURRENT_MUTATION", relative.as_posix())
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
                raise StartupRuntimeError("STARTUP_PATH_CONCURRENT_MUTATION", relative.as_posix())
        return _PathFingerprint(tuple(identities), digest, git_blob_sha1, git_blob_sha256)
    finally:
        if final_fd is not None:
            os.close(final_fd)
        os.close(directory_fd)


def _git_blob_sha1(raw: bytes) -> str:
    hasher = hashlib.sha1(f"blob {len(raw)}\0".encode("ascii"))
    hasher.update(raw)
    return hasher.hexdigest()


def _historical_structured_pair_matches(
    goal_path: Path,
    answer_path: Path,
    goal_rel: PurePosixPath,
    status: object,
) -> bool:
    expected = HISTORICAL_STRUCTURED_PAIRED_GOALS.get(goal_rel)
    if expected is None or status != expected[0]:
        return False
    try:
        observed = (
            _git_blob_sha1(goal_path.read_bytes()),
            _git_blob_sha1(answer_path.read_bytes()),
        )
    except OSError:
        return False
    return observed == expected[1:]


def _recheck_fingerprints(
    repo: Path,
    fingerprints: tuple[tuple[PurePosixPath, _PathFingerprint], ...],
) -> tuple[str, ...]:
    errors: list[str] = []
    for relative, expected in fingerprints:
        try:
            observed = _path_fingerprint(repo, relative)
        except StartupRuntimeError:
            errors.append(
                "STARTUP_BUS_CONCURRENT_MUTATION"
                if relative == BUS_REL
                else f"STARTUP_PATH_CONCURRENT_MUTATION:{relative.as_posix()}"
            )
            continue
        if observed != expected:
            errors.append(
                "STARTUP_BUS_CONCURRENT_MUTATION"
                if relative == BUS_REL
                else f"STARTUP_PATH_CONCURRENT_MUTATION:{relative.as_posix()}"
            )
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
        body for body in CONTROL_FENCE_RE.findall(text) if re.search(r"(?m)^CONTROL_ID\s*:", body)
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
            header.get("HONESTY_STATE") if isinstance(header.get("HONESTY_STATE"), str) else None
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
        raise StartupRuntimeError("STARTUP_PATH_INVALID", f"outside repository: {path}") from exc


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


def _goal_header_if_present(path: Path) -> dict[str, Any] | None:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise StartupRuntimeError("STARTUP_GOAL_HEADER_INVALID", f"{path}: {exc}") from exc
    if MACHINE_HEADER_RE.search(text) is None:
        return None
    header = goal_machine_header_text(text)
    if header is None:
        raise StartupRuntimeError(
            "STARTUP_GOAL_HEADER_INVALID", f"missing or malformed header: {path}"
        )
    return header


def _goal_header(path: Path) -> dict[str, Any]:
    header = _goal_header_if_present(path)
    if header is None:
        raise StartupRuntimeError(
            "STARTUP_GOAL_HEADER_INVALID", f"missing or malformed header: {path}"
        )
    return header


def _goal_id(
    path: Path,
    header: dict[str, Any],
    *,
    allow_paired_phase_alias: bool = False,
) -> str:
    match = GOAL_FILE_RE.fullmatch(path.name)
    value = header.get("GOAL")
    if match is None or not isinstance(value, str):
        raise StartupRuntimeError("STARTUP_GOAL_IDENTITY_MISMATCH", f"invalid identity: {path}")
    file_goal_id = match.group("goal_id")
    if value != file_goal_id:
        phase_alias = re.fullmatch(r"(?P<base>\d{3})[A-Za-z]+", file_goal_id)
        if (
            allow_paired_phase_alias
            and phase_alias is not None
            and value == phase_alias.group("base")
            and _nonempty_machine_scalar(header, "PHASE")
        ):
            return file_goal_id
        raise StartupRuntimeError(
            "STARTUP_GOAL_IDENTITY_MISMATCH",
            f"machine GOAL {value!r} disagrees with {path.name!r}",
        )
    return file_goal_id


def _nonempty_machine_scalar(mapping: dict[str, Any], key: str) -> bool:
    value = mapping.get(key)
    normalized = value.strip().lower() if isinstance(value, str) else None
    return isinstance(value, str) and bool(normalized) and normalized not in YAML_NULL_SPELLINGS


def _validate_modern_answer(
    goal_path: Path,
    goal_header: dict[str, Any],
    answer_path: Path,
) -> None:
    """Require one exact modern goal/answer closure edge."""

    try:
        answer_header = _goal_header(answer_path)
    except StartupRuntimeError as exc:
        raise StartupRuntimeError("STARTUP_ANSWER_INVALID", str(exc)) from exc

    match = GOAL_FILE_RE.fullmatch(goal_path.name)
    file_goal = match.group("goal_id") if match is not None else None
    goal_value = goal_header.get("GOAL")
    answer_value = answer_header.get("GOAL")
    goal_phase = goal_header.get("PHASE")
    answer_phase = answer_header.get("PHASE")
    goal_node = goal_header.get("NODE")
    answer_node = answer_header.get("NODE")
    phase_alias = (
        re.fullmatch(r"(?P<base>\d{3})[A-Za-z]+", file_goal) if isinstance(file_goal, str) else None
    )
    alias_valid = (
        phase_alias is not None
        and goal_value == phase_alias.group("base")
        and _nonempty_machine_scalar(goal_header, "PHASE")
        and answer_phase == goal_phase
    )
    identity_valid = (
        isinstance(file_goal, str)
        and isinstance(goal_value, str)
        and answer_value == goal_value
        and (goal_value == file_goal or alias_valid)
    )
    phase_valid = goal_phase == answer_phase
    node_valid = (
        _nonempty_machine_scalar(goal_header, "NODE")
        and _nonempty_machine_scalar(answer_header, "NODE")
        and answer_node == goal_node
    )
    result_valid = any(
        _nonempty_machine_scalar(answer_header, key)
        for key in ("EXACT_RESULT", "RESULT", "SUCCESS")
    )
    if (
        not identity_valid
        or not phase_valid
        or not node_valid
        or answer_header.get("STATUS") not in TERMINAL_GOAL_STATUSES
        or not result_valid
    ):
        raise StartupRuntimeError(
            "STARTUP_ANSWER_INVALID",
            f"identity, phase, node, status, or result invalid: {answer_path}",
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
        raise StartupRuntimeError("STARTUP_PATH_CONCURRENT_MUTATION", str(current_path))
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
    missing_node_pin = node is None
    return (
        ShadowGoalSelection(
            selected_goal=task_rel.as_posix(),
            exact_node_pin=node,
            exact_source_pin=source_commit,
            exact_theorem_pin=theorem,
            exact_consumer_pin=consumer,
            fatal_errors=("STARTUP_EXACT_PINS_MISSING",) if missing_node_pin else (),
            warnings=("CURRENT_ACTIVE_FALLBACK_WITHOUT_OPEN_BUS_GOAL",),
            next_action=(
                "STOP_FAIL_CLOSED" if missing_node_pin else "SHADOW_INSPECT_SELECTED_GOAL"
            ),
        ),
        (task_rel, task_fingerprint),
    )


def _physical_bus_paths(
    repo: Path,
    *,
    fingerprint_records: bool = True,
) -> tuple[
    tuple[Path, ...],
    tuple[Path, ...],
    str,
    tuple[tuple[PurePosixPath, _PathFingerprint], ...],
]:
    """Observe only the authoritative direct bus surface.

    Nested directories are deliberately opaque: neither tracked nor ignored
    descendants can become physical goals. Every direct entry participates in
    the fixed-size scan budget, and every direct record contributes its exact
    fingerprint to the concurrency manifest.
    """

    bus = _repo_file(repo, BUS_REL)
    goal_names: list[str] = []
    answer_names: list[str] = []
    records: list[tuple[str, _PathFingerprint]] = []
    bus_fingerprint = _path_fingerprint(repo, BUS_REL)
    try:
        with os.scandir(bus) as scan:
            for entry_count, entry in enumerate(scan, start=1):
                if entry_count > BUS_DIRECT_ENTRY_LIMIT:
                    raise StartupRuntimeError("STARTUP_BUS_SCAN_LIMIT_EXCEEDED")
                candidate = Path(entry.path)
                relative = _lexical_relative(repo, candidate)
                if entry.is_symlink():
                    raise StartupRuntimeError("STARTUP_SYMLINK_COMPONENT", relative.as_posix())
                if not entry.is_file(follow_symlinks=False):
                    continue
                path = relative.as_posix()
                if entry.name.endswith(".goal.md"):
                    goal_names.append(path)
                elif entry.name.endswith(".answer.md"):
                    answer_names.append(path)
                else:
                    continue
                if fingerprint_records:
                    records.append((path, _path_fingerprint(repo, relative)))
    except StartupRuntimeError:
        raise
    except OSError as exc:
        raise StartupRuntimeError("STARTUP_BUS_SCAN_UNAVAILABLE", str(exc)) from exc

    manifest = [
        {
            "path": path,
            "components": fingerprint.components,
            "content_sha256": fingerprint.content_sha256,
            "git_blob_sha1": fingerprint.git_blob_sha1,
            "git_blob_sha256": fingerprint.git_blob_sha256,
        }
        for path, fingerprint in sorted(records)
    ]
    encoded = json.dumps(
        manifest, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8", errors="surrogateescape")
    return (
        tuple(_repo_file(repo, PurePosixPath(name)) for name in sorted(goal_names)),
        tuple(_repo_file(repo, PurePosixPath(name)) for name in sorted(answer_names)),
        hashlib.sha256(encoded).hexdigest(),
        (
            (BUS_REL, bus_fingerprint),
            *tuple((PurePosixPath(path), fingerprint) for path, fingerprint in records),
        ),
    )


def _shadow_selection_context(
    repo: Path,
    git_state: _GitObservation,
    owned_paths: tuple[str, ...] = (),
    *,
    authoritative: bool = False,
    epoch_fingerprints: tuple[tuple[PurePosixPath, _PathFingerprint], ...] = (),
) -> _SelectionContext:
    bus = _repo_file(repo, BUS_REL)
    empty = ShadowGoalSelection(None, None, None, None, None, (), (), "STOP_FAIL_CLOSED")
    if _has_symlink_component(repo, BUS_REL) or not bus.is_dir():
        return _SelectionContext(
            replace(empty, fatal_errors=("STARTUP_BUS_MISSING",)),
            None,
            None,
            None,
            None,
            None,
            None,
            (),
            (),
            None,
        )
    try:
        (
            goal_paths,
            answer_paths,
            bus_manifest_sha256,
            bus_fingerprints,
        ) = _physical_bus_paths(repo, fingerprint_records=not authoritative)
    except StartupRuntimeError as exc:
        return _SelectionContext(
            replace(empty, fatal_errors=(str(exc),)),
            None,
            None,
            None,
            None,
            None,
            None,
            (),
            (),
            None,
        )

    open_goals: list[tuple[Path, dict[str, Any], _PathFingerprint | None]] = []
    paired: list[tuple[Path, Path]] = []
    historical_pairs: list[tuple[Path, Path]] = []
    fatal: list[str] = []
    warnings: list[str] = []
    fingerprints: list[tuple[PurePosixPath, _PathFingerprint]] = list(bus_fingerprints)
    answer_path_set = set(answer_paths)
    for goal_path in goal_paths:
        goal_rel = _lexical_relative(repo, goal_path)
        answer_path = goal_path.with_name(goal_path.name.removesuffix(".goal.md") + ".answer.md")
        answer_rel = _lexical_relative(repo, answer_path)
        if _has_symlink_component(repo, goal_rel) or _has_symlink_component(repo, answer_rel):
            fatal.append(f"STARTUP_SYMLINK_COMPONENT:{goal_rel.as_posix()}")
            continue
        paired_answer = answer_path in answer_path_set
        if authoritative and paired_answer:
            try:
                goal_fingerprint = _path_fingerprint(repo, goal_rel)
                answer_fingerprint = _path_fingerprint(repo, answer_rel)
                fingerprints.extend(
                    ((goal_rel, goal_fingerprint), (answer_rel, answer_fingerprint))
                )
                paired_header = _goal_header_if_present(goal_path)
                if paired_header is None:
                    historical_pairs.append((goal_path, answer_path))
                    continue
                _goal_id(goal_path, paired_header, allow_paired_phase_alias=True)
                paired_status = paired_header.get("STATUS")
                if _historical_structured_pair_matches(
                    goal_path, answer_path, goal_rel, paired_status
                ):
                    historical_pairs.append((goal_path, answer_path))
                    continue
            except StartupRuntimeError as exc:
                fatal.append(str(exc))
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
        answer_available = True
        if paired_answer:
            paired.append((goal_path, answer_path))
            if not answer_path.is_file():
                answer_available = False
                fatal.append(f"STARTUP_ANSWER_INVALID:{answer_rel.as_posix()}")
            else:
                try:
                    fingerprints.append((answer_rel, _path_fingerprint(repo, answer_rel)))
                except StartupRuntimeError as exc:
                    answer_available = False
                    fatal.append(str(exc))
        try:
            header = (
                _goal_header_if_present(goal_path) if paired_answer else _goal_header(goal_path)
            )
            if header is not None:
                _goal_id(
                    goal_path,
                    header,
                    allow_paired_phase_alias=paired_answer,
                )
                status = header.get("STATUS")
                if not isinstance(status, str) or STATUS_RE.fullmatch(status) is None:
                    raise StartupRuntimeError(
                        "STARTUP_GOAL_HEADER_INVALID", f"STATUS missing: {goal_path}"
                    )
            else:
                status = None
        except StartupRuntimeError as exc:
            fatal.append(str(exc))
            continue
        if header is None:
            historical_pairs.append((goal_path, answer_path))
            continue
        historical_expected = HISTORICAL_STRUCTURED_PAIRED_GOALS.get(goal_rel)
        if (
            not authoritative
            and paired_answer
            and answer_available
            and historical_expected is not None
            and status == historical_expected[0]
        ):
            historical_pairs.append((goal_path, answer_path))
            continue
        if status not in KNOWN_GOAL_STATUSES:
            fatal.append(f"STARTUP_UNKNOWN_GOAL_STATUS:{status}:{goal_rel.as_posix()}")
            continue
        answer_valid = False
        if paired_answer and answer_available:
            try:
                _validate_modern_answer(goal_path, header, answer_path)
                answer_valid = True
            except StartupRuntimeError as exc:
                fatal.append(str(exc))
        if paired_answer and status in PAUSED_STATUSES:
            fatal.append(f"STARTUP_ANSWER_INVALID:paused goal has answer:{goal_rel}")
            answer_valid = False
        if answer_valid:
            continue
        if status == OPEN_STATUS:
            open_goals.append((goal_path, header, fingerprint))
        elif status in PAUSED_STATUSES:
            warnings.append(f"PAUSED_RESTORABLE_EXCLUDED:{goal_rel.as_posix()}")
        elif status in TERMINAL_GOAL_STATUSES:
            if not paired_answer:
                fatal.append(f"STARTUP_ANSWER_MISSING:{goal_rel.as_posix()}")
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
        selection = replace(empty, fatal_errors=tuple(fatal), warnings=tuple(warnings))
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
            selection = replace(selection, warnings=tuple(warnings) + selection.warnings)
        except StartupRuntimeError as exc:
            selection = replace(empty, fatal_errors=(str(exc),), warnings=tuple(warnings))

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
                    fingerprints.append((source_rel, _path_fingerprint(repo, source_rel)))
                except StartupRuntimeError as exc:
                    fatal.append(str(exc))

    specs: list[str] = []
    fingerprint_by_path = {
        relative.as_posix(): value for relative, value in (*epoch_fingerprints, *fingerprints)
    }
    upstream = git_state.upstream or (
        f"origin/{git_state.branch}" if git_state.branch else "origin/HEAD"
    )
    identity_specs = ("HEAD", "HEAD^{tree}", upstream)
    if git_state.head is not None:
        specs.extend(identity_specs)
        specs.extend(
            (
                f"HEAD:{CONTROL_REL.as_posix()}",
                f"HEAD:{EXECUTION_STATE_REL.as_posix()}",
            )
        )
        specs.extend(f"HEAD:{relative.as_posix()}" for relative, _ in epoch_fingerprints)
        if historical_pairs:
            specs.append(HISTORICAL_PAIRED_BASELINE_COMMIT)
        for goal_path in goal_paths:
            goal_rel = _lexical_relative(repo, goal_path).as_posix()
            if (
                not authoritative
                or goal_path.with_name(goal_path.name.removesuffix(".goal.md") + ".answer.md")
                not in answer_path_set
            ):
                specs.append(f"HEAD:{goal_rel}")
        if CURRENT_REL.as_posix() in fingerprint_by_path:
            specs.append(f"HEAD:{CURRENT_REL.as_posix()}")
        for goal_path, answer_path in paired:
            for path in (goal_path, answer_path):
                relative = _lexical_relative(repo, path).as_posix()
                specs.append(f"HEAD:{relative}")
        for goal_path, answer_path in historical_pairs:
            for path in (goal_path, answer_path):
                relative = _lexical_relative(repo, path).as_posix()
                specs.extend(
                    (
                        f"HEAD:{relative}",
                        f"{HISTORICAL_PAIRED_BASELINE_COMMIT}:{relative}",
                    )
                )
        if selection.selected_goal and selection.selected_goal.startswith(f"{BUS_REL.as_posix()}/"):
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

    for relative, fingerprint in epoch_fingerprints:
        head_object = checked.get(f"HEAD:{relative.as_posix()}")
        if not _fingerprint_matches_git_blob(fingerprint, head_object[0] if head_object else None):
            fatal.append(f"STARTUP_DECLARED_SURFACE_BLOB_DRIFT:{relative.as_posix()}")

    if git_state.head is not None:
        for goal_path in goal_paths:
            if (
                authoritative
                and goal_path.with_name(goal_path.name.removesuffix(".goal.md") + ".answer.md")
                in answer_path_set
            ):
                continue
            goal_rel = _lexical_relative(repo, goal_path).as_posix()
            head_goal = checked.get(f"HEAD:{goal_rel}")
            if head_goal is None or not _fingerprint_matches_git_blob(
                fingerprint_by_path.get(goal_rel), head_goal[0]
            ):
                fatal.append("STARTUP_GOAL_BLOB_DRIFT")

    for goal_path, answer_path in paired:
        goal_rel = _lexical_relative(repo, goal_path).as_posix()
        answer_rel = _lexical_relative(repo, answer_path).as_posix()
        head_goal = checked.get(f"HEAD:{goal_rel}")
        head_answer = checked.get(f"HEAD:{answer_rel}")
        if head_answer is None:
            fatal.append(f"STARTUP_ANSWER_CLOSURE_UNTRACKED:{answer_rel}")
            continue
        if head_goal is None:
            fatal.append(f"STARTUP_ANSWER_CLOSURE_UNTRACKED:{goal_rel}")
            continue
        if not _fingerprint_matches_git_blob(fingerprint_by_path.get(goal_rel), head_goal[0]):
            fatal.append(f"STARTUP_ANSWER_CLOSURE_BLOB_DRIFT:{goal_rel}")
        if not _fingerprint_matches_git_blob(fingerprint_by_path.get(answer_rel), head_answer[0]):
            fatal.append(f"STARTUP_ANSWER_CLOSURE_BLOB_DRIFT:{answer_rel}")

    baseline_object = checked.get(HISTORICAL_PAIRED_BASELINE_COMMIT)
    baseline_available = (
        baseline_object is not None
        and baseline_object[0] == HISTORICAL_PAIRED_BASELINE_COMMIT
        and baseline_object[1] == "commit"
    )
    if baseline_available or historical_pairs:
        if not baseline_available:
            fatal.append("STARTUP_HISTORICAL_PAIRED_BASELINE_INVALID")
        if baseline_available:
            for goal_path, answer_path in historical_pairs:
                pair_valid = True
                for path in (goal_path, answer_path):
                    relative = _lexical_relative(repo, path).as_posix()
                    baseline_blob = checked.get(f"{HISTORICAL_PAIRED_BASELINE_COMMIT}:{relative}")
                    head_blob = checked.get(f"HEAD:{relative}")
                    if (
                        baseline_blob is None
                        or head_blob is None
                        or baseline_blob[1] != "blob"
                        or head_blob[1] != "blob"
                        or baseline_blob[0] != head_blob[0]
                        or not _fingerprint_matches_git_blob(
                            fingerprint_by_path.get(relative), head_blob[0]
                        )
                    ):
                        pair_valid = False
                if not pair_valid:
                    fatal.append(
                        "STARTUP_HISTORICAL_PAIRED_BLOB_DRIFT:"
                        f"{_lexical_relative(repo, goal_path).as_posix()}"
                    )

    final_tree = None
    final_origin = None
    owned_uncommitted_source_candidate = False
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
                source_fingerprint = fingerprint_by_path.get(source_path)
                owned_uncommitted_source_candidate = _owned_uncommitted_source_candidate(
                    source_path,
                    source_fingerprint,
                    head_blob,
                    git_state,
                    owned_paths,
                )
                if (
                    not _fingerprint_matches_git_blob(source_fingerprint, head_blob)
                    and not owned_uncommitted_source_candidate
                ):
                    fatal.append("STARTUP_SOURCE_WORKTREE_DRIFT")
                if pin_object is None:
                    fatal.append("STARTUP_SOURCE_PIN_INVALID")
                elif pin_object[1] == "blob":
                    if owned_uncommitted_source_candidate and head_blob is None:
                        blob_matches = _fingerprint_matches_git_blob(
                            source_fingerprint, pin_object[0]
                        )
                    else:
                        blob_matches = pin_object[0] == head_blob
                    if not blob_matches:
                        fatal.append("STARTUP_SOURCE_BLOB_DRIFT")
                elif pin_object[1] == "commit":
                    if pinned_source is None and not owned_uncommitted_source_candidate:
                        fatal.append("STARTUP_SOURCE_COMMIT_PIN_DRIFT")
                    elif pinned_source is not None and pinned_source[0] != head_blob:
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

    if git_state.head is not None and CURRENT_REL.as_posix() in fingerprint_by_path:
        head_current = checked.get(f"HEAD:{CURRENT_REL.as_posix()}")
        if not _fingerprint_matches_git_blob(
            fingerprint_by_path[CURRENT_REL.as_posix()],
            head_current[0] if head_current else None,
        ):
            fatal.append("STARTUP_CURRENT_BLOB_DRIFT")

    fatal.extend(selection.fatal_errors)
    fatal = list(dict.fromkeys(fatal))
    state_selected_goal = selection.selected_goal
    selection = replace(
        selection,
        selected_goal=None if fatal else selection.selected_goal,
        exact_node_pin=None if fatal else selection.exact_node_pin,
        exact_source_pin=None if fatal else selection.exact_source_pin,
        exact_theorem_pin=None if fatal else selection.exact_theorem_pin,
        exact_consumer_pin=None if fatal else selection.exact_consumer_pin,
        fatal_errors=tuple(fatal),
        next_action="STOP_FAIL_CLOSED" if fatal else selection.next_action,
    )
    control_object = checked.get(f"HEAD:{CONTROL_REL.as_posix()}")
    state_object = checked.get(f"HEAD:{EXECUTION_STATE_REL.as_posix()}")
    return _SelectionContext(
        selection,
        state_selected_goal,
        source_path,
        final_tree,
        final_origin,
        control_object[0] if control_object else None,
        state_object[0] if state_object else None,
        (),
        tuple(fingerprints),
        bus_manifest_sha256,
        owned_uncommitted_source_candidate,
    )


def select_v10_shadow_goal(
    repo: Path, *, git_state: _GitObservation | None = None
) -> ShadowGoalSelection:
    """Select exactly one global OPEN physical goal, without numeric authority."""

    repo = repo.resolve()
    observed = git_state if git_state is not None else _git_observation(repo)
    return _shadow_selection_context(repo, observed).selection


def _git_observation(repo: Path, *, owned_paths: tuple[str, ...] = ()) -> _GitObservation:
    git_env = {**os.environ, "GIT_OPTIONAL_LOCKS": "0"}
    status = subprocess.run(
        [
            "git",
            "status",
            "--porcelain=v2",
            "-z",
            "--branch",
            "--untracked-files=normal",
            "--",
            *GIT_STATUS_PATHS,
            *owned_paths,
        ],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        env=git_env,
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
    others_stdout = b""
    if owned_paths:
        others = subprocess.run(
            [
                "git",
                "ls-files",
                "--others",
                "--exclude-standard",
                "-z",
                "--",
                *owned_paths,
            ],
            cwd=repo,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            env=git_env,
        )
        if others.returncode != 0:
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
        others_stdout = others.stdout
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
    dirty.extend(decode(record) for record in others_stdout.split(b"\0") if record)
    dirty = list(dict.fromkeys(dirty))
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
        hashlib.sha256(status.stdout + b"\0LS_FILES_OTHERS\0" + others_stdout).hexdigest(),
        errors,
    )


def _batch_check(repo: Path, specs: tuple[str, ...]) -> dict[str, tuple[str, str] | None]:
    result = subprocess.run(
        ["git", "cat-file", "--batch-check", "-Z"],
        cwd=repo,
        check=False,
        input=b"".join(spec.encode("utf-8", errors="surrogateescape") + b"\0" for spec in specs),
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        env={**os.environ, "GIT_OPTIONAL_LOCKS": "0"},
    )
    records = result.stdout.split(b"\0")
    checked: dict[str, tuple[str, str] | None] = {}
    for index, spec in enumerate(specs):
        fields = records[index].rsplit(b" ", 2) if index < len(records) else []
        checked[spec] = (
            (fields[0].decode("ascii"), fields[1].decode("ascii"))
            if len(fields) == 3 and fields[1] in {b"blob", b"commit", b"tree", b"tag"}
            else None
        )
    return checked


def _is_owned(path: str, owned_paths: tuple[str, ...]) -> bool:
    candidate = PurePosixPath(path)
    for value in owned_paths:
        owned = PurePosixPath(value)
        if candidate == owned or owned in candidate.parents or candidate in owned.parents:
            return True
    return False


def _dirty_path_covers(path: str, target: str) -> bool:
    """Treat a collapsed untracked parent as covering an exact descendant."""

    dirty = PurePosixPath(path)
    exact = PurePosixPath(target)
    return dirty == exact or dirty in exact.parents


def _owned_uncommitted_source_candidate(
    source_path: str | None,
    source_fingerprint: _PathFingerprint | None,
    head_blob: str | None,
    git_state: _GitObservation,
    owned_paths: tuple[str, ...],
) -> bool:
    return (
        source_path is not None
        and source_fingerprint is not None
        and PurePosixPath(source_path).suffix == ".lean"
        and _is_owned(source_path, owned_paths)
        and (
            any(_dirty_path_covers(path, source_path) for path in git_state.dirty_paths)
            or head_blob is None
        )
    )


def _load_unique_json(path: Path, *, expected: _PathFingerprint | None = None) -> dict[str, Any]:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate key {key!r}")
            result[key] = value
        return result

    try:
        raw = path.read_bytes()
        if expected is not None and hashlib.sha256(raw).hexdigest() != expected.content_sha256:
            raise StartupRuntimeError("STARTUP_PATH_CONCURRENT_MUTATION", str(path))
        payload = json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object)
    except StartupRuntimeError:
        raise
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


def _valid_phase_key(value: object) -> bool:
    fields = {
        "route_id",
        "front_id",
        "source_object_family_id",
        "terminal_consumer_id",
        "honesty_state",
        "convention_lock_id",
    }
    return (
        isinstance(value, dict)
        and fields.issubset(value)
        and all(isinstance(value[field], str) and value[field] for field in fields)
    )


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
        raise StartupRuntimeError("WRITER_LOCK_IDENTITY_INVALID", "commondir is symlink")
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


@contextmanager
def _startup_read_epoch(
    repo: Path,
) -> Iterator[tuple[_WriterLockGuard, str | None]]:
    """Keep one writer-lock epoch open across startup and registry reads."""

    guard, lock_error = _acquire_writer_lock(repo.resolve())
    try:
        yield guard, lock_error
    finally:
        guard.close()


def _state_pins_and_errors(
    repo: Path,
    selected_goal: str | None,
    selected_physical: str | None,
    state_fingerprint: _PathFingerprint | None,
    *,
    compare_selector: bool = True,
) -> tuple[str | None, str | None, tuple[str, ...]]:
    if _has_symlink_component(repo, EXECUTION_STATE_REL):
        return None, None, ("STARTUP_SYMLINK_COMPONENT:execution-state",)
    try:
        state = _load_unique_json(_repo_file(repo, EXECUTION_STATE_REL), expected=state_fingerprint)
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
    if compare_selector and selected_physical is not None:
        match = GOAL_FILE_RE.fullmatch(Path(selected_physical).name)
        expected_id = match.group("goal_id")[:3] if match else None
        if (
            current.get("selected_bus_goal_path") != selected_physical
            or current.get("selected_bus_goal_nnn") != expected_id
        ):
            errors.append("STARTUP_SELECTOR_STATE_DRIFT")
    elif compare_selector and selected_state_path not in {None, ""}:
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
            key for key in history if isinstance(key, str) and normalized.startswith(key.lower())
        )
        if len(matching_keys) == 1:
            entry = history[matching_keys[0]]
            if isinstance(entry, dict) and isinstance(entry.get("exact_consumer"), str):
                consumer_pin = entry["exact_consumer"]
    return theorem_pin, consumer_pin, tuple(errors)


def _relevant_dirty(path: str, *, selected: str | None, source: str | None) -> bool:
    exact = {
        CONTROL_REL.as_posix(),
        EXECUTION_STATE_REL.as_posix(),
        CHANNEL_RUNTIME_REL.as_posix(),
        TOOL_MANIFEST_REL.as_posix(),
        selected,
        source,
    }
    selected_physical = selected is not None and selected.startswith(f"{BUS_REL.as_posix()}/")
    if not selected_physical:
        exact.add(CURRENT_REL.as_posix())
    relative = PurePosixPath(path)
    top_level_goal = relative.parent == BUS_REL and path.endswith(".goal.md")
    selected_answer = (
        selected_physical
        and selected is not None
        and path == selected.removesuffix(".goal.md") + ".answer.md"
    )
    return (
        any(target is not None and _dirty_path_covers(path, target) for target in exact)
        or top_level_goal
        or selected_answer
    )


def _validate_declared_startup_surfaces(
    repo: Path,
    fingerprints: tuple[tuple[PurePosixPath, _PathFingerprint], ...],
) -> tuple[str, ...]:
    """Validate non-selector surfaces declared for production startup."""

    by_path = dict(fingerprints)
    errors: list[str] = []
    try:
        channel = _load_unique_json(
            _repo_file(repo, CHANNEL_RUNTIME_REL),
            expected=by_path.get(CHANNEL_RUNTIME_REL),
        )
        required_channel_fields = {
            "control_status",
            "active_proshka_phase",
            "active_exploration",
            "last_exploration_close",
            "mathematical_authority_mode",
            "px_rh_claim_state",
            "operational_action_pending",
            "meter",
        }
        meter_fields = {
            "phases_opened",
            "fresh_chats_opened",
            "delegated_strategic_review_calls",
            "exploration_review_calls",
            "px_rh_claim_requests",
            "ordinary_goal_close_calls",
            "mathematical_owner_deferral_violations",
            "fanout_violations",
            "forced_rollovers",
        }
        meter = channel.get("meter")
        if (
            channel.get("schema") != "q3_channel_runtime.v1"
            or not required_channel_fields.issubset(channel)
            or channel.get("control_status") != "ACTIVE"
            or channel.get("mathematical_authority_mode") != "CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM"
            or channel.get("px_rh_claim_state")
            not in {"NOT_READY", "READY_FOR_OWNER", "AUTHORIZED", "DECLINED"}
            or not isinstance(meter, dict)
            or not meter_fields.issubset(meter)
            or any(type(meter[field]) is not int or meter[field] < 0 for field in meter_fields)
            or meter["fresh_chats_opened"] > meter["phases_opened"] + meter["forced_rollovers"]
            or meter["mathematical_owner_deferral_violations"] != 0
            or meter["fanout_violations"] != 0
            or meter["ordinary_goal_close_calls"] != 0
            or channel["last_exploration_close"] is not None
            and not isinstance(channel["last_exploration_close"], dict)
            or channel["operational_action_pending"] is not None
            and not isinstance(channel["operational_action_pending"], dict)
        ):
            raise StartupRuntimeError("STARTUP_CHANNEL_RUNTIME_INVALID")
        phase = channel["active_proshka_phase"]
        if phase is not None and (
            not isinstance(phase, dict)
            or not _valid_phase_key(phase.get("phase_key"))
            or phase.get("status") == "ACTIVE"
            and (
                not isinstance(phase.get("conversation_id"), str)
                or not phase.get("conversation_id", "").strip()
            )
        ):
            raise StartupRuntimeError("STARTUP_CHANNEL_RUNTIME_INVALID")
        exploration = channel["active_exploration"]
        if exploration is not None and (
            not isinstance(exploration, dict)
            or not _valid_phase_key(exploration.get("phase_key"))
            or not isinstance(exploration.get("candidates", []), list)
            or len(exploration.get("candidates", [])) > 5
            or not isinstance(exploration.get("cycles", []), list)
            or len(exploration.get("cycles", [])) > 12
            or type(exploration.get("proshka_review_count", 0)) is not int
            or exploration.get("proshka_review_count", 0) > 1
        ):
            raise StartupRuntimeError("STARTUP_CHANNEL_RUNTIME_INVALID")
    except StartupRuntimeError as exc:
        errors.append(
            str(exc)
            if exc.code == "STARTUP_CHANNEL_RUNTIME_INVALID"
            else f"STARTUP_CHANNEL_RUNTIME_INVALID:{exc}"
        )

    manifest_path = _repo_file(repo, TOOL_MANIFEST_REL)
    manifest_fingerprint = by_path.get(TOOL_MANIFEST_REL)
    try:
        raw = manifest_path.read_bytes()
        if (
            manifest_fingerprint is None
            or hashlib.sha256(raw).hexdigest() != manifest_fingerprint.content_sha256
        ):
            raise StartupRuntimeError("STARTUP_PATH_CONCURRENT_MUTATION")
        manifest = load_unique_yaml(raw.decode("utf-8"))
        mapping_sections = (
            "meta",
            "status_semantics",
            "mode_semantics",
            "tool_contract",
            "startup_contract",
            "memory_event_routes",
            "data_surfaces",
            "tool_families",
            "dynamic_queries",
            "tool_lifecycle",
        )
        if not isinstance(manifest, dict) or manifest.get("schema") != "q3_tool_manifest.v2":
            raise StartupRuntimeError("STARTUP_TOOL_MANIFEST_INVALID")
        if any(not isinstance(manifest.get(section), dict) for section in mapping_sections):
            raise StartupRuntimeError("STARTUP_TOOL_MANIFEST_INVALID")
        if not isinstance(manifest.get("known_hazards"), list):
            raise StartupRuntimeError("STARTUP_TOOL_MANIFEST_INVALID")

        status_values = manifest["status_semantics"].get("values")
        mode_values = manifest["mode_semantics"].get("values")
        families = manifest["tool_families"]
        startup_validation = manifest["startup_contract"].get("validation")
        required_contract_fields = manifest["tool_contract"].get("required_fields")
        expected_status_values = {
            "ENABLED",
            "AVAILABLE",
            "DEGRADED",
            "DISCONNECTED",
            "RETIRED",
            "BROKEN",
            "PLANNED",
        }
        expected_mode_values = {
            "READ_ONLY",
            "WRITES_DERIVED",
            "WRITES_CANONICAL",
            "NETWORK_WRITE",
            "EXTERNAL",
        }
        if (
            not isinstance(status_values, list)
            or not all(isinstance(value, str) for value in status_values)
            or set(status_values) != expected_status_values
            or not isinstance(mode_values, list)
            or not all(isinstance(value, str) for value in mode_values)
            or set(mode_values) != expected_mode_values
            or not families
            or not isinstance(startup_validation, dict)
            or startup_validation.get("command") != "python3 orchestrator/workflow_runtime.py plan"
            or startup_validation.get("writes") is not False
            or not isinstance(required_contract_fields, list)
            or not {
                "id",
                "status",
                "audience",
                "mode",
                "path_or_paths",
                "invocation",
                "trigger",
                "writes",
                "approval",
                "authority",
                "records_to",
                "last_verified",
            }.issubset(required_contract_fields)
        ):
            raise StartupRuntimeError("STARTUP_TOOL_MANIFEST_INVALID")

        required_tool_fields = {
            "id",
            "status",
            "audience",
            "mode",
            "trigger",
            "writes",
            "approval",
            "authority",
            "records_to",
            "last_verified",
        }
        allowed_audiences = {"CODEX", "CLAUDE_CODE", "HUMAN"}
        seen_ids: set[str] = set()
        for family in families.values():
            if not isinstance(family, dict) or not isinstance(family.get("tools"), list):
                raise StartupRuntimeError("STARTUP_TOOL_MANIFEST_INVALID")
            for tool in family["tools"]:
                if not isinstance(tool, dict) or not required_tool_fields.issubset(tool):
                    raise StartupRuntimeError("STARTUP_TOOL_MANIFEST_INVALID")
                tool_id = tool["id"]
                audience = tool["audience"]
                if (
                    not isinstance(tool_id, str)
                    or not tool_id
                    or tool_id in seen_ids
                    or tool["status"] not in status_values
                    or tool["mode"] not in mode_values
                    or not isinstance(audience, list)
                    or not audience
                    or any(item not in allowed_audiences for item in audience)
                    or not isinstance(tool["writes"], bool)
                    or (tool["mode"] == "READ_ONLY" and tool["writes"])
                    or (tool["writes"] and tool["approval"] == "NONE")
                    or ("path" not in tool and "paths" not in tool)
                    or not any(key in tool for key in ("invoke", "read_invoke", "write_invoke"))
                ):
                    raise StartupRuntimeError("STARTUP_TOOL_MANIFEST_INVALID")
                seen_ids.add(tool_id)
        for route in manifest["memory_event_routes"].values():
            run_ids = route.get("run", []) if isinstance(route, dict) else None
            if (
                not isinstance(route, dict)
                or not isinstance(run_ids, list)
                or any(item not in seen_ids for item in run_ids)
            ):
                raise StartupRuntimeError("STARTUP_TOOL_MANIFEST_INVALID")
    except StartupRuntimeError as exc:
        errors.append(
            str(exc)
            if exc.code == "STARTUP_TOOL_MANIFEST_INVALID"
            else f"STARTUP_TOOL_MANIFEST_INVALID:{exc}"
        )
    except (OSError, UnicodeDecodeError, yaml.YAMLError) as exc:
        errors.append(f"STARTUP_TOOL_MANIFEST_INVALID:{exc}")
    return tuple(errors)


def _build_startup_snapshot(
    repo: Path,
    owned_paths: tuple[str, ...] = (),
    *,
    authoritative: bool,
    _epoch_guard: _WriterLockGuard | None = None,
    _epoch_lock_error: str | None = None,
) -> StartupSnapshot:
    """Build one immutable startup observation under a single read epoch."""

    repo = repo.resolve()
    fatal: list[str] = []
    warnings: list[str] = []
    owns_guard = _epoch_guard is None
    if owns_guard:
        guard, lock_error = _acquire_writer_lock(repo)
    else:
        guard = _epoch_guard
        lock_error = _epoch_lock_error
        assert guard is not None
    if lock_error:
        fatal.append(lock_error)
    fingerprints: list[tuple[PurePosixPath, _PathFingerprint]] = []
    try:
        control_fingerprint: _PathFingerprint | None = None
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
            if authoritative:
                try:
                    _validate_battle_v10_identity(control)
                except StartupRuntimeError as exc:
                    fatal.append(str(exc))
            elif control.version == 9:
                warnings.append("CONTROL_V9_SHADOW_BASELINE")
            elif control.version == 10:
                try:
                    _validate_battle_v10_identity(control)
                except StartupRuntimeError as exc:
                    fatal.append(str(exc))
            else:
                fatal.append(f"STARTUP_CONTROL_VERSION_INVALID:{control.version}")

        declared_fingerprints: list[tuple[PurePosixPath, _PathFingerprint]] = []
        if authoritative:
            for declared_surface in (CHANNEL_RUNTIME_REL, TOOL_MANIFEST_REL):
                try:
                    binding = (
                        declared_surface,
                        _path_fingerprint(repo, declared_surface),
                    )
                    declared_fingerprints.append(binding)
                    fingerprints.append(binding)
                except StartupRuntimeError as exc:
                    fatal.append(str(exc))
            fatal.extend(_validate_declared_startup_surfaces(repo, tuple(declared_fingerprints)))

        git_state = _git_observation(repo, owned_paths=owned_paths)
        fatal.extend(git_state.errors)
        context = _shadow_selection_context(
            repo,
            git_state,
            owned_paths,
            authoritative=authoritative,
            epoch_fingerprints=tuple(declared_fingerprints),
        )
        selection = context.selection
        fatal.extend(selection.fatal_errors)
        fatal.extend(context.errors)
        warnings.extend(selection.warnings)
        fingerprints.extend(context.fingerprints)
        source_path = context.source_path
        final_tree = context.final_tree
        final_origin = context.final_origin
        control_head_blob = context.control_head_blob
        state_head_blob = context.state_head_blob
        state_selected_goal = context.state_selected_goal
        selected_physical = (
            state_selected_goal
            if state_selected_goal is not None
            and state_selected_goal.startswith(f"{BUS_REL.as_posix()}/")
            else None
        )
        if selection.selected_goal is not None:
            if selected_physical is None and not selection.selected_goal.startswith("docs/Codex/"):
                fatal.append("STARTUP_SELECTED_GOAL_PATH_INVALID")

        state_fingerprint: _PathFingerprint | None = None
        try:
            state_fingerprint = _path_fingerprint(repo, EXECUTION_STATE_REL)
            fingerprints.append((EXECUTION_STATE_REL, state_fingerprint))
        except StartupRuntimeError as exc:
            fatal.append(str(exc))
        state_theorem, state_consumer, state_errors = _state_pins_and_errors(
            repo,
            state_selected_goal,
            selected_physical,
            state_fingerprint,
            compare_selector=context.bus_manifest_sha256 is not None,
        )
        fatal.extend(state_errors)
        if git_state.head is not None:
            if control_head_blob is not None and not _fingerprint_matches_git_blob(
                control_fingerprint,
                control_head_blob,
            ):
                fatal.append("STARTUP_CONTROL_BLOB_DRIFT")
            if state_head_blob is not None and not _fingerprint_matches_git_blob(
                state_fingerprint,
                state_head_blob,
            ):
                fatal.append("STARTUP_STATE_BLOB_DRIFT")
        exact_theorem = selection.exact_theorem_pin or state_theorem
        exact_consumer = selection.exact_consumer_pin or state_consumer
        if selection.selected_goal is not None and any(
            pin is None for pin in (selection.exact_node_pin, selection.exact_source_pin)
        ):
            fatal.append("STARTUP_EXACT_PINS_MISSING")
        blocked_features: list[str] = []
        if selection.selected_goal is not None and exact_theorem is None:
            blocked_features.append("BLOCKED_FEATURE:EXACT_THEOREM_EDGE_UNSELECTED")
        if selection.selected_goal is not None and exact_consumer is None:
            blocked_features.append("BLOCKED_FEATURE:EXACT_CONSUMER_EDGE_UNSELECTED")
        owned_dirty_candidate = context.owned_uncommitted_source_candidate
        if owned_dirty_candidate:
            blocked_features.append("BLOCKED_FEATURE:OWNED_DIRTY_CANDIDATE_UNCOMMITTED")
        if not authoritative:
            blocked_features.extend(("RUN", "DISPATCH", "MINT", "STATE_WRITE"))

        if git_state.dirty_paths or owned_dirty_candidate:
            relevant = tuple(
                path
                for path in git_state.dirty_paths
                if _relevant_dirty(path, selected=selection.selected_goal, source=source_path)
                and not (
                    owned_dirty_candidate
                    and source_path is not None
                    and _dirty_path_covers(path, source_path)
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
                (binding for binding in fingerprints if binding[0] == current_task_rel),
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
        final_git = _git_observation(repo, owned_paths=owned_paths)
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
        if authoritative:
            next_action = {
                "SHADOW_INSPECT_SELECTED_GOAL": "INSPECT_SELECTED_GOAL",
                "SHADOW_STOP_NO_GOAL": "STOP_NO_GOAL",
            }.get(next_action, next_action)
        if any(item.startswith("BLOCKED_FEATURE:") for item in blocked_features):
            next_action = (
                "BLOCKED_EXACT_EDGE_SELECTION"
                if authoritative
                else "SHADOW_BLOCKED_EXACT_EDGE_SELECTION"
            )
        if fatal:
            selection = replace(
                selection,
                selected_goal=None,
                exact_node_pin=None,
                exact_source_pin=None,
                exact_theorem_pin=None,
                exact_consumer_pin=None,
                next_action="STOP_FAIL_CLOSED",
            )
            exact_theorem = None
            exact_consumer = None
            next_action = "STOP_FAIL_CLOSED"

        run_authorized = bool(
            authoritative
            and not fatal
            and selection.selected_goal is not None
            and all(
                isinstance(pin, str) and pin
                for pin in (
                    selection.exact_node_pin,
                    selection.exact_source_pin,
                    exact_theorem,
                    exact_consumer,
                )
            )
            and not blocked_features
        )
        snapshot = StartupSnapshot(
            schema=AUTHORITATIVE_SCHEMA if authoritative else SHADOW_SCHEMA,
            mode=AUTHORITATIVE_MODE if authoritative else SHADOW_MODE,
            control_sha256=control.sha256 if control else None,
            control_version=control.version if control else None,
            control_status=control.status if control else None,
            git_head=git_state.head,
            git_origin_head=final_origin,
            git_tree=final_tree,
            git_dirty=bool(git_state.dirty_paths) or owned_dirty_candidate,
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
            run_authorized=run_authorized,
        )
    finally:
        if owns_guard:
            guard.close()
    return snapshot


def build_shadow_snapshot(
    repo: Path,
    owned_paths: tuple[str, ...] = (),
    *,
    _epoch_guard: _WriterLockGuard | None = None,
    _epoch_lock_error: str | None = None,
) -> StartupSnapshot:
    """Build the non-authoritative v9/v10 comparison snapshot."""

    return _build_startup_snapshot(
        repo,
        owned_paths,
        authoritative=False,
        _epoch_guard=_epoch_guard,
        _epoch_lock_error=_epoch_lock_error,
    )


def build_startup_snapshot(
    repo: Path,
    owned_paths: tuple[str, ...] = (),
    *,
    _epoch_guard: _WriterLockGuard | None = None,
    _epoch_lock_error: str | None = None,
) -> StartupSnapshot:
    """Build the production Control-v10 snapshot; v9 fails closed."""

    return _build_startup_snapshot(
        repo,
        owned_paths,
        authoritative=True,
        _epoch_guard=_epoch_guard,
        _epoch_lock_error=_epoch_lock_error,
    )
