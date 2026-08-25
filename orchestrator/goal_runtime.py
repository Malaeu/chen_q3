#!/usr/bin/env python3
"""Read-only GOAL_RUN contract validator and physical-goal selector.

AUTOPILOT_000 deliberately stops before dispatch, goal minting, durable attempt
records, and database writes.  It decides what a later runner would be allowed
to do and fails closed on ambiguous physical state.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from collections.abc import Callable
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path, PurePosixPath
from typing import Any

import yaml

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from orchestrator import spine, three_body_loop  # noqa: E402
from orchestrator.routeb_goal_state import (  # noqa: E402
    PAUSED_STATUSES,
    STATUS_RE,
    goal_machine_header_text,
    load_unique_yaml,
)

DEFAULT_BUS = REPO_ROOT / "docs" / "routeB_bus"
CHANNEL_RUNTIME_REL = PurePosixPath("orchestrator/state/CHANNEL_RUNTIME.json")
FENCE_RE = re.compile(r"```(?:yaml|yml)\s*\n(.*?)```", re.DOTALL | re.IGNORECASE)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
OPERATIVE_RE = re.compile(r"^(?:TRY|KILL|RUN)_[A-Z0-9_]+$")
GOAL_FILE_RE = re.compile(r"^(?P<goal_id>\d{3}[A-Za-z]*)_.+\.goal\.md$")
ANSWER_FILE_RE = re.compile(r"^(?P<goal_id>\d{3}[A-Za-z]*)_.+\.answer\.md$")
GOAL_RUN_RE = re.compile(r"^GOAL(?P<goal_id>\d{3}[A-Za-z]*)-(?P<stamp>\d{8}T\d{6}Z)$")
RFC3339_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})$"
)
GRANT_RE = re.compile(r"^[A-Z][A-Z0-9_]{2,127}$")
LEASE_HOLDERS = frozenset({"CODEX_MAC", "CODEX_LINUX"})
REQUIRED_GRANT_FORBIDDENS = frozenset(
    {"PAID_EXTERNAL_CALL", "DESTRUCTIVE_ACTION", "PUBLICATION", "PX_RH_CLAIM"}
)

NEXT_SPEC_FIELDS = frozenset(
    {
        "schema",
        "target_id",
        "exact_statement_or_task",
        "terminal_consumer",
        "source_objects",
        "required_inputs",
        "forbidden_shortcuts",
        "validation",
        "success_condition",
        "failure_code",
        "source_provenance",
        "phase_key",
        "phase_key_change",
        "px_rh_claim",
    }
)
PROVENANCE_FIELDS = frozenset(
    {
        "origin",
        "source_path",
        "source_sha256",
        "operative_class",
        "source_commit",
        "receipt_path",
        "receipt_sha256",
    }
)
SOURCE_BOUND_SPEC_FIELDS = NEXT_SPEC_FIELDS - {"source_provenance"}
SOURCE_RECEIPT_FIELDS = frozenset(
    {
        "schema",
        "origin",
        "source_path",
        "source_sha256",
        "next_goal_spec_sha256",
        "conversation_id",
        "response_id",
        "operative_class",
        "outcome_guard_path",
    }
)
GRANT_RESOLUTION_FIELDS = frozenset(
    {"schema", "grant_id", "status", "scope_goal_file", "allowed_actions", "forbidden_actions"}
)
RUNTIME_FIELDS = frozenset(
    {
        "schema",
        "goal_run_id",
        "goal_file",
        "goal_sha256",
        "source_commit",
        "answer_file",
        "mathematical_phase_key_sha256",
        "state",
        "cycle_index",
        "stall_counter",
        "last_attempt_id",
        "next_target",
        "next_action",
        "operational_grant_id",
        "lease",
    }
)
RUNTIME_STATES = frozenset(
    {
        "BOOTSTRAP",
        "SELECTING",
        "RUNNING",
        "BOUNDED_EXPLORATION",
        "REQUESTING_PROSHKA",
        "CLOSING",
        "CLOSE_RETRY_PENDING",
        "CLOSED",
        "STOPPED_FAIL_CLOSED",
        "STOPPED_CLEAN",
        "STOP_OWNER_REQUIRED",
    }
)
NEXT_ACTIONS = frozenset(
    {
        "SELECT_EXACT_GOAL",
        "CONTINUE_STEP",
        "CLOSE_GOAL",
        "RETRY_CLOSE",
        "MINT_READY",
        "REQUEST_STRATEGIC_REVIEW",
        "VALIDATE_PHASE_TRANSITION",
        "STOP",
    }
)
STATE_ACTIONS = {
    "BOOTSTRAP": frozenset({"SELECT_EXACT_GOAL", "STOP"}),
    "SELECTING": frozenset(
        {
            "SELECT_EXACT_GOAL",
            "MINT_READY",
            "REQUEST_STRATEGIC_REVIEW",
            "VALIDATE_PHASE_TRANSITION",
            "STOP",
        }
    ),
    "RUNNING": frozenset({"CONTINUE_STEP", "REQUEST_STRATEGIC_REVIEW", "CLOSE_GOAL", "STOP"}),
    "BOUNDED_EXPLORATION": frozenset(
        {"CONTINUE_STEP", "REQUEST_STRATEGIC_REVIEW", "STOP"}
    ),
    "REQUESTING_PROSHKA": frozenset({"REQUEST_STRATEGIC_REVIEW", "STOP"}),
    "CLOSING": frozenset({"CLOSE_GOAL", "STOP"}),
    "CLOSE_RETRY_PENDING": frozenset({"RETRY_CLOSE", "STOP"}),
    "CLOSED": frozenset({"MINT_READY", "VALIDATE_PHASE_TRANSITION", "STOP"}),
    "STOPPED_FAIL_CLOSED": frozenset({"STOP"}),
    "STOPPED_CLEAN": frozenset({"STOP"}),
    "STOP_OWNER_REQUIRED": frozenset({"STOP"}),
}


class GoalRuntimeError(ValueError):
    """Fail-closed AUTOPILOT_000 decision."""

    def __init__(self, code: str, detail: str = "") -> None:
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class PhysicalGoal:
    goal_id: str
    path: Path
    answer_path: Path
    status: str
    phase_key: dict[str, str] | None


@dataclass(frozen=True)
class SelectionDecision:
    action: str
    selected_goal_id: str | None = None
    selected_goal_path: str | None = None
    mathematical_phase_key_sha256: str | None = None
    detail: str | None = None


def _fail(code: str, detail: str = "") -> None:
    raise GoalRuntimeError(code, detail)


def _validate_three_body_dispatch(
    *,
    repo_root: Path,
    semantic_attestation_resolver: Callable[[str], dict[str, Any] | None] | None = (
        three_body_loop.resolve_linux_semantic_attestation
    ),
    supplier_preflight_resolver: Callable[[str], str | None] | None = None,
    autonomy_lease_resolver: Callable[[str], dict[str, Any] | None] | None = None,
) -> None:
    try:
        three_body_loop.validate_repository_gate(
            repo_root=repo_root,
            require_dispatch_clear=True,
            semantic_attestation_resolver=semantic_attestation_resolver,
            supplier_preflight_resolver=supplier_preflight_resolver,
            autonomy_lease_resolver=autonomy_lease_resolver,
        )
    except three_body_loop.ThreeBodyViolation as exc:
        _fail(exc.code, exc.detail)


def _load_mapping(path: Path) -> dict[str, Any]:
    try:
        data = load_unique_yaml(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, yaml.YAMLError) as exc:
        _fail("AUTOPILOT_INPUT_INVALID", f"{path}: {exc}")
    if not isinstance(data, dict):
        _fail("AUTOPILOT_INPUT_INVALID", f"top level is not a mapping: {path}")
    return data


def _load_unique_json(path: Path, *, code: str) -> dict[str, Any]:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key!r}")
            result[key] = value
        return result

    try:
        payload = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=unique_object,
        )
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        _fail(code, f"{path}: {exc}")
    if not isinstance(payload, dict):
        _fail(code, f"top level is not a mapping: {path}")
    return payload


def _machine_header(path: Path) -> dict[str, Any]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        _fail("AUTOPILOT_GOAL_HEADER_INVALID", f"{path}: {exc}")
    header = goal_machine_header_text(text)
    if header is None:
        _fail("AUTOPILOT_GOAL_HEADER_INVALID", f"missing or malformed machine header: {path}")
    return header


def _repo_relative_file(
    value: object, *, repo_root: Path, code: str, label: str
) -> tuple[str, Path]:
    if not isinstance(value, str) or not value.strip():
        _fail(code, f"{label} missing")
    relative = PurePosixPath(value)
    if (
        relative.is_absolute()
        or ".." in relative.parts
        or "\\" in value
        or relative.as_posix() != value
    ):
        _fail(code, f"{label} must be a canonical repo-relative POSIX path")
    root = repo_root.resolve()
    resolved = (root / Path(*relative.parts)).resolve()
    if not resolved.is_relative_to(root) or not resolved.is_file():
        _fail(code, f"{label} is not an existing repository file: {value}")
    return value, resolved


def _git_blob(repo_root: Path, commit: str, path: str, *, code: str) -> bytes:
    object_type = subprocess.run(
        ["git", "cat-file", "-t", commit],
        cwd=repo_root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    reachable = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=repo_root,
        check=False,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    if object_type.returncode != 0 or object_type.stdout.strip() != "commit":
        _fail(code, f"{commit} is not a git commit")
    if reachable.returncode != 0:
        _fail(code, f"{commit} is not reachable from HEAD")
    result = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=repo_root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        _fail(code, f"{commit}:{path} is not a committed source blob")
    return result.stdout


def _canonical_phase_key(*, repo_root: Path) -> dict[str, str]:
    channel_runtime = repo_root / Path(*CHANNEL_RUNTIME_REL.parts)
    try:
        payload = _load_unique_json(
            channel_runtime,
            code="AUTOPILOT_CANONICAL_PHASE_UNAVAILABLE",
        )
        active_phase = payload["active_proshka_phase"]
        if not isinstance(active_phase, dict) or active_phase.get("status") != "ACTIVE":
            raise KeyError("active_proshka_phase is not ACTIVE")
        if not isinstance(active_phase.get("conversation_id"), str) or not active_phase[
            "conversation_id"
        ].strip():
            raise KeyError("active Proshka conversation handle is missing")
        return spine.validate_phase_key(active_phase["phase_key"])
    except (KeyError, TypeError) as exc:
        _fail("AUTOPILOT_CANONICAL_PHASE_UNAVAILABLE", str(exc))


def phase_key_sha256(phase_key: object) -> str:
    """Hash only the closed six-field mathematical phase key."""
    validated = spine.validate_phase_key(phase_key)
    payload = json.dumps(
        validated, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _goal_id(path: Path, header: dict[str, Any]) -> str:
    value = header.get("GOAL")
    if not isinstance(value, str) or re.fullmatch(r"\d{3}[A-Za-z]*", value) is None:
        _fail("AUTOPILOT_GOAL_HEADER_INVALID", f"invalid GOAL in {path}")
    filename_match = GOAL_FILE_RE.fullmatch(path.name)
    if filename_match is None:
        _fail("AUTOPILOT_GOAL_IDENTITY_MISMATCH", f"invalid goal filename {path.name!r}")
    file_goal_id = filename_match.group("goal_id")
    legacy_family_header = (
        len(value) == 3
        and file_goal_id.startswith(value)
        and file_goal_id[len(value) :].islower()
    )
    if file_goal_id != value and not legacy_family_header:
        _fail(
            "AUTOPILOT_GOAL_IDENTITY_MISMATCH",
            f"machine GOAL {value!r} disagrees with filename {path.name!r}",
        )
    return file_goal_id


def _answer_result_present(header: dict[str, Any]) -> bool:
    direct_keys = (
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
        for key in direct_keys
    )


def validate_matching_answer(goal: Path, answer: Path, goal_id: str) -> dict[str, Any]:
    """Validate a modern machine-closed answer before it hides an open goal."""
    answer_match = ANSWER_FILE_RE.fullmatch(answer.name)
    if answer_match is None or answer_match.group("goal_id") != goal_id:
        _fail("AUTOPILOT_ANSWER_INVALID", f"answer identity mismatch: {answer}")
    header = _machine_header(answer)
    answer_goal = header.get("GOAL")
    legacy_family_header = (
        isinstance(answer_goal, str)
        and len(answer_goal) == 3
        and goal_id.startswith(answer_goal)
        and goal_id[len(answer_goal) :].islower()
    )
    if answer_goal != goal_id and not legacy_family_header:
        _fail("AUTOPILOT_ANSWER_INVALID", f"machine GOAL mismatch: {answer}")
    if header.get("STATUS") not in {"CLOSED", "CLOSED_PHASE0"}:
        _fail("AUTOPILOT_ANSWER_INVALID", f"non-closing STATUS: {answer}")
    if not _answer_result_present(header):
        _fail("AUTOPILOT_ANSWER_INVALID", f"closing result missing: {answer}")
    return header


def _matches_head(repo_root: Path, path: Path) -> bool:
    try:
        relative = path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return False
    result = subprocess.run(
        ["git", "show", f"HEAD:{relative}"],
        cwd=repo_root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.returncode == 0 and result.stdout == path.read_bytes()


def _legacy_answer_pair_is_closed(goal: Path, answer: Path, *, repo_root: Path) -> bool:
    """Grandfather immutable pre-056 history; current/future answers are strict."""
    match = GOAL_FILE_RE.fullmatch(goal.name)
    if match is None or not match.group("goal_id").isdigit():
        return False
    if int(match.group("goal_id")) >= 56:
        return False
    return _matches_head(repo_root, goal) and _matches_head(repo_root, answer)


def scan_physical_goals(
    bus: Path, *, repo_root: Path = REPO_ROOT
) -> tuple[list[PhysicalGoal], list[PhysicalGoal]]:
    """Return executable and restorably paused unanswered physical goals."""
    if not bus.is_dir():
        _fail("AUTOPILOT_BUS_MISSING", str(bus))
    executable: list[PhysicalGoal] = []
    paused: list[PhysicalGoal] = []
    for path in sorted(bus.glob("*.goal.md")):
        answer = path.with_name(path.name.removesuffix(".goal.md") + ".answer.md")
        if answer.is_file() and _legacy_answer_pair_is_closed(
            path, answer, repo_root=repo_root
        ):
            continue
        header = _machine_header(path)
        goal_id = _goal_id(path, header)
        status = header.get("STATUS")
        if not isinstance(status, str) or STATUS_RE.fullmatch(status) is None:
            _fail("AUTOPILOT_GOAL_HEADER_INVALID", f"STATUS missing: {path}")
        if answer.is_file():
            if status in PAUSED_STATUSES:
                _fail(
                    "AUTOPILOT_ANSWER_INVALID",
                    f"paused goal must remain unanswered: {path}",
                )
            if status != "OPEN" and not (
                _matches_head(repo_root, path) and _matches_head(repo_root, answer)
            ):
                _fail(
                    "AUTOPILOT_UNKNOWN_GOAL_STATUS",
                    f"uncommitted closing pair has unknown goal status {status}: {path}",
                )
            validate_matching_answer(path, answer, goal_id)
            continue
        if status != "OPEN" and status not in PAUSED_STATUSES:
            _fail("AUTOPILOT_UNKNOWN_GOAL_STATUS", f"{status}: {path}")
        raw_phase = header.get("phase_key")
        phase_key = spine.validate_phase_key(raw_phase) if raw_phase is not None else None
        goal = PhysicalGoal(
            goal_id=goal_id,
            path=path,
            answer_path=answer,
            status=status,
            phase_key=phase_key,
        )
        if status == "OPEN":
            executable.append(goal)
        elif status in PAUSED_STATUSES:
            paused.append(goal)
        else:
            _fail("AUTOPILOT_UNKNOWN_GOAL_STATUS", f"{status}: {path}")
    return executable, paused


def validate_next_goal_spec(
    spec: object,
    *,
    repo_root: Path = REPO_ROOT,
    proshka_receipt_validator: Callable[[dict[str, Any]], bool] | None = None,
) -> dict[str, Any]:
    if not isinstance(spec, dict) or set(spec) != set(NEXT_SPEC_FIELDS):
        _fail(
            "AUTOPILOT_NEXT_GOAL_SPEC_INVALID",
            "fields must equal the closed q3_next_goal_spec.v1 schema",
        )
    if spec.get("schema") != "q3_next_goal_spec.v1":
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_INVALID", "unsupported schema")
    for field in (
        "target_id",
        "exact_statement_or_task",
        "terminal_consumer",
        "success_condition",
        "failure_code",
    ):
        if not isinstance(spec.get(field), str) or not spec[field].strip():
            _fail("AUTOPILOT_NEXT_GOAL_SPEC_INVALID", f"empty {field}")
    for field in ("source_objects", "required_inputs", "forbidden_shortcuts", "validation"):
        values = spec.get(field)
        if (
            not isinstance(values, list)
            or not values
            or any(not isinstance(value, str) or not value.strip() for value in values)
        ):
            _fail("AUTOPILOT_NEXT_GOAL_SPEC_INVALID", f"invalid {field}")
    if not isinstance(spec.get("phase_key_change"), bool) or not isinstance(
        spec.get("px_rh_claim"), bool
    ):
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_INVALID", "boolean control fields required")
    spec = dict(spec)
    spec["phase_key"] = spine.validate_phase_key(spec.get("phase_key"))

    provenance = spec.get("source_provenance")
    if not isinstance(provenance, dict) or set(provenance) != set(PROVENANCE_FIELDS):
        _fail(
            "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            "closed provenance fields are missing",
        )
    origin = provenance.get("origin")
    source_path = provenance.get("source_path")
    source_sha = provenance.get("source_sha256")
    operative_class = provenance.get("operative_class")
    source_commit = provenance.get("source_commit")
    receipt_path = provenance.get("receipt_path")
    receipt_sha = provenance.get("receipt_sha256")
    if not isinstance(source_sha, str) or SHA256_RE.fullmatch(source_sha) is None:
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", "source_sha256 invalid")
    if not isinstance(receipt_sha, str) or SHA256_RE.fullmatch(receipt_sha) is None:
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", "receipt_sha256 invalid")
    if not isinstance(source_commit, str) or COMMIT_RE.fullmatch(source_commit) is None:
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", "source_commit invalid")
    source_path, source_file = _repo_relative_file(
        source_path,
        repo_root=repo_root,
        code="AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
        label="source_path",
    )
    receipt_path, receipt_file = _repo_relative_file(
        receipt_path,
        repo_root=repo_root,
        code="AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
        label="receipt_path",
    )
    source_bytes = source_file.read_bytes()
    receipt_bytes = receipt_file.read_bytes()
    if hashlib.sha256(source_bytes).hexdigest() != source_sha:
        _fail(
            "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            f"source_sha256 drift for {source_path}",
        )
    if hashlib.sha256(receipt_bytes).hexdigest() != receipt_sha:
        _fail(
            "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            f"receipt_sha256 drift for {receipt_path}",
        )
    source_blob = _git_blob(
        repo_root,
        source_commit,
        source_path,
        code="AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
    )
    if source_blob != source_bytes:
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", "source blob differs from commit")
    receipt_blob = _git_blob(
        repo_root,
        source_commit,
        receipt_path,
        code="AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
    )
    if receipt_blob != receipt_bytes:
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", "receipt blob differs from commit")
    try:
        source_text = source_bytes.decode("utf-8")
        receipt = load_unique_yaml(receipt_bytes.decode("utf-8"))
    except UnicodeDecodeError:
        _fail(
            "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            "source-locked next-goal provenance must be UTF-8 text",
        )
    except yaml.YAMLError as exc:
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", f"invalid receipt YAML: {exc}")
    expected_source_spec = {field: spec[field] for field in SOURCE_BOUND_SPEC_FIELDS}
    source_specs: list[object] = []
    for match in FENCE_RE.finditer(source_text):
        try:
            document = load_unique_yaml(match.group(1))
        except yaml.YAMLError as exc:
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                f"invalid embedded YAML: {exc}",
            )
        if isinstance(document, dict) and "NEXT_GOAL_SPEC_SOURCE" in document:
            source_specs.append(document["NEXT_GOAL_SPEC_SOURCE"])
    if expected_source_spec not in source_specs:
        _fail(
            "AUTOPILOT_NEXT_GOAL_SPEC_SOURCE_BINDING_INVALID",
            "pinned source has no single structured NEXT_GOAL_SPEC_SOURCE matching the request",
        )
    if not isinstance(receipt, dict) or set(receipt) != set(SOURCE_RECEIPT_FIELDS):
        _fail(
            "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            "source receipt does not match the closed schema",
        )
    spec_sha = hashlib.sha256(
        json.dumps(
            expected_source_spec,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode()
    ).hexdigest()
    receipt_expected = {
        "schema": "q3_next_goal_source_receipt.v1",
        "origin": origin,
        "source_path": source_path,
        "source_sha256": source_sha,
        "next_goal_spec_sha256": spec_sha,
        "operative_class": operative_class,
    }
    if any(receipt.get(field) != value for field, value in receipt_expected.items()):
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", "receipt/source/spec binding drift")
    if origin == "PRECOMMITTED_SOURCE":
        guard_path = receipt.get("outcome_guard_path")
        if (
            operative_class is not None
            or receipt.get("conversation_id") is not None
            or receipt.get("response_id") is not None
            or not isinstance(guard_path, str)
            or not guard_path.startswith("docs/routeB_bus/")
            or not guard_path.endswith(".goal.md")
        ):
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "precommit receipt controls are invalid",
            )
        guard_path, guard_file = _repo_relative_file(
            guard_path,
            repo_root=repo_root,
            code="AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            label="outcome_guard_path",
        )
        guard_blob = _git_blob(
            repo_root,
            source_commit,
            guard_path,
            code="AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
        )
        if guard_blob != guard_file.read_bytes():
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "outcome guard differs from the precommit anchor",
            )
        if len({source_path, receipt_path, guard_path}) != 3:
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "source, receipt, and outcome guard must be distinct files",
            )
        guard_header = _machine_header(guard_file)
        _goal_id(guard_file, guard_header)
        if guard_header.get("STATUS") != "OPEN":
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "precommit outcome guard is not an OPEN physical goal",
            )
        guard_answer = guard_path.removesuffix(".goal.md") + ".answer.md"
        probe = subprocess.run(
            ["git", "cat-file", "-e", f"{source_commit}:{guard_answer}"],
            cwd=repo_root,
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if probe.returncode == 0:
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "precommit anchor already contained the matching outcome",
            )
        guard_answer_file = repo_root / Path(*PurePosixPath(guard_answer).parts)
        if not guard_answer_file.is_file() or not _matches_head(repo_root, guard_answer_file):
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "precommitted guard has no current committed outcome",
            )
        validate_matching_answer(
            guard_file,
            guard_answer_file,
            _goal_id(guard_file, guard_header),
        )
    elif origin == "OPERATIVE_PROSHKA_RESULT":
        if (
            not source_path.startswith("docs/routeB_bus/proshka/")
            or not receipt_path.startswith("docs/routeB_bus/proshka/")
            or not isinstance(operative_class, str)
            or OPERATIVE_RE.fullmatch(operative_class) is None
            or receipt.get("outcome_guard_path") is not None
        ):
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "operative Proshka provenance controls are invalid",
            )
        operative_token = rf"(?<![A-Z0-9_]){re.escape(operative_class)}(?![A-Z0-9_])"
        if re.search(operative_token, source_text) is None:
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "operative_class is not present in the pinned source bytes",
            )
        channel_path = repo_root / Path(*CHANNEL_RUNTIME_REL.parts)
        try:
            channel_payload = _load_unique_json(
                channel_path,
                code="AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            )
            channel = channel_payload["active_proshka_phase"]
            if not isinstance(channel, dict):
                raise TypeError("active_proshka_phase is not a mapping")
        except (KeyError, TypeError) as exc:
            _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", f"channel unavailable: {exc}")
        receipt_authenticated = False
        if proshka_receipt_validator is not None:
            try:
                receipt_authenticated = proshka_receipt_validator(receipt)
            except Exception:
                receipt_authenticated = False
        if (
            channel.get("status") != "ACTIVE"
            or not isinstance(channel.get("conversation_id"), str)
            or not channel["conversation_id"].strip()
            or not isinstance(channel.get("last_adjudicated_pin"), str)
            or not channel["last_adjudicated_pin"].strip()
            or receipt_authenticated is not True
            or receipt.get("conversation_id") != channel.get("conversation_id")
            or receipt.get("response_id") != channel.get("last_adjudicated_pin")
        ):
            _fail(
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                "Proshka receipt is not authenticated against the canonical channel",
            )
    else:
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID", "unknown origin")
    return spec


def select_action(
    bus: Path,
    *,
    next_goal_spec: dict[str, Any] | None = None,
    current_phase_key: dict[str, str] | None = None,
    repo_root: Path = REPO_ROOT,
    proshka_receipt_validator: Callable[[dict[str, Any]], bool] | None = None,
    semantic_attestation_resolver: Callable[[str], dict[str, Any] | None] | None = (
        three_body_loop.resolve_linux_semantic_attestation
    ),
    supplier_preflight_resolver: Callable[[str], str | None] | None = None,
    autonomy_lease_resolver: Callable[[str], dict[str, Any] | None] | None = None,
) -> SelectionDecision:
    expected_bus = repo_root.resolve() / "docs" / "routeB_bus"
    if bus.resolve() != expected_bus:
        _fail(
            "AUTOPILOT_BUS_MISSING",
            "selector accepts only the canonical repo-local docs/routeB_bus",
        )
    executable, _paused = scan_physical_goals(bus, repo_root=repo_root)
    if len(executable) > 1:
        labels = ",".join(goal.goal_id for goal in executable)
        _fail("AUTOPILOT_AMBIGUOUS_GOAL_SET", labels)
    if len(executable) == 1:
        goal = executable[0]
        canonical_phase = _canonical_phase_key(repo_root=repo_root)
        if (
            current_phase_key is not None
            and spine.validate_phase_key(current_phase_key) != canonical_phase
        ):
            _fail(
                "AUTOPILOT_CURRENT_PHASE_KEY_DRIFT",
                "caller-supplied phase key disagrees with canonical CHANNEL_RUNTIME.json",
            )
        if goal.phase_key is not None and goal.phase_key != canonical_phase:
            _fail(
                "AUTOPILOT_CURRENT_PHASE_KEY_DRIFT",
                "physical goal phase disagrees with canonical CHANNEL_RUNTIME.json",
            )
        _validate_three_body_dispatch(
            repo_root=repo_root,
            semantic_attestation_resolver=semantic_attestation_resolver,
            supplier_preflight_resolver=supplier_preflight_resolver,
            autonomy_lease_resolver=autonomy_lease_resolver,
        )
        return SelectionDecision(
            action="SELECT_EXACT_GOAL",
            selected_goal_id=goal.goal_id,
            selected_goal_path=str(goal.path.resolve()),
            mathematical_phase_key_sha256=phase_key_sha256(canonical_phase),
            detail="selection only; AUTOPILOT_000 performs no dispatch",
        )
    if next_goal_spec is None:
        _fail("AUTOPILOT_NEXT_GOAL_SPEC_MISSING")
    spec = validate_next_goal_spec(
        next_goal_spec,
        repo_root=repo_root,
        proshka_receipt_validator=proshka_receipt_validator,
    )
    if spec["px_rh_claim"]:
        return SelectionDecision(action="OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM")
    requested_phase = spec["phase_key"]
    current_phase = _canonical_phase_key(repo_root=repo_root)
    if (
        current_phase_key is not None
        and spine.validate_phase_key(current_phase_key) != current_phase
    ):
        _fail(
            "AUTOPILOT_CURRENT_PHASE_KEY_DRIFT",
            "caller-supplied phase key disagrees with canonical CHANNEL_RUNTIME.json",
        )
    keys_equal = current_phase == requested_phase
    if spec["phase_key_change"] != (not keys_equal):
        _fail(
            "AUTOPILOT_PHASE_CHANGE_DECLARATION_DRIFT",
            "phase_key_change disagrees with the closed six-field comparator",
        )
    if not keys_equal:
        return SelectionDecision(
            action="PHASE_TRANSITION_REQUIRED",
            mathematical_phase_key_sha256=phase_key_sha256(requested_phase),
        )
    _validate_three_body_dispatch(
        repo_root=repo_root,
        semantic_attestation_resolver=semantic_attestation_resolver,
        supplier_preflight_resolver=supplier_preflight_resolver,
        autonomy_lease_resolver=autonomy_lease_resolver,
    )
    return SelectionDecision(
        action="MINT_READY",
        mathematical_phase_key_sha256=phase_key_sha256(requested_phase),
        detail="validated source only; AUTOPILOT_000 does not mint",
    )


def _canonical_runtime_path(
    value: object, *, field: str, repo_root: Path, suffix: str
) -> tuple[str, Path]:
    if not isinstance(value, str) or not value.strip():
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", f"invalid {field}")
    relative = PurePosixPath(value)
    if (
        relative.is_absolute()
        or ".." in relative.parts
        or "\\" in value
        or relative.as_posix() != value
        or not value.startswith("docs/routeB_bus/")
        or not value.endswith(suffix)
    ):
        _fail(
            "AUTOPILOT_RUNTIME_SCHEMA_INVALID",
            f"{field} must be a canonical Route B repo-relative path",
        )
    root = repo_root.resolve()
    resolved = (root / Path(*relative.parts)).resolve()
    if not resolved.is_relative_to(root):
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", f"{field} escapes repository")
    return value, resolved


def validate_operational_grant(
    grant_id: object,
    *,
    goal_file: str,
    required_action: str,
    resolver: Callable[[str], dict[str, Any] | None] | None,
) -> dict[str, Any]:
    if not isinstance(grant_id, str) or GRANT_RE.fullmatch(grant_id) is None:
        _fail("AUTOPILOT_OPERATIONAL_GRANT_INVALID", "grant ID is not canonical")
    if resolver is None:
        _fail("AUTOPILOT_OPERATIONAL_GRANT_INVALID", "no grant authority resolver")
    try:
        grant = resolver(grant_id)
    except Exception:
        _fail("AUTOPILOT_OPERATIONAL_GRANT_INVALID", "grant authority resolver failed")
    if not isinstance(grant, dict) or set(grant) != set(GRANT_RESOLUTION_FIELDS):
        _fail("AUTOPILOT_OPERATIONAL_GRANT_INVALID", "grant authority returned no closed record")
    if (
        grant.get("schema") != "q3_operational_grant_resolution.v1"
        or grant.get("grant_id") != grant_id
        or grant.get("status") != "ACTIVE"
        or grant.get("scope_goal_file") != goal_file
    ):
        _fail("AUTOPILOT_OPERATIONAL_GRANT_INVALID", "grant identity or scope mismatch")
    allowed = grant.get("allowed_actions")
    forbidden = grant.get("forbidden_actions")
    if (
        not isinstance(allowed, list)
        or allowed != [required_action]
        or not isinstance(forbidden, list)
        or any(not isinstance(item, str) for item in forbidden)
        or len(forbidden) != len(set(forbidden))
        or not REQUIRED_GRANT_FORBIDDENS.issubset(forbidden)
        or required_action in forbidden
    ):
        _fail("AUTOPILOT_OPERATIONAL_GRANT_INVALID", "grant action boundary invalid")
    return grant


def _validate_rfc3339(value: object, *, field: str) -> str:
    if not isinstance(value, str) or RFC3339_RE.fullmatch(value) is None:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", f"invalid {field}")
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", f"invalid {field}")
    if parsed.tzinfo is None:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", f"timezone missing from {field}")
    return value


def _verify_source_pin(
    *, repo_root: Path, source_commit: str, goal_file: str, goal_sha256: str
) -> None:
    source_blob = _git_blob(
        repo_root,
        source_commit,
        goal_file,
        code="AUTOPILOT_RUNTIME_SOURCE_PIN_INVALID",
    )
    if hashlib.sha256(source_blob).hexdigest() != goal_sha256:
        _fail(
            "AUTOPILOT_RUNTIME_SOURCE_PIN_INVALID",
            "source_commit does not contain the pinned goal bytes",
        )


def _canonical_phase_hash(*, repo_root: Path, goal_header: dict[str, Any]) -> str:
    canonical_phase = _canonical_phase_key(repo_root=repo_root)
    goal_phase = goal_header.get("phase_key")
    if goal_phase is not None:
        validated_goal_phase = spine.validate_phase_key(goal_phase)
        if validated_goal_phase != canonical_phase:
            _fail(
                "AUTOPILOT_RUNTIME_PHASE_PIN_INVALID",
                "goal-embedded phase disagrees with canonical CHANNEL_RUNTIME.json",
            )
    return phase_key_sha256(canonical_phase)


def validate_runtime_state(
    runtime: object,
    *,
    repo_root: Path = REPO_ROOT,
    grant_resolver: Callable[[str], dict[str, Any] | None] | None = None,
    semantic_attestation_resolver: Callable[[str], dict[str, Any] | None] | None = (
        three_body_loop.resolve_linux_semantic_attestation
    ),
    supplier_preflight_resolver: Callable[[str], str | None] | None = None,
    autonomy_lease_resolver: Callable[[str], dict[str, Any] | None] | None = None,
) -> dict[str, Any]:
    """Validate the closed q3_goal_run.v1 crash-recovery record schema."""
    if not isinstance(runtime, dict) or set(runtime) != set(RUNTIME_FIELDS):
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "closed runtime fields differ")
    if runtime.get("schema") != "q3_goal_run.v1":
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "unsupported schema")
    for field in ("goal_run_id", "next_target", "operational_grant_id"):
        if not isinstance(runtime.get(field), str) or not runtime[field].strip():
            _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", f"invalid {field}")
    run_match = GOAL_RUN_RE.fullmatch(runtime["goal_run_id"])
    if run_match is None:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "goal_run_id is not canonical")
    _validate_rfc3339(
        f"{run_match.group('stamp')[:4]}-{run_match.group('stamp')[4:6]}-"
        f"{run_match.group('stamp')[6:8]}T{run_match.group('stamp')[9:11]}:"
        f"{run_match.group('stamp')[11:13]}:{run_match.group('stamp')[13:15]}Z",
        field="goal_run_id timestamp",
    )
    goal_file, goal_path = _canonical_runtime_path(
        runtime.get("goal_file"), field="goal_file", repo_root=repo_root, suffix=".goal.md"
    )
    answer_file, answer_path = _canonical_runtime_path(
        runtime.get("answer_file"),
        field="answer_file",
        repo_root=repo_root,
        suffix=".answer.md",
    )
    goal_name = Path(goal_file).name
    goal_match = GOAL_FILE_RE.fullmatch(goal_name)
    if goal_match is None or goal_match.group("goal_id") != run_match.group("goal_id"):
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "goal identity disagrees with goal_run_id")
    expected_answer = goal_file.removesuffix(".goal.md") + ".answer.md"
    if answer_file != expected_answer:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "answer_file does not match goal_file")
    validate_operational_grant(
        runtime["operational_grant_id"],
        goal_file=goal_file,
        required_action=runtime["next_action"],
        resolver=grant_resolver,
    )
    if not isinstance(runtime.get("goal_sha256"), str) or SHA256_RE.fullmatch(
        runtime["goal_sha256"]
    ) is None:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "goal_sha256 invalid")
    if not isinstance(runtime.get("source_commit"), str) or COMMIT_RE.fullmatch(
        runtime["source_commit"]
    ) is None:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "source_commit invalid")
    phase_sha = runtime.get("mathematical_phase_key_sha256")
    if phase_sha is not None and (
        not isinstance(phase_sha, str) or SHA256_RE.fullmatch(phase_sha) is None
    ):
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "phase-key SHA invalid")
    state = runtime.get("state")
    action = runtime.get("next_action")
    if state not in RUNTIME_STATES or action not in NEXT_ACTIONS:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "unknown state or next_action")
    if action not in STATE_ACTIONS[state]:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", f"{state} cannot request {action}")
    for field in ("cycle_index", "stall_counter"):
        if (
            not isinstance(runtime.get(field), int)
            or isinstance(runtime[field], bool)
            or not 0 <= runtime[field] <= 12
        ):
            _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", f"invalid {field}")
    if runtime["stall_counter"] > runtime["cycle_index"]:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "stall_counter exceeds cycle_index")
    if runtime["cycle_index"] == 12 and action != "STOP":
        _fail("AUTOPILOT_RUNTIME_BUDGET_INVALID", "twelve cycles require STOP")
    if runtime["stall_counter"] >= 6 and action not in {"REQUEST_STRATEGIC_REVIEW", "STOP"}:
        _fail(
            "AUTOPILOT_RUNTIME_BUDGET_INVALID",
            "six no-delta cycles require strategic review or STOP",
        )
    if (
        runtime["stall_counter"] >= 3
        and state == "RUNNING"
        and action == "CONTINUE_STEP"
    ):
        _fail(
            "AUTOPILOT_RUNTIME_BUDGET_INVALID",
            "three no-delta cycles cannot remain in the normal running loop",
        )
    last_attempt = runtime.get("last_attempt_id")
    expected_attempt = (
        None
        if runtime["cycle_index"] == 0
        else f"ATTEMPT_GOAL{run_match.group('goal_id')}_{runtime['cycle_index']:03d}"
    )
    if last_attempt != expected_attempt:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "last_attempt_id disagrees with cycle_index")
    if phase_sha is None:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "run lacks phase-key SHA")
    lease = runtime.get("lease")
    if not isinstance(lease, dict) or set(lease) != {"holder", "heartbeat_at"}:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "lease invalid")
    if lease["holder"] not in LEASE_HOLDERS:
        _fail("AUTOPILOT_RUNTIME_SCHEMA_INVALID", "unknown lease holder")
    _validate_rfc3339(lease["heartbeat_at"], field="lease heartbeat_at")
    if not goal_path.is_file():
        _fail("AUTOPILOT_RUNTIME_GOAL_PIN_INVALID", "pinned goal file is missing")
    actual_goal_sha = hashlib.sha256(goal_path.read_bytes()).hexdigest()
    if actual_goal_sha != runtime["goal_sha256"]:
        _fail("AUTOPILOT_RUNTIME_GOAL_PIN_INVALID", "goal_sha256 drift")
    header = _machine_header(goal_path)
    if _goal_id(goal_path, header) != run_match.group("goal_id"):
        _fail("AUTOPILOT_RUNTIME_GOAL_PIN_INVALID", "machine goal identity drift")
    if header.get("STATUS") != "OPEN":
        _fail(
            "AUTOPILOT_RUNTIME_GOAL_PIN_INVALID",
            "runtime cannot execute a non-OPEN physical goal",
        )
    _verify_source_pin(
        repo_root=repo_root,
        source_commit=runtime["source_commit"],
        goal_file=goal_file,
        goal_sha256=runtime["goal_sha256"],
    )
    canonical_phase_sha = _canonical_phase_hash(repo_root=repo_root, goal_header=header)
    if phase_sha != canonical_phase_sha:
        _fail(
            "AUTOPILOT_RUNTIME_PHASE_PIN_INVALID",
            "mathematical_phase_key_sha256 disagrees with the canonical six-field key",
        )
    answer_exists = answer_path.is_file()
    answer_required_states = {"CLOSED", "STOPPED_CLEAN"}
    answer_allowed_states = answer_required_states | {"CLOSING", "CLOSE_RETRY_PENDING"}
    if state in answer_required_states:
        if not answer_exists:
            _fail("AUTOPILOT_RUNTIME_ANSWER_STATE_INVALID", f"{state} requires matching answer")
        validate_matching_answer(goal_path, answer_path, run_match.group("goal_id"))
    elif state in answer_allowed_states and answer_exists:
        validate_matching_answer(goal_path, answer_path, run_match.group("goal_id"))
    elif answer_exists:
        _fail("AUTOPILOT_RUNTIME_ANSWER_STATE_INVALID", f"{state} cannot have matching answer")
    if action != "STOP":
        _validate_three_body_dispatch(
            repo_root=repo_root,
            semantic_attestation_resolver=semantic_attestation_resolver,
            supplier_preflight_resolver=supplier_preflight_resolver,
            autonomy_lease_resolver=autonomy_lease_resolver,
        )
    return runtime


def _write_goal(bus: Path, goal_id: str, phase_key: dict[str, str]) -> None:
    payload = {
        "GOAL": goal_id,
        "NODE": f"Plant{goal_id}",
        "STATUS": "OPEN",
        "phase_key": phase_key,
    }
    (bus / f"{goal_id}_plant.goal.md").write_text(
        "# plant\n\n```yaml\n" + yaml.safe_dump(payload, sort_keys=False) + "```\n",
        encoding="utf-8",
    )


def _valid_spec(phase_key: dict[str, str]) -> dict[str, Any]:
    return {
        "schema": "q3_next_goal_spec.v1",
        "target_id": "AUTOPILOT_000_PLANT_TARGET",
        "exact_statement_or_task": "Synthetic selector plant only",
        "terminal_consumer": "AUTOPILOT_000_SELFTEST",
        "source_objects": ["SYNTHETIC_SOURCE_OBJECT"],
        "required_inputs": ["SYNTHETIC_INPUT"],
        "forbidden_shortcuts": ["NO_PRODUCTION_MINT"],
        "validation": ["AUTOPILOT_000_SELFTEST"],
        "success_condition": "SYNTHETIC_MINT_READY",
        "failure_code": "SYNTHETIC_PLANT_FAILURE",
        "source_provenance": {
            "origin": "PRECOMMITTED_SOURCE",
            "source_path": "",
            "source_sha256": "0" * 64,
            "operative_class": None,
            "source_commit": "0" * 40,
            "receipt_path": "",
            "receipt_sha256": "0" * 64,
        },
        "phase_key": phase_key,
        "phase_key_change": False,
        "px_rh_claim": False,
    }


def _bind_plant_spec(root: Path, spec: dict[str, Any]) -> None:
    source_rel = "source.md"
    receipt_rel = "source.receipt.yaml"
    guard_rel = "docs/routeB_bus/999_plant_guard.goal.md"
    source = root / source_rel
    guard = root / guard_rel
    guard.parent.mkdir(parents=True)
    guard.write_text(
        "# plant guard\n\n```yaml\nGOAL: '999'\nSTATUS: OPEN\n```\n",
        encoding="utf-8",
    )
    bound = {field: spec[field] for field in SOURCE_BOUND_SPEC_FIELDS}
    source.write_text(
        "```yaml\n"
        + yaml.safe_dump({"NEXT_GOAL_SPEC_SOURCE": bound}, sort_keys=False)
        + "```\n",
        encoding="utf-8",
    )
    source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
    spec_sha = hashlib.sha256(
        json.dumps(bound, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    receipt = {
        "schema": "q3_next_goal_source_receipt.v1",
        "origin": "PRECOMMITTED_SOURCE",
        "source_path": source_rel,
        "source_sha256": source_sha,
        "next_goal_spec_sha256": spec_sha,
        "conversation_id": None,
        "response_id": None,
        "operative_class": None,
        "outcome_guard_path": guard_rel,
    }
    receipt_path = root / receipt_rel
    receipt_path.write_text(yaml.safe_dump(receipt, sort_keys=False), encoding="utf-8")
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    subprocess.run(["git", "add", source_rel, receipt_rel, guard_rel], cwd=root, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=AUTOPILOT Plant",
            "-c",
            "user.email=autopilot-plant.invalid",
            "commit",
            "-qm",
            "plant",
        ],
        cwd=root,
        check=True,
    )
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    answer_rel = guard_rel.removesuffix(".goal.md") + ".answer.md"
    (root / answer_rel).write_text(
        "# synthetic plant outcome\n\n```yaml\n"
        "GOAL: '999'\nSTATUS: CLOSED\nEXACT_RESULT: SYNTHETIC_OUTCOME_OBSERVED\n```\n",
        encoding="utf-8",
    )
    subprocess.run(["git", "add", answer_rel], cwd=root, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=AUTOPILOT Plant",
            "-c",
            "user.email=autopilot-plant.invalid",
            "commit",
            "-qm",
            "plant outcome",
        ],
        cwd=root,
        check=True,
    )
    spec["source_provenance"] = {
        "origin": "PRECOMMITTED_SOURCE",
        "source_path": source_rel,
        "source_sha256": source_sha,
        "operative_class": None,
        "source_commit": commit,
        "receipt_path": receipt_rel,
        "receipt_sha256": hashlib.sha256(receipt_path.read_bytes()).hexdigest(),
    }


def run_selftest() -> int:
    phase = {
        "route_id": "ROUTE",
        "front_id": "FRONT",
        "source_object_family_id": "SOURCE",
        "terminal_consumer_id": "CONSUMER",
        "honesty_state": "CHALLENGER_NOT_RH",
        "convention_lock_id": "LOCK",
    }
    checks: list[tuple[str, bool]] = []

    # P1: goal number is excluded from mathematical phase identity.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        bus = root / "docs" / "routeB_bus"
        bus.mkdir(parents=True)
        _write_goal(bus, "101", phase)
        _write_goal(bus, "102", phase)
        goals, _ = scan_physical_goals(bus, repo_root=root)
        phase_hashes = {phase_key_sha256(goal.phase_key) for goal in goals}
        checks.append(("P1_SAME_PHASE_TWO_GOAL_NUMBERS", len(phase_hashes) == 1))
        try:
            select_action(bus, repo_root=root)
        except GoalRuntimeError as exc:
            checks.append(
                (
                    "P2_TWO_EXECUTABLE_FAIL_CLOSED",
                    exc.code == "AUTOPILOT_AMBIGUOUS_GOAL_SET",
                )
            )
        else:
            checks.append(("P2_TWO_EXECUTABLE_FAIL_CLOSED", False))

    # P3: a post-outcome self-selected spec without locked provenance is rejected.
    bad = _valid_spec(phase)
    bad["source_provenance"] = {}
    try:
        validate_next_goal_spec(bad)
    except GoalRuntimeError as exc:
        checks.append(
            (
                "P3_POST_OUTCOME_SPEC_REJECTED",
                exc.code == "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            )
        )
    else:
        checks.append(("P3_POST_OUTCOME_SPEC_REJECTED", False))

    # P4: an explicit PX/RH claim never reaches MINT_READY.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        spec = _valid_spec(phase)
        spec["px_rh_claim"] = True
        _bind_plant_spec(root, spec)
        decision = select_action(
            root / "docs" / "routeB_bus",
            next_goal_spec=spec,
            current_phase_key=phase,
            repo_root=root,
        )
        checks.append(
            (
                "P4_PX_RH_OWNER_STOP",
                decision.action == "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM",
            )
        )

    for name, passed in checks:
        print(f"{name}: {'PASS' if passed else 'FAIL'}")
    if not all(passed for _, passed in checks):
        print("AUTOPILOT_CONTROL_OR_SELECTOR_GAP")
        return 1
    print("GOAL_RUN_CONTRACT_VALIDATED_WITH_FOUR_PLANTS")
    return 0


def _args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bus", type=Path, default=DEFAULT_BUS)
    parser.add_argument("--next-goal-spec", type=Path)
    parser.add_argument("--current-phase-key", type=Path)
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("--json", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = _args()
    if args.selftest:
        return run_selftest()
    try:
        if args.bus.resolve() != DEFAULT_BUS.resolve():
            _fail(
                "AUTOPILOT_BUS_MISSING",
                "production CLI accepts only canonical docs/routeB_bus; "
                "use --selftest for plants",
            )
        spec = _load_mapping(args.next_goal_spec) if args.next_goal_spec else None
        current = _load_mapping(args.current_phase_key) if args.current_phase_key else None
        result: Any = asdict(
            select_action(args.bus.resolve(), next_goal_spec=spec, current_phase_key=current)
        )
    except (GoalRuntimeError, spine.ControlViolation) as exc:
        code = getattr(exc, "code", "AUTOPILOT_CONTROL_OR_SELECTOR_GAP")
        detail = getattr(exc, "detail", str(exc))
        if args.json:
            print(json.dumps({"ok": False, "code": code, "detail": detail}, ensure_ascii=False))
        else:
            print(f"{code}: {detail}" if detail else code, file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps({"ok": True, "result": result}, ensure_ascii=False, indent=2))
    else:
        print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
