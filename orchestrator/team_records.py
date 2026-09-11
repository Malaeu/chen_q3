"""Pure, strict preparation helpers for the Q3 team registries.

The module deliberately contains no filesystem writer, lock, process launcher,
database, selector or scheduler.  It prepares bytes and receipts for the
caller which owns those effects.

``INSTRUCTION_ISSUES.md`` and ``AGENTS_LEDGER.md`` are treated as immutable
legacy prefixes.  A first structured write appends one
``q3_team_records_boundary.v1`` marker carrying the exact prefix length and
SHA-256, followed by length-framed canonical JSON event bytes.  A frame is::

    Q3_TEAM_RECORD_FRAME_V1 length=<decimal byte count>\\n<canonical JSON bytes>

The JSON object itself always ends in exactly one LF.  Events use the closed
``q3_team_event.v1`` envelope.  Issue reports use ``q3_issue_report.v1``;
issue transitions use ``q3_issue_transition.v1``; assignments use
``q3_assignment.v1``.  The report and initial issue IDs are respectively
``report-`` and ``issue-`` followed by the full SHA-256 of the report payload
bytes.  Assignment IDs are supplied by the owner and are never inferred from
prose.

The envelope's ``previous_event_sha256`` is the predecessor of the previous
frame in this registry.  A transition payload's ``previous_event_sha256`` is
the predecessor of that issue, and an assignment payload's
``previous_assignment_event_sha256`` is the predecessor of that assignment.
Keeping those two chains separate permits interleaved reports and assignments
without weakening either CAS (compare-and-swap, проверка точного предшественника).

The public ``read_registry`` result contains ``sha256``, ``legacy_sha256``,
``events``, ``issues`` and ``assignments``.  Underscore-prefixed values in the
result are implementation metadata used only to reconstruct receipts.  All
normal parsing is bounded by the constants below; corrupted or ambiguous
history raises ``TeamRecordError`` without returning a partial result.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import PurePosixPath
from typing import Any


ISSUE_REPORT_SCHEMA = "q3_issue_report.v1"
ISSUE_TRANSITION_SCHEMA = "q3_issue_transition.v1"
ASSIGNMENT_SCHEMA = "q3_assignment.v1"
EVENT_SCHEMA = "q3_team_event.v1"
BOUNDARY_SCHEMA = "q3_team_records_boundary.v1"
ARCHIVE_SCHEMA = "q3_team_records_archive.v1"
ARCHIVE_REF_SCHEMA = "q3_team_archive_ref.v1"
RECEIPT_SCHEMA = "q3_team_record_receipt.v1"
FRAME_PREFIX = b"Q3_TEAM_RECORD_FRAME_V1 length="
BOUNDARY_MARKER = b"<!-- Q3_TEAM_RECORDS_BOUNDARY\n"

# These are intentionally finite and conservative.  A recovery tool can do a
# separately authorised full verification, while routine plan output remains
# bounded as the registries grow.
MAX_JSON_BYTES = 1024 * 1024
MAX_REGISTRY_BYTES = 8 * 1024 * 1024
MAX_FRAME_BYTES = 512 * 1024
MAX_ARCHIVE_BYTES = 4 * 1024 * 1024
MAX_EVENTS = 4096
MAX_ARCHIVE_DEPTH = 8
MAX_JSON_DEPTH = 40
MAX_COLLECTION_ITEMS = 4096
MAX_TEXT_BYTES = 128 * 1024

SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
COMMIT_RE = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:-]{0,127}$")
DERIVED_ID_RE = re.compile(r"^(?:report|issue|event)-[0-9a-f]{64}$")
TIMESTAMP_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}"
    r"(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})$"
)
MODEL_EFFORTS = frozenset({"none", "minimal", "low", "medium", "high", "xhigh", "max", "ultra"})
SEVERITIES = frozenset({"CRITICAL", "HIGH", "MEDIUM", "LOW", "WORDING"})
ISSUE_DISPOSITIONS = frozenset(
    {
        "CONFIRMED_BUG",
        "CONFIRMED_RULE_CONFLICT",
        "AGENT_CONTEXT_ERROR",
        "EXPECTED_GUARD",
        "UNREPRODUCED",
        "DUPLICATE",
        "DEFERRED",
    }
)
REPAIR_STATES = frozenset(
    {"ASSIGNED", "FIX_CANDIDATE", "FIX_VERIFIED", "FIX_COMMITTED", "FIX_PUSH_VERIFIED"}
)
ALLOWED_TRANSITIONS = frozenset({"REPRODUCING", *ISSUE_DISPOSITIONS, *REPAIR_STATES})
ASSIGNMENT_OPERATIONS = frozenset({"CREATE", "UPDATE", "RETRY"})
ASSIGNMENT_STATUSES = frozenset(
    {
        "ASSIGNED",
        "READY",
        "RUNNING",
        "IN_PROGRESS",
        "OPEN",
        "PENDING",
        "WAITING",
        "BLOCKED",
        "DONE",
        "COMPLETED",
        "FAILED",
        "CANCELLED",
        "UNKNOWN",
        "RETRY_PENDING",
    }
)
NATIVE_OBSERVATION_SCHEMA = "q3_team_assignment_observation.v1"
REPAIR_REVIEW_SCHEMA = "q3_repair_review.v1"
NATIVE_OBSERVATION_REQUIRED_FIELDS = frozenset(
    {
        "schema",
        "assignment_id",
        "phase",
        "operation_id",
        "owner_task",
        "owner_installation_ref",
        "owner_epoch",
        "assignee",
        "native_agent_id",
        "native_owner_task",
        "requested_model",
        "requested_effort",
        "resolved_model",
        "resolved_effort",
        "subject",
        "state",
        "output_locator",
        "output_sha256",
        "provider_receipt_locator",
        "provider_receipt_sha256",
        "payload_sha256",
        "evidence_sha256",
        "source_sha256",
    }
)
NATIVE_OBSERVATION_STATES = frozenset({"RUNNING", "COMPLETED"})
REPAIR_REVIEW_REQUIRED_FIELDS = frozenset(
    {
        "schema",
        "issue_id",
        "repair_subject_type",
        "repair_subject_id",
        "base_commit",
        "candidate_manifest",
        "verdict",
    }
)
OWNER_ACTOR_ROLES = frozenset({"owner", "owner-transition", "orchestrator"})
INDEPENDENT_ACTOR_ROLES = frozenset(
    {
        "independent-check",
        "independent-checker",
        "independent-reproducer",
        "independent-reviewer",
    }
)
IMPLEMENTER_ACTOR_ROLES = frozenset({"implementer", "implementation"})
IMPLEMENTER_ASSIGNMENT_ROLES = frozenset({"implementation", "implementer"})
CONFIRMED_OBSERVATION_STATE = "CONFIRMED"

REPORT_REQUIRED_FIELDS = frozenset(
    {
        "schema",
        "reporter_task",
        "reporter_host",
        "assignment_id",
        "attempt_id",
        "observed_at",
        "subject_id",
        "subject_type",
        "base_commit",
        "input_paths",
        "severity",
        "suspected_class",
        "expected_behavior",
        "expected_rule_source",
        "actual_behavior",
        "reproduction",
        "affected_operations",
        "evidence",
        "uncertainty",
    }
)
REPORT_OPTIONAL_FIELDS = frozenset({"supersedes_report_id"})

TRANSITION_REQUIRED_FIELDS = frozenset(
    {
        "schema",
        "issue_id",
        "report_id",
        "transition",
        "actor_id",
        "actor_role",
        "evidence",
        "source_binding",
        "reason",
        "previous_event_sha256",
        "previous_state_sha256",
    }
)
TRANSITION_OPTIONAL_FIELDS = frozenset(
    {
        "implementer_id",
        "verifier_id",
        "duplicate_of_issue_id",
        "repair_subject_type",
        "repair_subject_id",
        "reviewer_severity",
        "candidate_manifest",
        "candidate_commit",
    }
)

ASSIGNMENT_REQUIRED_FIELDS = frozenset(
    {
        "schema",
        "assignment_id",
        "operation",
        "owner_task",
        "owner_host",
        "owner_installation_ref",
        "owner_epoch",
        "assignee",
        "requested_model",
        "requested_effort",
        "resolved_model",
        "resolved_effort",
        "role",
        "subject",
        "base_commit",
        "input_hashes",
        "permitted_paths",
        "output_locator",
        "prerequisites",
        "stopping_condition",
        "expected_duration_seconds",
        "next_check",
        "status",
        "previous_assignment_event_sha256",
        "previous_assignment_sha256",
    }
)

EVENT_FIELDS = frozenset(
    {
        "schema",
        "event_id",
        "event_type",
        "kind",
        "issue_id",
        "report_id",
        "payload",
        "payload_sha256",
        "previous_event_sha256",
        "previous_state_sha256",
        "previous_registry_sha256",
    }
)
ARCHIVE_PAYLOAD_FIELDS = frozenset(
    {"schema", "archive_ref", "event_count", "first_event_sha256", "last_event_sha256"}
)


class TeamRecordError(ValueError):
    """Fail-closed error with a stable machine-readable code."""

    def __init__(self, code: str, detail: str = "") -> None:
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code
        self.detail = detail


def _fail(code: str, detail: str = "") -> None:
    raise TeamRecordError(code, detail)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


@dataclass(frozen=True)
class TrustedTeamContext:
    """Verified current owner plus closed native observations.

    ``observations`` maps an assignment ID to exactly two closed observation
    dictionaries, one ``phase=LAUNCH`` and one ``phase=RESULT``.  The caller
    constructs this context only after native provider and file hashes have
    been checked; the validators below still recheck every binding.
    ``output_artifacts`` maps those hash-checked output locators to their exact
    bytes so a repair review cannot be replaced by a free observation field.
    """

    owner_task: str
    owner_host: str
    owner_installation_ref: str
    owner_epoch: int
    actor_id: str
    observations: Mapping[str, Sequence[Mapping[str, Any]]]
    output_artifacts: Mapping[str, bytes] = field(default_factory=dict)


def _is_sha(value: object, *, allow_absent: bool = False) -> bool:
    return (allow_absent and value == "ABSENT") or (
        isinstance(value, str) and SHA256_RE.fullmatch(value) is not None
    )


def _check_json_value(value: object, *, depth: int = 0, seen: set[int] | None = None) -> None:
    """Reject values which JSON can spell ambiguously or which exceed bounds."""
    if depth > MAX_JSON_DEPTH:
        _fail("LIMIT_JSON_DEPTH", str(MAX_JSON_DEPTH))
    if seen is None:
        seen = set()
    if isinstance(value, float):
        _fail("UNSUPPORTED_JSON_VALUE", "floats and non-finite numbers are forbidden")
    if value is None or isinstance(value, (str, int, bool)):
        if isinstance(value, str) and len(value.encode("utf-8")) > MAX_TEXT_BYTES:
            _fail("LIMIT_TEXT_BYTES", str(MAX_TEXT_BYTES))
        return
    if isinstance(value, (bytes, bytearray, memoryview)):
        _fail("UNSUPPORTED_JSON_VALUE", "bytes are not JSON payloads")
    if not isinstance(value, (dict, list)):
        _fail("UNSUPPORTED_JSON_VALUE", type(value).__name__)
    object_id = id(value)
    if object_id in seen:
        _fail("UNSUPPORTED_JSON_VALUE", "cyclic container")
    seen.add(object_id)
    try:
        if isinstance(value, dict):
            if len(value) > MAX_COLLECTION_ITEMS:
                _fail("LIMIT_COLLECTION_ITEMS", str(MAX_COLLECTION_ITEMS))
            for key, item in value.items():
                if not isinstance(key, str):
                    _fail("UNSUPPORTED_JSON_VALUE", "object keys must be strings")
                _check_json_value(key, depth=depth + 1, seen=seen)
                _check_json_value(item, depth=depth + 1, seen=seen)
        else:
            if len(value) > MAX_COLLECTION_ITEMS:
                _fail("LIMIT_COLLECTION_ITEMS", str(MAX_COLLECTION_ITEMS))
            for item in value:
                _check_json_value(item, depth=depth + 1, seen=seen)
    finally:
        seen.remove(object_id)


def canonical_json(payload: object) -> bytes:
    """Return compact UTF-8 JSON with sorted keys and exactly one final LF."""
    _check_json_value(payload)
    try:
        encoded = json.dumps(
            payload,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode("utf-8")
    except (UnicodeEncodeError, TypeError, ValueError, RecursionError) as exc:
        _fail("UNSUPPORTED_JSON_VALUE", str(exc))
    if len(encoded) + 1 > MAX_JSON_BYTES:
        _fail("LIMIT_JSON_BYTES", str(MAX_JSON_BYTES))
    return encoded + b"\n"


def load_payload(raw: bytes) -> dict[str, Any]:
    """Load one exact canonical JSON object, rejecting duplicate keys."""
    if not isinstance(raw, (bytes, bytearray, memoryview)):
        _fail("PAYLOAD_TYPE", "raw payload must be bytes")
    raw_bytes = bytes(raw)
    if not raw_bytes or len(raw_bytes) > MAX_JSON_BYTES:
        _fail("LIMIT_JSON_BYTES", str(MAX_JSON_BYTES))

    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                _fail("DUPLICATE_JSON_KEY", key)
            result[key] = value
        return result

    def reject_constant(value: str) -> object:
        _fail("UNSUPPORTED_JSON_VALUE", value)

    try:
        text = raw_bytes.decode("utf-8")
        payload = json.loads(
            text,
            object_pairs_hook=unique_object,
            parse_constant=reject_constant,
        )
    except TeamRecordError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        _fail("PAYLOAD_INVALID", str(exc))
    if not isinstance(payload, dict):
        _fail("PAYLOAD_NOT_OBJECT")
    try:
        canonical = canonical_json(payload)
    except TeamRecordError:
        raise
    if canonical != raw_bytes:
        _fail("NONCANONICAL_PAYLOAD")
    return payload


def _coerce_payload(payload: object) -> dict[str, Any]:
    if isinstance(payload, (bytes, bytearray, memoryview)):
        return load_payload(bytes(payload))
    if not isinstance(payload, dict):
        _fail("PAYLOAD_TYPE", "payload must be a dict or canonical JSON bytes")
    # Running the same value through canonical_json catches unsupported values
    # before schema validation without normalising the caller's object.
    canonical_json(payload)
    return dict(payload)


def _require_closed(payload: Mapping[str, Any], required: frozenset[str], optional: frozenset[str] = frozenset()) -> None:
    keys = set(payload)
    missing = required - keys
    unknown = keys - required - optional
    if missing:
        _fail("SCHEMA_MISSING_FIELD", ",".join(sorted(missing)))
    if unknown:
        _fail("SCHEMA_UNKNOWN_FIELD", ",".join(sorted(unknown)))


def _text(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        _fail("FIELD_INVALID", field)
    if "\x00" in value or len(value.encode("utf-8")) > MAX_TEXT_BYTES:
        _fail("FIELD_INVALID", field)
    return value


def _id(value: object, field: str) -> str:
    text = _text(value, field)
    if ID_RE.fullmatch(text) is None:
        _fail("FIELD_INVALID", field)
    return text


def _timestamp(value: object, field: str) -> str:
    text = _text(value, field)
    if TIMESTAMP_RE.fullmatch(text) is None:
        _fail("FIELD_INVALID", field)
    try:
        datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError:
        _fail("FIELD_INVALID", field)
    return text


def _sha_field(value: object, field: str, *, allow_absent: bool = False) -> str:
    if not _is_sha(value, allow_absent=allow_absent):
        _fail("FIELD_INVALID", field)
    return str(value)


def _commit_field(value: object, field: str) -> str:
    if not isinstance(value, str) or COMMIT_RE.fullmatch(value) is None:
        _fail("FIELD_INVALID", field)
    return value


def _relative_path(value: object, field: str) -> str:
    text = _text(value, field)
    path = PurePosixPath(text)
    if path.is_absolute() or ".." in path.parts or "\\" in text or path.as_posix() != text:
        _fail("FIELD_INVALID", field)
    return text


def _locator(value: object, field: str) -> str:
    text = _text(value, field)
    if "\r" in text or "\n" in text:
        _fail("FIELD_INVALID", field)
    return text


def _pair_list(value: object, field: str, key: str, *, path_key: bool = False) -> list[dict[str, str]]:
    if not isinstance(value, list) or len(value) > MAX_COLLECTION_ITEMS:
        _fail("FIELD_INVALID", field)
    rows: list[dict[str, str]] = []
    seen: set[str] = set()
    for index, row in enumerate(value):
        if not isinstance(row, dict) or set(row) != {key, "sha256"}:
            _fail("FIELD_INVALID", f"{field}[{index}]")
        name = (_relative_path if path_key else _locator)(row[key], f"{field}[{index}].{key}")
        digest = _sha_field(row["sha256"], f"{field}[{index}].sha256")
        if name in seen:
            _fail("DUPLICATE_ARRAY_ITEM", f"{field}:{name}")
        seen.add(name)
        rows.append({key: name, "sha256": digest})
    if [row[key] for row in rows] != sorted(row[key] for row in rows):
        _fail("NONCANONICAL_ARRAY_ORDER", field)
    return rows


def _string_list(value: object, field: str, *, paths: bool = False, sorted_values: bool = True) -> list[str]:
    if not isinstance(value, list) or len(value) > MAX_COLLECTION_ITEMS:
        _fail("FIELD_INVALID", field)
    result: list[str] = []
    seen: set[str] = set()
    for index, item in enumerate(value):
        item_value = (_relative_path if paths else _text)(item, f"{field}[{index}]")
        if item_value in seen:
            _fail("DUPLICATE_ARRAY_ITEM", f"{field}:{item_value}")
        seen.add(item_value)
        result.append(item_value)
    if sorted_values and result != sorted(result):
        _fail("NONCANONICAL_ARRAY_ORDER", field)
    return result


def _source_ref(value: object, field: str) -> dict[str, str]:
    if not isinstance(value, dict) or set(value) != {"locator", "sha256"}:
        _fail("FIELD_INVALID", field)
    return {
        "locator": _locator(value["locator"], f"{field}.locator"),
        "sha256": _sha_field(value["sha256"], f"{field}.sha256"),
    }


def _validate_report(payload: Mapping[str, Any]) -> dict[str, Any]:
    _require_closed(payload, REPORT_REQUIRED_FIELDS, REPORT_OPTIONAL_FIELDS)
    if payload["schema"] != ISSUE_REPORT_SCHEMA:
        _fail("SCHEMA_UNSUPPORTED", "report")
    if any(key in payload for key in ("report_id", "issue_id", "payload_sha256")):
        _fail("SCHEMA_DERIVED_FIELD", "report IDs are derived")
    result = dict(payload)
    for field in (
        "reporter_task",
        "reporter_host",
        "assignment_id",
        "attempt_id",
        "subject_id",
        "subject_type",
        "suspected_class",
        "expected_behavior",
        "actual_behavior",
        "reproduction",
        "uncertainty",
    ):
        result[field] = _text(result[field], field)
    if result["severity"] not in SEVERITIES:
        _fail("FIELD_INVALID", "severity")
    result["observed_at"] = _timestamp(result["observed_at"], "observed_at")
    result["base_commit"] = _commit_field(result["base_commit"], "base_commit")
    result["input_paths"] = _pair_list(result["input_paths"], "input_paths", "path", path_key=True)
    if not result["input_paths"]:
        _fail("INPUT_BINDING_REQUIRED", "input_paths")
    result["expected_rule_source"] = _source_ref(result["expected_rule_source"], "expected_rule_source")
    result["affected_operations"] = _string_list(result["affected_operations"], "affected_operations")
    if not result["affected_operations"]:
        _fail("AFFECTED_OPERATION_REQUIRED", "affected_operations")
    result["evidence"] = _pair_list(result["evidence"], "evidence", "locator")
    if not result["evidence"]:
        _fail("EVIDENCE_REQUIRED", "evidence")
    if "supersedes_report_id" in result:
        supersedes = result["supersedes_report_id"]
        if not isinstance(supersedes, str) or re.fullmatch(r"report-[0-9a-f]{64}", supersedes) is None:
            _fail("FIELD_INVALID", "supersedes_report_id")
    return result


def _validate_transition(payload: Mapping[str, Any]) -> dict[str, Any]:
    _require_closed(payload, TRANSITION_REQUIRED_FIELDS, TRANSITION_OPTIONAL_FIELDS)
    if payload["schema"] != ISSUE_TRANSITION_SCHEMA:
        _fail("SCHEMA_UNSUPPORTED", "issue transition")
    result = dict(payload)
    issue_id = result["issue_id"]
    report_id = result["report_id"]
    if not isinstance(issue_id, str) or not re.fullmatch(r"issue-[0-9a-f]{64}", issue_id):
        _fail("FIELD_INVALID", "issue_id")
    if not isinstance(report_id, str) or not re.fullmatch(r"report-[0-9a-f]{64}", report_id):
        _fail("FIELD_INVALID", "report_id")
    transition = result["transition"]
    if not isinstance(transition, str) or transition not in ALLOWED_TRANSITIONS:
        _fail("TRANSITION_INVALID", str(transition))
    result["actor_id"] = _text(result["actor_id"], "actor_id")
    result["actor_role"] = _text(result["actor_role"], "actor_role")
    result["reason"] = _text(result["reason"], "reason")
    result["evidence"] = _pair_list(result["evidence"], "evidence", "locator")
    result["source_binding"] = _pair_list(result["source_binding"], "source_binding", "locator")
    if not result["evidence"] or not result["source_binding"]:
        _fail("SOURCE_BINDING_REQUIRED", transition)
    result["previous_event_sha256"] = _sha_field(
        result["previous_event_sha256"], "previous_event_sha256", allow_absent=True
    )
    result["previous_state_sha256"] = _sha_field(
        result["previous_state_sha256"], "previous_state_sha256", allow_absent=True
    )
    for field in ("implementer_id", "verifier_id", "repair_subject_type", "repair_subject_id"):
        if field in result:
            result[field] = (_text if field in {"implementer_id", "verifier_id"} else _id)(result[field], field)
    if "reviewer_severity" in result and result["reviewer_severity"] not in SEVERITIES:
        _fail("FIELD_INVALID", "reviewer_severity")
    if transition == "DUPLICATE":
        if "duplicate_of_issue_id" not in result:
            _fail("FIELD_REQUIRED", "duplicate_of_issue_id")
        if not isinstance(result["duplicate_of_issue_id"], str) or re.fullmatch(
            r"issue-[0-9a-f]{64}", result["duplicate_of_issue_id"]
        ) is None:
            _fail("FIELD_INVALID", "duplicate_of_issue_id")
    elif "duplicate_of_issue_id" in result:
        _fail("FIELD_INVALID", "duplicate_of_issue_id")
    if transition in REPAIR_STATES:
        for field in ("repair_subject_type", "repair_subject_id"):
            if field not in result:
                _fail("FIELD_REQUIRED", field)
    has_candidate_manifest = "candidate_manifest" in result
    has_candidate_commit = "candidate_commit" in result
    if has_candidate_manifest:
        result["candidate_manifest"] = _pair_list(
            result["candidate_manifest"], "candidate_manifest", "path", path_key=True
        )
        if not result["candidate_manifest"]:
            _fail("CANDIDATE_MANIFEST_REQUIRED", transition)
    if has_candidate_commit:
        result["candidate_commit"] = _commit_field(result["candidate_commit"], "candidate_commit")
    if transition == "FIX_VERIFIED":
        if not has_candidate_manifest:
            _fail("FIELD_REQUIRED", "candidate_manifest")
        if has_candidate_commit:
            _fail("CANDIDATE_COMMIT_PREMATURE", transition)
    elif transition in {"FIX_COMMITTED", "FIX_PUSH_VERIFIED"}:
        if not has_candidate_manifest:
            _fail("FIELD_REQUIRED", "candidate_manifest")
        if not has_candidate_commit:
            _fail("FIELD_REQUIRED", "candidate_commit")
    elif has_candidate_manifest or has_candidate_commit:
        _fail("CANDIDATE_FIELDS_INVALID", transition)
    if transition == "FIX_VERIFIED" and "verifier_id" in result:
        if result["verifier_id"] != result["actor_id"]:
            _fail("INDEPENDENT_IDENTITY_REQUIRED", "verifier_id must equal actor_id")
    return result


def _validate_repair_review(payload: Mapping[str, Any]) -> dict[str, Any]:
    _require_closed(payload, REPAIR_REVIEW_REQUIRED_FIELDS)
    if payload["schema"] != REPAIR_REVIEW_SCHEMA:
        _fail("SCHEMA_UNSUPPORTED", "repair review")
    result = dict(payload)
    for field_name in ("issue_id",):
        if not isinstance(result[field_name], str) or re.fullmatch(
            r"issue-[0-9a-f]{64}", result[field_name]
        ) is None:
            _fail("FIELD_INVALID", field_name)
    result["repair_subject_type"] = _id(result["repair_subject_type"], "repair_subject_type")
    result["repair_subject_id"] = _id(result["repair_subject_id"], "repair_subject_id")
    result["base_commit"] = _commit_field(result["base_commit"], "base_commit")
    result["candidate_manifest"] = _pair_list(
        result["candidate_manifest"], "candidate_manifest", "path", path_key=True
    )
    if not result["candidate_manifest"]:
        _fail("CANDIDATE_MANIFEST_REQUIRED", "repair review")
    if result["verdict"] != "REPAIR_APPROVED":
        _fail("REPAIR_REVIEW_NOT_APPROVED", "repair review verdict")
    return result


def _validate_assignment(payload: Mapping[str, Any]) -> dict[str, Any]:
    _require_closed(payload, ASSIGNMENT_REQUIRED_FIELDS)
    if payload["schema"] != ASSIGNMENT_SCHEMA:
        _fail("SCHEMA_UNSUPPORTED", "assignment")
    result = dict(payload)
    for field in (
        "assignment_id",
        "owner_task",
        "owner_host",
        "assignee",
        "role",
        "subject",
        "output_locator",
        "stopping_condition",
    ):
        result[field] = _id(result[field], field) if field == "assignment_id" else _text(result[field], field)
    result["owner_installation_ref"] = _sha_field(result["owner_installation_ref"], "owner_installation_ref")
    if not isinstance(result["owner_epoch"], int) or isinstance(result["owner_epoch"], bool) or result["owner_epoch"] < 0:
        _fail("FIELD_INVALID", "owner_epoch")
    for field in ("requested_model", "resolved_model"):
        result[field] = _text(result[field], field)
    for field in ("requested_effort", "resolved_effort"):
        result[field] = _text(result[field], field)
        if result[field] not in MODEL_EFFORTS:
            _fail("FIELD_INVALID", field)
    if result["operation"] not in ASSIGNMENT_OPERATIONS:
        _fail("FIELD_INVALID", "operation")
    result["base_commit"] = _commit_field(result["base_commit"], "base_commit")
    result["input_hashes"] = _pair_list(result["input_hashes"], "input_hashes", "path", path_key=True)
    result["permitted_paths"] = _string_list(result["permitted_paths"], "permitted_paths", paths=True)
    result["prerequisites"] = _string_list(result["prerequisites"], "prerequisites")
    if not isinstance(result["expected_duration_seconds"], int) or isinstance(
        result["expected_duration_seconds"], bool
    ) or result["expected_duration_seconds"] < 0:
        _fail("FIELD_INVALID", "expected_duration_seconds")
    result["next_check"] = _timestamp(result["next_check"], "next_check")
    if result["status"] not in ASSIGNMENT_STATUSES:
        _fail("FIELD_INVALID", "status")
    result["previous_assignment_sha256"] = _sha_field(
        result["previous_assignment_sha256"], "previous_assignment_sha256", allow_absent=True
    )
    result["previous_assignment_event_sha256"] = _sha_field(
        result["previous_assignment_event_sha256"],
        "previous_assignment_event_sha256",
        allow_absent=True,
    )
    return result


def _validate_archive_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    _require_closed(payload, ARCHIVE_PAYLOAD_FIELDS)
    if payload["schema"] != ARCHIVE_REF_SCHEMA:
        _fail("SCHEMA_UNSUPPORTED", "archive reference")
    ref = payload["archive_ref"]
    if not isinstance(ref, dict) or set(ref) != {"path", "sha256"}:
        _fail("FIELD_INVALID", "archive_ref")
    path = _relative_path(ref["path"], "archive_ref.path")
    digest = _sha_field(ref["sha256"], "archive_ref.sha256")
    count = payload["event_count"]
    if not isinstance(count, int) or isinstance(count, bool) or not 1 <= count <= MAX_EVENTS:
        _fail("FIELD_INVALID", "event_count")
    return {
        "schema": ARCHIVE_REF_SCHEMA,
        "archive_ref": {"path": path, "sha256": digest},
        "event_count": count,
        "first_event_sha256": _sha_field(payload["first_event_sha256"], "first_event_sha256"),
        "last_event_sha256": _sha_field(payload["last_event_sha256"], "last_event_sha256"),
    }


def _event_id(core: Mapping[str, Any]) -> str:
    return "event-" + _sha256(canonical_json(dict(core)))


def _event_sha(event: Mapping[str, Any]) -> str:
    return _sha256(canonical_json(dict(event)))


def _payload_sha(payload: Mapping[str, Any]) -> str:
    return _sha256(canonical_json(dict(payload)))


def _assignment_registry_view(assignments_registry: Mapping[str, Any]) -> Mapping[str, Any]:
    """Return the parsed assignment rows used for provenance checks."""
    if not isinstance(assignments_registry, Mapping):
        _fail("ASSIGNMENT_REGISTRY_INVALID", "expected parsed assignment registry")
    if "kind" in assignments_registry and assignments_registry.get("kind") != "assignments":
        _fail("ASSIGNMENT_REGISTRY_INVALID", "registry kind is not assignments")
    rows = assignments_registry.get("assignments", assignments_registry)
    if not isinstance(rows, Mapping):
        _fail("ASSIGNMENT_REGISTRY_INVALID", "assignments must be a mapping")
    return rows


def _assignment_from_row(row: object, assignment_id: str) -> dict[str, Any]:
    if not isinstance(row, Mapping) or not isinstance(row.get("assignment"), Mapping):
        _fail("ASSIGNMENT_REGISTRY_INVALID", assignment_id)
    assignment = _validate_assignment(dict(row["assignment"]))
    if assignment["assignment_id"] != assignment_id:
        _fail("ASSIGNMENT_REGISTRY_INVALID", "assignment key does not match payload")
    return assignment


def _validated_context(context: TrustedTeamContext) -> TrustedTeamContext:
    if not isinstance(context, TrustedTeamContext):
        _fail("TRUSTED_CONTEXT_INVALID", "TrustedTeamContext required")
    _text(context.owner_task, "owner_task")
    _text(context.owner_host, "owner_host")
    _sha_field(context.owner_installation_ref, "owner_installation_ref")
    if not isinstance(context.owner_epoch, int) or isinstance(context.owner_epoch, bool) or context.owner_epoch < 0:
        _fail("TRUSTED_CONTEXT_INVALID", "owner_epoch")
    _id(context.actor_id, "actor_id")
    if not isinstance(context.observations, Mapping):
        _fail("TRUSTED_CONTEXT_INVALID", "observations must be a mapping")
    if not isinstance(context.output_artifacts, Mapping):
        _fail("TRUSTED_CONTEXT_INVALID", "output_artifacts must be a mapping")
    for locator, raw in context.output_artifacts.items():
        _locator(locator, "output_artifacts.locator")
        if not isinstance(raw, (bytes, bytearray, memoryview)):
            _fail("TRUSTED_CONTEXT_INVALID", "output_artifacts bytes required")
    return context


def _validate_assignment_owner(assignment: Mapping[str, Any], context: TrustedTeamContext) -> None:
    if assignment["owner_task"] != context.owner_task:
        _fail("OWNER_CONTEXT_MISMATCH", "owner_task")
    if assignment["owner_host"] != context.owner_host:
        _fail("OWNER_CONTEXT_MISMATCH", "owner_host")
    if assignment["owner_installation_ref"] != context.owner_installation_ref:
        _fail("OWNER_CONTEXT_MISMATCH", "owner_installation_ref")
    if assignment["owner_epoch"] != context.owner_epoch:
        _fail("OWNER_CONTEXT_MISMATCH", "owner_epoch")


def _validate_native_observation(
    assignment: Mapping[str, Any], observation: Mapping[str, Any], *, phase: str
) -> dict[str, Any]:
    if not isinstance(observation, Mapping):
        _fail("NATIVE_OBSERVATION_INVALID", phase)
    if set(observation) != NATIVE_OBSERVATION_REQUIRED_FIELDS:
        _fail("NATIVE_OBSERVATION_SCHEMA_INVALID", phase)
    if observation["schema"] != NATIVE_OBSERVATION_SCHEMA:
        _fail("NATIVE_OBSERVATION_SCHEMA_INVALID", phase)
    if observation["phase"] != phase:
        _fail("NATIVE_OBSERVATION_PHASE_INVALID", phase)
    if observation["assignment_id"] != assignment["assignment_id"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", phase)
    _text(observation["operation_id"], f"{phase}.operation_id")
    if observation["state"] not in NATIVE_OBSERVATION_STATES:
        _fail("NATIVE_OBSERVATION_STATE_INVALID", f"{phase}:{observation['state']}")
    if phase == "LAUNCH" and observation["state"] != "RUNNING":
        _fail("NATIVE_OBSERVATION_STATE_INVALID", "launch must be RUNNING")
    if observation["owner_task"] != assignment["owner_task"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.owner_task")
    if observation["owner_installation_ref"] != assignment["owner_installation_ref"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.owner_installation_ref")
    if observation["owner_epoch"] != assignment["owner_epoch"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.owner_epoch")
    if observation["assignee"] != assignment["assignee"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.assignee")
    if observation["subject"] != assignment["subject"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.subject")
    if observation["native_owner_task"] != assignment["owner_task"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.native_owner_task")
    if observation["requested_model"] != assignment["requested_model"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.requested_model")
    if observation["requested_effort"] != assignment["requested_effort"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.requested_effort")
    if observation["resolved_model"] != assignment["resolved_model"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.resolved_model")
    if observation["resolved_effort"] != assignment["resolved_effort"]:
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.resolved_effort")
    _text(observation["native_agent_id"], f"{phase}.native_agent_id")
    _sha_field(observation["owner_installation_ref"], f"{phase}.owner_installation_ref")
    if not isinstance(observation["owner_epoch"], int) or isinstance(observation["owner_epoch"], bool):
        _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.owner_epoch")
    for field in ("requested_effort", "resolved_effort"):
        if observation[field] not in MODEL_EFFORTS:
            _fail("NATIVE_ASSIGNMENT_BINDING_INVALID", f"{phase}.{field}")
    _locator(observation["output_locator"], f"{phase}.output_locator")
    _sha_field(observation["output_sha256"], f"{phase}.output_sha256")
    _locator(observation["provider_receipt_locator"], f"{phase}.provider_receipt_locator")
    _sha_field(observation["provider_receipt_sha256"], f"{phase}.provider_receipt_sha256")
    _sha_field(observation["payload_sha256"], f"{phase}.payload_sha256")
    _sha_field(observation["evidence_sha256"], f"{phase}.evidence_sha256")
    _sha_field(observation["source_sha256"], f"{phase}.source_sha256")
    if observation["payload_sha256"] != _assignment_binding_sha(assignment):
        _fail("NATIVE_PAYLOAD_BINDING_INVALID", phase)
    expected_source = _sha256(canonical_json(assignment["input_hashes"]))
    if observation["source_sha256"] != expected_source:
        _fail("NATIVE_SOURCE_BINDING_INVALID", phase)
    receipt_evidence = [
        {"locator": observation["output_locator"], "sha256": observation["output_sha256"]},
        {"locator": observation["provider_receipt_locator"], "sha256": observation["provider_receipt_sha256"]},
    ]
    if observation["evidence_sha256"] != _sha256(canonical_json(receipt_evidence)):
        _fail("NATIVE_EVIDENCE_BINDING_INVALID", phase)
    return dict(observation)


def _assignment_observations(
    context: TrustedTeamContext, assignment_id: str
) -> tuple[dict[str, Any], dict[str, Any]]:
    raw = context.observations.get(assignment_id)
    if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes, bytearray)):
        _fail("NATIVE_OBSERVATION_MISSING", assignment_id)
    by_phase: dict[str, Mapping[str, Any]] = {}
    for item in raw:
        if not isinstance(item, Mapping):
            _fail("NATIVE_OBSERVATION_INVALID", assignment_id)
        item_phase = item.get("phase")
        if not isinstance(item_phase, str) or item_phase not in {"LAUNCH", "RESULT"}:
            _fail("NATIVE_OBSERVATION_PHASE_INVALID", assignment_id)
        if item_phase in by_phase:
            _fail("NATIVE_OBSERVATION_DUPLICATE", f"{assignment_id}:{item_phase}")
        by_phase[item_phase] = item
    if set(by_phase) != {"LAUNCH", "RESULT"}:
        _fail("NATIVE_OBSERVATION_MISSING", assignment_id)
    launch = dict(by_phase["LAUNCH"])
    result = dict(by_phase["RESULT"])
    if launch["operation_id"] == result["operation_id"]:
        _fail("NATIVE_OPERATION_BINDING_INVALID", "launch/result operation IDs collide")
    return launch, result


def _validated_assignment_observation(
    assignment: Mapping[str, Any], context: TrustedTeamContext
) -> tuple[dict[str, Any], dict[str, Any]]:
    launch, result = _assignment_observations(context, assignment["assignment_id"])
    if launch["native_agent_id"] != result["native_agent_id"]:
        _fail("NATIVE_AGENT_BINDING_INVALID", assignment["assignment_id"])
    if launch["subject"] != result["subject"]:
        _fail("NATIVE_SUBJECT_BINDING_INVALID", assignment["assignment_id"])
    return (
        _validate_native_observation(assignment, launch, phase="LAUNCH"),
        _validate_native_observation(assignment, result, phase="RESULT"),
    )


def _provenance_result(
    assignment: Mapping[str, Any],
    observations: tuple[dict[str, Any], dict[str, Any]],
    *,
    actor_class: str | None = None,
) -> dict[str, Any]:
    evidence = tuple(
        (observation["phase"], kind, observation[locator], observation[digest])
        for observation in observations
        for kind, locator, digest in (
            ("output", "output_locator", "output_sha256"),
            ("provider_receipt", "provider_receipt_locator", "provider_receipt_sha256"),
        )
    )
    result: dict[str, Any] = {
        "assignment_id": assignment["assignment_id"],
        "source_hashes": tuple((row["path"], row["sha256"]) for row in assignment["input_hashes"]),
        "evidence_hashes": evidence,
        "operation_ids": tuple(observation["operation_id"] for observation in observations),
    }
    if actor_class is not None:
        result["actor_class"] = actor_class
    return result


def validate_report_provenance(
    report: object,
    assignments_registry: Mapping[str, Any],
    context: TrustedTeamContext,
) -> dict[str, Any]:
    """Validate report identity against parsed assignments and native receipts.

    The caller supplies ``context`` only after its native provider and file
    observations have been checked.  This pure helper verifies their hashes and
    bindings, then returns the source/evidence locators the caller must retain
    in its durable receipt.
    """
    payload = _validate_report(_coerce_payload(report))
    context = _validated_context(context)
    rows = _assignment_registry_view(assignments_registry)
    assignment_id = payload["assignment_id"]
    row = rows.get(assignment_id)
    if row is None:
        _fail("ASSIGNMENT_UNKNOWN", assignment_id)
    assignment = _assignment_from_row(row, assignment_id)
    if payload["reporter_task"] != assignment["assignee"]:
        _fail("REPORTER_ASSIGNMENT_MISMATCH", assignment_id)
    if payload["reporter_host"] != assignment["owner_host"]:
        _fail("REPORTER_HOST_MISMATCH", assignment_id)
    if payload["base_commit"] != assignment["base_commit"]:
        _fail("REPORT_BASE_MISMATCH", assignment_id)
    _validate_assignment_owner(assignment, context)
    # The already running orchestrator can report its own observation without
    # inventing a child launch; independent adjudication remains a later event.
    if assignment["assignee"] == context.owner_task and assignment["role"] == "orchestrator":
        return {"assignment_id": assignment_id, "actor_class": "owner",
                "source_hashes": tuple((row["path"], row["sha256"]) for row in assignment["input_hashes"]),
                "evidence_hashes": (), "operation_ids": ()}
    checked = _validated_assignment_observation(assignment, context)
    if checked[1]["output_sha256"] != _payload_sha(payload):
        _fail("REPORT_OUTPUT_BINDING_INVALID", assignment_id)
    return _provenance_result(assignment, checked)


OWNER_TRANSITIONS = frozenset(
    {"REPRODUCING", "ASSIGNED", "FIX_COMMITTED", "FIX_PUSH_VERIFIED"}
)
INDEPENDENT_TRANSITIONS = frozenset({*ISSUE_DISPOSITIONS, "FIX_VERIFIED"})


def _require_result_evidence(payload: Mapping[str, Any], result: Mapping[str, Any]) -> None:
    if not any(
        row["locator"] == result["output_locator"] and row["sha256"] == result["output_sha256"]
        for row in payload["evidence"]
    ):
        _fail("NATIVE_RESULT_EVIDENCE_REQUIRED", result["assignment_id"])
    if result["state"] != "COMPLETED":
        _fail("NATIVE_COMPLETED_RESULT_REQUIRED", result["assignment_id"])


def _require_repair_review_artifact(
    payload: Mapping[str, Any],
    assignment: Mapping[str, Any],
    result: Mapping[str, Any],
    context: TrustedTeamContext,
    *,
    expected_base_commit: str | None,
) -> dict[str, Any]:
    if expected_base_commit is None:
        _fail("NATIVE_REVIEW_BASE_REQUIRED", payload["issue_id"])
    _commit_field(expected_base_commit, "expected_base_commit")
    raw = context.output_artifacts.get(result["output_locator"])
    if not isinstance(raw, (bytes, bytearray, memoryview)):
        _fail("NATIVE_REVIEW_ARTIFACT_MISSING", result["assignment_id"])
    artifact_bytes = bytes(raw)
    if _sha256(artifact_bytes) != result["output_sha256"]:
        _fail("NATIVE_REVIEW_ARTIFACT_HASH_MISMATCH", result["assignment_id"])
    try:
        artifact = _validate_repair_review(load_payload(artifact_bytes))
    except TeamRecordError as exc:
        raise TeamRecordError("NATIVE_REVIEW_ARTIFACT_INVALID", str(exc)) from exc
    if artifact["issue_id"] != payload["issue_id"]:
        _fail("NATIVE_REVIEW_ISSUE_MISMATCH", artifact["issue_id"])
    if (
        artifact["repair_subject_type"] != payload["repair_subject_type"]
        or artifact["repair_subject_id"] != payload["repair_subject_id"]
    ):
        _fail("NATIVE_REVIEW_REPAIR_MISMATCH", payload["repair_subject_id"])
    if artifact["base_commit"] != expected_base_commit:
        _fail("NATIVE_REVIEW_BASE_MISMATCH", artifact["base_commit"])
    if artifact["base_commit"] != assignment["base_commit"]:
        _fail("NATIVE_REVIEW_ASSIGNMENT_BASE_MISMATCH", artifact["base_commit"])
    if artifact["candidate_manifest"] != payload["candidate_manifest"]:
        _fail("NATIVE_REVIEW_MANIFEST_MISMATCH", payload["issue_id"])
    return artifact


def validate_issue_event_actor(
    issue_event: object,
    assignments_registry: Mapping[str, Any],
    context: TrustedTeamContext,
    *,
    expected_base_commit: str | None = None,
) -> dict[str, Any]:
    """Validate owner or independent actor identity for an issue transition."""
    payload = _validate_transition(_coerce_payload(issue_event))
    context = _validated_context(context)
    rows = _assignment_registry_view(assignments_registry)
    transition = payload["transition"]
    actor_role = payload["actor_role"]
    actor_id = payload["actor_id"]
    if transition in OWNER_TRANSITIONS:
        if actor_role not in OWNER_ACTOR_ROLES:
            _fail("ACTOR_ROLE_INVALID", f"owner transition {transition}")
        if actor_id != context.actor_id:
            _fail("OWNER_ACTOR_MISMATCH", transition)
        # Assignment and publication are owner actions. Their exact predecessor,
        # source and publication receipts are checked by the registry/runtime;
        # they do not pretend to be a child's independent result.
        return {"actor_class": "owner", "operation_ids": (), "evidence_hashes": ()}

    if transition == "FIX_CANDIDATE":
        if actor_role not in IMPLEMENTER_ACTOR_ROLES:
            _fail("ACTOR_ROLE_INVALID", "FIX_CANDIDATE requires implementer")
        if payload.get("implementer_id", actor_id) != actor_id:
            _fail("IMPLEMENTER_IDENTITY_INVALID", "candidate actor must equal implementer")
        for assignment_id in sorted(context.observations):
            assignment = _assignment_from_row(rows[assignment_id], assignment_id)
            if assignment["assignee"] != actor_id or assignment["role"] not in IMPLEMENTER_ASSIGNMENT_ROLES:
                continue
            _validate_assignment_owner(assignment, context)
            checked = _validated_assignment_observation(assignment, context)
            _require_result_evidence(payload, checked[1])
            return _provenance_result(assignment, checked, actor_class="implementer")
        _fail("IMPLEMENTER_ASSIGNMENT_MISMATCH", actor_id)

    if transition not in INDEPENDENT_TRANSITIONS:
        _fail("ACTOR_ROLE_INVALID", f"unsupported transition {transition}")
    if actor_role not in INDEPENDENT_ACTOR_ROLES:
        _fail("ACTOR_ROLE_INVALID", f"independent transition {transition}")
    for assignment_id in sorted(context.observations):
        assignment = _assignment_from_row(rows[assignment_id], assignment_id)
        if (
            assignment["assignee"] != actor_id
            or assignment["role"] != actor_role
            or assignment["role"] not in INDEPENDENT_ACTOR_ROLES
        ):
            continue
        _validate_assignment_owner(assignment, context)
        checked = _validated_assignment_observation(assignment, context)
        _require_result_evidence(payload, checked[1])
        if transition == "FIX_VERIFIED":
            _require_repair_review_artifact(
                payload,
                assignment,
                checked[1],
                context,
                expected_base_commit=expected_base_commit,
            )
        return _provenance_result(assignment, checked, actor_class="independent")
    _fail("INDEPENDENT_ACTOR_MISMATCH", actor_id)


def _build_event(
    *,
    kind: str,
    event_type: str,
    issue_id: str,
    report_id: str,
    payload: Mapping[str, Any],
    previous_event_sha256: str,
    previous_state_sha256: str,
    previous_registry_sha256: str,
) -> dict[str, Any]:
    core: dict[str, Any] = {
        "schema": EVENT_SCHEMA,
        "event_type": event_type,
        "kind": kind,
        "issue_id": issue_id,
        "report_id": report_id,
        "payload": dict(payload),
        "payload_sha256": _payload_sha(payload),
        "previous_event_sha256": previous_event_sha256,
        "previous_state_sha256": previous_state_sha256,
        "previous_registry_sha256": previous_registry_sha256,
    }
    event = dict(core)
    event["event_id"] = _event_id(core)
    # The field order is irrelevant on the wire; canonical_json sorts it.
    return event


def _render_frame(event: Mapping[str, Any]) -> bytes:
    event_bytes = canonical_json(dict(event))
    if len(event_bytes) > MAX_FRAME_BYTES:
        _fail("LIMIT_FRAME_BYTES", str(MAX_FRAME_BYTES))
    return FRAME_PREFIX + str(len(event_bytes)).encode("ascii") + b"\n" + event_bytes


def _boundary(kind: str, legacy: bytes) -> bytes:
    return (
        BOUNDARY_MARKER
        + b"schema: "
        + BOUNDARY_SCHEMA.encode("ascii")
        + b"\nkind: "
        + kind.encode("ascii")
        + b"\nlegacy_bytes: "
        + str(len(legacy)).encode("ascii")
        + b"\nlegacy_sha256: "
        + _sha256(legacy).encode("ascii")
        + b"\nframe: q3_team_records_frame.v1\nmanual_text_after_boundary: forbidden\n-->\n"
    )


def _expected_hash(expected_sha256: object) -> str:
    if not isinstance(expected_sha256, str) or SHA256_RE.fullmatch(expected_sha256) is None:
        _fail("EXPECTED_HASH_INVALID")
    return expected_sha256


def _split_registry(raw: bytes, kind: str) -> tuple[bytes, bytes, bool]:
    if not isinstance(raw, bytes):
        _fail("REGISTRY_TYPE", "registry bytes required")
    if len(raw) > MAX_REGISTRY_BYTES:
        _fail("LIMIT_REGISTRY_BYTES", str(MAX_REGISTRY_BYTES))
    marker_count = raw.count(BOUNDARY_MARKER)
    if marker_count == 0:
        return raw, b"", False
    if marker_count != 1:
        _fail("REGISTRY_BOUNDARY_INVALID", "expected one boundary")
    boundary_start = raw.index(BOUNDARY_MARKER)
    legacy = raw[:boundary_start]
    end_marker = raw.find(b"-->\n", boundary_start)
    if end_marker < 0:
        _fail("REGISTRY_BOUNDARY_INVALID", "unterminated boundary")
    boundary_end = end_marker + len(b"-->\n")
    boundary = raw[boundary_start:boundary_end]
    expected = (
        BOUNDARY_MARKER
        + b"schema: "
        + BOUNDARY_SCHEMA.encode("ascii")
        + b"\nkind: "
        + kind.encode("ascii")
        + b"\nlegacy_bytes: "
        + str(len(legacy)).encode("ascii")
        + b"\nlegacy_sha256: "
        + _sha256(legacy).encode("ascii")
        + b"\nframe: q3_team_records_frame.v1\nmanual_text_after_boundary: forbidden\n-->\n"
    )
    if boundary != expected:
        _fail("REGISTRY_BOUNDARY_INVALID", "marker fields or prefix hash drift")
    return legacy, raw[boundary_end:], True


def _validate_event_shape(event: Mapping[str, Any], kind: str) -> dict[str, Any]:
    _require_closed(event, EVENT_FIELDS)
    if event["schema"] != EVENT_SCHEMA or event["kind"] != kind:
        _fail("EVENT_INVALID", "schema or kind")
    event_id = event["event_id"]
    if not isinstance(event_id, str) or DERIVED_ID_RE.fullmatch(event_id) is None or not event_id.startswith("event-"):
        _fail("EVENT_INVALID", "event_id")
    if event["event_type"] not in {"REPORT_RECORDED", "ISSUE_TRANSITION", "ASSIGNMENT_RECORDED", "ARCHIVE"}:
        _fail("EVENT_INVALID", "event_type")
    if not isinstance(event["payload"], dict):
        _fail("EVENT_INVALID", "payload")
    _sha_field(event["payload_sha256"], "payload_sha256")
    if event["payload_sha256"] != _payload_sha(event["payload"]):
        _fail("EVENT_HASH_INVALID", "payload_sha256")
    _sha_field(event["previous_event_sha256"], "previous_event_sha256", allow_absent=True)
    _sha_field(event["previous_state_sha256"], "previous_state_sha256", allow_absent=True)
    _sha_field(event["previous_registry_sha256"], "previous_registry_sha256", allow_absent=True)
    core = {key: event[key] for key in EVENT_FIELDS if key != "event_id"}
    if event_id != _event_id(core):
        _fail("EVENT_HASH_INVALID", "event_id")
    event_type = event["event_type"]
    payload = event["payload"]
    if event_type == "REPORT_RECORDED":
        if kind != "issues" or event["issue_id"] != "issue-" + event["payload_sha256"] or event["report_id"] != "report-" + event["payload_sha256"]:
            _fail("EVENT_INVALID", "report identity")
        _validate_report(payload)
    elif event_type == "ISSUE_TRANSITION":
        if kind != "issues":
            _fail("EVENT_INVALID", "transition kind")
        transition = _validate_transition(payload)
        if event["issue_id"] != transition["issue_id"] or event["report_id"] != transition["report_id"]:
            _fail("EVENT_INVALID", "transition identity")
        if transition["previous_state_sha256"] != event["previous_state_sha256"]:
            _fail("EVENT_INVALID", "transition state binding")
    elif event_type == "ASSIGNMENT_RECORDED":
        if kind != "assignments" or event["issue_id"] != "NONE" or event["report_id"] != "NONE":
            _fail("EVENT_INVALID", "assignment identity")
        _validate_assignment(payload)
    else:
        if event["issue_id"] != "NONE" or event["report_id"] != "NONE":
            _fail("EVENT_INVALID", "archive identity")
        _validate_archive_payload(payload)
    return dict(event)


def _parse_frames(raw_suffix: bytes, kind: str) -> list[dict[str, Any]]:
    frames: list[dict[str, Any]] = []
    cursor = 0
    while cursor < len(raw_suffix):
        if len(frames) >= MAX_EVENTS:
            _fail("LIMIT_EVENTS", str(MAX_EVENTS))
        if not raw_suffix.startswith(FRAME_PREFIX, cursor):
            _fail("REGISTRY_FRAMING_INVALID", f"offset {cursor}")
        header_end = raw_suffix.find(b"\n", cursor + len(FRAME_PREFIX))
        if header_end < 0:
            _fail("REGISTRY_FRAMING_INVALID", "missing frame header LF")
        number = raw_suffix[cursor + len(FRAME_PREFIX) : header_end]
        if (
            not number.isdigit()
            or len(number) > 12
            or (len(number) > 1 and number.startswith(b"0"))
        ):
            _fail("REGISTRY_FRAMING_INVALID", "invalid frame length")
        try:
            length = int(number)
        except ValueError:
            _fail("REGISTRY_FRAMING_INVALID", "invalid frame length")
        if length <= 0 or length > MAX_FRAME_BYTES:
            _fail("LIMIT_FRAME_BYTES", str(length))
        payload_start = header_end + 1
        payload_end = payload_start + length
        if payload_end > len(raw_suffix):
            _fail("REGISTRY_FRAMING_INVALID", "truncated frame")
        payload_raw = raw_suffix[payload_start:payload_end]
        event = load_payload(payload_raw)
        _validate_event_shape(event, kind)
        frames.append(
            {
                "event": event,
                "start": cursor,
                "end": payload_end,
                "frame": raw_suffix[cursor:payload_end],
            }
        )
        cursor = payload_end
    return frames


def _archive_load(ref: Mapping[str, str], archive_loader: object) -> bytes:
    if archive_loader is None:
        _fail("ARCHIVE_LOADER_REQUIRED", ref["path"])
    try:
        if callable(archive_loader):
            result = archive_loader(ref["path"])
        elif isinstance(archive_loader, Mapping):
            result = archive_loader[ref["path"]]
        else:
            _fail("ARCHIVE_LOADER_INVALID", type(archive_loader).__name__)
    except TeamRecordError:
        raise
    except (KeyError, OSError, TypeError, ValueError) as exc:
        _fail("ARCHIVE_LOAD_FAILED", str(exc))
    if not isinstance(result, (bytes, bytearray, memoryview)):
        _fail("ARCHIVE_LOAD_FAILED", "loader must return bytes")
    archive = bytes(result)
    if len(archive) > MAX_ARCHIVE_BYTES:
        _fail("LIMIT_ARCHIVE_BYTES", str(MAX_ARCHIVE_BYTES))
    if _sha256(archive) != ref["sha256"]:
        _fail("ARCHIVE_HASH_INVALID", ref["path"])
    return archive


def _load_archive_records(
    archive: bytes,
    *,
    kind: str,
    expected_previous_event: str,
    archive_loader: object,
    depth: int,
) -> tuple[list[dict[str, Any]], str]:
    if depth > MAX_ARCHIVE_DEPTH:
        _fail("LIMIT_ARCHIVE_DEPTH", str(MAX_ARCHIVE_DEPTH))
    document = load_payload(archive)
    required = {"schema", "kind", "records", "first_event_sha256", "last_event_sha256"}
    if set(document) != required or document["schema"] != ARCHIVE_SCHEMA or document["kind"] != kind:
        _fail("ARCHIVE_INVALID", "closed archive schema")
    records = document["records"]
    if not isinstance(records, list) or not records or len(records) > MAX_EVENTS:
        _fail("ARCHIVE_INVALID", "record count")
    result: list[dict[str, Any]] = []
    previous = expected_previous_event
    for index, row in enumerate(records):
        if not isinstance(row, dict) or set(row) != {"event", "post_registry_sha256"}:
            _fail("ARCHIVE_INVALID", f"records[{index}]")
        event = _validate_event_shape(row["event"], kind)
        post = _sha_field(row["post_registry_sha256"], f"records[{index}].post_registry_sha256")
        if event["event_type"] == "ARCHIVE":
            _fail("ARCHIVE_INVALID", "nested archive marker is not an event")
        if event["previous_event_sha256"] != previous:
            _fail("EVENT_CHAIN_INVALID", f"archive record {index}")
        result.append({"event": event, "post_registry_sha256": post, "archived": True})
        previous = _event_sha(event)
    if document["first_event_sha256"] != _event_sha(result[0]["event"]):
        _fail("ARCHIVE_INVALID", "first event hash")
    if document["last_event_sha256"] != _event_sha(result[-1]["event"]):
        _fail("ARCHIVE_INVALID", "last event hash")
    return result, previous


def _issue_state_view(issue: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "issue_id": issue["issue_id"],
        "report_id": issue["report_id"],
        "state": issue["state"],
        "registration_status": issue["registration_status"],
        "implementer_id": issue.get("implementer_id"),
        "verifier_id": issue.get("verifier_id"),
        "duplicate_of_issue_id": issue.get("duplicate_of_issue_id"),
        "repair_subject_type": issue.get("repair_subject_type"),
        "repair_subject_id": issue.get("repair_subject_id"),
        "repair_candidate_manifest": issue.get("repair_candidate_manifest"),
        "repair_candidate_commit": issue.get("repair_candidate_commit"),
        "reviewer_severity": issue.get("reviewer_severity"),
    }


def _state_sha(issue: Mapping[str, Any]) -> str:
    return _sha256(canonical_json(_issue_state_view(issue)))


def _assignment_state_sha(assignment: Mapping[str, Any]) -> str:
    return _sha256(canonical_json(dict(assignment)))


ASSIGNMENT_BINDING_EXCLUDED_FIELDS = frozenset(
    {
        "operation",
        "status",
        "next_check",
        "previous_assignment_event_sha256",
        "previous_assignment_sha256",
    }
)
ASSIGNMENT_UPDATE_MUTABLE_FIELDS = frozenset(
    {*ASSIGNMENT_BINDING_EXCLUDED_FIELDS, "resolved_model", "resolved_effort"}
)


def _assignment_binding_view(assignment: Mapping[str, Any]) -> dict[str, Any]:
    """Return the stable assignment contract bound into native observations."""
    return {
        key: assignment[key]
        for key in sorted(assignment)
        if key not in ASSIGNMENT_BINDING_EXCLUDED_FIELDS
    }


def _assignment_binding_sha(assignment: Mapping[str, Any]) -> str:
    return _sha256(canonical_json(_assignment_binding_view(assignment)))


def _assignment_immutable_view(assignment: Mapping[str, Any]) -> dict[str, Any]:
    return {
        key: assignment[key]
        for key in sorted(assignment)
        if key not in ASSIGNMENT_UPDATE_MUTABLE_FIELDS
    }


def _apply_issue_event(
    event: Mapping[str, Any],
    event_sha: str,
    issues: dict[str, dict[str, Any]],
    *,
    expected_previous_event: str,
) -> None:
    if event["previous_event_sha256"] != expected_previous_event:
        _fail("EVENT_CHAIN_INVALID", event["event_id"])
    if event["event_type"] == "REPORT_RECORDED":
        # Each report starts a new issue state, while the registry itself is a
        # single global event chain.  Therefore a later report may point to a
        # prior report event as its global predecessor.
        if event["previous_state_sha256"] != "ABSENT":
            _fail("EVENT_CHAIN_INVALID", "initial report predecessor")
        issue_id = event["issue_id"]
        if issue_id in issues:
            _fail("EVENT_CHAIN_INVALID", "duplicate issue")
        report = _validate_report(event["payload"])
        issues[issue_id] = {
            "issue_id": issue_id,
            "report_id": event["report_id"],
            "report": report,
            "state": "OBSERVED",
            "registration_status": "REGISTRY_RECORDED",
            "last_event_sha256": event_sha,
            "event_ids": [event["event_id"]],
        }
        return
    if event["event_type"] != "ISSUE_TRANSITION":
        return
    issue = issues.get(event["issue_id"])
    if issue is None:
        _fail("EVENT_CHAIN_INVALID", "transition before report")
    if event["previous_state_sha256"] != _state_sha(issue):
        _fail("EVENT_PRECONDITION", event["event_id"])
    payload = _validate_transition(event["payload"])
    if payload["previous_event_sha256"] != issue["last_event_sha256"]:
        _fail("EVENT_PRECONDITION", "previous event")
    transition = payload["transition"]
    state = issue["state"]
    legal: dict[str, set[str]] = {
        "OBSERVED": {"REPRODUCING"},
        "REPRODUCING": set(ISSUE_DISPOSITIONS),
        "CONFIRMED_BUG": {"ASSIGNED"},
        "CONFIRMED_RULE_CONFLICT": {"ASSIGNED"},
        "AGENT_CONTEXT_ERROR": set(),
        "EXPECTED_GUARD": set(),
        "UNREPRODUCED": set(),
        "DUPLICATE": set(),
        "DEFERRED": set(),
        "ASSIGNED": {"FIX_CANDIDATE"},
        "FIX_CANDIDATE": {"FIX_VERIFIED"},
        "FIX_VERIFIED": {"FIX_COMMITTED"},
        "FIX_COMMITTED": {"FIX_PUSH_VERIFIED"},
        "FIX_PUSH_VERIFIED": set(),
    }
    if transition not in legal.get(state, set()):
        _fail("ILLEGAL_TRANSITION", f"{state}->{transition}")
    reporter = issue["report"]["reporter_task"]
    actor = payload["actor_id"]
    if "reviewer_severity" in payload:
        previous_severity = issue.get("reviewer_severity")
        if previous_severity is not None and payload["reviewer_severity"] != previous_severity:
            _fail("SEVERITY_IMMUTABLE", "reviewer severity cannot be overwritten")
        issue["reviewer_severity"] = payload["reviewer_severity"]
    if transition in {*ISSUE_DISPOSITIONS, "FIX_VERIFIED"}:
        if actor == reporter:
            _fail("INDEPENDENT_IDENTITY_REQUIRED", "actor equals reporter")
    if transition == "FIX_VERIFIED":
        implementer = issue.get("implementer_id")
        if implementer and actor == implementer:
            _fail("INDEPENDENT_IDENTITY_REQUIRED", "verifier equals implementer")
    if transition == "FIX_CANDIDATE" and payload.get("implementer_id", actor) != actor:
        _fail("IMPLEMENTER_IDENTITY_INVALID", "candidate actor must equal implementer")
    if transition == "FIX_VERIFIED":
        issue["verifier_id"] = actor
    if transition == "FIX_CANDIDATE":
        issue["implementer_id"] = payload.get("implementer_id", actor)
    if transition == "FIX_VERIFIED":
        issue["repair_candidate_manifest"] = payload["candidate_manifest"]
    if transition == "FIX_COMMITTED":
        if payload["candidate_manifest"] != issue.get("repair_candidate_manifest"):
            _fail("REPAIR_CANDIDATE_CHANGED", transition)
        issue["repair_candidate_commit"] = payload["candidate_commit"]
    if transition == "FIX_PUSH_VERIFIED":
        if (payload["candidate_manifest"] != issue.get("repair_candidate_manifest")
                or payload["candidate_commit"] != issue.get("repair_candidate_commit")):
            _fail("REPAIR_CANDIDATE_CHANGED", transition)
    if transition == "DUPLICATE":
        duplicate_of = payload["duplicate_of_issue_id"]
        if duplicate_of == issue["issue_id"] or duplicate_of not in issues:
            _fail("DUPLICATE_TARGET_INVALID", duplicate_of)
        issue["duplicate_of_issue_id"] = duplicate_of
    if transition in REPAIR_STATES:
        if state in REPAIR_STATES and any(payload[key] != issue[key] for key in ("repair_subject_type", "repair_subject_id")):
            _fail("REPAIR_SUBJECT_CHANGED", transition)
        sources = {row["locator"].split(":", 2)[-1]: row["sha256"] for row in payload["source_binding"]}
        if len(sources) != len(payload["source_binding"]):
            _fail("REPAIR_SOURCE_DUPLICATE", transition)
        if state in {"FIX_CANDIDATE", "FIX_VERIFIED", "FIX_COMMITTED"} and sources != issue["repair_sources"]:
            _fail("REPAIR_SOURCE_CHANGED", transition)
        issue["repair_sources"] = sources
        issue["repair_subject_type"] = payload["repair_subject_type"]
        issue["repair_subject_id"] = payload["repair_subject_id"]
    issue["state"] = transition
    issue["last_event_sha256"] = event_sha
    issue["event_ids"].append(event["event_id"])


def _apply_assignment_event(
    event: Mapping[str, Any],
    event_sha: str,
    assignments: dict[str, dict[str, Any]],
    *,
    expected_previous_event: str,
) -> None:
    if event["previous_event_sha256"] != expected_previous_event:
        _fail("EVENT_CHAIN_INVALID", event["event_id"])
    if event["event_type"] != "ASSIGNMENT_RECORDED":
        return
    payload = _validate_assignment(event["payload"])
    assignment_id = payload["assignment_id"]
    current = assignments.get(assignment_id)
    if payload["operation"] == "CREATE":
        if current is not None or payload["previous_assignment_sha256"] != "ABSENT":
            _fail("ASSIGNMENT_PRECONDITION", assignment_id)
    else:
        if current is None or payload["previous_assignment_sha256"] != _assignment_state_sha(current["assignment"]):
            _fail("ASSIGNMENT_PRECONDITION", assignment_id)
        if _assignment_immutable_view(payload) != _assignment_immutable_view(current["assignment"]):
            _fail("ASSIGNMENT_IMMUTABLE_FIELD", assignment_id)
    if payload["previous_assignment_event_sha256"] != (
        "ABSENT" if current is None else current["last_event_sha256"]
    ):
        _fail("ASSIGNMENT_PRECONDITION", "assignment event predecessor")
    if event["previous_state_sha256"] != payload["previous_assignment_sha256"]:
        _fail("EVENT_PRECONDITION", "assignment state")
    assignments[assignment_id] = {
        "assignment_id": assignment_id,
        "assignment": payload,
        "last_event_sha256": event_sha,
        "event_ids": ([] if current is None else current["event_ids"]) + [event["event_id"]],
    }


def _archive_marker_records(
    frames: Sequence[Mapping[str, Any]],
    *,
    raw: bytes,
    kind: str,
    archive_loader: object,
    suffix_offset: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Expand archive marker frames into event records and retain markers."""
    records: list[dict[str, Any]] = []
    markers: list[dict[str, Any]] = []
    previous = "ABSENT"
    for frame in frames:
        event = frame["event"]
        if event["event_type"] == "ARCHIVE":
            if event["previous_event_sha256"] != previous:
                _fail("EVENT_CHAIN_INVALID", "archive marker predecessor")
            payload = _validate_archive_payload(event["payload"])
            archive = _archive_load(payload["archive_ref"], archive_loader)
            archived, previous = _load_archive_records(
                archive,
                kind=kind,
                expected_previous_event=event["previous_event_sha256"],
                archive_loader=archive_loader,
                depth=1,
            )
            if len(archived) != payload["event_count"] or _event_sha(archived[0]["event"]) != payload["first_event_sha256"] or _event_sha(archived[-1]["event"]) != payload["last_event_sha256"]:
                _fail("ARCHIVE_INVALID", "marker summary")
            records.extend(archived)
            markers.append(
                {
                    "event": event,
                    "post_registry_sha256": _sha256(raw[: suffix_offset + frame["end"]]),
                    "archived": False,
                }
            )
        else:
            event_sha = _event_sha(event)
            if event["previous_event_sha256"] != previous:
                _fail("EVENT_CHAIN_INVALID", event["event_id"])
            records.append(
                {
                    "event": event,
                    "post_registry_sha256": _sha256(raw[: suffix_offset + frame["end"]]),
                    "archived": False,
                }
            )
            previous = event_sha
    return records, markers


def read_registry(raw: bytes, kind: str, archive_loader: object = None) -> dict[str, Any]:
    """Parse one issues/assignments registry without executing its text."""
    if kind not in {"issues", "assignments"}:
        _fail("REGISTRY_KIND_INVALID", str(kind))
    if not isinstance(raw, (bytes, bytearray, memoryview)):
        _fail("REGISTRY_TYPE")
    raw_bytes = bytes(raw)
    legacy, suffix, has_boundary = _split_registry(raw_bytes, kind)
    frames = _parse_frames(suffix, kind) if has_boundary else []
    records, markers = _archive_marker_records(
        frames,
        raw=raw_bytes,
        kind=kind,
        archive_loader=archive_loader,
        suffix_offset=len(raw_bytes) - len(suffix),
    )
    issues: dict[str, dict[str, Any]] = {}
    assignments: dict[str, dict[str, Any]] = {}
    previous = "ABSENT"
    for record in records:
        event = record["event"]
        event_sha = _event_sha(event)
        if kind == "issues":
            _apply_issue_event(event, event_sha, issues, expected_previous_event=previous)
        else:
            _apply_assignment_event(event, event_sha, assignments, expected_previous_event=previous)
        previous = event_sha
    return {
        "kind": kind,
        "sha256": _sha256(raw_bytes),
        "legacy_sha256": _sha256(legacy),
        "legacy_prefix": legacy,
        "events": [dict(record["event"]) for record in records],
        "issues": issues,
        "assignments": assignments,
        "_event_records": records,
        "_archive_markers": markers,
        "_has_boundary": has_boundary,
        "_last_event_sha256": previous if records else "ABSENT",
    }


def _frame_append(raw: bytes, kind: str, event: Mapping[str, Any]) -> tuple[bytes, str]:
    legacy, _suffix, has_boundary = _split_registry(raw, kind)
    base = raw if has_boundary else raw + _boundary(kind, legacy)
    frame = _render_frame(event)
    new_raw = base + frame
    if len(new_raw) > MAX_REGISTRY_BYTES:
        _fail("LIMIT_REGISTRY_BYTES", str(MAX_REGISTRY_BYTES))
    return new_raw, _sha256(new_raw)


def _record_core(
    *,
    operation: str,
    event: Mapping[str, Any],
    event_sha256: str,
    pre_registry_sha256: str,
    post_registry_sha256: str,
    status: str,
    report_id: str = "NONE",
    issue_id: str = "NONE",
    assignment_id: str = "NONE",
    extra_fields: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    payload = event["payload"]
    core: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "operation": operation,
        "event_id": event["event_id"],
        "event_sha256": event_sha256,
        "payload_sha256": event["payload_sha256"],
        "pre_registry_sha256": pre_registry_sha256,
        "post_registry_sha256": post_registry_sha256,
        "report_id": report_id,
        "issue_id": issue_id,
        "assignment_id": assignment_id,
        "evidence_sha256": _sha256(canonical_json(payload.get("evidence", payload.get("source_binding", [])))),
    }
    if extra_fields is not None:
        if not isinstance(extra_fields, Mapping):
            _fail("RECEIPT_INVALID", "extra receipt fields must be a mapping")
        if set(core) & set(extra_fields):
            _fail("RECEIPT_INVALID", "extra receipt field collides with core")
        core.update(dict(extra_fields))
    receipt = dict(core)
    receipt["status"] = status
    receipt["receipt_sha256"] = _sha256(canonical_json(core))
    return receipt


def _find_report_record(registry: Mapping[str, Any], report_hash: str) -> dict[str, Any] | None:
    for record in registry["_event_records"]:
        event = record["event"]
        if event["event_type"] == "REPORT_RECORDED" and event["payload_sha256"] == report_hash:
            return record
    return None


def _find_transition_record(registry: Mapping[str, Any], payload_hash: str) -> dict[str, Any] | None:
    for record in registry["_event_records"]:
        event = record["event"]
        if event["event_type"] == "ISSUE_TRANSITION" and event["payload_sha256"] == payload_hash:
            return record
    return None


def _find_assignment_record(registry: Mapping[str, Any], payload_hash: str) -> dict[str, Any] | None:
    for record in registry["_event_records"]:
        event = record["event"]
        if event["event_type"] == "ASSIGNMENT_RECORDED" and event["payload_sha256"] == payload_hash:
            return record
    return None


def _replay_receipt(
    record: Mapping[str, Any],
    *,
    operation: str,
    status: str,
    report_id: str = "NONE",
    issue_id: str = "NONE",
    assignment_id: str = "NONE",
) -> dict[str, Any]:
    event = record["event"]
    return _record_core(
        operation=operation,
        event=event,
        event_sha256=_event_sha(event),
        pre_registry_sha256=event["previous_registry_sha256"],
        post_registry_sha256=record["post_registry_sha256"],
        status=status,
        report_id=report_id,
        issue_id=issue_id,
        assignment_id=assignment_id,
    )


def prepare_report(
    raw: bytes,
    payload: object,
    expected_sha256: str,
    archive_loader: object = None,
) -> tuple[bytes, dict[str, Any]]:
    """Prepare one immutable report append or an exact replay receipt."""
    registry = read_registry(raw, "issues", archive_loader)
    report = _validate_report(_coerce_payload(payload))
    payload_hash = _payload_sha(report)
    report_id = "report-" + payload_hash
    issue_id = "issue-" + payload_hash
    existing = _find_report_record(registry, payload_hash)
    if existing is not None:
        return bytes(raw), _replay_receipt(
            existing,
            operation="REPORT",
            status="NOOP",
            report_id=report_id,
            issue_id=issue_id,
        )
    tuple_key = (report["reporter_task"], report["assignment_id"], report["attempt_id"])
    for issue in registry["issues"].values():
        old = issue["report"]
        if (old["reporter_task"], old["assignment_id"], old["attempt_id"]) == tuple_key:
            _fail("ATTEMPT_COLLISION", "same reporter/assignment/attempt has different bytes")
    if "supersedes_report_id" in report:
        supersedes = report["supersedes_report_id"]
        if not any(issue["report_id"] == supersedes for issue in registry["issues"].values()):
            _fail("SUPERSEDES_UNKNOWN", supersedes)
        old = next(issue["report"] for issue in registry["issues"].values() if issue["report_id"] == supersedes)
        if (old["reporter_task"], old["assignment_id"], old["attempt_id"]) == tuple_key:
            _fail("ATTEMPT_COLLISION", "correction must use a new attempt")
    expected = _expected_hash(expected_sha256)
    actual = registry["sha256"]
    if actual != expected:
        _fail("STALE_REGISTRY", f"expected {expected}, actual {actual}")
    previous_event = registry["_last_event_sha256"]
    event = _build_event(
        kind="issues",
        event_type="REPORT_RECORDED",
        issue_id=issue_id,
        report_id=report_id,
        payload=report,
        previous_event_sha256=previous_event,
        previous_state_sha256="ABSENT",
        previous_registry_sha256=actual,
    )
    new_raw, post = _frame_append(bytes(raw), "issues", event)
    return new_raw, _record_core(
        operation="REPORT",
        event=event,
        event_sha256=_event_sha(event),
        pre_registry_sha256=actual,
        post_registry_sha256=post,
        status="RECORDED",
        report_id=report_id,
        issue_id=issue_id,
    )


def prepare_issue_event(
    raw: bytes,
    payload: object,
    expected_sha256: str,
    archive_loader: object = None,
) -> tuple[bytes, dict[str, Any]]:
    """Prepare one strictly checked issue lifecycle transition."""
    registry = read_registry(raw, "issues", archive_loader)
    transition = _validate_transition(_coerce_payload(payload))
    payload_hash = _payload_sha(transition)
    existing = _find_transition_record(registry, payload_hash)
    if existing is not None:
        return bytes(raw), _replay_receipt(
            existing,
            operation="ISSUE_EVENT",
            status="NOOP",
            report_id=transition["report_id"],
            issue_id=transition["issue_id"],
        )
    expected = _expected_hash(expected_sha256)
    actual = registry["sha256"]
    if actual != expected:
        _fail("STALE_REGISTRY", f"expected {expected}, actual {actual}")
    issue = registry["issues"].get(transition["issue_id"])
    if issue is None or issue["report_id"] != transition["report_id"]:
        _fail("ISSUE_UNKNOWN", transition["issue_id"])
    if transition["previous_event_sha256"] != issue["last_event_sha256"]:
        _fail("EVENT_PRECONDITION", "previous event")
    if transition["previous_state_sha256"] != _state_sha(issue):
        _fail("EVENT_PRECONDITION", "previous state")
    # Validate the transition against a copy of the current state before bytes
    # are prepared; _apply_issue_event is the single lifecycle implementation.
    candidate_issues = {
        issue_key: {
            key: (list(value) if key == "event_ids" else dict(value) if key == "report" else value)
            for key, value in issue_value.items()
        }
        for issue_key, issue_value in registry["issues"].items()
    }
    pseudo_event = _build_event(
        kind="issues",
        event_type="ISSUE_TRANSITION",
        issue_id=transition["issue_id"],
        report_id=transition["report_id"],
        payload=transition,
        # The envelope chains every frame in this registry.  The transition
        # payload separately carries the predecessor of this particular issue.
        previous_event_sha256=registry["_last_event_sha256"],
        previous_state_sha256=transition["previous_state_sha256"],
        previous_registry_sha256=actual,
    )
    _apply_issue_event(
        pseudo_event,
        _event_sha(pseudo_event),
        candidate_issues,
        expected_previous_event=registry["_last_event_sha256"],
    )
    new_raw, post = _frame_append(bytes(raw), "issues", pseudo_event)
    return new_raw, _record_core(
        operation="ISSUE_EVENT",
        event=pseudo_event,
        event_sha256=_event_sha(pseudo_event),
        pre_registry_sha256=actual,
        post_registry_sha256=post,
        status="RECORDED",
        report_id=transition["report_id"],
        issue_id=transition["issue_id"],
    )


def prepare_assignment(
    raw: bytes,
    payload: object,
    expected_sha256: str,
    archive_loader: object = None,
) -> tuple[bytes, dict[str, Any]]:
    """Prepare an exact CREATE/UPDATE/RETRY assignment event."""
    registry = read_registry(raw, "assignments", archive_loader)
    assignment = _validate_assignment(_coerce_payload(payload))
    payload_hash = _payload_sha(assignment)
    existing = _find_assignment_record(registry, payload_hash)
    if existing is not None:
        return bytes(raw), _replay_receipt(
            existing,
            operation="ASSIGNMENT",
            status="NOOP",
            assignment_id=assignment["assignment_id"],
        )
    expected = _expected_hash(expected_sha256)
    actual = registry["sha256"]
    if actual != expected:
        _fail("STALE_REGISTRY", f"expected {expected}, actual {actual}")
    current = registry["assignments"].get(assignment["assignment_id"])
    if assignment["operation"] == "CREATE":
        if current is not None or assignment["previous_assignment_sha256"] != "ABSENT":
            _fail("ASSIGNMENT_CONFLICT", assignment["assignment_id"])
    else:
        if current is None:
            _fail("ASSIGNMENT_UNKNOWN", assignment["assignment_id"])
        if assignment["previous_assignment_sha256"] != _assignment_state_sha(current["assignment"]):
            _fail("ASSIGNMENT_PRECONDITION", assignment["assignment_id"])
        if _assignment_immutable_view(assignment) != _assignment_immutable_view(current["assignment"]):
            _fail("ASSIGNMENT_IMMUTABLE_FIELD", assignment["assignment_id"])
    previous_assignment_event = current["last_event_sha256"] if current is not None else "ABSENT"
    if assignment["previous_assignment_event_sha256"] != previous_assignment_event:
        _fail("ASSIGNMENT_PRECONDITION", "assignment event predecessor")
    if previous_assignment_event == "ABSENT" and assignment["operation"] != "CREATE":
        _fail("ASSIGNMENT_PRECONDITION", "missing predecessor")
    event = _build_event(
        kind="assignments",
        event_type="ASSIGNMENT_RECORDED",
        issue_id="NONE",
        report_id="NONE",
        payload=assignment,
        # As with issue transitions, keep global frame order in the envelope
        # and assignment-local CAS in the payload.
        previous_event_sha256=registry["_last_event_sha256"],
        previous_state_sha256=assignment["previous_assignment_sha256"],
        previous_registry_sha256=actual,
    )
    new_raw, post = _frame_append(bytes(raw), "assignments", event)
    return new_raw, _record_core(
        operation="ASSIGNMENT",
        event=event,
        event_sha256=_event_sha(event),
        pre_registry_sha256=actual,
        post_registry_sha256=post,
        status="RECORDED",
        assignment_id=assignment["assignment_id"],
    )


def prepare_archive(
    raw: bytes,
    kind: str,
    expected_sha256: str,
    archive_ref: str | None = None,
    *,
    event_count: int = 1,
    archive_loader: object = None,
) -> tuple[bytes, bytes, dict[str, Any]]:
    """Return ``(immutable_archive_bytes, new_registry_bytes, receipt)``.

    The helper archives a prefix of currently live event frames.  The caller
    writes the returned archive bytes to its existing protocol area and then
    atomically installs the returned registry bytes.  It does not touch either
    destination.  Archiving an already archived prefix is rejected so the
    chain stays bounded and unambiguous.
    """
    registry = read_registry(raw, kind, archive_loader)
    expected = _expected_hash(expected_sha256)
    actual = registry["sha256"]
    if actual != expected:
        _fail("STALE_REGISTRY", f"expected {expected}, actual {actual}")
    if not registry["_has_boundary"] or not registry["_event_records"]:
        _fail("ARCHIVE_NOT_AVAILABLE", "no structured events")
    if not isinstance(event_count, int) or isinstance(event_count, bool) or not 1 <= event_count <= len(registry["_event_records"]):
        _fail("ARCHIVE_EVENT_COUNT_INVALID")
    if registry["_archive_markers"]:
        _fail("ARCHIVE_PREFIX_ALREADY_MOVED")
    records = registry["_event_records"][:event_count]
    # Locate the corresponding raw frame range after the boundary.
    _legacy, suffix, _has_boundary = _split_registry(bytes(raw), kind)
    _frames = _parse_frames(suffix, kind)
    if len(_frames) < event_count:
        _fail("ARCHIVE_INVALID", "frame range")
    boundary_end = len(raw) - len(suffix)
    first_start = boundary_end + _frames[0]["start"]
    last_end = boundary_end + _frames[event_count - 1]["end"]
    prefix = bytes(raw[:first_start])
    suffix_after = bytes(raw[last_end:])
    archive_path = archive_ref or f"archive/{kind}-{_event_sha(records[-1]['event'] )}.json"
    archive_path = _relative_path(archive_path, "archive_ref.path")
    archive_records = [
        {
            "event": record["event"],
            "post_registry_sha256": record["post_registry_sha256"],
        }
        for record in records
    ]
    archive_document = {
        "schema": ARCHIVE_SCHEMA,
        "kind": kind,
        "records": archive_records,
        "first_event_sha256": _event_sha(records[0]["event"]),
        "last_event_sha256": _event_sha(records[-1]["event"]),
    }
    archive_bytes = canonical_json(archive_document)
    if len(archive_bytes) > MAX_ARCHIVE_BYTES:
        _fail("LIMIT_ARCHIVE_BYTES", str(MAX_ARCHIVE_BYTES))
    archive_digest = _sha256(archive_bytes)
    marker_payload = {
        "schema": ARCHIVE_REF_SCHEMA,
        "archive_ref": {"path": archive_path, "sha256": archive_digest},
        "event_count": event_count,
        "first_event_sha256": _event_sha(records[0]["event"]),
        "last_event_sha256": _event_sha(records[-1]["event"]),
    }
    marker = _build_event(
        kind=kind,
        event_type="ARCHIVE",
        issue_id="NONE",
        report_id="NONE",
        payload=marker_payload,
        previous_event_sha256="ABSENT",
        previous_state_sha256="ABSENT",
        previous_registry_sha256=_sha256(prefix),
    )
    new_raw = prefix + _render_frame(marker) + suffix_after
    if len(new_raw) > MAX_REGISTRY_BYTES:
        _fail("LIMIT_REGISTRY_BYTES", str(MAX_REGISTRY_BYTES))
    receipt = _record_core(
        operation="ARCHIVE",
        event=marker,
        event_sha256=_event_sha(marker),
        pre_registry_sha256=actual,
        post_registry_sha256=_sha256(new_raw),
        status="RECORDED",
        extra_fields={"archive_sha256": archive_digest, "archive_ref": archive_path},
    )
    return archive_bytes, new_raw, receipt


__all__ = [
    "ASSIGNMENT_SCHEMA",
    "ASSIGNMENT_REQUIRED_FIELDS",
    "BOUNDARY_SCHEMA",
    "EVENT_SCHEMA",
    "EVENT_FIELDS",
    "ISSUE_DISPOSITIONS",
    "ISSUE_REPORT_SCHEMA",
    "NATIVE_OBSERVATION_SCHEMA",
    "NATIVE_OBSERVATION_REQUIRED_FIELDS",
    "NATIVE_OBSERVATION_STATES",
    "REPAIR_REVIEW_SCHEMA",
    "REPAIR_REVIEW_REQUIRED_FIELDS",
    "REPORT_REQUIRED_FIELDS",
    "REPAIR_STATES",
    "SEVERITIES",
    "ISSUE_TRANSITION_SCHEMA",
    "TRANSITION_REQUIRED_FIELDS",
    "TrustedTeamContext",
    "TeamRecordError",
    "canonical_json",
    "load_payload",
    "prepare_archive",
    "prepare_assignment",
    "prepare_issue_event",
    "prepare_report",
    "read_registry",
    "validate_issue_event_actor",
    "validate_report_provenance",
]
