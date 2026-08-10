#!/usr/bin/env python3
"""Knowledge Spine aggregator and strict control-plane entrypoint.

Collects every negative-knowledge / insight / strategy-memory surface of the
repo into one deterministic machine view and one human view.

Sources are never modified. Ownership zones stay intact: this script lives in
the conductor zone (orchestrator/) and only reads elsewhere.

Usage:
    ./orchestrator/spine.py            # write SPINE_STATE.json + SPINE_VIEW.md
    ./orchestrator/spine.py --refresh  # write upstream refreshes before validation
    ./orchestrator/spine.py --stdout   # read-only unless combined with --refresh
    ./orchestrator/spine.py --strict --stdout --reason session-start

P9 control/runtime/operator validation is unconditional in every mode.
``--strict`` adds the semantic-index plant gate and a receipt; it does not turn
otherwise absent P9 validation on.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import sqlite3
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import yaml

try:
    from orchestrator import observability as _observability
    from orchestrator import kb as _kb
except ModuleNotFoundError:  # direct `python3 orchestrator/spine.py`
    import observability as _observability
    import kb as _kb

REPO = Path(__file__).resolve().parents[1]
OUT = REPO / "orchestrator" / "state" / "SPINE_VIEW.md"
STATE_OUT = REPO / "orchestrator" / "state" / "SPINE_STATE.json"
META_CORPUS_OUT = REPO / "orchestrator" / "state" / "META_CORPUS.json"
KNOWLEDGE_DB = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"
CONTROL = REPO / "docs" / "CODEX_CONTROL.md"
CHANNEL_RUNTIME = REPO / "orchestrator" / "state" / "CHANNEL_RUNTIME.json"
BEHAVIOR_REGISTRY = REPO / "orchestrator" / "BEHAVIOR_CONTROL_REGISTRY.json"
ARTIFACT_REGISTRY = REPO / "orchestrator" / "ARTIFACT_IDENTITY_REGISTRY.json"
AUTOPSY_MAP = REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs" / "AUTOPSY_MAP.json"
SEMANTIC_INDEX_STATUS = REPO / "orchestrator" / "state" / "SEMANTIC_INDEX_STATUS.json"
OBSERVABILITY_DB = (
    REPO / "q3.lean.aristotle" / "aristotle_db" / "observability.db"
)
COGNITIVE_OPERATOR_REGISTRY = REPO / "q3.lean.aristotle" / "COGNITIVE_OPERATORS.md"
TOOL_MANIFEST = REPO / "docs" / "cartographer" / "TOOLS.yaml"
TOOL_MANIFEST_MIRROR = Path("/Users/emalam/GitHub/codex_specs/TOOLS.yaml")

PHASE_KEY_FIELDS = (
    "route_id",
    "front_id",
    "source_object_family_id",
    "terminal_consumer_id",
    "honesty_state",
    "convention_lock_id",
)
PROGRESS_DELTA_KINDS = {
    "THEOREM_OR_LEMMA_CLOSED",
    "SOURCE_FOUND",
    "SOURCE_ABSENCE_CERTIFIED",
    "HYPOTHESIS_REMOVED",
    "COUNTEREXAMPLE_FOUND",
    "BLOCKER_DECOMPOSED",
    "QUANTITATIVE_INTERVAL_NARROWED",
    "DEPENDENCY_EDGE_REMOVED",
}
NON_PROGRESS_KINDS = {
    "COMMIT_CREATED",
    "BUILD_REPEATED",
    "WRAPPER_CREATED",
    "FILE_RENAMED",
    "WORDING_CHANGED",
    "ELAPSED_TIME",
    "CONTEXT_REUPLOADED",
    "SAME_EXPERIMENT_RENAMED",
}
DELTA_SCOPES = {"ABSTRACT", "FINITE_CELL", "COFINAL_FAMILY"}
DELTA_VERIFIERS = {"LEAN", "ARB_INTERVAL", "PAPER", "CONDITIONAL"}
RESET_VERIFIERS = {"LEAN", "ARB_INTERVAL", "PAPER"}
DECISION_EFFECTS = {
    "CANDIDATE_SELECTED",
    "CANDIDATE_KILLED",
    "ASSUMPTION_REMOVED",
    "SOURCE_STATUS_CHANGED",
    "BLOCKER_STRICTLY_SHRUNK",
    "INTERVAL_STRICTLY_NARROWED",
    "DEPENDENCY_REMOVED",
}


class ControlViolation(ValueError):
    """A fail-closed P9A behavior-control violation."""

    def __init__(self, code: str, detail: str = "") -> None:
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code
        self.detail = detail


def _fail(code: str, detail: str = "") -> None:
    raise ControlViolation(code, detail)


def validate_phase_key(phase_key: object) -> dict[str, str]:
    if not isinstance(phase_key, dict):
        _fail("PHASE_KEY_SCHEMA_MISMATCH", "phase_key is not an object")
    if set(phase_key) != set(PHASE_KEY_FIELDS):
        _fail("PHASE_KEY_SCHEMA_MISMATCH", "phase_key fields are not the closed six-field set")
    if any(not isinstance(phase_key[field], str) or not phase_key[field].strip()
           for field in PHASE_KEY_FIELDS):
        _fail("PHASE_KEY_SCHEMA_MISMATCH", "phase_key fields must be nonempty strings")
    return {field: phase_key[field] for field in PHASE_KEY_FIELDS}


def phase_keys_equal(left: object, right: object) -> bool:
    return validate_phase_key(left) == validate_phase_key(right)


def decide_phase_chat(
    runtime: dict[str, object], requested_phase_key: dict[str, str], *, event: str,
    phase_change_ratified: bool = False,
) -> str:
    """Return the closed P9 chat action without looking at goal number or time."""
    validate_runtime(runtime)
    active = runtime.get("active_proshka_phase")
    requested = validate_phase_key(requested_phase_key)
    if not isinstance(active, dict) or active.get("status") != "ACTIVE":
        return "OPEN_NEW_PHASE_CHAT"
    if not isinstance(active.get("conversation_id"), str) or not active["conversation_id"].strip():
        _fail("PROSHKA_CHAT_HANDLE_LOST", "active phase has no conversation handle")
    current = validate_phase_key(active.get("phase_key"))
    if event == "FATAL":
        return "CLOSE_PHASE_IMMEDIATELY"
    if current == requested:
        return "CONTINUE_EXISTING_CHAT"
    if not phase_change_ratified:
        _fail("PROSHKA_FRESH_CHAT_WITHOUT_PHASE_CHANGE", "phase-key change is not materialized")
    return "CLOSE_OLD_OPEN_NEW_PHASE_CHAT"


def _fingerprint(payload: dict[str, object], fields: tuple[str, ...]) -> str:
    normalized = {field: payload.get(field) for field in fields}
    raw = json.dumps(normalized, ensure_ascii=False, sort_keys=True,
                     separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def blocker_fingerprint(payload: dict[str, object]) -> str:
    """Normalize mathematical blocker identity while excluding cosmetic state."""
    return _fingerprint(payload, (
        "phase_key", "source_object", "terminal_consumer", "missing_implication",
        "missing_dependency_ids", "preserved_invariants", "quantifier_scope",
        "mathematical_domain",
    ))


def route_fingerprint(payload: dict[str, object]) -> str:
    """Normalize route identity so renaming cannot restart a killed experiment."""
    return _fingerprint(payload, (
        "source_object", "terminal_consumer", "normalized_theorem_shape",
        "assumption_set", "conclusion", "dependency_set", "preserved_invariants",
        "dropped_structures", "decisive_test_class",
    ))


def decide_exploration_entry(request: dict[str, object]) -> str:
    gate = request.get("entry_gate")
    if gate == "NAMED_THEOREM_SHAPE_FORK":
        candidates = request.get("candidates")
        if not isinstance(candidates, list) or not 2 <= len(candidates) <= 5:
            _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK", "requires two to five candidates")
        fingerprints: list[str] = []
        for candidate in candidates:
            if not isinstance(candidate, dict):
                _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK", "candidate is not an object")
            if candidate.get("reversible") is not True or not candidate.get("cheapest_killer"):
                _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK",
                      "every candidate must be reversible and have a cheapest killer")
            fingerprints.append(route_fingerprint(candidate))
        if len(set(fingerprints)) != len(fingerprints):
            _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK",
                  "candidate theorem shapes normalize to the same route")
        if request.get("same_phase_key") is not True or request.get("same_honesty_state") is not True:
            _fail("EXPLORATION_PHASE_KEY_SMUGGLE", "bounded exploration must remain in one phase")
        if request.get("source_locked_winner_found") is not False:
            _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK", "a source-locked winner already exists")
        if request.get("already_named_single_theorem_target") is not False:
            _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK", "one exact hard lemma is normal execution")
        return "ENTER_BOUNDED_EXPLORATION"
    if gate == "EXPLORATION_STALL":
        if request.get("same_blocker") is True and request.get("no_progress_streak", 0) >= 3:
            return "ENTER_BOUNDED_EXPLORATION"
        _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK", "soft-stall predicate is false")
    if gate == "LOOP_TRAP":
        if request.get("normalized_route_unchanged") is True and request.get("cosmetic_only") is True:
            return "ENTER_BOUNDED_EXPLORATION"
        _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK", "loop identity is not established")
    _fail("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK", "unknown entry gate")


def validate_progress_delta(delta: dict[str, object]) -> dict[str, object]:
    kind = delta.get("kind")
    if kind in NON_PROGRESS_KINDS:
        _fail("PROGRESS_DELTA_INVALID_COSMETIC", str(kind))
    required = {
        "delta_id", "exploration_id", "cycle_index", "kind", "scope", "verifier",
        "subject_id", "blocker_fingerprint_before", "blocker_fingerprint_after",
        "before", "after", "decision_effect", "evidence", "validated",
        "stall_counter_reset",
    }
    if not required.issubset(delta):
        _fail("PROGRESS_DELTA_SCHEMA_INVALID", "required fields are missing")
    if kind not in PROGRESS_DELTA_KINDS or delta.get("scope") not in DELTA_SCOPES:
        _fail("PROGRESS_DELTA_SCHEMA_INVALID", "kind or scope is outside the closed schema")
    verifier = delta.get("verifier")
    if verifier not in DELTA_VERIFIERS or delta.get("decision_effect") not in DECISION_EFFECTS:
        _fail("PROGRESS_DELTA_SCHEMA_INVALID", "verifier or decision effect is invalid")
    evidence = delta.get("evidence")
    if not isinstance(evidence, list) or not evidence:
        _fail("PROGRESS_DELTA_SCHEMA_INVALID", "evidence is required")
    for item in evidence:
        if not isinstance(item, dict) or not item.get("kind") or not item.get("ref"):
            _fail("PROGRESS_DELTA_SCHEMA_INVALID", "evidence items require kind and ref")
        sha = item.get("sha256")
        if sha is not None and (not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{64}", sha)):
            _fail("PROGRESS_DELTA_SCHEMA_INVALID", "evidence sha256 is invalid")
    may_reset = delta.get("validated") is True and verifier in RESET_VERIFIERS
    if bool(delta.get("stall_counter_reset")) != may_reset:
        _fail("STALL_COUNTER_RESET_INVALID", "reset does not match validated evidence")
    return {
        "result": "VALID_PROGRESS_DELTA",
        "stall_counter_reset": may_reset,
        "candidate_set_shrunk": (
            kind == "COUNTEREXAMPLE_FOUND"
            and delta.get("decision_effect") == "CANDIDATE_KILLED"
        ),
    }


def stall_decision(*, no_progress_streak: int, total_cycles: int,
                   active_reasoning_seconds: int, proshka_review_count: int) -> dict[str, object]:
    if min(no_progress_streak, total_cycles, active_reasoning_seconds, proshka_review_count) < 0:
        _fail("EXPLORATION_RUNTIME_MISSING", "negative counters")
    warnings = []
    if active_reasoning_seconds >= 8 * 60 * 60:
        warnings.append("EXPLORATION_TIME_BUDGET_WARNING")
    if total_cycles >= 12:
        state, call = "EXPLORATION_BUDGET_EXHAUSTED", False
    elif no_progress_streak >= 6:
        if proshka_review_count == 0:
            state, call = "HARD_STALL", True
        else:
            state, call = "TERMINAL_STALL", False
    elif no_progress_streak >= 3:
        state, call = "SOFT_STALL", False
    else:
        state, call = "LOCAL_EXPLORATION", False
    return {"state": state, "proshka_call": call, "warnings": warnings}


def validate_exploration_review(call: dict[str, object]) -> str:
    if call.get("fresh_chat") is True:
        _fail("EXPLORATION_CHAT_FANOUT", "review must reuse the phase chat")
    if call.get("full_context_reupload") is True:
        _fail("EXPLORATION_REVIEW_OUTSIDE_GATE", "review accepts a delta packet only")
    if call.get("state") not in {"REVIEW_READY", "HARD_STALL"}:
        _fail("EXPLORATION_REVIEW_OUTSIDE_GATE", "runtime state is not review-ready")
    if call.get("review_count_for_episode", 0) != 0 or call.get("review_count_for_phase_blocker", 0) != 0:
        _fail("EXPLORATION_REVIEW_DUPLICATE", "one review per episode and phase/blocker")
    if call.get("ordinary_goal_close_as_sole_trigger") is True:
        _fail("EXPLORATION_REVIEW_OUTSIDE_GATE", "ordinary goal close is never a call trigger")
    return "EXPLORATION_REVIEW_ALLOWED"


def validate_proshka_operative_class(value: str) -> str:
    if value == "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM":
        return value
    if re.fullmatch(r"(?:TRY|KILL|RUN)_[A-Za-z0-9_.-]+", value):
        return value
    if value.startswith("OWNER_AUTHORITY_REQUIRED_"):
        _fail("MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH", value)
    if value == "OWNER_FORK" or re.search(r"owner\s+(?:must\s+)?choose", value, re.I):
        _fail("PROSHKA_UNSTRUCTURED_OWNER_DEFERRAL", value)
    _fail("INVALID_OWNER_AUTHORITY_REQUIRED_CLASS", value)


def validate_two_keys(codex_key: dict[str, bool], proshka_key: dict[str, bool],
                      *, independent_source_check: bool = True) -> str:
    if proshka_key.get("source_object_not_surrogate") is not True:
        _fail("EXPLORATION_SURROGATE_COLLUSION", "source object is reconstructed or displaced")
    if not independent_source_check:
        _fail("EXPLORATION_TWO_KEY_NOT_INDEPENDENT", "Proshka only echoed Codex")
    if not all(codex_key.get(field) is True for field in ("locally_executable", "source_compatible")):
        return "RUN_CHEAPEST_BELIEF_CHANGING_TEST"
    if not all(proshka_key.get(field) is True for field in ("mathematically_honest", "non_surrogate")):
        return "RUN_CHEAPEST_BELIEF_CHANGING_TEST"
    return "DELEGATED_MATHEMATICAL_DECISION_COMPLETE"


def validate_phase_preservation(before: dict[str, str], after: dict[str, str],
                                *, claimed_same_phase: bool) -> str:
    equal = phase_keys_equal(before, after)
    if claimed_same_phase and not equal:
        _fail("EXPLORATION_PHASE_KEY_SMUGGLE", "a phase-key field changed")
    return "SAME_PHASE" if equal else "DELEGATED_PHASE_CHANGE_REQUIRED"


def ensure_no_alias_restart(previous_fingerprints: set[str], candidate: dict[str, object]) -> str:
    if route_fingerprint(candidate) in previous_fingerprints:
        _fail("EXPLORATION_ALIAS_RESTART", "normalized route was already closed")
    return "NEW_ROUTE_IDENTITY"


def validate_normal_loop_admission(admission: dict[str, object]) -> str:
    if admission.get("production_imports_experimental") is True:
        _fail("EXPERIMENTAL_CANONICAL_CONTAMINATION", "production imports experimental code")
    required_true = (
        "operative_result_present", "codex_key_pass", "proshka_key_pass",
        "phase_key_unchanged", "exact_source_object_named", "exact_consumer_named",
        "theorem_contract_frozen", "validated_progress_delta", "source_or_lean_gate_pass",
        "taint_axiom_gate_pass", "experimental_diff_scoped", "rollback_target_named",
    )
    if not all(admission.get(field) is True for field in required_true):
        _fail("NORMAL_LOOP_ADMISSION_EVIDENCE_MISSING", "third-gate evidence is incomplete")
    return "NORMAL_LOOP_ADMISSION"


def resolve_owner_boundary(*, decision: str, request_owner: bool,
                           operational_action: str | None = None) -> dict[str, object]:
    if decision == "PX_RH_CLAIM":
        if not request_owner:
            _fail("PX_RH_CLAIM_WITHOUT_OWNER_AUTHORIZATION", "PX/RH claim needs the Owner")
        return {"mathematical_state": "READY_FOR_OWNER",
                "operative_class": "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM"}
    if request_owner:
        _fail("MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH", decision)
    return {
        "mathematical_state": "DELEGATED_MATHEMATICAL_DECISION_REMAINS_SELECTED",
        "operational_state": "OPERATIONAL_ACTION_PENDING" if operational_action else None,
        "operational_action": operational_action,
        "owner_mathematical_action_required": False,
    }


def validate_runtime(runtime: object) -> dict[str, object]:
    if not isinstance(runtime, dict) or runtime.get("schema") != "q3_channel_runtime.v1":
        _fail("EXPLORATION_RUNTIME_MISSING", "runtime schema is missing or unsupported")
    required = {
        "control_status", "active_proshka_phase", "active_exploration",
        "last_exploration_close", "mathematical_authority_mode", "px_rh_claim_state",
        "operational_action_pending", "meter",
    }
    if not required.issubset(runtime):
        _fail("EXPLORATION_RUNTIME_MISSING", "runtime fields are missing")
    if runtime["control_status"] != "ACTIVE":
        _fail("EXPLORATION_CONTOUR_ORPHANED", "P9 runtime is not active")
    if runtime["mathematical_authority_mode"] != "CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM":
        _fail("MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH", "runtime authority mode drift")
    if runtime["px_rh_claim_state"] not in {"NOT_READY", "READY_FOR_OWNER", "AUTHORIZED", "DECLINED"}:
        _fail("EXPLORATION_RUNTIME_MISSING", "invalid PX/RH claim state")
    meter = runtime.get("meter")
    meter_fields = {
        "phases_opened", "fresh_chats_opened", "delegated_strategic_review_calls",
        "exploration_review_calls", "px_rh_claim_requests", "ordinary_goal_close_calls",
        "mathematical_owner_deferral_violations", "fanout_violations",
        "forced_rollovers",
    }
    if not isinstance(meter, dict) or not meter_fields.issubset(meter):
        _fail("EXPLORATION_RUNTIME_MISSING", "call meter is incomplete")
    if any(not isinstance(meter[field], int) or meter[field] < 0 for field in meter_fields):
        _fail("EXPLORATION_RUNTIME_MISSING", "call meter contains invalid counters")
    if meter["fresh_chats_opened"] > meter["phases_opened"] + meter["forced_rollovers"]:
        _fail("PROSHKA_PHASE_FANOUT_VIOLATION", "fresh chats exceed opened phases")
    if meter["mathematical_owner_deferral_violations"] != 0:
        _fail("MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH", "runtime records a deferral")
    if meter["fanout_violations"] != 0:
        _fail("PROSHKA_PHASE_FANOUT_VIOLATION", "runtime records chat fanout")
    if meter["ordinary_goal_close_calls"] != 0:
        _fail("EXPLORATION_REVIEW_OUTSIDE_GATE", "ordinary goal close called Proshka")
    phase = runtime.get("active_proshka_phase")
    if phase is not None:
        if not isinstance(phase, dict):
            _fail("EXPLORATION_RUNTIME_MISSING", "active Proshka phase is not an object")
        validate_phase_key(phase.get("phase_key"))
        if phase.get("status") == "ACTIVE" and not str(phase.get("conversation_id") or "").strip():
            _fail("PROSHKA_CHAT_HANDLE_LOST", "active phase has no conversation handle")
    active = runtime.get("active_exploration")
    if active is not None:
        if not isinstance(active, dict):
            _fail("EXPLORATION_RUNTIME_MISSING", "active exploration is not an object")
        validate_phase_key(active.get("phase_key"))
        if len(active.get("candidates", [])) > 5 or len(active.get("cycles", [])) > 12:
            _fail("EXPLORATION_BUDGET_EXHAUSTED", "runtime exceeds retention bounds")
        if active.get("proshka_review_count", 0) > 1:
            _fail("EXPLORATION_REVIEW_DUPLICATE", "runtime records more than one review")
    return runtime


def _read_runtime() -> dict[str, object]:
    if not CHANNEL_RUNTIME.is_file():
        _fail("EXPLORATION_RUNTIME_MISSING", str(CHANNEL_RUNTIME.relative_to(REPO)))
    try:
        return validate_runtime(json.loads(CHANNEL_RUNTIME.read_text(encoding="utf-8")))
    except json.JSONDecodeError as exc:
        _fail("EXPLORATION_RUNTIME_MISSING", f"invalid JSON: {exc}")


def record_delegated_review(
    runtime: dict[str, object], event: dict[str, object],
) -> tuple[dict[str, object], bool]:
    """Record one review boundary without hand-editing CHANNEL_RUNTIME.

    The caller supplies both the phase-local and global meter indices.  This
    makes missing or reordered events fail closed instead of silently
    normalizing whichever counter happened to be edited last.
    """
    validate_runtime(runtime)
    required = {
        "request_message_id", "conversation_id", "boundary_id",
        "adjudicated_pin", "phase_call_index", "meter_call_index",
    }
    if set(event) != required:
        _fail("EXPLORATION_RUNTIME_MISSING", "review event fields are incomplete")
    for field in ("request_message_id", "conversation_id", "boundary_id", "adjudicated_pin"):
        if not isinstance(event[field], str) or not str(event[field]).strip():
            _fail("EXPLORATION_RUNTIME_MISSING", f"review event {field} is empty")
    for field in ("phase_call_index", "meter_call_index"):
        if not isinstance(event[field], int) or int(event[field]) <= 0:
            _fail("EXPLORATION_RUNTIME_MISSING", f"review event {field} is invalid")

    updated = json.loads(json.dumps(runtime))
    ledger = updated.setdefault("recorded_review_events", [])
    if not isinstance(ledger, list):
        _fail("EXPLORATION_RUNTIME_MISSING", "recorded_review_events is not a list")
    request_id = str(event["request_message_id"])
    for existing in ledger:
        if not isinstance(existing, dict):
            _fail("EXPLORATION_RUNTIME_MISSING", "recorded review event is not an object")
        if existing.get("request_message_id") == request_id:
            if existing != event:
                _fail("EXPLORATION_REVIEW_DUPLICATE", request_id)
            return updated, False

    phase = updated.get("active_proshka_phase")
    meter = updated.get("meter")
    if not isinstance(phase, dict) or phase.get("status") != "ACTIVE":
        _fail("EXPLORATION_RUNTIME_MISSING", "no active Proshka phase")
    if event["conversation_id"] != phase.get("conversation_id"):
        _fail("EXPLORATION_CHAT_FANOUT", str(event["conversation_id"]))
    expected_phase = int(phase.get("proshka_calls", 0)) + 1
    expected_meter = int(meter.get("delegated_strategic_review_calls", 0)) + 1
    if event["phase_call_index"] != expected_phase or event["meter_call_index"] != expected_meter:
        _fail(
            "EXPLORATION_RUNTIME_MISSING",
            f"review meter drift: expected phase={expected_phase},meter={expected_meter}",
        )

    phase["proshka_calls"] = event["phase_call_index"]
    phase["last_boundary_id"] = event["boundary_id"]
    phase["last_adjudicated_pin"] = event["adjudicated_pin"]
    meter["delegated_strategic_review_calls"] = event["meter_call_index"]
    ledger.append(dict(event))
    validate_runtime(updated)
    return updated, True


def write_runtime_atomic(runtime: dict[str, object], path: Path = CHANNEL_RUNTIME) -> None:
    """Validate and atomically replace one canonical runtime JSON file."""
    validate_runtime(runtime)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(runtime, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, prefix=f".{path.name}.", delete=False,
    ) as handle:
        pending = Path(handle.name)
        handle.write(payload)
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(pending, path)
    finally:
        pending.unlink(missing_ok=True)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_behavior_registry(
    data: dict[str, object] | None = None, *, repo: Path = REPO,
) -> list[dict[str, str]]:
    if data is None:
        if not BEHAVIOR_REGISTRY.is_file():
            _fail("BEHAVIOR_CONTROL_MISSING", str(BEHAVIOR_REGISTRY))
        try:
            data = json.loads(BEHAVIOR_REGISTRY.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            _fail("BEHAVIOR_CONTROL_MISSING", f"invalid registry JSON: {exc}")
    if data.get("schema") != "q3_behavior_control_registry.v1":
        _fail("BEHAVIOR_CONTROL_MISSING", "unsupported registry schema")
    rows = data.get("controls")
    if not isinstance(rows, list):
        _fail("BEHAVIOR_CONTROL_MISSING", "controls is not a list")
    active = [row for row in rows if isinstance(row, dict) and row.get("status") == "ACTIVE"]
    expected = {"FABLE_MYTHOS", "PROSHKA", "CODEX_EXECUTOR"}
    for body in expected:
        matches = [row for row in active if row.get("body") == body]
        if not matches:
            _fail("BEHAVIOR_CONTROL_MISSING", body)
        if len(matches) != 1:
            _fail("BEHAVIOR_CONTROL_MULTIPLE_ACTIVE", body)
    if any(row.get("body") not in expected for row in active):
        _fail("BEHAVIOR_BODY_MULTIROLE", "unknown active body")
    paths = [str(row.get("path") or "") for row in active]
    if len(set(paths)) != len(paths):
        _fail("BEHAVIOR_BODY_MULTIROLE", "one file controls multiple bodies")
    validated: list[dict[str, str]] = []
    for row in sorted(active, key=lambda item: str(item["body"])):
        for field, code in (
            ("trigger_owner", "BEHAVIOR_TRIGGER_OWNER_MISSING"),
            ("existing_entry_gate", "BEHAVIOR_TRIGGER_OWNER_MISSING"),
            ("spine_wiring", "BEHAVIOR_SPINE_WIRING_MISSING"),
        ):
            if not isinstance(row.get(field), str) or not str(row[field]).strip():
                _fail(code, f"{row.get('body')}:{field}")
        rel = Path(str(row.get("path") or ""))
        if rel.is_absolute() or not (repo / rel).is_file():
            _fail("BEHAVIOR_CONTROL_MISSING", str(rel))
        mirror = row.get("mirror_path")
        if mirror:
            mirror_path = repo / str(mirror)
            if not mirror_path.is_file() or _sha256_file(repo / rel) != _sha256_file(mirror_path):
                _fail("BEHAVIOR_CONTROL_MISSING", f"mirror drift: {mirror}")
        validated.append({
            "body": str(row["body"]), "control_id": str(row["control_id"]),
            "path": rel.as_posix(), "sha256": _sha256_file(repo / rel),
            "trigger_owner": str(row["trigger_owner"]),
            "existing_entry_gate": str(row["existing_entry_gate"]),
            "spine_wiring": str(row["spine_wiring"]), "status": "ACTIVE",
        })
    validate_codex_bootstrap(repo=repo)
    addendum = repo / "docs/EXECUTOR_ARSENAL_ADDENDUM_2026-08-04.md"
    addendum_text = addendum.read_text(encoding="utf-8") if addendum.is_file() else ""
    if "STATUS: SUPERSEDED_BY_CODEX_CONTROL" not in addendum_text or "ACTIVE_POLICY: false" not in addendum_text:
        _fail("SUPERSEDED_CONTROL_STILL_ACTIVE", str(addendum.relative_to(repo)))
    return validated


def validate_thin_pointer_text(text: str, label: str = "pointer") -> str:
    forbidden_pointer_policy = (
        "fresh chat", "one living proshka", "phase_key:", "owner boundary",
        "ordinary goal close", "BOUNDED_EXPLORATION_PHASE",
    )
    if "CODEX_CONTROL.md" not in text:
        _fail("BEHAVIOR_CONTROL_MISSING", label)
    if any(token.lower() in text.lower() for token in forbidden_pointer_policy):
        _fail("THIN_POINTER_CONTAINS_POLICY", label)
    if len(text.splitlines()) > 24:
        _fail("THIN_POINTER_CONTAINS_POLICY", label)
    return "THIN_POINTER_VALID"


def validate_codex_bootstrap(*, repo: Path = REPO) -> str:
    """Validate only the bootstrap that Codex actually reads.

    Claude Code is an independent observer/administrator with its own CLAUDE.md
    policy. Its files are deliberately outside Codex startup validation.
    """
    pointer = repo / "AGENTS.md"
    text = pointer.read_text(encoding="utf-8") if pointer.is_file() else ""
    validate_thin_pointer_text(text, str(pointer.relative_to(repo)))
    return "CODEX_BOOTSTRAP_VALID"


def _validate_active_control() -> None:
    if not CONTROL.is_file():
        _fail("EXPLORATION_CONTOUR_ORPHANED", "docs/CODEX_CONTROL.md is missing")
    text = CONTROL.read_text(encoding="utf-8")
    required = (
        "CONTROL_ID: Q3_EXECUTOR_CONTROL",
        "STATUS: ACTIVE",
        "ROLE: CODEX_EXECUTOR",
        "BODIES:\n  - CODEX_MAC",
        "CLAUDE_CODE_INDEPENDENT_OBSERVER",
        "TRIGGER_OWNER: Codex",
        "behavior_control_and_bounded_exploration",
        "There is exactly one mathematical owner boundary",
        "PX_RH_CLAIM",
        "BOUNDED_EXPLORATION_PHASE",
        "MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH",
        "q3.lean.aristotle/aristotle_db/knowledge.db",
        "q3.lean.aristotle/aristotle_db/aristotle_proofs.db",
        "q3.lean.aristotle/aristotle_db/observability.db",
        "~/.codex/memories_1.sqlite",
        "PROJECT_DATABASES_MUST_NOT_BE_MERGED",
        "NATIVE_MEMORY_SEMANTIC_OVERRIDE",
        "OBSERVABILITY_SNAPSHOT_INVALID",
        "AUTOPSY: dropped=<AUTOPSY_TAG_V1>",
        "fresh_chats_opened <= phases_opened + forced_rollovers",
    )
    missing = [token for token in required if token not in text]
    if missing:
        _fail("EXPLORATION_CONTOUR_ORPHANED", f"missing control tokens: {missing}")
    try:
        control_header = text.split("```yaml", 1)[1].split("```", 1)[0]
    except IndexError:
        _fail("EXPLORATION_CONTOUR_ORPHANED", "missing control YAML header")
    if "CLAUDE.md" in control_header or "CLAUDE_CODE_LINUX" in control_header:
        _fail("BEHAVIOR_BODY_MULTIROLE", "Claude bootstrap leaked into Codex control")
    owner_classes = set(re.findall(
        r"^OWNER_AUTHORITY_REQUIRED_[A-Z0-9_]+$", text, re.MULTILINE))
    if owner_classes != {"OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM"}:
        _fail("INVALID_OWNER_AUTHORITY_REQUIRED_CLASS", repr(sorted(owner_classes)))
    if "OWNER_AUTHORITY_BYPASS" in text:
        _fail("MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH", "removed failure code remains")


def _live_cognitive_operator_tokens() -> list[str]:
    tokens: list[str] = []
    proshka_dir = REPO / "docs" / "routeB_bus" / "proshka"
    if not proshka_dir.is_dir():
        return tokens
    pattern = re.compile(
        r"^(?:cognitive_operator_used|COGNITIVE_OPERATOR):\s*([A-Z][A-Z0-9_]*)\s*$",
        re.MULTILINE,
    )
    for path in sorted(proshka_dir.glob("*.md")):
        tokens.extend(pattern.findall(path.read_text(encoding="utf-8", errors="replace")))
    return tokens


def validate_cognitive_operator_tokens(tokens: list[str], canonical: set[str]) -> None:
    unknown = sorted(set(tokens) - canonical)
    if unknown:
        _fail("COGNITIVE_OPERATOR_REGISTRY_UNAVAILABLE_OR_INVALID",
              f"unknown live cognitive operators: {unknown}")


def validate_cognitive_operator_registry(
    *, registry_path: Path = COGNITIVE_OPERATOR_REGISTRY,
    db_path: Path = KNOWLEDGE_DB,
    live_tokens: list[str] | None = None,
) -> dict[str, object]:
    try:
        payload = _kb.load_operator_registry(registry_path)
        canonical = {row["token"] for row in payload["canonical_enum"]["operators"]}
        legacy = {row["token"] for row in payload["legacy_enum"]["operators"]}
        expected_crosswalk = {
            (row["legacy_token"], row["relation"], row["canonical_token"], row["note"])
            for row in payload["crosswalk"]
        }
        if not db_path.is_file():
            raise ValueError(f"knowledge database missing: {db_path}")
        conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
        try:
            db_canonical = {row[0] for row in conn.execute(
                "SELECT token FROM cognitive_operator_registry WHERE vocabulary='PROSHKA_M2'")}
            db_legacy = {row[0] for row in conn.execute(
                "SELECT token FROM cognitive_operator_registry "
                "WHERE vocabulary='LEGACY_CONTROL_ACTION'")}
            db_crosswalk = set(conn.execute(
                "SELECT legacy_token,relation,canonical_token,note "
                "FROM cognitive_operator_crosswalk"))
        finally:
            conn.close()
        if db_canonical != canonical or db_legacy != legacy or db_crosswalk != expected_crosswalk:
            raise ValueError("operator registry file/database drift")
        validate_cognitive_operator_tokens(
            _live_cognitive_operator_tokens() if live_tokens is None else live_tokens,
            canonical,
        )
        return {"schema": payload["schema"], "canonical": 8, "legacy": 9, "crosswalk": 9}
    except (OSError, ValueError, sqlite3.DatabaseError, KeyError, TypeError) as exc:
        _fail("COGNITIVE_OPERATOR_REGISTRY_UNAVAILABLE_OR_INVALID", str(exc))


def validate_tool_manifest() -> dict[str, object]:
    """Validate the live tool contract and its byte-identical external mirror."""
    if not TOOL_MANIFEST.is_file() or not TOOL_MANIFEST_MIRROR.is_file():
        _fail("TOOL_MANIFEST_INVALID", "canonical tool manifest or mirror is missing")
    canonical = TOOL_MANIFEST.read_bytes()
    mirror = TOOL_MANIFEST_MIRROR.read_bytes()
    if canonical != mirror:
        _fail("TOOL_MANIFEST_INVALID", "canonical tool manifest and mirror differ")
    try:
        data = yaml.safe_load(canonical.decode("utf-8"))
    except (UnicodeDecodeError, yaml.YAMLError) as exc:
        _fail("TOOL_MANIFEST_INVALID", f"TOOLS.yaml cannot be parsed: {exc}")
    required_sections = {
        "schema",
        "meta",
        "tool_contract",
        "startup_contract",
        "memory_event_routes",
        "data_surfaces",
        "tool_families",
        "dynamic_queries",
        "tool_lifecycle",
        "known_hazards",
    }
    if not isinstance(data, dict) or data.get("schema") != "q3_tool_manifest.v2":
        _fail("TOOL_MANIFEST_INVALID", "unsupported or missing tool manifest schema")
    missing_sections = sorted(required_sections - set(data))
    if missing_sections:
        _fail("TOOL_MANIFEST_INVALID", f"missing sections: {', '.join(missing_sections)}")
    families = data.get("tool_families")
    if not isinstance(families, dict) or not families:
        _fail("TOOL_MANIFEST_INVALID", "tool_families must be a nonempty mapping")
    statuses = set(data.get("status_semantics", {}).get("values", []))
    modes = set(data.get("mode_semantics", {}).get("values", []))
    audiences = {"CODEX", "CLAUDE_CODE", "HUMAN"}
    required_fields = {
        "id", "status", "audience", "mode", "trigger", "writes",
        "approval", "authority", "records_to", "last_verified",
    }
    seen: set[str] = set()
    tool_count = 0
    writer_count = 0
    for family_id, family in families.items():
        if not isinstance(family, dict) or not isinstance(family.get("tools"), list):
            _fail("TOOL_MANIFEST_INVALID", f"family {family_id} has no tools list")
        for tool in family["tools"]:
            tool_count += 1
            if not isinstance(tool, dict):
                _fail("TOOL_MANIFEST_INVALID", f"family {family_id} contains a non-mapping tool")
            missing = sorted(required_fields - set(tool))
            if missing:
                _fail(
                    "TOOL_MANIFEST_INVALID",
                    f"tool {tool.get('id', '<missing>')} lacks: {', '.join(missing)}",
                )
            tool_id = str(tool["id"])
            if tool_id in seen:
                _fail("TOOL_MANIFEST_INVALID", f"duplicate tool id: {tool_id}")
            seen.add(tool_id)
            if tool["status"] not in statuses or tool["mode"] not in modes:
                _fail("TOOL_MANIFEST_INVALID", f"tool {tool_id} has unknown status or mode")
            declared_audience = tool["audience"]
            if (
                not isinstance(declared_audience, list)
                or not declared_audience
                or any(item not in audiences for item in declared_audience)
            ):
                _fail("TOOL_MANIFEST_INVALID", f"tool {tool_id} has invalid audience")
            if "path" not in tool and "paths" not in tool:
                _fail("TOOL_MANIFEST_INVALID", f"tool {tool_id} has no path or paths")
            if not any(key in tool for key in ("invoke", "read_invoke", "write_invoke")):
                _fail("TOOL_MANIFEST_INVALID", f"tool {tool_id} has no invocation")
            writes = tool["writes"]
            if not isinstance(writes, bool):
                _fail("TOOL_MANIFEST_INVALID", f"tool {tool_id} writes must be boolean")
            if tool["mode"] == "READ_ONLY" and writes:
                _fail("TOOL_MANIFEST_INVALID", f"read-only tool {tool_id} declares writes")
            if writes and tool["approval"] == "NONE":
                _fail("TOOL_MANIFEST_INVALID", f"writer {tool_id} has no approval gate")
            writer_count += int(writes)
    for event_id, route in data["memory_event_routes"].items():
        if not isinstance(route, dict):
            _fail("TOOL_MANIFEST_INVALID", f"memory route {event_id} is not a mapping")
        run_ids = route.get("run", [])
        if not isinstance(run_ids, list) or any(item not in seen for item in run_ids):
            _fail("TOOL_MANIFEST_INVALID", f"memory route {event_id} names an unknown tool")
    return {
        "schema": data["schema"],
        "family_count": len(families),
        "tool_count": tool_count,
        "writer_count": writer_count,
        "sha256": hashlib.sha256(canonical).hexdigest(),
    }


def validate_p9a() -> dict[str, object]:
    _validate_active_control()
    controls = validate_behavior_registry()
    runtime = _read_runtime()
    cognitive_operators = validate_cognitive_operator_registry()
    tool_manifest = validate_tool_manifest()
    return {
        "control": "ACTIVE",
        "authority": runtime["mathematical_authority_mode"],
        "runtime": "VALID",
        "behavior_controls": controls,
        "cognitive_operators": cognitive_operators,
        "tool_manifest": tool_manifest,
    }

SOURCES = {
    "failure_atlas": REPO / "q3.lean.aristotle/ACTIVE/pipeline/FAILURE_ATLAS.json",
    "failed_strategies": REPO / "q3.lean.aristotle/ACTIVE/FAILED_STRATEGIES.yaml",
    "errors_destroyer": REPO / "q3.lean.aristotle/docs/ERRORS_DESTROYER.md",
    "s5_failure_atlas": REPO / "docs/trackB/S5_FAILURE_ATLAS.md",
    "obstruction_atlas": REPO / "Q3_OBSTRUCTION_ATLAS.md",
    "trick_atlas": REPO / "docs/RH_TRICK_ATLAS.md",
    "insights": REPO / "q3.lean.aristotle/docs/INSIGHTS.md",
    "progress_log": REPO / "docs/Progress_Log.md",
    "genealogy": REPO / "docs/GENEALOGY.md",
    "recording_rules": REPO / "docs/RECORDING_RULES.md",
    "tool_manifest": TOOL_MANIFEST,
    "cognitive_governor": REPO / "q3.lean.aristotle/ACTIVE/COGNITIVE_GOVERNOR.md",
    "bus_dir": REPO / "docs/routeB_bus",
}


def _git_date(path: Path) -> str:
    try:
        out = subprocess.run(
            ["git", "log", "-1", "--format=%cs", "--", str(path.relative_to(REPO))],
            cwd=REPO, capture_output=True, text=True, timeout=10,
        ).stdout.strip()
        return out or "untracked"
    except Exception:
        return "unknown"


def _freshness_table() -> list[str]:
    lines = ["| Source | Last commit |", "|---|---|"]
    for key, path in SOURCES.items():
        if key == "bus_dir":
            continue
        date = _git_date(path) if path.exists() else "MISSING"
        lines.append(f"| `{path.relative_to(REPO)}` | {date} |")
    return lines


def _kills_from_db() -> list[str]:
    """All kills from knowledge.db, grouped by unit type.

    Replaces the former `_object_kills()` (JSON) and `_strategy_kills()` (hand-rolled YAML
    regex). Those two rendered 13 of the family's 38 records; the walls of
    Q3_OBSTRUCTION_ATLAS.md and the S5 lift were imported in SOURCES but never displayed.
    """
    if not KNOWLEDGE_DB.exists():
        return ["(knowledge.db missing — run ./orchestrator/kb.py init && "
                "./orchestrator/kb_migrate_kills.py)"]
    conn = sqlite3.connect(f"file:{KNOWLEDGE_DB}?mode=ro", uri=True)
    conn.row_factory = sqlite3.Row
    lines: list[str] = []
    for (unit,) in conn.execute(
            "SELECT DISTINCT unit_type FROM kill ORDER BY unit_type"):
        rows = conn.execute(
            "SELECT id, subject, status, replacement, rollback_target, stop_code "
            "FROM kill WHERE unit_type=? ORDER BY id", (unit,)).fetchall()
        lines += [f"", f"**{unit}** ({len(rows)})", "",
                  "| id | subject | status | next / rollback |", "|---|---|---|---|"]
        for r in rows:
            nxt = r["replacement"] or r["rollback_target"] or ""
            nxt = (nxt[:87] + "...") if len(nxt) > 90 else nxt
            subj = (r["subject"] or "")[:70].replace("|", "\\|")
            lines.append(f"| {r['id']} | {subj} | {r['status']} | {nxt.replace('|', chr(92)+'|')} |")
    n = conn.execute("SELECT COUNT(*) FROM kill").fetchone()[0]
    a = conn.execute("SELECT COUNT(*) FROM kill_alias").fetchone()[0]
    conn.close()
    lines += ["", f"_{n} records, {a} cross-file aliases. Query: "
                  "`./orchestrator/kb.py search <term>`._"]
    return lines


def _bus_iteration_blocks() -> list[str]:
    """Harvest M3 strategy-memory YAML blocks from bus verdicts."""
    bus = SOURCES["bus_dir"]
    if not bus.is_dir():
        return ["(bus dir missing)"]
    rows: list[tuple[str, str, str, str]] = []
    for md in sorted(bus.glob("*.md")):
        text = md.read_text(encoding="utf-8", errors="replace")
        for m in re.finditer(r"^iteration:\n((?:[ \t]+\S.*\n?)+)", text, re.M):
            block = m.group(1)

            def field(name: str) -> str:
                fm = re.search(rf"{name}:\s*(.+)", block)
                return fm.group(1).strip() if fm else ""

            row = (md.name, field("target"), field("forbidden_future_move"),
                   field("new_gap_name"))
            if any("<" in v for v in row[1:]):  # skip prompt-template blocks
                continue
            rows.append(row)
    if not rows:
        return ["(no iteration blocks found on the bus)"]
    lines = ["| verdict file | target | forbidden_future_move | new_gap |",
             "|---|---|---|---|"]
    for f, t, fb, g in rows:
        lines.append(f"| {f} | {t} | {fb} | {g} |")
    return lines


def _process_errors() -> list[str]:
    path = SOURCES["errors_destroyer"]
    if not path.exists():
        return ["(ERRORS_DESTROYER.md missing)"]
    heads = re.findall(r"^## (Ошибка.*)$", path.read_text(encoding="utf-8"), re.M)
    return [f"- {h}" for h in heads] or ["(no recorded errors)"]


def _trick_cards() -> list[str]:
    path = SOURCES["trick_atlas"]
    if not path.exists():
        return ["(RH_TRICK_ATLAS.md missing)"]
    text = path.read_text(encoding="utf-8")
    lines = []
    for m in re.finditer(r"^##+ (\d+\..+)$", text, re.M):  # numbered cards only
        title = m.group(1).strip()
        tail = text[m.end():m.end() + 400]
        sm = re.search(r"`?Status`?\s*[:*]*\s*`?(applied|hot candidate|candidate|parked|awaiting-research)`?", tail)
        if sm:
            lines.append(f"- [{sm.group(1)}] {title}")
    return lines or ["(no cards with Status found)"]


def _recent_insights(n: int = 8) -> list[str]:
    path = SOURCES["insights"]
    if not path.exists():
        return ["(INSIGHTS.md missing)"]
    heads = []
    with path.open(encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("## ") and not line.startswith("## Навигация"):
                heads.append(line[3:].strip())
            if len(heads) >= n:
                break
    return [f"- {h}" for h in heads]


def _recent_branch_decisions(n: int = 6) -> list[str]:
    path = SOURCES["progress_log"]
    if not path.exists():
        return ["(Progress_Log.md missing)"]
    heads = re.findall(
        r"^##\s+(\d{4}-\d{2}-\d{2}(?:\s*→\s*\d{4}-\d{2}-\d{2})?\s+—\s+.+)$",
        path.read_text(encoding="utf-8"),
        re.MULTILINE,
    )
    if not heads:
        return ["(no branch decisions found)"]

    selected = heads[:n]
    manifest_anchor = next(
        (head for head in heads if "манифест соединён с обратным поиском" in head),
        None,
    )
    if manifest_anchor is not None and manifest_anchor not in selected:
        selected.append(manifest_anchor)
    return [f"- {head}" for head in selected]


def _latest_exploration_closeouts(n: int = 5) -> list[sqlite3.Row]:
    if not KNOWLEDGE_DB.exists():
        return []
    conn = sqlite3.connect(f"file:{KNOWLEDGE_DB}?mode=ro", uri=True)
    conn.row_factory = sqlite3.Row
    try:
        return conn.execute(
            "SELECT id, date, state, target, validation, artifact_sha, boundary, next_target "
            "FROM journal_entry WHERE kind='exploration_close' "
            "ORDER BY COALESCE(date, '') DESC, id DESC LIMIT ?", (n,),
        ).fetchall()
    finally:
        conn.close()


def _bounded_exploration_view(runtime: dict[str, object]) -> list[str]:
    lines = [
        f"- control status: `{runtime['control_status']}`",
        f"- mathematical authority: `{runtime['mathematical_authority_mode']}`",
        f"- PX/RH claim state: `{runtime['px_rh_claim_state']}`",
    ]
    active = runtime.get("active_exploration")
    if not isinstance(active, dict):
        lines.append("- active exploration: `NONE`")
    else:
        candidates = active.get("candidates", [])
        lines.extend([
            f"- active exploration: `{active.get('exploration_id', 'MISSING')}`",
            f"- entry gate: `{active.get('entry_gate', 'MISSING')}`",
            f"- blocker: `{active.get('blocker_id', 'MISSING')}`",
            f"- candidates: `{len(candidates) if isinstance(candidates, list) else 'INVALID'}`",
            f"- cycles / no-progress: `{active.get('total_cycles', 0)}` / "
            f"`{active.get('no_progress_streak', 0)}`",
            f"- review used: `{bool(active.get('proshka_review_count', 0))}`",
            f"- selected route: `{active.get('selected_route_id') or 'NONE'}`",
            f"- rollback: `{active.get('rollback_target') or 'NONE'}`",
            f"- latest validated delta: "
            f"`{(active.get('last_progress_delta') or {}).get('delta_id', 'NONE') if isinstance(active.get('last_progress_delta'), dict) else 'NONE'}`",
        ])
    pending = runtime.get("operational_action_pending")
    lines.append(f"- operational action pending: `{pending or 'NONE'}`")
    meter = runtime["meter"]
    lines.extend([
        "",
        "| Meter | Count |",
        "|---|---:|",
        *[f"| `{key}` | {meter[key]} |" for key in sorted(meter)],
        "",
        "### Latest durable exploration closeouts",
        "",
    ])
    rows = _latest_exploration_closeouts()
    if not rows:
        lines.append("- none")
    else:
        lines += [
            "| id | date | state | target | boundary | next |",
            "|---|---|---|---|---|---|",
        ]
        for row in rows:
            cells = [
                row["id"], row["date"] or "", row["state"] or "",
                row["target"] or "", row["boundary"] or "", row["next_target"] or "",
            ]
            cells = [str(cell).replace("|", "\\|").replace("\n", " ")[:100]
                     for cell in cells]
            lines.append("| " + " | ".join(cells) + " |")
    return lines


def _knowledge_counts() -> dict[str, int | str]:
    if not KNOWLEDGE_DB.is_file():
        return {"status": "MISSING"}
    conn = sqlite3.connect(f"file:{KNOWLEDGE_DB}?mode=ro", uri=True)
    try:
        result: dict[str, int | str] = {"status": "READY"}
        for table in ("kill", "move", "journal_entry", "dossier", "postmortem", "excluded_source"):
            try:
                result[table] = int(conn.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0])
            except sqlite3.DatabaseError:
                result[table] = -1
        return result
    finally:
        conn.close()


def _load_json(path: Path, default: dict[str, object]) -> dict[str, object]:
    if not path.is_file():
        return default
    data = json.loads(path.read_text(encoding="utf-8"))
    return data if isinstance(data, dict) else default


def build_meta_corpus() -> dict[str, object]:
    """Small derived registry of corpora; never a fourth semantic database."""
    surfaces = [
        {
            "id": "SEMANTIC_PROJECT_MEMORY", "kind": "sqlite",
            "path": "q3.lean.aristotle/aristotle_db/knowledge.db",
            "authority": "CANONICAL_PROJECT_SEMANTIC_MEMORY",
        },
        {
            "id": "PROOF_ARTIFACT_REGISTRY", "kind": "sqlite",
            "path": "q3.lean.aristotle/aristotle_db/aristotle_proofs.db",
            "authority": "METADATA_NOT_LEAN_TRUTH",
        },
        {
            "id": "OBSERVABILITY_PROJECTION", "kind": "sqlite",
            "path": "q3.lean.aristotle/aristotle_db/observability.db",
            "authority": "DERIVED_NONCANONICAL_OBSERVABILITY",
        },
        {
            "id": "Q3_DOCS_SEMANTIC_INDEX", "kind": "qmd_collection",
            "path": "qmd://q3_docs/", "authority": "RETRIEVAL_ONLY",
        },
        {
            "id": "BRANCH_RATIONALE_JOURNAL", "kind": "reviewed_markdown",
            "path": "docs/Progress_Log.md",
            "authority": "CANONICAL_BRANCH_RATIONALE",
        },
        {
            "id": "PROJECT_GENEALOGY", "kind": "reviewed_markdown",
            "path": "docs/GENEALOGY.md",
            "authority": "REVIEWED_HISTORICAL_TOPOLOGY",
        },
        {
            "id": "TOOL_MANIFEST", "kind": "yaml_manifest",
            "path": "docs/cartographer/TOOLS.yaml",
            "authority": "CANONICAL_OPERATIONAL_TOOL_CATALOGUE",
        },
        {
            "id": "LITREVIEW_CORPUS", "kind": "documents_and_bibliography",
            "path": "docs/routeB_bus/litreview",
            "authority": "SOURCE_EVIDENCE_ONLY",
        },
        {
            "id": "AUTOPSY_WALL_MAP", "kind": "derived_json",
            "path": "q3.lean.aristotle/ACTIVE/graphs/AUTOPSY_MAP.json",
            "authority": "DERIVED_NONCANONICAL_OBSERVABILITY",
        },
    ]
    return {
        "schema": "q3_meta_corpus.v1",
        "authority": "DERIVED_REGISTRY_NOT_NEW_TRUTH_SOURCE",
        "separation_rule": "PROJECT_DATABASES_MUST_NOT_BE_MERGED",
        "surfaces": surfaces,
    }


def validate_artifact_identities() -> list[dict[str, object]]:
    data = _load_json(ARTIFACT_REGISTRY, {})
    if data.get("schema") != "q3_artifact_identity_registry.v1":
        _fail("ARTIFACT_IDENTITY_DRIFT", "registry missing or schema invalid")
    artifacts = data.get("artifacts")
    if not isinstance(artifacts, list) or not artifacts:
        _fail("ARTIFACT_IDENTITY_DRIFT", "artifact list empty")
    for row in artifacts:
        if not isinstance(row, dict) or not row.get("path") or not row.get("sha256"):
            _fail("ARTIFACT_IDENTITY_DRIFT", "artifact row incomplete")
        path = REPO / str(row["path"])
        if not path.is_file() or _sha256_file(path) != row["sha256"]:
            _fail("ARTIFACT_IDENTITY_DRIFT", str(row.get("id")))
        mirror = row.get("mirror_path")
        if mirror:
            mirror_path = REPO / str(mirror)
            if not mirror_path.is_file() or _sha256_file(mirror_path) != row["sha256"]:
                _fail("ARTIFACT_IDENTITY_DRIFT", f"mirror:{row.get('id')}")
    return artifacts


def validate_semantic_index() -> dict[str, object]:
    data = _load_json(SEMANTIC_INDEX_STATUS, {})
    plants = data.get("plants")
    if (
        data.get("schema") != "q3_semantic_index_status.v1"
        or data.get("status") != "PASS"
        or not isinstance(plants, list)
        or not plants
        or any(not isinstance(row, dict) or row.get("status") != "PASS" for row in plants)
    ):
        _fail("SEMANTIC_INDEX_PLANT_FAILED", "q3_docs status or mandatory plants are not PASS")
    return data


def build_state() -> dict[str, object]:
    validation = validate_p9a()
    runtime = _read_runtime()
    if OBSERVABILITY_DB.is_file():
        observability = _observability.summary_data(OBSERVABILITY_DB)
    else:
        observability = {"status": "MISSING"}
    autopsy = _load_json(AUTOPSY_MAP, {
        "schema": "q3_autopsy_map.v1", "authority": "DERIVED_NONCANONICAL_OBSERVABILITY",
        "events": [], "walls": [], "namewatch_candidates": [],
    })
    semantic = _load_json(SEMANTIC_INDEX_STATUS, {
        "schema": "q3_semantic_index_status.v1", "status": "NOT_VALIDATED",
        "plants": [],
    })
    return {
        "schema": "q3_spine_state.v1",
        "authority": "DERIVED_NONCANONICAL_OPERATIONAL_VIEW",
        "source_commit": subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=REPO, capture_output=True, text=True,
        ).stdout.strip() or "UNKNOWN",
        "behavior_controls": validation["behavior_controls"],
        "tool_manifest": validation["tool_manifest"],
        "artifact_identities": validate_artifact_identities(),
        "runtime": runtime,
        "knowledge": _knowledge_counts(),
        "observability": observability,
        "autopsy": {
            "schema": autopsy.get("schema"),
            "authority": autopsy.get("authority"),
            "event_count": len(autopsy.get("events", [])),
            "structured_count": sum(
                1 for event in autopsy.get("events", [])
                if isinstance(event, dict) and event.get("structured")
            ),
            "walls": autopsy.get("walls", []),
            "namewatch_candidates": autopsy.get("namewatch_candidates", []),
        },
        "semantic_index": semantic,
        "meta_corpus": build_meta_corpus(),
        "invariants": {
            "single_owner_boundary": "PX_RH_CLAIM",
            "ordinary_goal_close_proshka_calls": 0,
            "database_separation": "PROJECT_DATABASES_MUST_NOT_BE_MERGED",
            "route_honesty": "CHALLENGER_NOT_RH",
            "bus_010": "VOID",
        },
    }


def _behavior_control_view(controls: list[dict[str, str]]) -> list[str]:
    lines = [
        "| Body | Active control | Trigger owner | Entry gate | Spine wiring |",
        "|---|---|---|---|---|",
    ]
    for control in controls:
        lines.append(
            f"| `{control['body']}` | `{control['path']}` | "
            f"{control['trigger_owner']} | `{control['existing_entry_gate']}` | "
            f"`{control['spine_wiring']}` |"
        )
    return lines


def _autopsy_view(state: dict[str, object]) -> list[str]:
    autopsy = state["autopsy"]
    assert isinstance(autopsy, dict)
    walls = autopsy.get("walls", [])
    flags = autopsy.get("namewatch_candidates", [])
    lines = [
        f"- events / structured: `{autopsy['event_count']}` / `{autopsy['structured_count']}`",
        f"- walls / NEW_FLAG candidates: `{len(walls)}` / `{len(flags)}`",
        "- legacy free text remains visible but namewatch-ineligible; auto-promotion is forbidden.",
    ]
    for flag in flags:
        if isinstance(flag, dict):
            lines.append(
                f"- `[NEW_FLAG?] {flag.get('id')}`: `{flag.get('tag')}` / "
                f"`{flag.get('shape')}`; status `{flag.get('status')}`."
            )
    return lines


def _artifact_identity_view(state: dict[str, object]) -> list[str]:
    artifacts = state.get("artifact_identities", [])
    lines = ["| Artifact | Selected path | SHA-256 | Status |", "|---|---|---|---|"]
    for row in artifacts:
        if isinstance(row, dict):
            lines.append(
                f"| `{row.get('id')}` | `{row.get('path')}` | "
                f"`{str(row.get('sha256'))[:16]}…` | `{row.get('status')}` |"
            )
    return lines


def _semantic_index_view(state: dict[str, object]) -> list[str]:
    semantic = state.get("semantic_index", {})
    if not isinstance(semantic, dict):
        return ["- status: `INVALID`"]
    lines = [
        f"- collection: `{semantic.get('collection', 'q3_docs')}`",
        f"- mode / status: `{semantic.get('mode', 'unknown')}` / `{semantic.get('status', 'NOT_VALIDATED')}`",
    ]
    for plant in semantic.get("plants", []):
        if isinstance(plant, dict):
            lines.append(
                f"- `{plant.get('id')}` query `{plant.get('query')}`: "
                f"`{plant.get('status')}`, results `{plant.get('result_count')}`."
            )
    return lines


def _staleness_warnings() -> list[str]:
    warns = []
    runtime = _read_runtime()
    phase = runtime.get("active_proshka_phase")
    if isinstance(phase, dict) and phase.get("status") == "ACTIVE":
        opened_at = phase.get("opened_at")
        try:
            opened = _dt.datetime.fromisoformat(str(opened_at))
            now = _dt.datetime.now(tz=opened.tzinfo)
            age_hours = max(0, int((now - opened).total_seconds() // 3600))
            if age_hours >= 24:
                warns.append(
                    f"- CHANNEL_RUNTIME active phase record is {age_hours} hours old "
                    f"({opened_at}); revalidate the existing chat handle and six-field "
                    "phase key. Age alone never authorizes a fresh chat."
                )
        except (TypeError, ValueError):
            warns.append(
                "- CHANNEL_RUNTIME active phase has no parseable opened_at; revalidate "
                "the existing chat handle and phase key without opening a fresh chat."
            )
    if OBSERVABILITY_DB.is_file():
        data = _observability.summary_data(OBSERVABILITY_DB)
        stale = [row["source_id"] for row in data["sources"] if row["stale"]]
        if stale:
            warns.append(
                f"- observability sources stale: {len(stale)}/{len(data['sources'])} "
                f"({', '.join(stale)}) — refresh upstream generators, then rebuild "
                "observability.db."
            )
        degraded = [
            f"{row['source_id']}:{row['health_status']}"
            for row in data["sources"] if row["health_status"] != "READY"
        ]
        if degraded:
            warns.append(
                "- observability source health degraded: " + ", ".join(degraded) +
                " — this is not a green sensor state."
            )
    else:
        warns.append("- observability.db is missing — rebuild before trusting sensor state.")
    gov = SOURCES["cognitive_governor"]
    if gov.exists():
        text = gov.read_text(encoding="utf-8")
        dm = re.search(r"date:\s*(\d{4}-\d{2}-\d{2})", text)
        if dm:
            age = (_dt.date.today() - _dt.date.fromisoformat(dm.group(1))).days
            if age > 14:
                warns.append(
                    f"- COGNITIVE_GOVERNOR.md is {age} days old "
                    f"({dm.group(1)}) and references a possibly retired front — regenerate."
                )
    fs = SOURCES["failed_strategies"]
    if fs.exists():
        um = re.search(r"updated:\s*(\d{4}-\d{2}-\d{2})", fs.read_text(encoding="utf-8"))
        if um:
            age = (_dt.date.today() - _dt.date.fromisoformat(um.group(1))).days
            if age > 14:
                warns.append(
                    f"- FAILED_STRATEGIES.yaml last updated {um.group(1)} "
                    f"({age} days) — bus iteration blocks after that date are NOT merged."
                )
    return warns or ["- none detected"]


def build(state: dict[str, object] | None = None) -> str:
    state = state or build_state()
    validation = validate_p9a()
    runtime = _read_runtime()
    parts = [
        "# SPINE VIEW — unified negative-knowledge / memory ledger",
        "",
        "Generated deterministically by `orchestrator/spine.py`. DO NOT EDIT.",
        "Adapter over existing sources; sources stay canonical, this file is a read view.",
        "",
        "## Behavior controls (P9 active)",
        *_behavior_control_view(validation["behavior_controls"]),
        "",
        "## Operational tool manifest",
        f"- schema / mirror: `{validation['tool_manifest']['schema']}` / `BYTE_IDENTICAL`",
        f"- families / tools / writers: `{validation['tool_manifest']['family_count']}` / "
        f"`{validation['tool_manifest']['tool_count']}` / "
        f"`{validation['tool_manifest']['writer_count']}`",
        f"- SHA-256: `{validation['tool_manifest']['sha256']}`",
        "",
        "## Phase chat and bounded exploration",
        f"- validation: `{validation['runtime']}`",
        *_bounded_exploration_view(runtime),
        "",
        "## AUTOPSY wall map and namewatch",
        *_autopsy_view(state),
        "",
        "## Canonical artifact identities",
        *_artifact_identity_view(state),
        "",
        "## Semantic index plants",
        *_semantic_index_view(state),
        "",
        "## Meta-corpus registry",
        f"- derived surfaces: `{len(state['meta_corpus']['surfaces'])}`; authority: "
        f"`{state['meta_corpus']['authority']}`.",
        "",
        "## Observability snapshot (derived, non-authoritative)",
        *_observability.summary_lines(OBSERVABILITY_DB),
        "",
        "## Staleness warnings",
        *_staleness_warnings(),
        "",
        "## Source freshness",
        *_freshness_table(),
        "",
        "## 1-2. Kills (knowledge.db: routes, objects, strategies, walls, criteria)",
        *_kills_from_db(),
        "",
        "## 3. Bus strategy memory (M3 iteration blocks in verdicts)",
        *_bus_iteration_blocks(),
        "",
        "## 4. Process errors (ERRORS_DESTROYER)",
        *_process_errors(),
        "",
        "## 5. Trick arsenal index (RH_TRICK_ATLAS, K9)",
        *_trick_cards(),
        "",
        "## 6. Recent branch decisions (Progress_Log.md)",
        *_recent_branch_decisions(),
        "",
        "## 7. Recent insights (INSIGHTS.md head)",
        *_recent_insights(),
        "",
    ]
    return "\n".join(parts) + "\n"


def write_outputs() -> dict[str, object]:
    state = build_state()
    view = build(state)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    STATE_OUT.write_text(
        json.dumps(state, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    META_CORPUS_OUT.write_text(
        json.dumps(state["meta_corpus"], ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    OUT.write_text(view, encoding="utf-8")
    return state


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--stdout", action="store_true",
        help="print instead of writing Spine outputs; read-only unless combined with --refresh",
    )
    ap.add_argument("--strict", action="store_true",
                    help="add semantic-index validation and a receipt; base P9 validation is unconditional")
    ap.add_argument("--refresh", action="store_true",
                    help="write the complete sensor/index refresh before validation and Spine rendering")
    ap.add_argument("--reason", default="manual",
                    help="audit label only; not written into the deterministic view")
    ap.add_argument(
        "--record-review", action="append", default=[], metavar="JSON",
        help="atomically record one delegated-review event; repeat for ordered backfill",
    )
    args = ap.parse_args()
    try:
        if args.record_review:
            if args.stdout or args.strict or args.refresh:
                _fail("EXPLORATION_RUNTIME_MISSING", "record-review cannot be combined with render flags")
            runtime = _read_runtime()
            changed = 0
            for raw_event in args.record_review:
                try:
                    event = json.loads(raw_event)
                except json.JSONDecodeError as exc:
                    _fail("EXPLORATION_RUNTIME_MISSING", f"invalid review JSON: {exc}")
                if not isinstance(event, dict):
                    _fail("EXPLORATION_RUNTIME_MISSING", "review event is not an object")
                runtime, did_change = record_delegated_review(runtime, event)
                changed += int(did_change)
            if changed:
                write_runtime_atomic(runtime)
            print(f"CHANNEL_RUNTIME_REVIEW_EVENTS_RECORDED={changed}")
            return 0
        if args.refresh:
            if args.reason == "goal-close":
                migrate_progress_log = subprocess.run(
                    [sys.executable, "orchestrator/kb_migrate_progress_log.py"],
                    cwd=REPO, text=True,
                )
                if migrate_progress_log.returncode != 0:
                    _fail("BRANCH_DECISION_MIGRATION_FAILED",
                          "kb_migrate_progress_log.py failed at goal close")
                migrate_verdicts = subprocess.run(
                    [sys.executable, "orchestrator/kb_migrate_verdicts.py"],
                    cwd=REPO, text=True,
                )
                if migrate_verdicts.returncode != 0:
                    _fail("VERDICT_KNOWLEDGE_MIGRATION_FAILED",
                          "kb_migrate_verdicts.py failed at goal close")
            try:
                from orchestrator import sensors as _sensors
            except ModuleNotFoundError:
                import sensors as _sensors
            _sensors.refresh(dry_run=False)
            refresh_index = subprocess.run(
                [sys.executable, "q3.lean.aristotle/scripts/refresh_q3_docs.py"],
                cwd=REPO, text=True,
            )
            if refresh_index.returncode != 0:
                _fail("SEMANTIC_INDEX_PLANT_FAILED", "q3_docs refresh failed")
            plant_index = subprocess.run(
                [sys.executable, "scripts/semantic_index_plants.py"],
                cwd=REPO, text=True,
            )
            if plant_index.returncode != 0:
                _fail("SEMANTIC_INDEX_PLANT_FAILED", "semantic-index plants failed")
        validation = validate_p9a()
        if args.strict and args.reason != "sensor-refresh":
            validate_semantic_index()
        state = build_state()
        view = build(state)
    except ControlViolation as exc:
        print(exc, file=sys.stderr)
        return 2
    if args.stdout:
        sys.stdout.write(view)
    else:
        write_outputs()
        print(f"wrote {STATE_OUT}, {OUT}, {META_CORPUS_OUT}")
    if args.strict:
        print(
            f"P9_STRICT_PASS reason={args.reason} base_control=PASS "
            f"semantic_index=PASS tool_manifest=PASS authority={validation['authority']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
