"""One source-locked registration repair; no dispatch or proof admission."""
from __future__ import annotations

import datetime as dt
import hashlib
import json
from pathlib import Path

from orchestrator import spine

TRANSITION = "GOAL058_FOKAS_EXISTING_CHAT_20260923"
PREIMAGE = "f7bb8eed28bf9b67292f67bbbdde96cecb4baf42e758e0acbb4be34d5baa6418"
RECEIPT_SHA = "2258fdd66ec35cf57674c0dba38eac6cf8cde72e1148e238efd660270e70fec7"
RECEIPT_PATH = "docs/session_protocols/FOKAS_PHASE_RECONCILIATION_20260923.json"


def reconcile(raw: bytes, event: dict, *, repo: Path, recorded_at: str) -> tuple[dict, bool]:
    """Caller owns the writer lock, epoch and final byte-CAS.

    Evidence must exist as immutable Git documentation. This function trusts
    the reviewed, fixed host observation, not an invented native receipt.
    It never increments review counters or manufactures delivery/acceptance.
    """
    if (not isinstance(event, dict)
            or set(event) != {"transition_id", "expected_runtime_sha256", "receipt_pin"}
            or event["transition_id"] != TRANSITION
            or event["expected_runtime_sha256"] != PREIMAGE):
        spine._fail("FOKAS_PHASE_EVENT_INVALID")
    runtime = spine.validate_runtime(json.loads(raw))
    history = runtime.get("observed_phase_transitions", [])
    if not isinstance(history, list):
        spine._fail("FOKAS_PHASE_HISTORY_INVALID")
    for row in history:
        if not isinstance(row, dict):
            spine._fail("FOKAS_PHASE_HISTORY_INVALID")
        if row.get("event", {}).get("transition_id") == TRANSITION:
            saved = row.pop("successor_sha256", None)
            actual = spine._phase_record_digest(runtime)
            row["successor_sha256"] = saved
            if row["event"] != event or saved != actual:
                spine._fail("FOKAS_PHASE_REPLAY_CONFLICT")
            return runtime, False
    if hashlib.sha256(raw).hexdigest() != PREIMAGE:
        spine._fail("FOKAS_PHASE_STALE_PREIMAGE")
    pin = event["receipt_pin"]
    if (not isinstance(pin, dict) or pin.get("path") != RECEIPT_PATH
            or pin.get("sha256") != RECEIPT_SHA):
        spine._fail("FOKAS_PHASE_RECEIPT_INVALID")
    evidence_text = spine._phase_record_pin(pin, repo=repo)
    if hashlib.sha256(evidence_text.encode("utf-8")).hexdigest() != RECEIPT_SHA:
        spine._fail("FOKAS_PHASE_RECEIPT_INVALID")
    evidence = json.loads(evidence_text)
    stamp = dt.datetime.fromisoformat(recorded_at)
    if stamp.tzinfo is None:
        spine._fail("FOKAS_PHASE_TIME_INVALID")
    if runtime.get("active_exploration") is not None:
        spine._fail("FOKAS_PHASE_EXPLORATION_PENDING")
    phase = runtime["active_proshka_phase"]
    if (phase["conversation_id"] != evidence["registered_predecessor_conversation_id"]
            or phase["status"] != "ACTIVE"):
        spine._fail("FOKAS_PHASE_PREDECESSOR_MISMATCH")
    key = spine.validate_phase_key(evidence["phase_key"])
    updated = json.loads(json.dumps(runtime))
    updated.setdefault("observed_phase_transitions", []).append({
        "event": event,
        "predecessor_phase": phase,
        "predecessor_meter": runtime["meter"],
        "preimage_sha256": PREIMAGE,
        "receipt": evidence,
        "recorded_at": recorded_at,
        "disposition": "REGISTRATION_REPLACED_NOT_MATHEMATICAL_CLOSURE",
    })
    updated["active_proshka_phase"] = {
        "status": "ACTIVE", "phase_id": evidence["phase_id"], "phase_key": key,
        "conversation_id": evidence["existing_conversation_id"],
        "opened_at": recorded_at, "opening_pin": pin["commit"],
        "proshka_calls": 0, "full_context_uploads": 0,
        "owner_boundary_count": 0, "last_boundary_id": None,
        "last_adjudicated_pin": None,
    }
    # A new registered mathematical phase uses an already existing user chat.
    updated["meter"]["phases_opened"] += 1
    spine.validate_runtime(updated)
    updated["observed_phase_transitions"][-1]["successor_sha256"] = spine._phase_record_digest(updated)
    return updated, True
