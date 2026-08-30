#!/usr/bin/env python3
"""Closed consumer-first contract for candidate theorem dependencies."""

from __future__ import annotations

import re
from typing import Any


class DependencyContractError(ValueError):
    pass


NECESSITY = {"PROVED_NECESSARY", "SUFFICIENT_ONLY", "UNKNOWN", "NOT_NECESSARY"}
FAILURE_TYPES = {
    "NO_SOURCE", "NO_DERIVATION", "FORMALIZATION_COST",
    "COUNTEREXAMPLE", "INCOMPATIBILITY", "FORMAL_IMPOSSIBILITY", "OTHER",
}
EPISTEMIC = {"RESEARCH_DEBT", "MATHEMATICALLY_DEAD", "UNRESOLVED"}
EVIDENCE_FIELDS = frozenset({"kind", "path", "commit", "git_blob", "scope", "claim"})
HEX40_RE = re.compile(r"^[0-9a-f]{40}$")


def _text(row: dict[str, Any], key: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value.strip():
        raise DependencyContractError(f"RIGID_DEPENDENCY_UNJUSTIFIED:{key}")
    return value.strip()


def validate_evidence(value: object, *, field: str) -> list[dict[str, str]]:
    """Validate source-pinned evidence rather than accepting a truthy label."""
    if not isinstance(value, list):
        raise DependencyContractError(f"RESEARCH_DEPENDENCY_EVIDENCE_INVALID:{field}")
    result: list[dict[str, str]] = []
    for index, item in enumerate(value):
        if not isinstance(item, dict) or set(item) != EVIDENCE_FIELDS:
            raise DependencyContractError(
                f"RESEARCH_DEPENDENCY_EVIDENCE_INVALID:{field}:{index}:fields"
            )
        normalized: dict[str, str] = {}
        for key in EVIDENCE_FIELDS:
            raw = item.get(key)
            if not isinstance(raw, str) or not raw.strip():
                raise DependencyContractError(
                    f"RESEARCH_DEPENDENCY_EVIDENCE_INVALID:{field}:{index}:{key}"
                )
            normalized[key] = raw.strip()
        path = normalized["path"]
        if path.startswith("/") or ".." in path.split("/"):
            raise DependencyContractError(
                f"RESEARCH_DEPENDENCY_EVIDENCE_INVALID:{field}:{index}:path"
            )
        for key in ("commit", "git_blob"):
            if HEX40_RE.fullmatch(normalized[key]) is None:
                raise DependencyContractError(
                    f"RESEARCH_DEPENDENCY_EVIDENCE_INVALID:{field}:{index}:{key}"
                )
        result.append(normalized)
    return result


def validate(row: dict[str, Any]) -> None:
    """Reject a named dependency unless its consumer and necessity audit are explicit."""
    _text(row, "original_requested_object")
    _text(row, "downstream_consumer")
    _text(row, "actual_consumer_requirement")
    _text(row, "consumer_implication")
    _text(row, "weaker_interface_probe")
    necessity = row.get("original_object_is")
    if necessity not in NECESSITY:
        raise DependencyContractError("RIGID_DEPENDENCY_UNJUSTIFIED:original_object_is")
    evidence = validate_evidence(row.get("necessity_evidence"), field="necessity_evidence")
    if necessity == "PROVED_NECESSARY" and not evidence:
        raise DependencyContractError("RIGID_DEPENDENCY_UNJUSTIFIED:necessity_evidence_required")
    weaker = row.get("known_weaker_interfaces")
    if not isinstance(weaker, list) or any(
        not isinstance(item, str) or not item.strip() for item in weaker
    ):
        raise DependencyContractError("RIGID_DEPENDENCY_UNJUSTIFIED:known_weaker_interfaces")
    if necessity != "PROVED_NECESSARY" and not weaker:
        raise DependencyContractError("RIGID_DEPENDENCY_UNJUSTIFIED:known_weaker_interfaces_required")
    failure = row.get("failure_type")
    if failure not in FAILURE_TYPES:
        raise DependencyContractError("RESEARCH_DEPENDENCY_FAILURE_TYPE_INVALID")
    epistemic = row.get("epistemic_status")
    if epistemic not in EPISTEMIC:
        raise DependencyContractError("RESEARCH_DEPENDENCY_EPISTEMIC_STATUS_INVALID")
    _text(row, "failure_scope")
    death_evidence = validate_evidence(row.get("death_evidence"), field="death_evidence")
    if epistemic == "MATHEMATICALLY_DEAD":
        if failure not in {"COUNTEREXAMPLE", "INCOMPATIBILITY", "FORMAL_IMPOSSIBILITY"}:
            raise DependencyContractError("MATHEMATICALLY_DEAD_WITHOUT_IMPOSSIBILITY")
        if not death_evidence:
            raise DependencyContractError("MATHEMATICALLY_DEAD_WITHOUT_EVIDENCE")
    elif death_evidence:
        raise DependencyContractError("DEATH_EVIDENCE_ON_NONDEAD_DEPENDENCY")
    if epistemic == "RESEARCH_DEBT":
        triggers = row.get("reopen_triggers")
        if not isinstance(triggers, list) or not triggers or any(
            not isinstance(item, str) or not item.strip() for item in triggers
        ):
            raise DependencyContractError("RESEARCH_DEBT_REOPEN_TRIGGERS_INVALID")
