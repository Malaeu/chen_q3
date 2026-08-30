#!/usr/bin/env python3
"""Closed consumer-first contract for candidate theorem dependencies."""

from __future__ import annotations

from typing import Any


class DependencyContractError(ValueError):
    pass


NECESSITY = {"PROVED_NECESSARY", "UNKNOWN", "NOT_NECESSARY"}
FAILURE_TYPES = {
    "NO_SOURCE", "NO_DERIVATION", "FORMALIZATION_COST",
    "COUNTEREXAMPLE", "INCOMPATIBILITY", "FORMAL_IMPOSSIBILITY", "OTHER",
}
EPISTEMIC = {"RESEARCH_DEBT", "MATHEMATICALLY_DEAD", "UNRESOLVED"}


def _text(row: dict[str, Any], key: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value.strip():
        raise DependencyContractError(f"RIGID_DEPENDENCY_UNJUSTIFIED:{key}")
    return value.strip()


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
    evidence = row.get("necessity_evidence")
    if not isinstance(evidence, list):
        raise DependencyContractError("RIGID_DEPENDENCY_UNJUSTIFIED:necessity_evidence")
    if necessity == "PROVED_NECESSARY" and not evidence:
        raise DependencyContractError("RIGID_DEPENDENCY_UNJUSTIFIED:necessity_evidence_required")
    weaker = row.get("known_weaker_interfaces")
    if not isinstance(weaker, list) or not weaker or any(
        not isinstance(item, str) or not item.strip() for item in weaker
    ):
        raise DependencyContractError("RIGID_DEPENDENCY_UNJUSTIFIED:known_weaker_interfaces")
    failure = row.get("failure_type")
    if failure not in FAILURE_TYPES:
        raise DependencyContractError("RESEARCH_DEPENDENCY_FAILURE_TYPE_INVALID")
    epistemic = row.get("epistemic_status")
    if epistemic not in EPISTEMIC:
        raise DependencyContractError("RESEARCH_DEPENDENCY_EPISTEMIC_STATUS_INVALID")
    death_evidence = row.get("death_evidence")
    if not isinstance(death_evidence, list):
        raise DependencyContractError("RESEARCH_DEPENDENCY_DEATH_EVIDENCE_INVALID")
    if epistemic == "MATHEMATICALLY_DEAD":
        if failure not in {"COUNTEREXAMPLE", "INCOMPATIBILITY", "FORMAL_IMPOSSIBILITY"}:
            raise DependencyContractError("MATHEMATICALLY_DEAD_WITHOUT_IMPOSSIBILITY")
        if not death_evidence:
            raise DependencyContractError("MATHEMATICALLY_DEAD_WITHOUT_EVIDENCE")
    elif death_evidence:
        raise DependencyContractError("DEATH_EVIDENCE_ON_NONDEAD_DEPENDENCY")
