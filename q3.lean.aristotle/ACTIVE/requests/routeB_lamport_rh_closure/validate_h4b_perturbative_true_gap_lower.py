#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-28 H4b generic gap core."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H4B_PERTURBATIVE_TRUE_GAP_LOWER_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"
FORBIDDEN = re.compile(r"\b(sorry|admit)\b|exact\?")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def pinned(record: dict[str, object], code: str) -> Path:
    path = REPO_ROOT / str(record["path"])
    require(path.is_file(), f"{code}_MISSING:{record['path']}")
    require(sha256(path) == record["sha256"], f"{code}_HASH_DRIFT:{record['path']}")
    return path


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    state = json.loads(STATE_PATH.read_text(encoding="utf-8"))

    require(cert["revision_target"] == 28, "H4B_CERT_REVISION_DRIFT")
    require(state["revision"] >= 28, "H4B_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H4B_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H4B_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H4B_SOURCE_{index}")
    pinned(cert["artifact"], "H4B_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H4B_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H4B_LEAN_HOLE")
    require("#print axioms" in proof_text, "H4B_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H4B_THEOREM_MISSING:{theorem}")
    for token in (
        "trueLow ≤ modelLow + errLow",
        "modelHigh - errHigh ≤ trueHigh",
        "floor + errLow + errHigh ≤ modelHigh - modelLow",
        "abs_le.mp",
        "hfloor.trans_le",
        "filter_upwards",
        "[NeBot l]",
        "positive_model_gap_without_endpoint_control_does_not_force_true_gap",
        "endpoint_errors_can_consume_entire_model_gap",
    ):
        require(token in proof_text, f"H4B_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h4b = nodes["H4b"]
    require(h4b["kind"] == "AND", "H4B_PARENT_NOT_AND")
    require(h4b["dependencies"] == ["H4b.0"], "H4B_PARENT_DEPENDENCY_DRIFT")
    require(h4b["ordered_children"] == ["H4b1", "H4b2"], "H4B_CHILD_ORDER_DRIFT")
    require(h4b["assembly_theorem_id"] == "H4b3", "H4B_ASSEMBLY_ADDRESS_DRIFT")
    require(h4b["proof_status"] == "OPEN", "H4B_PARENT_FALSE_PASS")
    for code in (
        "SAFE_GAP_LOWER_NO_SOURCE",
        "TRUE_GAP_LOWER_MISSING",
        "H4B_EXACT_SAME_PARITY_FUCHS_GAP_INSTANTIATION_MISSING",
        "MODEL_GAP_SUBSTITUTION",
        "GROUND_SECTOR_MISMATCH",
    ):
        require(code in h4b["failure_codes"], f"H4B_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h4b_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H4B_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H4B_PROVED_NODE_ACTIVE:{node_id}")
    h4b1 = nodes["H4b1"]
    require(h4b1["validation"] == "GENERIC_PERTURBATIVE_TRUE_GAP_LOWER_LEAN", "H4B1_VERDICT_DRIFT")
    require(
        h4b1["proof_artifact"] == "Q3/Proofs/RouteB/PerturbativeTrueGapLower.lean",
        "H4B1_PROOF_ARTIFACT_DRIFT",
    )

    h4b2 = nodes["H4b2"]
    require(h4b2["proof_status"] == "OPEN", "H4B2_FALSE_PASS")
    require(not h4b2["eligibility"]["eligible"], "H4B2_FALSE_ELIGIBILITY")
    require(h4b2["dependencies"] == ["D0", "H2a", "H4b1"], "H4B2_DEPENDENCY_DRIFT")
    require(
        h4b2["external_requirements"] == ["H4B_EXACT_SAME_PARITY_FUCHS_GAP"],
        "H4B2_EXTERNAL_REQUIREMENT_DRIFT",
    )
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in h4b2["failure_codes"], f"H4B2_GUARD_MISSING:{code}")

    h4b3 = nodes["H4b3"]
    require(h4b3["proof_status"] == "OPEN", "H4B3_FALSE_PASS")
    require(not h4b3["eligibility"]["eligible"], "H4B3_FALSE_ELIGIBILITY")
    require(h4b3["dependencies"] == ["H4b.0", "H4b1", "H4b2"], "H4B3_DEPENDENCY_DRIFT")

    for node_id in ("H4", "H3e", "H4c2", "H4d2b", "L0c2", "L0"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H4B_COLLATERAL_FALSE_PASS:{node_id}")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H4B_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 28:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H4B_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H4B_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H4B_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H4B_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H4B_BUS_010_CREATED")
    require("NO_TRUE_GAP_RATE" in cert["explicit_nonclaims"], "H4B_EXACT_RATE_OVERCLAIM")
    require("NO_H4B_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H4B_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H4B_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H4B_PERTURBATIVE_TRUE_GAP_LOWER_REV28_VALID",
        "h4b1": "GENERIC_PERTURBATIVE_TRUE_GAP_LOWER_LEAN",
        "h4b2": "OPEN_EXACT_SAME_PARITY_FUCHS_GAP",
        "falsifiers": cert["h4b_repair"]["falsifiers"],
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
