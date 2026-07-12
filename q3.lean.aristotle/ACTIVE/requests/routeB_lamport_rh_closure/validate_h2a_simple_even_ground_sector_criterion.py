#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-20 H2a generic sector criterion."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H2A_SIMPLE_EVEN_GROUND_SECTOR_CRITERION_CERTIFICATE.json"
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

    require(cert["revision_target"] == 20, "H2A_CERT_REVISION_DRIFT")
    require(state["revision"] >= 20, "H2A_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H2A_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H2A_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H2A_SOURCE_{index}")
    pinned(cert["artifact"], "H2A_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H2A_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H2A_LEAN_HOLE")
    require("#print axioms" in proof_text, "H2A_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H2A_THEOREM_MISSING:{theorem}")
    for token in (
        "IsSimpleEvenGround",
        "evenPart",
        "oddPart",
        "Commute A J",
        "hoddStrict",
        "smul_left_injective",
        "sq_eq_one_iff",
        "IsSimpleGround oddGroundOperator2 0 (0, 1)",
        "IsOddVector parityInvolution2 (0, 1)",
    ):
        require(token in proof_text, f"H2A_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h2a = nodes["H2a"]
    require(h2a["kind"] == "AND", "H2A_PARENT_NOT_AND")
    require(h2a["ordered_children"] == ["H2a1", "H2a2"], "H2A_CHILD_ORDER_DRIFT")
    require(h2a["assembly_theorem_id"] == "H2a3", "H2A_ASSEMBLY_ADDRESS_DRIFT")
    require(h2a["proof_status"] == "OPEN", "H2A_PARENT_FALSE_PASS")
    for code in (
        "SIMPLE_EVEN_GROUND_MISSING",
        "GROUND_SECTOR_MISMATCH",
        "H2A_EXACT_SECTOR_ORDERING_MISSING",
        "H2A_SAME_FAMILY_SELECTION_MISSING",
    ):
        require(code in h2a["failure_codes"], f"H2A_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h2a_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H2A_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H2A_PROVED_NODE_ACTIVE:{node_id}")
    h2a1 = nodes["H2a1"]
    require(
        h2a1["validation"] == "GENERIC_SIMPLE_EVEN_GROUND_SECTOR_CRITERION_LEAN",
        "H2A1_VERDICT_DRIFT",
    )
    require(
        h2a1["proof_artifact"] == "Q3/Proofs/RouteB/SimpleEvenGroundSectorCriterion.lean",
        "H2A1_PROOF_ARTIFACT_DRIFT",
    )

    h2a2 = nodes["H2a2"]
    require(h2a2["proof_status"] == "OPEN", "H2A2_FALSE_PASS")
    require(not h2a2["eligibility"]["eligible"], "H2A2_FALSE_ELIGIBILITY")
    require(
        h2a2["dependencies"] == ["D0.4", "D0.5", "D0.8", "H1c3", "H2a1"],
        "H2A2_SAME_FAMILY_DEPENDENCY_DRIFT",
    )
    for code in (
        "H2A_EXACT_SECTOR_ORDERING_MISSING",
        "H2A_EVEN_INTERNAL_GAP_MISSING",
        "H2A_EVEN_ODD_BOTTOM_ORDER_MISSING",
        "H2A_ISOLATION_RADIUS_MISSING",
        "H2A_SAME_FAMILY_SELECTION_MISSING",
    ):
        require(code in h2a2["failure_codes"], f"H2A2_GUARD_MISSING:{code}")

    h2a3 = nodes["H2a3"]
    require(h2a3["proof_status"] == "OPEN", "H2A3_FALSE_PASS")
    require(not h2a3["eligibility"]["eligible"], "H2A3_FALSE_ELIGIBILITY")
    require(
        h2a3["dependencies"] == ["H2a.0", "H2a1", "H2a2"],
        "H2A3_DEPENDENCY_DRIFT",
    )

    require(nodes["H2"]["proof_status"] == "OPEN", "H2_PARENT_FALSE_PASS")
    require(nodes["H2b"]["proof_status"] == "CONDITIONAL", "H2B_CONDITIONAL_DRIFT")
    require(nodes["H2c"]["proof_status"] == "OPEN", "H2C_FALSE_PASS")
    require(nodes["H4a3b"]["proof_status"] == "OPEN", "H4A3B_COLLATERAL_FALSE_PASS")
    require(nodes["H4b"]["proof_status"] == "OPEN", "H4B_COLLATERAL_FALSE_PASS")
    require(nodes["H4c"]["proof_status"] == "OPEN", "H4C_COLLATERAL_FALSE_PASS")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H2A_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 20:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H2A_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H2A_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H2A_ACTIVE_LEAF_DRIFT")
    require(
        state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING",
        "H2A_ACTIVE_STOP_DRIFT",
    )
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H2A_BUS_010_CREATED")
    require("NO_H2A_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H2A_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H2A_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H2A_SIMPLE_EVEN_GROUND_SECTOR_CRITERION_REV20_VALID",
        "h2a1": "GENERIC_SIMPLE_EVEN_GROUND_SECTOR_CRITERION_LEAN",
        "falsifier": "COMMUTING_SIMPLE_GROUND_CAN_BE_ODD",
        "h2a2": "OPEN_EXACT_SELECTED_FAMILY_SECTOR_ORDERING",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
