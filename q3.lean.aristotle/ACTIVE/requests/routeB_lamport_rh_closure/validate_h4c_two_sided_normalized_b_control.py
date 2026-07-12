#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-26 H4c b-control core."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H4C_TWO_SIDED_NORMALIZED_B_CONTROL_CERTIFICATE.json"
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

    require(cert["revision_target"] == 26, "H4C_CERT_REVISION_DRIFT")
    require(state["revision"] >= 26, "H4C_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H4C_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H4C_STATE_RH_OVERCLAIM")

    source_paths = []
    for index, source in enumerate(cert["source_pins"]):
        source_paths.append(pinned(source, f"H4C_SOURCE_{index}"))
    pinned(cert["artifact"], "H4C_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H4C_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H4C_LEAN_HOLE")
    require("#print axioms" in proof_text, "H4C_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H4C_THEOREM_MISSING:{theorem}")
    for token in (
        "Real.rpow_pos_of_pos",
        "Real.rpow_neg",
        "inv_mul_cancel₀",
        "one_div_le_one_div_of_le",
        "mul_inv",
        "filter_upwards",
        "[NeBot l]",
        "div_eq_mul_inv",
    ):
        require(token in proof_text, f"H4C_MECHANISM_MISSING:{token}")
    falsifier_text = source_paths[4].read_text(encoding="utf-8")
    for token in cert["mandatory_falsifier"]["theorems"]:
        require(token in falsifier_text, f"H4C_FALSIFIER_MISSING:{token}")

    nodes = state["nodes"]
    h4c = nodes["H4c"]
    require(h4c["kind"] == "AND", "H4C_PARENT_NOT_AND")
    require(h4c["dependencies"] == ["H4c.0"], "H4C_PARENT_DEPENDENCY_DRIFT")
    require(h4c["ordered_children"] == ["H4c1", "H4c2"], "H4C_CHILD_ORDER_DRIFT")
    require(h4c["assembly_theorem_id"] == "H4c3", "H4C_ASSEMBLY_ADDRESS_DRIFT")
    require(h4c["proof_status"] == "OPEN", "H4C_PARENT_FALSE_PASS")
    for code in (
        "H0_A1_ALPHA_DEFINITION_MISSING",
        "NORMALIZATION_ZERO",
        "NORMALIZATION_CONTROL_MISSING",
        "H4D_COFINAL_NONZERO_LOCUS_MISSING",
        "H4D_BDET_RECIPROCAL_CONTROL_MISSING",
        "H4D_QB_VALUE_UNPROVED",
        "H4C_EXACT_SIGN_AND_B_INSTANTIATION_MISSING",
    ):
        require(code in h4c["failure_codes"], f"H4C_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h4c_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H4C_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H4C_PROVED_NODE_ACTIVE:{node_id}")
    h4c1 = nodes["H4c1"]
    require(
        h4c1["validation"] == "H4C_GENERIC_TWO_SIDED_NORMALIZED_B_CONTROL_LEAN",
        "H4C1_VERDICT_DRIFT",
    )
    require(
        h4c1["proof_artifact"] == "Q3/Proofs/RouteB/TwoSidedNormalizedBControl.lean",
        "H4C1_PROOF_ARTIFACT_DRIFT",
    )

    h4c2 = nodes["H4c2"]
    require(h4c2["proof_status"] == "OPEN", "H4C2_FALSE_PASS")
    require(not h4c2["eligibility"]["eligible"], "H4C2_FALSE_ELIGIBILITY")
    require(h4c2["dependencies"] == ["D0", "H2a", "H4c1"], "H4C2_DEPENDENCY_DRIFT")
    require(h4c2["external_requirements"] == ["PO-1/A1"], "H4C2_EXTERNAL_REQUIREMENT_DRIFT")
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in h4c2["failure_codes"], f"H4C2_GUARD_MISSING:{code}")

    h4c3 = nodes["H4c3"]
    require(h4c3["proof_status"] == "OPEN", "H4C3_FALSE_PASS")
    require(not h4c3["eligibility"]["eligible"], "H4C3_FALSE_ELIGIBILITY")
    require(h4c3["dependencies"] == ["H4c.0", "H4c1", "H4c2"], "H4C3_DEPENDENCY_DRIFT")

    for node_id in ("H3e", "H4d2", "H4d2b", "H4", "H4e"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H4C_COLLATERAL_FALSE_PASS:{node_id}")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H4C_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 26:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H4C_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H4C_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H4C_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H4C_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H4C_BUS_010_CREATED")
    require("NO_UNIFORM_POSITIVE_B_LOWER_BOUND" in cert["explicit_nonclaims"], "H4C_UNIFORM_LOWER_OVERCLAIM")
    require("NO_H4C_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H4C_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H4C_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H4C_TWO_SIDED_NORMALIZED_B_CONTROL_REV26_VALID",
        "h4c1": "H4C_GENERIC_TWO_SIDED_NORMALIZED_B_CONTROL_LEAN",
        "h4c2": "OPEN_EXACT_SAFE_SIGN_AND_B_INSTANTIATION",
        "falsifier": "NORMALIZED_LOWER_PRODUCT_DOES_NOT_IMPLY_UNIFORM_B_LOWER_BOUND",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
