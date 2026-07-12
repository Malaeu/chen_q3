#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-25 H2b determinant core."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H2B_HERMITIAN_DETERMINANT_REAL_ZEROS_CERTIFICATE.json"
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

    require(cert["revision_target"] == 25, "H2B_CERT_REVISION_DRIFT")
    require(state["revision"] >= 25, "H2B_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H2B_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H2B_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H2B_SOURCE_{index}")
    pinned(cert["artifact"], "H2B_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H2B_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H2B_LEAN_HOLE")
    require("#print axioms" in proof_text, "H2B_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H2B_THEOREM_MISSING:{theorem}")
    for token in (
        "periodicScalingDet",
        "Complex.exp_eq_one_iff",
        "Matrix.mem_spectrum_iff_isRoot_charpoly",
        "spectrum_eq_image_range",
        "ZerosRealOn",
        "nonHermitianPlantMatrix",
        "hermitianZeroMatrix1",
        "vanishingUnitPlant",
    ):
        require(token in proof_text, f"H2B_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h2b = nodes["H2b"]
    require(h2b["kind"] == "AND", "H2B_PARENT_NOT_AND")
    require(h2b["dependencies"] == ["H2b.0"], "H2B_PARENT_DEPENDENCY_DRIFT")
    require(h2b["ordered_children"] == ["H2b1", "H2b2"], "H2B_CHILD_ORDER_DRIFT")
    require(h2b["assembly_theorem_id"] == "H2b3", "H2B_ASSEMBLY_ADDRESS_DRIFT")
    require(h2b["proof_status"] == "CONDITIONAL", "H2B_PARENT_MUST_REMAIN_CONDITIONAL")
    for code in (
        "REAL_ZERO_THEOREM_OBJECT_MISMATCH",
        "THEOREM_5_10_HYPOTHESIS_GAP",
        "H2_COMPLETED_TRACKER_GLOBAL_REAL_ZERO_FALSE",
        "H2B_COMPLETION_SCOPE_GAP",
        "H2B_EXACT_THEOREM510_FACTORIZATION_MISSING",
    ):
        require(code in h2b["failure_codes"], f"H2B_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h2b_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H2B_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H2B_PROVED_NODE_ACTIVE:{node_id}")
    h2b1 = nodes["H2b1"]
    require(
        h2b1["validation"] == "GENERIC_HERMITIAN_DETERMINANT_REAL_ZERO_TRANSFER_LEAN",
        "H2B1_VERDICT_DRIFT",
    )
    require(
        h2b1["proof_artifact"] == "Q3/Proofs/RouteB/HermitianDeterminantRealZeros.lean",
        "H2B1_PROOF_ARTIFACT_DRIFT",
    )

    h2b2 = nodes["H2b2"]
    require(h2b2["proof_status"] == "OPEN", "H2B2_FALSE_PASS")
    require(not h2b2["eligibility"]["eligible"], "H2B2_FALSE_ELIGIBILITY")
    if state["revision"] >= 34:
        require(h2b2["kind"] == "AND", "H2B2_PARENT_NOT_AND")
        require(h2b2["dependencies"] == ["H2b2.0"], "H2B2_PARENT_DEPENDENCY_DRIFT")
        require(h2b2["ordered_children"] == ["H2b2a", "H2b2b"], "H2B2_CHILD_ORDER_DRIFT")
        require(h2b2["assembly_theorem_id"] == "H2b2c", "H2B2_ASSEMBLY_ADDRESS_DRIFT")
        nested_h2b2 = nodes["H2b2b"]
        require(nested_h2b2["proof_status"] == "OPEN", "H2B2B_FALSE_PASS")
        require(not nested_h2b2["eligibility"]["eligible"], "H2B2B_FALSE_ELIGIBILITY")
        if state["revision"] >= 37:
            require(nested_h2b2["kind"] == "AND", "H2B2B_PARENT_NOT_AND")
            require(nested_h2b2["dependencies"] == ["H2b2b.0"], "H2B2B_PARENT_DEPENDENCY_DRIFT")
            require(nested_h2b2["ordered_children"] == ["H2b2b1", "H2b2b2"], "H2B2B_CHILD_ORDER_DRIFT")
            require(nested_h2b2["assembly_theorem_id"] == "H2b2b3", "H2B2B_ASSEMBLY_ADDRESS_DRIFT")
            exact_h2b2 = nodes["H2b2b2"]
            require(exact_h2b2["proof_status"] == "OPEN", "H2B2B2_FALSE_PASS")
            require(not exact_h2b2["eligibility"]["eligible"], "H2B2B2_FALSE_ELIGIBILITY")
            require(
                exact_h2b2["dependencies"] == [
                    "D0.3d", "D0.6", "D0.7", "D0.8", "H1c2", "H1c3", "H2a", "H2b1", "H2b2a", "H2b2b1"
                ],
                "H2B2B2_DEPENDENCY_DRIFT",
            )
        else:
            exact_h2b2 = nested_h2b2
            require(
                exact_h2b2["dependencies"] == [
                    "D0.3d", "D0.6", "D0.7", "D0.8", "H1c2", "H1c3", "H2a", "H2b1", "H2b2a"
                ],
                "H2B2B_DEPENDENCY_DRIFT",
            )
    else:
        exact_h2b2 = h2b2
        require(
            exact_h2b2["dependencies"] == [
                "D0.3d", "D0.6", "D0.7", "D0.8", "H1c2", "H1c3", "H2a", "H2b1"
            ],
            "H2B2_DEPENDENCY_DRIFT",
        )
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in exact_h2b2["failure_codes"], f"H2B2_GUARD_MISSING:{code}")

    h2b3 = nodes["H2b3"]
    require(h2b3["proof_status"] == "OPEN", "H2B3_FALSE_PASS")
    require(not h2b3["eligibility"]["eligible"], "H2B3_FALSE_ELIGIBILITY")
    require(h2b3["dependencies"] == ["H2b.0", "H2b1", "H2b2"], "H2B3_DEPENDENCY_DRIFT")

    for node_id in ("H2", "H2a", "H2c"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H2B_COLLATERAL_FALSE_PASS:{node_id}")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H2B_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 25:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H2B_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H2B_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H2B_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H2B_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H2B_BUS_010_CREATED")
    require("NO_H2B_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H2B_PARENT_GUARD_DROPPED")
    require("NO_EXACT_THEOREM510_FACTORIZATION" in cert["explicit_nonclaims"], "H2B_EXACT_FACTOR_OVERCLAIM")
    require("NO_RH" in cert["explicit_nonclaims"], "H2B_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H2B_HERMITIAN_DETERMINANT_REAL_ZEROS_REV25_VALID",
        "h2b1": "GENERIC_HERMITIAN_DETERMINANT_REAL_ZERO_TRANSFER_LEAN",
        "falsifiers": ["NONHERMITIAN_CHARPOLY_NONREAL_ZERO", "VANISHING_UNIT_NONREAL_ZERO"],
        "h2b2": "OPEN_EXACT_THEOREM510_FACTORIZATION",
        "h2b_parent": "CONDITIONAL",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
