#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-34 H2b2 rank-one core."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H2B2_RANK_ONE_CORRECTION_WEIGHTED_SYMMETRY_CERTIFICATE.json"
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

    require(cert["revision_target"] == 34, "H2B2_CERT_REVISION_DRIFT")
    require(state["revision"] >= 34, "H2B2_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H2B2_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H2B2_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H2B2_SOURCE_{index}")
    pinned(cert["artifact"], "H2B2_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H2B2_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H2B2_LEAN_HOLE")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H2B2_THEOREM_MISSING:{theorem}")
    for token in (
        "def rankOneCorrection",
        "Matrix.sub_mulVec",
        "Matrix.vecMulVec_mulVec",
        "Matrix.mulVec_transpose",
        "Matrix.mul_vecMulVec",
        "Matrix.transpose_vecMulVec",
        "Matrix.vecMulVec_mul",
        "eta ⬝ᵥ xi = 1",
        "T * D - D * T",
        "#print axioms",
    ):
        require(token in proof_text, f"H2B2_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    parent = nodes["H2b2"]
    require(parent["kind"] == "AND", "H2B2_PARENT_NOT_AND")
    require(parent["dependencies"] == ["H2b2.0"], "H2B2_PARENT_DEPENDENCY_DRIFT")
    require(parent["ordered_children"] == ["H2b2a", "H2b2b"], "H2B2_CHILD_ORDER_DRIFT")
    require(parent["assembly_theorem_id"] == "H2b2c", "H2B2_ASSEMBLY_ADDRESS_DRIFT")
    require(parent["proof_status"] == "OPEN", "H2B2_PARENT_FALSE_PASS")

    for node_id in cert["h2b2_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H2B2_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H2B2_PROVED_NODE_ACTIVE:{node_id}")
    require(
        nodes["H2b2a"]["validation"]
        == "H2B2_GENERIC_RANK_ONE_CORRECTION_WEIGHTED_SYMMETRY_LEAN",
        "H2B2A_VERDICT_DRIFT",
    )
    require(
        nodes["H2b2a"]["proof_artifact"]
        == "Q3/Proofs/RouteB/RankOneCorrectionWeightedSymmetry.lean",
        "H2B2A_PROOF_ARTIFACT_DRIFT",
    )

    exact_parent = nodes["H2b2b"]
    require(exact_parent["proof_status"] == "OPEN", "H2B2B_FALSE_PASS")
    require(not exact_parent["eligibility"]["eligible"], "H2B2B_FALSE_ELIGIBILITY")
    if state["revision"] >= 37:
        require(exact_parent["kind"] == "AND", "H2B2B_PARENT_NOT_AND")
        require(exact_parent["dependencies"] == ["H2b2b.0"], "H2B2B_PARENT_DEPENDENCY_DRIFT")
        require(exact_parent["ordered_children"] == ["H2b2b1", "H2b2b2"], "H2B2B_CHILD_ORDER_DRIFT")
        require(exact_parent["assembly_theorem_id"] == "H2b2b3", "H2B2B_ASSEMBLY_ADDRESS_DRIFT")
        exact_parent = nodes["H2b2b2"]
        if state["revision"] >= 38:
            require(exact_parent["kind"] == "AND", "H2B2B2_PARENT_NOT_AND")
            require(exact_parent["dependencies"] == ["H2b2b2.0"], "H2B2B2_PARENT_DEPENDENCY_DRIFT")
            require(
                exact_parent["ordered_children"] == ["H2b2b2a", "H2b2b2b"],
                "H2B2B2_CHILD_ORDER_DRIFT",
            )
            require(exact_parent["assembly_theorem_id"] == "H2b2b2c", "H2B2B2_ASSEMBLY_ADDRESS_DRIFT")
            exact_parent = nodes["H2b2b2b"]
            if state["revision"] >= 39:
                require(exact_parent["kind"] == "AND", "H2B2B2B_PARENT_NOT_AND")
                require(exact_parent["dependencies"] == ["H2b2b2b.0"], "H2B2B2B_PARENT_DEPENDENCY_DRIFT")
                require(
                    exact_parent["ordered_children"] == ["H2b2b2b1", "H2b2b2b2"],
                    "H2B2B2B_CHILD_ORDER_DRIFT",
                )
                require(exact_parent["assembly_theorem_id"] == "H2b2b2b3", "H2B2B2B_ASSEMBLY_ADDRESS_DRIFT")
                exact_parent = nodes["H2b2b2b2"]
                if state["revision"] >= 40:
                    require(exact_parent["kind"] == "AND", "H2B2B2B2_PARENT_NOT_AND")
                    require(exact_parent["dependencies"] == ["H2b2b2b2.0"], "H2B2B2B2_PARENT_DEPENDENCY_DRIFT")
                    require(
                        exact_parent["ordered_children"] == ["H2b2b2b2a", "H2b2b2b2b"],
                        "H2B2B2B2_CHILD_ORDER_DRIFT",
                    )
                    require(exact_parent["assembly_theorem_id"] == "H2b2b2b2c", "H2B2B2B2_ASSEMBLY_ADDRESS_DRIFT")
                    exact = nodes["H2b2b2b2b"]
                    expected_dependencies = [
                        "D0.3d", "D0.6", "D0.7", "D0.8", "H1c2", "H1c3", "H2a", "H2b1",
                        "H2b2a", "H2b2b1", "H2b2b2a", "H2b2b2b1", "H2b2b2b2a",
                    ]
                else:
                    exact = exact_parent
                    expected_dependencies = [
                        "D0.3d", "D0.6", "D0.7", "D0.8", "H1c2", "H1c3", "H2a", "H2b1",
                        "H2b2a", "H2b2b1", "H2b2b2a", "H2b2b2b1",
                    ]
            else:
                exact = exact_parent
                expected_dependencies = [
                    "D0.3d", "D0.6", "D0.7", "D0.8", "H1c2", "H1c3", "H2a", "H2b1",
                    "H2b2a", "H2b2b1", "H2b2b2a",
                ]
        else:
            exact = exact_parent
            expected_dependencies = [
                "D0.3d", "D0.6", "D0.7", "D0.8", "H1c2", "H1c3", "H2a", "H2b1",
                "H2b2a", "H2b2b1",
            ]
        require(exact["proof_status"] == "OPEN", "H2B2B2_FALSE_PASS")
        require(not exact["eligibility"]["eligible"], "H2B2B2_FALSE_ELIGIBILITY")
        require(exact["dependencies"] == expected_dependencies, "H2B2B2_DEPENDENCY_DRIFT")
    else:
        exact = exact_parent
        require(
            exact["dependencies"] == cert["exact_instantiation_guard"]["dependencies"],
            "H2B2B_DEPENDENCY_DRIFT",
        )
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in exact["failure_codes"], f"H2B2B_GUARD_MISSING:{code}")

    assembly = nodes["H2b2c"]
    require(assembly["proof_status"] == "OPEN", "H2B2C_FALSE_PASS")
    require(not assembly["eligibility"]["eligible"], "H2B2C_FALSE_ELIGIBILITY")
    require(
        assembly["dependencies"] == ["H2b2.0", "H2b2a", "H2b2b"],
        "H2B2C_DEPENDENCY_DRIFT",
    )
    require(nodes["H2b"]["proof_status"] == "CONDITIONAL", "H2B_PARENT_STATUS_DRIFT")
    require(nodes["H2b3"]["dependencies"] == ["H2b.0", "H2b1", "H2b2"], "H2B3_CONSUMER_DRIFT")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H2B2_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 34:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H2B2_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H2B2_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H2B2_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H2B2_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H2B2_BUS_010_CREATED")
    require("NO_EXACT_THEOREM510_FACTORIZATION" in cert["explicit_nonclaims"], "H2B2_EXACT_OVERCLAIM")
    require("NO_RH" in cert["explicit_nonclaims"], "H2B2_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H2B2_RANK_ONE_CORRECTION_WEIGHTED_SYMMETRY_REV34_VALID",
        "h2b2a": "H2B2_GENERIC_RANK_ONE_CORRECTION_WEIGHTED_SYMMETRY_LEAN",
        "h2b2b": "OPEN_EXACT_MODIFIED_HILBERT_FACTORIZATION",
        "h2b_parent": "CONDITIONAL",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
