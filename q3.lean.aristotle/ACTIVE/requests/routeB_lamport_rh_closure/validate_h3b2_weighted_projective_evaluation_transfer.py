#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-32 H3b2 generic bridge."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H3B2_WEIGHTED_PROJECTIVE_EVALUATION_TRANSFER_CERTIFICATE.json"
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
    require(cert["revision_target"] == 32, "H3B2_CERT_REVISION_DRIFT")
    require(state["revision"] >= 32, "H3B2_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H3B2_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H3B2_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H3B2_SOURCE_{index}")
    pinned(cert["artifact"], "H3B2_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H3B2_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H3B2_LEAN_HOLE")
    require("#print axioms" in proof_text, "H3B2_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H3B2_THEOREM_MISSING:{theorem}")
    for token in (
        "import Q3.Proofs.RouteB.PhaseAlignmentRateTransfer",
        "import Q3.Proofs.RouteB.CompactEvaluationRateTransfer",
        "phase_alignment_norm_le_sqrt_two_projective_defect",
        "tendstoUniformlyOn_zero_of_evaluation_rate",
        "squeeze_zero'",
        "[NeBot l]",
        "mul_le_mul_of_nonneg_left",
        "C i * √(2 * (1 - ‖inner ℂ (u i) (v i)‖ ^ 2))",
        "filter_upwards",
        "simpa [e]",
    ):
        require(token in proof_text, f"H3B2_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    parent = nodes["H3b2"]
    require(parent["kind"] == "AND", "H3B2_PARENT_NOT_AND")
    require(parent["dependencies"] == ["H3b2.0"], "H3B2_PARENT_DEPENDENCY_DRIFT")
    require(parent["ordered_children"] == ["H3b2a", "H3b2b"], "H3B2_CHILD_ORDER_DRIFT")
    require(parent["assembly_theorem_id"] == "H3b2c", "H3B2_ASSEMBLY_ADDRESS_DRIFT")
    require(parent["proof_status"] == "OPEN", "H3B2_PARENT_FALSE_PASS")
    for code in ("H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING", "H3B2_EXACT_WEIGHTED_PROJECTIVE_INPUTS_MISSING", "PO_XWALK_UNIFORM_EVAL"):
        require(code in parent["failure_codes"], f"H3B2_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h3b2_repair"]["proved"]:
        require(nodes[node_id]["proof_status"] == "PROVED", f"H3B2_PROVED_NODE_DRIFT:{node_id}")
        require(nodes[node_id]["activity"] == "INACTIVE", f"H3B2_PROVED_NODE_ACTIVE:{node_id}")
    core = nodes["H3b2a"]
    require(core["dependencies"] == ["H3a1", "H3b1"], "H3B2A_DEPENDENCY_DRIFT")
    require(core["validation"] == "H3B2_GENERIC_WEIGHTED_PROJECTIVE_EVALUATION_TRANSFER_LEAN", "H3B2A_VERDICT_DRIFT")
    require(core["proof_artifact"] == "Q3/Proofs/RouteB/WeightedProjectiveEvaluationTransfer.lean", "H3B2A_PROOF_ARTIFACT_DRIFT")
    for code in ("H3B2_BOTTOM_FILTER_VACUITY", "H3B2_NEGATIVE_EVALUATION_ENVELOPE", "H3B2_FIXED_BOUND_WITHOUT_WEIGHTED_RATE"):
        require(code in core["failure_codes"], f"H3B2A_GUARD_MISSING:{code}")

    exact = nodes["H3b2b"]
    require(exact["proof_status"] == "OPEN" and not exact["eligibility"]["eligible"], "H3B2B_FALSE_PASS")
    require(exact["dependencies"] == ["D0", "H3a", "H3b2a"], "H3B2B_DEPENDENCY_DRIFT")
    require(exact["external_requirements"] == ["PO_XWALK_UNIFORM_EVAL"], "H3B2B_EXTERNAL_REQUIREMENT_DRIFT")
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in exact["failure_codes"], f"H3B2B_GUARD_MISSING:{code}")
    assembly = nodes["H3b2c"]
    require(assembly["proof_status"] == "OPEN" and not assembly["eligibility"]["eligible"], "H3B2C_FALSE_PASS")
    require(assembly["dependencies"] == ["H3b2.0", "H3b2a", "H3b2b"], "H3B2C_DEPENDENCY_DRIFT")
    require(nodes["H3b3"]["dependencies"] == ["H3b.0", "H3b1", "H3b2"], "H3B3_PARENT_CONSUMER_DRIFT")

    for node_id in ("H3b3", "H3b", "H3c2", "H3e2", "H3", "H3d", "L0c2", "L0"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H3B2_COLLATERAL_FALSE_PASS:{node_id}")
    eligible = [node_id for node_id, node in nodes.items() if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]]
    require(eligible == [], f"H3B2_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")
    counts: dict[str, int] = {}
    for node in nodes.values():
        counts[node["proof_status"]] = counts.get(node["proof_status"], 0) + 1
    if state["revision"] == 32:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H3B2_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H3B2_NODE_COUNT_DRIFT:{status}")
    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H3B2_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H3B2_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H3B2_BUS_010_CREATED")
    for nonclaim in ("NO_EXACT_PROJECTIVE_DEFECT_RATE", "NO_EXACT_COMPACT_EVALUATION_ENVELOPE", "NO_H3B2_PARENT_CLOSURE", "NO_RH"):
        require(nonclaim in cert["explicit_nonclaims"], f"H3B2_NONCLAIM_MISSING:{nonclaim}")

    print(json.dumps({"verdict": "H3B2_WEIGHTED_PROJECTIVE_EVALUATION_TRANSFER_REV32_VALID", "h3b2a": "H3B2_GENERIC_WEIGHTED_PROJECTIVE_EVALUATION_TRANSFER_LEAN", "h3b2b": "OPEN_EXACT_WEIGHTED_PROJECTIVE_INPUTS", "node_counts": counts, "eligible_worker_leaves": eligible, "active_leaf": active[0], "bus_010": "NOT_CREATED", "rh": "NOT_RH"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
