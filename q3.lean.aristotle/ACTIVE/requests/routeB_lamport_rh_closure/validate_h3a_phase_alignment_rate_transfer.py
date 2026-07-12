#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-27 H3a phase core."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H3A_PHASE_ALIGNMENT_RATE_TRANSFER_CERTIFICATE.json"
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

    require(cert["revision_target"] == 27, "H3A_CERT_REVISION_DRIFT")
    require(state["revision"] >= 27, "H3A_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H3A_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H3A_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H3A_SOURCE_{index}")
    pinned(cert["artifact"], "H3A_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H3A_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H3A_LEAN_HOLE")
    require("#print axioms" in proof_text, "H3A_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H3A_THEOREM_MISSING:{theorem}")
    for token in (
        "alignmentPhase",
        "starRingEnd ℂ",
        "Complex.mul_conj",
        "Complex.normSq_eq_norm_sq",
        "norm_sub_sq (𝕜 := ℂ)",
        "inner_smul_left",
        "norm_inner_le_norm (𝕜 := ℂ)",
        "tendsto_of_tendsto_of_tendsto_of_le_of_le'",
        ".const_mul 2",
        ".sqrt",
        "filter_upwards",
        "[NeBot l]",
    ):
        require(token in proof_text, f"H3A_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h3a = nodes["H3a"]
    require(h3a["kind"] == "AND", "H3A_PARENT_NOT_AND")
    require(h3a["dependencies"] == ["H3a.0"], "H3A_PARENT_DEPENDENCY_DRIFT")
    require(h3a["ordered_children"] == ["H3a1", "H3a2"], "H3A_CHILD_ORDER_DRIFT")
    require(h3a["assembly_theorem_id"] == "H3a3", "H3A_ASSEMBLY_ADDRESS_DRIFT")
    require(h3a["proof_status"] == "OPEN", "H3A_PARENT_FALSE_PASS")
    require("PHASE_ALIGNMENT_MISSING" not in h3a["failure_codes"], "H3A_RETIRED_GENERIC_GUARD_STILL_LIVE")
    for code in ("GROUND_TRIAL_TRACKING_MISSING", "H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING"):
        require(code in h3a["failure_codes"], f"H3A_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h3a_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H3A_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H3A_PROVED_NODE_ACTIVE:{node_id}")
    h3a1 = nodes["H3a1"]
    require(h3a1["validation"] == "GENERIC_PHASE_ALIGNMENT_RATE_TRANSFER_LEAN", "H3A1_VERDICT_DRIFT")
    require(
        h3a1["proof_artifact"] == "Q3/Proofs/RouteB/PhaseAlignmentRateTransfer.lean",
        "H3A1_PROOF_ARTIFACT_DRIFT",
    )

    h3a2 = nodes["H3a2"]
    require(h3a2["proof_status"] == "OPEN", "H3A2_FALSE_PASS")
    require(not h3a2["eligibility"]["eligible"], "H3A2_FALSE_ELIGIBILITY")
    require(h3a2["dependencies"] == ["D0", "H3a1"], "H3A2_DEPENDENCY_DRIFT")
    require(h3a2["external_requirements"] == ["H3A_EXACT_GROUND_TRIAL_PROJECTIVE_RATE"], "H3A2_EXTERNAL_REQUIREMENT_DRIFT")
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in h3a2["failure_codes"], f"H3A2_GUARD_MISSING:{code}")

    h3a3 = nodes["H3a3"]
    require(h3a3["proof_status"] == "OPEN", "H3A3_FALSE_PASS")
    require(not h3a3["eligibility"]["eligible"], "H3A3_FALSE_ELIGIBILITY")
    require(h3a3["dependencies"] == ["H3a.0", "H3a1", "H3a2"], "H3A3_DEPENDENCY_DRIFT")

    for node_id in ("H3", "H3b2", "H3c2", "H3e", "L0c2", "L0"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H3A_COLLATERAL_FALSE_PASS:{node_id}")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H3A_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 27:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H3A_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H3A_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H3A_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H3A_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H3A_BUS_010_CREATED")
    require("NO_EXACT_PROJECTIVE_DEFECT_RATE" in cert["explicit_nonclaims"], "H3A_EXACT_RATE_OVERCLAIM")
    require("NO_H3A_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H3A_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H3A_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H3A_PHASE_ALIGNMENT_RATE_TRANSFER_REV27_VALID",
        "h3a1": "GENERIC_PHASE_ALIGNMENT_RATE_TRANSFER_LEAN",
        "h3a2": "OPEN_EXACT_GROUND_TRIAL_PROJECTIVE_RATE",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
