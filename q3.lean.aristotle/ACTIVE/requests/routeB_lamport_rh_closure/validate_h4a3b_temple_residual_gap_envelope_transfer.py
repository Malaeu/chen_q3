#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-33 H4a3b generic rate core."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H4A3B_TEMPLE_RESIDUAL_GAP_ENVELOPE_TRANSFER_CERTIFICATE.json"
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
    require(cert["revision_target"] == 33, "H4A3B_CERT_REVISION_DRIFT")
    require(state["revision"] >= 33, "H4A3B_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H4A3B_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H4A3B_STATE_RH_OVERCLAIM")
    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H4A3B_SOURCE_{index}")
    pinned(cert["artifact"], "H4A3B_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H4A3B_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H4A3B_LEAN_HOLE")
    require("#print axioms" in proof_text, "H4A3B_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H4A3B_THEOREM_MISSING:{theorem}")
    for token in ("rayleigh_excess_le_two_mul_residual_sq_div_gap", "div_le_div₀", "Real.rpow_sub", "field_simp", "[NeBot l]", "filter_upwards", "one_envelope_residual_gap_bounds_do_not_force_safe_alpha"):
        require(token in proof_text, f"H4A3B_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    parent = nodes["H4a3b"]
    require(parent["kind"] == "AND", "H4A3B_PARENT_NOT_AND")
    require(parent["dependencies"] == ["H4a3b.0"], "H4A3B_PARENT_DEPENDENCY_DRIFT")
    require(parent["ordered_children"] == ["H4a3b1", "H4a3b2"], "H4A3B_CHILD_ORDER_DRIFT")
    require(parent["assembly_theorem_id"] == "H4a3b3", "H4A3B_ASSEMBLY_ADDRESS_DRIFT")
    require(parent["proof_status"] == "OPEN", "H4A3B_PARENT_FALSE_PASS")
    require("H4A_RESIDUAL_RATE_TO_ALPHA_RATE_MISSING" not in parent["failure_codes"], "H4A3B_RETIRED_STOP_LIVE")
    for node_id in cert["h4a3b_repair"]["proved"]:
        require(nodes[node_id]["proof_status"] == "PROVED", f"H4A3B_PROVED_NODE_DRIFT:{node_id}")
        require(nodes[node_id]["activity"] == "INACTIVE", f"H4A3B_PROVED_NODE_ACTIVE:{node_id}")
    core = nodes["H4a3b1"]
    require(core["dependencies"] == ["H4a3a"], "H4A3B1_DEPENDENCY_DRIFT")
    require(core["validation"] == "GENERIC_TEMPLE_RESIDUAL_GAP_ENVELOPE_TRANSFER_LEAN", "H4A3B1_VERDICT_DRIFT")
    require(core["proof_artifact"] == "Q3/Proofs/RouteB/TempleResidualGapEnvelopeTransfer.lean", "H4A3B1_ARTIFACT_DRIFT")
    exact = nodes["H4a3b2"]
    require(exact["proof_status"] == "OPEN" and not exact["eligibility"]["eligible"], "H4A3B2_FALSE_PASS")
    require(exact["dependencies"] == cert["exact_instantiation_guard"]["dependencies"], "H4A3B2_DEPENDENCY_DRIFT")
    require(exact["external_requirements"] == cert["exact_instantiation_guard"]["external_requirements"], "H4A3B2_EXTERNAL_REQUIREMENT_DRIFT")
    require("H4A_RESIDUAL_RATE_TO_ALPHA_RATE_MISSING" not in exact["failure_codes"], "H4A3B2_RETIRED_STOP_LIVE")
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in exact["failure_codes"], f"H4A3B2_GUARD_MISSING:{code}")
    assembly = nodes["H4a3b3"]
    require(assembly["proof_status"] == "OPEN" and not assembly["eligibility"]["eligible"], "H4A3B3_FALSE_PASS")
    require(assembly["dependencies"] == ["H4a3b.0", "H4a3b1", "H4a3b2"], "H4A3B3_DEPENDENCY_DRIFT")
    require(nodes["H4a3c"]["dependencies"] == ["H4a3.0", "H4a3a", "H4a3b"], "H4A3C_PARENT_CONSUMER_DRIFT")
    for node_id in ("H4a3c", "H4a3", "H4a", "H4a4", "H4", "H3e", "L0c2", "L0"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H4A3B_COLLATERAL_FALSE_PASS:{node_id}")
    eligible = [node_id for node_id, node in nodes.items() if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]]
    require(eligible == [], f"H4A3B_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")
    counts: dict[str, int] = {}
    for node in nodes.values():
        counts[node["proof_status"]] = counts.get(node["proof_status"], 0) + 1
    if state["revision"] == 33:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H4A3B_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H4A3B_NODE_COUNT_DRIFT:{status}")
    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H4A3B_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H4A3B_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H4A3B_BUS_010_CREATED")
    for nonclaim in ("NO_EXACT_RESIDUAL_SQUARE_ENVELOPE", "NO_EXACT_TRUE_GAP_ENVELOPE", "NO_H4A3B_PARENT_CLOSURE", "NO_RH"):
        require(nonclaim in cert["explicit_nonclaims"], f"H4A3B_NONCLAIM_MISSING:{nonclaim}")
    print(json.dumps({"verdict": "H4A3B_TEMPLE_RESIDUAL_GAP_ENVELOPE_TRANSFER_REV33_VALID", "h4a3b1": "GENERIC_TEMPLE_RESIDUAL_GAP_ENVELOPE_TRANSFER_LEAN", "h4a3b2": "OPEN_EXACT_RESIDUAL_GAP_ENVELOPES", "falsifier": cert["h4a3b_repair"]["falsifier"], "node_counts": counts, "eligible_worker_leaves": eligible, "active_leaf": active[0], "bus_010": "NOT_CREATED", "rh": "NOT_RH"}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
