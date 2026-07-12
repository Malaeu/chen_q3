#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-30 H4a2 envelope receiver."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H4A2_AMBIENT_RESIDUAL_ENVELOPE_TRANSFER_CERTIFICATE.json"
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

    require(cert["revision_target"] == 30, "H4A2_CERT_REVISION_DRIFT")
    require(state["revision"] >= 30, "H4A2_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H4A2_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H4A2_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H4A2_SOURCE_{index}")
    pinned(cert["artifact"], "H4A2_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H4A2_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H4A2_LEAN_HOLE")
    require("#print axioms" in proof_text, "H4A2_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H4A2_THEOREM_MISSING:{theorem}")
    for token in (
        "ambient_residual_eq_compressed_residual_add_leakage",
        "norm_add_le",
        "add_le_add",
        "mul_self_le_mul_self",
        "ambient_residual_norm_eq_leakage_norm_of_compressed_eigen",
        "filter_upwards",
        "[NeBot l]",
    ):
        require(token in proof_text, f"H4A2_MECHANISM_MISSING:{token}")

    falsifier = pinned(cert["source_pins"][4], "H4A2_FALSIFIER")
    falsifier_text = falsifier.read_text(encoding="utf-8")
    require(FORBIDDEN.search(falsifier_text) is None, "H4A2_FALSIFIER_HOLE")
    require(
        "compressed_residual_zero_ambient_residual_nonzero" in falsifier_text,
        "H4A2_LEAKAGE_PLANT_MISSING",
    )

    nodes = state["nodes"]
    h4a2 = nodes["H4a2"]
    require(h4a2["kind"] == "AND", "H4A2_PARENT_NOT_AND")
    require(h4a2["dependencies"] == ["H4a2.0"], "H4A2_PARENT_DEPENDENCY_DRIFT")
    require(h4a2["ordered_children"] == ["H4a2a", "H4a2b"], "H4A2_CHILD_ORDER_DRIFT")
    require(h4a2["assembly_theorem_id"] == "H4a2c", "H4A2_ASSEMBLY_ADDRESS_DRIFT")
    require(h4a2["proof_status"] == "OPEN", "H4A2_PARENT_FALSE_PASS")
    for code in (
        "H4A2_EXACT_COMPONENT_RATE_INSTANTIATION_MISSING",
        "H4A1_LEAKAGE_NORM_RATE_MISSING",
        "H4A2_COMPRESSED_RESIDUAL_RATE_MISSING",
        "H4A_OPERATOR_DOMAIN_GAP",
        "H4A_FORM_COMPRESSION_NOT_OPERATOR_COMPRESSION",
    ):
        require(code in h4a2["failure_codes"], f"H4A2_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h4a2_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H4A2_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H4A2_PROVED_NODE_ACTIVE:{node_id}")
    h4a2a = nodes["H4a2a"]
    require(
        h4a2a["validation"] == "GENERIC_AMBIENT_RESIDUAL_ENVELOPE_TRANSFER_LEAN",
        "H4A2A_VERDICT_DRIFT",
    )
    require(
        h4a2a["proof_artifact"] == "Q3/Proofs/RouteB/AmbientResidualEnvelopeTransfer.lean",
        "H4A2A_PROOF_ARTIFACT_DRIFT",
    )

    h4a2b = nodes["H4a2b"]
    require(h4a2b["proof_status"] == "OPEN", "H4A2B_FALSE_PASS")
    require(not h4a2b["eligibility"]["eligible"], "H4A2B_FALSE_ELIGIBILITY")
    require(h4a2b["dependencies"] == ["D0", "H4a1", "H4a2a"], "H4A2B_DEPENDENCY_DRIFT")
    require(
        h4a2b["external_requirements"] == ["H4A2_EXACT_COMPONENT_RATE"],
        "H4A2B_EXTERNAL_REQUIREMENT_DRIFT",
    )
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in h4a2b["failure_codes"], f"H4A2B_GUARD_MISSING:{code}")

    h4a2c = nodes["H4a2c"]
    require(h4a2c["proof_status"] == "OPEN", "H4A2C_FALSE_PASS")
    require(not h4a2c["eligibility"]["eligible"], "H4A2C_FALSE_ELIGIBILITY")
    require(h4a2c["dependencies"] == ["H4a2.0", "H4a2a", "H4a2b"], "H4A2C_DEPENDENCY_DRIFT")

    for node_id in ("H4a", "H4a3b", "H4a4", "H4", "H3e", "L0c2", "L0"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H4A2_COLLATERAL_FALSE_PASS:{node_id}")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H4A2_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 30:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H4A2_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H4A2_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H4A2_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H4A2_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H4A2_BUS_010_CREATED")
    require("NO_EXACT_COMPRESSED_RESIDUAL_RATE" in cert["explicit_nonclaims"], "H4A2_COMPRESSED_RATE_OVERCLAIM")
    require("NO_EXACT_LEAKAGE_RATE" in cert["explicit_nonclaims"], "H4A2_LEAKAGE_RATE_OVERCLAIM")
    require("NO_H4A2_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H4A2_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H4A2_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H4A2_AMBIENT_RESIDUAL_ENVELOPE_TRANSFER_REV30_VALID",
        "h4a2a": "GENERIC_AMBIENT_RESIDUAL_ENVELOPE_TRANSFER_LEAN",
        "h4a2b": "OPEN_EXACT_COMPONENT_RATE_INSTANTIATION",
        "falsifier": cert["h4a2_repair"]["falsifier"],
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
