#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-22 H4a1 residual split."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H4A1_AMBIENT_RESIDUAL_SPLIT_CERTIFICATE.json"
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

    require(cert["revision_target"] == 22, "H4A1_CERT_REVISION_DRIFT")
    require(state["revision"] >= 22, "H4A1_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H4A1_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H4A1_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H4A1_SOURCE_{index}")
    pinned(cert["artifact"], "H4A1_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H4A1_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H4A1_LEAN_HOLE")
    require("#print axioms" in proof_text, "H4A1_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H4A1_THEOREM_MISSING:{theorem}")
    for token in (
        "ambientResidual",
        "compressedResidual",
        "projectionLeakage",
        "abel",
        "coordinateProjection2",
        "swapOperator2",
        "ambientResidual swapOperator2 (1, 0) 0 ≠ 0",
    ):
        require(token in proof_text, f"H4A1_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h4a1 = nodes["H4a1"]
    require(h4a1["kind"] == "AND", "H4A1_PARENT_NOT_AND")
    require(h4a1["ordered_children"] == ["H4a1a", "H4a1b"], "H4A1_CHILD_ORDER_DRIFT")
    require(h4a1["assembly_theorem_id"] == "H4a1c", "H4A1_ASSEMBLY_ADDRESS_DRIFT")
    require(h4a1["proof_status"] == "OPEN", "H4A1_PARENT_FALSE_PASS")
    for code in (
        "RESIDUAL_IDENTITY_MISSING",
        "INTERNAL_RESIDUAL_TAUTOLOGY",
        "H4A1_EXACT_AMBIENT_RESIDUAL_CROSSWALK_MISSING",
    ):
        require(code in h4a1["failure_codes"], f"H4A1_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h4a1_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H4A1_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H4A1_PROVED_NODE_ACTIVE:{node_id}")
    h4a1a = nodes["H4a1a"]
    require(
        h4a1a["validation"] == "GENERIC_AMBIENT_COMPRESSED_RESIDUAL_SPLIT_LEAN",
        "H4A1A_VERDICT_DRIFT",
    )
    require(
        h4a1a["proof_artifact"] == "Q3/Proofs/RouteB/AmbientResidualSplit.lean",
        "H4A1A_PROOF_ARTIFACT_DRIFT",
    )

    h4a1b = nodes["H4a1b"]
    require(h4a1b["proof_status"] == "OPEN", "H4A1B_FALSE_PASS")
    require(not h4a1b["eligibility"]["eligible"], "H4A1B_FALSE_ELIGIBILITY")
    require(h4a1b["dependencies"] == ["D0", "H4a1a"], "H4A1B_DEPENDENCY_DRIFT")
    for code in (
        "H4A1_EXACT_AMBIENT_RESIDUAL_CROSSWALK_MISSING",
        "H4A_OPERATOR_DOMAIN_GAP",
        "H4A_FORM_COMPRESSION_NOT_OPERATOR_COMPRESSION",
        "H4A_TRIAL_RITZ_OBJECT_MISMATCH",
        "H4A1_PROJECTION_NOT_SOURCE_LOCKED",
        "H4A1_LEAKAGE_NORM_RATE_MISSING",
    ):
        require(code in h4a1b["failure_codes"], f"H4A1B_GUARD_MISSING:{code}")

    h4a1c = nodes["H4a1c"]
    require(h4a1c["proof_status"] == "OPEN", "H4A1C_FALSE_PASS")
    require(not h4a1c["eligibility"]["eligible"], "H4A1C_FALSE_ELIGIBILITY")
    require(
        h4a1c["dependencies"] == ["H4a1.0", "H4a1a", "H4a1b"],
        "H4A1C_DEPENDENCY_DRIFT",
    )

    require(nodes["H4a"]["proof_status"] == "OPEN", "H4A_PARENT_FALSE_PASS")
    require(nodes["H4a2"]["proof_status"] == "OPEN", "H4A2_FALSE_PASS")
    require(nodes["H4a3b"]["proof_status"] == "OPEN", "H4A3B_FALSE_PASS")
    require(nodes["H4a4"]["proof_status"] == "OPEN", "H4A4_FALSE_PASS")
    require(nodes["H4"]["proof_status"] == "OPEN", "H4_PARENT_FALSE_PASS")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H4A1_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 22:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H4A1_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H4A1_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H4A1_ACTIVE_LEAF_DRIFT")
    require(
        state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING",
        "H4A1_ACTIVE_STOP_DRIFT",
    )
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H4A1_BUS_010_CREATED")
    require("NO_H4A1_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H4A1_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H4A1_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H4A1_AMBIENT_RESIDUAL_SPLIT_REV22_VALID",
        "h4a1a": "GENERIC_AMBIENT_COMPRESSED_RESIDUAL_SPLIT_LEAN",
        "falsifier": "ZERO_COMPRESSED_RESIDUAL_NONZERO_AMBIENT_RESIDUAL",
        "h4a1b": "OPEN_EXACT_ROUTE_B_AMBIENT_RESIDUAL_CROSSWALK",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
