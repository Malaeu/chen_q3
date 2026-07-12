#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-18 L0c generic zero transfer."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "L0C_GENERIC_ZERO_TRANSFER_CERTIFICATE.json"
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

    require(cert["revision_target"] == 18, "L0C_CERT_REVISION_DRIFT")
    require(state["revision"] >= 18, "L0C_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "L0C_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "L0C_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"L0C_SOURCE_{index}")
    pinned(cert["artifact"], "L0C_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "L0C_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "L0C_LEAN_HOLE")
    require("#print axioms" in proof_text, "L0C_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"L0C_THEOREM_MISSING:{theorem}")
    for token in (
        "ball_subset_image_closedBall",
        "eventually_eq_zero_or_eventually_ne_zero",
        "exists_isMinOn",
        "Nat.findGreatest",
        "Nat.le_findGreatest",
        "tendsto_one_div_add_atTop_nhds_zero_nat",
        "ZerosApproachOn",
    ):
        require(token in proof_text, f"L0C_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    l0c = nodes["L0c"]
    require(l0c["kind"] == "AND", "L0C_PARENT_NOT_AND")
    require(l0c["ordered_children"] == ["L0c1", "L0c2"], "L0C_CHILD_ORDER_DRIFT")
    require(l0c["assembly_theorem_id"] == "L0c3", "L0C_ASSEMBLY_ADDRESS_DRIFT")
    require(l0c["proof_status"] == "OPEN", "L0C_PARENT_FALSE_PASS")

    for node_id in cert["l0c_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"L0C_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"L0C_PROVED_NODE_ACTIVE:{node_id}")
    l0c1 = nodes["L0c1"]
    require(
        l0c1["validation"] == "GENERIC_ROUCHE_HURWITZ_ZERO_TRANSFER_LEAN",
        "L0C1_VERDICT_DRIFT",
    )
    require(
        l0c1["proof_artifact"] == "Q3/Proofs/RouteB/GenericZeroTransfer.lean",
        "L0C1_PROOF_ARTIFACT_DRIFT",
    )
    require(nodes["L0c2"]["proof_status"] == "OPEN", "L0C2_FALSE_PASS")
    require(not nodes["L0c2"]["eligibility"]["eligible"], "L0C2_FALSE_ELIGIBILITY")
    require(
        "L0C_EXACT_FAMILY_INSTANTIATION_MISSING" in nodes["L0c2"]["failure_codes"],
        "L0C2_EXACT_FAMILY_STOP_MISSING",
    )
    require(
        "XI_LIMIT_OBJECT_MISMATCH" in nodes["L0c2"]["failure_codes"],
        "L0C2_XI_LIMIT_GUARD_MISSING",
    )
    require(nodes["L0c3"]["proof_status"] == "OPEN", "L0C3_FALSE_PASS")
    require(not nodes["L0c3"]["eligibility"]["eligible"], "L0C3_FALSE_ELIGIBILITY")
    require(nodes["L0"]["proof_status"] == "OPEN", "L0_PARENT_FALSE_PASS")
    require(nodes["L0d"]["proof_status"] == "OPEN", "L0D_FALSE_PASS")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"L0C_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 18:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "L0C_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"L0C_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "L0C_ACTIVE_LEAF_DRIFT")
    require(
        state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING",
        "L0C_ACTIVE_STOP_DRIFT",
    )
    require(not any(BUS_DIR.glob("010_*.goal.md")), "L0C_BUS_010_CREATED")
    require("NO_HIDDEN_SUBSEQUENCE" in cert["explicit_nonclaims"], "L0C_FILTER_GUARD_MISSING")
    require("NO_RH" in cert["explicit_nonclaims"], "L0C_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "L0C_GENERIC_ZERO_TRANSFER_REV18_VALID",
        "l0c1": "GENERIC_ROUCHE_HURWITZ_ZERO_TRANSFER_LEAN",
        "full_tail": "ORIGINAL_NAT_INDEX_EVENTUAL_ZEROS",
        "l0c2": "OPEN_EXACT_ROUTE_B_FAMILY_INSTANTIATION",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
