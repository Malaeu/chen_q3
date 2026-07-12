#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-29 H2a2 isolation receiver."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H2A2_SECTOR_ISOLATION_RADIUS_CERTIFICATE.json"
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

    require(cert["revision_target"] == 29, "H2A2_CERT_REVISION_DRIFT")
    require(state["revision"] >= 29, "H2A2_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H2A2_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H2A2_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H2A2_SOURCE_{index}")
    pinned(cert["artifact"], "H2A2_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H2A2_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H2A2_LEAN_HOLE")
    require("#print axioms" in proof_text, "H2A2_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H2A2_THEOREM_MISSING:{theorem}")
    for token in (
        "def sectorIsolationRadius",
        "min (epsilonPlus2 - epsilonPlus1)",
        "(epsilonMinus1 - epsilonPlus1) / 2",
        "lt_min",
        "min_le_left",
        "min_le_right",
        "sub_le_sub_right",
        "sectorIsolationRadius_certificate",
    ):
        require(token in proof_text, f"H2A2_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h2a2 = nodes["H2a2"]
    require(h2a2["kind"] == "AND", "H2A2_PARENT_NOT_AND")
    require(h2a2["dependencies"] == ["H2a2.0"], "H2A2_PARENT_DEPENDENCY_DRIFT")
    require(h2a2["ordered_children"] == ["H2a2a", "H2a2b"], "H2A2_CHILD_ORDER_DRIFT")
    require(h2a2["assembly_theorem_id"] == "H2a2c", "H2A2_ASSEMBLY_ADDRESS_DRIFT")
    require(h2a2["proof_status"] == "OPEN", "H2A2_PARENT_FALSE_PASS")
    require("H2A_ISOLATION_RADIUS_MISSING" not in h2a2["failure_codes"], "H2A2_RETIRED_GENERIC_GUARD_STILL_LIVE")
    for code in (
        "H2A_EXACT_SECTOR_ORDERING_MISSING",
        "H2A_EXACT_ISOLATION_RADIUS_INSTANTIATION_MISSING",
        "H2A_SAME_FAMILY_SELECTION_MISSING",
    ):
        require(code in h2a2["failure_codes"], f"H2A2_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h2a2_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H2A2_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H2A2_PROVED_NODE_ACTIVE:{node_id}")
    h2a2a = nodes["H2a2a"]
    require(h2a2a["validation"] == "GENERIC_SECTOR_ISOLATION_RADIUS_LEAN", "H2A2A_VERDICT_DRIFT")
    require(
        h2a2a["proof_artifact"] == "Q3/Proofs/RouteB/SectorIsolationRadius.lean",
        "H2A2A_PROOF_ARTIFACT_DRIFT",
    )

    h2a2b = nodes["H2a2b"]
    require(h2a2b["proof_status"] == "OPEN", "H2A2B_FALSE_PASS")
    require(not h2a2b["eligibility"]["eligible"], "H2A2B_FALSE_ELIGIBILITY")
    require(
        h2a2b["dependencies"] == ["D0.4", "D0.5", "D0.8", "H1c3", "H2a1", "H2a2a"],
        "H2A2B_DEPENDENCY_DRIFT",
    )
    require(
        h2a2b["external_requirements"] == ["H2A_EXACT_SELECTED_FAMILY_SECTOR_GAPS"],
        "H2A2B_EXTERNAL_REQUIREMENT_DRIFT",
    )
    require("H2A_ISOLATION_RADIUS_MISSING" not in h2a2b["failure_codes"], "H2A2B_RETIRED_GENERIC_GUARD_STILL_LIVE")
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in h2a2b["failure_codes"], f"H2A2B_GUARD_MISSING:{code}")

    h2a2c = nodes["H2a2c"]
    require(h2a2c["proof_status"] == "OPEN", "H2A2C_FALSE_PASS")
    require(not h2a2c["eligibility"]["eligible"], "H2A2C_FALSE_ELIGIBILITY")
    require(
        h2a2c["dependencies"] == ["H2a2.0", "H2a2a", "H2a2b"],
        "H2A2C_DEPENDENCY_DRIFT",
    )

    for node_id in ("H2a", "H2a3", "H2", "H4b2", "H4", "L0c2", "L0"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H2A2_COLLATERAL_FALSE_PASS:{node_id}")
    require(nodes["H2b"]["proof_status"] == "CONDITIONAL", "H2A2_H2B_CONDITIONAL_DRIFT")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H2A2_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 29:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H2A2_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H2A2_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H2A2_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H2A2_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H2A2_BUS_010_CREATED")
    require("NO_EVEN_INTERNAL_GAP_PROOF" in cert["explicit_nonclaims"], "H2A2_EXACT_GAP_OVERCLAIM")
    require("NO_H2A2_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H2A2_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H2A2_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H2A2_SECTOR_ISOLATION_RADIUS_REV29_VALID",
        "h2a2a": "GENERIC_SECTOR_ISOLATION_RADIUS_LEAN",
        "h2a2b": "OPEN_EXACT_SELECTED_FAMILY_SECTOR_GAPS",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
