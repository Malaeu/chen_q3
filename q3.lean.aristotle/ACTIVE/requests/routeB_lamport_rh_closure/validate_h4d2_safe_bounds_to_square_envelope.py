#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-23 H4d2 square envelope."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H4D2_SAFE_BOUNDS_TO_SQUARE_ENVELOPE_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"
FORBIDDEN = re.compile(r"\b(sorry|admit)\b|exact\?")
WPRIME_MINT = re.compile(r"\b(?:def|abbrev)\s+WPrime\b|\bWPrime\s*:=")


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

    require(cert["revision_target"] == 23, "H4D2_CERT_REVISION_DRIFT")
    require(state["revision"] >= 23, "H4D2_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H4D2_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H4D2_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H4D2_SOURCE_{index}")
    pinned(cert["artifact"], "H4D2_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H4D2_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H4D2_LEAN_HOLE")
    require(WPRIME_MINT.search(proof_text) is None, "H4D2_WPRIME_MINTED")
    require("#print axioms" in proof_text, "H4D2_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H4D2_THEOREM_MISSING:{theorem}")
    for token in (
        "div_le_div₀",
        "Real.rpow_sub",
        "sq_le_sq₀",
        "Real.sq_sqrt",
        "Real.rpow_mul_natCast",
        "filter_upwards",
        "(hW : W ^ 2 = |b| ^ 2 * scale * alpha / gap)",
    ):
        require(token in proof_text, f"H4D2_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h4d2 = nodes["H4d2"]
    require(h4d2["kind"] == "AND", "H4D2_PARENT_NOT_AND")
    require(h4d2["dependencies"] == ["H4d2.0"], "H4D2_PARENT_DEPENDENCY_DRIFT")
    require(h4d2["ordered_children"] == ["H4d2a", "H4d2b"], "H4D2_CHILD_ORDER_DRIFT")
    require(h4d2["assembly_theorem_id"] == "H4d2c", "H4D2_ASSEMBLY_ADDRESS_DRIFT")
    require(h4d2["proof_status"] == "OPEN", "H4D2_PARENT_FALSE_PASS")
    for code in (
        "H4D_WPRIME_SQUARE_ENVELOPE_MISSING",
        "H4D_EXACT_SQUARE_ENVELOPE_INSTANTIATION_MISSING",
        "H4_LIMIT_FILTER_UNSELECTED",
    ):
        require(code in h4d2["failure_codes"], f"H4D2_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h4d2_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H4D2_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H4D2_PROVED_NODE_ACTIVE:{node_id}")
    h4d2a = nodes["H4d2a"]
    require(
        h4d2a["validation"] == "GENERIC_SAFE_BOUNDS_TO_SQUARE_ENVELOPE_LEAN",
        "H4D2A_VERDICT_DRIFT",
    )
    require(
        h4d2a["proof_artifact"] == "Q3/Proofs/RouteB/SafeBoundsToSquareEnvelope.lean",
        "H4D2A_PROOF_ARTIFACT_DRIFT",
    )

    h4d2b = nodes["H4d2b"]
    require(h4d2b["proof_status"] == "OPEN", "H4D2B_FALSE_PASS")
    require(not h4d2b["eligibility"]["eligible"], "H4D2B_FALSE_ELIGIBILITY")
    require(
        h4d2b["dependencies"] == ["D0.7e.5c", "H4a", "H4b", "H4c"],
        "H4D2B_DEPENDENCY_DRIFT",
    )
    require(h4d2b["external_requirements"] == ["H4_JOINT_FILTER"], "H4D2B_FILTER_DRIFT")
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in h4d2b["failure_codes"], f"H4D2B_GUARD_MISSING:{code}")

    h4d2c = nodes["H4d2c"]
    require(h4d2c["proof_status"] == "OPEN", "H4D2C_FALSE_PASS")
    require(not h4d2c["eligibility"]["eligible"], "H4D2C_FALSE_ELIGIBILITY")
    require(
        h4d2c["dependencies"] == ["H4d2.0", "H4d2a", "H4d2b"],
        "H4D2C_DEPENDENCY_DRIFT",
    )

    require(nodes["H4d3"]["dependencies"] == ["H4d.0", "H4d1", "H4d2"], "H4D3_DEPENDENCY_DRIFT")
    require(nodes["H4d3"]["proof_status"] == "OPEN", "H4D3_FALSE_PASS")
    require(nodes["H4d"]["proof_status"] == "OPEN", "H4D_PARENT_FALSE_PASS")
    require(nodes["H4"]["proof_status"] == "OPEN", "H4_PARENT_FALSE_PASS")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H4D2_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 23:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H4D2_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H4D2_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H4D2_ACTIVE_LEAF_DRIFT")
    require(
        state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING",
        "H4D2_ACTIVE_STOP_DRIFT",
    )
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H4D2_BUS_010_CREATED")
    require(
        "NO_WPRIME_DEFINITION_FROM_TARGET_IDENTITY" in cert["explicit_nonclaims"],
        "H4D2_TAUTOLOGY_FIREWALL_DROPPED",
    )
    require("NO_H4D2_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H4D2_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H4D2_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H4D2_SAFE_BOUNDS_TO_SQUARE_ENVELOPE_REV23_VALID",
        "h4d2a": "GENERIC_SAFE_BOUNDS_TO_SQUARE_ENVELOPE_LEAN",
        "h4d2b": "OPEN_EXACT_SAFE_INPUTS_AND_JOINT_FILTER",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
