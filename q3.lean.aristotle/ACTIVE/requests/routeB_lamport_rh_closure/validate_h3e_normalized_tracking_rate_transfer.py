#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-31 H3e generic rate transfer."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H3E_NORMALIZED_TRACKING_RATE_TRANSFER_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"
FORBIDDEN = re.compile(r"\b(sorry|admit)\b|exact\?")
FORBIDDEN_MINT = re.compile(
    r"(?:def|abbrev)\s+(?:WPrime|alpha|DeltaE)\b|\b(?:WPrime|alpha|DeltaE)\s*:="
)


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

    require(cert["revision_target"] == 31, "H3E_CERT_REVISION_DRIFT")
    require(state["revision"] >= 31, "H3E_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H3E_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H3E_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H3E_SOURCE_{index}")
    pinned(cert["artifact"], "H3E_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H3E_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H3E_LEAN_HOLE")
    require(FORBIDDEN_MINT.search(proof_text) is None, "H3E_FORBIDDEN_OBJECT_MINT")
    require("#print axioms" in proof_text, "H3E_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H3E_THEOREM_MISSING:{theorem}")
    for token in (
        "two_sided_normalized_b_control_eventually",
        "b⁻¹ • (F - b • X)",
        "norm_smul",
        "norm_inv",
        "Metric.tendstoUniformlyOn_iff",
        "[NeBot l]",
        "R i * W i",
        "R i * eps i",
        "safe_margin_does_not_imply_relative_rate_margin",
        "detector_decay_does_not_imply_relative_decay",
    ):
        require(token in proof_text, f"H3E_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h3e = nodes["H3e"]
    require(h3e["kind"] == "AND", "H3E_PARENT_NOT_AND")
    require(h3e["dependencies"] == ["H3e.0"], "H3E_PARENT_DEPENDENCY_DRIFT")
    require(h3e["ordered_children"] == ["H3e1", "H3e2"], "H3E_CHILD_ORDER_DRIFT")
    require(h3e["assembly_theorem_id"] == "H3e3", "H3E_ASSEMBLY_ADDRESS_DRIFT")
    require(h3e["proof_status"] == "OPEN", "H3E_PARENT_FALSE_PASS")
    require(h3e["consumes_slot"] == "D0.7e.5", "H3E_SLOT_DRIFT")
    require(h3e["consumer_identity_dependency"] == "D0.7e.5c", "H3E_CONSUMER_DEPENDENCY_DRIFT")
    for code in (
        "D0_7E_WPRIME_CONSUMER_MISSING",
        "H3E_EXACT_RELATIVE_TRACKING_INPUTS_MISSING",
        "H3E_RELATIVE_WPRIME_RATE_MARGIN_MISSING",
        "H3E_RELATIVE_RESIDUAL_RATE_MISSING",
        "H3E_ABSOLUTE_TO_NORMALIZED_ERROR_GAP",
        "H3E_IB2_LIMINF_MISIDENTIFICATION",
    ):
        require(code in h3e["failure_codes"], f"H3E_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h3e_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H3E_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H3E_PROVED_NODE_ACTIVE:{node_id}")
    h3e1 = nodes["H3e1"]
    require(
        h3e1["validation"] == "H3E_GENERIC_NORMALIZED_TRACKING_RATE_TRANSFER_LEAN",
        "H3E1_VERDICT_DRIFT",
    )
    require(
        h3e1["proof_artifact"] == "Q3/Proofs/RouteB/NormalizedTrackingRateTransfer.lean",
        "H3E1_PROOF_ARTIFACT_DRIFT",
    )
    for code in (
        "H3E_BOTTOM_FILTER_VACUITY",
        "H3E_DETECTOR_DECAY_ONLY_PLANT",
        "H3E_SAFE_MARGIN_ONLY_PLANT",
        "H3E_WPRIME_MINTED_IN_GENERIC_CORE",
    ):
        require(code in h3e1["failure_codes"], f"H3E1_GUARD_MISSING:{code}")

    h3e2 = nodes["H3e2"]
    require(h3e2["proof_status"] == "OPEN", "H3E2_FALSE_PASS")
    require(not h3e2["eligibility"]["eligible"], "H3E2_FALSE_ELIGIBILITY")
    require(
        h3e2["dependencies"] == ["D0", "H3a", "H3b", "H3c", "H4b", "H4c", "H3e1"],
        "H3E2_DEPENDENCY_DRIFT",
    )
    require(
        h3e2["external_requirements"] == ["PO-1/A1", "PO_XWALK_UNIFORM_EVAL", "H3E_RELATIVE_NORMALIZATION_TRANSFER"],
        "H3E2_EXTERNAL_REQUIREMENT_DRIFT",
    )
    require(h3e2["consumes_slot"] == "D0.7e.5", "H3E2_SLOT_DRIFT")
    require(h3e2["consumer_identity_dependency"] == "D0.7e.5c", "H3E2_CONSUMER_DEPENDENCY_DRIFT")
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in h3e2["failure_codes"], f"H3E2_GUARD_MISSING:{code}")

    h3e3 = nodes["H3e3"]
    require(h3e3["proof_status"] == "OPEN", "H3E3_FALSE_PASS")
    require(not h3e3["eligibility"]["eligible"], "H3E3_FALSE_ELIGIBILITY")
    require(h3e3["dependencies"] == ["H3e.0", "H3e1", "H3e2"], "H3E3_DEPENDENCY_DRIFT")

    for node_id in ("H3b2", "H3c2", "H4c2", "H4c", "H4", "H3", "H3d", "L0c2", "L0c3", "L0"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H3E_COLLATERAL_FALSE_PASS:{node_id}")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H3E_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 31:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H3E_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H3E_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H3E_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H3E_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H3E_BUS_010_CREATED")
    for nonclaim in (
        "NO_WPRIME_DEFINITION_OR_RECONSTRUCTION",
        "NO_EXACT_RELATIVE_WPRIME_RATE",
        "NO_EXACT_RELATIVE_RESIDUAL_RATE",
        "NO_CURRENT_CONTRACT_MARGIN_IMPLICATION",
        "NO_H3E_PARENT_CLOSURE",
        "NO_RH",
    ):
        require(nonclaim in cert["explicit_nonclaims"], f"H3E_NONCLAIM_MISSING:{nonclaim}")

    print(json.dumps({
        "verdict": "H3E_NORMALIZED_TRACKING_RATE_TRANSFER_REV31_VALID",
        "h3e1": "H3E_GENERIC_NORMALIZED_TRACKING_RATE_TRANSFER_LEAN",
        "h3e2": "OPEN_EXACT_RELATIVE_TRACKING_INPUTS",
        "plants": cert["plants"],
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
