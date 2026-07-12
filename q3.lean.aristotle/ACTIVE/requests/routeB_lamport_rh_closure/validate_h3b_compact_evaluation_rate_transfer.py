#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-21 H3b generic transfer."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H3B_COMPACT_EVALUATION_RATE_TRANSFER_CERTIFICATE.json"
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

    require(cert["revision_target"] == 21, "H3B_CERT_REVISION_DRIFT")
    require(state["revision"] >= 21, "H3B_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H3B_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H3B_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H3B_SOURCE_{index}")
    pinned(cert["artifact"], "H3B_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H3B_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H3B_LEAN_HOLE")
    require("#print axioms" in proof_text, "H3B_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H3B_THEOREM_MISSING:{theorem}")
    for token in (
        "Metric.tendstoUniformlyOn_iff",
        "tendsto_order.1",
        "filter_upwards",
        "tendstoLocallyUniformlyOn_iff_forall_isCompact",
        "TendstoUniformlyOn",
        "tendsto_nhds_unique",
    ):
        require(token in proof_text, f"H3B_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h3b = nodes["H3b"]
    require(h3b["kind"] == "AND", "H3B_PARENT_NOT_AND")
    require(h3b["ordered_children"] == ["H3b1", "H3b2"], "H3B_CHILD_ORDER_DRIFT")
    require(h3b["assembly_theorem_id"] == "H3b3", "H3B_ASSEMBLY_ADDRESS_DRIFT")
    require(h3b["proof_status"] == "OPEN", "H3B_PARENT_FALSE_PASS")
    for code in (
        "COMPACT_STRIP_EVALUATION_MISSING",
        "H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING",
        "PO_XWALK_UNIFORM_EVAL",
    ):
        require(code in h3b["failure_codes"], f"H3B_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h3b_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H3B_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H3B_PROVED_NODE_ACTIVE:{node_id}")
    h3b1 = nodes["H3b1"]
    require(
        h3b1["validation"] == "GENERIC_COMPACT_EVALUATION_RATE_TRANSFER_LEAN",
        "H3B1_VERDICT_DRIFT",
    )
    require(
        h3b1["proof_artifact"] == "Q3/Proofs/RouteB/CompactEvaluationRateTransfer.lean",
        "H3B1_PROOF_ARTIFACT_DRIFT",
    )

    h3b2 = nodes["H3b2"]
    require(h3b2["proof_status"] == "OPEN", "H3B2_FALSE_PASS")
    require(not h3b2["eligibility"]["eligible"], "H3B2_FALSE_ELIGIBILITY")
    if state["revision"] >= 32:
        require(h3b2["kind"] == "AND", "H3B2_PARENT_NOT_AND")
        require(h3b2["dependencies"] == ["H3b2.0"], "H3B2_DEPENDENCY_DRIFT")
        require(h3b2["ordered_children"] == ["H3b2a", "H3b2b"], "H3B2_CHILD_ORDER_DRIFT")
        require(h3b2["assembly_theorem_id"] == "H3b2c", "H3B2_ASSEMBLY_ADDRESS_DRIFT")
        require(nodes["H3b2b"]["dependencies"] == ["D0", "H3a", "H3b2a"], "H3B2B_DEPENDENCY_DRIFT")
    else:
        require(h3b2["dependencies"] == ["D0", "H3a", "H3b1"], "H3B2_DEPENDENCY_DRIFT")
    for code in (
        "H3B_EXACT_WEIGHTED_RATE_INSTANTIATION_MISSING",
        "H3B_UNIFORM_COMPACT_ENVELOPE_MISSING",
        "H3B_WEIGHTED_ERROR_RATE_MISSING",
        "H3B_SAME_FAMILY_FILTER_MISSING",
        "PO_XWALK_UNIFORM_EVAL",
    ):
        require(code in h3b2["failure_codes"], f"H3B2_GUARD_MISSING:{code}")

    h3b3 = nodes["H3b3"]
    require(h3b3["proof_status"] == "OPEN", "H3B3_FALSE_PASS")
    require(not h3b3["eligibility"]["eligible"], "H3B3_FALSE_ELIGIBILITY")
    require(
        h3b3["dependencies"] == ["H3b.0", "H3b1", "H3b2"],
        "H3B3_DEPENDENCY_DRIFT",
    )

    require(nodes["H3"]["proof_status"] == "OPEN", "H3_PARENT_FALSE_PASS")
    require(nodes["H3a"]["proof_status"] == "OPEN", "H3A_FALSE_PASS")
    require(nodes["H3c"]["proof_status"] == "OPEN", "H3C_FALSE_PASS")
    require(nodes["H3e"]["proof_status"] == "OPEN", "H3E_FALSE_PASS")
    require(nodes["H3d"]["proof_status"] == "OPEN", "H3D_FALSE_PASS")
    require(nodes["H4a3b"]["proof_status"] == "OPEN", "H4A3B_COLLATERAL_FALSE_PASS")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H3B_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 21:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H3B_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H3B_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H3B_ACTIVE_LEAF_DRIFT")
    require(
        state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING",
        "H3B_ACTIVE_STOP_DRIFT",
    )
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H3B_BUS_010_CREATED")
    require("NO_H3B_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H3B_PARENT_GUARD_DROPPED")
    require("NO_RH" in cert["explicit_nonclaims"], "H3B_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H3B_COMPACT_EVALUATION_RATE_TRANSFER_REV21_VALID",
        "h3b1": "GENERIC_COMPACT_EVALUATION_RATE_TRANSFER_LEAN",
        "falsifier": "FIXED_BOUND_WITHOUT_VANISHING_RATE_NOT_UNIFORM_ZERO",
        "h3b2": "OPEN_EXACT_WEIGHTED_RATE_INSTANTIATION",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
