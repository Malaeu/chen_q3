#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-24 H3c strip guard."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H3C_DOUBLE_COMPLETION_STRIP_GUARD_CERTIFICATE.json"
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

    require(cert["revision_target"] == 24, "H3C_CERT_REVISION_DRIFT")
    require(state["revision"] >= 24, "H3C_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H3C_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H3C_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H3C_SOURCE_{index}")
    pinned(cert["artifact"], "H3C_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H3C_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H3C_LEAN_HOLE")
    require("#print axioms" in proof_text, "H3C_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H3C_THEOREM_MISSING:{theorem}")
    for token in (
        "normalizedDoubleCompletedXi",
        "gammaC_half_ne_zero",
        "Complex.differentiableAt_Gamma",
        "comp_of_eq",
        "const_cpow",
        "Metric.mem_closure_iff",
        "mem_closure_iff_nhdsWithin_neBot",
        "tendsto_nhds_unique_of_eventuallyEq",
        "centered_argument_neg_I_div_two",
        "gammaC_one",
        "riemannXi_one",
        "Set.EqOn",
        "push_neg",
    ):
        require(token in proof_text, f"H3C_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    h3c = nodes["H3c"]
    require(h3c["kind"] == "AND", "H3C_PARENT_NOT_AND")
    require(h3c["dependencies"] == ["H3c.0"], "H3C_PARENT_DEPENDENCY_DRIFT")
    require(h3c["ordered_children"] == ["H3c1", "H3c2"], "H3C_CHILD_ORDER_DRIFT")
    require(h3c["assembly_theorem_id"] == "H3c3", "H3C_ASSEMBLY_ADDRESS_DRIFT")
    require(h3c["proof_status"] == "OPEN", "H3C_PARENT_FALSE_PASS")
    require("H3C_DOUBLE_COMPLETION_NOT_EXCLUDED" not in h3c["failure_codes"], "H3C_RETIRED_GUARD_STILL_LIVE")
    for code in (
        "H3C_RAW_OR_INVERSE_COMPLETION_SELECTION_MISSING",
        "H3C_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER_MISSING",
        "XI_LIMIT_OBJECT_MISMATCH",
        "XI_LIMIT_IDENTIFICATION_MISSING",
    ):
        require(code in h3c["failure_codes"], f"H3C_PARENT_GUARD_MISSING:{code}")

    for node_id in cert["h3c_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H3C_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H3C_PROVED_NODE_ACTIVE:{node_id}")
    h3c1 = nodes["H3c1"]
    require(
        h3c1["validation"] == "H3C_NORMALIZED_DOUBLE_COMPLETION_STRIP_MISMATCH_LEAN",
        "H3C1_VERDICT_DRIFT",
    )
    require(
        h3c1["proof_artifact"] == "Q3/Proofs/RouteB/DoubleCompletionStripMismatch.lean",
        "H3C1_PROOF_ARTIFACT_DRIFT",
    )
    require(h3c1["dependencies"] == ["C0", "D0.7e.2", "D0.7e.3"], "H3C1_DEPENDENCY_DRIFT")

    h3c2 = nodes["H3c2"]
    require(h3c2["proof_status"] == "OPEN", "H3C2_FALSE_PASS")
    require(not h3c2["eligibility"]["eligible"], "H3C2_FALSE_ELIGIBILITY")
    require(h3c2["dependencies"] == ["D0", "H3a", "H3b", "H3c1"], "H3C2_DEPENDENCY_DRIFT")
    require(h3c2["external_requirements"] == ["H3C_COMPLETION_OBJECT_CROSSWALK"], "H3C2_EXTERNAL_REQUIREMENT_DRIFT")
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in h3c2["failure_codes"], f"H3C2_GUARD_MISSING:{code}")

    h3c3 = nodes["H3c3"]
    require(h3c3["proof_status"] == "OPEN", "H3C3_FALSE_PASS")
    require(not h3c3["eligibility"]["eligible"], "H3C3_FALSE_ELIGIBILITY")
    require(h3c3["dependencies"] == ["H3c.0", "H3c1", "H3c2"], "H3C3_DEPENDENCY_DRIFT")

    for node_id in ("H3", "H3d", "H3e", "L0c2", "L0c3", "L0", "L0d"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H3C_COLLATERAL_FALSE_PASS:{node_id}")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H3C_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 24:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H3C_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H3C_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H3C_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H3C_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H3C_BUS_010_CREATED")
    require("NO_H3C_PARENT_CLOSURE" in cert["explicit_nonclaims"], "H3C_PARENT_GUARD_DROPPED")
    require("NO_EXACT_XI_LIMIT_IDENTIFICATION" in cert["explicit_nonclaims"], "H3C_EXACT_LIMIT_OVERCLAIM")
    require("NO_RH" in cert["explicit_nonclaims"], "H3C_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H3C_DOUBLE_COMPLETION_STRIP_GUARD_REV24_VALID",
        "h3c1": "H3C_NORMALIZED_DOUBLE_COMPLETION_STRIP_MISMATCH_LEAN",
        "h3c2": "OPEN_EXACT_LIMIT_OBJECT_AND_JOINT_FILTER",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH"
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
