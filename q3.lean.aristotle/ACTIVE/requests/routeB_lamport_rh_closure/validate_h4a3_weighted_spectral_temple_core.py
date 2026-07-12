#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-19 H4a3 Temple core."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H4A3_WEIGHTED_SPECTRAL_TEMPLE_CORE_CERTIFICATE.json"
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

    require(cert["revision_target"] == 19, "H4A3_CERT_REVISION_DRIFT")
    require(state["revision"] >= 19, "H4A3_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H4A3_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H4A3_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H4A3_SOURCE_{index}")
    pinned(cert["artifact"], "H4A3_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H4A3_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H4A3_LEAN_HOLE")
    require("#print axioms" in proof_text, "H4A3_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H4A3_THEOREM_MISSING:{theorem}")
    for token in (
        "Finset.sum_nonneg",
        "Finset.sum_le_sum",
        "Finset.sum_add_distrib",
        "Finset.sum_sub_distrib",
        "Finset.mul_sum",
        "le_div_iff₀",
        "alpha * (gap - alpha)",
    ):
        require(token in proof_text, f"H4A3_MECHANISM_MISSING:{token}")

    falsifier = pinned(cert["source_pins"][2], "H4A3_FALSIFIER")
    falsifier_text = falsifier.read_text(encoding="utf-8")
    require(FORBIDDEN.search(falsifier_text) is None, "H4A3_FALSIFIER_HOLE")
    require(
        "residual_bridge_direction_counterexample" in falsifier_text,
        "H4A3_FALSE_BRIDGE_PLANT_MISSING",
    )

    nodes = state["nodes"]
    h4a3 = nodes["H4a3"]
    require(h4a3["kind"] == "AND", "H4A3_PARENT_NOT_AND")
    require(h4a3["ordered_children"] == ["H4a3a", "H4a3b"], "H4A3_CHILD_ORDER_DRIFT")
    require(h4a3["assembly_theorem_id"] == "H4a3c", "H4A3_ASSEMBLY_ADDRESS_DRIFT")
    require(h4a3["proof_status"] == "OPEN", "H4A3_PARENT_FALSE_PASS")
    require(
        "PO_XWALK_RESIDUAL_BRIDGE_DIRECTION_FALSE" in h4a3["failure_codes"],
        "H4A3_FALSE_BRIDGE_GUARD_DROPPED",
    )

    for node_id in cert["h4a3_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H4A3_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H4A3_PROVED_NODE_ACTIVE:{node_id}")
    h4a3a = nodes["H4a3a"]
    require(
        h4a3a["validation"] == "WEIGHTED_SPECTRAL_TEMPLE_CORE_LEAN",
        "H4A3A_VERDICT_DRIFT",
    )
    require(
        h4a3a["proof_artifact"] == "Q3/Proofs/RouteB/WeightedSpectralTempleCore.lean",
        "H4A3A_PROOF_ARTIFACT_DRIFT",
    )
    require(nodes["H4a3b"]["proof_status"] == "OPEN", "H4A3B_FALSE_PASS")
    require(not nodes["H4a3b"]["eligibility"]["eligible"], "H4A3B_FALSE_ELIGIBILITY")
    if state["revision"] >= 33:
        h4a3b = nodes["H4a3b"]
        require(h4a3b["kind"] == "AND", "H4A3B_PARENT_NOT_AND")
        require(h4a3b["dependencies"] == ["H4a3b.0"], "H4A3B_PARENT_DEPENDENCY_DRIFT")
        require(h4a3b["ordered_children"] == ["H4a3b1", "H4a3b2"], "H4A3B_CHILD_ORDER_DRIFT")
        require(h4a3b["assembly_theorem_id"] == "H4a3b3", "H4A3B_ASSEMBLY_ADDRESS_DRIFT")
        exact_h4a3b = nodes["H4a3b2"]
        require(exact_h4a3b["proof_status"] == "OPEN", "H4A3B2_FALSE_PASS")
        require(not exact_h4a3b["eligibility"]["eligible"], "H4A3B2_FALSE_ELIGIBILITY")
        require(
            exact_h4a3b["dependencies"] ==
            ["D0", "H2a", "H4a1", "H4a2", "H4b", "H4a3b1"],
            "H4A3B2_DEPENDENCY_DRIFT",
        )
    require(
        "H4A3_EXACT_SPECTRAL_INSTANTIATION_MISSING" in nodes["H4a3b"]["failure_codes"],
        "H4A3B_EXACT_INSTANTIATION_STOP_MISSING",
    )
    require(
        "PO_XWALK_ERROR_SUBSPACE_UNPINNED" in nodes["H4a3b"]["failure_codes"],
        "H4A3B_ERROR_SUBSPACE_GUARD_MISSING",
    )
    require(nodes["H4a3c"]["proof_status"] == "OPEN", "H4A3C_FALSE_PASS")
    require(not nodes["H4a3c"]["eligibility"]["eligible"], "H4A3C_FALSE_ELIGIBILITY")
    require(nodes["H4a"]["proof_status"] == "OPEN", "H4A_PARENT_FALSE_PASS")
    require(nodes["H4a4"]["proof_status"] == "OPEN", "H4A4_FALSE_PASS")
    require(nodes["H4"]["proof_status"] == "OPEN", "H4_PARENT_FALSE_PASS")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H4A3_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")

    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 19:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H4A3_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H4A3_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H4A3_ACTIVE_LEAF_DRIFT")
    require(
        state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING",
        "H4A3_ACTIVE_STOP_DRIFT",
    )
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H4A3_BUS_010_CREATED")
    require("NO_FALSE_BRIDGE_REVIVAL" in cert["explicit_nonclaims"], "H4A3_PLANT_GUARD_MISSING")
    require("NO_RH" in cert["explicit_nonclaims"], "H4A3_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H4A3_WEIGHTED_SPECTRAL_TEMPLE_CORE_REV19_VALID",
        "h4a3a": "WEIGHTED_SPECTRAL_TEMPLE_CORE_LEAN",
        "exact_denominator": "GAP_MINUS_RAYLEIGH_EXCESS",
        "false_bridge": "PRESERVED_KILLED",
        "h4a3b": "OPEN_EXACT_ROUTE_B_SPECTRAL_INSTANTIATION",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
