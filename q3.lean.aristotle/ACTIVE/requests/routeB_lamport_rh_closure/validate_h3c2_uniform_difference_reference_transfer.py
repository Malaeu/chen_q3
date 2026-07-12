#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-36 H3c2 generic core."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H3C2_UNIFORM_DIFFERENCE_REFERENCE_TRANSFER_CERTIFICATE.json"
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

    require(cert["revision_target"] == 36, "H3C2_CERT_REVISION_DRIFT")
    require(state["revision"] >= 36, "H3C2_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H3C2_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H3C2_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H3C2_SOURCE_{index}")
    pinned(cert["artifact"], "H3C2_ARTIFACT")
    proof_path = pinned(cert["proof_artifact"], "H3C2_LEAN")
    proof_text = proof_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(proof_text) is None, "H3C2_LEAN_HOLE")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in proof_text, f"H3C2_THEOREM_MISSING:{theorem}")
    for token in (
        "TendstoUniformlyOn",
        "TendstoLocallyUniformlyOn",
        "hdiff.add href",
        "tendstoLocallyUniformlyOn_iff_forall_isCompact",
        "LocallyCompactSpace",
        "IsOpen",
        "#print axioms",
    ):
        require(token in proof_text, f"H3C2_MECHANISM_MISSING:{token}")

    nodes = state["nodes"]
    parent = nodes["H3c2"]
    require(parent["kind"] == "AND", "H3C2_PARENT_NOT_AND")
    require(parent["dependencies"] == ["H3c2.0"], "H3C2_PARENT_DEPENDENCY_DRIFT")
    require(parent["ordered_children"] == ["H3c2a", "H3c2b"], "H3C2_CHILD_ORDER_DRIFT")
    require(parent["assembly_theorem_id"] == "H3c2c", "H3C2_ASSEMBLY_ADDRESS_DRIFT")
    require(parent["proof_status"] == "OPEN", "H3C2_PARENT_FALSE_PASS")

    for node_id in cert["h3c2_repair"]["proved"]:
        node = nodes[node_id]
        require(node["proof_status"] == "PROVED", f"H3C2_PROVED_NODE_DRIFT:{node_id}")
        require(node["activity"] == "INACTIVE", f"H3C2_PROVED_NODE_ACTIVE:{node_id}")
    require(
        nodes["H3c2a"]["validation"]
        == "H3C2_GENERIC_DIFFERENCE_REFERENCE_LIMIT_TRANSFER_LEAN",
        "H3C2A_VERDICT_DRIFT",
    )
    require(
        nodes["H3c2a"]["proof_artifact"]
        == "Q3/Proofs/RouteB/UniformDifferenceReferenceTransfer.lean",
        "H3C2A_PROOF_ARTIFACT_DRIFT",
    )

    exact = nodes["H3c2b"]
    require(exact["proof_status"] == "OPEN", "H3C2B_FALSE_PASS")
    require(not exact["eligibility"]["eligible"], "H3C2B_FALSE_ELIGIBILITY")
    require(
        exact["dependencies"] == cert["exact_instantiation_guard"]["dependencies"],
        "H3C2B_DEPENDENCY_DRIFT",
    )
    require(
        exact["external_requirements"] == [cert["exact_instantiation_guard"]["external_requirement"]],
        "H3C2B_EXTERNAL_REQUIREMENT_DRIFT",
    )
    for code in cert["exact_instantiation_guard"]["open_codes"]:
        require(code in exact["failure_codes"], f"H3C2B_GUARD_MISSING:{code}")

    assembly = nodes["H3c2c"]
    require(assembly["proof_status"] == "OPEN", "H3C2C_FALSE_PASS")
    require(not assembly["eligibility"]["eligible"], "H3C2C_FALSE_ELIGIBILITY")
    require(
        assembly["dependencies"] == ["H3c2.0", "H3c2a", "H3c2b"],
        "H3C2C_DEPENDENCY_DRIFT",
    )
    require(nodes["H3c"]["proof_status"] == "OPEN", "H3C_PARENT_FALSE_PASS")
    require(nodes["H3c3"]["dependencies"] == ["H3c.0", "H3c1", "H3c2"], "H3C3_CONSUMER_DRIFT")

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"H3C2_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")
    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    if state["revision"] == 36:
        expected = cert["expected_node_counts"]
        require(len(nodes) == expected["total"], "H3C2_NODE_TOTAL_DRIFT")
        for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
            require(counts.get(status, 0) == expected[status], f"H3C2_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H3C2_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H3C2_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H3C2_BUS_010_CREATED")
    require("NO_EXACT_XI_LIMIT_IDENTIFICATION" in cert["explicit_nonclaims"], "H3C2_XI_OVERCLAIM")
    require("NO_RH" in cert["explicit_nonclaims"], "H3C2_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H3C2_UNIFORM_DIFFERENCE_REFERENCE_TRANSFER_REV36_VALID",
        "h3c2a": "H3C2_GENERIC_DIFFERENCE_REFERENCE_LIMIT_TRANSFER_LEAN",
        "h3c2b": "OPEN_EXACT_REFERENCE_XI_LIMIT_AND_CROSSWALK",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
