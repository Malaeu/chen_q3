#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-41 generic-frontier audit."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "GENERIC_FRONTIER_EXHAUSTION_AUDIT_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"


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

    require(cert["revision_target"] == 41, "FRONTIER_AUDIT_CERT_REVISION_DRIFT")
    require(state["revision"] >= 41, "FRONTIER_AUDIT_STATE_REVISION_TOO_OLD")
    require(cert["verdict"] == "GENERIC_FRONTIER_EXHAUSTED", "FRONTIER_AUDIT_VERDICT_DRIFT")
    require(cert["rh_status"] == "NOT_RH", "FRONTIER_AUDIT_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "FRONTIER_AUDIT_STATE_RH_OVERCLAIM")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"FRONTIER_AUDIT_SOURCE_{index}")
    artifact_path = pinned(cert["artifact"], "FRONTIER_AUDIT_ARTIFACT")
    artifact_text = artifact_path.read_text(encoding="utf-8")
    for token in (
        "GENERIC_FRONTIER_EXHAUSTED",
        "ASSEMBLY_ONLY_NO_EXACT_BLOCK_DECOMPOSITION",
        "D0_7E_WPRIME_CONSUMER_MISSING",
        "H2B2B2_EXACT_WEIL_POSITIVITY_AND_RADICAL_INSTANTIATION_MISSING",
        "SUPPLY_AND_RATIFY_A_NEW_NONTAUTOLOGICAL_WPRIME_CONSUMER_DEFINITION_WITH_EXACT_B_ORIENTATION",
        "NOT_RH",
    ):
        require(token in artifact_text, f"FRONTIER_AUDIT_TOKEN_MISSING:{token}")

    transaction = state["generic_frontier_exhaustion_audit"]
    require(transaction["verdict"] == "GENERIC_FRONTIER_EXHAUSTED", "FRONTIER_AUDIT_STATE_VERDICT_DRIFT")
    require(transaction["next_worker_leaf"] is None, "FRONTIER_AUDIT_FALSE_NEXT_WORKER")
    require(transaction["active_leaf_unchanged"] == "D0.7e.5a", "FRONTIER_AUDIT_ACTIVE_LEAF_DRIFT")
    require(transaction["remaining_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "FRONTIER_AUDIT_STOP_DRIFT")
    require(transaction["rh_status"] == "NOT_RH", "FRONTIER_AUDIT_TRANSACTION_RH_OVERCLAIM")

    nodes = state["nodes"]
    for node_id in cert["exact_open_leaf_addresses"]:
        require(node_id in nodes, f"FRONTIER_AUDIT_NODE_MISSING:{node_id}")
        require(
            nodes[node_id]["proof_status"] in {"OPEN", "BLOCKED"},
            f"FRONTIER_AUDIT_EXACT_NODE_FALSE_CLOSED:{node_id}",
        )
    for node_id in (
        "L0c1",
        "H2b2b1",
        "H2b2b2a",
        "H2b2b2b1",
        "H2b2b2b2a",
        "H3a2a",
        "H3b2a",
        "H3c2a",
        "H3e1",
        "H4a3b1",
        "H4b1",
        "H4c1",
        "H4d2a",
    ):
        require(nodes[node_id]["proof_status"] == "PROVED", f"FRONTIER_AUDIT_GENERIC_CORE_DRIFT:{node_id}")

    registered_names = "\n".join(
        str(node.get("statement", "")) + " " + str(node.get("validation", ""))
        for node in nodes.values()
    )
    require(
        "GenericKilledLineCharpolyFactor" not in registered_names,
        "FRONTIER_AUDIT_ASSEMBLY_ONLY_NODE_REGISTERED",
    )
    require(
        cert["rejected_assembly_only_candidate"]["retired_live_stop_codes"] == [],
        "FRONTIER_AUDIT_FALSE_STOP_RETIREMENT",
    )

    eligible = [
        node_id for node_id, node in nodes.items()
        if node["proof_status"] == "OPEN" and node["eligibility"]["eligible"]
    ]
    require(eligible == [], f"FRONTIER_AUDIT_UNEXPECTED_ELIGIBLE_WORKER:{eligible}")
    counts: dict[str, int] = {}
    for node in nodes.values():
        status = node["proof_status"]
        counts[status] = counts.get(status, 0) + 1
    expected = cert["expected_node_counts"]
    require(len(nodes) == expected["total"], "FRONTIER_AUDIT_NODE_TOTAL_DRIFT")
    for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
        require(counts.get(status, 0) == expected[status], f"FRONTIER_AUDIT_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "FRONTIER_AUDIT_ACTIVE_SET_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "FRONTIER_AUDIT_RESUME_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "FRONTIER_AUDIT_BUS_010_CREATED")
    require("NO_RH" in cert["explicit_nonclaims"], "FRONTIER_AUDIT_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "GENERIC_FRONTIER_EXHAUSTION_AUDIT_REV41_VALID",
        "generic_frontier": "EXHAUSTED",
        "remaining_work": "EXACT_SOURCE_OWNER_INPUTS_ONLY",
        "node_counts": counts,
        "eligible_worker_leaves": eligible,
        "active_leaf": active[0],
        "active_stop": state["resume"]["current_stop"],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
