#!/usr/bin/env python3
"""Fail-closed validator for the Route B revision-15 H3/H4 repair."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "H3_H4_CONTRACT_REPAIR_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"
FORBIDDEN = re.compile(r"\b(sorry|admit)\b|exact\?")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def pinned(record: dict[str, str], code: str) -> Path:
    path = REPO_ROOT / record["path"]
    require(path.is_file(), f"{code}_MISSING:{record['path']}")
    require(sha256(path) == record["sha256"], f"{code}_HASH_DRIFT:{record['path']}")
    return path


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    state = json.loads(STATE_PATH.read_text(encoding="utf-8"))

    require(cert["revision_target"] == 15, "H34_CERT_REVISION_DRIFT")
    require(state["revision"] >= 15, "H34_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "H34_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "H34_STATE_RH_OVERCLAIM")

    authority = pinned(cert["authority"], "H34_CONTRACT_V2")
    authority_text = authority.read_text(encoding="utf-8")
    for token in ("SafeAlphaUpper", "SafeGapLower", "SafeSignAndB", "SafeRateAssembly"):
        require(token in authority_text, f"H4_CONTRACT_LEAF_MISSING:{token}")

    lean_path = pinned(cert["proof_artifact"], "H34_LEAN")
    lean_text = lean_path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(lean_text) is None, "H34_LEAN_PROOF_HOLE")
    require("#print axioms" in lean_text, "H34_LEAN_AXIOM_PRINT_MISSING")
    for theorem in cert["proof_artifact"]["proved"]:
        require(theorem in lean_text, f"H34_LEAN_THEOREM_MISSING:{theorem}")

    for index, source in enumerate(cert["source_pins"]):
        pinned(source, f"H34_SOURCE_{index}")
    pinned(cert["artifact"], "H34_ARTIFACT")

    falsifiers = cert["falsifiers"]
    require(
        falsifiers["residual_bridge"]["verdict"] ==
        "PO_XWALK_RESIDUAL_BRIDGE_DIRECTION_FALSE",
        "H34_RESIDUAL_FALSE_VERDICT_DRIFT",
    )
    require(
        falsifiers["ib2_liminf"]["verdict"] ==
        "H3E_IB2_LIMINF_MISIDENTIFICATION",
        "H3E_IB2_FALSE_VERDICT_DRIFT",
    )
    require(
        cert["open_limit_object_audit"]["verdict"] == "XI_LIMIT_OBJECT_MISMATCH",
        "H3C_LIMIT_OBJECT_VERDICT_DRIFT",
    )

    nodes = state["nodes"]
    h4 = nodes["H4"]
    require(h4["kind"] == "AND", "H4_PARENT_NOT_AND")
    require(h4["ordered_children"] == ["H4a", "H4b", "H4c", "H4d"], "H4_CHILD_ORDER_DRIFT")
    require(h4["assembly_theorem_id"] == "H4e", "H4_ASSEMBLY_ADDRESS_DRIFT")
    require(h4["proof_status"] == "OPEN", "H4_FALSE_PASS")

    expected_labels = cert["h4_repair"]["labels"]
    for node_id, name in expected_labels.items():
        require(nodes[node_id].get("name") == name, f"H4_SAFE_LABEL_DRIFT:{node_id}")
    for node_id in ("H4.0", "H4a.0", "H4d.0", "H4d1"):
        require(nodes[node_id]["proof_status"] == "PROVED", f"H4_GENERIC_NODE_NOT_PROVED:{node_id}")
        require(nodes[node_id]["activity"] == "INACTIVE", f"H4_GENERIC_NODE_ACTIVE:{node_id}")
    for node_id in ("H4a", "H4a1", "H4a2", "H4a3", "H4a4", "H4b", "H4c", "H4d", "H4d2", "H4d3", "H4e"):
        require(nodes[node_id]["proof_status"] == "OPEN", f"H4_EXACT_NODE_FALSE_PASS:{node_id}")

    require(
        "PO_XWALK_RESIDUAL_BRIDGE_DIRECTION_FALSE" in nodes["H4a3"]["failure_codes"],
        "H4A3_FALSE_BRIDGE_NOT_REGISTERED",
    )
    require(
        "H3E_IB2_LIMINF_MISIDENTIFICATION" in nodes["H3e"]["failure_codes"],
        "H3E_IB2_GAP_NOT_REGISTERED",
    )
    require(
        nodes["H3e"]["dependencies"] == ["D0", "H3a", "H3b", "H3c", "H4b", "H4c"],
        "H3E_CONTRACT_V2_SEMANTIC_DEPENDENCY_REMAP_DRIFT",
    )
    require(
        "XI_LIMIT_OBJECT_MISMATCH" in nodes["H3c"]["failure_codes"],
        "H3C_LIMIT_OBJECT_GAP_NOT_REGISTERED",
    )
    require(nodes["H3e"]["proof_status"] == "OPEN", "H3E_FALSE_PASS")

    counts: dict[str, int] = {}
    for node in nodes.values():
        counts[node["proof_status"]] = counts.get(node["proof_status"], 0) + 1
    expected = cert["h4_repair"]["expected_node_counts"]
    require(len(nodes) == expected["total"], "H34_NODE_TOTAL_DRIFT")
    for status in ("PROVED", "OPEN", "BLOCKED", "CONDITIONAL"):
        require(counts.get(status, 0) == expected[status], f"H34_NODE_COUNT_DRIFT:{status}")

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "H34_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "H34_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "H34_BUS_010_CREATED")
    require("NO_RH" in cert["explicit_nonclaims"], "H34_RH_FIREWALL_MISSING")

    print(json.dumps({
        "verdict": "H3_H4_CONTRACT_REPAIR_REV15_VALID",
        "h4_children": h4["ordered_children"],
        "residual_bridge": falsifiers["residual_bridge"]["verdict"],
        "ib2": falsifiers["ib2_liminf"]["verdict"],
        "limit_object": cert["open_limit_object_audit"]["verdict"],
        "node_counts": counts,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
