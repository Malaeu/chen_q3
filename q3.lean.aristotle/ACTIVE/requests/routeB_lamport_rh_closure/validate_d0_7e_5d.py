#!/usr/bin/env python3
"""Fail-closed validator for the PO_D0_7E_XWALK address migration."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_7E_5D_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def has_dependency_cycle(nodes: dict[str, Any]) -> bool:
    color = {node_id: 0 for node_id in nodes}

    def visit(node_id: str) -> bool:
        if color[node_id] == 1:
            return True
        if color[node_id] == 2:
            return False
        color[node_id] = 1
        for dependency in nodes[node_id].get("dependencies", []):
            if dependency not in nodes or visit(dependency):
                return True
        color[node_id] = 2
        return False

    return any(visit(node_id) for node_id in nodes if color[node_id] == 0)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    state = json.loads(STATE_PATH.read_text(encoding="utf-8"))
    source_lines = (REQUEST_DIR / "D0_7E_OWNER_INPUT.md").read_text(encoding="utf-8").splitlines()
    migration = (REQUEST_DIR / "D0_7E_5D_XWALK_MIGRATION.md").read_text(encoding="utf-8")
    verbatim = "\n".join(source_lines[77:98])

    require(cert["node_id"] == "D0.7e.5d", "D0_7E_5D_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_7E_5D_NOT_PROVED")
    require(cert["proof_scope"] == "ADDRESS_AND_WORDING_MIGRATION_ONLY", "D0_7E_5D_SCOPE_OVERCLAIM")
    require(cert["exit_code"] == "D0_7E_XWALK_MIGRATION_LOCKED", "D0_7E_5D_EXIT_DRIFT")
    require(cert["source_obligation"]["wording"] == "UNCHANGED_VERBATIM", "D0_7E_XWALK_WORDING_DRIFT")
    require(verbatim in migration, "D0_7E_XWALK_WORDING_DRIFT")

    checked: list[str] = []
    for pin in cert["dependency_pins"] + cert["artifacts"]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_7E_5D_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_7E_5D_PIN_DRIFT:{pin['path']}")
        checked.append(pin["path"])

    address = cert["new_address"]
    require(address["node_id"] == "H3e", "D0_7E_H3E_ADDRESS_MISSING")
    require(address["canonical_label"] == "H3e_ExactWPrimeTrackingTheorem", "D0_7E_H3E_LABEL_DRIFT")
    require(address["tracking_proof_status"] == "OPEN", "D0_7E_H3E_THEOREM_SMUGGLED")
    require(address["external_requirements"] == ["PO-1/A1", "PO_XWALK_UNIFORM_EVAL"], "D0_7E_PO_XWALK_UNIFORM_EVAL_UNREGISTERED")

    nodes = state["nodes"]
    require(not has_dependency_cycle(nodes), "D0_7E_D0_DEPENDENCY_CYCLE")
    leaf = nodes["D0.7e.5d"]
    require(leaf["proof_status"] == "PROVED", "D0_7E_5D_STATE_NOT_PROVED")
    require(leaf["dependencies"] == ["D0.7e.5.0"], "D0_7E_5D_DEPENDENCY_DRIFT")
    require(leaf["validation"] == "D0_7E_XWALK_MIGRATION_LOCKED", "D0_7E_5D_STATE_VALIDATION_DRIFT")
    h3e = nodes["H3e"]
    require(h3e.get("name") == "H3e_ExactWPrimeTrackingTheorem", "D0_7E_H3E_LABEL_DRIFT")
    if state["revision"] >= 31:
        require(h3e["kind"] == "AND", "D0_7E_H3E_PARENT_NOT_AND")
        require(h3e["dependencies"] == ["H3e.0"], "D0_7E_H3E_DEPENDENCY_DRIFT")
        require(h3e["ordered_children"] == ["H3e1", "H3e2"], "D0_7E_H3E_CHILD_ORDER_DRIFT")
        require(h3e["assembly_theorem_id"] == "H3e3", "D0_7E_H3E_ASSEMBLY_DRIFT")
        require(
            nodes["H3e2"]["dependencies"] ==
            ["D0", "H3a", "H3b", "H3c", "H4b", "H4c", "H3e1"],
            "D0_7E_H3E2_DEPENDENCY_DRIFT",
        )
        require(
            h3e["external_requirements"] ==
            ["PO-1/A1", "PO_XWALK_UNIFORM_EVAL", "H3E_RELATIVE_NORMALIZATION_TRANSFER"],
            "D0_7E_H3E_EXTERNAL_REQUIREMENT_DRIFT",
        )
        require(
            state["h3_h4_contract_repair"]["status"] ==
            "CONTRACT_V2_DAG_REPAIRED_THREE_GAPS_REGISTERED_NOT_RH",
            "D0_7E_H3E_SEMANTIC_REMAP_UNREGISTERED",
        )
    elif state["revision"] >= 15:
        # Contract-v2 rev15 retyped the old H4c/H4d meanings as
        # H4b SafeGapLower / H4c SafeSignAndB.  The certificate above remains
        # the immutable historical migration snapshot; validate the semantic
        # remap registered by the later repair instead of stale labels.
        require(
            h3e["dependencies"] == ["D0", "H3a", "H3b", "H3c", "H4b", "H4c"],
            "D0_7E_H3E_DEPENDENCY_DRIFT",
        )
        require(
            h3e["external_requirements"] ==
            ["PO-1/A1", "PO_XWALK_UNIFORM_EVAL", "H3E_RELATIVE_NORMALIZATION_TRANSFER"],
            "D0_7E_H3E_EXTERNAL_REQUIREMENT_DRIFT",
        )
        require(
            state["h3_h4_contract_repair"]["status"] ==
            "CONTRACT_V2_DAG_REPAIRED_THREE_GAPS_REGISTERED_NOT_RH",
            "D0_7E_H3E_SEMANTIC_REMAP_UNREGISTERED",
        )
    else:
        require(h3e["dependencies"] == address["dependencies"], "D0_7E_H3E_DEPENDENCY_DRIFT")
        require(h3e["external_requirements"] == address["external_requirements"], "D0_7E_H3E_EXTERNAL_REQUIREMENT_DRIFT")
    require(h3e["proof_status"] == "OPEN" and h3e["activity"] == "INACTIVE", "D0_7E_H3E_THEOREM_SMUGGLED")
    require(state["external_obligations"]["PO_XWALK_UNIFORM_EVAL"]["status"] == "OPEN_CRITICAL", "D0_7E_UNIFORM_EVAL_SMUGGLED")

    # Deterministic plants.
    require(verbatim.replace("PO_D0_7E_XWALK", "PO_D0_7E_XWALK_PLANT") not in migration, "D0_7E_XWALK_WORDING_DRIFT_PLANT_INERT")
    planted = {"H3e": {"dependencies": ["H4c"]}, "H4c": {"dependencies": ["H3e"]}}
    require(has_dependency_cycle(planted), "D0_7E_D0_DEPENDENCY_CYCLE_PLANT_INERT")
    require("NO_TRACKING_THEOREM_PROOF" in cert["explicit_nonclaims"], "D0_7E_H3E_THEOREM_SMUGGLED_PLANT_INERT")

    require(not any(BUS_DIR.glob("010_*.goal.md")), "D0_7E_5D_BUS_010_CREATED")
    require(cert["rh_status"] == "NOT_RH" and "NO_RH" in cert["explicit_nonclaims"], "D0_7E_5D_RH_OVERCLAIM")

    print(json.dumps({
        "node": "D0.7e.5d",
        "verdict": "D0_7E_XWALK_MIGRATION_LOCKED",
        "proof_status": "PROVED",
        "h3e": "OPEN_INACTIVE",
        "po_xwalk_uniform_eval": "OPEN_CRITICAL",
        "pins_checked": checked,
        "plants": list(cert["plants"].values()),
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
