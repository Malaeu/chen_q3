#!/usr/bin/env python3
"""Fail-closed validation of the owner-ratified D0.7e.5 B-prime tree."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_7E_5_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def has_dependency_cycle(nodes: dict[str, Any]) -> bool:
    """Return True iff the directed dependency graph contains a cycle."""
    color: dict[str, int] = {node_id: 0 for node_id in nodes}

    def visit(node_id: str) -> bool:
        if color[node_id] == 1:
            return True
        if color[node_id] == 2:
            return False
        color[node_id] = 1
        for dependency in nodes[node_id].get("dependencies", []):
            if visit(dependency):
                return True
        color[node_id] = 2
        return False

    return any(visit(node_id) for node_id in nodes if color[node_id] == 0)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    state = json.loads(STATE_PATH.read_text(encoding="utf-8"))

    require(cert["node_id"] == "D0.7e.5", "D0_7E_5_CERT_NODE_MISMATCH")
    require(cert["kind"] == "AND", "D0_7E_5_NOT_AND")
    require(cert["proof_status"] == "BLOCKED", "D0_7E_5_FALSE_PASS")
    require(cert["partial_exit_code"] == "D0_7E_5_DECOMPOSITION_LOCKED", "D0_7E_5_DECOMPOSITION_UNLOCKED")
    require(cert["stop_code"] == "D0_7E_WPRIME_CONSUMER_MISSING", "D0_7E_5_STOP_DRIFT")
    require(cert["rh_status"] == "NOT_RH", "D0_7E_5_RH_FIREWALL_MISSING")

    checked: list[str] = []
    for pin in cert["dependency_pins"] + cert["artifacts"]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_7E_5_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_7E_5_PIN_DRIFT:{pin['path']}")
        checked.append(pin["path"])

    ratification = (REQUEST_DIR / "D0_7E_BPRIME_OWNER_RATIFICATION.md").read_text(encoding="utf-8")
    for token in (
        "Ратифицирую рекомендованные R1–R5.",
        "R2 = H3e_ExactWPrimeTrackingTheorem",
        "R3 = CONTRACT_V2_DIRECT_QB_CONVENTION",
        "R4 = TWO_PARAMETER_m_N_NO_KAPPA_NO_SELECTOR",
        "R5 = ALPHA_DEFINITION_HOME_H0_A1",
        "D0.7e.5_REMAINS_BLOCKED_UNTIL_INDEPENDENT_CONSUMER_AND_ORIENTATION_PASS",
        "NOT_RH",
    ):
        require(token in ratification, f"D0_7E_5_OWNER_TOKEN_MISSING:{token}")

    decomposition = cert["decomposition"]
    require(decomposition["node"] == "D0.7e.5.0", "D0_7E_5_DECOMPOSITION_NODE_DRIFT")
    require(decomposition["proof_status"] == "PROVED_BY_OWNER_RATIFIED_DEFINITION", "D0_7E_5_DECOMPOSITION_OVERCLAIM")
    require(decomposition["children"] == ["D0.7e.5a", "D0.7e.5b", "D0.7e.5c", "D0.7e.5d"], "D0_7E_5_CHILD_ORDER_DRIFT")
    require(decomposition["assembly"] == "D0.7e.5e", "D0_7E_5_ASSEMBLY_ID_DRIFT")

    components = cert["components"]
    require(components["D0.7e.5a"].startswith("ACTIVE_BLOCKED_"), "D0_7E_5A_FALSE_PASS")
    require(components["D0.7e.5b"] == "PROVED_INTERFACE_TYPECHECK_ONLY", "D0_7E_5B_STATUS_DRIFT")
    require(components["D0.7e.5c"].startswith("OPEN_INELIGIBLE_"), "D0_7E_5C_PREMATURE")
    require(components["D0.7e.5d"] == "PROVED_MIGRATION_CORRECTNESS_ONLY_H3E_OPEN", "D0_7E_5D_STATUS_DRIFT")
    require(components["D0.7e.5e"].startswith("BLOCKED_"), "D0_7E_5_ASSEMBLY_OVERCLAIM")

    slot = cert["typed_slot"]
    require(slot["carrier"] == "INDEPENDENT_TWO_PARAMETER_m_N", "D0_7E_SELECTOR_INVENTED")
    require(slot["alpha_definition_home"] == "CONTRACT_V2_H0_A1_OPEN_CRITICAL", "D0_7E_ALPHA_WRONG_HOME")
    require(slot["q_b_convention"] == "0<c_b<=abs(b(lambda))*lambda^(-q_b)<=C_b", "D0_7E_QB_CONVENTION_DRIFT")
    require(slot["q_b_value"] == "NOT_PROVED_FIT_NOT_LAW_ONLY", "D0_7E_QB_FIT_PROMOTED")
    require(slot["N_lambda_selector"] == "FORBIDDEN_UNTIL_SOURCE_BACKED", "D0_7E_SELECTOR_INVENTED")
    require(slot["consumer_definition"] == "NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE_T0_CORPUS", "D0_7E_CONSUMER_SMUGGLED")
    require(slot["consumer_orientation"] == "UNPINNED", "D0_7E_B_ORIENTATION_SMUGGLED")

    export = cert["downstream_export"]
    require(export["address"] == "H3e", "D0_7E_H3E_ADDRESS_MISSING")
    require(export["proof_status"] == "OPEN", "D0_7E_H3E_THEOREM_SMUGGLED")
    require(export["uniform_obligation"] == "PO_XWALK_UNIFORM_EVAL_OPEN_CRITICAL", "D0_7E_PO_XWALK_UNIFORM_EVAL_UNREGISTERED")
    require(export["consumer_definition_policy"] == "INDEPENDENT_SOURCE_REQUIRED_DESIRED_RHS_FORBIDDEN", "D0_7E_TAUTOLOGY")
    require(export["slot_vacuity_link"] == "H3e_CONSUMES_D0.7e.5_AND_D0.7e.5c", "D0_7E_SLOT_VACUITY")
    require(export["D0_8_tracking_owner"] is False and export["PO_10_tracking_owner"] is False, "D0_7E_XWALK_WRONG_ADDRESS")

    nodes = state["nodes"]
    for node_id, node in nodes.items():
        for dependency in node.get("dependencies", []):
            require(dependency in nodes, f"D0_7E_DAG_DEPENDENCY_MISSING:{node_id}:{dependency}")
    require(not has_dependency_cycle(nodes), "D0_7E_D0_DEPENDENCY_CYCLE")
    parent = nodes["D0.7e.5"]
    require(parent["kind"] == "AND", "D0_7E_5_STATE_NOT_AND")
    require(parent["ordered_children"] == decomposition["children"], "D0_7E_5_STATE_CHILD_DRIFT")
    require(parent["assembly_theorem_id"] == "D0.7e.5e", "D0_7E_5_STATE_ASSEMBLY_DRIFT")
    require(nodes["D0.7e.5.0"]["proof_status"] == "PROVED", "D0_7E_5_DECOMPOSITION_NODE_NOT_PROVED")
    require(nodes["D0.7e.5a"]["activity"] == "ACTIVE", "D0_7E_5A_NOT_ACTIVE")
    require(nodes["D0.7e.5a"]["proof_status"] == "BLOCKED", "D0_7E_5A_STATE_FALSE_PASS")
    require(nodes["D0.7e.5a"]["failure_codes"][0] == "D0_7E_WPRIME_CONSUMER_MISSING", "D0_7E_5A_PRIMARY_STOP_DRIFT")
    require(nodes["D0.7e.5b"]["proof_status"] == "PROVED", "D0_7E_5B_STATE_NOT_PROVED")
    require(nodes["D0.7e.5b"]["validation"] == "D0_7E_5B_TYPED_INTERFACE_LOCKED", "D0_7E_5B_STATE_VALIDATION_DRIFT")
    require(nodes["D0.7e.5c"]["proof_status"] == "OPEN", "D0_7E_5C_FALSE_PASS")
    require(nodes["D0.7e.5d"]["proof_status"] == "PROVED", "D0_7E_5D_STATE_NOT_PROVED")
    require(nodes["D0.7e.5d"]["validation"] == "D0_7E_XWALK_MIGRATION_LOCKED", "D0_7E_5D_STATE_VALIDATION_DRIFT")
    require(nodes["D0.7e.5e"]["proof_status"] == "BLOCKED", "D0_7E_5_ASSEMBLY_OVERCLAIM")
    active = [node["id"] for node in nodes.values() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "D0_7E_5_ACTIVE_NODE_DRIFT")

    h3 = nodes["H3"]
    h3d = nodes["H3d"]
    h3e = nodes["H3e"]
    require(h3["ordered_children"] == ["H3a", "H3b", "H3c", "H3e"], "D0_7E_H3_CHILD_ORDER_DRIFT")
    require(h3["assembly_theorem_id"] == "H3d", "D0_7E_H3_ASSEMBLY_RENUMBERED")
    require(h3d["dependencies"] == ["H3a", "H3b", "H3c", "H3e"], "D0_7E_H3_ASSEMBLY_OMITS_H3E")
    require(h3e["proof_status"] == "OPEN" and h3e["activity"] == "INACTIVE", "D0_7E_H3E_PREMATURE")
    require(h3e.get("name") == "H3e_ExactWPrimeTrackingTheorem", "D0_7E_H3E_LABEL_DRIFT")
    if state["revision"] >= 15:
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
        require(h3e["dependencies"] == ["D0", "H3a", "H3b", "H3c", "H4c", "H4d"], "D0_7E_H3E_DEPENDENCY_DRIFT")
        require(h3e["external_requirements"] == ["PO-1/A1", "PO_XWALK_UNIFORM_EVAL"], "D0_7E_H3E_EXTERNAL_REQUIREMENT_DRIFT")
    require(h3e["consumes_slot"] == "D0.7e.5", "D0_7E_SLOT_VACUITY")
    require(h3e["consumer_identity_dependency"] == "D0.7e.5c", "D0_7E_SLOT_VACUITY")

    external = state["external_obligations"]
    require(external["PO-1/A1"]["status"] == "OPEN_CRITICAL", "D0_7E_ALPHA_DEFINITION_SMUGGLED")
    require(external["PO_XWALK_UNIFORM_EVAL"]["status"] == "OPEN_CRITICAL", "D0_7E_UNIFORM_EVAL_SMUGGLED")
    require(h3e["eligibility"]["eligible"] is False, "D0_7E_H3E_ELIGIBILITY_SMUGGLED")

    # Deterministic structural plants.
    require("D0.7e.5" in export["slot_vacuity_link"], "D0_7E_SLOT_VACUITY_PLANT_INERT")
    fake_policy = "DEFINED_BY_DESIRED_RHS"
    require(fake_policy != export["consumer_definition_policy"], "D0_7E_TAUTOLOGY_PLANT_INERT")
    planted_cycle = {
        "H3e": {"dependencies": ["H4c"]},
        "H4c": {"dependencies": ["H3e"]},
    }
    require(has_dependency_cycle(planted_cycle), "D0_7E_D0_DEPENDENCY_CYCLE_PLANT_INERT")
    require("NO_ALPHA_DEFINITION_IN_D0" in cert["explicit_nonclaims"], "D0_7E_ALPHA_HOME_PLANT_INERT")
    require("NO_N_LAMBDA_SELECTOR" in cert["explicit_nonclaims"], "D0_7E_SELECTOR_PLANT_INERT")
    require("NO_D0_7E_5_ASSEMBLY" in cert["explicit_nonclaims"], "D0_7E_5_ASSEMBLY_PLANT_INERT")

    require(not any(BUS_DIR.glob("010_*.goal.md")), "D0_7E_5_BUS_010_CREATED")
    require("NO_H3C_H4_IMPORT_INTO_D0" in cert["explicit_nonclaims"], "D0_7E_5_DOWNSTREAM_IMPORT")
    require("NO_RH" in cert["explicit_nonclaims"], "D0_7E_5_RH_OVERCLAIM")

    result = {
        "node": "D0.7e.5",
        "verdict": "D0_7E_5_DECOMPOSITION_LOCKED",
        "proof_status": "BLOCKED",
        "proved_children": ["D0.7e.5b", "D0.7e.5d"],
        "active_blocked_child": {"D0.7e.5a": "D0_7E_WPRIME_CONSUMER_MISSING"},
        "downstream_address": "H3e_OPEN_INACTIVE",
        "external_obligations": ["PO-1/A1", "PO_XWALK_UNIFORM_EVAL"],
        "pins_checked": checked,
        "plants": list(cert["plants"].values()),
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
