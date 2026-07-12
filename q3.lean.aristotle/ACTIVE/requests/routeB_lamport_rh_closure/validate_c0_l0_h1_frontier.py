#!/usr/bin/env python3
"""Fail-closed validator for Route B revision-14 C0/H1/L0 progress."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "C0_L0_H1_FRONTIER_CERTIFICATE.json"
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


def audit_lean(record: dict[str, str], required: list[str], code: str) -> str:
    path = pinned(record, code)
    text = path.read_text(encoding="utf-8")
    require(FORBIDDEN.search(text) is None, f"{code}_PROOF_HOLE")
    require("#print axioms" in text, f"{code}_AXIOM_PRINT_MISSING")
    for theorem in required:
        require(theorem in text, f"{code}_THEOREM_MISSING:{theorem}")
    return text


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    state = json.loads(STATE_PATH.read_text(encoding="utf-8"))

    require(cert["revision_target"] == 14, "FRONTIER_CERT_REVISION_DRIFT")
    require(state["revision"] >= 14, "FRONTIER_STATE_REVISION_TOO_OLD")
    require(cert["rh_status"] == "NOT_RH", "FRONTIER_CERT_RH_OVERCLAIM")
    require(state["honesty"]["rh_status"] == "OPEN", "FRONTIER_STATE_RH_OVERCLAIM")

    c0 = cert["c0"]
    require(c0["proof_status"] == "PROVED", "C0_CERT_NOT_PROVED")
    require(c0["exit_code"] == "XI_RH_INTERFACE_LOCKED", "C0_EXIT_DRIFT")
    c0_text = audit_lean(
        c0["lean_file"],
        ["riemannXi", "centeredXi", "rh_iff_centeredXi_zeros_real"],
        "C0_LEAN",
    )
    require("completedRiemannZeta₀" in c0_text, "C0_ENTIRE_COMPLETION_NOT_PINNED")
    for index, source in enumerate(c0["source_pins"]):
        pinned(source, f"C0_SOURCE_{index}")

    h1 = cert["h1_generic"]
    h1_text = audit_lean(
        h1["lean_file"],
        [
            "differentiable_finiteEntireCombination",
            "differentiable_phaseScaledReflection",
            "phaseScaledReflection_eq_zero_iff",
        ],
        "H1_GENERIC_LEAN",
    )
    require("finiteEntireCombination" in h1_text, "H1_GENERIC_FINITE_SUM_MISSING")
    pinned(h1["source_pin"], "H1_PRIMARY_SOURCE")
    require(h1["exact_h1_status"] == "OPEN_DEPENDENCY_BLOCKED", "H1_EXACT_FALSE_PASS")

    l0 = cert["l0_generic"]
    audit_lean(
        l0["lean_file"],
        ["zerosRealOn_of_zerosApproachOn", "tendsto_zero_of_detector_bound"],
        "L0_GENERIC_LEAN",
    )
    require(l0["exact_l0_status"] == "OPEN_DEPENDENCY_BLOCKED", "L0_EXACT_FALSE_PASS")

    falsifier = cert["completed_tracker_falsifier"]
    falsifier_text = audit_lean(
        falsifier["lean_file"],
        ["completedTrialTracker_neg_I_div_two_zero", "neg_I_div_two_not_real"],
        "H2_TRACKER_FALSIFIER_LEAN",
    )
    require("gammaC_one" in falsifier_text, "H2_TRACKER_FALSIFIER_GAMMAC_ONE_MISSING")
    require(
        falsifier["verdict"] == "H2_COMPLETED_TRACKER_GLOBAL_REAL_ZERO_FALSE",
        "H2_TRACKER_FALSIFIER_VERDICT_DRIFT",
    )

    pinned(cert["artifact"], "FRONTIER_ARTIFACT")
    require(cert["lean_audit"]["holes"] == 0, "FRONTIER_HOLE_COUNT_NONZERO")
    require(cert["lean_audit"]["unexpected_axioms"] == [], "FRONTIER_UNEXPECTED_AXIOM")
    require("NO_RH" in cert["explicit_nonclaims"], "FRONTIER_RH_FIREWALL_MISSING")

    nodes = state["nodes"]
    require(nodes["C0"]["proof_status"] == "PROVED", "C0_STATE_NOT_PROVED")
    for node_id in ("H1.0", "H1a", "H1b", "L0.0", "L0a", "L0b"):
        require(nodes[node_id]["proof_status"] == "PROVED", f"FRONTIER_NODE_NOT_PROVED:{node_id}")
        require(nodes[node_id]["activity"] == "INACTIVE", f"FRONTIER_NODE_ACTIVE:{node_id}")
    require(nodes["H1"]["proof_status"] == "OPEN", "H1_PARENT_FALSE_PASS")
    require(nodes["H1c"]["proof_status"] == "OPEN", "H1C_FALSE_PASS")
    require(nodes["H1d"]["proof_status"] == "OPEN", "H1D_FALSE_PASS")
    require(nodes["L0"]["proof_status"] == "OPEN", "L0_PARENT_FALSE_PASS")
    require(nodes["L0c"]["proof_status"] == "OPEN", "L0C_FALSE_PASS")
    require(nodes["L0d"]["proof_status"] == "OPEN", "L0D_FALSE_PASS")
    require(
        "H2_COMPLETED_TRACKER_GLOBAL_REAL_ZERO_FALSE" in nodes["H2"]["failure_codes"],
        "H2_TRACKER_FALSIFIER_NOT_REGISTERED",
    )

    active = [node_id for node_id, node in nodes.items() if node["activity"] == "ACTIVE"]
    require(active == ["D0.7e.5a"], "FRONTIER_ACTIVE_LEAF_DRIFT")
    require(state["resume"]["current_stop"] == "D0_7E_WPRIME_CONSUMER_MISSING", "FRONTIER_ACTIVE_STOP_DRIFT")
    require(not any(BUS_DIR.glob("010_*.goal.md")), "FRONTIER_BUS_010_CREATED")

    counts: dict[str, int] = {}
    for node in nodes.values():
        counts[node["proof_status"]] = counts.get(node["proof_status"], 0) + 1

    print(json.dumps({
        "verdict": "C0_L0_H1_FRONTIER_REV14_VALID",
        "c0": "XI_RH_INTERFACE_LOCKED",
        "h1": "GENERIC_CORE_PROVED_EXACT_FAMILY_BLOCKED",
        "h2_falsifier": falsifier["verdict"],
        "l0": "GENERIC_LOGIC_PROVED_ANALYTIC_TRANSFER_BLOCKED",
        "node_counts": counts,
        "active_leaf": active[0],
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
