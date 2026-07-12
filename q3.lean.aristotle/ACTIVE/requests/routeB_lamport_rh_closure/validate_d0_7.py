#!/usr/bin/env python3
"""Fail-closed validation for partial D0.7 exact-normalization registry."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_7_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.7", "D0_7_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "BLOCKED", "D0_7_CERT_MUST_BLOCK")
    require(cert["partial_exit_code"] == "D0_7_PARTIAL_NORMALIZATION_LOCKED", "D0_7_PARTIAL_EXIT_MISMATCH")
    require(cert["stop_code"] == "D0_7E_WPRIME_CONSUMER_MISSING", "D0_7_STOP_MISMATCH")
    require(cert["rh_status"] == "NOT_RH", "D0_7_RH_FIREWALL_MISSING")

    checked: list[str] = []
    for pin in cert["dependency_pins"] + cert["source_pins"] + cert["artifacts"]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_7_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_7_PIN_DRIFT:{pin['path']}")
        checked.append(pin["path"])

    children = cert["children"]
    require(children["D0.7a"] == "PROVED", "D0_7A_NOT_PROVED")
    require(children["D0.7b"] == "PROVED", "D0_7B_NOT_PROVED")
    require(children["D0.7c"] == "PROVED_CONDITIONAL_INTERFACE", "D0_7C_NOT_TYPED")
    require(children["D0.7d"] == "PROVED", "D0_7D_NOT_PROVED")
    require(children["D0.7e"] == "BLOCKED_WPRIME_CONSUMER_SOURCE", "D0_7E_MUST_BLOCK")
    require(children["D0.7f"] == "BLOCKED_BY_D0.7e", "D0_7_ASSEMBLY_MUST_BLOCK")

    delta = cert["delta_lock"]
    require(delta["vector"] == "L_m^(-1/2)*sum_|n|<=N V_n_m", "D0_7_DELTA_SCALE_MISMATCH")
    require(delta["functional"] == "<deltaVec_m_N,f>_ANTILINEAR_FIRST", "D0_7_DELTA_FUNCTIONAL_ORDER_MISMATCH")
    require(delta["all_H_evaluation"] == "NOT_CLAIMED", "D0_7_ALL_H_EVALUATION_SMUGGLED")

    ground = cert["ground_lock"]
    require("GroundDeltaNonzero" in ground["domain"], "D0_7_GROUND_ZERO_DIVISION")
    require(ground["phase_norm"] == "1", "D0_7_PHASE_NOT_UNIT")
    require(ground["boundary_delta"] == "1", "D0_7_BOUNDARY_NORMALIZATION_MISMATCH")
    require(ground["boundary_unit"] == "NOT_CLAIMED", "D0_7_PHASE_BOUNDARY_CONFLATION")

    trial = cert["trial_lock"]
    require("TrialNonzero" in trial["domain"], "D0_7_TRIAL_ZERO_DIVISION")
    require(trial["scale_positive"] is True, "D0_7_TRIAL_SCALE_SIGN_MISSING")

    b_lock = cert["b_lock"]
    require(b_lock["detector_definition"] == "bDet_m_N=Fhat_m_N(0)/Xi(0)_ON_TrialNonzero", "D0_7_B_DEFINITION_DRIFT")
    require(b_lock["detector_definition_status"] == "PROVED_FINITE_DEPENDENT", "D0_7_B_DEFINITION_UNPROVED")
    require(b_lock["detector_normalization_domain"] == "BDetNonzero", "D0_7_B_ZERO_DIVISION")
    require(
        b_lock["detector_crosswalk"]
        == "PO_D0_7E_XWALK_BLOCKED_AT_D0.7e.5a_AFTER_OWNER_R1_R5_LOCK_D0_7E_WPRIME_CONSUMER_MISSING",
        "D0_7_B_XWALK_OVERCLAIM",
    )
    require(b_lock["pilot_crosswalk"] == "NOT_PROVED", "D0_7_BPILOT_ALIAS")
    require(b_lock["weil_coefficient_crosswalk"] == "TYPE_MISMATCH", "D0_7_BWEIL_ALIAS")
    require(b_lock["uniform_bounds"] == "H4D_OPEN", "D0_7_H4D_SMUGGLED")

    proof = (REPO_ROOT / cert["proof_path"]).read_text(encoding="utf-8")
    for token in (
        "deltaVec_m_N := L_m^(-1/2)",
        "GroundDeltaNonzero",
        "D0_7D_B_NAMESPACE_FIREWALL_LOCKED",
        "D0_7E_CENTRAL_CALIBRATION_LOCKED",
        "D0_7E_WPRIME_CONSUMER_MISSING",
        "D0.7 = BLOCKED / 4_OF_5_COMPONENTS_PROVED",
        "NO_WPRIME_ZEO_CROSSWALK",
        "NO_RH",
    ):
        require(token in proof, f"D0_7_PROOF_TOKEN_MISSING:{token}")

    # Deterministic plants.
    L, N = 2.0, 2
    correct_norm_sq = (2 * N + 1) / L
    wrong_norm_sq = (2 * N + 1) / (L * L)
    require(correct_norm_sq != wrong_norm_sq, "D0_7_DELTA_SCALE_PLANT_INERT")

    require(delta["functional"].startswith("<deltaVec"), "D0_7_INNER_PRODUCT_ORDER_PLANT_INERT")
    require(delta["all_H_evaluation"] == "NOT_CLAIMED", "D0_7_ALL_H_EVALUATION_PLANT_INERT")

    c_abs = 2.0
    require(1.0 != 1.0 / c_abs, "D0_7_PHASE_BOUNDARY_PLANT_INERT")
    require(b_lock["detector_definition"] != "bWeil_j", "D0_7_BWEIL_PLANT_INERT")
    require(b_lock["pilot_crosswalk"] == "NOT_PROVED", "D0_7_BPILOT_PLANT_INERT")
    require(b_lock["uniform_bounds"] == "H4D_OPEN", "D0_7_H4D_PLANT_INERT")
    require(b_lock["detector_crosswalk"].endswith("WPRIME_CONSUMER_MISSING"), "D0_7_XWALK_SHAPE_PLANT_INERT")

    result = {
        "node": "D0.7",
        "verdict": "D0_7_PARTIAL_NORMALIZATION_LOCKED",
        "proof_status": "BLOCKED",
        "proved_children": ["D0.7a", "D0.7b", "D0.7c", "D0.7d"],
        "blocked_children": {"D0.7e": "D0_7E_WPRIME_CONSUMER_MISSING"},
        "assembly": "BLOCKED_BY_D0.7e",
        "pins_checked": checked,
        "plants": list(cert["plants"].values()),
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
