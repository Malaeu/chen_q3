#!/usr/bin/env python3
"""Fail-closed validator for the R2 pre-mint P1--P4 battery."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
LADDER = HERE.parent / "routeB_twolevel_spectral_ladder"
RESULT = HERE / "D0_7E_5A_PRE_MINT_FALSIFIER_BATTERY.json"
DRAFT = HERE / "D0_7E_5A_OWNER_MINT_DRAFT_WPRIME_CONSUMER.md"
STATE = HERE / "STATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    result = json.loads(RESULT.read_text(encoding="utf-8"))
    require(
        result["schema"] == "route_b_d0_7e_5a_pre_mint_falsifier_battery.v1",
        "D0_7E_5A_BATTERY_SCHEMA_DRIFT",
    )
    require(result["draft"]["sha256"] == sha256(DRAFT), "D0_7E_5A_DRAFT_SHA_DRIFT")
    require(result["draft_revision_audit"]["revision"] == "R2_V2_SELF_CORRECTION", "D0_7E_5A_NOT_R2")
    require(result["arithmetic"] == "IEEE754_BINARY64_ONLY_NO_DPS_ESCALATION", "D0_7E_5A_NOT_FLOAT64")

    scores = result["scores"]
    require(scores["P1"]["status"] == "FAIL", "D0_7E_5A_P1_SCORE_DRIFT")
    require(scores["P2"]["status"] == "FAIL", "D0_7E_5A_P2_SCORE_DRIFT")
    require(scores["P3"]["status"] == "PASS", "D0_7E_5A_P3_SCORE_DRIFT")
    require(scores["P4"]["status"] == "FAIL", "D0_7E_5A_P4_SCORE_DRIFT")
    require(
        scores["P1"]["shadow_reduced_S0"]["all_relative_residuals_below_threshold"],
        "D0_7E_5A_P1_SHADOW_THRESHOLD_FAIL",
    )
    for cell in scores["P2"]["cells"]:
        require(cell["bCal_within_factor_ten_of_one"], "D0_7E_5A_P2_NOT_ZERO_CONSISTENT")
        require(
            cell["current_R2_orientation_ratio_relative_error_vs_bCal_fourth"] <= 5e-15,
            "D0_7E_5A_P2_FACTOR_DRIFT",
        )
        require(
            cell["two_level_rayleigh_alpha_closure_ratio_bCal"] < 1e-90,
            "D0_7E_5A_P2_RAYLEIGH_MISMATCH_DISAPPEARED",
        )
    for cell in scores["P3"]["cells"]:
        require(cell["plant"] == "SLOT_VACUITY", "D0_7E_5A_P3_PLANT_INERT")
        require(cell["independent_WPrime_degree_of_freedom"] is False, "D0_7E_5A_P3_NOT_VACUOUS")
    for carrier in ("two_level_S0_N120", "full_float64_residual_proxy_N120"):
        require(
            abs(scores["P4"][carrier]["beta_W_minus_beta_r"] - 0.5) <= 1e-12,
            "D0_7E_5A_P4_PREFATOR_DRIFT",
        )

    state = json.loads(STATE.read_text(encoding="utf-8"))
    node = state["nodes"]["D0.7e.5a"]
    require(node["proof_status"] == "BLOCKED", "D0_7E_5A_ILLEGAL_CLOSURE")
    require(node["activity"] == "ACTIVE", "D0_7E_5A_ACTIVITY_DRIFT")
    require(result["control_plane_guards"]["mint_activated"] is False, "D0_7E_5A_MINT_ACTIVATED")
    require(not list((LADDER / "bus").glob("010_*")), "D0_7E_5A_BUS_010_CREATED")
    report = HERE.parents[3] / result["report"]["path"]
    require(sha256(report) == result["report"]["sha256"], "D0_7E_5A_REPORT_SHA_DRIFT")
    print("D0_7E_5A_PRE_MINT_BATTERY_VALID")


if __name__ == "__main__":
    main()
