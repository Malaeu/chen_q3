#!/usr/bin/env python3
"""Fail-closed validator for Goal 3 exact ledger, measurements, and phase note."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
THEOREM = HERE / "SOFT_L2_EXACT_PROJECTION_DEFECT_LAG_EQUATION_2026-07-13.md"
EDGE = HERE / "SOFT_L2_EDGE_MASS_PROFILE.json"
LAG = HERE / "SOFT_L2_LAG_LEDGER_13_120.json"
PHASE = HERE / "PHASE_STRUCTURE_PROBE.json"
REPORT = HERE / "SOFT_L2_EXACT_PROJECTION_DEFECT_LAG_EQUATION_REPORT_GOAL3_2026-07-13.md"
BUS = HERE.parent / "routeB_twolevel_spectral_ladder" / "bus"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    theorem = THEOREM.read_text(encoding="utf-8")
    report = REPORT.read_text(encoding="utf-8")
    edge = json.loads(EDGE.read_text(encoding="utf-8"))
    lag = json.loads(LAG.read_text(encoding="utf-8"))
    phase = json.loads(PHASE.read_text(encoding="utf-8"))

    theorem_tokens = [
        "S_(m,N) := Pi_sec Pi_(m,N) P_L",
        "Eproj = <(I-S) U_t q,T_full q>",
        "E_win + E_Gal + E_sec + E_Arch",
        "E_corr = E_polemid",
        "D_(a,L)(t) != 0  ==>  t*a>0 and |t-a|<L",
        "|D_(a,L)(t)| <= r_L(t) r_L(a)",
        "Plant A",
        "Plant B",
        "SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED",
    ]
    for token in theorem_tokens:
        require(token in theorem, f"SOFT_L2_GOAL3_THEOREM_TOKEN_MISSING:{token}")

    require(len(edge["summaries"]) == 7, "SOFT_L2_GOAL3_EDGE_CELL_OMISSION")
    require(edge["prediction"]["high_precision_strictly_increasing_exponent"],
            "SOFT_L2_GOAL3_EDGE_PREDICTION_FAILED")
    require(not edge["prediction"]["all_cell_strict_monotonicity_resolved"],
            "SOFT_L2_GOAL3_FLOAT64_FLOOR_HIDDEN")
    require(not edge["claims"]["smallness_proved"], "SOFT_L2_GOAL3_SMALLNESS_SMUGGLED")

    require(lag["cell"]["lambda_sq"] == 13 and lag["cell"]["N"] == 120,
            "SOFT_L2_GOAL3_WRONG_LAG_CELL")
    require(len(lag["rows"]) == 13, "SOFT_L2_GOAL3_LAG_GRID_INCOMPLETE")
    require(lag["prediction"]["outcome"] == "SUPPORTED_FOR_AGGREGATE_REMAINDER_ON_GRID",
            "SOFT_L2_GOAL3_REMAINDER_PREDICTION_FAILED")
    require(lag["remainder_scope"].startswith("aggregate Galerkin+sector"),
            "SOFT_L2_GOAL3_PURE_GALERKIN_OVERCLAIM")
    require(not lag["claims"]["compact_support_proved"],
            "SOFT_L2_GOAL3_COMPACT_SUPPORT_SMUGGLED")

    diagnostic = phase["phase_slope_diagnostic"]
    require(phase["verdict_code"] == "C2_PHASE_FREE", "SOFT_L2_GOAL3_PHASE_VERDICT_CHANGED")
    require(diagnostic["code"] == "PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC",
            "SOFT_L2_GOAL3_PHASE_DIAGNOSTIC_MISSING")
    require(diagnostic["preserves_verdict"] == "C2_PHASE_FREE",
            "SOFT_L2_GOAL3_PHASE_DIAGNOSTIC_OVERCLAIM")
    require("V1 parity-closure" in diagnostic["use"],
            "SOFT_L2_GOAL3_V1_INPUT_MISSING")

    for token in [
        "SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED",
        "SOFT_L2_MEASUREMENTS_COMPLETE",
        "C2_PHASE_FREE",
        "PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC",
        "Bus 010 was not created",
    ]:
        require(token in report, f"SOFT_L2_GOAL3_REPORT_TOKEN_MISSING:{token}")

    require(not list(BUS.glob("010_*.goal.md")), "SOFT_L2_GOAL3_BUS_010_SMUGGLED")

    print("SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED")
    print("SOFT_L2_MEASUREMENTS_COMPLETE")
    print("C2_PHASE_FREE")
    print("PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC")
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
