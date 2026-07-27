#!/usr/bin/env python3
"""Fail-closed validator for the SOFT_3Q1 Sharp/Fubini gate."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
THEOREM = HERE / "SOFT_3Q1_DIRECT_HERMITIAN_KERNEL_PAIRING_THEOREM_2026-07-13.md"
RESULT = HERE / "SOFT_3Q1_KERNEL_PAIRING_CROSSCHECK.json"
REPORT = HERE / "SOFT_3Q1_DIRECT_HERMITIAN_KERNEL_PAIRING_REPORT_2026-07-13.md"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    theorem = THEOREM.read_text()
    result = json.loads(RESULT.read_text())
    report = REPORT.read_text()

    for token in (
        "w=i z",
        "F^sharp_Z(z)=conj(F(conj z))",
        "c_D0.6=1",
        "hat_phi_D06(u-v)",
        "SOFT_3Q1_ZERO_PRODUCT_TARGET_MISMATCH",
        "SOFT_3Q1_DIRECT_HERMITIAN_KERNEL_PAIRING_AND_SHARP_LOCKED",
    ):
        require(token in theorem, f"SOFT_3Q1_THEOREM_TOKEN_MISSING:{token}")

    plant = result["sharp_lock"]["plant"]
    require(plant["relative_difference"] > 0.5, "SOFT_3Q1_SHARP_PLANT_INERT")
    require(plant["even_control_difference"] == 0, "SOFT_3Q1_XI_CONTROL_NOT_SILENT")
    require(result["fubini"]["coefficient_c_D06"] == 1, "SOFT_3Q1_D06_NORMALIZATION_GAP")
    require(result["fubini"]["kernel_argument"] == "u-v", "SOFT_3Q1_D06_KERNEL_SIGN_WRONG")
    for cell in result["fubini"]["cells"]:
        require(cell["relative_error"] < 2e-10, "SOFT_3Q1_FUBINI_CROSSCHECK_FAILED")
        require("sign-changing" in cell["phi"], "SOFT_3Q1_SIGN_CHANGING_PHI_MISSING")
    require(result["kernel_sign_plant"]["relative_difference"] > 0.4, "SOFT_3Q1_U_MINUS_V_PLANT_INERT")

    away = result["support_away_plant"]
    require(away["sample_nodes_inside_support"] == 0, "SOFT_3Q1_SUPPORT_AWAY_HIT_SAMPLE")
    require(away["Psi_zero_sampling_value"] == 0, "SOFT_3Q1_PSI_PLANT_NOT_ZERO")
    require(away["direct_real_axis_pairing"] > 1e-7, "SOFT_3Q1_DIRECT_PAIRING_VANISHED")
    require(away["verdict"] == "SOFT_3Q1_ZERO_PRODUCT_TARGET_MISMATCH", "SOFT_3Q1_PSI_MISMATCH_NOT_RECORDED")

    expected = {
        "P1": "PASS_DIRECT_FUBINI",
        "P2": "FIRED_PSI_SUPPORT_AWAY_MISMATCH",
        "P3": "PASS_ZEO_SHARP_IS_CONJUGATION",
        "P4": "PASS_SIGN_CHANGING_PHI_LEGAL",
        "P5": "OPEN_RANK_ONE_KERNEL_CONVERGENCE_IS_NEXT_WALL",
    }
    require(result["scoring"] == expected, "SOFT_3Q1_P1_P5_SCORING_MISMATCH")
    require(not result["bus_010_created"], "SOFT_3Q1_BUS_010_SMUGGLED")
    require("Bus 010 was not created" in report, "SOFT_3Q1_REPORT_BUS_GUARD_MISSING")

    print("SOFT_3Q1_SHARP_LOCK_PASS")
    print("SOFT_3Q1_FUBINI_CROSSCHECK_PASS_13_120_53_120")
    print("SOFT_3Q1_ZERO_PRODUCT_TARGET_MISMATCH_FIRED")
    print("SOFT_3Q1_DIRECT_HERMITIAN_KERNEL_PAIRING_AND_SHARP_LOCKED")
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
