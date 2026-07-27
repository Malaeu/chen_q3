#!/usr/bin/env python3
"""Fail-closed validator for SOFT_L2_RigidityFreeze."""

from __future__ import annotations

import json
from pathlib import Path

from soft_l2_rigidity_freeze_plants import run_plants


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
THEOREM = HERE / "SOFT_L2_RIGIDITY_FREEZE_THEOREM_2026-07-13.md"
REPORT = HERE / "SOFT_L2_RIGIDITY_FREEZE_REPORT_2026-07-13.md"
PLANTS = HERE / "SOFT_L2_RIGIDITY_FREEZE_PLANTS.json"
MANIFEST = HERE / "ROUTE_B_DATA_MANIFEST.md"
LEAN_RIGIDITY = ROOT / "Q3/Proofs/RouteB/EvenRealAutocorrelationRigidity.lean"
LEAN_ROOT = ROOT / "Q3/Proofs/RouteB/AutocorrelationSquareRootReconstruction.lean"
BUS = ROOT / "ACTIVE/requests/routeB_twolevel_spectral_ladder/bus"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    theorem = THEOREM.read_text(encoding="utf-8")
    report = REPORT.read_text(encoding="utf-8")
    recorded = json.loads(PLANTS.read_text(encoding="utf-8"))
    replay = run_plants()
    manifest = MANIFEST.read_text(encoding="utf-8")
    lean_rigidity = LEAN_RIGIDITY.read_text(encoding="utf-8")
    lean_root = LEAN_ROOT.read_text(encoding="utf-8")

    require(recorded == replay, "SOFT_L2_RIGIDITY_PLANT_RECORD_DRIFT")
    require(recorded["status"] == "ALL_PLANTS_LIVE", "SOFT_L2_RIGIDITY_PLANT_INERT")

    required_theorem_tokens = (
        "SOFT_L2_EvenRealFullAutocorrelationRigidity",
        "SOFT_L2_SOURCE_INJECTIVITY_LOCKED",
        "SOFT_L2_AutocorrelationSquareRootReconstruction",
        "SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED",
        "SOFT_L2_O2_INTERTWINER_LOCKED",
        "kappaHat_m Gamma_m = J kappaHat_m",
        "T(Jq)(z)=Tq(-z)=conj(Tq(conj(z)))=(Tq)^sharp_Z(z)",
        "EVEN_FROM_SIMPLE_GROUND",
        "NO_SIMPLE_EVEN_GROUND",
        "P5_PROSHKA_RECONSTRUCTOR_REFUSED",
        "BUS_010_CREATED=false",
    )
    for token in required_theorem_tokens:
        require(token in theorem, f"SOFT_L2_RIGIDITY_THEOREM_TOKEN_MISSING:{token}")

    require("theorem evenRealFullAutocorrelationRigidity" in lean_rigidity,
            "SOFT_L2_RIGIDITY_LEAN_THEOREM_MISSING")
    require("theorem evenRealFullAutocorrelationRigidity_of_positive_anchor" in lean_rigidity,
            "SOFT_L2_RIGIDITY_LEAN_ANCHOR_MISSING")
    require("[NoZeroDivisors A]" in lean_rigidity,
            "SOFT_L2_RIGIDITY_LEAN_DOMAIN_ROOF_MISSING")
    require("structure AutocorrelationSquareRootReconstructionInput" in lean_root,
            "SOFT_L2_ROOT_INPUT_TYPE_MISSING")
    require("EntireZeroMultiplicityCertificate" in lean_root,
            "SOFT_L2_EVEN_ZERO_CERTIFICATE_TYPE_MISSING")
    require("order_zero_multiple_four" in lean_root,
            "SOFT_L2_ORD0_FOUR_TYPE_MISSING")
    require("type_at_most_two_R" in lean_root,
            "SOFT_L2_TYPE_TWO_R_MISSING")

    for path, text in ((LEAN_RIGIDITY, lean_rigidity), (LEAN_ROOT, lean_root)):
        require("sorry" not in text and "admit" not in text and "exact?" not in text,
                f"SOFT_L2_LEAN_HOLE:{path.name}")

    expected_plants = {
        "PL1": "PL1_EVEN_REAL_RECONSTRUCTION_PASS",
        "PL2": "PL2_NON_EVEN_TWINS_AMBIGUITY_DETECTED",
        "PL3": "PL3_COMPLEX_EVEN_SHARP_SQUARE_MISMATCH_DETECTED",
        "PL4": "PL4_POSITIVE_ANCHOR_SELECTS_GLOBAL_SIGN",
        "P5": "P5_PROSHKA_RECONSTRUCTOR_REFUSED",
    }
    for key, expected in expected_plants.items():
        require(recorded["plants"][key]["observed"] == expected,
                f"SOFT_L2_PLANT_CODE_MISMATCH:{key}")
    require(recorded["plants"]["P5"]["missing_certificate_code"] ==
            "EVEN_ZERO_CERTIFICATE_MISSING_OR_FALSE",
            "SOFT_L2_P5_MISSING_CERT_NOT_REFUSED")
    require(recorded["plants"]["P5"]["forged_certificate_code"] ==
            "ODD_ZERO_MULTIPLICITY_DETECTED",
            "SOFT_L2_P5_FORGED_CERT_NOT_KILLED")

    for token in (
        "SOFT_L2_SOURCE_INJECTIVITY_LOCKED",
        "SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED",
        "SOFT_L2_O2_INTERTWINER_LOCKED",
        "EVEN_FROM_SIMPLE_GROUND",
        "ALL_PLANTS_LIVE",
        "NOT_RH",
    ):
        require(token in report, f"SOFT_L2_RIGIDITY_REPORT_TOKEN_MISSING:{token}")

    for filename in (
        THEOREM.name,
        REPORT.name,
        PLANTS.name,
        LEAN_RIGIDITY.name,
        LEAN_ROOT.name,
    ):
        require(filename in manifest, f"SOFT_L2_RIGIDITY_MANIFEST_MISSING:{filename}")

    require(not list(BUS.glob("010_*")), "SOFT_L2_BUS_010_SMUGGLED")
    require(recorded["bus_010_created"] is False, "SOFT_L2_BUS_010_RECORD_BAD")

    print("PL1_EVEN_REAL_RECONSTRUCTION_PASS")
    print("PL2_NON_EVEN_TWINS_AMBIGUITY_DETECTED")
    print("PL3_COMPLEX_EVEN_SHARP_SQUARE_MISMATCH_DETECTED")
    print("PL4_POSITIVE_ANCHOR_SELECTS_GLOBAL_SIGN")
    print("P5_PROSHKA_RECONSTRUCTOR_REFUSED")
    print("SOFT_L2_SOURCE_INJECTIVITY_LOCKED")
    print("SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED")
    print("SOFT_L2_O2_INTERTWINER_LOCKED")
    print("EVEN_FROM_SIMPLE_GROUND")
    print("ALL_PLANTS_LIVE")
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
