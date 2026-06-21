#!/usr/bin/env python3
"""Fail-closed component Taylor residual payload for Step33A.1-A sub0.

This is the route-B payload selected for the current full-Taylor residual
derivative interval blocker.  The generator records the proof-producing shape
for a cancellation-preserving component Taylor certificate:

1. build Taylor data for omega, omega', E, and E';
2. assemble the raw derivative polynomial exactly;
3. subtract the checked full-Taylor model derivative coefficients;
4. bound the assembled residual polynomial plus one combined remainder.

It does not emit Lean proof data yet.  Omega-prime is now proof-grade, and the
Omega integrated-polynomial derivative crosswalk and the Omega center-anchor
payload are Lean-checked.  The generator still fails closed until the remaining
component Taylor/remainder and assembly fields are present.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any

from generate_step33_a1_sub0_cancellation_residual_interval_certificate import (
    COEFF_DEF,
    LANDING_FILE,
    REQUEST_DIR,
    extract_coefficients,
    file_hash,
    parse_rat,
    rat_text,
)


DEFAULT_COMPONENT_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_cancellation_residual_interval_certificate.json"
)
DEFAULT_OMEGA_PRIME_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_omega_prime_taylor_payload.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.md"
)

SCHEMA = "q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v15"
ROUTE_ID = "STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL"
STATUS_MISSING_OMEGA_PRIME = "fail_closed_missing_omega_omegaprime_taylor_remainder"
STATUS_AFTER_OMEGA_PRIME = (
    "fail_closed_missing_omega_shape_shapederiv_taylor_remainders"
)
STATUS_AFTER_OMEGA_CROSSWALK = (
    "fail_closed_missing_omega_anchor_shape_shapederiv_taylor_remainders"
)
STATUS_AFTER_OMEGA_ANCHOR = (
    "fail_closed_missing_shape_shapederiv_taylor_remainders"
)
STATUS_AFTER_SHAPESQ_RECEIVER = (
    "fail_closed_missing_shapesq_deriv_source_shapederiv_taylor_remainders"
)
STATUS_AFTER_SHAPESQ_DERIV_SOURCE = (
    "fail_closed_shapesq_constant_deriv_source_budget_gap_shapederiv_taylor_remainders"
)
STATUS_AFTER_SHAPESQ_TAYLOR_SOURCE = (
    "fail_closed_shapesq_value_taylor_source_budget_gap_shapederiv_taylor_remainders"
)
STATUS_AFTER_SHAPESQ_INTERVAL_CERT_RECEIVER = (
    "fail_closed_missing_shapesq_deriv_order16_zero_cell_interval_cert"
)
STATUS_AFTER_SHAPESQ_CENTER_COEFF_BRIDGE = (
    "fail_closed_missing_shapesq_deriv_explicit_cauchy_power_series_order16_cert"
)
STATUS_AFTER_SHAPESQ_COEFF0_ROW = (
    "fail_closed_missing_shapesq_deriv_explicit_cauchy_rows_1_to_15_order16_cert"
)
STATUS_AFTER_SHAPESQ_COEFF1_ROW = (
    "fail_closed_missing_shapesq_deriv_explicit_cauchy_rows_2_to_15_order16_cert"
)
STATUS_AFTER_SHAPESQ_ORDER_SHIFT_RECEIVER = (
    "fail_closed_missing_shapesq_deriv_iterated_leibniz_crosswalk_bounds_payload"
)
STATUS_AFTER_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER = (
    "fail_closed_missing_shapesq_deriv_product_leibniz_bounds_payload"
)
STATUS_AFTER_SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER = (
    "fail_closed_missing_shapesq_deriv_shape_derivative_bounds_payload"
)
FIRST_FAILURE_MISSING_OMEGA_PRIME = (
    "STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP"
)
FIRST_FAILURE_AFTER_OMEGA_PRIME = (
    "STEP33_A1_SUB0_OMEGA_SHAPE_SHAPEDERIV_TAYLOR_REMAINDER_GAP"
)
OMEGA_TAYLOR_CROSSWALK_FAILURE = (
    "STEP33_A1_SUB0_OMEGA_TAYLOR_INTEGRATED_POLY_DERIV_CROSSWALK_GAP"
)
FIRST_FAILURE_AFTER_OMEGA_CROSSWALK = (
    "STEP33_A1_SUB0_OMEGA_TAYLOR_CENTER_ANCHOR_PAYLOAD_GAP"
)
FIRST_FAILURE_AFTER_OMEGA_ANCHOR = "STEP33_A1_SUB0_SHAPE_TAYLOR_REMAINDER_GAP"
FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_TAYLOR_SOURCE_GAP"
)
FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE = (
    "STEP33_A1_SUB0_SHAPESQ_CONSTANT_DERIV_TAYLOR_BUDGET_GAP"
)
FIRST_FAILURE_AFTER_SHAPESQ_INTERVAL_CERT_RECEIVER = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_ZERO_CELL_PROOF_GAP"
)
SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_GAP"
)
FIRST_FAILURE_AFTER_SHAPESQ_CENTER_COEFF_BRIDGE = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_POWER_SERIES_GAP"
)
FIRST_FAILURE_AFTER_SHAPESQ_COEFF0_ROW = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_1_TO_15_ORDER16_GAP"
)
FIRST_FAILURE_AFTER_SHAPESQ_COEFF1_ROW = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP"
)
SHAPESQ_DERIV_CENTER_COEFF0_ROW_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_POWER_SERIES_COEFF0_ROW_GAP"
)
SHAPESQ_DERIV_CENTER_COEFF1_ROW_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_POWER_SERIES_COEFF1_ROW_GAP"
)
SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_GAP"
)
FIRST_FAILURE_AFTER_SHAPESQ_ORDER_SHIFT_RECEIVER = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_ITERATED_LEIBNIZ_CROSSWALK_GAP"
)
SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_GAP"
)
FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_PRODUCT_LEIBNIZ_BOUNDS_PAYLOAD_GAP"
)
SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_PRODUCT_LEIBNIZ_BOUNDS_PAYLOAD_GAP"
)
FIRST_FAILURE_AFTER_SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_SHAPE_DERIVATIVE_BOUNDS_PAYLOAD_GAP"
)
SHAPE_TAYLOR_RECEIVER_GAP = (
    "STEP33_A1_SUB0_SHAPESQ_ENDPOINT_TO_TAYLOR_COEFF_REMAINDER_RECEIVER_GAP"
)
SHAPESQ_INTEGRATED_RECEIVER_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_INTEGRATED_POLY_DERIV_CROSSWALK_GAP"
)
SHAPE_DERIV_TAYLOR_RECEIVER_GAP = (
    "STEP33_A1_SUB0_SHAPEDERIV_ENDPOINT_TO_TAYLOR_COEFF_REMAINDER_RECEIVER_GAP"
)
OMEGA_PRIME_CLOSED_FAILURES = [
    FIRST_FAILURE_MISSING_OMEGA_PRIME,
    "STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP",
    "STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP",
    "STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP",
]

TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "fullTaylor_residual_deriv_taylor_enclosure"
)
TARGET_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean"
Q3_ROOT = LANDING_FILE.parents[2]
DEFAULT_ENDPOINT_SUPPORT = Q3_ROOT / TARGET_FILE
OMEGA_TAYLOR_CENTER_ANCHOR_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderLanding.lean"
)
DEFAULT_ENDPOINT_LANDING = Q3_ROOT / OMEGA_TAYLOR_CENTER_ANCHOR_FILE
ENDPOINT_RATIONAL_IMPORT_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointRationalImport.lean"
)
DEFAULT_ENDPOINT_RATIONAL_IMPORT = Q3_ROOT / ENDPOINT_RATIONAL_IMPORT_FILE
SHAPESQ_DERIV_CENTER_COEFF_ROWS_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivCoeffRows.lean"
)
DEFAULT_SHAPESQ_DERIV_CENTER_COEFF_ROWS = (
    Q3_ROOT / SHAPESQ_DERIV_CENTER_COEFF_ROWS_FILE
)
SHAPESQ_DERIV_PRODUCT_BOUNDS_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqProductBounds.lean"
)
DEFAULT_SHAPESQ_DERIV_PRODUCT_BOUNDS = (
    Q3_ROOT / SHAPESQ_DERIV_PRODUCT_BOUNDS_FILE
)
CHUNK_TAYLOR_CHECKER_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean"
)
DEFAULT_CHUNK_TAYLOR_CHECKER = Q3_ROOT / CHUNK_TAYLOR_CHECKER_FILE
TARGET_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "fullTaylor_residual_deriv_closedForm_interval"
)
TARGET_INTERVAL_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean"
OMEGA_PRIME_VALID_THEOREM = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "omegaPrimeGeneratedRemainderCert_valid"
)
OMEGA_PRIME_VALID_THEOREM_LOCAL = (
    "theorem omegaPrimeGeneratedRemainderCert_valid"
)
OMEGA_PRIME_CERT_DEF = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "omegaPrimeGeneratedRemainderCert"
)
OMEGA_TAYLOR_CROSSWALK_THEOREM = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "integratedPoly_deriv_eq_poly"
)
OMEGA_TAYLOR_CROSSWALK_THEOREM_LOCAL = "theorem integratedPoly_deriv_eq_poly"
OMEGA_TAYLOR_CENTER_ANCHOR_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_omegaTaylor_center_anchor"
)
OMEGA_TAYLOR_ANCHOR_LOWER = (
    "-85314634821843642073465861701640867472353398314119326820557162830783014314359848985502357/"
    "16000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
)
OMEGA_TAYLOR_ANCHOR_UPPER = (
    "-426573174109218210367240990627486922998187245419326080653670377242934688213891611916507071/"
    "80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
)
SHAPESQ_ENDPOINT_BOUNDS_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated"
)
SHAPESQ_ENDPOINT_RECEIVER_THEOREM = "ShapeSqEndpointBoundsCert"
SHAPE_VALUE_BOUNDS_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeValueBounds_of_deriv_bounds_and_anchor_generated"
)
SHAPE_DERIV_ANCHOR_BOUNDS_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated"
)
SHAPE_DERIV_INTERVAL_BOUNDS_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeDerivClosedForm_interval_bounds_of_anchor_second_deriv_bound_generated"
)
SHAPESQ_INTEGRATED_RECEIVER_THEOREM = (
    "shapeSqTaylor_bound_of_shapeSqDerivTaylor_bound"
)
SHAPESQ_INTEGRATED_CROSSWALK_THEOREM = (
    "integratedTaylorPolynomial_deriv_eq_base"
)
SHAPESQ_DERIV_TAYLOR_BRIDGE_THEOREM = (
    "shapeSqDerivTaylor_bound_of_endpoint_bounds"
)
SHAPESQ_DERIV_TAYLOR_SOURCE_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorSource_generated"
)
SHAPESQ_DERIV_TAYLOR_COEFF_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated"
)
SHAPESQ_DERIV_TAYLOR_REMAINDER_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorRemainderAbs_generated"
)
SHAPESQ_DERIV_TAYLOR_COARSE_CENTER = "-3/40"
SHAPESQ_DERIV_TAYLOR_COARSE_REMAINDER = "3/40"
SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_SOURCE = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv"
)
SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_STRUCTURE = (
    "ShapeSqDerivTaylorIntervalCert"
)
SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_VALID = (
    "ShapeSqDerivTaylorIntervalCert.Valid"
)
SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_INPUTS = (
    "ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs"
)
SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_SOURCE_THEOREM = (
    "ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource"
)
SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_DEF = (
    "ShapeSqDerivTaylorIntervalCert.single"
)
SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_VALID_THEOREM = (
    "ShapeSqDerivTaylorIntervalCert.Valid.of_single_segment"
)
SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_ABS_DEF = (
    "ShapeSqDerivTaylorIntervalCert.singleAbs"
)
SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_ABS_VALID_THEOREM = (
    "ShapeSqDerivTaylorIntervalCert.Valid.of_single_abs"
)
SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_INTERVAL_CERT_RECEIVER_GAP"
)
SHAPESQ_DERIV_CENTER_POWER_SERIES_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter"
)
SHAPESQ_DERIV_CENTER_HAS_FPOWER_SERIES_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_hasFPowerSeriesAt_center"
)
SHAPESQ_DERIV_CENTER_JET_COEFF_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff"
)
SHAPESQ_DERIV_CENTER_DERIV_FORMULA_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_center_deriv_formula"
)
SHAPESQ_DERIV_CENTER_COEFF_VALID_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_abs"
)
SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_VALID_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_interval"
)
SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_RECEIVER_CLOSED = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_COEFF_INTERVAL_RECEIVER_GAP"
)
SHAPESQ_DERIV_ORDER_SHIFT_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ"
)
SHAPESQ_DERIV_COEFF_ABS_FROM_SHAPESQ_SUCC_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "shapeSqDeriv_powerSeriesCoeff_abs_of_shapeSq_succ_abs"
)
SHAPESQ_DERIV_ORDER16_FROM_SHAPESQ_ORDER17_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "shapeSqDeriv_order16_abs_of_shapeSq_order17_abs"
)
SHAPESQ_DERIV_VALID_FROM_SHAPESQ_DERIVATIVE_ABS_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "shapeSqDeriv_valid_of_shapeSq_derivative_abs"
)
SHAPESQ_DERIV_PRODUCT_BOUNDS_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "shapeSq_derivative_abs_of_shape_derivative_abs"
)
SHAPESQ_DERIV_CENTER_COEFF0_LOWER_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated"
)
SHAPESQ_DERIV_CENTER_COEFF0_UPPER_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated"
)
SHAPESQ_DERIV_CENTER_COEFF0_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "shapeSqDeriv_powerSeriesCoeff0_interval_generated"
)
SHAPESQ_DERIV_CENTER_COEFF1_LOWER_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Lower_generated"
)
SHAPESQ_DERIV_CENTER_COEFF1_UPPER_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Upper_generated"
)
SHAPESQ_DERIV_CENTER_COEFF1_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "shapeSqDeriv_powerSeriesCoeff1_interval_generated"
)
SHAPESQ_TAYLOR_SOURCE_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorSource_generated"
)
SHAPESQ_TAYLOR_COEFF_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated"
)
SHAPESQ_TAYLOR_ANCHOR_COEFF_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated"
)
SHAPESQ_TAYLOR_ANCHOR_ERROR_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated"
)
SHAPESQ_TAYLOR_REMAINDER_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorRemainderAbs_generated"
)
SHAPESQ_TAYLOR_COARSE_REMAINDER = "1/250"

CELL_L = "0"
CELL_U = "1/10"
CENTER = "1/20"
RADIUS = "1/20"
COMPONENT_DEGREE = 15
ASSEMBLED_DEGREE = 45
TARGET_LOWER = "-94119513411/500000000000000000000000000000"
TARGET_UPPER = "1866608532757/500000000000000000000000000000"


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def padded_model_coefficients(
    model_coeffs: list[dict[str, Any]],
    *,
    assembled_degree: int,
) -> list[dict[str, Any]]:
    coeff_by_index = {
        int(item["index"]): parse_rat(str(item["value"])) for item in model_coeffs
    }
    out: list[dict[str, Any]] = []
    for index in range(assembled_degree + 1):
        value = coeff_by_index.get(index, Fraction(0, 1))
        out.append({"index": index, "value": rat_text(value)})
    return out


def component_slots(name: str) -> list[dict[str, Any]]:
    return [
        {
            "index": index,
            "value": None,
            "status": "missing_proof_grade_component_taylor_coeff",
            "component": name,
        }
        for index in range(COMPONENT_DEGREE + 1)
    ]


def linked_component_slots(
    name: str,
    *,
    value_source: str,
    theorem: str,
    proof_status: str,
) -> list[dict[str, Any]]:
    return [
        {
            "index": index,
            "value": None,
            "valueSource": f"{value_source}[{index}]",
            "status": proof_status,
            "component": name,
            "sourceLeanTheorem": theorem,
        }
        for index in range(COMPONENT_DEGREE + 1)
    ]


def omega_prime_status(
    *,
    payload_path: Path,
    lean_path: Path,
) -> dict[str, Any]:
    payload = load_json(payload_path)
    lean_text = lean_path.read_text(encoding="utf-8") if lean_path.exists() else ""
    theorem_found = (
        OMEGA_PRIME_VALID_THEOREM in lean_text
        or OMEGA_PRIME_VALID_THEOREM_LOCAL in lean_text
    )
    payload_proof_status = payload.get("proofStatus", {}) if payload else {}
    payload_closed = bool(
        payload_proof_status.get("omegaPrimeGeneratedValidCertProved")
    )
    proof_grade = theorem_found and payload_closed
    return {
        "payloadPath": str(payload_path),
        "payloadSchema": payload.get("schema") if payload else None,
        "payloadStatus": payload.get("status") if payload else None,
        "leanFile": str(lean_path),
        "validTheorem": OMEGA_PRIME_VALID_THEOREM,
        "validTheoremFound": theorem_found,
        "payloadGeneratedValidCertProved": payload_closed,
        "proofGrade": proof_grade,
        "coeffSource": (
            "omegaPrimePayload.generatorFields.coeff"
            if payload is not None
            else None
        ),
        "remainderSource": (
            "omegaPrimePayload.generatorFields.remainder.remainderAbs"
            if payload is not None
            else None
        ),
        "certDef": OMEGA_PRIME_CERT_DEF,
    }


def omega_taylor_crosswalk_status(*, lean_path: Path) -> dict[str, Any]:
    lean_text = lean_path.read_text(encoding="utf-8") if lean_path.exists() else ""
    theorem_found = (
        OMEGA_TAYLOR_CROSSWALK_THEOREM in lean_text
        or OMEGA_TAYLOR_CROSSWALK_THEOREM_LOCAL in lean_text
    )
    return {
        "leanFile": str(lean_path),
        "leanTheorem": OMEGA_TAYLOR_CROSSWALK_THEOREM,
        "leanTheoremFound": theorem_found,
        "proofGrade": theorem_found,
        "failureClosed": (
            OMEGA_TAYLOR_CROSSWALK_FAILURE if theorem_found else None
        ),
    }


def omega_taylor_center_anchor_status(*, lean_path: Path) -> dict[str, Any]:
    lean_text = lean_path.read_text(encoding="utf-8") if lean_path.exists() else ""
    theorem_found = OMEGA_TAYLOR_CENTER_ANCHOR_THEOREM in lean_text
    lower = parse_rat(OMEGA_TAYLOR_ANCHOR_LOWER)
    upper = parse_rat(OMEGA_TAYLOR_ANCHOR_UPPER)
    return {
        "leanFile": str(lean_path),
        "leanTheorem": OMEGA_TAYLOR_CENTER_ANCHOR_THEOREM,
        "leanTheoremFound": theorem_found,
        "proofGrade": theorem_found,
        "anchorLower": OMEGA_TAYLOR_ANCHOR_LOWER,
        "anchorUpper": OMEGA_TAYLOR_ANCHOR_UPPER,
        "anchorCoeff": rat_text((lower + upper) / 2),
        "anchorErrorAbs": rat_text((upper - lower) / 2),
        "failureClosed": (
            FIRST_FAILURE_AFTER_OMEGA_CROSSWALK if theorem_found else None
        ),
    }


def shape_endpoint_source_status(*, lean_path: Path) -> dict[str, Any]:
    lean_text = lean_path.read_text(encoding="utf-8") if lean_path.exists() else ""
    shape_sq_endpoint_found = SHAPESQ_ENDPOINT_BOUNDS_THEOREM in lean_text
    shape_sq_receiver_found = SHAPESQ_ENDPOINT_RECEIVER_THEOREM in lean_text
    shape_value_found = SHAPE_VALUE_BOUNDS_THEOREM in lean_text
    shape_deriv_anchor_found = SHAPE_DERIV_ANCHOR_BOUNDS_THEOREM in lean_text
    shape_deriv_interval_found = SHAPE_DERIV_INTERVAL_BOUNDS_THEOREM in lean_text
    endpoint_proof_grade = (
        shape_sq_endpoint_found
        and shape_sq_receiver_found
        and shape_value_found
        and shape_deriv_anchor_found
        and shape_deriv_interval_found
    )
    return {
        "leanFile": str(lean_path),
        "shapeSqEndpointBoundsTheorem": SHAPESQ_ENDPOINT_BOUNDS_THEOREM,
        "shapeSqEndpointBoundsTheoremFound": shape_sq_endpoint_found,
        "shapeSqEndpointReceiver": SHAPESQ_ENDPOINT_RECEIVER_THEOREM,
        "shapeSqEndpointReceiverFound": shape_sq_receiver_found,
        "shapeValueBoundsTheorem": SHAPE_VALUE_BOUNDS_THEOREM,
        "shapeValueBoundsTheoremFound": shape_value_found,
        "shapeDerivAnchorBoundsTheorem": SHAPE_DERIV_ANCHOR_BOUNDS_THEOREM,
        "shapeDerivAnchorBoundsTheoremFound": shape_deriv_anchor_found,
        "shapeDerivIntervalBoundsTheorem": SHAPE_DERIV_INTERVAL_BOUNDS_THEOREM,
        "shapeDerivIntervalBoundsTheoremFound": shape_deriv_interval_found,
        "proofGradeEndpointBounds": endpoint_proof_grade,
        "proofGradeTaylorPayload": False,
        "firstShapeReceiverGap": SHAPE_TAYLOR_RECEIVER_GAP,
        "firstShapeDerivReceiverGap": SHAPE_DERIV_TAYLOR_RECEIVER_GAP,
        "whyNotTaylorPayload": (
            "The existing shape endpoint facts bound the shape-square value and "
            "first derivative on the subchunk.  They do not provide "
            "shapeCoeff[0..15], shapeDerivCoeff[0..15], shapeRemainderAbs, or "
            "shapeDerivRemainderAbs in the component Taylor payload convention."
        ),
        "nextReceiverNeeded": (
            "A proof-grade Taylor source for the derivative of the shape-square "
            "term, then the checked integrated receiver can produce the value "
            "Taylor enclosure.  Endpoint/value/deriv interval facts alone do "
            "not provide the high-order Taylor source."
        ),
    }


def shape_integrated_receiver_status(*, lean_path: Path) -> dict[str, Any]:
    lean_text = lean_path.read_text(encoding="utf-8") if lean_path.exists() else ""
    receiver_found = SHAPESQ_INTEGRATED_RECEIVER_THEOREM in lean_text
    crosswalk_found = SHAPESQ_INTEGRATED_CROSSWALK_THEOREM in lean_text
    proof_grade = receiver_found and crosswalk_found
    return {
        "leanFile": str(lean_path),
        "receiverTheorem": SHAPESQ_INTEGRATED_RECEIVER_THEOREM,
        "receiverTheoremFound": receiver_found,
        "integratedCrosswalkTheorem": SHAPESQ_INTEGRATED_CROSSWALK_THEOREM,
        "integratedCrosswalkTheoremFound": crosswalk_found,
        "proofGrade": proof_grade,
        "failureClosed": SHAPESQ_INTEGRATED_RECEIVER_CLOSED if proof_grade else None,
        "nextMissing": (
            FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER
            if proof_grade
            else SHAPE_TAYLOR_RECEIVER_GAP
        ),
        "boundary": (
            "This receiver is not a shape Taylor certificate by itself.  It "
            "requires a proof-grade Taylor/remainder source for the derivative "
            "of shape-square, plus a center anchor budget."
        ),
    }


def shape_sq_deriv_taylor_source_status(
    *,
    endpoint_rational_import_path: Path,
    chunk_taylor_checker_path: Path,
) -> dict[str, Any]:
    endpoint_text = (
        endpoint_rational_import_path.read_text(encoding="utf-8")
        if endpoint_rational_import_path.exists()
        else ""
    )
    checker_text = (
        chunk_taylor_checker_path.read_text(encoding="utf-8")
        if chunk_taylor_checker_path.exists()
        else ""
    )
    source_found = SHAPESQ_DERIV_TAYLOR_SOURCE_THEOREM in endpoint_text
    coeff_found = SHAPESQ_DERIV_TAYLOR_COEFF_DEF in endpoint_text
    remainder_found = SHAPESQ_DERIV_TAYLOR_REMAINDER_DEF in endpoint_text
    bridge_found = SHAPESQ_DERIV_TAYLOR_BRIDGE_THEOREM in checker_text
    proof_grade = source_found and coeff_found and remainder_found and bridge_found
    return {
        "leanFile": str(endpoint_rational_import_path),
        "checkerFile": str(chunk_taylor_checker_path),
        "bridgeTheorem": SHAPESQ_DERIV_TAYLOR_BRIDGE_THEOREM,
        "bridgeTheoremFound": bridge_found,
        "sourceTheorem": SHAPESQ_DERIV_TAYLOR_SOURCE_THEOREM,
        "sourceTheoremFound": source_found,
        "coeffDef": SHAPESQ_DERIV_TAYLOR_COEFF_DEF,
        "coeffDefFound": coeff_found,
        "remainderDef": SHAPESQ_DERIV_TAYLOR_REMAINDER_DEF,
        "remainderDefFound": remainder_found,
        "constantTaylorCenter": SHAPESQ_DERIV_TAYLOR_COARSE_CENTER,
        "constantTaylorRemainderAbs": SHAPESQ_DERIV_TAYLOR_COARSE_REMAINDER,
        "proofGrade": proof_grade,
        "failureClosed": (
            FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER if proof_grade else None
        ),
        "nextMissing": (
            FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE
            if proof_grade
            else FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER
        ),
        "boundary": (
            "This is a proof-grade constant Taylor source for deriv(E^2), "
            "not a final component Taylor closure.  The coarse remainder "
            "3/40 must still pass the shape-square integrated budget and "
            "then the raw-derivative assembly budget."
        ),
    }


def shape_sq_deriv_interval_cert_receiver_status(
    *,
    chunk_taylor_checker_path: Path,
) -> dict[str, Any]:
    checker_text = (
        chunk_taylor_checker_path.read_text(encoding="utf-8")
        if chunk_taylor_checker_path.exists()
        else ""
    )
    source_found = SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_SOURCE in checker_text
    structure_found = SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_STRUCTURE in checker_text
    valid_found = (
        SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_VALID in checker_text
        or "structure Valid (data : ShapeSqDerivTaylorIntervalCert)" in checker_text
    )
    inputs_found = (
        SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_INPUTS in checker_text
        or "theorem toTaylorInputs" in checker_text
    )
    source_theorem_found = (
        SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_SOURCE_THEOREM in checker_text
        or "theorem toShapeSqDerivTaylorSource" in checker_text
    )
    single_def_found = (
        SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_DEF in checker_text
        or "def single\n    (coeff coeffErrorAbs jetLower jetUpper : Fin 16 -> Rat)"
        in checker_text
    )
    single_valid_theorem_found = (
        SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_VALID_THEOREM in checker_text
        or "theorem of_single_segment" in checker_text
    )
    single_abs_def_found = (
        SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_ABS_DEF in checker_text
        or "def singleAbs" in checker_text
    )
    single_abs_valid_theorem_found = (
        SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_ABS_VALID_THEOREM in checker_text
        or "theorem of_single_abs" in checker_text
    )
    proof_grade = (
        source_found
        and structure_found
        and valid_found
        and inputs_found
        and source_theorem_found
    )
    return {
        "checkerFile": str(chunk_taylor_checker_path),
        "sourceDef": SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_SOURCE,
        "sourceDefFound": source_found,
        "certStructure": SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_STRUCTURE,
        "certStructureFound": structure_found,
        "validPredicate": SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_VALID,
        "validPredicateFound": valid_found,
        "toTaylorInputs": SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_INPUTS,
        "toTaylorInputsFound": inputs_found,
        "toShapeSqDerivTaylorSource": (
            SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_SOURCE_THEOREM
        ),
        "toShapeSqDerivTaylorSourceFound": source_theorem_found,
        "singleConstructor": SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_DEF,
        "singleConstructorFound": single_def_found,
        "singleValidityConstructor": (
            SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_VALID_THEOREM
        ),
        "singleValidityConstructorFound": single_valid_theorem_found,
        "singleAbsConstructor": SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_ABS_DEF,
        "singleAbsConstructorFound": single_abs_def_found,
        "singleAbsValidityConstructor": (
            SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_ABS_VALID_THEOREM
        ),
        "singleAbsValidityConstructorFound": single_abs_valid_theorem_found,
        "oneSegmentBookkeepingClosed": (
            single_def_found and single_valid_theorem_found
        ),
        "compactAbsBookkeepingClosed": (
            single_abs_def_found and single_abs_valid_theorem_found
        ),
        "proofGradeReceiver": proof_grade,
        "failureClosed": (
            SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_CLOSED
            if proof_grade
            else None
        ),
        "nextMissing": (
            FIRST_FAILURE_AFTER_SHAPESQ_INTERVAL_CERT_RECEIVER
            if proof_grade
            else FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE
        ),
        "boundary": (
            "This is only the Lean-checked interval-certificate receiver for "
            "future rational center-jet and order-16 rows.  The one-segment "
            "and compact absolute-error constructors close zero-cell "
            "bookkeeping only; they are not the generated ShapeSqDeriv payload "
            "and they do not close the coarse constant-source budget failure."
        ),
    }


def shape_sq_deriv_center_coeff_bridge_status(
    *,
    endpoint_support_path: Path,
) -> dict[str, Any]:
    endpoint_text = (
        endpoint_support_path.read_text(encoding="utf-8")
        if endpoint_support_path.exists()
        else ""
    )
    power_series_found = SHAPESQ_DERIV_CENTER_POWER_SERIES_DEF in endpoint_text
    has_fpower_series_found = (
        SHAPESQ_DERIV_CENTER_HAS_FPOWER_SERIES_THEOREM in endpoint_text
    )
    center_jet_found = SHAPESQ_DERIV_CENTER_JET_COEFF_THEOREM in endpoint_text
    valid_wrapper_found = SHAPESQ_DERIV_CENTER_COEFF_VALID_THEOREM in endpoint_text
    interval_wrapper_found = (
        SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_VALID_THEOREM in endpoint_text
    )
    proof_grade = (
        power_series_found
        and has_fpower_series_found
        and center_jet_found
        and valid_wrapper_found
    )
    proof_grade_interval_receiver = proof_grade and interval_wrapper_found
    return {
        "leanFile": str(endpoint_support_path),
        "powerSeriesDef": SHAPESQ_DERIV_CENTER_POWER_SERIES_DEF,
        "powerSeriesDefFound": power_series_found,
        "hasFPowerSeriesTheorem": SHAPESQ_DERIV_CENTER_HAS_FPOWER_SERIES_THEOREM,
        "hasFPowerSeriesTheoremFound": has_fpower_series_found,
        "centerJetCoeffTheorem": SHAPESQ_DERIV_CENTER_JET_COEFF_THEOREM,
        "centerJetCoeffTheoremFound": center_jet_found,
        "validWrapperTheorem": SHAPESQ_DERIV_CENTER_COEFF_VALID_THEOREM,
        "validWrapperTheoremFound": valid_wrapper_found,
        "intervalWrapperTheorem": (
            SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_VALID_THEOREM
        ),
        "intervalWrapperTheoremFound": interval_wrapper_found,
        "proofGradeBridge": proof_grade,
        "proofGradeIntervalReceiver": proof_grade_interval_receiver,
        "failureClosed": (
            SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_CLOSED
            if proof_grade
            else None
        ),
        "intervalReceiverFailureClosed": (
            SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_RECEIVER_CLOSED
            if proof_grade_interval_receiver
            else None
        ),
        "nextMissing": (
            FIRST_FAILURE_AFTER_SHAPESQ_CENTER_COEFF_BRIDGE
            if proof_grade
            else SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_CLOSED
        ),
        "boundary": (
            "This is only the Lean-checked bridge from the ShapeSqDeriv "
            "center jet to power-series coefficients and the compact "
            "absolute-error/interval certificate wrappers.  It does not "
            "provide exact rational coefficient rows or the order-16 uniform "
            "bound needed by ShapeSqDerivTaylorIntervalCert.Valid."
        ),
    }


def shape_sq_deriv_order_shift_receiver_status(
    *,
    endpoint_support_path: Path,
) -> dict[str, Any]:
    endpoint_text = (
        endpoint_support_path.read_text(encoding="utf-8")
        if endpoint_support_path.exists()
        else ""
    )
    order_shift_found = SHAPESQ_DERIV_ORDER_SHIFT_THEOREM in endpoint_text
    coeff_receiver_found = (
        SHAPESQ_DERIV_COEFF_ABS_FROM_SHAPESQ_SUCC_THEOREM in endpoint_text
    )
    order16_receiver_found = (
        SHAPESQ_DERIV_ORDER16_FROM_SHAPESQ_ORDER17_THEOREM in endpoint_text
    )
    proof_grade = (
        order_shift_found and coeff_receiver_found and order16_receiver_found
    )
    return {
        "leanFile": str(endpoint_support_path),
        "orderShiftTheorem": SHAPESQ_DERIV_ORDER_SHIFT_THEOREM,
        "orderShiftTheoremFound": order_shift_found,
        "coefficientReceiverTheorem": (
            SHAPESQ_DERIV_COEFF_ABS_FROM_SHAPESQ_SUCC_THEOREM
        ),
        "coefficientReceiverTheoremFound": coeff_receiver_found,
        "order16ReceiverTheorem": SHAPESQ_DERIV_ORDER16_FROM_SHAPESQ_ORDER17_THEOREM,
        "order16ReceiverTheoremFound": order16_receiver_found,
        "proofGradeReceiver": proof_grade,
        "failureClosed": (
            SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_CLOSED
            if proof_grade
            else None
        ),
        "nextMissing": (
            FIRST_FAILURE_AFTER_SHAPESQ_ORDER_SHIFT_RECEIVER
            if proof_grade
            else FIRST_FAILURE_AFTER_SHAPESQ_COEFF1_ROW
        ),
        "boundary": (
            "This is only the Lean-checked structural receiver "
            "iteratedDeriv^j(ShapeSqDeriv) = iteratedDeriv^(j+1)(shape^2), "
            "plus coefficient-row and order-16 receiver interfaces.  It does "
            "not provide the product-Leibniz/Cauchy bounds for derivatives of "
            "the shape function, and it does not close rows 2..15 or the "
            "order-16 uniform bound."
        ),
    }


def shape_sq_deriv_shape_sq_derivative_receiver_status(
    *,
    endpoint_support_path: Path,
) -> dict[str, Any]:
    endpoint_text = (
        endpoint_support_path.read_text(encoding="utf-8")
        if endpoint_support_path.exists()
        else ""
    )
    receiver_found = (
        SHAPESQ_DERIV_VALID_FROM_SHAPESQ_DERIVATIVE_ABS_THEOREM
        in endpoint_text
    )
    return {
        "leanFile": str(endpoint_support_path),
        "validFromShapeSqDerivativeAbsTheorem": (
            SHAPESQ_DERIV_VALID_FROM_SHAPESQ_DERIVATIVE_ABS_THEOREM
        ),
        "validFromShapeSqDerivativeAbsTheoremFound": receiver_found,
        "proofGradeReceiver": receiver_found,
        "failureClosed": (
            SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_CLOSED
            if receiver_found
            else None
        ),
        "nextMissing": (
            FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER
            if receiver_found
            else FIRST_FAILURE_AFTER_SHAPESQ_ORDER_SHIFT_RECEIVER
        ),
        "boundary": (
            "This is only the Lean-checked normalization receiver from "
            "bounds on iterated derivatives of the shape-square function "
            "into ShapeSqDerivTaylorIntervalCert.Valid.  It does not prove "
            "the product-Leibniz formula or any Cauchy/derivative bounds for "
            "the shape function itself."
        ),
    }


def shape_sq_deriv_product_bounds_receiver_status(
    *,
    product_bounds_path: Path,
) -> dict[str, Any]:
    product_bounds_text = (
        product_bounds_path.read_text(encoding="utf-8")
        if product_bounds_path.exists()
        else ""
    )
    receiver_found = SHAPESQ_DERIV_PRODUCT_BOUNDS_THEOREM in product_bounds_text
    return {
        "leanFile": str(product_bounds_path),
        "productBoundsTheorem": SHAPESQ_DERIV_PRODUCT_BOUNDS_THEOREM,
        "productBoundsTheoremFound": receiver_found,
        "proofGradeReceiver": receiver_found,
        "failureClosed": (
            SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER_CLOSED
            if receiver_found
            else None
        ),
        "nextMissing": (
            FIRST_FAILURE_AFTER_SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER
            if receiver_found
            else FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER
        ),
        "boundary": (
            "This is only the Lean-checked Mathlib product-bound receiver "
            "from proof-grade derivative bounds on the active shape function "
            "to derivative bounds for the square of that shape function.  It "
            "does not provide those shape derivative bounds, rational rows "
            "2..15, or the order-17 full-cell bound consumed by the "
            "ShapeSqDeriv interval certificate."
        ),
    }


def shape_sq_deriv_center_coeff_rows_status(
    *,
    coeff_rows_path: Path,
) -> dict[str, Any]:
    rows_text = (
        coeff_rows_path.read_text(encoding="utf-8")
        if coeff_rows_path.exists()
        else ""
    )
    lower_def_found = SHAPESQ_DERIV_CENTER_COEFF0_LOWER_DEF in rows_text
    upper_def_found = SHAPESQ_DERIV_CENTER_COEFF0_UPPER_DEF in rows_text
    row0_theorem_found = SHAPESQ_DERIV_CENTER_COEFF0_INTERVAL_THEOREM in rows_text
    row0_proof_grade = lower_def_found and upper_def_found and row0_theorem_found
    row1_lower_def_found = SHAPESQ_DERIV_CENTER_COEFF1_LOWER_DEF in rows_text
    row1_upper_def_found = SHAPESQ_DERIV_CENTER_COEFF1_UPPER_DEF in rows_text
    row1_theorem_found = SHAPESQ_DERIV_CENTER_COEFF1_INTERVAL_THEOREM in rows_text
    row1_proof_grade = (
        row0_proof_grade
        and row1_lower_def_found
        and row1_upper_def_found
        and row1_theorem_found
    )
    rows_closed_count = 2 if row1_proof_grade else 1 if row0_proof_grade else 0
    return {
        "leanFile": str(coeff_rows_path),
        "row0LowerDef": SHAPESQ_DERIV_CENTER_COEFF0_LOWER_DEF,
        "row0LowerDefFound": lower_def_found,
        "row0UpperDef": SHAPESQ_DERIV_CENTER_COEFF0_UPPER_DEF,
        "row0UpperDefFound": upper_def_found,
        "row0IntervalTheorem": SHAPESQ_DERIV_CENTER_COEFF0_INTERVAL_THEOREM,
        "row0IntervalTheoremFound": row0_theorem_found,
        "row1LowerDef": SHAPESQ_DERIV_CENTER_COEFF1_LOWER_DEF,
        "row1LowerDefFound": row1_lower_def_found,
        "row1UpperDef": SHAPESQ_DERIV_CENTER_COEFF1_UPPER_DEF,
        "row1UpperDefFound": row1_upper_def_found,
        "row1IntervalTheorem": SHAPESQ_DERIV_CENTER_COEFF1_INTERVAL_THEOREM,
        "row1IntervalTheoremFound": row1_theorem_found,
        "proofGradeRow0": row0_proof_grade,
        "proofGradeRow1": row1_proof_grade,
        "proofGradeRows": row0_proof_grade,
        "rowsClosedCount": rows_closed_count,
        "rowsRequiredCount": COMPONENT_DEGREE + 1,
        "missingRows": list(range(rows_closed_count, COMPONENT_DEGREE + 1)),
        "order16UniformBoundPresent": False,
        "failureClosed": (
            SHAPESQ_DERIV_CENTER_COEFF0_ROW_CLOSED
            if row0_proof_grade
            else None
        ),
        "failureClosedRow1": (
            SHAPESQ_DERIV_CENTER_COEFF1_ROW_CLOSED
            if row1_proof_grade
            else None
        ),
        "nextMissing": (
            FIRST_FAILURE_AFTER_SHAPESQ_COEFF1_ROW
            if row1_proof_grade
            else FIRST_FAILURE_AFTER_SHAPESQ_COEFF0_ROW
            if row0_proof_grade
            else FIRST_FAILURE_AFTER_SHAPESQ_CENTER_COEFF_BRIDGE
        ),
        "boundary": (
            "This source closes only the j=0 and j=1 rational interval rows "
            "for the ShapeSqDeriv center power series.  Rows 2..15 and the "
            "full-cell order-16 uniform bound are still missing, so it is not "
            "yet a ShapeSqDerivTaylorIntervalCert.Valid payload."
            if row1_proof_grade
            else
            "This source closes only the j=0 rational interval row for the "
            "ShapeSqDeriv center power series.  Rows 1..15 and the full-cell "
            "order-16 uniform bound are still missing, so it is not yet a "
            "ShapeSqDerivTaylorIntervalCert.Valid payload."
        ),
    }


def shape_sq_taylor_source_status(
    *,
    endpoint_rational_import_path: Path,
    chunk_taylor_checker_path: Path,
    shape_sq_deriv_source_closed: bool,
) -> dict[str, Any]:
    endpoint_text = (
        endpoint_rational_import_path.read_text(encoding="utf-8")
        if endpoint_rational_import_path.exists()
        else ""
    )
    checker_text = (
        chunk_taylor_checker_path.read_text(encoding="utf-8")
        if chunk_taylor_checker_path.exists()
        else ""
    )
    source_found = SHAPESQ_TAYLOR_SOURCE_THEOREM in endpoint_text
    coeff_found = SHAPESQ_TAYLOR_COEFF_DEF in endpoint_text
    anchor_coeff_found = SHAPESQ_TAYLOR_ANCHOR_COEFF_DEF in endpoint_text
    anchor_error_found = SHAPESQ_TAYLOR_ANCHOR_ERROR_DEF in endpoint_text
    remainder_found = SHAPESQ_TAYLOR_REMAINDER_DEF in endpoint_text
    receiver_found = SHAPESQ_INTEGRATED_RECEIVER_THEOREM in checker_text
    proof_grade = (
        shape_sq_deriv_source_closed
        and source_found
        and coeff_found
        and anchor_coeff_found
        and anchor_error_found
        and remainder_found
        and receiver_found
    )
    return {
        "leanFile": str(endpoint_rational_import_path),
        "checkerFile": str(chunk_taylor_checker_path),
        "receiverTheorem": SHAPESQ_INTEGRATED_RECEIVER_THEOREM,
        "receiverTheoremFound": receiver_found,
        "sourceTheorem": SHAPESQ_TAYLOR_SOURCE_THEOREM,
        "sourceTheoremFound": source_found,
        "coeffDef": SHAPESQ_TAYLOR_COEFF_DEF,
        "coeffDefFound": coeff_found,
        "anchorCoeffDef": SHAPESQ_TAYLOR_ANCHOR_COEFF_DEF,
        "anchorCoeffDefFound": anchor_coeff_found,
        "anchorErrorDef": SHAPESQ_TAYLOR_ANCHOR_ERROR_DEF,
        "anchorErrorDefFound": anchor_error_found,
        "remainderDef": SHAPESQ_TAYLOR_REMAINDER_DEF,
        "remainderDefFound": remainder_found,
        "constantTaylorRemainderAbs": SHAPESQ_TAYLOR_COARSE_REMAINDER,
        "proofGrade": proof_grade,
        "failureClosed": None,
        "nextMissing": FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE,
        "boundary": (
            "This is a proof-grade value Taylor enclosure for shape-square "
            "built from the checked constant derivative source and the center "
            "anchor budget.  It is not raw-derivative assembly and the coarse "
            "1/250 remainder is expected to be too wide for the final "
            "residual budget unless a later exact assembly test proves "
            "otherwise."
        ),
    }


def component_taylor_status(
    omega_prime_closed: bool,
    omega_crosswalk_closed: bool,
    omega_anchor_closed: bool,
    shape_endpoint_available: bool,
    shape_integrated_receiver_closed: bool,
    shape_sq_deriv_center_coeff_bridge_closed: bool,
    shape_sq_deriv_interval_cert_receiver_closed: bool,
    shape_sq_deriv_center_coeff0_row_closed: bool,
    shape_sq_deriv_center_coeff1_row_closed: bool,
    shape_sq_deriv_order_shift_receiver_closed: bool,
    shape_sq_deriv_shape_sq_derivative_receiver_closed: bool,
    shape_sq_deriv_product_bounds_receiver_closed: bool,
    shape_sq_deriv_source_closed: bool,
    shape_sq_taylor_source_closed: bool,
) -> dict[str, Any]:
    return {
        "omegaDerivTaylor": (
            {
                "status": "FORMAL",
                "leanTheorem": OMEGA_PRIME_VALID_THEOREM,
                "leanChecked": True,
                "receiver": "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid",
                "missing": False,
                "assembledIntoRawDerivative": False,
            }
            if omega_prime_closed
            else {
                "status": "MISSING_PROOF_GRADE_REMAINDER",
                "leanTheorem": OMEGA_PRIME_VALID_THEOREM,
                "leanChecked": False,
                "receiver": "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid",
                "missing": True,
                "assembledIntoRawDerivative": False,
            }
        ),
        "omegaTaylor": (
            {
                "status": "CROSSWALK_AND_CENTER_ANCHOR_FORMAL_MISSING_COMPONENT_ASSEMBLY",
                "missing": True,
                "integratedPolyDerivCrosswalk": {
                    "status": "FORMAL",
                    "leanTheorem": OMEGA_TAYLOR_CROSSWALK_THEOREM,
                    "leanChecked": True,
                    "missing": False,
                },
                "centerAnchor": {
                    "status": "FORMAL",
                    "leanTheorem": OMEGA_TAYLOR_CENTER_ANCHOR_THEOREM,
                    "leanChecked": True,
                    "missing": False,
                },
                "firstMissing": FIRST_FAILURE_AFTER_OMEGA_ANCHOR,
            }
            if omega_anchor_closed
            else
            {
                "status": "CROSSWALK_FORMAL_MISSING_CENTER_ANCHOR_PAYLOAD",
                "missing": True,
                "integratedPolyDerivCrosswalk": {
                    "status": "FORMAL",
                    "leanTheorem": OMEGA_TAYLOR_CROSSWALK_THEOREM,
                    "leanChecked": True,
                    "missing": False,
                },
                "firstMissing": FIRST_FAILURE_AFTER_OMEGA_CROSSWALK,
            }
            if omega_crosswalk_closed
            else {
                "status": "MISSING_PROOF_GRADE_REMAINDER",
                "missing": True,
                "integratedPolyDerivCrosswalk": {
                    "status": "MISSING_FORMAL_CROSSWALK",
                    "leanTheorem": OMEGA_TAYLOR_CROSSWALK_THEOREM,
                    "leanChecked": False,
                    "missing": True,
                },
                "firstMissing": OMEGA_TAYLOR_CROSSWALK_FAILURE,
            }
        ),
        "shapeTaylor": {
            "status": (
                "SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER_FORMAL_MISSING_SHAPE_DERIVATIVE_BOUNDS_PAYLOAD"
                if shape_sq_deriv_product_bounds_receiver_closed
                else
                "SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_FORMAL_MISSING_PRODUCT_LEIBNIZ_BOUNDS_PAYLOAD"
                if shape_sq_deriv_shape_sq_derivative_receiver_closed
                else
                "SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_FORMAL_MISSING_ITERATED_LEIBNIZ_CROSSWALK_BOUNDS"
                if shape_sq_deriv_order_shift_receiver_closed
                else
                "SHAPESQ_DERIV_COEFF0_1_ROWS_FORMAL_MISSING_ROWS_2_TO_15_ORDER16"
                if shape_sq_deriv_center_coeff1_row_closed
                else
                "SHAPESQ_DERIV_COEFF0_ROW_FORMAL_MISSING_ROWS_1_TO_15_ORDER16"
                if shape_sq_deriv_center_coeff0_row_closed
                else
                "SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_FORMAL_MISSING_EXPLICIT_ROWS"
                if shape_sq_deriv_center_coeff_bridge_closed
                else
                "SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_FORMAL_MISSING_ZERO_CELL_ROWS"
                if shape_sq_deriv_interval_cert_receiver_closed
                else "SHAPESQ_VALUE_TAYLOR_SOURCE_FORMAL_BUDGET_NOT_ASSEMBLED"
                if shape_sq_taylor_source_closed
                else "CONSTANT_DERIV_TAYLOR_SOURCE_FORMAL_BUDGET_NOT_ASSEMBLED"
                if shape_sq_deriv_source_closed
                else "INTEGRATED_RECEIVER_FORMAL_MISSING_SHAPESQ_DERIV_TAYLOR_SOURCE"
                if shape_integrated_receiver_closed
                else "ENDPOINT_BOUNDS_FORMAL_MISSING_TAYLOR_COEFF_REMAINDER_RECEIVER"
                if shape_endpoint_available
                else "MISSING_PROOF_GRADE_REMAINDER"
            ),
            "missing": True,
            "endpointBoundsAvailable": shape_endpoint_available,
            "integratedReceiverAvailable": shape_integrated_receiver_closed,
            "shapeSqDerivCenterCoeffBridgeAvailable": (
                shape_sq_deriv_center_coeff_bridge_closed
            ),
            "shapeSqDerivIntervalCertReceiverAvailable": (
                shape_sq_deriv_interval_cert_receiver_closed
            ),
            "shapeSqDerivCenterCoeff0RowAvailable": (
                shape_sq_deriv_center_coeff0_row_closed
            ),
            "shapeSqDerivCenterCoeff1RowAvailable": (
                shape_sq_deriv_center_coeff1_row_closed
            ),
            "shapeSqDerivOrderShiftReceiverAvailable": (
                shape_sq_deriv_order_shift_receiver_closed
            ),
            "shapeSqDerivShapeSqDerivativeReceiverAvailable": (
                shape_sq_deriv_shape_sq_derivative_receiver_closed
            ),
            "shapeSqDerivProductBoundsReceiverAvailable": (
                shape_sq_deriv_product_bounds_receiver_closed
            ),
            "shapeSqDerivTaylorSourceAvailable": shape_sq_deriv_source_closed,
            "shapeSqTaylorSourceAvailable": shape_sq_taylor_source_closed,
            "firstReceiverGap": (
                FIRST_FAILURE_AFTER_SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER
                if shape_sq_deriv_product_bounds_receiver_closed
                else
                FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER
                if shape_sq_deriv_shape_sq_derivative_receiver_closed
                else
                FIRST_FAILURE_AFTER_SHAPESQ_ORDER_SHIFT_RECEIVER
                if shape_sq_deriv_order_shift_receiver_closed
                else
                FIRST_FAILURE_AFTER_SHAPESQ_COEFF1_ROW
                if shape_sq_deriv_center_coeff1_row_closed
                else
                FIRST_FAILURE_AFTER_SHAPESQ_COEFF0_ROW
                if shape_sq_deriv_center_coeff0_row_closed
                else
                FIRST_FAILURE_AFTER_SHAPESQ_CENTER_COEFF_BRIDGE
                if shape_sq_deriv_center_coeff_bridge_closed
                else
                FIRST_FAILURE_AFTER_SHAPESQ_INTERVAL_CERT_RECEIVER
                if shape_sq_deriv_interval_cert_receiver_closed
                else FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE
                if shape_sq_taylor_source_closed
                else FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE
                if shape_sq_deriv_source_closed
                else FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER
                if shape_integrated_receiver_closed
                else SHAPE_TAYLOR_RECEIVER_GAP
            ),
        },
        "shapeDerivTaylor": {
            "status": (
                "ENDPOINT_DERIV_BOUNDS_FORMAL_MISSING_TAYLOR_COEFF_REMAINDER_RECEIVER"
                if shape_endpoint_available
                else "MISSING_PROOF_GRADE_REMAINDER"
            ),
            "missing": True,
            "endpointBoundsAvailable": shape_endpoint_available,
            "firstReceiverGap": SHAPE_DERIV_TAYLOR_RECEIVER_GAP,
        },
        "assemblyLeanWritten": False,
        "overallProofSafe": False,
    }


def build_report(
    *,
    landing_path: Path,
    component_ledger_path: Path,
    omega_prime_payload_path: Path,
    endpoint_support_path: Path,
    endpoint_landing_path: Path,
    endpoint_rational_import_path: Path,
    shape_sq_deriv_center_coeff_rows_path: Path,
    shape_sq_deriv_product_bounds_path: Path,
    chunk_taylor_checker_path: Path,
) -> dict[str, Any]:
    model_coeffs, source_lines = extract_coefficients(landing_path)
    component_ledger = load_json(component_ledger_path)
    omega_prime = omega_prime_status(
        payload_path=omega_prime_payload_path,
        lean_path=endpoint_support_path,
    )
    omega_prime_closed = bool(omega_prime["proofGrade"])
    omega_crosswalk = omega_taylor_crosswalk_status(lean_path=endpoint_support_path)
    omega_crosswalk_closed = omega_prime_closed and bool(omega_crosswalk["proofGrade"])
    omega_anchor = omega_taylor_center_anchor_status(lean_path=endpoint_landing_path)
    omega_anchor_closed = omega_crosswalk_closed and bool(omega_anchor["proofGrade"])
    shape_endpoint = shape_endpoint_source_status(
        lean_path=endpoint_rational_import_path
    )
    shape_endpoint_available = bool(shape_endpoint["proofGradeEndpointBounds"])
    shape_integrated_receiver = shape_integrated_receiver_status(
        lean_path=chunk_taylor_checker_path
    )
    shape_integrated_receiver_closed = bool(shape_integrated_receiver["proofGrade"])
    shape_sq_deriv_source = shape_sq_deriv_taylor_source_status(
        endpoint_rational_import_path=endpoint_rational_import_path,
        chunk_taylor_checker_path=chunk_taylor_checker_path,
    )
    shape_sq_deriv_source_closed = (
        shape_integrated_receiver_closed
        and shape_endpoint_available
        and bool(shape_sq_deriv_source["proofGrade"])
    )
    shape_sq_deriv_interval_cert_receiver = (
        shape_sq_deriv_interval_cert_receiver_status(
            chunk_taylor_checker_path=chunk_taylor_checker_path
        )
    )
    shape_sq_deriv_interval_cert_receiver_closed = bool(
        shape_sq_deriv_interval_cert_receiver["proofGradeReceiver"]
    )
    shape_sq_deriv_center_coeff_bridge = (
        shape_sq_deriv_center_coeff_bridge_status(
            endpoint_support_path=endpoint_support_path
        )
    )
    shape_sq_deriv_center_coeff_bridge_closed = (
        shape_sq_deriv_interval_cert_receiver_closed
        and bool(shape_sq_deriv_center_coeff_bridge["proofGradeBridge"])
    )
    shape_sq_deriv_center_coeff_interval_receiver_closed = (
        shape_sq_deriv_center_coeff_bridge_closed
        and bool(shape_sq_deriv_center_coeff_bridge["proofGradeIntervalReceiver"])
    )
    shape_sq_deriv_center_coeff_rows = shape_sq_deriv_center_coeff_rows_status(
        coeff_rows_path=shape_sq_deriv_center_coeff_rows_path
    )
    shape_sq_deriv_center_coeff0_row_closed = (
        shape_sq_deriv_center_coeff_interval_receiver_closed
        and bool(shape_sq_deriv_center_coeff_rows["proofGradeRow0"])
    )
    shape_sq_deriv_center_coeff1_row_closed = (
        shape_sq_deriv_center_coeff_interval_receiver_closed
        and bool(shape_sq_deriv_center_coeff_rows["proofGradeRow1"])
    )
    shape_sq_deriv_order_shift_receiver = (
        shape_sq_deriv_order_shift_receiver_status(
            endpoint_support_path=endpoint_support_path
        )
    )
    shape_sq_deriv_order_shift_receiver_closed = (
        shape_sq_deriv_center_coeff_interval_receiver_closed
        and bool(shape_sq_deriv_order_shift_receiver["proofGradeReceiver"])
    )
    shape_sq_deriv_shape_sq_derivative_receiver = (
        shape_sq_deriv_shape_sq_derivative_receiver_status(
            endpoint_support_path=endpoint_support_path
        )
    )
    shape_sq_deriv_shape_sq_derivative_receiver_closed = (
        shape_sq_deriv_order_shift_receiver_closed
        and bool(
            shape_sq_deriv_shape_sq_derivative_receiver["proofGradeReceiver"]
        )
    )
    shape_sq_deriv_product_bounds_receiver = (
        shape_sq_deriv_product_bounds_receiver_status(
            product_bounds_path=shape_sq_deriv_product_bounds_path
        )
    )
    shape_sq_deriv_product_bounds_receiver_closed = (
        shape_sq_deriv_shape_sq_derivative_receiver_closed
        and bool(shape_sq_deriv_product_bounds_receiver["proofGradeReceiver"])
    )
    shape_sq_taylor_source = shape_sq_taylor_source_status(
        endpoint_rational_import_path=endpoint_rational_import_path,
        chunk_taylor_checker_path=chunk_taylor_checker_path,
        shape_sq_deriv_source_closed=shape_sq_deriv_source_closed,
    )
    shape_sq_taylor_source_closed = bool(shape_sq_taylor_source["proofGrade"])
    if (
        omega_anchor_closed
        and shape_sq_deriv_center_coeff1_row_closed
        and shape_sq_deriv_product_bounds_receiver_closed
    ):
        status = STATUS_AFTER_SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER
    elif (
        omega_anchor_closed
        and shape_sq_deriv_center_coeff1_row_closed
        and shape_sq_deriv_shape_sq_derivative_receiver_closed
    ):
        status = STATUS_AFTER_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER
        first_failure = (
            FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER
        )
    elif (
        omega_anchor_closed
        and shape_sq_deriv_center_coeff1_row_closed
        and shape_sq_deriv_order_shift_receiver_closed
    ):
        status = STATUS_AFTER_SHAPESQ_ORDER_SHIFT_RECEIVER
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_ORDER_SHIFT_RECEIVER
    elif omega_anchor_closed and shape_sq_deriv_center_coeff1_row_closed:
        status = STATUS_AFTER_SHAPESQ_COEFF1_ROW
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_COEFF1_ROW
    elif omega_anchor_closed and shape_sq_deriv_center_coeff0_row_closed:
        status = STATUS_AFTER_SHAPESQ_COEFF0_ROW
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_COEFF0_ROW
    elif omega_anchor_closed and shape_sq_deriv_center_coeff_bridge_closed:
        status = STATUS_AFTER_SHAPESQ_CENTER_COEFF_BRIDGE
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_CENTER_COEFF_BRIDGE
    elif omega_anchor_closed and shape_sq_deriv_interval_cert_receiver_closed:
        status = STATUS_AFTER_SHAPESQ_INTERVAL_CERT_RECEIVER
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_INTERVAL_CERT_RECEIVER
    elif omega_anchor_closed and shape_sq_taylor_source_closed:
        status = STATUS_AFTER_SHAPESQ_TAYLOR_SOURCE
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE
    elif omega_anchor_closed and shape_sq_deriv_source_closed:
        status = STATUS_AFTER_SHAPESQ_DERIV_SOURCE
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE
    elif omega_anchor_closed and shape_integrated_receiver_closed:
        status = STATUS_AFTER_SHAPESQ_RECEIVER
        first_failure = FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER
    elif omega_anchor_closed:
        status = STATUS_AFTER_OMEGA_ANCHOR
        first_failure = FIRST_FAILURE_AFTER_OMEGA_ANCHOR
    elif omega_crosswalk_closed:
        status = STATUS_AFTER_OMEGA_CROSSWALK
        first_failure = FIRST_FAILURE_AFTER_OMEGA_CROSSWALK
    elif omega_prime_closed:
        status = STATUS_AFTER_OMEGA_PRIME
        first_failure = OMEGA_TAYLOR_CROSSWALK_FAILURE
    else:
        status = STATUS_MISSING_OMEGA_PRIME
        first_failure = FIRST_FAILURE_MISSING_OMEGA_PRIME
    closed_historical_failures: list[str] = []
    if omega_prime_closed:
        closed_historical_failures.extend(OMEGA_PRIME_CLOSED_FAILURES)
    if omega_crosswalk_closed:
        closed_historical_failures.append(OMEGA_TAYLOR_CROSSWALK_FAILURE)
    if omega_anchor_closed:
        closed_historical_failures.append(FIRST_FAILURE_AFTER_OMEGA_CROSSWALK)
    if shape_integrated_receiver_closed:
        closed_historical_failures.append(SHAPESQ_INTEGRATED_RECEIVER_CLOSED)
    if shape_sq_deriv_source_closed:
        closed_historical_failures.append(FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER)
    if shape_sq_deriv_interval_cert_receiver_closed:
        closed_historical_failures.append(
            SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_CLOSED
        )
    if shape_sq_deriv_center_coeff_bridge_closed:
        closed_historical_failures.append(SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_CLOSED)
    if shape_sq_deriv_center_coeff_interval_receiver_closed:
        closed_historical_failures.append(
            SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_RECEIVER_CLOSED
        )
    if shape_sq_deriv_center_coeff0_row_closed:
        closed_historical_failures.append(SHAPESQ_DERIV_CENTER_COEFF0_ROW_CLOSED)
    if shape_sq_deriv_center_coeff1_row_closed:
        closed_historical_failures.append(SHAPESQ_DERIV_CENTER_COEFF1_ROW_CLOSED)
    if shape_sq_deriv_order_shift_receiver_closed:
        closed_historical_failures.append(SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_CLOSED)
    if shape_sq_deriv_shape_sq_derivative_receiver_closed:
        closed_historical_failures.append(
            SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_CLOSED
        )
    if shape_sq_deriv_product_bounds_receiver_closed:
        closed_historical_failures.append(SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER_CLOSED)
    omega_deriv_coeff = (
        linked_component_slots(
            "omegaDeriv",
            value_source="omegaPrimePayload.generatorFields.coeff",
            theorem=OMEGA_PRIME_VALID_THEOREM,
            proof_status="formal_available_via_omega_prime_valid_cert_not_assembled",
        )
        if omega_prime_closed
        else component_slots("omegaDeriv")
    )
    omega_deriv_remainder = (
        {
            "value": None,
            "valueSource": "omegaPrimePayload.generatorFields.remainder.remainderAbs",
            "status": "formal_available_via_omega_prime_valid_cert_not_assembled",
            "sourceLeanTheorem": OMEGA_PRIME_VALID_THEOREM,
        }
        if omega_prime_closed
        else None
    )
    target_lower = parse_rat(TARGET_LOWER)
    target_upper = parse_rat(TARGET_UPPER)

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
            "status": status,
            "chosenRoute": "B",
            "advisorySource": "browser_proshka_route_advice_not_proof_evidence",
            "firstFailure": first_failure,
            "closedHistoricalFailures": closed_historical_failures,
            "failureCodes": list(dict.fromkeys([
                first_failure,
                SHAPE_TAYLOR_RECEIVER_GAP,
                SHAPESQ_INTEGRATED_RECEIVER_CLOSED,
                FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER,
                FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SOURCE,
                SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_CLOSED,
                SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_CLOSED,
                SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_RECEIVER_CLOSED,
                SHAPESQ_DERIV_CENTER_COEFF0_ROW_CLOSED,
                SHAPESQ_DERIV_CENTER_COEFF1_ROW_CLOSED,
                SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_CLOSED,
                SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_CLOSED,
                SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER_CLOSED,
                FIRST_FAILURE_AFTER_SHAPESQ_CENTER_COEFF_BRIDGE,
                FIRST_FAILURE_AFTER_SHAPESQ_COEFF0_ROW,
                FIRST_FAILURE_AFTER_SHAPESQ_COEFF1_ROW,
                FIRST_FAILURE_AFTER_SHAPESQ_ORDER_SHIFT_RECEIVER,
                FIRST_FAILURE_AFTER_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER,
                FIRST_FAILURE_AFTER_SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER,
                FIRST_FAILURE_AFTER_SHAPESQ_INTERVAL_CERT_RECEIVER,
                SHAPE_DERIV_TAYLOR_RECEIVER_GAP,
                "STEP33_A1_SUB0_SHAPE_TAYLOR_REMAINDER_GAP",
                "STEP33_A1_SUB0_SHAPE_SHAPEDERIV_TAYLOR_REMAINDER_GAP",
                "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_GAP",
                "STEP33_A1_SUB0_RESIDUAL_POLYNOMIAL_RANGE_GAP",
            "STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL_LEAN_PAYLOAD_MISSING",
        ])),
        "cell": {
            "cellL": CELL_L,
            "cellU": CELL_U,
            "center": CENTER,
            "radius": RADIUS,
            "targetLower": TARGET_LOWER,
            "targetUpper": TARGET_UPPER,
            "targetWidth": rat_text(target_upper - target_lower),
        },
        "degrees": {
            "componentDegree": COMPONENT_DEGREE,
            "assembledDegree": ASSEMBLED_DEGREE,
            "modelDegree": 15,
        },
        "targetTheorem": {
            "file": TARGET_FILE,
            "name": TARGET_THEOREM,
            "statementAscii": (
                f"theorem {TARGET_THEOREM} {{eta : Real}} "
                "(heta : eta in Set.Icc 0 (1/10)) : "
                "norm ((RawIntegrandDerivClosedForm eta - "
                "rawOmegaATaylorPolynomial 15 (1/20) ResidualDerivmodelCoeff eta) - "
                "rawOmegaATaylorPolynomial 45 (1/20) ResidualTaylorCoeff eta) <= "
                "ResidualTaylorRemainderAbs"
            ),
        },
        "downstreamIntervalTheorem": {
            "file": TARGET_INTERVAL_FILE,
            "name": TARGET_INTERVAL_THEOREM,
            "consumes": [
                TARGET_THEOREM,
                "residualPolynomialLower",
                "residualPolynomialUpper",
                "finalResidualLower",
                "finalResidualUpper",
                "budgetPassed",
            ],
        },
            "generatorFields": {
                "omegaCoeff": component_slots("omega"),
                "omegaIntegratedDerivCrosswalk": {
                    "status": (
                        "formal_available_with_center_anchor"
                        if omega_anchor_closed
                        else "formal_available_missing_center_anchor"
                        if omega_crosswalk_closed
                        else "missing_formal_crosswalk"
                    ),
                    "sourceLeanTheorem": OMEGA_TAYLOR_CROSSWALK_THEOREM,
                    "anchorLeanTheorem": OMEGA_TAYLOR_CENTER_ANCHOR_THEOREM,
                    "anchorLeanTheoremFound": omega_anchor_closed,
                    "anchorCoeff": (
                        omega_anchor["anchorCoeff"] if omega_anchor_closed else None
                    ),
                    "anchorErrorAbs": (
                        omega_anchor["anchorErrorAbs"] if omega_anchor_closed else None
                    ),
                    "anchorCoeffStatus": (
                        "formal_center_anchor_payload"
                        if omega_anchor_closed
                        else "missing_center_anchor_payload"
                    ),
                    "omegaPrimeCoeffSource": (
                        "omegaPrimePayload.generatorFields.coeff"
                        if omega_prime_closed
                        else None
                    ),
                },
                "omegaDerivCoeff": omega_deriv_coeff,
                "shapeCoeff": component_slots("shape"),
                "shapeDerivCoeff": component_slots("shapeDeriv"),
                "shapeEndpointSource": shape_endpoint,
                "shapeIntegratedReceiverSource": shape_integrated_receiver,
                "shapeSqDerivTaylorSource": shape_sq_deriv_source,
                "shapeSqDerivIntervalCertReceiverSource": (
                    shape_sq_deriv_interval_cert_receiver
                ),
                "shapeSqDerivCenterCoeffBridgeSource": (
                    shape_sq_deriv_center_coeff_bridge
                ),
                "shapeSqDerivOrderShiftReceiverSource": (
                    shape_sq_deriv_order_shift_receiver
                ),
                "shapeSqDerivShapeSqDerivativeReceiverSource": (
                    shape_sq_deriv_shape_sq_derivative_receiver
                ),
                "shapeSqDerivProductBoundsReceiverSource": (
                    shape_sq_deriv_product_bounds_receiver
                ),
                "shapeSqDerivCenterCoeffRowsSource": (
                    shape_sq_deriv_center_coeff_rows
                ),
                "shapeSqTaylorSource": shape_sq_taylor_source,
            "omegaRemainderAbs": None,
            "omegaDerivRemainderAbs": omega_deriv_remainder,
            "shapeRemainderAbs": None,
            "shapeDerivRemainderAbs": None,
            "assembledRawDerivCoeff": None,
            "modelDerivCoeff": model_coeffs,
            "modelDerivCoeffPaddedToAssembledDegree": padded_model_coefficients(
                model_coeffs, assembled_degree=ASSEMBLED_DEGREE
            ),
            "residualTaylorCoeff": None,
            "productTruncationRemainderAbs": None,
            "componentPropagationRemainderAbs": None,
            "residualTaylorRemainderAbs": None,
            "residualPolynomialLower": None,
            "residualPolynomialUpper": None,
            "finalResidualLower": None,
            "finalResidualUpper": None,
        },
            "proofStatus": {
                "exactCoefficientAssemblyPassed": False,
                "componentTaylorProofsPresent": False,
                "omegaTaylorIntegratedPolyDerivCrosswalkProofPresent": (
                    omega_crosswalk_closed
                ),
                "omegaTaylorCenterAnchorPayloadPresent": omega_anchor_closed,
                "omegaDerivTaylorProofPresent": omega_prime_closed,
                "shapeEndpointBoundsProofPresent": shape_endpoint_available,
                "shapeSqIntegratedTaylorReceiverPresent": (
                    shape_integrated_receiver_closed
                ),
                "shapeSqDerivTaylorSourcePresent": (
                    shape_sq_deriv_source_closed
                ),
                "shapeSqDerivIntervalCertReceiverPresent": (
                    shape_sq_deriv_interval_cert_receiver_closed
                ),
                "shapeSqDerivCenterCoeffBridgePresent": (
                    shape_sq_deriv_center_coeff_bridge_closed
                ),
                "shapeSqDerivCenterCoeffIntervalReceiverPresent": (
                    shape_sq_deriv_center_coeff_interval_receiver_closed
                ),
                "shapeSqDerivCenterCoeff0RowPresent": (
                    shape_sq_deriv_center_coeff0_row_closed
                ),
                "shapeSqDerivCenterCoeff1RowPresent": (
                    shape_sq_deriv_center_coeff1_row_closed
                ),
                "shapeSqDerivOrderShiftReceiverPresent": (
                    shape_sq_deriv_order_shift_receiver_closed
                ),
                "shapeSqDerivShapeSqDerivativeReceiverPresent": (
                    shape_sq_deriv_shape_sq_derivative_receiver_closed
                ),
                "shapeSqDerivProductBoundsReceiverPresent": (
                    shape_sq_deriv_product_bounds_receiver_closed
                ),
                "shapeSqDerivCenterCoeffRowsClosedCount": (
                    shape_sq_deriv_center_coeff_rows["rowsClosedCount"]
                    if shape_sq_deriv_center_coeff0_row_closed
                    else 0
                ),
                "shapeSqDerivCenterCoeffRowsRequiredCount": (
                    shape_sq_deriv_center_coeff_rows["rowsRequiredCount"]
                ),
                "shapeSqDerivOrder16UniformBoundPresent": (
                    shape_sq_deriv_center_coeff_rows[
                        "order16UniformBoundPresent"
                    ]
                ),
                "shapeSqTaylorSourcePresent": shape_sq_taylor_source_closed,
                "shapeTaylorReceiverPresent": shape_sq_taylor_source_closed,
                "shapeDerivTaylorReceiverPresent": False,
                "omegaDerivTaylorProofAssembledIntoRawDerivative": False,
                "residualPolynomialRangePassed": False,
                "finalBudgetPassed": False,
                "proofSafeClosedFields": (
                    (1 if omega_prime_closed else 0)
                    + (1 if omega_crosswalk_closed else 0)
                    + (1 if omega_anchor_closed else 0)
                    + (1 if shape_integrated_receiver_closed else 0)
                    + (1 if shape_sq_deriv_source_closed else 0)
                    + (1 if shape_sq_deriv_interval_cert_receiver_closed else 0)
                    + (1 if shape_sq_deriv_center_coeff_bridge_closed else 0)
                    + (
                        1
                        if shape_sq_deriv_center_coeff_interval_receiver_closed
                        else 0
                    )
                    + (1 if shape_sq_deriv_center_coeff0_row_closed else 0)
                    + (1 if shape_sq_deriv_center_coeff1_row_closed else 0)
                    + (
                        1
                        if shape_sq_deriv_order_shift_receiver_closed
                        else 0
                    )
                    + (
                        1
                        if shape_sq_deriv_shape_sq_derivative_receiver_closed
                        else 0
                    )
                    + (
                        1
                        if shape_sq_deriv_product_bounds_receiver_closed
                        else 0
                    )
                    + (1 if shape_sq_taylor_source_closed else 0)
                ),
                "outLeanWritten": False,
            },
            "componentClosureLedger": {
                "omega": (
                    "formal_center_anchor_available_missing_component_assembly"
                    if omega_anchor_closed
                    else "formal_derivative_crosswalk_missing_center_anchor_payload"
                    if omega_crosswalk_closed
                    else "missing_proof_grade_component_taylor_remainder"
                ),
                "omegaDeriv": (
                    "formal_available_not_assembled"
                    if omega_prime_closed
                else "missing_proof_grade_component_taylor_remainder"
            ),
            "shape": (
                "product_bounds_receiver_formal_missing_shape_derivative_bounds_payload"
                if shape_sq_deriv_product_bounds_receiver_closed
                else
                "shape_square_derivative_receiver_formal_missing_product_bounds_receiver"
                if shape_sq_deriv_shape_sq_derivative_receiver_closed
                else
                "order_shift_receiver_formal_missing_iterated_leibniz_crosswalk_bounds"
                if shape_sq_deriv_order_shift_receiver_closed
                else
                "center_coeff0_1_rows_formal_missing_rows_2_to_15_order16_bound"
                if shape_sq_deriv_center_coeff1_row_closed
                else
                "center_coeff0_row_formal_missing_rows_1_to_15_order16_bound"
                if shape_sq_deriv_center_coeff0_row_closed
                else
                "center_coeff_bridge_formal_missing_explicit_cauchy_rows_order16_bound"
                if shape_sq_deriv_center_coeff_bridge_closed
                else
                "interval_cert_receiver_formal_missing_zero_cell_rows"
                if shape_sq_deriv_interval_cert_receiver_closed
                else
                "constant_shapesq_value_source_formal_budget_not_assembled"
                if shape_sq_taylor_source_closed
                else "constant_shapesq_deriv_source_formal_budget_not_assembled"
                if shape_sq_deriv_source_closed
                else "integrated_receiver_formal_missing_shapesq_deriv_taylor_source"
                if shape_integrated_receiver_closed
                else "endpoint_bounds_formal_missing_component_taylor_receiver"
                if shape_endpoint_available
                else "missing_proof_grade_component_taylor_remainder"
            ),
            "shapeDeriv": (
                "endpoint_deriv_bounds_formal_missing_component_taylor_receiver"
                if shape_endpoint_available
                else "missing_proof_grade_component_taylor_remainder"
            ),
            },
            "componentTaylorStatus": component_taylor_status(
                omega_prime_closed,
                omega_crosswalk_closed,
                omega_anchor_closed,
                shape_endpoint_available,
                shape_integrated_receiver_closed,
                shape_sq_deriv_center_coeff_bridge_closed,
                shape_sq_deriv_interval_cert_receiver_closed,
                shape_sq_deriv_center_coeff0_row_closed,
                shape_sq_deriv_center_coeff1_row_closed,
                shape_sq_deriv_order_shift_receiver_closed,
                shape_sq_deriv_shape_sq_derivative_receiver_closed,
                shape_sq_deriv_product_bounds_receiver_closed,
                shape_sq_deriv_source_closed,
                shape_sq_taylor_source_closed,
            ),
            "omegaPrimeTaylorSource": omega_prime,
            "omegaTaylorCrosswalkSource": omega_crosswalk,
            "omegaTaylorCenterAnchorSource": omega_anchor,
            "shapeEndpointSource": shape_endpoint,
            "shapeIntegratedReceiverSource": shape_integrated_receiver,
            "shapeSqDerivTaylorSource": shape_sq_deriv_source,
            "shapeSqDerivIntervalCertReceiverSource": (
                shape_sq_deriv_interval_cert_receiver
            ),
            "shapeSqDerivCenterCoeffBridgeSource": (
                shape_sq_deriv_center_coeff_bridge
            ),
            "shapeSqDerivOrderShiftReceiverSource": (
                shape_sq_deriv_order_shift_receiver
            ),
            "shapeSqDerivShapeSqDerivativeReceiverSource": (
                shape_sq_deriv_shape_sq_derivative_receiver
            ),
            "shapeSqDerivProductBoundsReceiverSource": (
                shape_sq_deriv_product_bounds_receiver
            ),
            "shapeSqDerivCenterCoeffRowsSource": (
                shape_sq_deriv_center_coeff_rows
            ),
            "shapeSqTaylorSource": shape_sq_taylor_source,
            "existingLeanInputs": {
            "modelDerivCoeffSource": COEFF_DEF,
            "modelDerivCoeffCount": len(model_coeffs),
            "fullTaylorPolynomialDerivativeCrosswalk": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "fullTaylor_polynomial_deriv_eq_derivmodel"
            ),
            "fullTaylorResidualDerivativeCrosswalk": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "fullTaylor_residual_deriv_eq_closedForm"
            ),
            "fullTaylorDirectValidityBridge": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "fullTaylor_direct_segment_cert_valid_of_residual_bounds"
            ),
                "omegaDerivTaylorValidCert": OMEGA_PRIME_VALID_THEOREM,
                "omegaTaylorIntegratedPolyDerivCrosswalk": (
                    OMEGA_TAYLOR_CROSSWALK_THEOREM
                ),
                "omegaTaylorCenterAnchor": OMEGA_TAYLOR_CENTER_ANCHOR_THEOREM,
                "shapeSqEndpointBounds": SHAPESQ_ENDPOINT_BOUNDS_THEOREM,
                "shapeSqEndpointReceiver": SHAPESQ_ENDPOINT_RECEIVER_THEOREM,
                "shapeSqIntegratedTaylorReceiver": SHAPESQ_INTEGRATED_RECEIVER_THEOREM,
                "shapeSqIntegratedTaylorCrosswalk": SHAPESQ_INTEGRATED_CROSSWALK_THEOREM,
                "shapeSqDerivTaylorBridge": SHAPESQ_DERIV_TAYLOR_BRIDGE_THEOREM,
                "shapeSqDerivTaylorSource": SHAPESQ_DERIV_TAYLOR_SOURCE_THEOREM,
                "shapeSqDerivIntervalCertReceiver": (
                    SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_SOURCE_THEOREM
                ),
                "shapeSqDerivIntervalCertSingle": (
                    SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_DEF
                ),
                "shapeSqDerivIntervalCertSingleValid": (
                    SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_VALID_THEOREM
                ),
                "shapeSqDerivIntervalCertSingleAbs": (
                    SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_ABS_DEF
                ),
                "shapeSqDerivIntervalCertSingleAbsValid": (
                    SHAPESQ_DERIV_INTERVAL_CERT_SINGLE_ABS_VALID_THEOREM
                ),
                "shapeSqDerivCenterPowerSeries": (
                    SHAPESQ_DERIV_CENTER_POWER_SERIES_DEF
                ),
                "shapeSqDerivCenterHasFPowerSeries": (
                    SHAPESQ_DERIV_CENTER_HAS_FPOWER_SERIES_THEOREM
                ),
                "shapeSqDerivCenterJetCoeff": (
                    SHAPESQ_DERIV_CENTER_JET_COEFF_THEOREM
                ),
                "shapeSqDerivCenterDerivFormula": (
                    SHAPESQ_DERIV_CENTER_DERIV_FORMULA_THEOREM
                ),
                "shapeSqDerivCenterCoeffValid": (
                    SHAPESQ_DERIV_CENTER_COEFF_VALID_THEOREM
                ),
                "shapeSqDerivCenterCoeffIntervalValid": (
                    SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_VALID_THEOREM
                ),
                "shapeSqDerivOrderShift": (
                    SHAPESQ_DERIV_ORDER_SHIFT_THEOREM
                ),
                "shapeSqDerivCoeffAbsFromShapeSqSucc": (
                    SHAPESQ_DERIV_COEFF_ABS_FROM_SHAPESQ_SUCC_THEOREM
                ),
                "shapeSqDerivOrder16FromShapeSqOrder17": (
                    SHAPESQ_DERIV_ORDER16_FROM_SHAPESQ_ORDER17_THEOREM
                ),
                "shapeSqDerivValidFromShapeSqDerivativeAbs": (
                    SHAPESQ_DERIV_VALID_FROM_SHAPESQ_DERIVATIVE_ABS_THEOREM
                ),
                "shapeSqDerivProductBounds": SHAPESQ_DERIV_PRODUCT_BOUNDS_THEOREM,
                "shapeSqDerivCenterCoeff0Lower": (
                    SHAPESQ_DERIV_CENTER_COEFF0_LOWER_DEF
                ),
                "shapeSqDerivCenterCoeff0Upper": (
                    SHAPESQ_DERIV_CENTER_COEFF0_UPPER_DEF
                ),
                "shapeSqDerivCenterCoeff0Interval": (
                    SHAPESQ_DERIV_CENTER_COEFF0_INTERVAL_THEOREM
                ),
                "shapeSqDerivCenterCoeff1Lower": (
                    SHAPESQ_DERIV_CENTER_COEFF1_LOWER_DEF
                ),
                "shapeSqDerivCenterCoeff1Upper": (
                    SHAPESQ_DERIV_CENTER_COEFF1_UPPER_DEF
                ),
                "shapeSqDerivCenterCoeff1Interval": (
                    SHAPESQ_DERIV_CENTER_COEFF1_INTERVAL_THEOREM
                ),
                "shapeSqTaylorSource": SHAPESQ_TAYLOR_SOURCE_THEOREM,
                "shapeSqTaylorCoeff": SHAPESQ_TAYLOR_COEFF_DEF,
                "shapeValueBounds": SHAPE_VALUE_BOUNDS_THEOREM,
                "shapeDerivAnchorBounds": SHAPE_DERIV_ANCHOR_BOUNDS_THEOREM,
                "shapeDerivIntervalBounds": SHAPE_DERIV_INTERVAL_BOUNDS_THEOREM,
        },
        "proshkaDecision": {
            "chosen": "B_component_taylor_route",
            "followupChosen": (
                "B_shapesq_deriv_product_bounds_receiver_after_mathlib_bridge"
                if shape_sq_deriv_product_bounds_receiver_closed
                else
                "B_shapesq_deriv_shape_square_derivative_receiver_after_proshka_browser"
                if shape_sq_deriv_shape_sq_derivative_receiver_closed
                else
                "B_shapesq_deriv_order_shift_receiver_after_proshka"
                if shape_sq_deriv_order_shift_receiver_closed
                else
                "A_shapesq_deriv_power_series_coeff1_row_leaf_after_coeff0"
                if shape_sq_deriv_center_coeff1_row_closed
                else "A_shapesq_deriv_power_series_coeff0_row_leaf"
            ),
            "followupFailureClosed": (
                SHAPESQ_DERIV_PRODUCT_BOUNDS_RECEIVER_CLOSED
                if shape_sq_deriv_product_bounds_receiver_closed
                else
                SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_CLOSED
                if shape_sq_deriv_shape_sq_derivative_receiver_closed
                else
                SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_CLOSED
                if shape_sq_deriv_order_shift_receiver_closed
                else
                SHAPESQ_DERIV_CENTER_COEFF1_ROW_CLOSED
                if shape_sq_deriv_center_coeff1_row_closed
                else SHAPESQ_DERIV_CENTER_COEFF0_ROW_CLOSED
                if shape_sq_deriv_center_coeff0_row_closed
                else
                SHAPESQ_DERIV_CENTER_COEFF_INTERVAL_RECEIVER_CLOSED
                if shape_sq_deriv_center_coeff_interval_receiver_closed
                else
                SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_CLOSED
                if shape_sq_deriv_center_coeff_bridge_closed
                else SHAPESQ_DERIV_INTERVAL_CERT_RECEIVER_CLOSED
                if shape_sq_deriv_interval_cert_receiver_closed
                else None
            ),
            "followupFirstMissing": first_failure,
            "whyNotA": (
                "Earlier endpoint finite-cover machinery still lacked proof-grade "
                "Omega/OmegaPrime/E/EPrime remainder sources; it would create "
                "another empty checker first."
            ),
            "whyNotC": (
                "A monolithic direct Lean proof would mix component expansions, "
                "product assembly, model subtraction, and range proof in one "
                "hard-to-audit theorem."
            ),
            "followupWhyA": (
                "After the ShapeSqDeriv receiver reduced the problem to "
                "bounds on derivatives of shape-square, the smallest "
                "proof-moving patch was an isolated Mathlib product-bound "
                "receiver.  It proves that proof-grade derivative bounds for "
                "the active shape function imply the needed shape-square "
                "derivative bounds, but it leaves those shape derivative "
                "bounds as the first live payload gap."
                if shape_sq_deriv_product_bounds_receiver_closed
                else
                "Proshka's browser-visible route advice selected the reusable "
                "ShapeSqDeriv/iterated-Leibniz path, not manual row replay.  "
                "The smallest local checked patch was a normalization receiver "
                "from shape-square derivative bounds into "
                "ShapeSqDerivTaylorIntervalCert.Valid.  It closes only that "
                "receiver and leaves the product-Leibniz/Cauchy derivative "
                "bounds payload as the first live gap."
                if shape_sq_deriv_shape_sq_derivative_receiver_closed
                else
                "After Proshka selected route B, the smallest proof-moving "
                "patch was an isolated structural order-shift receiver: "
                "iterated derivatives of ShapeSqDeriv reduce to one higher "
                "derivative of shape-square.  This advances the interface "
                "without claiming rows 2..15 or the order-16 uniform bound."
                if shape_sq_deriv_order_shift_receiver_closed
                else
                "After the interval coefficient receiver and j=0 row became "
                "Lean-checked, the smallest proof-moving patch was an "
                "isolated j=1 coefficient row.  It advances the real "
                "proof-data layer without claiming rows 2..15 or the "
                "order-16 uniform bound."
                if shape_sq_deriv_center_coeff1_row_closed
                else
                "After the interval coefficient receiver became Lean-checked, "
                "the smallest proof-moving patch was an isolated j=0 "
                "coefficient row.  It advances the real proof-data layer "
                "without claiming rows 1..15 or the order-16 uniform bound."
            ),
        },
        "sourceStatus": {
            "componentLedgerPath": str(component_ledger_path),
            "componentLedgerSchema": (
                component_ledger.get("schema") if component_ledger else None
            ),
            "componentLedgerStatus": (
                component_ledger.get("status") if component_ledger else None
            ),
            "omegaPrimePayloadPath": str(omega_prime_payload_path),
            "omegaPrimePayloadStatus": omega_prime.get("payloadStatus"),
            "omegaPrimeProofGrade": omega_prime_closed,
            "omegaTaylorCrosswalkProofGrade": omega_crosswalk_closed,
            "omegaTaylorCenterAnchorProofGrade": omega_anchor_closed,
            "shapeEndpointBoundsProofGrade": shape_endpoint_available,
            "shapeSqIntegratedTaylorReceiverProofGrade": (
                shape_integrated_receiver_closed
            ),
            "shapeSqDerivTaylorSourceProofGrade": (
                shape_sq_deriv_source_closed
            ),
            "shapeSqDerivIntervalCertReceiverProofGrade": (
                shape_sq_deriv_interval_cert_receiver_closed
            ),
                "shapeSqDerivCenterCoeffBridgeProofGrade": (
                    shape_sq_deriv_center_coeff_bridge_closed
                ),
            "shapeSqDerivCenterCoeffIntervalReceiverProofGrade": (
                shape_sq_deriv_center_coeff_interval_receiver_closed
            ),
            "shapeSqDerivCenterCoeff0RowProofGrade": (
                shape_sq_deriv_center_coeff0_row_closed
            ),
            "shapeSqDerivCenterCoeff1RowProofGrade": (
                shape_sq_deriv_center_coeff1_row_closed
            ),
            "shapeSqDerivOrderShiftReceiverProofGrade": (
                shape_sq_deriv_order_shift_receiver_closed
            ),
            "shapeSqDerivShapeSqDerivativeReceiverProofGrade": (
                shape_sq_deriv_shape_sq_derivative_receiver_closed
            ),
            "shapeSqDerivProductBoundsReceiverProofGrade": (
                shape_sq_deriv_product_bounds_receiver_closed
            ),
            "shapeSqDerivCenterCoeffRowsClosedCount": (
                shape_sq_deriv_center_coeff_rows["rowsClosedCount"]
                if shape_sq_deriv_center_coeff0_row_closed
                else 0
            ),
            "shapeSqDerivCenterCoeffRowsRequiredCount": (
                shape_sq_deriv_center_coeff_rows["rowsRequiredCount"]
            ),
            "shapeSqTaylorSourceProofGrade": shape_sq_taylor_source_closed,
        },
        "sourceDefinitionLines": source_lines,
        "sourceDefinitionHashes": {
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean": file_hash(
                landing_path
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_cancellation_residual_interval_certificate.json": (
                file_hash(component_ledger_path)
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_omega_prime_taylor_payload.json": (
                file_hash(omega_prime_payload_path)
            ),
            TARGET_FILE: file_hash(endpoint_support_path),
            OMEGA_TAYLOR_CENTER_ANCHOR_FILE: file_hash(endpoint_landing_path),
            ENDPOINT_RATIONAL_IMPORT_FILE: file_hash(endpoint_rational_import_path),
            SHAPESQ_DERIV_CENTER_COEFF_ROWS_FILE: file_hash(
                shape_sq_deriv_center_coeff_rows_path
            ),
            SHAPESQ_DERIV_PRODUCT_BOUNDS_FILE: file_hash(
                shape_sq_deriv_product_bounds_path
            ),
            CHUNK_TAYLOR_CHECKER_FILE: file_hash(chunk_taylor_checker_path),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    if report["proofStatus"]["shapeSqDerivProductBoundsReceiverPresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver,",
            "coarse constant shape-square Taylor source, ShapeSqDeriv",
            "interval-certificate receiver, the ShapeSqDeriv center-coeff",
            "bridge, coefficient rows `j = 0,1`, the structural",
            "ShapeSqDeriv order-shift receiver, the direct shape-square",
            "derivative receiver into `ShapeSqDerivTaylorIntervalCert.Valid`,",
            "and the isolated product-bound receiver from active shape",
            "derivative bounds to shape-square derivative bounds are now",
            "Lean-checked.",
            "This does not provide the proof-grade derivative bounds for the",
            "shape function, rational rows `2..15`, or the full-cell order-17",
            "shape-square bound.  The first live proof gap is now the",
            "shape-derivative bounds payload consumed by the product-bound",
            "receiver.",
            "Raw-derivative assembly, residual polynomial bounds, and the",
            "final interval theorem remain open.",
        ]
    elif report["proofStatus"]["shapeSqDerivShapeSqDerivativeReceiverPresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver,",
            "coarse constant shape-square Taylor source, ShapeSqDeriv",
            "interval-certificate receiver, the ShapeSqDeriv center-coeff",
            "bridge, coefficient rows `j = 0,1`, the structural",
            "ShapeSqDeriv order-shift receiver, and the direct",
            "shape-square derivative receiver into",
            "`ShapeSqDerivTaylorIntervalCert.Valid` are now Lean-checked.",
            "This does not prove the product-Leibniz formula, Cauchy bounds,",
            "rows `2..15`, or the full-cell order-16 uniform bound.  The",
            "first live proof gap is now the product-Leibniz/Cauchy",
            "derivative-bound payload for the shape-square function.",
            "Raw-derivative assembly, residual polynomial bounds, and the",
            "final interval theorem remain open.",
        ]
    elif report["proofStatus"]["shapeSqDerivOrderShiftReceiverPresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver,",
            "coarse constant shape-square Taylor source, ShapeSqDeriv",
            "interval-certificate receiver, the ShapeSqDeriv center-coeff",
            "bridge, coefficient rows `j = 0,1`, and the structural",
            "ShapeSqDeriv order-shift receiver are now Lean-checked.",
            "This does not close rows `2..15` or the full-cell order-16",
            "uniform bound.  The first live proof gap is now the",
            "product-Leibniz/Cauchy crosswalk and derivative-bound payload",
            "for the shape-square function itself.",
            "Raw-derivative assembly, residual polynomial bounds, and the",
            "final interval theorem remain open.",
        ]
    elif report["proofStatus"]["shapeSqDerivCenterCoeff1RowPresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver,",
            "coarse constant shape-square Taylor source, ShapeSqDeriv",
            "interval-certificate receiver, the ShapeSqDeriv center-coeff",
            "bridge, and the first two ShapeSqDeriv power-series coefficient",
            "rows are now Lean-checked.",
            "This closes only the `j = 0` and `j = 1` rows.  Rows `2..15`",
            "and the full-cell order-16 uniform bound are still missing, so",
            "`ShapeSqDerivTaylorIntervalCert.Valid` is not closed.",
            "Raw-derivative assembly, residual polynomial bounds, and the",
            "final interval theorem remain open.",
        ]
    elif report["proofStatus"]["shapeSqDerivCenterCoeff0RowPresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver,",
            "coarse constant shape-square Taylor source, ShapeSqDeriv",
            "interval-certificate receiver, the ShapeSqDeriv center-coeff",
            "bridge, and the first ShapeSqDeriv power-series coefficient row",
            "are now Lean-checked.",
            "This closes only the `j = 0` row.  Rows `1..15` and the",
            "full-cell order-16 uniform bound are still missing, so",
            "`ShapeSqDerivTaylorIntervalCert.Valid` is not closed.",
            "Raw-derivative assembly, residual polynomial bounds, and the",
            "final interval theorem remain open.",
        ]
    elif report["proofStatus"]["shapeSqDerivCenterCoeffBridgePresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver,",
            "coarse constant shape-square Taylor source, ShapeSqDeriv",
            "interval-certificate receiver, and the ShapeSqDeriv",
            "center-coefficient bridge are now Lean-checked.",
            "The compact center bridge connects center jets to power-series",
            "coefficients and the absolute-error/interval certificate wrappers,",
            "but it adds no exact rational rows.  The first live gate is now",
            "the explicit Cauchy/power-series coefficient source and order-16",
            "uniform bound needed by `ShapeSqDerivTaylorIntervalCert.Valid`.",
            "Raw-derivative assembly, residual polynomial bounds, and the",
            "final interval theorem remain open.",
        ]
    elif report["proofStatus"]["shapeSqDerivIntervalCertReceiverPresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver,",
            "coarse constant shape-square Taylor source, and the new",
            "ShapeSqDeriv interval-certificate receiver are now Lean-checked.",
            "The compact absolute-error constructor closes more zero-cell",
            "bookkeeping but adds no analytic rows.  The coarse source remains",
            "fail-closed for the current budget; the productive next gate is",
            "the concrete zero-cell rational interval certificate rows for",
            "`ShapeSqDerivTaylorIntervalCert.Valid`.",
            "Raw-derivative assembly, residual polynomial bounds, and the",
            "final interval theorem remain open.",
        ]
    elif report["proofStatus"]["shapeSqTaylorSourcePresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver,",
            "constant derivative Taylor source, and the induced value Taylor",
            "source for shape-square are now Lean-checked.  The node remains",
            "fail-closed at the exact budget/assembly test for this coarse",
            "source, followed by shape-derivative Taylor data, raw-derivative",
            "assembly, residual polynomial bounds, and the final interval",
            "theorem.",
        ]
    elif report["proofStatus"]["shapeSqDerivTaylorSourcePresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, shape-square integrated Taylor receiver, and a",
            "proof-grade constant Taylor source for the derivative of",
            "shape-square are now Lean-checked.  The next immediate",
            "proof-producing gate is the exact budget/assembly test for this",
            "coarse shape-square source, followed by shape-derivative Taylor",
            "data, raw-derivative assembly, residual polynomial bounds, and",
            "the final interval theorem.",
        ]
    elif report["proofStatus"]["shapeSqIntegratedTaylorReceiverPresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk, center",
            "anchor payload, and shape-square integrated Taylor receiver are",
            "now Lean-checked.  The next immediate proof-producing gate is a",
            "proof-grade Taylor/remainder source for the derivative of the",
            "shape-square term.  Shape-derivative Taylor data, raw-derivative",
            "assembly, residual polynomial bounds, and the final interval",
            "theorem remain open.",
        ]
    elif report["proofStatus"]["omegaTaylorCenterAnchorPayloadPresent"]:
        decision_text = [
            "The Omega integrated-polynomial derivative crosswalk and center",
            "anchor payload are now Lean-checked.  The next immediate",
            "proof-producing gate is the `shape` / `shapeDeriv` Taylor",
            "remainder data, followed by raw-derivative assembly, model",
            "subtraction, residual polynomial bounds, and the final interval",
            "theorem.",
        ]
    else:
        decision_text = [
            "The next immediate proof-producing gate is the Omega center-anchor",
            "payload needed by the checked integrated-polynomial derivative",
            "crosswalk.  After that, `shape` and `shapeDeriv` still need",
            "proof-grade Taylor/remainder data, plus a raw-derivative assembly",
            "bridge that consumes the checked `omega`/`omegaDeriv` sources.",
            "Only after those component proofs exist may the generator assemble",
            "the raw derivative, subtract the model derivative coefficients,",
            "bound the residual polynomial, and emit Lean for the interval",
            "theorem.",
        ]

    lines = [
        "# Step33A.1-A Sub0 Component Taylor Residual Payload",
        "",
        "Fail-closed route-B payload. This is not Lean proof data and does",
        "not close Step33A.1-A.",
        "",
        "## Status",
        "",
        f"- schema: `{report['schema']}`",
        f"- route: `{report['routeId']}`",
        f"- chosen route: `{report['chosenRoute']}`",
        f"- status: `{report['status']}`",
        f"- first failure: `{report['firstFailure']}`",
        "- closed historical failures: "
        f"`{', '.join(report['closedHistoricalFailures']) if report['closedHistoricalFailures'] else 'none'}`",
        f"- advisory source: `{report['advisorySource']}`",
        f"- proof-safe closed fields: `{report['proofStatus']['proofSafeClosedFields']}`",
        f"- Lean emitted: `{report['proofStatus']['outLeanWritten']}`",
        "",
        "## Target",
        "",
        f"- theorem: `{report['targetTheorem']['name']}`",
        f"- file: `{report['targetTheorem']['file']}`",
        f"- component degree: `{report['degrees']['componentDegree']}`",
        f"- assembled degree: `{report['degrees']['assembledDegree']}`",
        f"- center: `{report['cell']['center']}`",
        f"- radius: `{report['cell']['radius']}`",
        f"- target interval: `[{report['cell']['targetLower']}, {report['cell']['targetUpper']}]`",
        "",
        "```text",
        report["targetTheorem"]["statementAscii"],
        "```",
        "",
        "## Model Derivative Coefficients",
        "",
        f"Extracted from local Lean definition `{report['existingLeanInputs']['modelDerivCoeffSource']}`.",
        "",
        "| i | coeff | source line |",
        "| --- | --- | --- |",
    ]
    for item in report["generatorFields"]["modelDerivCoeff"]:
        lines.append(
            f"| {item['index']} | `{item['value']}` | {item['sourceLine']} |"
        )

    lines.extend(
        [
            "",
            "## Required Component Fields",
            "",
            "- `omegaCoeff[0..15]`",
            "- `omegaDerivCoeff[0..15]`",
            "- `shapeCoeff[0..15]`",
            "- `shapeDerivCoeff[0..15]`",
            "- `omegaRemainderAbs`",
            "- `omegaDerivRemainderAbs`",
            "- `shapeRemainderAbs`",
            "- `shapeDerivRemainderAbs`",
            "- `assembledRawDerivCoeff[0..45]`",
            "- `residualTaylorCoeff[0..45]`",
            "- `residualTaylorRemainderAbs`",
            "- `residualPolynomialLower` / `residualPolynomialUpper`",
            "- `finalResidualLower` / `finalResidualUpper`",
            "",
            "## Component Closure Ledger",
            "",
        ]
    )
    for key, value in report["componentClosureLedger"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## OmegaDeriv Taylor Source",
            "",
            f"- proof-grade: `{report['omegaPrimeTaylorSource']['proofGrade']}`",
            f"- valid theorem: `{report['omegaPrimeTaylorSource']['validTheorem']}`",
            f"- theorem found: `{report['omegaPrimeTaylorSource']['validTheoremFound']}`",
            f"- payload generated valid cert proved: `{report['omegaPrimeTaylorSource']['payloadGeneratedValidCertProved']}`",
            f"- coeff source: `{report['omegaPrimeTaylorSource']['coeffSource']}`",
            f"- remainder source: `{report['omegaPrimeTaylorSource']['remainderSource']}`",
            "",
            "## OmegaTaylor Crosswalk Source",
            "",
            f"- proof-grade: `{report['omegaTaylorCrosswalkSource']['proofGrade']}`",
            f"- theorem: `{report['omegaTaylorCrosswalkSource']['leanTheorem']}`",
            f"- theorem found: `{report['omegaTaylorCrosswalkSource']['leanTheoremFound']}`",
            f"- first missing: `{report['componentTaylorStatus']['omegaTaylor']['firstMissing']}`",
            "",
            "## OmegaTaylor Center Anchor Source",
            "",
            f"- proof-grade: `{report['omegaTaylorCenterAnchorSource']['proofGrade']}`",
            f"- theorem: `{report['omegaTaylorCenterAnchorSource']['leanTheorem']}`",
            f"- theorem found: `{report['omegaTaylorCenterAnchorSource']['leanTheoremFound']}`",
            f"- anchor coeff: `{report['omegaTaylorCenterAnchorSource']['anchorCoeff']}`",
            f"- anchor error abs: `{report['omegaTaylorCenterAnchorSource']['anchorErrorAbs']}`",
            "",
            "## Component Taylor Status",
            "",
            f"- omegaDerivTaylor: `{report['componentTaylorStatus']['omegaDerivTaylor']['status']}`",
            f"- omegaDerivTaylor Lean theorem: `{report['componentTaylorStatus']['omegaDerivTaylor']['leanTheorem']}`",
            f"- omegaTaylor: `{report['componentTaylorStatus']['omegaTaylor']['status']}`",
            f"- shapeTaylor: `{report['componentTaylorStatus']['shapeTaylor']['status']}`",
            f"- shapeDerivTaylor: `{report['componentTaylorStatus']['shapeDerivTaylor']['status']}`",
            f"- shape endpoint bounds available: `{report['shapeEndpointSource']['proofGradeEndpointBounds']}`",
            f"- shapeSq integrated receiver available: `{report['shapeIntegratedReceiverSource']['proofGrade']}`",
            f"- shapeSq deriv Taylor source available: `{report['shapeSqDerivTaylorSource']['proofGrade']}`",
            f"- shapeSq deriv interval cert receiver available: `{report['shapeSqDerivIntervalCertReceiverSource']['proofGradeReceiver']}`",
            f"- shapeSq deriv center-coeff bridge available: `{report['shapeSqDerivCenterCoeffBridgeSource']['proofGradeBridge']}`",
            f"- shapeSq deriv center-coeff interval receiver available: `{report['shapeSqDerivCenterCoeffBridgeSource']['proofGradeIntervalReceiver']}`",
            f"- shapeSq deriv coeff0 row available: `{report['shapeSqDerivCenterCoeffRowsSource']['proofGradeRow0']}`",
            f"- shapeSq deriv coeff1 row available: `{report['shapeSqDerivCenterCoeffRowsSource']['proofGradeRow1']}`",
            f"- shapeSq deriv order-shift receiver available: `{report['shapeSqDerivOrderShiftReceiverSource']['proofGradeReceiver']}`",
            f"- shapeSq deriv shape-square derivative receiver available: `{report['shapeSqDerivShapeSqDerivativeReceiverSource']['proofGradeReceiver']}`",
            f"- shapeSq deriv coeff rows closed: `{report['shapeSqDerivCenterCoeffRowsSource']['rowsClosedCount']} / {report['shapeSqDerivCenterCoeffRowsSource']['rowsRequiredCount']}`",
            f"- shapeSq deriv order16 uniform bound available: `{report['shapeSqDerivCenterCoeffRowsSource']['order16UniformBoundPresent']}`",
            f"- shapeSq value Taylor source available: `{report['shapeSqTaylorSource']['proofGrade']}`",
            f"- shape Taylor receiver gap: `{report['componentTaylorStatus']['shapeTaylor']['firstReceiverGap']}`",
            f"- shapeDeriv Taylor receiver gap: `{report['shapeEndpointSource']['firstShapeDerivReceiverGap']}`",
            f"- assembly Lean written: `{report['componentTaylorStatus']['assemblyLeanWritten']}`",
            f"- overall proof safe: `{report['componentTaylorStatus']['overallProofSafe']}`",
            "",
            "## Shape Endpoint Source",
            "",
            f"- endpoint proof-grade: `{report['shapeEndpointSource']['proofGradeEndpointBounds']}`",
            f"- Taylor payload proof-grade: `{report['shapeEndpointSource']['proofGradeTaylorPayload']}`",
            f"- shapeSq endpoint theorem: `{report['shapeEndpointSource']['shapeSqEndpointBoundsTheorem']}`",
            f"- shapeSq endpoint theorem found: `{report['shapeEndpointSource']['shapeSqEndpointBoundsTheoremFound']}`",
            f"- shape value bounds theorem: `{report['shapeEndpointSource']['shapeValueBoundsTheorem']}`",
            f"- shape value bounds theorem found: `{report['shapeEndpointSource']['shapeValueBoundsTheoremFound']}`",
            f"- shape deriv anchor bounds theorem: `{report['shapeEndpointSource']['shapeDerivAnchorBoundsTheorem']}`",
            f"- shape deriv anchor bounds theorem found: `{report['shapeEndpointSource']['shapeDerivAnchorBoundsTheoremFound']}`",
            f"- shape deriv interval theorem: `{report['shapeEndpointSource']['shapeDerivIntervalBoundsTheorem']}`",
            f"- shape deriv interval theorem found: `{report['shapeEndpointSource']['shapeDerivIntervalBoundsTheoremFound']}`",
            f"- receiver needed: {report['shapeEndpointSource']['nextReceiverNeeded']}",
            f"- why not Taylor payload: {report['shapeEndpointSource']['whyNotTaylorPayload']}",
            "",
            "## ShapeSq Integrated Taylor Receiver",
            "",
            f"- proof-grade: `{report['shapeIntegratedReceiverSource']['proofGrade']}`",
            f"- receiver theorem: `{report['shapeIntegratedReceiverSource']['receiverTheorem']}`",
            f"- receiver theorem found: `{report['shapeIntegratedReceiverSource']['receiverTheoremFound']}`",
            f"- integrated crosswalk theorem: `{report['shapeIntegratedReceiverSource']['integratedCrosswalkTheorem']}`",
            f"- integrated crosswalk theorem found: `{report['shapeIntegratedReceiverSource']['integratedCrosswalkTheoremFound']}`",
            f"- failure closed: `{report['shapeIntegratedReceiverSource']['failureClosed']}`",
            f"- next missing: `{report['shapeIntegratedReceiverSource']['nextMissing']}`",
            f"- boundary: {report['shapeIntegratedReceiverSource']['boundary']}",
            "",
            "## ShapeSq Deriv Taylor Source",
            "",
            f"- proof-grade: `{report['shapeSqDerivTaylorSource']['proofGrade']}`",
            f"- bridge theorem: `{report['shapeSqDerivTaylorSource']['bridgeTheorem']}`",
            f"- bridge theorem found: `{report['shapeSqDerivTaylorSource']['bridgeTheoremFound']}`",
            f"- source theorem: `{report['shapeSqDerivTaylorSource']['sourceTheorem']}`",
            f"- source theorem found: `{report['shapeSqDerivTaylorSource']['sourceTheoremFound']}`",
            f"- coeff def: `{report['shapeSqDerivTaylorSource']['coeffDef']}`",
            f"- remainder def: `{report['shapeSqDerivTaylorSource']['remainderDef']}`",
            f"- constant center: `{report['shapeSqDerivTaylorSource']['constantTaylorCenter']}`",
            f"- constant remainder abs: `{report['shapeSqDerivTaylorSource']['constantTaylorRemainderAbs']}`",
            f"- failure closed: `{report['shapeSqDerivTaylorSource']['failureClosed']}`",
            f"- next missing: `{report['shapeSqDerivTaylorSource']['nextMissing']}`",
            f"- boundary: {report['shapeSqDerivTaylorSource']['boundary']}",
            "",
            "## ShapeSq Deriv Interval Cert Receiver",
            "",
            f"- proof-grade receiver: `{report['shapeSqDerivIntervalCertReceiverSource']['proofGradeReceiver']}`",
            f"- source def: `{report['shapeSqDerivIntervalCertReceiverSource']['sourceDef']}`",
            f"- source def found: `{report['shapeSqDerivIntervalCertReceiverSource']['sourceDefFound']}`",
            f"- cert structure: `{report['shapeSqDerivIntervalCertReceiverSource']['certStructure']}`",
            f"- cert structure found: `{report['shapeSqDerivIntervalCertReceiverSource']['certStructureFound']}`",
            f"- valid predicate: `{report['shapeSqDerivIntervalCertReceiverSource']['validPredicate']}`",
            f"- valid predicate found: `{report['shapeSqDerivIntervalCertReceiverSource']['validPredicateFound']}`",
            f"- Taylor input theorem: `{report['shapeSqDerivIntervalCertReceiverSource']['toTaylorInputs']}`",
            f"- Taylor input theorem found: `{report['shapeSqDerivIntervalCertReceiverSource']['toTaylorInputsFound']}`",
            f"- source theorem: `{report['shapeSqDerivIntervalCertReceiverSource']['toShapeSqDerivTaylorSource']}`",
            f"- source theorem found: `{report['shapeSqDerivIntervalCertReceiverSource']['toShapeSqDerivTaylorSourceFound']}`",
            f"- one-segment constructor: `{report['shapeSqDerivIntervalCertReceiverSource']['singleConstructor']}`",
            f"- one-segment constructor found: `{report['shapeSqDerivIntervalCertReceiverSource']['singleConstructorFound']}`",
            f"- one-segment validity constructor: `{report['shapeSqDerivIntervalCertReceiverSource']['singleValidityConstructor']}`",
            f"- one-segment validity constructor found: `{report['shapeSqDerivIntervalCertReceiverSource']['singleValidityConstructorFound']}`",
            f"- one-segment bookkeeping closed: `{report['shapeSqDerivIntervalCertReceiverSource']['oneSegmentBookkeepingClosed']}`",
            f"- compact abs constructor: `{report['shapeSqDerivIntervalCertReceiverSource']['singleAbsConstructor']}`",
            f"- compact abs constructor found: `{report['shapeSqDerivIntervalCertReceiverSource']['singleAbsConstructorFound']}`",
            f"- compact abs validity constructor: `{report['shapeSqDerivIntervalCertReceiverSource']['singleAbsValidityConstructor']}`",
            f"- compact abs validity constructor found: `{report['shapeSqDerivIntervalCertReceiverSource']['singleAbsValidityConstructorFound']}`",
            f"- compact abs bookkeeping closed: `{report['shapeSqDerivIntervalCertReceiverSource']['compactAbsBookkeepingClosed']}`",
            f"- failure closed: `{report['shapeSqDerivIntervalCertReceiverSource']['failureClosed']}`",
            f"- next missing: `{report['shapeSqDerivIntervalCertReceiverSource']['nextMissing']}`",
            f"- boundary: {report['shapeSqDerivIntervalCertReceiverSource']['boundary']}",
            "",
            "## ShapeSq Deriv Center-Coeff Bridge",
            "",
            f"- proof-grade bridge: `{report['shapeSqDerivCenterCoeffBridgeSource']['proofGradeBridge']}`",
            f"- power series def: `{report['shapeSqDerivCenterCoeffBridgeSource']['powerSeriesDef']}`",
            f"- power series def found: `{report['shapeSqDerivCenterCoeffBridgeSource']['powerSeriesDefFound']}`",
            f"- HasFPowerSeries theorem: `{report['shapeSqDerivCenterCoeffBridgeSource']['hasFPowerSeriesTheorem']}`",
            f"- HasFPowerSeries theorem found: `{report['shapeSqDerivCenterCoeffBridgeSource']['hasFPowerSeriesTheoremFound']}`",
            f"- center jet theorem: `{report['shapeSqDerivCenterCoeffBridgeSource']['centerJetCoeffTheorem']}`",
            f"- center jet theorem found: `{report['shapeSqDerivCenterCoeffBridgeSource']['centerJetCoeffTheoremFound']}`",
            f"- valid wrapper theorem: `{report['shapeSqDerivCenterCoeffBridgeSource']['validWrapperTheorem']}`",
            f"- valid wrapper theorem found: `{report['shapeSqDerivCenterCoeffBridgeSource']['validWrapperTheoremFound']}`",
            f"- interval wrapper theorem: `{report['shapeSqDerivCenterCoeffBridgeSource']['intervalWrapperTheorem']}`",
            f"- interval wrapper theorem found: `{report['shapeSqDerivCenterCoeffBridgeSource']['intervalWrapperTheoremFound']}`",
            f"- proof-grade interval receiver: `{report['shapeSqDerivCenterCoeffBridgeSource']['proofGradeIntervalReceiver']}`",
            f"- failure closed: `{report['shapeSqDerivCenterCoeffBridgeSource']['failureClosed']}`",
            f"- interval receiver failure closed: `{report['shapeSqDerivCenterCoeffBridgeSource']['intervalReceiverFailureClosed']}`",
            f"- next missing: `{report['shapeSqDerivCenterCoeffBridgeSource']['nextMissing']}`",
            f"- boundary: {report['shapeSqDerivCenterCoeffBridgeSource']['boundary']}",
            "",
            "## ShapeSq Deriv Order-Shift Receiver",
            "",
            f"- proof-grade receiver: `{report['shapeSqDerivOrderShiftReceiverSource']['proofGradeReceiver']}`",
            f"- order-shift theorem: `{report['shapeSqDerivOrderShiftReceiverSource']['orderShiftTheorem']}`",
            f"- order-shift theorem found: `{report['shapeSqDerivOrderShiftReceiverSource']['orderShiftTheoremFound']}`",
            f"- coefficient receiver theorem: `{report['shapeSqDerivOrderShiftReceiverSource']['coefficientReceiverTheorem']}`",
            f"- coefficient receiver theorem found: `{report['shapeSqDerivOrderShiftReceiverSource']['coefficientReceiverTheoremFound']}`",
            f"- order16 receiver theorem: `{report['shapeSqDerivOrderShiftReceiverSource']['order16ReceiverTheorem']}`",
            f"- order16 receiver theorem found: `{report['shapeSqDerivOrderShiftReceiverSource']['order16ReceiverTheoremFound']}`",
            f"- failure closed: `{report['shapeSqDerivOrderShiftReceiverSource']['failureClosed']}`",
            f"- next missing: `{report['shapeSqDerivOrderShiftReceiverSource']['nextMissing']}`",
            f"- boundary: {report['shapeSqDerivOrderShiftReceiverSource']['boundary']}",
            "",
            "## ShapeSq Deriv Shape-Square Derivative Receiver",
            "",
            f"- proof-grade receiver: `{report['shapeSqDerivShapeSqDerivativeReceiverSource']['proofGradeReceiver']}`",
            f"- theorem: `{report['shapeSqDerivShapeSqDerivativeReceiverSource']['validFromShapeSqDerivativeAbsTheorem']}`",
            f"- theorem found: `{report['shapeSqDerivShapeSqDerivativeReceiverSource']['validFromShapeSqDerivativeAbsTheoremFound']}`",
            f"- failure closed: `{report['shapeSqDerivShapeSqDerivativeReceiverSource']['failureClosed']}`",
            f"- next missing: `{report['shapeSqDerivShapeSqDerivativeReceiverSource']['nextMissing']}`",
            f"- boundary: {report['shapeSqDerivShapeSqDerivativeReceiverSource']['boundary']}",
            "",
            "## ShapeSq Deriv Product-Bounds Receiver",
            "",
            f"- proof-grade receiver: `{report['shapeSqDerivProductBoundsReceiverSource']['proofGradeReceiver']}`",
            f"- Lean file: `{report['shapeSqDerivProductBoundsReceiverSource']['leanFile']}`",
            f"- theorem: `{report['shapeSqDerivProductBoundsReceiverSource']['productBoundsTheorem']}`",
            f"- theorem found: `{report['shapeSqDerivProductBoundsReceiverSource']['productBoundsTheoremFound']}`",
            f"- failure closed: `{report['shapeSqDerivProductBoundsReceiverSource']['failureClosed']}`",
            f"- next missing: `{report['shapeSqDerivProductBoundsReceiverSource']['nextMissing']}`",
            f"- boundary: {report['shapeSqDerivProductBoundsReceiverSource']['boundary']}",
            "",
            "## ShapeSq Deriv Center-Coeff Rows",
            "",
            f"- proof-grade row0: `{report['shapeSqDerivCenterCoeffRowsSource']['proofGradeRow0']}`",
            f"- proof-grade row1: `{report['shapeSqDerivCenterCoeffRowsSource']['proofGradeRow1']}`",
            f"- Lean file: `{report['shapeSqDerivCenterCoeffRowsSource']['leanFile']}`",
            f"- row0 lower def: `{report['shapeSqDerivCenterCoeffRowsSource']['row0LowerDef']}`",
            f"- row0 lower def found: `{report['shapeSqDerivCenterCoeffRowsSource']['row0LowerDefFound']}`",
            f"- row0 upper def: `{report['shapeSqDerivCenterCoeffRowsSource']['row0UpperDef']}`",
            f"- row0 upper def found: `{report['shapeSqDerivCenterCoeffRowsSource']['row0UpperDefFound']}`",
            f"- row0 interval theorem: `{report['shapeSqDerivCenterCoeffRowsSource']['row0IntervalTheorem']}`",
            f"- row0 interval theorem found: `{report['shapeSqDerivCenterCoeffRowsSource']['row0IntervalTheoremFound']}`",
            f"- row1 lower def: `{report['shapeSqDerivCenterCoeffRowsSource']['row1LowerDef']}`",
            f"- row1 lower def found: `{report['shapeSqDerivCenterCoeffRowsSource']['row1LowerDefFound']}`",
            f"- row1 upper def: `{report['shapeSqDerivCenterCoeffRowsSource']['row1UpperDef']}`",
            f"- row1 upper def found: `{report['shapeSqDerivCenterCoeffRowsSource']['row1UpperDefFound']}`",
            f"- row1 interval theorem: `{report['shapeSqDerivCenterCoeffRowsSource']['row1IntervalTheorem']}`",
            f"- row1 interval theorem found: `{report['shapeSqDerivCenterCoeffRowsSource']['row1IntervalTheoremFound']}`",
            f"- rows closed: `{report['shapeSqDerivCenterCoeffRowsSource']['rowsClosedCount']} / {report['shapeSqDerivCenterCoeffRowsSource']['rowsRequiredCount']}`",
            f"- missing rows: `{report['shapeSqDerivCenterCoeffRowsSource']['missingRows']}`",
            f"- order16 uniform bound present: `{report['shapeSqDerivCenterCoeffRowsSource']['order16UniformBoundPresent']}`",
            f"- failure closed: `{report['shapeSqDerivCenterCoeffRowsSource']['failureClosed']}`",
            f"- next missing: `{report['shapeSqDerivCenterCoeffRowsSource']['nextMissing']}`",
            f"- boundary: {report['shapeSqDerivCenterCoeffRowsSource']['boundary']}",
            "",
            "## ShapeSq Value Taylor Source",
            "",
            f"- proof-grade: `{report['shapeSqTaylorSource']['proofGrade']}`",
            f"- receiver theorem: `{report['shapeSqTaylorSource']['receiverTheorem']}`",
            f"- receiver theorem found: `{report['shapeSqTaylorSource']['receiverTheoremFound']}`",
            f"- source theorem: `{report['shapeSqTaylorSource']['sourceTheorem']}`",
            f"- source theorem found: `{report['shapeSqTaylorSource']['sourceTheoremFound']}`",
            f"- coeff def: `{report['shapeSqTaylorSource']['coeffDef']}`",
            f"- anchor coeff def: `{report['shapeSqTaylorSource']['anchorCoeffDef']}`",
            f"- anchor error def: `{report['shapeSqTaylorSource']['anchorErrorDef']}`",
            f"- remainder def: `{report['shapeSqTaylorSource']['remainderDef']}`",
            f"- constant remainder abs: `{report['shapeSqTaylorSource']['constantTaylorRemainderAbs']}`",
            f"- failure closed: `{report['shapeSqTaylorSource']['failureClosed']}`",
            f"- next missing: `{report['shapeSqTaylorSource']['nextMissing']}`",
            f"- boundary: {report['shapeSqTaylorSource']['boundary']}",
            "",
            "## Proof Status",
            "",
        ]
    )
    for key, value in report["proofStatus"].items():
        lines.append(f"- {key}: `{value}`")

    lines.extend(
        [
            "",
            "## Existing Lean Inputs",
            "",
        ]
    )
    for key, value in report["existingLeanInputs"].items():
        lines.append(f"- {key}: `{value}`")

    lines.extend(
        [
            "",
            "## Proshka Decision",
            "",
            f"- chosen: `{report['proshkaDecision']['chosen']}`",
            f"- follow-up chosen: `{report['proshkaDecision']['followupChosen']}`",
            f"- follow-up failure closed: `{report['proshkaDecision']['followupFailureClosed']}`",
            f"- follow-up first missing: `{report['proshkaDecision']['followupFirstMissing']}`",
            f"- why not A: {report['proshkaDecision']['whyNotA']}",
            f"- why not C: {report['proshkaDecision']['whyNotC']}",
            f"- follow-up why A: {report['proshkaDecision']['followupWhyA']}",
            "",
            "## Failure Codes",
            "",
        ]
    )
    for code in report["failureCodes"]:
        lines.append(f"- `{code}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            *decision_text,
            "",
        ]
    )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--landing", type=Path, default=LANDING_FILE)
    parser.add_argument(
        "--component-ledger", type=Path, default=DEFAULT_COMPONENT_LEDGER
    )
    parser.add_argument(
        "--omega-prime-payload", type=Path, default=DEFAULT_OMEGA_PRIME_PAYLOAD
    )
    parser.add_argument("--endpoint-support", type=Path, default=DEFAULT_ENDPOINT_SUPPORT)
    parser.add_argument("--endpoint-landing", type=Path, default=DEFAULT_ENDPOINT_LANDING)
    parser.add_argument(
        "--endpoint-rational-import",
        type=Path,
        default=DEFAULT_ENDPOINT_RATIONAL_IMPORT,
    )
    parser.add_argument(
        "--shape-sq-deriv-center-coeff-rows",
        type=Path,
        default=DEFAULT_SHAPESQ_DERIV_CENTER_COEFF_ROWS,
    )
    parser.add_argument(
        "--shape-sq-deriv-product-bounds",
        type=Path,
        default=DEFAULT_SHAPESQ_DERIV_PRODUCT_BOUNDS,
    )
    parser.add_argument(
        "--chunk-taylor-checker",
        type=Path,
        default=DEFAULT_CHUNK_TAYLOR_CHECKER,
    )
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(
        landing_path=args.landing,
        component_ledger_path=args.component_ledger,
        omega_prime_payload_path=args.omega_prime_payload,
        endpoint_support_path=args.endpoint_support,
        endpoint_landing_path=args.endpoint_landing,
        endpoint_rational_import_path=args.endpoint_rational_import,
        shape_sq_deriv_center_coeff_rows_path=(
            args.shape_sq_deriv_center_coeff_rows
        ),
        shape_sq_deriv_product_bounds_path=args.shape_sq_deriv_product_bounds,
        chunk_taylor_checker_path=args.chunk_taylor_checker,
    )
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} first_failure={failure} model_coeffs={coeffs} out_json={out_json}".format(
            status=report["status"],
            failure=report["firstFailure"],
            coeffs=len(report["generatorFields"]["modelDerivCoeff"]),
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
