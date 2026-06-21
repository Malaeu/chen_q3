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

SCHEMA = "q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v6"
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


def component_taylor_status(
    omega_prime_closed: bool,
    omega_crosswalk_closed: bool,
    omega_anchor_closed: bool,
    shape_endpoint_available: bool,
    shape_integrated_receiver_closed: bool,
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
                "INTEGRATED_RECEIVER_FORMAL_MISSING_SHAPESQ_DERIV_TAYLOR_SOURCE"
                if shape_integrated_receiver_closed
                else "ENDPOINT_BOUNDS_FORMAL_MISSING_TAYLOR_COEFF_REMAINDER_RECEIVER"
                if shape_endpoint_available
                else "MISSING_PROOF_GRADE_REMAINDER"
            ),
            "missing": True,
            "endpointBoundsAvailable": shape_endpoint_available,
            "integratedReceiverAvailable": shape_integrated_receiver_closed,
            "firstReceiverGap": (
                FIRST_FAILURE_AFTER_SHAPESQ_RECEIVER
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
    if omega_anchor_closed and shape_integrated_receiver_closed:
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
                "shapeTaylorReceiverPresent": False,
                "shapeDerivTaylorReceiverPresent": False,
                "omegaDerivTaylorProofAssembledIntoRawDerivative": False,
                "residualPolynomialRangePassed": False,
                "finalBudgetPassed": False,
                "proofSafeClosedFields": (
                    (1 if omega_prime_closed else 0)
                    + (1 if omega_crosswalk_closed else 0)
                    + (1 if omega_anchor_closed else 0)
                    + (1 if shape_integrated_receiver_closed else 0)
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
                "integrated_receiver_formal_missing_shapesq_deriv_taylor_source"
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
            ),
            "omegaPrimeTaylorSource": omega_prime,
            "omegaTaylorCrosswalkSource": omega_crosswalk,
            "omegaTaylorCenterAnchorSource": omega_anchor,
            "shapeEndpointSource": shape_endpoint,
            "shapeIntegratedReceiverSource": shape_integrated_receiver,
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
                "shapeValueBounds": SHAPE_VALUE_BOUNDS_THEOREM,
                "shapeDerivAnchorBounds": SHAPE_DERIV_ANCHOR_BOUNDS_THEOREM,
                "shapeDerivIntervalBounds": SHAPE_DERIV_INTERVAL_BOUNDS_THEOREM,
        },
        "proshkaDecision": {
            "chosen": "B_component_taylor_route",
            "followupChosen": "A_omega_prime_to_omega_integrated_lift",
            "followupFailureClosed": (
                FIRST_FAILURE_AFTER_OMEGA_CROSSWALK
                if omega_anchor_closed
                else OMEGA_TAYLOR_CROSSWALK_FAILURE
                if omega_crosswalk_closed
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
                "After OmegaPrime became proof-grade, the smallest proof-producing "
                "patch was the integrated-polynomial derivative crosswalk plus "
                "the center-anchor payload for Omega."
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
            CHUNK_TAYLOR_CHECKER_FILE: file_hash(chunk_taylor_checker_path),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    if report["proofStatus"]["shapeSqIntegratedTaylorReceiverPresent"]:
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
            f"- shape Taylor receiver gap: `{report['shapeEndpointSource']['firstShapeReceiverGap']}`",
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
