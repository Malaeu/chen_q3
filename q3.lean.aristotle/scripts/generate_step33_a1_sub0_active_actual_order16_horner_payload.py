#!/usr/bin/env python3
"""Fail-closed activeActual order-16 Horner payload entrypoint.

This is the first generator-facing surface for the payload requested by the
activeActual Horner family bridge.  It deliberately refuses to emit Lean until a
proof-grade rational/interval source supplies an activeActual low-degree
coefficient row, a uniform segment remainder bound for
`activeScale * D^16(ComponentProductActual)`, and then zero-extends that row
into the checked degree-29/Fin30 container.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_active_actual_order16_horner_payload.v8"
DEGREE0_SCHEMA = "q3_psdpd_step33_a1_sub0_active_actual_order16_degree0_payload.v3"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

ROW_SOURCE_JSON = REQUEST_DIR / "step33_a1_sub0_active_actual_horner_row_source.json"
JSON_OUT = REQUEST_DIR / "step33_a1_sub0_active_actual_order16_horner_payload.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_active_actual_order16_horner_payload.md"
DEGREE0_JSON_OUT = (
    REQUEST_DIR / "step33_a1_sub0_active_actual_order16_degree0_payload.json"
)
DEGREE0_MD_OUT = (
    REQUEST_DIR / "step33_a1_sub0_active_actual_order16_degree0_payload.md"
)

SEGMENT_RECEIVER_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean"
)
FAMILY_BRIDGE_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerFamilyBridge.lean"
)
ACTIVE_CENTER_ROWS_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean"
)
LOW_DEGREE_BRIDGE_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualLowDegreeBridge.lean"
)
DEGREE0_SOURCE_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0Source.lean"
)
RAW_PRODUCT18_BRIDGE_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Payload.lean"
)
RAW_PRODUCT18_MAJORANT_RECEIVER_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18MajorantReceiver.lean"
)
ACTIVE_SCALE_BOUND_INPUTS_LEAN = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean"
)
ACTIVE_SCALE_BOUND_ASSEMBLY_LEAN = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean"
)
FUTURE_PAYLOAD_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerPayload.lean"
)

ROW_SOURCE_GAP = "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP"
D46_SOURCE_GAP = "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D46_UNIFORM_REMAINDER_SOURCE_GAP"
LOW_DEGREE_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_LOW_DEGREE_SEGMENT_REMAINDER_SOURCE_GAP"
)
LOW_DEGREE_ALIGNMENT_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_LOW_DEGREE_TO_FIN30_ALIGNMENT_GAP"
)
D16_CENTER_D17_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP"
)
D17_UNIFORM_SOURCE_GAP = "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D17_UNIFORM_SOURCE_GAP"
RAW_PRODUCT18_UNIFORM_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_RAW_PRODUCT18_UNIFORM_SOURCE_GAP"
)
RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP = (
    "STEP33_A1_SUB0_RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP"
)
OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP = (
    "STEP33_A1_SUB0_OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP"
)
SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP = (
    "STEP33_A1_SUB0_SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP"
)
DEGREE0_BUDGET_CONSTANT_FAIL = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_REMAINDER_BUDGET_CONSTANT_FAIL"
)
PAYLOAD_VALIDATION_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_LEAN_PAYLOAD_VALIDATION_GAP"
)

REQUIRED_SEGMENT_SYMBOLS = [
    "Step33Sub0ActiveActualOrder16HornerSegmentCert",
    "structure Valid",
    "remainderBound",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert",
]

REQUIRED_FAMILY_SYMBOLS = [
    "Step33Sub0ActiveActualOrder16HornerFamilyCert",
    "structure Valid",
    "primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily",
]

REQUIRED_LOW_DEGREE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29",
    "primaryFiniteRow0Parent0Split100Sub0_activeActualPoly_zeroExtend29_eq",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree",
]

REQUIRED_DEGREE0_SOURCE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff",
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff17",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_contDiff17",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_checked_contDiff17",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
]

REQUIRED_RAW_PRODUCT18_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18",
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_abs",
]

REQUIRED_RAW_PRODUCT18_MAJORANT_RECEIVER_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant",
    "primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs",
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_factor_derivative_abs",
]

ACTIVE_SCALE_ABS_BOUND_RAT = (
    "95492965855137201461330258024/"
    "1000000000000000000000000000000"
)


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def active_scale_source() -> dict[str, Any]:
    return {
        "status": "checked",
        "kind": "Lean",
        "path": rel(ACTIVE_SCALE_BOUND_INPUTS_LEAN),
        "theorem": "primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound",
        "line": 111,
        "statement": (
            "|primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <= "
            "(primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real)"
        ),
        "exactBoundPath": rel(ACTIVE_SCALE_BOUND_ASSEMBLY_LEAN),
        "exactBoundDef": "primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound",
        "exactBoundLine": 490,
        "exactRat": ACTIVE_SCALE_ABS_BOUND_RAT,
    }


def raw_product18_bridge_source(raw_product18_ready: bool) -> dict[str, Any]:
    return {
        "status": "checked" if raw_product18_ready else "missing",
        "kind": "Lean",
        "path": rel(RAW_PRODUCT18_BRIDGE_LEAN),
        "equalityTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18"
        ),
        "absTransferTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_abs"
        ),
        "meaning": (
            "D^17(ComponentProductActual) is reduced to D^18(RawProductActual)"
        ),
        "stillMissing": (
            "proof-grade uniform source for D^18(RawProductActual) on Set.Icc 0 (1/10)"
        ),
        "failureIfMissing": RAW_PRODUCT18_UNIFORM_SOURCE_GAP,
    }


def raw_product18_majorant_receiver_source(receiver_ready: bool) -> dict[str, Any]:
    return {
        "status": "checked" if receiver_ready else "missing",
        "kind": "Lean",
        "path": rel(RAW_PRODUCT18_MAJORANT_RECEIVER_LEAN),
        "majorantDef": "primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant",
        "rawProductTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs"
        ),
        "componentTransferTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_factor_derivative_abs"
        ),
        "meaning": (
            "conditional Leibniz receiver from Omega/ShapeSq derivative bounds 0..18 "
            "to the D18(RawProductActual) majorant"
        ),
        "stillMissing": [
            OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP,
            SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP,
        ],
        "failureIfMissing": RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP,
    }


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def symbol_audit(path: Path, symbols: list[str]) -> dict[str, dict[str, Any]]:
    text = read_text(path)
    lines = text.splitlines()
    out: dict[str, dict[str, Any]] = {}
    for symbol in symbols:
        line_no = next(
            (index for index, line in enumerate(lines, start=1) if symbol in line),
            None,
        )
        out[symbol] = {"present": line_no is not None, "line": line_no}
    return out


def all_present(items: dict[str, dict[str, Any]]) -> bool:
    return all(bool(item["present"]) for item in items.values())


def rat_or_none(value: str | None) -> Fraction | None:
    if value is None:
        return None
    return Fraction(value)


def rat_str(value: Fraction | None) -> str | None:
    if value is None:
        return None
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def exact_degree0_budget(
    *,
    coeff_error_abs: str | None,
    active_scale_abs: str | None,
    order17_abs: str | None,
    poly_error_abs: str | None,
) -> dict[str, Any]:
    coeff_error_abs_rat = rat_or_none(coeff_error_abs)
    active_scale_abs_rat = rat_or_none(active_scale_abs)
    order17_abs_rat = rat_or_none(order17_abs)
    poly_error_abs_rat = rat_or_none(poly_error_abs)
    missing = [
        name
        for name, value in [
            ("coeffErrorAbs", coeff_error_abs_rat),
            ("activeScaleAbs", active_scale_abs_rat),
            ("order17Abs", order17_abs_rat),
            ("polyErrorAbs", poly_error_abs_rat),
        ]
        if value is None
    ]
    if missing:
        return {
            "available": False,
            "missing": missing,
            "lhs": None,
            "rhs": poly_error_abs,
            "passed": None,
            "failureIfFalse": DEGREE0_BUDGET_CONSTANT_FAIL,
        }
    lhs = coeff_error_abs_rat + active_scale_abs_rat * order17_abs_rat / 20
    return {
        "available": True,
        "missing": [],
        "lhs": rat_str(lhs),
        "rhs": poly_error_abs,
        "passed": lhs <= poly_error_abs_rat,
        "failureIfFalse": DEGREE0_BUDGET_CONSTANT_FAIL,
    }


def center_row_status() -> dict[str, Any]:
    text = read_text(ACTIVE_CENTER_ROWS_LEAN)
    return {
        "path": rel(ACTIVE_CENTER_ROWS_LEAN),
        "exists": ACTIVE_CENTER_ROWS_LEAN.exists(),
        "hasFin16Rows": "Fin 16" in text,
        "hasActiveActualCenterRowInterval": (
            "primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows"
            in text
        ),
        "proofGradeForCenterJetsOnly": (
            "primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows"
            in text
        ),
        "availableOrders": "0..15",
        "neededForFullDegree29Only": {
            "coefficientOrders": "16..45",
            "remainderOrder": 46,
            "firstSubgapIfFullDegree29IsUsed": D46_SOURCE_GAP,
        },
        "usableAsLowDegreeCoefficientSeedOnly": True,
        "usableForSmokeSegmentRemainder": False,
    }


def build_degree0_preflight(
    degree0_ready: bool,
    raw_product18_bridge_ready: bool,
    raw_product18_majorant_receiver_ready: bool,
) -> dict[str, Any]:
    fields: dict[str, str | None] = {
        "d16CenterLower": None,
        "d16CenterUpper": None,
        "coeff0": None,
        "coeffErrorAbs": None,
        "order17Abs": None,
        "activeScaleAbs": ACTIVE_SCALE_ABS_BOUND_RAT,
        "polyErrorAbs": None,
    }
    budget = exact_degree0_budget(
        coeff_error_abs=fields["coeffErrorAbs"],
        active_scale_abs=fields["activeScaleAbs"],
        order17_abs=fields["order17Abs"],
        poly_error_abs=fields["polyErrorAbs"],
    )
    d16_proof_grade = False
    d17_proof_grade = False
    active_scale_proof_grade = True
    first_failure = D16_CENTER_D17_SOURCE_GAP
    if budget["available"] and not budget["passed"]:
        first_failure = DEGREE0_BUDGET_CONSTANT_FAIL
    elif budget["available"] and not d17_proof_grade:
        first_failure = D17_UNIFORM_SOURCE_GAP

    return {
        "schema": DEGREE0_SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "active_actual_order16_degree0_preflight",
        "proofStatus": "blocked_missing_d16_center_d17_uniform_source",
        "proofGrade": False,
        "receiverReady": degree0_ready,
        "outLeanWritten": False,
        "target": "ActiveScaleCoeff * D^16(ComponentProductActual)",
        "cell": "Set.Icc 0 (1/10)",
        "center": "1/20",
        "degree": 0,
        "receiverTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
        "outputObject": rel(DEGREE0_JSON_OUT),
        "firstFileToEdit": rel(Path(__file__).resolve()),
        "fields": fields,
        "activeScaleSource": active_scale_source(),
        "order17UniformRoute": {
            "selectedRoute": "B_rawProduct18",
            "selectedBy": "Browser/Computer Use Proshka review",
            "bridge": raw_product18_bridge_source(raw_product18_bridge_ready),
            "majorantReceiver": raw_product18_majorant_receiver_source(
                raw_product18_majorant_receiver_ready
            ),
            "requiredUniformSource": (
                "forall eta in Set.Icc 0 (1/10), "
                "|D^18(RawProductActual)(eta)| <= order17Abs"
            ),
            "remainingFactorSources": [
                OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP,
                SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP,
            ],
            "notClosedByBridgeAlone": True,
        },
        "budgetFormula": "coeffErrorAbs + activeScaleAbs * order17Abs / 20 <= polyErrorAbs",
        "budgetPassed": budget["passed"],
        "budgetAudit": budget,
        "d16CenterProofGrade": d16_proof_grade,
        "order17UniformProofGrade": d17_proof_grade,
        "activeScaleProofGrade": active_scale_proof_grade,
        "firstFailure": first_failure,
        "failureCodes": {
            "missingD16OrD17": D16_CENTER_D17_SOURCE_GAP,
            "missingD17AfterArithmeticPass": D17_UNIFORM_SOURCE_GAP,
            "missingRawProduct18UniformSource": RAW_PRODUCT18_UNIFORM_SOURCE_GAP,
            "missingRawProduct18LeibnizReceiver": RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP,
            "missingOmegaPrimeOrder17Source": OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP,
            "missingShapeSqOrder18Source": SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP,
            "exactBudgetFalse": DEGREE0_BUDGET_CONSTANT_FAIL,
        },
        "checkOrder": [
            "D16 center interval",
            "midpoint/error",
            "uniform D17 bound",
            "active-scale multiplication",
            "coeffErrorAbs + activeScaleAbs * order17Abs / 20",
            "exact Rat comparison with polyErrorAbs",
        ],
        "doNotProceedTo": [
            "higher degree beyond the selected RawProduct18 D17-uniform route",
            "higher degree",
            "D46",
            "Lean payload emission",
        ],
    }


def build_ledger() -> dict[str, Any]:
    row_source = load_json(ROW_SOURCE_JSON)
    segment_symbols = symbol_audit(SEGMENT_RECEIVER_LEAN, REQUIRED_SEGMENT_SYMBOLS)
    family_symbols = symbol_audit(FAMILY_BRIDGE_LEAN, REQUIRED_FAMILY_SYMBOLS)
    low_degree_symbols = symbol_audit(LOW_DEGREE_BRIDGE_LEAN, REQUIRED_LOW_DEGREE_SYMBOLS)
    degree0_symbols = symbol_audit(DEGREE0_SOURCE_LEAN, REQUIRED_DEGREE0_SOURCE_SYMBOLS)
    raw_product18_symbols = symbol_audit(
        RAW_PRODUCT18_BRIDGE_LEAN, REQUIRED_RAW_PRODUCT18_BRIDGE_SYMBOLS
    )
    raw_product18_majorant_receiver_symbols = symbol_audit(
        RAW_PRODUCT18_MAJORANT_RECEIVER_LEAN,
        REQUIRED_RAW_PRODUCT18_MAJORANT_RECEIVER_SYMBOLS,
    )
    segment_ready = all_present(segment_symbols)
    family_ready = all_present(family_symbols)
    low_degree_ready = all_present(low_degree_symbols)
    degree0_ready = all_present(degree0_symbols)
    raw_product18_bridge_ready = all_present(raw_product18_symbols)
    raw_product18_majorant_receiver_ready = all_present(
        raw_product18_majorant_receiver_symbols
    )
    interface_ready = segment_ready and family_ready and low_degree_ready and degree0_ready
    degree0_preflight = build_degree0_preflight(
        degree0_ready, raw_product18_bridge_ready, raw_product18_majorant_receiver_ready
    )

    required_inputs = [
        {
            "id": "S0_smoke_segment_domain",
            "status": "planned",
            "cellL": "0",
            "cellU": "1/10",
            "center": "1/20",
            "degree": 29,
        },
        {
            "id": "S1_low_degree_activeActual_row",
            "status": "missing",
            "required": (
                "Use the degree-0 source first: supply a Rat coeff0 for "
                "activeScale * D^16(ComponentProductActual) at center 1/20"
            ),
            "degreePolicy": "low-degree row accepted via checked zero-extension into Fin30",
            "failureCode": D16_CENTER_D17_SOURCE_GAP,
        },
        {
            "id": "S2_low_degree_uniform_remainder",
            "status": "missing",
            "required": (
                "D16 center enclosure, D17 uniform bound, and exact rational budget"
            ),
            "analyticOrderForDegree0": "D16 center plus D17 uniform derivative source",
            "failureCode": D16_CENTER_D17_SOURCE_GAP,
        },
        {
            "id": "S2a_degree0_source_interface",
            "status": "checked" if degree0_ready else "missing",
            "source": rel(DEGREE0_SOURCE_LEAN),
            "coeffDef": "primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff",
            "componentProductActualContDiff17": "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff17",
            "theorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
            "failureCode": D16_CENTER_D17_SOURCE_GAP,
        },
        {
            "id": "S2b_rawProduct18_d17_uniform_bridge",
            "status": "checked" if raw_product18_bridge_ready else "missing",
            "source": rel(RAW_PRODUCT18_BRIDGE_LEAN),
            "equalityTheorem": "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18",
            "absTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_abs",
            "requiredNextSource": "proof-grade uniform D18(RawProductActual) bound",
            "failureCode": RAW_PRODUCT18_UNIFORM_SOURCE_GAP,
        },
        {
            "id": "S2c_rawProduct18_factor_leibniz_receiver",
            "status": "checked" if raw_product18_majorant_receiver_ready else "missing",
            "source": rel(RAW_PRODUCT18_MAJORANT_RECEIVER_LEAN),
            "majorantDef": "primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant",
            "rawProductTheorem": "primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs",
            "componentTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_factor_derivative_abs",
            "requiredNextSources": [
                OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP,
                SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP,
            ],
            "failureCode": RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP,
        },
        {
            "id": "S3_zero_extend_low_degree_to_Fin30",
            "status": "checked" if low_degree_ready else "missing",
            "source": rel(LOW_DEGREE_BRIDGE_LEAN),
            "def": "primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29",
            "theorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree",
            "failureCode": LOW_DEGREE_ALIGNMENT_GAP,
        },
        {
            "id": "S4_horner_range_rows",
            "status": "blocked_on_low_degree_source",
            "required": "stageLower/stageUpper rows for the converted direct segment",
            "failureCode": ROW_SOURCE_GAP,
        },
        {
            "id": "S5_budget_rows",
            "status": "blocked_on_low_degree_source",
            "required": "polyLower/polyUpper/lower/upper/residualAbs rows",
            "failureCode": ROW_SOURCE_GAP,
        },
    ]

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "active_actual_order16_horner_payload_smoke_segment",
        "proofStatus": "blocked_missing_d16_center_d17_uniform_source",
        "proofGrade": False,
        "proofSafeClosedFields": 1 if degree0_preflight["activeScaleProofGrade"] else 0,
        "interfaceReady": interface_ready,
        "outLeanWritten": False,
        "targetLeanFileWhenRowsPass": rel(FUTURE_PAYLOAD_LEAN),
        "currentGap": ROW_SOURCE_GAP,
        "firstFailureCode": ROW_SOURCE_GAP,
        "firstConcreteSubgap": degree0_preflight["firstFailure"],
        "leanValidationStatus": "not_run_payload_not_emitted",
        "sourceFileDigests": {
            rel(SEGMENT_RECEIVER_LEAN): sha256_file(SEGMENT_RECEIVER_LEAN),
            rel(FAMILY_BRIDGE_LEAN): sha256_file(FAMILY_BRIDGE_LEAN),
            rel(LOW_DEGREE_BRIDGE_LEAN): sha256_file(LOW_DEGREE_BRIDGE_LEAN),
            rel(DEGREE0_SOURCE_LEAN): sha256_file(DEGREE0_SOURCE_LEAN),
            rel(RAW_PRODUCT18_BRIDGE_LEAN): sha256_file(RAW_PRODUCT18_BRIDGE_LEAN),
            rel(RAW_PRODUCT18_MAJORANT_RECEIVER_LEAN): sha256_file(
                RAW_PRODUCT18_MAJORANT_RECEIVER_LEAN
            ),
            rel(ACTIVE_CENTER_ROWS_LEAN): sha256_file(ACTIVE_CENTER_ROWS_LEAN),
            rel(ACTIVE_SCALE_BOUND_INPUTS_LEAN): sha256_file(ACTIVE_SCALE_BOUND_INPUTS_LEAN),
            rel(ACTIVE_SCALE_BOUND_ASSEMBLY_LEAN): sha256_file(ACTIVE_SCALE_BOUND_ASSEMBLY_LEAN),
            rel(ROW_SOURCE_JSON): sha256_file(ROW_SOURCE_JSON),
        },
        "degree0Preflight": {
            "path": rel(DEGREE0_JSON_OUT),
            "markdown": rel(DEGREE0_MD_OUT),
            "schema": DEGREE0_SCHEMA,
            "proofGrade": degree0_preflight["proofGrade"],
            "budgetPassed": degree0_preflight["budgetPassed"],
            "firstFailure": degree0_preflight["firstFailure"],
            "receiverReady": degree0_preflight["receiverReady"],
            "activeScaleAbs": degree0_preflight["fields"]["activeScaleAbs"],
            "activeScaleProofGrade": degree0_preflight["activeScaleProofGrade"],
            "rawProduct18BridgeReady": raw_product18_bridge_ready,
            "rawProduct18MajorantReceiverReady": raw_product18_majorant_receiver_ready,
            "rawProduct18UniformSourceChecked": False,
        },
        "rowSourceLedger": {
            "path": rel(ROW_SOURCE_JSON),
            "schema": row_source.get("schema"),
            "proofStatus": row_source.get("proofStatus"),
            "proofGrade": row_source.get("proofGrade"),
            "firstFailureCode": row_source.get("firstFailureCode"),
        },
        "targetLeanSurface": {
            "dataObject": "primaryFiniteRow0Parent0Split100Sub0ActiveActualOrder16HornerSegment0",
            "validTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment0_valid",
            "remainderTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment0_remainder_generated",
            "degree0SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source",
            "degree0ContDiff17SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17",
            "degree0CheckedContDiff17SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
            "familyValidTarget": "Step33Sub0ActiveActualOrder16HornerFamilyCert.Valid",
            "payloadTarget": "primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily",
        },
        "smokeSegment": {
            "cellL": "0",
            "cellU": "1/10",
            "center": "1/20",
            "degree": 29,
            "cell": "Set.Icc 0 (1/10)",
            "payloadAllowed": False,
            "outLeanWritten": False,
            "degree29IsContainerOnly": True,
        },
        "degree29ContainerPolicy": {
            "targetFunction": "activeScale * D^16(ComponentProductActual)",
            "containerDegree": 29,
            "containerCoeffType": "Fin 30 -> Rat",
            "lowDegreeAccepted": low_degree_ready,
            "lowDegreeBridge": rel(LOW_DEGREE_BRIDGE_LEAN),
            "zeroExtendDef": "primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29",
            "transferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree",
            "degree0SourceBridge": rel(DEGREE0_SOURCE_LEAN),
            "degree0SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source",
            "degree0ContDiff17SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17",
            "degree0CheckedContDiff17SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
            "firstConcreteSubgap": D16_CENTER_D17_SOURCE_GAP,
            "d17UniformRoute": {
                "selectedRoute": "B_rawProduct18",
                "bridgeSource": rel(RAW_PRODUCT18_BRIDGE_LEAN),
                "bridgeReady": raw_product18_bridge_ready,
                "majorantReceiverSource": rel(RAW_PRODUCT18_MAJORANT_RECEIVER_LEAN),
                "majorantReceiverReady": raw_product18_majorant_receiver_ready,
                "failureIfUniformSourceMissing": RAW_PRODUCT18_UNIFORM_SOURCE_GAP,
                "remainingFactorSources": [
                    OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP,
                    SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP,
                ],
            },
            "fullDegree29Specialization": {
                "coefficientJetOrdersNeeded": "16..45",
                "uniformRemainderDerivativeOrderNeeded": 46,
                "firstMissingSubgapIfChosen": D46_SOURCE_GAP,
            },
        },
        "availableUpstreamEvidence": {
            "activeActualCenterJetRows": center_row_status(),
            "activeScaleBound": active_scale_source(),
            "rawProduct18Bridge": raw_product18_bridge_source(raw_product18_bridge_ready),
            "rawProduct18MajorantReceiver": raw_product18_majorant_receiver_source(
                raw_product18_majorant_receiver_ready
            ),
        },
        "requiredInputs": required_inputs,
        "validationGates": {
            "segmentReceiverReady": segment_ready,
            "familyBridgeReady": family_ready,
            "lowDegreeBridgeReady": low_degree_ready,
            "degree0SourceInterfaceReady": degree0_ready,
            "rawProduct18BridgeReady": raw_product18_bridge_ready,
            "rawProduct18MajorantReceiverReady": raw_product18_majorant_receiver_ready,
            "rawProduct18UniformSourceChecked": False,
            "omegaPrimeOrder17UniformSourceChecked": False,
            "shapeSqOrder18UniformSourceChecked": False,
            "degree0PreflightWritten": True,
            "degree0BudgetPassed": degree0_preflight["budgetPassed"],
            "activeScaleBoundChecked": degree0_preflight["activeScaleProofGrade"],
            "activeActualLowDegreeSegmentRemainderSourceChecked": False,
            "activeActualD16CenterD17UniformSourceChecked": False,
            "activeActualD46UniformRemainderSourceChecked": False,
            "activeActualCoeffOrders16To45Checked": False,
            "smokeSegmentValidChecked": False,
            "hornerRangeRowsChecked": False,
            "budgetRowsChecked": False,
            "allPayloadObligationsPassed": False,
        },
        "computerUseDecision": {
            "used": True,
            "advisoryOnly": True,
            "recommendedOption": "A",
            "firstFileToEdit": rel(Path(__file__).resolve()),
            "exactOutputObject": rel(DEGREE0_JSON_OUT),
            "decision": (
                "Add a fail-closed degree-0 preflight for the checked "
                "Degree0Source receiver before D18, higher degree, D46, or Lean "
                "payload emission."
            ),
            "budgetFailureCode": DEGREE0_BUDGET_CONSTANT_FAIL,
            "d17SourceFailureCode": D17_UNIFORM_SOURCE_GAP,
            "rawProduct18UniformSourceFailureCode": RAW_PRODUCT18_UNIFORM_SOURCE_GAP,
            "notProofEvidence": True,
        },
        "computerUseRawProduct18Decision": {
            "used": True,
            "advisoryOnly": True,
            "recommendedOption": "B",
            "firstFileToEdit": rel(RAW_PRODUCT18_BRIDGE_LEAN),
            "bridgeTheorem": "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18",
            "uniformSourceFailureCode": RAW_PRODUCT18_UNIFORM_SOURCE_GAP,
            "budgetFailureCode": DEGREE0_BUDGET_CONSTANT_FAIL,
            "notProofEvidence": True,
        },
        "computerUseRawProduct18ReceiverDecision": {
            "used": True,
            "advisoryOnly": True,
            "recommendedOption": "A",
            "firstFileToEdit": rel(RAW_PRODUCT18_MAJORANT_RECEIVER_LEAN),
            "firstTheorem": "primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs",
            "receiverFailureCode": RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP,
            "omegaPrimeOrder17SourceFailureCode": OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP,
            "shapeSqOrder18SourceFailureCode": SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP,
            "notProofEvidence": True,
        },
        "doNotUseAsProof": [
            "sampled activeActual rows",
            "center-jet rows as uniform segment remainder rows",
            "coarse P45/factor-majorant route",
            "separate activeActual and nominal error budgets",
            "Lean payload file before S1/S2 proof-grade inputs exist",
            "D46 backend as mandatory before the low-degree source is tested",
        ],
        "nextImplementablePatch": (
            "Build the remaining proof-grade factor sources for the checked "
            "RawProduct18 receiver: OmegaPrime order17 and ShapeSq order18, "
            "then compute the exact RawProduct18 majorant and degree-0 budget "
            "before emitting any Lean payload."
        ),
    }


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A ActiveActual Order-16 Horner Payload Gate",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        "",
        "## Verdict",
        "",
        f"- proofStatus: `{ledger['proofStatus']}`",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- proofSafeClosedFields: `{ledger['proofSafeClosedFields']}`",
        f"- interfaceReady: `{ledger['interfaceReady']}`",
        f"- outLeanWritten: `{ledger['outLeanWritten']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- firstFailureCode: `{ledger['firstFailureCode']}`",
        f"- firstConcreteSubgap: `{ledger['firstConcreteSubgap']}`",
        f"- leanValidationStatus: `{ledger['leanValidationStatus']}`",
        "",
        "## Target Lean Surface",
        "",
    ]
    for key, value in ledger["targetLeanSurface"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Smoke Segment", ""])
    for key, value in ledger["smokeSegment"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Degree-0 Preflight", ""])
    for key, value in ledger["degree0Preflight"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Degree-29 Container Policy", ""])
    for key, value in ledger["degree29ContainerPolicy"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Required Inputs", ""])
    for item in ledger["requiredInputs"]:
        lines.append(f"### {item['id']}")
        lines.append("")
        for key, value in item.items():
            if key != "id":
                lines.append(f"- `{key}`: `{value}`")
        lines.append("")

    lines.extend(["## Validation Gates", ""])
    for key, value in ledger["validationGates"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Available Upstream Evidence", ""])
    active = ledger["availableUpstreamEvidence"]["activeActualCenterJetRows"]
    lines.append("### activeActualCenterJetRows")
    lines.append("")
    for key, value in active.items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Row Source Ledger", ""])
    for key, value in ledger["rowSourceLedger"].items():
        lines.append(f"- `{key}`: `{value}`")

    decision = ledger["computerUseDecision"]
    lines.extend(["", "## Computer Use Decision", ""])
    for key, value in decision.items():
        lines.append(f"- `{key}`: `{value}`")

    raw_decision = ledger["computerUseRawProduct18Decision"]
    lines.extend(["", "## Computer Use RawProduct18 Decision", ""])
    for key, value in raw_decision.items():
        lines.append(f"- `{key}`: `{value}`")

    receiver_decision = ledger["computerUseRawProduct18ReceiverDecision"]
    lines.extend(["", "## Computer Use RawProduct18 Receiver Decision", ""])
    for key, value in receiver_decision.items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Do Not Use As Proof", ""])
    for item in ledger["doNotUseAsProof"]:
        lines.append(f"- {item}")

    lines.extend(["", "## Next Implementable Patch", ""])
    lines.append(ledger["nextImplementablePatch"])
    lines.append("")
    return "\n".join(lines)


def render_degree0_markdown(preflight: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A ActiveActual Order-16 Degree-0 Preflight",
        "",
        f"schema: `{preflight['schema']}`",
        f"route: `{preflight['route']}`",
        "",
        "## Verdict",
        "",
        f"- proofStatus: `{preflight['proofStatus']}`",
        f"- proofGrade: `{preflight['proofGrade']}`",
        f"- receiverReady: `{preflight['receiverReady']}`",
        f"- outLeanWritten: `{preflight['outLeanWritten']}`",
        f"- budgetPassed: `{preflight['budgetPassed']}`",
        f"- firstFailure: `{preflight['firstFailure']}`",
        "",
        "## Target",
        "",
        f"- target: `{preflight['target']}`",
        f"- cell: `{preflight['cell']}`",
        f"- center: `{preflight['center']}`",
        f"- degree: `{preflight['degree']}`",
        f"- receiverTheorem: `{preflight['receiverTheorem']}`",
        "",
        "## Fields",
        "",
    ]
    for key, value in preflight["fields"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Budget Audit", ""])
    lines.append(f"- formula: `{preflight['budgetFormula']}`")
    for key, value in preflight["budgetAudit"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Proof Flags", ""])
    lines.append(f"- `d16CenterProofGrade`: `{preflight['d16CenterProofGrade']}`")
    lines.append(f"- `order17UniformProofGrade`: `{preflight['order17UniformProofGrade']}`")
    lines.append(f"- `activeScaleProofGrade`: `{preflight['activeScaleProofGrade']}`")

    lines.extend(["", "## Active Scale Source", ""])
    for key, value in preflight["activeScaleSource"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Order17 Uniform Route", ""])
    for key, value in preflight["order17UniformRoute"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Failure Codes", ""])
    for key, value in preflight["failureCodes"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Check Order", ""])
    for item in preflight["checkOrder"]:
        lines.append(f"- {item}")

    lines.extend(["", "## Do Not Proceed To", ""])
    for item in preflight["doNotProceedTo"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    degree0_preflight = build_degree0_preflight(
        bool(ledger["validationGates"]["degree0SourceInterfaceReady"]),
        bool(ledger["validationGates"]["rawProduct18BridgeReady"]),
        bool(ledger["validationGates"]["rawProduct18MajorantReceiverReady"]),
    )
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    DEGREE0_JSON_OUT.write_text(
        json.dumps(degree0_preflight, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    DEGREE0_MD_OUT.write_text(render_degree0_markdown(degree0_preflight), encoding="utf-8")
    print(f"wrote {rel(JSON_OUT)}")
    print(f"wrote {rel(MD_OUT)}")
    print(f"wrote {rel(DEGREE0_JSON_OUT)}")
    print(f"wrote {rel(DEGREE0_MD_OUT)}")
    print(ledger["proofStatus"])
    print(ledger["firstFailureCode"])
    print(ledger["firstConcreteSubgap"])
    print(degree0_preflight["firstFailure"])

    if ledger["validationGates"]["allPayloadObligationsPassed"]:
        raise SystemExit(
            "payload obligations are marked passed, but Lean emission is not "
            "implemented in this fail-closed gate"
        )


if __name__ == "__main__":
    main()
