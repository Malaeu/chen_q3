#!/usr/bin/env python3
"""Fail-closed combined cancellation high-order certificate ledger.

This script records the exact proof-grade interface for the current
Step33A.1-A sub0 gate:

    P45 residualTaylor polynomial + ScaledCancellationRhs

on [0, 1/10].  It deliberately does not emit Lean or mark the node closed
until a proof-grade `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid`
payload is available.  Sampled diagnostic intervals may be copied into the
ledger, but they remain diagnostic.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

DEFAULT_SEGMENTED_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_segmented_residual_deriv_interval_payload.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_combined_cancellation_interval_certificate.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_combined_cancellation_interval_certificate.md"
)

COMBINED_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval.lean"
)
CERT_CHECKER_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalCert.lean"
)
CONDITIONAL_PAYLOAD_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload.lean"
)
HIGH_ORDER_SOURCE_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationHighOrderTaylorSource.lean"
)
SOURCE_MODEL_BRIDGE_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean"
)
SOURCE_INTERVAL_CERT_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean"
)
SOURCE_NORMAL_FORM_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean"
)
ACTIVE_ACTUAL_CENTERJET_ROWS_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean"
)
CENTERJET_PAYLOAD_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationCenterJetPayload.lean"
)
ORDER16_FACTOR_MAJORANT_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorMajorant.lean"
)
ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver.lean"
)
ORDER16_FACTOR_DERIVATIVE_MAJORANT_BRIDGE_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge.lean"
)
ORDER16_BUDGET_PAYLOAD_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean"
)
BOUND_INPUTS_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean"
)
NORM_RECEIVER_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean"
)
P45_BRIDGE_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationP45Bridge.lean"
)
LANDING_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean"
COMPONENT_ASSEMBLY_PAYLOAD_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean"
)
COMPONENT_ASSEMBLY_LEDGER = (
    "ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_assembly_stream_ledger.json"
)
OMEGA_PRIME_PAYLOAD = (
    "ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_taylor_payload.json"
)

SCHEMA = "q3_psdpd_step33_a1_sub0_combined_cancellation_interval_certificate.v20"
ROUTE_ID = "STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_TAYLOR"
STATUS = "fail_closed_missing_high_order_valid_payload"
FIRST_FAILURE = "STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_VALID_PAYLOAD_GAP"
NEXT_PAYLOAD_FAILURE = (
    "STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JETS_ORDER16_PAYLOAD_GAP"
)
SOURCE_MODEL_FAILURE = (
    "STEP33_A1_SUB0_COMBINED_CANCELLATION_WHOLE_EXPRESSION_SOURCE_MODEL_GAP"
)
CENTER_JET_SOURCE_MODEL_FAILURE = (
    "STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JET_SOURCE_MODEL_GAP"
)
ORDER16_SOURCE_MODEL_FAILURE = (
    "STEP33_A1_SUB0_COMBINED_CANCELLATION_ORDER16_SOURCE_MODEL_GAP"
)
SAMPLED_STATUS = "sampled_candidate_not_lean_proof"
TARGET_LOWER = "-94119513411/500000000000000000000000000000"
TARGET_UPPER = "1866608532757/500000000000000000000000000000"
CELL_L = "0"
CELL_U = "1/10"

TARGET_EXPR = "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr"
TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_combined_bounds"
)
TARGET_CLOSED_FORM_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_closedForm_residual_bounds_of_combined_bounds"
)
TARGET_PROOF_DATA = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_combined_bounds"
)
HIGH_ORDER_CERT_STRUCTURE = "Step33Sub0CombinedCancellationHighOrderTaylorCert"
HIGH_ORDER_VALID = "Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid"
HIGH_ORDER_REMAINDER = "Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.remainder_bound"
HIGH_ORDER_TO_INTERVAL = "Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_interval_valid"
HIGH_ORDER_TO_HCOMBINED = "Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_hCombined"
HIGH_ORDER_TO_RESIDUAL = (
    "Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_fullTaylor_residual_deriv_interval"
)
SOURCE_MODEL_SMOOTH_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16"
)
SOURCE_MODEL_CENTER_JET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_componentSource"
)
SOURCE_MODEL_ORDER16_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource"
)
SOURCE_MODEL_ORDER16_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_eq_componentSource"
)
SOURCE_MODEL_ORDER16_BOUND_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_bound_of_componentSource"
)
SOURCE_MODEL_CENTER_JET_BOUNDS_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_bounds_of_componentSource"
)
SOURCE_MODEL_HIGH_ORDER_VALID_CONSTRUCTOR = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_bounds"
)
SOURCE_MODEL_HIGH_ORDER_INTERVAL_CONSTRUCTOR = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_interval"
)
SOURCE_INTERVAL_CERT_STRUCTURE = "Step33Sub0CombinedCancellationSourceIntervalCert"
SOURCE_INTERVAL_CERT_VALID = "Step33Sub0CombinedCancellationSourceIntervalCert.Valid"
SOURCE_INTERVAL_CERT_TO_HIGH_ORDER = (
    "Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_highOrderValid"
)
SOURCE_INTERVAL_CERT_TO_HCOMBINED = (
    "Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_hCombined"
)
SOURCE_INTERVAL_CERT_TO_RESIDUAL = (
    "Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_fullTaylor_residual_deriv_interval"
)
SOURCE_NORMAL_FORM_CANCELLATION_CAUCHY = (
    "primaryFiniteRow0Parent0Split100Sub0_cancellationResidualCauchy_eq_actual_sub_nominal"
)
SOURCE_NORMAL_FORM_CONDITIONAL_CENTER_JET = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model_of_residualJet"
)
SOURCE_NORMAL_FORM_RESIDUAL_JET_BRIDGE = (
    "primaryFiniteRow0Parent0Split100Sub0_residualTaylor_centerJet_low_eq_nominalProduct_sub_model"
)
SOURCE_NORMAL_FORM_NONCONDITIONAL_CENTER_JET = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model"
)
SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceCenterInterval_of_activeActual_interval"
)
SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_VALID_CONSTRUCTOR = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_activeActual_interval"
)
SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_SOURCE_INTERVAL_VALID = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceIntervalValid_of_activeActual_interval"
)
SOURCE_NORMAL_FORM_COEFF_ALIGNMENT_FAILURE = (
    "STEP33_A1_SUB0_COMBINED_CANCELLATION_SOURCE_NORMAL_FORM_COEFF_ALIGNMENT_GAP"
)
ACTIVE_ACTUAL_SINGLEABS_TO_SIGNED_FAILURE = (
    "STEP33_A1_SUB0_COMPONENT_PRODUCT_ACTUAL_SINGLEABS_TO_SIGNED_CENTERJET_CROSSWALK_GAP"
)
ACTIVE_ACTUAL_CENTERJET_INTERVAL_OF_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0_centerJet_interval_of_abs"
)
ACTIVE_ACTUAL_SHAPESQDERIV_SINGLEABS_SIGNED = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_singleAbs_signed_centerJet_interval"
)
ACTIVE_ACTUAL_SHAPESQDERIV_ROWS_SIGNED = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567891011_signed_centerJet_interval"
)
ACTIVE_ACTUAL_OMEGAPRIME_SIGNED = (
    "primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_signed_centerJet_interval"
)
ACTIVE_ACTUAL_OMEGA_SIGNED = (
    "primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval"
)
ACTIVE_ACTUAL_SHAPESQ_SIGNED = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval"
)
ACTIVE_ACTUAL_SIGNED_FACTOR_ROWS_FAILURE = (
    "STEP33_A1_SUB0_COMPONENT_PRODUCT_ACTUAL_SIGNED_FACTOR_JET_ROWS_GAP"
)
ACTIVE_ACTUAL_FACTOR_INTERVAL_RECEIVER_FAILURE = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_FACTOR_INTERVAL_TO_ROW_RECEIVER_GAP"
)
ACTIVE_ACTUAL_SUM_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_sum_interval_of_term_intervals"
)
ACTIVE_ACTUAL_CAUCHY_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_normalizedJetConvolution_interval_of_term_intervals"
)
ACTIVE_ACTUAL_COMPONENT_PRODUCT_CAUCHY_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActualCauchy_interval"
)
ACTIVE_ACTUAL_SCALE_NONNEG = (
    "primaryFiniteRow0Parent0Split100Sub0_activeScale_nonneg"
)
ACTIVE_ACTUAL_ROW_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_of_product_interval"
)
ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyAbs"
)
ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActualCauchy_abs_interval"
)
ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_NONNEG = (
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActualCauchyAbs_nonneg"
)
ACTIVE_ACTUAL_CENTER_ROW_LOWER = (
    "primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowLower"
)
ACTIVE_ACTUAL_CENTER_ROW_UPPER = (
    "primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowUpper"
)
ACTIVE_ACTUAL_CENTER_ROW_INTERVAL_FROM_FACTOR_ROWS = (
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows"
)
ACTIVE_ACTUAL_PRODUCT_ROWS_FAILURE = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_PRODUCT_ROW_INTERVALS_GAP"
)
CENTERJET_ABS_PAYLOAD_FAILURE = (
    "STEP33_A1_SUB0_COMBINED_CANCELLATION_SIGNED_ROWS_TO_CENTERJET_ABS_GAP"
)
ORDER16_SOURCE_INTERVAL_PAYLOAD_FAILURE = (
    "STEP33_A1_SUB0_COMBINED_CANCELLATION_ORDER16_SOURCE_INTERVAL_PAYLOAD_GAP"
)
FACTOR_DERIVATIVE_BOUNDS_FAILURE = (
    "STEP33_A1_SUB0_COMPONENT_PRODUCT_ACTUAL_FACTOR_DERIVATIVE_BOUNDS_0_TO_16_GAP"
)
FACTOR_DERIVATIVE_BUDGET_FAILURE = (
    "STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL"
)
FACTOR_DERIVATIVE_BUDGET_FAILURE_ALIAS = (
    "STEP33_A1_SUB0_COMPONENT_PRODUCT_ACTUAL_FACTOR_DERIVATIVE_BUDGET_CONSTANT_FAIL"
)
CENTERJET_COEFF = (
    "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeff"
)
CENTERJET_COEFF_ERROR_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs"
)
CENTERJET_COEFF_ERROR_ABS_NONNEG = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_coeffErrorAbs_nonneg"
)
CENTERJET_COMPONENT_SOURCE_ABS_GENERATED = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_componentSource_centerJet_abs_generated"
)
CENTERJET_ABS_GENERATED = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_abs_generated"
)
ORDER16_SOURCE_EQ_ACTIVE_ACTUAL = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual"
)
ORDER16_COMPONENT_PRODUCT_MAJORANT = (
    "primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant"
)
ORDER16_COMPONENT_PRODUCT_ABS_RECEIVER = (
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_factor_derivative_abs"
)
ORDER16_SOURCE_ABS_RECEIVER = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_abs_of_factor_derivative_abs"
)
ORDER16_SOURCE_INTERVAL_RECEIVER = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_factor_derivative_abs"
)
ORDER16_SOURCE_INTERVAL_CENTERED_TAYLOR_RECEIVER = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_centeredTaylor_factor_majorants"
)
ORDER16_ACTIVE_SCALE_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_activeScaleAbs"
)
ORDER16_BUDGET_LE_DECLARED_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16BudgetRat_le_declaredAbs"
)
ORDER16_REMAINDER_WIDTH_FAIL_RAT = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail_rat"
)
ORDER16_REMAINDER_WIDTH_FAIL = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail"
)


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def file_hash(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def parse_rat(value: str | int) -> Fraction:
    if isinstance(value, int):
        return Fraction(value, 1)
    text = str(value)
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def rat_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def normalize_segments(segmented: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not segmented:
        return []
    segments: list[dict[str, Any]] = []
    for item in segmented.get("segments", []):
        if not isinstance(item, dict):
            continue
        lower = item.get("residualLower")
        upper = item.get("residualUpper")
        budget_passes = False
        if lower is not None and upper is not None:
            budget_passes = (
                parse_rat(TARGET_LOWER) <= parse_rat(lower)
                and parse_rat(upper) <= parse_rat(TARGET_UPPER)
            )
        proof_status = item.get("sourceProofStatus")
        segments.append(
            {
                "cell": item.get("cell"),
                "segmentL": item.get("segmentL"),
                "segmentU": item.get("segmentU"),
                "combinedLower": lower,
                "combinedUpper": upper,
                "sourceProofStatus": proof_status,
                "budgetPassesExactRational": budget_passes,
                "isProofGrade": proof_status
                not in (None, SAMPLED_STATUS, "probe", "diagnostic"),
                "proofGradeCombinedBounds": "missing",
            }
        )
    return segments


def coverage_report(segments: list[dict[str, Any]]) -> dict[str, Any]:
    if not segments:
        return {
            "coveragePassedExactRational": False,
            "adjacencyPassedExactRational": False,
            "segmentNonemptyPassedExactRational": False,
            "firstFailure": "STEP33_A1_SUB0_COMBINED_SEGMENT_INPUTS_MISSING",
        }
    lefts = [parse_rat(str(item["segmentL"])) for item in segments]
    rights = [parse_rat(str(item["segmentU"])) for item in segments]
    nonempty = all(left <= right for left, right in zip(lefts, rights))
    endpoint = lefts[0] == parse_rat(CELL_L) and rights[-1] == parse_rat(CELL_U)
    adjacency = all(rights[i] == lefts[i + 1] for i in range(len(segments) - 1))
    coverage = nonempty and endpoint and adjacency
    return {
        "coveragePassedExactRational": coverage,
        "adjacencyPassedExactRational": adjacency,
        "segmentNonemptyPassedExactRational": nonempty,
        "leftEndpoint": rat_text(lefts[0]),
        "rightEndpoint": rat_text(rights[-1]),
        "expectedLeftEndpoint": CELL_L,
        "expectedRightEndpoint": CELL_U,
        "firstFailure": None if coverage else "STEP33_A1_SUB0_COMBINED_SEGMENT_COVERAGE_FAIL",
    }


def line_of_symbol(path: Path, symbol: str) -> int | None:
    if not path.exists():
        return None
    for index, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if symbol.startswith(("def ", "theorem ", "structure ")):
            stripped = line.strip()
            if (
                stripped == symbol
                or stripped.startswith(symbol + " ")
                or stripped.startswith(symbol + " :")
                or stripped.startswith(symbol + " (")
            ):
                return index
            continue
        if symbol in line:
            return index
    return None


def symbol_ref(file_name: str, symbol: str) -> dict[str, Any]:
    path = ROOT / file_name
    return {
        "file": file_name,
        "symbol": symbol,
        "line": line_of_symbol(path, symbol),
        "exists": path.exists(),
    }


def symbol_ref_lookup(file_name: str, symbol: str, lookup_symbol: str) -> dict[str, Any]:
    path = ROOT / file_name
    return {
        "file": file_name,
        "symbol": symbol,
        "lookupSymbol": lookup_symbol,
        "line": line_of_symbol(path, lookup_symbol),
        "exists": path.exists(),
    }


def build_report(segmented_path: Path) -> dict[str, Any]:
    segmented = load_json(segmented_path)
    segments = normalize_segments(segmented)
    coverage = coverage_report(segments)
    budget_passed = bool(segments) and all(
        segment["budgetPassesExactRational"] for segment in segments
    )
    proof_grade_segments = bool(segments) and all(
        segment["isProofGrade"] for segment in segments
    )
    target_width = parse_rat(TARGET_UPPER) - parse_rat(TARGET_LOWER)
    source_model_smooth_present = (
        line_of_symbol(ROOT / SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_SMOOTH_THEOREM)
        is not None
    )
    source_model_center_jet_present = (
        line_of_symbol(ROOT / SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_CENTER_JET_THEOREM)
        is not None
    )
    source_model_order16_present = (
        line_of_symbol(ROOT / SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_ORDER16_DEF)
        is not None
        and line_of_symbol(ROOT / SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_ORDER16_THEOREM)
        is not None
        and line_of_symbol(
            ROOT / SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_ORDER16_BOUND_THEOREM
        )
        is not None
    )
    source_model_bridge_present = (
        source_model_smooth_present and source_model_center_jet_present
    )
    full_source_model_bridge_present = (
        source_model_bridge_present and source_model_order16_present
    )
    source_bounds_constructor_present = (
        full_source_model_bridge_present
        and line_of_symbol(
            ROOT / SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_CENTER_JET_BOUNDS_THEOREM
        )
        is not None
        and line_of_symbol(
            ROOT / SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_HIGH_ORDER_VALID_CONSTRUCTOR
        )
        is not None
    )
    source_interval_constructor_present = (
        source_bounds_constructor_present
        and line_of_symbol(
            ROOT / SOURCE_MODEL_BRIDGE_FILE,
            SOURCE_MODEL_HIGH_ORDER_INTERVAL_CONSTRUCTOR,
        )
        is not None
    )
    source_interval_cert_structure_present = (
        line_of_symbol(
            ROOT / SOURCE_INTERVAL_CERT_FILE,
            f"structure {SOURCE_INTERVAL_CERT_STRUCTURE}",
        )
        is not None
    )
    source_interval_cert_valid_present = (
        line_of_symbol(ROOT / SOURCE_INTERVAL_CERT_FILE, "structure Valid")
        is not None
    )
    source_interval_cert_to_high_order_present = (
        line_of_symbol(ROOT / SOURCE_INTERVAL_CERT_FILE, "theorem to_highOrderValid")
        is not None
    )
    source_interval_cert_to_hcombined_present = (
        line_of_symbol(ROOT / SOURCE_INTERVAL_CERT_FILE, "theorem to_hCombined")
        is not None
    )
    source_interval_cert_to_residual_present = (
        line_of_symbol(
            ROOT / SOURCE_INTERVAL_CERT_FILE,
            "theorem to_fullTaylor_residual_deriv_interval",
        )
        is not None
    )
    source_interval_cert_target_present = (
        source_interval_cert_structure_present
        and source_interval_cert_valid_present
        and source_interval_cert_to_high_order_present
        and source_interval_cert_to_hcombined_present
        and source_interval_cert_to_residual_present
    )
    source_normal_form_cancellation_cauchy_present = (
        line_of_symbol(
            ROOT / SOURCE_NORMAL_FORM_FILE,
            f"theorem {SOURCE_NORMAL_FORM_CANCELLATION_CAUCHY}",
        )
        is not None
    )
    source_normal_form_conditional_center_jet_present = (
        line_of_symbol(
            ROOT / SOURCE_NORMAL_FORM_FILE,
            f"theorem {SOURCE_NORMAL_FORM_CONDITIONAL_CENTER_JET}",
        )
        is not None
    )
    source_normal_form_residual_jet_bridge_present = (
        line_of_symbol(
            ROOT / SOURCE_NORMAL_FORM_FILE,
            f"theorem {SOURCE_NORMAL_FORM_RESIDUAL_JET_BRIDGE}",
        )
        is not None
    )
    source_normal_form_nonconditional_present = (
        line_of_symbol(
            ROOT / SOURCE_NORMAL_FORM_FILE,
            f"theorem {SOURCE_NORMAL_FORM_NONCONDITIONAL_CENTER_JET}",
        )
        is not None
    )
    source_normal_form_active_actual_interval_present = (
        line_of_symbol(
            ROOT / SOURCE_NORMAL_FORM_FILE,
            f"theorem {SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_INTERVAL}",
        )
        is not None
    )
    source_normal_form_active_actual_valid_constructor_present = (
        line_of_symbol(
            ROOT / SOURCE_NORMAL_FORM_FILE,
            f"theorem {SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_VALID_CONSTRUCTOR}",
        )
        is not None
    )
    source_normal_form_active_actual_source_interval_valid_present = (
        line_of_symbol(
            ROOT / SOURCE_NORMAL_FORM_FILE,
            f"theorem {SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_SOURCE_INTERVAL_VALID}",
        )
        is not None
    )
    source_normal_form_support_present = (
        source_normal_form_cancellation_cauchy_present
        and source_normal_form_conditional_center_jet_present
    )
    source_normal_form_complete_present = (
        source_normal_form_support_present
        and source_normal_form_residual_jet_bridge_present
        and source_normal_form_nonconditional_present
    )
    source_normal_form_active_actual_interface_present = (
        source_normal_form_complete_present
        and source_normal_form_active_actual_interval_present
        and source_normal_form_active_actual_valid_constructor_present
        and source_normal_form_active_actual_source_interval_valid_present
    )
    active_actual_centerjet_interval_of_abs_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_CENTERJET_INTERVAL_OF_ABS}",
        )
        is not None
    )
    active_actual_shapesqderiv_singleabs_signed_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_SHAPESQDERIV_SINGLEABS_SIGNED}",
        )
        is not None
    )
    active_actual_shapesqderiv_rows_signed_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_SHAPESQDERIV_ROWS_SIGNED}",
        )
        is not None
    )
    active_actual_omegaprime_signed_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_OMEGAPRIME_SIGNED}",
        )
        is not None
    )
    active_actual_omega_signed_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_OMEGA_SIGNED}",
        )
        is not None
    )
    active_actual_shapesq_signed_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_SHAPESQ_SIGNED}",
        )
        is not None
    )
    active_actual_singleabs_to_signed_present = (
        active_actual_centerjet_interval_of_abs_present
        and active_actual_shapesqderiv_singleabs_signed_present
        and active_actual_shapesqderiv_rows_signed_present
    )
    active_actual_all_factor_signed_rows_present = (
        active_actual_omegaprime_signed_present
        and active_actual_omega_signed_present
        and active_actual_shapesq_signed_present
        and active_actual_shapesqderiv_rows_signed_present
    )
    active_actual_sum_interval_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_SUM_INTERVAL}",
        )
        is not None
    )
    active_actual_cauchy_interval_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_CAUCHY_INTERVAL}",
        )
        is not None
    )
    active_actual_component_product_cauchy_interval_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_COMPONENT_PRODUCT_CAUCHY_INTERVAL}",
        )
        is not None
    )
    active_actual_scale_nonneg_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_SCALE_NONNEG}",
        )
        is not None
    )
    active_actual_row_interval_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_ROW_INTERVAL}",
        )
        is not None
    )
    active_actual_factor_interval_receiver_present = (
        active_actual_sum_interval_present
        and active_actual_cauchy_interval_present
        and active_actual_component_product_cauchy_interval_present
        and active_actual_scale_nonneg_present
        and active_actual_row_interval_present
    )
    active_actual_component_product_abs_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"def {ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS}",
        )
        is not None
    )
    active_actual_component_product_abs_interval_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_INTERVAL}",
        )
        is not None
    )
    active_actual_component_product_abs_nonneg_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_NONNEG}",
        )
        is not None
    )
    active_actual_center_row_lower_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"def {ACTIVE_ACTUAL_CENTER_ROW_LOWER}",
        )
        is not None
    )
    active_actual_center_row_upper_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"def {ACTIVE_ACTUAL_CENTER_ROW_UPPER}",
        )
        is not None
    )
    active_actual_center_row_interval_from_factor_rows_present = (
        line_of_symbol(
            ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            f"theorem {ACTIVE_ACTUAL_CENTER_ROW_INTERVAL_FROM_FACTOR_ROWS}",
        )
        is not None
    )
    active_actual_product_row_intervals_present = (
        active_actual_component_product_abs_present
        and active_actual_component_product_abs_interval_present
        and active_actual_component_product_abs_nonneg_present
        and active_actual_center_row_lower_present
        and active_actual_center_row_upper_present
        and active_actual_center_row_interval_from_factor_rows_present
    )
    centerjet_payload_file_present = (ROOT / CENTERJET_PAYLOAD_FILE).exists()
    centerjet_coeff_present = (
        line_of_symbol(ROOT / CENTERJET_PAYLOAD_FILE, f"def {CENTERJET_COEFF}")
        is not None
    )
    centerjet_coeff_error_abs_present = (
        line_of_symbol(
            ROOT / CENTERJET_PAYLOAD_FILE, f"def {CENTERJET_COEFF_ERROR_ABS}"
        )
        is not None
    )
    centerjet_coeff_error_abs_nonneg_present = (
        line_of_symbol(
            ROOT / CENTERJET_PAYLOAD_FILE,
            f"theorem {CENTERJET_COEFF_ERROR_ABS_NONNEG}",
        )
        is not None
    )
    centerjet_component_source_abs_present = (
        line_of_symbol(
            ROOT / CENTERJET_PAYLOAD_FILE,
            f"theorem {CENTERJET_COMPONENT_SOURCE_ABS_GENERATED}",
        )
        is not None
    )
    centerjet_abs_generated_present = (
        line_of_symbol(
            ROOT / CENTERJET_PAYLOAD_FILE,
            f"theorem {CENTERJET_ABS_GENERATED}",
        )
        is not None
    )
    centerjet_abs_payload_present = (
        centerjet_payload_file_present
        and centerjet_coeff_present
        and centerjet_coeff_error_abs_present
        and centerjet_coeff_error_abs_nonneg_present
        and centerjet_component_source_abs_present
        and centerjet_abs_generated_present
    )
    order16_factor_majorant_file_present = (ROOT / ORDER16_FACTOR_MAJORANT_FILE).exists()
    order16_source_eq_active_actual_present = (
        line_of_symbol(
            ROOT / ORDER16_FACTOR_MAJORANT_FILE,
            f"theorem {ORDER16_SOURCE_EQ_ACTIVE_ACTUAL}",
        )
        is not None
    )
    order16_structural_reduction_present = (
        order16_factor_majorant_file_present
        and order16_source_eq_active_actual_present
    )
    order16_factor_derivative_receiver_file_present = (
        ROOT / ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE
    ).exists()
    order16_component_product_majorant_present = (
        line_of_symbol(
            ROOT / ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE,
            f"def {ORDER16_COMPONENT_PRODUCT_MAJORANT}",
        )
        is not None
    )
    order16_component_product_abs_receiver_present = (
        line_of_symbol(
            ROOT / ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE,
            f"theorem {ORDER16_COMPONENT_PRODUCT_ABS_RECEIVER}",
        )
        is not None
    )
    order16_source_abs_receiver_present = (
        line_of_symbol(
            ROOT / ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE,
            f"theorem {ORDER16_SOURCE_ABS_RECEIVER}",
        )
        is not None
    )
    order16_source_interval_receiver_present = (
        line_of_symbol(
            ROOT / ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE,
            f"theorem {ORDER16_SOURCE_INTERVAL_RECEIVER}",
        )
        is not None
    )
    order16_factor_derivative_receiver_present = (
        order16_factor_derivative_receiver_file_present
        and order16_component_product_majorant_present
        and order16_component_product_abs_receiver_present
        and order16_source_abs_receiver_present
        and order16_source_interval_receiver_present
    )
    order16_centered_taylor_factor_majorant_bridge_present = (
        line_of_symbol(
            ROOT / ORDER16_FACTOR_DERIVATIVE_MAJORANT_BRIDGE_FILE,
            f"theorem {ORDER16_SOURCE_INTERVAL_CENTERED_TAYLOR_RECEIVER}",
        )
        is not None
    )
    order16_budget_payload_file_present = (ROOT / ORDER16_BUDGET_PAYLOAD_FILE).exists()
    order16_active_scale_abs_present = (
        line_of_symbol(
            ROOT / ORDER16_BUDGET_PAYLOAD_FILE,
            f"theorem {ORDER16_ACTIVE_SCALE_ABS}",
        )
        is not None
    )
    order16_budget_le_declared_abs_present = (
        line_of_symbol(
            ROOT / ORDER16_BUDGET_PAYLOAD_FILE,
            f"theorem {ORDER16_BUDGET_LE_DECLARED_ABS}",
        )
        is not None
    )
    order16_remainder_width_fail_rat_present = (
        line_of_symbol(
            ROOT / ORDER16_BUDGET_PAYLOAD_FILE,
            f"theorem {ORDER16_REMAINDER_WIDTH_FAIL_RAT}",
        )
        is not None
    )
    order16_remainder_width_fail_present = (
        line_of_symbol(
            ROOT / ORDER16_BUDGET_PAYLOAD_FILE,
            f"theorem {ORDER16_REMAINDER_WIDTH_FAIL}",
        )
        is not None
    )
    order16_centered_taylor_factor_route_budget_killed = (
        order16_centered_taylor_factor_majorant_bridge_present
        and order16_budget_payload_file_present
        and order16_active_scale_abs_present
        and order16_remainder_width_fail_present
    )

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": STATUS,
        "firstFailure": FIRST_FAILURE,
        "failureCodes": [
            FIRST_FAILURE,
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_TAYLOR_RECEIVER_GAP",
            NEXT_PAYLOAD_FAILURE,
            ACTIVE_ACTUAL_SINGLEABS_TO_SIGNED_FAILURE,
            ACTIVE_ACTUAL_SIGNED_FACTOR_ROWS_FAILURE,
            ACTIVE_ACTUAL_FACTOR_INTERVAL_RECEIVER_FAILURE,
            ACTIVE_ACTUAL_PRODUCT_ROWS_FAILURE,
            CENTERJET_ABS_PAYLOAD_FAILURE,
            FACTOR_DERIVATIVE_BOUNDS_FAILURE,
            FACTOR_DERIVATIVE_BUDGET_FAILURE,
            FACTOR_DERIVATIVE_BUDGET_FAILURE_ALIAS,
            ORDER16_SOURCE_INTERVAL_PAYLOAD_FAILURE,
            SOURCE_MODEL_FAILURE,
            CENTER_JET_SOURCE_MODEL_FAILURE,
            ORDER16_SOURCE_MODEL_FAILURE,
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JET_ROWS_MISSING",
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_ORDER16_ROWS_MISSING",
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_HORNER_RANGE_ROWS_MISSING",
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_TARGET_BUDGET_ROWS_MISSING",
            "STEP33_A1_SUB0_COMBINED_INTERVAL_PROOF_GRADE_SOURCE_MISSING",
            "STEP33_A1_SUB0_COMBINED_INTERVAL_LEAN_PAYLOAD_MISSING",
            "STEP33_A1_SUB0_CANCELLATION_PRESERVING_TAYLOR_REMAINDER_GAP",
        ],
        "proofStatus": {
            "isLeanProofData": False,
            "outLeanWritten": False,
            "conditionalPayloadPresent": (ROOT / CONDITIONAL_PAYLOAD_FILE).exists(),
            "conditionalPayloadIsUnconditionalProof": False,
            "highOrderSourceFilePresent": (ROOT / HIGH_ORDER_SOURCE_FILE).exists(),
            "highOrderValidPayloadPresent": False,
            "highOrderCenterJetRowsPresent": centerjet_abs_payload_present,
            "highOrderOrder16RowsPresent": False,
            "highOrderHornerRangeRowsPresent": False,
            "highOrderTargetBudgetRowsPresent": False,
            "wholeExpressionSourceModelPresent": source_model_bridge_present,
            "centerJetSourceModelPresent": source_model_center_jet_present,
            "order16SourceModelPresent": source_model_order16_present,
            "fullSourceModelBridgePresent": full_source_model_bridge_present,
            "sourceBoundsToHighOrderValidConstructorPresent": (
                source_bounds_constructor_present
            ),
            "sourceIntervalRowsToHighOrderValidConstructorPresent": (
                source_interval_constructor_present
            ),
            "sourceIntervalCertStructurePresent": (
                source_interval_cert_structure_present
            ),
            "sourceIntervalCertValidPredicatePresent": (
                source_interval_cert_valid_present
            ),
            "sourceIntervalCertToHighOrderValidPresent": (
                source_interval_cert_to_high_order_present
            ),
            "sourceIntervalCertToHCombinedPresent": (
                source_interval_cert_to_hcombined_present
            ),
            "sourceIntervalCertToResidualIntervalPresent": (
                source_interval_cert_to_residual_present
            ),
            "sourceNormalFormCancellationCauchyPresent": (
                source_normal_form_cancellation_cauchy_present
            ),
            "sourceNormalFormConditionalCenterJetPresent": (
                source_normal_form_conditional_center_jet_present
            ),
            "sourceNormalFormSupportPresent": source_normal_form_support_present,
            "sourceNormalFormResidualJetBridgePresent": (
                source_normal_form_residual_jet_bridge_present
            ),
            "sourceNormalFormNonconditionalPresent": (
                source_normal_form_nonconditional_present
            ),
            "sourceNormalFormActiveActualIntervalPresent": (
                source_normal_form_active_actual_interval_present
            ),
            "sourceNormalFormActiveActualValidConstructorPresent": (
                source_normal_form_active_actual_valid_constructor_present
            ),
            "sourceNormalFormActiveActualSourceIntervalValidPresent": (
                source_normal_form_active_actual_source_interval_valid_present
            ),
            "sourceNormalFormActiveActualInterfacePresent": (
                source_normal_form_active_actual_interface_present
            ),
            "activeActualCenterJetRowsFilePresent": (
                ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE
            ).exists(),
            "activeActualSingleAbsToSignedCenterJetCrosswalkPresent": (
                active_actual_singleabs_to_signed_present
            ),
            "activeActualShapeSqDerivSingleAbsSignedRowsPresent": (
                active_actual_shapesqderiv_singleabs_signed_present
            ),
            "activeActualShapeSqDerivRows01234567891011SignedPresent": (
                active_actual_shapesqderiv_rows_signed_present
            ),
            "activeActualOmegaPrimeSignedRowsPresent": (
                active_actual_omegaprime_signed_present
            ),
            "activeActualOmegaSignedRowsPresent": (
                active_actual_omega_signed_present
            ),
            "activeActualShapeSqSignedRowsPresent": (
                active_actual_shapesq_signed_present
            ),
            "activeActualAllFactorSignedRowsPresent": (
                active_actual_all_factor_signed_rows_present
            ),
            "activeActualFactorIntervalReceiverPresent": (
                active_actual_factor_interval_receiver_present
            ),
            "activeActualSumIntervalReceiverPresent": (
                active_actual_sum_interval_present
            ),
            "activeActualCauchyIntervalReceiverPresent": (
                active_actual_cauchy_interval_present
            ),
            "activeActualComponentProductCauchyIntervalReceiverPresent": (
                active_actual_component_product_cauchy_interval_present
            ),
            "activeActualScaleNonnegPresent": active_actual_scale_nonneg_present,
            "activeActualRowIntervalReceiverPresent": (
                active_actual_row_interval_present
            ),
            "activeActualComponentProductAbsPresent": (
                active_actual_component_product_abs_present
            ),
            "activeActualComponentProductAbsIntervalPresent": (
                active_actual_component_product_abs_interval_present
            ),
            "activeActualComponentProductAbsNonnegPresent": (
                active_actual_component_product_abs_nonneg_present
            ),
            "activeActualCenterRowLowerPresent": (
                active_actual_center_row_lower_present
            ),
            "activeActualCenterRowUpperPresent": (
                active_actual_center_row_upper_present
            ),
            "activeActualCenterRowIntervalFromFactorRowsPresent": (
                active_actual_center_row_interval_from_factor_rows_present
            ),
            "activeActualProductRowIntervalsPresent": (
                active_actual_product_row_intervals_present
            ),
            "centerJetPayloadFilePresent": centerjet_payload_file_present,
            "centerJetCoeffPresent": centerjet_coeff_present,
            "centerJetCoeffErrorAbsPresent": centerjet_coeff_error_abs_present,
            "centerJetCoeffErrorAbsNonnegPresent": (
                centerjet_coeff_error_abs_nonneg_present
            ),
            "centerJetComponentSourceAbsGeneratedPresent": (
                centerjet_component_source_abs_present
            ),
            "centerJetAbsGeneratedPresent": centerjet_abs_generated_present,
            "centerJetAbsPayloadPresent": centerjet_abs_payload_present,
            "order16FactorMajorantFilePresent": (
                order16_factor_majorant_file_present
            ),
            "order16SourceEqActiveActualPresent": (
                order16_source_eq_active_actual_present
            ),
            "order16StructuralReductionPresent": (
                order16_structural_reduction_present
            ),
            "order16FactorDerivativeReceiverFilePresent": (
                order16_factor_derivative_receiver_file_present
            ),
            "order16ComponentProductMajorantPresent": (
                order16_component_product_majorant_present
            ),
            "order16ComponentProductAbsReceiverPresent": (
                order16_component_product_abs_receiver_present
            ),
            "order16SourceAbsReceiverPresent": (
                order16_source_abs_receiver_present
            ),
            "order16SourceIntervalReceiverPresent": (
                order16_source_interval_receiver_present
            ),
            "order16FactorDerivativeReceiverPresent": (
                order16_factor_derivative_receiver_present
            ),
            "order16CenteredTaylorFactorMajorantBridgePresent": (
                order16_centered_taylor_factor_majorant_bridge_present
            ),
            "order16BudgetPayloadFilePresent": order16_budget_payload_file_present,
            "order16ActiveScaleAbsPresent": order16_active_scale_abs_present,
            "order16BudgetLeDeclaredAbsPresent": (
                order16_budget_le_declared_abs_present
            ),
            "order16RemainderWidthFailRatPresent": (
                order16_remainder_width_fail_rat_present
            ),
            "order16RemainderWidthFailPresent": (
                order16_remainder_width_fail_present
            ),
            "order16CenteredTaylorFactorRouteBudgetKilled": (
                order16_centered_taylor_factor_route_budget_killed
            ),
            "sourceIntervalCertPayloadPresent": False,
            "omegaPrimePayloadReusableForWholeExpression": False,
            "residualTaylorCoeffPayloadPresent": (
                ROOT / COMPONENT_ASSEMBLY_PAYLOAD_FILE
            ).exists(),
            "componentAssemblyLedgerPresent": (ROOT / COMPONENT_ASSEMBLY_LEDGER).exists(),
            "proofSafeClosedFields": 0,
            "combinedReceiverCheckedInLean": True,
            "combinedExpressionDefinedInLean": True,
            "combinedIntervalTheoremCheckedInLean": True,
            "proofGradeCombinedBoundsPresent": False,
            "sampledCandidateIsProof": False,
            "segmentCoveragePassedExactRational": coverage[
                "coveragePassedExactRational"
            ],
            "allSegmentsBudgetPassedExactRational": budget_passed,
            "allSegmentsProofGrade": proof_grade_segments,
        },
        "cell": {
            "cellL": CELL_L,
            "cellU": CELL_U,
            "targetLower": TARGET_LOWER,
            "targetUpper": TARGET_UPPER,
            "targetWidth": rat_text(target_width),
        },
        "targetLeanSurface": {
            "file": COMBINED_FILE,
            "certCheckerFile": CERT_CHECKER_FILE,
            "conditionalPayloadFile": CONDITIONAL_PAYLOAD_FILE,
            "highOrderSourceFile": HIGH_ORDER_SOURCE_FILE,
            "sourceModelBridgeFile": SOURCE_MODEL_BRIDGE_FILE,
            "sourceModelOrder16Source": SOURCE_MODEL_ORDER16_DEF,
            "sourceModelOrder16Theorem": SOURCE_MODEL_ORDER16_THEOREM,
            "sourceModelOrder16BoundAdapter": SOURCE_MODEL_ORDER16_BOUND_THEOREM,
            "sourceModelCenterJetBoundsAdapter": SOURCE_MODEL_CENTER_JET_BOUNDS_THEOREM,
            "sourceModelHighOrderValidConstructor": SOURCE_MODEL_HIGH_ORDER_VALID_CONSTRUCTOR,
            "sourceModelHighOrderIntervalConstructor": (
                SOURCE_MODEL_HIGH_ORDER_INTERVAL_CONSTRUCTOR
            ),
            "sourceIntervalCertFile": SOURCE_INTERVAL_CERT_FILE,
            "sourceIntervalCertStructure": SOURCE_INTERVAL_CERT_STRUCTURE,
            "sourceIntervalCertValidPredicate": SOURCE_INTERVAL_CERT_VALID,
            "sourceIntervalCertToHighOrderValid": SOURCE_INTERVAL_CERT_TO_HIGH_ORDER,
            "sourceIntervalCertToHCombined": SOURCE_INTERVAL_CERT_TO_HCOMBINED,
            "sourceIntervalCertToResidualInterval": SOURCE_INTERVAL_CERT_TO_RESIDUAL,
            "sourceNormalFormFile": SOURCE_NORMAL_FORM_FILE,
            "sourceNormalFormCancellationCauchy": SOURCE_NORMAL_FORM_CANCELLATION_CAUCHY,
            "sourceNormalFormConditionalCenterJet": (
                SOURCE_NORMAL_FORM_CONDITIONAL_CENTER_JET
            ),
            "sourceNormalFormResidualJetBridge": SOURCE_NORMAL_FORM_RESIDUAL_JET_BRIDGE,
            "sourceNormalFormNonconditionalCenterJet": (
                SOURCE_NORMAL_FORM_NONCONDITIONAL_CENTER_JET
            ),
            "sourceNormalFormActiveActualInterval": (
                SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_INTERVAL
            ),
            "sourceNormalFormActiveActualValidConstructor": (
                SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_VALID_CONSTRUCTOR
            ),
            "sourceNormalFormActiveActualSourceIntervalValid": (
                SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_SOURCE_INTERVAL_VALID
            ),
            "activeActualCenterJetRowsFile": ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
            "activeActualCenterJetIntervalOfAbs": (
                ACTIVE_ACTUAL_CENTERJET_INTERVAL_OF_ABS
            ),
            "activeActualShapeSqDerivSingleAbsSigned": (
                ACTIVE_ACTUAL_SHAPESQDERIV_SINGLEABS_SIGNED
            ),
            "activeActualShapeSqDerivRows01234567891011Signed": (
                ACTIVE_ACTUAL_SHAPESQDERIV_ROWS_SIGNED
            ),
            "activeActualOmegaPrimeSignedRows": ACTIVE_ACTUAL_OMEGAPRIME_SIGNED,
            "activeActualOmegaSignedRows": ACTIVE_ACTUAL_OMEGA_SIGNED,
            "activeActualShapeSqSignedRows": ACTIVE_ACTUAL_SHAPESQ_SIGNED,
            "activeActualSumIntervalReceiver": ACTIVE_ACTUAL_SUM_INTERVAL,
            "activeActualCauchyIntervalReceiver": ACTIVE_ACTUAL_CAUCHY_INTERVAL,
            "activeActualComponentProductCauchyIntervalReceiver": (
                ACTIVE_ACTUAL_COMPONENT_PRODUCT_CAUCHY_INTERVAL
            ),
            "activeActualScaleNonneg": ACTIVE_ACTUAL_SCALE_NONNEG,
            "activeActualRowIntervalReceiver": ACTIVE_ACTUAL_ROW_INTERVAL,
            "activeActualComponentProductAbs": ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS,
            "activeActualComponentProductAbsInterval": (
                ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_INTERVAL
            ),
            "activeActualComponentProductAbsNonneg": (
                ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_NONNEG
            ),
            "activeActualCenterRowLower": ACTIVE_ACTUAL_CENTER_ROW_LOWER,
            "activeActualCenterRowUpper": ACTIVE_ACTUAL_CENTER_ROW_UPPER,
            "activeActualCenterRowIntervalFromFactorRows": (
                ACTIVE_ACTUAL_CENTER_ROW_INTERVAL_FROM_FACTOR_ROWS
            ),
            "centerJetPayloadFile": CENTERJET_PAYLOAD_FILE,
            "centerJetCoeff": CENTERJET_COEFF,
            "centerJetCoeffErrorAbs": CENTERJET_COEFF_ERROR_ABS,
            "centerJetCoeffErrorAbsNonneg": CENTERJET_COEFF_ERROR_ABS_NONNEG,
            "centerJetComponentSourceAbsGenerated": (
                CENTERJET_COMPONENT_SOURCE_ABS_GENERATED
            ),
            "centerJetAbsGenerated": CENTERJET_ABS_GENERATED,
            "order16FactorMajorantFile": ORDER16_FACTOR_MAJORANT_FILE,
            "order16SourceEqActiveActual": ORDER16_SOURCE_EQ_ACTIVE_ACTUAL,
            "order16FactorDerivativeReceiverFile": (
                ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE
            ),
            "order16FactorDerivativeMajorantBridgeFile": (
                ORDER16_FACTOR_DERIVATIVE_MAJORANT_BRIDGE_FILE
            ),
            "order16BudgetPayloadFile": ORDER16_BUDGET_PAYLOAD_FILE,
            "order16ComponentProductMajorant": ORDER16_COMPONENT_PRODUCT_MAJORANT,
            "order16ComponentProductAbsReceiver": (
                ORDER16_COMPONENT_PRODUCT_ABS_RECEIVER
            ),
            "order16SourceAbsReceiver": ORDER16_SOURCE_ABS_RECEIVER,
            "order16SourceIntervalReceiver": ORDER16_SOURCE_INTERVAL_RECEIVER,
            "certStructure": "Step33Sub0CombinedCancellationIntervalCert",
            "certValidPredicate": "Step33Sub0CombinedCancellationIntervalCert.Valid",
            "certToHCombined": "Step33Sub0CombinedCancellationIntervalCert.Valid.to_hCombined",
            "highOrderCertStructure": HIGH_ORDER_CERT_STRUCTURE,
            "highOrderValidPredicate": HIGH_ORDER_VALID,
            "highOrderRemainderTheorem": HIGH_ORDER_REMAINDER,
            "highOrderToIntervalTheorem": HIGH_ORDER_TO_INTERVAL,
            "highOrderToHCombinedTheorem": HIGH_ORDER_TO_HCOMBINED,
            "highOrderToResidualTheorem": HIGH_ORDER_TO_RESIDUAL,
            "highOrderReceiverTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_remainder_bound_of_centerJet15_order16"
            ),
            "highOrderAliasTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerTaylor15_remainder_of_order16"
            ),
            "conditionalRemainderProp": (
                "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp"
            ),
            "conditionalPayloadTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_remainder_bound"
            ),
            "conditionalHCombinedTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_hCombined_of_remainder_bound"
            ),
            "expression": TARGET_EXPR,
            "consumerTheorem": TARGET_THEOREM,
            "closedFormTheorem": TARGET_CLOSED_FORM_THEOREM,
            "proofDataWrapper": TARGET_PROOF_DATA,
            "boundInputsFile": BOUND_INPUTS_FILE,
            "normReceiverFile": NORM_RECEIVER_FILE,
            "p45BridgeFile": P45_BRIDGE_FILE,
            "landingFile": LANDING_FILE,
        },
        "targetStatement": (
            "forall eta in Set.Icc (0 : Real) ((1 : Real) / 10), "
            f"({TARGET_LOWER}) <= {TARGET_EXPR} eta and "
            f"{TARGET_EXPR} eta <= ({TARGET_UPPER})"
        ),
        "combinedExpressionMeaning": (
            "rawOmegaATaylorPolynomial assembledDegree 1/20 ResidualTaylorCoeff eta "
            "+ ScaledCancellationRhs eta"
        ),
        "requiredCertificate": {
            "kind": "proof_grade_high_order_taylor_and_horner_payload",
            "mustProve": (
                "a concrete Step33Sub0CombinedCancellationSourceIntervalCert.Valid "
                "payload plus Horner range and target-budget inequalities"
            ),
            "mayUse": [
                "rational interval arithmetic",
                "Lean-verifiable matrix/free polynomial interval certificate",
                "independently checkable generated rational output",
            ],
            "mustNotUse": [
                "sampled JSON as proof",
                "separate norm bounds for residualTaylor polynomial and ScaledCancellationRhs",
                "independent raw/poly interval subtraction",
                "product-budget rows route after width-fail",
            ],
        },
        "requiredHighOrderPayload": {
            "certStructure": HIGH_ORDER_CERT_STRUCTURE,
            "validPredicate": HIGH_ORDER_VALID,
            "mustProvide": [
                "smooth proof for primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr",
                "coeff : Fin 16 -> Rat",
                "coeffErrorAbs : Fin 16 -> Rat",
                "coeffErrorNonneg proof",
                "remainderNonneg proof",
                "centerJet rows j = 0..15 at center 1/20",
                "component-source centerJet lower/upper rows j = 0..15",
                "uniform order16Abs on Set.Icc 0 (1/10)",
                "component-source order16 lower/upper rows on Set.Icc 0 (1/10)",
                "remainderBudget proof",
                "polyLower and polyUpper for the degree-15 polynomial",
                "Step33Sub0CombinedCancellationHornerRangeCert.Valid",
                "target lower budget proof",
                "target upper budget proof",
            ],
            "adapterChain": [
                SOURCE_INTERVAL_CERT_TO_HIGH_ORDER,
                SOURCE_INTERVAL_CERT_TO_HCOMBINED,
                SOURCE_INTERVAL_CERT_TO_RESIDUAL,
                SOURCE_MODEL_HIGH_ORDER_INTERVAL_CONSTRUCTOR,
                SOURCE_MODEL_HIGH_ORDER_VALID_CONSTRUCTOR,
                HIGH_ORDER_REMAINDER,
                HIGH_ORDER_TO_INTERVAL,
                HIGH_ORDER_TO_HCOMBINED,
                HIGH_ORDER_TO_RESIDUAL,
            ],
        },
        "sourceModelInventory": {
            "status": (
                "source_interval_cert_target_checked_payload_missing"
                if source_interval_cert_target_present
                else
                "source_interval_rows_to_valid_constructor_checked_payload_rows_missing"
                if source_interval_constructor_present
                else
                "source_bounds_to_valid_constructor_checked_payload_rows_missing"
                if source_bounds_constructor_present
                else "source_model_bridge_checked_payload_rows_missing"
                if full_source_model_bridge_present
                else "center_jet_source_model_checked_order16_source_missing"
                if source_model_bridge_present
                else "fail_closed_source_model_gap"
            ),
            "firstSourceFailure": (
                NEXT_PAYLOAD_FAILURE
                if full_source_model_bridge_present
                else ORDER16_SOURCE_MODEL_FAILURE
                if source_model_bridge_present
                else SOURCE_MODEL_FAILURE
            ),
            "centerJetFailure": (
                None
                if source_model_center_jet_present
                else CENTER_JET_SOURCE_MODEL_FAILURE
            ),
            "order16Failure": (
                None if source_model_order16_present else ORDER16_SOURCE_MODEL_FAILURE
            ),
            "sourceIntervalCertTarget": {
                "file": SOURCE_INTERVAL_CERT_FILE,
                "structure": symbol_ref_lookup(
                    SOURCE_INTERVAL_CERT_FILE,
                    SOURCE_INTERVAL_CERT_STRUCTURE,
                    f"structure {SOURCE_INTERVAL_CERT_STRUCTURE}",
                ),
                "validPredicate": symbol_ref_lookup(
                    SOURCE_INTERVAL_CERT_FILE,
                    SOURCE_INTERVAL_CERT_VALID,
                    "structure Valid",
                ),
                "toHighOrderValid": symbol_ref_lookup(
                    SOURCE_INTERVAL_CERT_FILE,
                    SOURCE_INTERVAL_CERT_TO_HIGH_ORDER,
                    "theorem to_highOrderValid",
                ),
                "toHCombined": symbol_ref_lookup(
                    SOURCE_INTERVAL_CERT_FILE,
                    SOURCE_INTERVAL_CERT_TO_HCOMBINED,
                    "theorem to_hCombined",
                ),
                "toResidualInterval": symbol_ref_lookup(
                    SOURCE_INTERVAL_CERT_FILE,
                    SOURCE_INTERVAL_CERT_TO_RESIDUAL,
                    "theorem to_fullTaylor_residual_deriv_interval",
                ),
                "structurePresent": source_interval_cert_structure_present,
                "validPredicatePresent": source_interval_cert_valid_present,
                "toHighOrderValidPresent": source_interval_cert_to_high_order_present,
                "toHCombinedPresent": source_interval_cert_to_hcombined_present,
                "toResidualIntervalPresent": source_interval_cert_to_residual_present,
                "targetPresent": source_interval_cert_target_present,
                "payloadPresent": False,
                "status": (
                    "checked_target_payload_missing"
                    if source_interval_cert_target_present
                    else "missing_or_incomplete"
                ),
                "whyNotEnough": (
                    "This packages the component-source lower/upper row "
                    "obligations into a Lean-checked certificate target and "
                    "routes any Valid payload to HighOrderTaylorCert.Valid and "
                    "the final residual-derivative interval receiver. It does "
                    "not emit concrete lower/upper rows, Horner rows, "
                    "target-budget rows, or a Valid payload."
                ),
            },
            "sourceNormalFormSupport": {
                "file": SOURCE_NORMAL_FORM_FILE,
                "cancellationResidualCauchy": symbol_ref_lookup(
                    SOURCE_NORMAL_FORM_FILE,
                    SOURCE_NORMAL_FORM_CANCELLATION_CAUCHY,
                    f"theorem {SOURCE_NORMAL_FORM_CANCELLATION_CAUCHY}",
                ),
                "conditionalCenterJetNormalForm": symbol_ref_lookup(
                    SOURCE_NORMAL_FORM_FILE,
                    SOURCE_NORMAL_FORM_CONDITIONAL_CENTER_JET,
                    f"theorem {SOURCE_NORMAL_FORM_CONDITIONAL_CENTER_JET}",
                ),
                "residualJetBridge": symbol_ref_lookup(
                    SOURCE_NORMAL_FORM_FILE,
                    SOURCE_NORMAL_FORM_RESIDUAL_JET_BRIDGE,
                    f"theorem {SOURCE_NORMAL_FORM_RESIDUAL_JET_BRIDGE}",
                ),
                "nonconditionalCenterJetNormalForm": symbol_ref_lookup(
                    SOURCE_NORMAL_FORM_FILE,
                    SOURCE_NORMAL_FORM_NONCONDITIONAL_CENTER_JET,
                    f"theorem {SOURCE_NORMAL_FORM_NONCONDITIONAL_CENTER_JET}",
                ),
                "activeActualIntervalAdapter": symbol_ref_lookup(
                    SOURCE_NORMAL_FORM_FILE,
                    SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_INTERVAL,
                    f"theorem {SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_INTERVAL}",
                ),
                "activeActualValidConstructor": symbol_ref_lookup(
                    SOURCE_NORMAL_FORM_FILE,
                    SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_VALID_CONSTRUCTOR,
                    f"theorem {SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_VALID_CONSTRUCTOR}",
                ),
                "activeActualSourceIntervalValid": symbol_ref_lookup(
                    SOURCE_NORMAL_FORM_FILE,
                    SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_SOURCE_INTERVAL_VALID,
                    f"theorem {SOURCE_NORMAL_FORM_ACTIVE_ACTUAL_SOURCE_INTERVAL_VALID}",
                ),
                "supportPresent": source_normal_form_support_present,
                "residualJetBridgePresent": (
                    source_normal_form_residual_jet_bridge_present
                ),
                "nonconditionalNormalFormPresent": (
                    source_normal_form_nonconditional_present
                ),
                "activeActualInterfacePresent": (
                    source_normal_form_active_actual_interface_present
                ),
                "status": (
                    "checked_nonconditional_normal_form_payload_missing"
                    if source_normal_form_complete_present
                    else (
                        "checked_conditional_residual_jet_bridge_missing"
                        if source_normal_form_support_present
                        else "missing_or_incomplete"
                    )
                ),
                "firstFailure": (
                    NEXT_PAYLOAD_FAILURE
                    if source_normal_form_complete_present
                    else SOURCE_NORMAL_FORM_COEFF_ALIGNMENT_FAILURE
                ),
                "missingBridge": (
                    None
                    if source_normal_form_complete_present
                    else (
                        "prove the residual Taylor center-jet coefficient "
                        "alignment: for every j : Fin 16, "
                        "NormalizedCenterJet ResidualTaylorPoly j.1 equals "
                        "NominalScaleCoeff * ComponentProductNominalCauchyCenterJet "
                        "j.1 minus ResidualDerivmodelCoeff j"
                    )
                ),
                "whyNotEnough": (
                    "The residual Taylor center-jet alignment bridge and "
                    "nonconditional active-actual normal form are now "
                    "Lean-checked, including a generator-facing active-actual "
                    "interval adapter and source-interval Valid constructor. "
                    "This is still not a generated source interval payload: "
                    "concrete lower/upper rows, Horner rows, target-budget "
                    "rows, and a Valid payload are still missing."
                    if source_normal_form_complete_present
                    else (
                        "This proves the cancellation-residual Cauchy rows equal "
                        "actual Cauchy rows minus nominal Cauchy rows, and proves "
                        "the combined source active-actual normal form only under "
                        "the explicit residual-jet alignment hypothesis. It does "
                        "not prove the coefficient extraction bridge from "
                        "rawOmegaATaylorPolynomial coefficients to normalized "
                        "center jets, so it is not the nonconditional normal form "
                        "and cannot feed a generated payload yet."
                    )
                ),
            },
            "activeActualFactorRowsBridge": {
                "file": ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                "intervalOfAbs": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_CENTERJET_INTERVAL_OF_ABS,
                    f"theorem {ACTIVE_ACTUAL_CENTERJET_INTERVAL_OF_ABS}",
                ),
                "shapeSqDerivSingleAbsSigned": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_SHAPESQDERIV_SINGLEABS_SIGNED,
                    f"theorem {ACTIVE_ACTUAL_SHAPESQDERIV_SINGLEABS_SIGNED}",
                ),
                "shapeSqDerivRows01234567891011Signed": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_SHAPESQDERIV_ROWS_SIGNED,
                    f"theorem {ACTIVE_ACTUAL_SHAPESQDERIV_ROWS_SIGNED}",
                ),
                "omegaPrimeSignedRows": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_OMEGAPRIME_SIGNED,
                    f"theorem {ACTIVE_ACTUAL_OMEGAPRIME_SIGNED}",
                ),
                "omegaSignedRows": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_OMEGA_SIGNED,
                    f"theorem {ACTIVE_ACTUAL_OMEGA_SIGNED}",
                ),
                "shapeSqSignedRows": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_SHAPESQ_SIGNED,
                    f"theorem {ACTIVE_ACTUAL_SHAPESQ_SIGNED}",
                ),
                "sumIntervalReceiver": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_SUM_INTERVAL,
                    f"theorem {ACTIVE_ACTUAL_SUM_INTERVAL}",
                ),
                "cauchyIntervalReceiver": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_CAUCHY_INTERVAL,
                    f"theorem {ACTIVE_ACTUAL_CAUCHY_INTERVAL}",
                ),
                "componentProductCauchyIntervalReceiver": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_COMPONENT_PRODUCT_CAUCHY_INTERVAL,
                    f"theorem {ACTIVE_ACTUAL_COMPONENT_PRODUCT_CAUCHY_INTERVAL}",
                ),
                "activeScaleNonneg": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_SCALE_NONNEG,
                    f"theorem {ACTIVE_ACTUAL_SCALE_NONNEG}",
                ),
                "activeActualRowIntervalReceiver": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_ROW_INTERVAL,
                    f"theorem {ACTIVE_ACTUAL_ROW_INTERVAL}",
                ),
                "componentProductAbs": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS,
                    f"def {ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS}",
                ),
                "componentProductAbsInterval": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_INTERVAL,
                    f"theorem {ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_INTERVAL}",
                ),
                "componentProductAbsNonneg": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_NONNEG,
                    f"theorem {ACTIVE_ACTUAL_COMPONENT_PRODUCT_ABS_NONNEG}",
                ),
                "activeActualCenterRowLower": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_CENTER_ROW_LOWER,
                    f"def {ACTIVE_ACTUAL_CENTER_ROW_LOWER}",
                ),
                "activeActualCenterRowUpper": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_CENTER_ROW_UPPER,
                    f"def {ACTIVE_ACTUAL_CENTER_ROW_UPPER}",
                ),
                "activeActualCenterRowIntervalFromFactorRows": symbol_ref_lookup(
                    ACTIVE_ACTUAL_CENTERJET_ROWS_FILE,
                    ACTIVE_ACTUAL_CENTER_ROW_INTERVAL_FROM_FACTOR_ROWS,
                    f"theorem {ACTIVE_ACTUAL_CENTER_ROW_INTERVAL_FROM_FACTOR_ROWS}",
                ),
                "singleAbsToSignedPresent": active_actual_singleabs_to_signed_present,
                "omegaPrimeSignedRowsPresent": active_actual_omegaprime_signed_present,
                "omegaSignedRowsPresent": active_actual_omega_signed_present,
                "shapeSqSignedRowsPresent": active_actual_shapesq_signed_present,
                "allFactorSignedRowsPresent": (
                    active_actual_all_factor_signed_rows_present
                ),
                "factorIntervalReceiverPresent": (
                    active_actual_factor_interval_receiver_present
                ),
                "componentProductAbsPresent": (
                    active_actual_component_product_abs_present
                ),
                "componentProductAbsIntervalPresent": (
                    active_actual_component_product_abs_interval_present
                ),
                "componentProductAbsNonnegPresent": (
                    active_actual_component_product_abs_nonneg_present
                ),
                "activeActualCenterRowLowerPresent": (
                    active_actual_center_row_lower_present
                ),
                "activeActualCenterRowUpperPresent": (
                    active_actual_center_row_upper_present
                ),
                "activeActualCenterRowIntervalFromFactorRowsPresent": (
                    active_actual_center_row_interval_from_factor_rows_present
                ),
                "activeActualProductRowIntervalsPresent": (
                    active_actual_product_row_intervals_present
                ),
                "closedFailure": (
                    ACTIVE_ACTUAL_SINGLEABS_TO_SIGNED_FAILURE
                    if active_actual_singleabs_to_signed_present
                    else None
                ),
                "closedFactorRowsFailure": (
                    ACTIVE_ACTUAL_SIGNED_FACTOR_ROWS_FAILURE
                    if active_actual_all_factor_signed_rows_present
                    else None
                ),
                "closedReceiverFailure": (
                    ACTIVE_ACTUAL_FACTOR_INTERVAL_RECEIVER_FAILURE
                    if active_actual_factor_interval_receiver_present
                    else None
                ),
                "closedProductRowsFailure": (
                    ACTIVE_ACTUAL_PRODUCT_ROWS_FAILURE
                    if active_actual_product_row_intervals_present
                    else None
                ),
                "status": (
                    "checked_factor_signed_rows_active_actual_product_rows_and_receiver"
                    if (
                        active_actual_all_factor_signed_rows_present
                        and active_actual_product_row_intervals_present
                        and active_actual_factor_interval_receiver_present
                    )
                    else "checked_factor_signed_rows_and_active_actual_row_receiver"
                    if (
                        active_actual_all_factor_signed_rows_present
                        and active_actual_factor_interval_receiver_present
                    )
                    else "checked_factor_interval_to_active_actual_row_receiver"
                    if active_actual_factor_interval_receiver_present
                    else "checked_factor_signed_rows"
                    if active_actual_all_factor_signed_rows_present
                    else "checked_shapesqderiv_singleabs_to_signed_rows"
                    if active_actual_singleabs_to_signed_present
                    else "missing_or_incomplete"
                ),
                "whyNotEnough": (
                    "Lean now has proof-grade signed center-jet intervals for "
                    "OmegaPrimeActual, OmegaActual, ShapeSqActual, and "
                    "ShapeSqDerivActual, a receiver from termwise "
                    "factor-product intervals through Cauchy convolution, "
                    "activeScale, and ResidualDerivmodelCoeff subtraction to "
                    "the active-actual row premise, and concrete rational "
                    "active-actual center-row lower/upper definitions with a "
                    "checked row interval proof. This still does not "
                    "instantiate SourceIntervalCert.Valid: highOrderData, "
                    "coeffErrorBudget/remainderBudget, order16 source "
                    "interval, Horner range, and target-budget rows are still "
                    "missing."
                ),
                "nextFailure": NEXT_PAYLOAD_FAILURE,
            },
            "centerJetPayload": {
                "file": CENTERJET_PAYLOAD_FILE,
                "coeff": symbol_ref_lookup(
                    CENTERJET_PAYLOAD_FILE,
                    CENTERJET_COEFF,
                    f"def {CENTERJET_COEFF}",
                ),
                "coeffErrorAbs": symbol_ref_lookup(
                    CENTERJET_PAYLOAD_FILE,
                    CENTERJET_COEFF_ERROR_ABS,
                    f"def {CENTERJET_COEFF_ERROR_ABS}",
                ),
                "coeffErrorAbsNonneg": symbol_ref_lookup(
                    CENTERJET_PAYLOAD_FILE,
                    CENTERJET_COEFF_ERROR_ABS_NONNEG,
                    f"theorem {CENTERJET_COEFF_ERROR_ABS_NONNEG}",
                ),
                "componentSourceAbsGenerated": symbol_ref_lookup(
                    CENTERJET_PAYLOAD_FILE,
                    CENTERJET_COMPONENT_SOURCE_ABS_GENERATED,
                    f"theorem {CENTERJET_COMPONENT_SOURCE_ABS_GENERATED}",
                ),
                "centerJetAbsGenerated": symbol_ref_lookup(
                    CENTERJET_PAYLOAD_FILE,
                    CENTERJET_ABS_GENERATED,
                    f"theorem {CENTERJET_ABS_GENERATED}",
                ),
                "payloadPresent": centerjet_abs_payload_present,
                "closedFailure": (
                    CENTERJET_ABS_PAYLOAD_FAILURE
                    if centerjet_abs_payload_present
                    else None
                ),
                "status": (
                    "checked_signed_rows_to_midpoint_error_centerjet_abs_payload"
                    if centerjet_abs_payload_present
                    else "missing_or_incomplete"
                ),
                "whyNotEnough": (
                    "This provides coeff and coeffErrorAbs from the active-actual "
                    "lower/upper rows and proves the high-order center-jet abs "
                    "rows for the whole combined expression. It still does not "
                    "provide the order16 source interval, Horner rows, "
                    "target-budget rows, or SourceIntervalCert.Valid."
                ),
                "nextFailure": ORDER16_SOURCE_INTERVAL_PAYLOAD_FAILURE,
            },
            "checkedBridge": {
                "file": SOURCE_MODEL_BRIDGE_FILE,
                "smoothTheorem": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_SMOOTH_THEOREM
                ),
                "centerJetTheorem": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_CENTER_JET_THEOREM
                ),
                "order16Source": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_ORDER16_DEF
                ),
                "order16Theorem": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_ORDER16_THEOREM
                ),
                "order16BoundAdapter": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_ORDER16_BOUND_THEOREM
                ),
                "order16StructuralReduction": symbol_ref(
                    ORDER16_FACTOR_MAJORANT_FILE, ORDER16_SOURCE_EQ_ACTIVE_ACTUAL
                ),
                "order16FactorDerivativeReceiverFile": (
                    ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE
                ),
                "order16FactorDerivativeMajorantBridgeFile": (
                    ORDER16_FACTOR_DERIVATIVE_MAJORANT_BRIDGE_FILE
                ),
                "order16BudgetPayloadFile": ORDER16_BUDGET_PAYLOAD_FILE,
                "order16ComponentProductMajorant": symbol_ref(
                    ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE,
                    ORDER16_COMPONENT_PRODUCT_MAJORANT,
                ),
                "order16ComponentProductAbsReceiver": symbol_ref(
                    ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE,
                    ORDER16_COMPONENT_PRODUCT_ABS_RECEIVER,
                ),
                "order16SourceAbsReceiver": symbol_ref(
                    ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE,
                    ORDER16_SOURCE_ABS_RECEIVER,
                ),
                "order16SourceIntervalReceiver": symbol_ref(
                    ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE,
                    ORDER16_SOURCE_INTERVAL_RECEIVER,
                ),
                "order16CenteredTaylorFactorMajorantsReceiver": symbol_ref(
                    ORDER16_FACTOR_DERIVATIVE_MAJORANT_BRIDGE_FILE,
                    ORDER16_SOURCE_INTERVAL_CENTERED_TAYLOR_RECEIVER,
                ),
                "order16ActiveScaleAbs": symbol_ref(
                    ORDER16_BUDGET_PAYLOAD_FILE,
                    ORDER16_ACTIVE_SCALE_ABS,
                ),
                "order16BudgetLeDeclaredAbs": symbol_ref(
                    ORDER16_BUDGET_PAYLOAD_FILE,
                    ORDER16_BUDGET_LE_DECLARED_ABS,
                ),
                "order16RemainderWidthFailRat": symbol_ref(
                    ORDER16_BUDGET_PAYLOAD_FILE,
                    ORDER16_REMAINDER_WIDTH_FAIL_RAT,
                ),
                "order16RemainderWidthFail": symbol_ref(
                    ORDER16_BUDGET_PAYLOAD_FILE,
                    ORDER16_REMAINDER_WIDTH_FAIL,
                ),
                "centerJetBoundsAdapter": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_CENTER_JET_BOUNDS_THEOREM
                ),
                "highOrderValidConstructor": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_HIGH_ORDER_VALID_CONSTRUCTOR
                ),
                "highOrderIntervalConstructor": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE,
                    SOURCE_MODEL_HIGH_ORDER_INTERVAL_CONSTRUCTOR,
                ),
                "smoothPresent": source_model_smooth_present,
                "centerJetPresent": source_model_center_jet_present,
                "order16Present": source_model_order16_present,
                "order16StructuralReductionPresent": (
                    order16_structural_reduction_present
                ),
                "order16FactorDerivativeReceiverPresent": (
                    order16_factor_derivative_receiver_present
                ),
                "order16CenteredTaylorFactorMajorantBridgePresent": (
                    order16_centered_taylor_factor_majorant_bridge_present
                ),
                "order16CenteredTaylorFactorRouteBudgetKilled": (
                    order16_centered_taylor_factor_route_budget_killed
                ),
                "order16CenteredTaylorFactorBudgetFailure": (
                    FACTOR_DERIVATIVE_BUDGET_FAILURE
                    if order16_centered_taylor_factor_route_budget_killed
                    else None
                ),
                "sourceBoundsConstructorPresent": source_bounds_constructor_present,
                "sourceIntervalConstructorPresent": source_interval_constructor_present,
                "status": (
                    "checked_centered_taylor_factor_route_budget_killed"
                    if order16_centered_taylor_factor_route_budget_killed
                    else
                    "checked_order16_factor_derivative_receiver_payload_missing"
                    if order16_factor_derivative_receiver_present
                    else
                    "checked_source_interval_rows_to_valid_constructor"
                    if source_interval_constructor_present
                    else
                    "checked_source_bounds_to_valid_constructor"
                    if source_bounds_constructor_present
                    else "checked_source_model_support"
                    if full_source_model_bridge_present
                    else "checked_center_jet_support_order16_missing"
                    if source_model_bridge_present
                    else "missing_or_incomplete"
                ),
                "whyNotEnough": (
                    "This proves the whole-expression smooth bridge, all-row "
                    "component-source center-jet crosswalk, and an exact "
                    "order-16 source-model/norm adapter, plus the constructor "
                    "from source-bounds to HighOrderTaylorCert.Valid and the "
                    "interval-row constructor for component-source rows. The "
                    "nonconditional source normal form is also checked, and "
                    "the order-16 component source structurally reduces to "
                    "activeScale times the actual component-product order-16 "
                    "derivative. A separate checked receiver now shows that "
                    "proof-grade factor derivative bounds through order 16 "
                    "would feed a signed order16 source interval. It still "
                    "does not emit rational coeff rows, concrete factor "
                    "derivative bounds, a proof-grade order16Abs source bound, "
                    "Horner range rows, target-budget rows, or a concrete "
                    "Valid payload."
                ),
                "budgetKillMeaning": (
                    "The centered-Taylor factor-majorant bridge now supplies the "
                    "four uniform factor-derivative families and an adapter to "
                    "a signed order16 source interval, but the existing exact "
                    "budget audit proves this route is too wide for the current "
                    "combined-cancellation half-width. It is therefore a checked "
                    "kill certificate/pattern, not the current closure route."
                ),
            },
            "targetFunction": {
                "meaning": (
                    "whole expression, not a component: residualTaylor degree-45 "
                    "polynomial plus ScaledCancellationRhs"
                ),
                "definition": symbol_ref(COMBINED_FILE, TARGET_EXPR),
                "formula": (
                    "rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) "
                    "ResidualTaylorCoeff eta + ScaledCancellationRhs eta"
                ),
            },
            "rationalPolynomialPart": {
                "status": "present_but_not_sufficient",
                "degree": 45,
                "definition": symbol_ref(
                    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean",
                    "def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff",
                ),
                "payload": symbol_ref(
                    COMPONENT_ASSEMBLY_PAYLOAD_FILE,
                    "def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffPayload",
                ),
                "payloadEquality": symbol_ref(
                    COMPONENT_ASSEMBLY_PAYLOAD_FILE,
                    "theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylorCoeff_payload_eq",
                ),
                "whyNotEnough": (
                    "This materializes the algebraic residual polynomial, but "
                    "the high-order Valid object needs center jets and a uniform "
                    "16th-derivative bound for the whole combined expression."
                ),
            },
            "scaledCancellationRhs": {
                "status": (
                    "source_model_checked_for_center_jets_and_order16"
                    if source_model_order16_present
                    else "source_model_checked_for_center_jets"
                    if source_model_center_jet_present
                    else "source_model_missing"
                ),
                "definition": symbol_ref(
                    NORM_RECEIVER_FILE,
                    "def primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs",
                ),
                "activeScale": symbol_ref(
                    NORM_RECEIVER_FILE,
                    "def primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff",
                ),
                "formula": (
                    "ActiveScaleCoeff * ComponentProductCancellationResidual "
                    "+ (ActiveScaleCoeff - NominalScaleCoeff) * ComponentProductNominal"
                ),
                "normalizationHazard": (
                    "ActiveScaleCoeff is ((3/10)/Real.pi), while the residual "
                    "polynomial payload is rational and nominal-scale based."
                ),
                "missing": [
                    "concrete rational center-jet rows j=0..15 for the combined expression",
                    "proof-grade uniform order16 bound for the order16 component source",
                    "same-surface addition with the residualTaylor polynomial in the high-order receiver normalization",
                ],
            },
            "reusableButNotSufficient": {
                "omegaPrimePayload": {
                    "path": OMEGA_PRIME_PAYLOAD,
                    "exists": (ROOT / OMEGA_PRIME_PAYLOAD).exists(),
                    "status": "proof_grade_for_omega_prime_only",
                    "whyNotEnough": (
                        "It certifies step22OmegaArchWeightDerivClosedForm, "
                        "not the whole CombinedCancellationIntervalExpr."
                    ),
                },
                "hornerRangeChecker": {
                    "definition": symbol_ref(
                        "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationPolynomialRange.lean",
                        "structure Step33Sub0CombinedCancellationHornerRangeCert",
                    ),
                    "status": "ready_after_coefficients",
                    "whyNotEnough": (
                        "It consumes a degree-15 polynomial range; it does not "
                        "produce center jets or order16 source bounds."
                    ),
                },
                "componentAssemblyLedger": {
                    "path": COMPONENT_ASSEMBLY_LEDGER,
                    "exists": (ROOT / COMPONENT_ASSEMBLY_LEDGER).exists(),
                    "status": "algebraic_coefficients_checked_remainder_source_open",
                    "whyNotEnough": (
                        "It records exact assembly/payload facts but still marks "
                        "component remainder/source-model closure open."
                    ),
                },
                "centeredTaylorFactorDerivativeRoute": {
                    "bridgeFile": ORDER16_FACTOR_DERIVATIVE_MAJORANT_BRIDGE_FILE,
                    "budgetFile": ORDER16_BUDGET_PAYLOAD_FILE,
                    "status": (
                        "checked_but_budget_killed"
                        if order16_centered_taylor_factor_route_budget_killed
                        else "missing_or_incomplete"
                    ),
                    "failureCode": (
                        FACTOR_DERIVATIVE_BUDGET_FAILURE
                        if order16_centered_taylor_factor_route_budget_killed
                        else FACTOR_DERIVATIVE_BOUNDS_FAILURE
                    ),
                    "whyNotEnough": (
                        "It proves a useful receiver/pattern for future sharper "
                        "factor rows, but current centered-Taylor majorants do "
                        "not fit the active budget. The live proof object remains "
                        "a whole-expression interval certificate for "
                        "ComponentSource - NonzeroModelPoly."
                    ),
                },
            },
            "requiredBridgeShape": [
                (
                    "active-actual lower/upper center-row intervals are now "
                    "available from the signed factor rows and checked "
                    "factor-product receiver"
                ),
                (
                    "midpoint/error center-jet abs rows are now available for "
                    "the whole combined expression"
                ),
                (
                    "forall j : Fin 16, norm(iteratedDeriv j "
                    "CombinedCancellationIntervalExpr center / j! - coeff[j]) "
                    "<= coeffErrorAbs[j]"
                ),
                (
                    "forall eta in Icc 0 (1/10), norm(iteratedDeriv 16 "
                    "CombinedCancellationIntervalExpr eta) <= order16Abs"
                ),
                (
                    "sum_j coeffErrorAbs[j] * radius^j + "
                    "order16Abs * radius^16 / 16! <= remainderAbs"
                ),
                "Horner range for rawOmegaATaylorPolynomial 15 center coeff",
                "target lower/upper budget after subtracting/adding remainderAbs",
            ],
            "nextPatchRecommendation": (
                "Build the order16 source interval payload in the same source "
                "normalization. Do not instantiate SourceIntervalCert.Valid "
                "until order16 source interval, Horner range, and target-budget "
                "rows are all proof-grade."
            ),
        },
        "candidateSegmentSource": {
            "path": str(segmented_path),
            "exists": segmented is not None,
            "schema": segmented.get("schema") if segmented else None,
            "status": segmented.get("status") if segmented else None,
            "proofMode": segmented.get("proofMode") if segmented else None,
            "sourceIsProofGrade": False,
            "interpretation": (
                "The candidate records exact rational coverage and budget checks, "
                "but its sourceProofStatus remains sampled_candidate_not_lean_proof. "
                "It cannot instantiate the high-order Valid payload."
            ),
        },
        "segments": segments,
        "candidateArithmeticStatus": {
            "coverage": coverage,
            "budgetPassedExactRational": budget_passed,
            "candidateReadyForLeanShape": coverage["coveragePassedExactRational"]
            and budget_passed,
            "proofGradeCombinedBoundsPresent": proof_grade_segments,
        },
        "closedLocalFacts": [
            "OmegaPrime generated Taylor remainder cert is Valid and has a public bound.",
            "Omega Taylor bound is obtained by integrating OmegaPrime plus anchor interval.",
            "rawDeriv - assembledPoly equals the scaled cancellation RHS.",
            "deriv residual equals residualTaylor P45 polynomial plus ScaledCancellationRhs.",
            "triangle split is killed by checked residualTaylor final-slope failures.",
            "rows0..11 independent product budget is width-killed.",
            "High-order Taylor receiver surface is the target adapter; it still needs concrete proof rows.",
            "Whole-expression smoothness and all-row component-source center-jet crosswalk are Lean-checked.",
            "Whole-expression order-16 component-source bridge and norm adapter are Lean-checked.",
            "Source-bounds-to-HighOrderTaylorCert.Valid constructor is Lean-checked.",
            "Component-source lower/upper interval rows can feed HighOrderTaylorCert.Valid through a Lean-checked constructor.",
            "Source-interval certificate target routes component-source lower/upper rows to HighOrderTaylorCert.Valid and final combined interval receivers.",
            "Nonconditional source-normal-form support is Lean-checked: cancellationResidualCauchy = actualCauchy - nominalCauchy, the residual Taylor center-jet alignment bridge is checked, and the active-actual center-jet normal form no longer has a residual-jet hypothesis.",
            "ShapeSqDeriv singleAbs/partial-sharp Valid rows can now be transported to signed center-jet intervals for the ShapeSqDerivActual factor.",
            "OmegaPrimeActual, OmegaActual, ShapeSqActual, and ShapeSqDerivActual now have Lean-checked signed center-jet interval row sources.",
            "A Lean-checked receiver now transports termwise factor-product intervals through Cauchy convolution, activeScale, and ResidualDerivmodelCoeff subtraction to active-actual center-row intervals.",
            "Concrete rational active-actual center-row lower/upper definitions and row interval proof are Lean-checked from the signed factor rows and scale upper bound.",
            "The signed active-actual lower/upper rows now feed midpoint/error coeff rows and a Lean-checked center-jet abs theorem for the whole combined expression.",
            "Order-16 component-source algebra now Lean-reduces to activeScale times the actual component-product order-16 derivative.",
            "A Lean-checked order16 factor-derivative receiver now reduces the source interval row to concrete factor derivative bounds for OmegaPrimeActual, OmegaActual, ShapeSqActual, and ShapeSqDerivActual through order 16 plus a scalar active-scale budget comparison.",
            "The centered-Taylor factor-majorant adapter for those four factor families is now locally present, but the exact rational budget audit is killed by the checked order16 remainder-width failure.",
        ],
        "rejectedRoutes": {
            "independentTriangleSplit": (
                "killed: residualTaylor polynomial alone exceeds final slope at the center"
            ),
            "rowsProductBudgetRefinement": (
                "not a closure path while it preserves the independent product-budget style"
            ),
            "centeredTaylorFactorDerivativeRoute": (
                "checked adapter/pattern but budget-killed at current constants; use "
                f"{FACTOR_DERIVATIVE_BUDGET_FAILURE}"
            ),
            "sampledSegmentPayload": "diagnostic only, not proof evidence",
        },
        "nextImplementablePatch": {
            "recommendation": (
                "build the proof-grade whole-expression interval certificate "
                "for ComponentSource - NonzeroModelPoly in the active "
                "nonzero-model scaled-remainder normalization; the current "
                "centered-Taylor factor-derivative route is checked as a pattern "
                "but budget-killed"
            ),
            "firstFailureIfMissing": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP"
            ),
            "leanPayloadTarget": (
                "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean"
            ),
            "checkerTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated"
            ),
            "remainingGap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP"
            ),
            "nextRouteLevelGapAfterSuccess": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP"
            ),
            "killedAlternative": FACTOR_DERIVATIVE_BUDGET_FAILURE,
            "doNot": [
                "do not build C1 point-separation first",
                "do not use sampled/probe rows",
                "do not revive component triangle/product split",
                "do not reuse OmegaPrime payload as a certificate for the whole expression",
                "do not mark Valid/finalBudgetPassed before Lean-checked rows",
                "do not call coarse singleAbs rows tight; they are only proof-grade intervals",
                "do not treat active-actual product row intervals as a SourceIntervalCert.Valid payload",
                "do not treat center-jet abs rows as a SourceIntervalCert.Valid payload",
                "do not treat the order16 structural reduction as a numeric bound",
                "do not treat the factor-derivative receiver as a concrete closure payload",
                "do not spend the centered-Taylor factor-majorant route at current constants; it is budget-killed",
                "do not mark Valid/finalBudgetPassed before order16, Horner, and target-budget rows are checked",
            ],
        },
        "sourceDefinitionHashes": {
            COMBINED_FILE: file_hash(ROOT / COMBINED_FILE),
            CERT_CHECKER_FILE: file_hash(ROOT / CERT_CHECKER_FILE),
            CONDITIONAL_PAYLOAD_FILE: file_hash(ROOT / CONDITIONAL_PAYLOAD_FILE),
            HIGH_ORDER_SOURCE_FILE: file_hash(ROOT / HIGH_ORDER_SOURCE_FILE),
            SOURCE_MODEL_BRIDGE_FILE: file_hash(ROOT / SOURCE_MODEL_BRIDGE_FILE),
            SOURCE_INTERVAL_CERT_FILE: file_hash(ROOT / SOURCE_INTERVAL_CERT_FILE),
            SOURCE_NORMAL_FORM_FILE: file_hash(ROOT / SOURCE_NORMAL_FORM_FILE),
            ORDER16_FACTOR_MAJORANT_FILE: file_hash(ROOT / ORDER16_FACTOR_MAJORANT_FILE),
            ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE: file_hash(
                ROOT / ORDER16_FACTOR_DERIVATIVE_RECEIVER_FILE
            ),
            ORDER16_FACTOR_DERIVATIVE_MAJORANT_BRIDGE_FILE: file_hash(
                ROOT / ORDER16_FACTOR_DERIVATIVE_MAJORANT_BRIDGE_FILE
            ),
            ORDER16_BUDGET_PAYLOAD_FILE: file_hash(ROOT / ORDER16_BUDGET_PAYLOAD_FILE),
            ACTIVE_ACTUAL_CENTERJET_ROWS_FILE: file_hash(
                ROOT / ACTIVE_ACTUAL_CENTERJET_ROWS_FILE
            ),
            CENTERJET_PAYLOAD_FILE: file_hash(ROOT / CENTERJET_PAYLOAD_FILE),
            BOUND_INPUTS_FILE: file_hash(ROOT / BOUND_INPUTS_FILE),
            NORM_RECEIVER_FILE: file_hash(ROOT / NORM_RECEIVER_FILE),
            P45_BRIDGE_FILE: file_hash(ROOT / P45_BRIDGE_FILE),
            LANDING_FILE: file_hash(ROOT / LANDING_FILE),
            COMPONENT_ASSEMBLY_PAYLOAD_FILE: file_hash(ROOT / COMPONENT_ASSEMBLY_PAYLOAD_FILE),
            COMPONENT_ASSEMBLY_LEDGER: file_hash(ROOT / COMPONENT_ASSEMBLY_LEDGER),
            OMEGA_PRIME_PAYLOAD: file_hash(ROOT / OMEGA_PRIME_PAYLOAD),
            str(segmented_path.relative_to(ROOT)): file_hash(segmented_path),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Sub0 Combined Cancellation Interval Certificate",
        "",
        "Fail-closed certificate ledger.  This is not Lean proof data and does",
        "not close Step33A.1-A.",
        "",
        "## Summary",
        "",
        f"- schema: `{report['schema']}`",
        f"- route: `{report['routeId']}`",
        f"- status: `{report['status']}`",
        f"- first failure: `{report['firstFailure']}`",
        f"- target lower: `{report['cell']['targetLower']}`",
        f"- target upper: `{report['cell']['targetUpper']}`",
        f"- target width: `{report['cell']['targetWidth']}`",
        "",
        "## Lean Surface",
        "",
    ]
    for key, value in report["targetLeanSurface"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## High-Order Payload Target", ""])
    payload = report["requiredHighOrderPayload"]
    lines.extend(
        [
            f"- certStructure: `{payload['certStructure']}`",
            f"- validPredicate: `{payload['validPredicate']}`",
            "",
            "Must provide:",
        ]
    )
    for item in payload["mustProvide"]:
        lines.append(f"- {item}")
    lines.extend(["", "Adapter chain:"])
    for item in payload["adapterChain"]:
        lines.append(f"- `{item}`")
    lines.extend(
        [
            "",
            "Target statement:",
            "",
            "```text",
            report["targetStatement"],
            "```",
            "",
            "Combined expression:",
            "",
            f"`{report['combinedExpressionMeaning']}`",
            "",
            "## Proof Status",
            "",
        ]
    )
    for key, value in report["proofStatus"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Source Model Inventory", ""])
    source_model = report["sourceModelInventory"]
    lines.extend(
        [
            f"- status: `{source_model['status']}`",
            f"- firstSourceFailure: `{source_model['firstSourceFailure']}`",
            f"- centerJetFailure: `{source_model['centerJetFailure']}`",
            f"- order16Failure: `{source_model['order16Failure']}`",
            "",
            "Source-interval certificate target:",
        ]
    )
    for key, value in source_model["sourceIntervalCertTarget"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "Source normal-form support:",
        ]
    )
    for key, value in source_model["sourceNormalFormSupport"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "Checked source-model bridge:",
        ]
    )
    for key, value in source_model["checkedBridge"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "Target function:",
            f"- meaning: `{source_model['targetFunction']['meaning']}`",
            f"- formula: `{source_model['targetFunction']['formula']}`",
            f"- definition: `{source_model['targetFunction']['definition']}`",
            "",
            "Rational polynomial part:",
        ]
    )
    for key, value in source_model["rationalPolynomialPart"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "ScaledCancellationRhs:", ""])
    for key, value in source_model["scaledCancellationRhs"].items():
        if isinstance(value, list):
            lines.append(f"- {key}:")
            for item in value:
                lines.append(f"  - {item}")
        else:
            lines.append(f"- {key}: `{value}`")
    lines.extend(["", "Reusable but not sufficient:", ""])
    for key, value in source_model["reusableButNotSufficient"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "Required bridge shape:", ""])
    for item in source_model["requiredBridgeShape"]:
        lines.append(f"- {item}")
    lines.append(
        f"- nextPatchRecommendation: `{source_model['nextPatchRecommendation']}`"
    )
    lines.extend(["", "## Candidate Segments", ""])
    if report["segments"]:
        for segment in report["segments"]:
            lines.extend(
                [
                    f"- cell `{segment['cell']}`:",
                    f"  segment = `[{segment['segmentL']}, {segment['segmentU']}]`",
                    f"  combined = `[{segment['combinedLower']}, {segment['combinedUpper']}]`",
                    f"  budgetPassesExactRational = `{segment['budgetPassesExactRational']}`",
                    f"  sourceProofStatus = `{segment['sourceProofStatus']}`",
                    f"  isProofGrade = `{segment['isProofGrade']}`",
                    f"  proofGradeCombinedBounds = `{segment['proofGradeCombinedBounds']}`",
                ]
            )
    else:
        lines.append("- no candidate segments found")
    lines.extend(["", "## Candidate Arithmetic", ""])
    arithmetic = report["candidateArithmeticStatus"]
    coverage = arithmetic["coverage"]
    for key, value in coverage.items():
        lines.append(f"- coverage.{key}: `{value}`")
    lines.extend(
        [
            f"- budgetPassedExactRational: `{arithmetic['budgetPassedExactRational']}`",
            f"- candidateReadyForLeanShape: `{arithmetic['candidateReadyForLeanShape']}`",
            f"- proofGradeCombinedBoundsPresent: `{arithmetic['proofGradeCombinedBoundsPresent']}`",
            "",
            "## Required Certificate",
            "",
        ]
    )
    cert = report["requiredCertificate"]
    lines.extend(
        [
            f"- kind: `{cert['kind']}`",
            f"- must prove: `{cert['mustProve']}`",
            "",
            "May use:",
        ]
    )
    for item in cert["mayUse"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("Must not use:")
    for item in cert["mustNotUse"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Closed Local Facts", ""])
    for item in report["closedLocalFacts"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Rejected Routes", ""])
    for key, value in report["rejectedRoutes"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Candidate Source", ""])
    for key, value in report["candidateSegmentSource"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Next Implementable Patch", ""])
    for key, value in report["nextImplementablePatch"].items():
        if isinstance(value, list):
            lines.append(f"- {key}:")
            for item in value:
                lines.append(f"  - {item}")
        else:
            lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Failure Codes", ""])
    for code in report["failureCodes"]:
        lines.append(f"- `{code}`")
    lines.extend(["", "## Source Hashes", ""])
    for key, value in report["sourceDefinitionHashes"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--segmented-payload", type=Path, default=DEFAULT_SEGMENTED_PAYLOAD)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(args.segmented_payload)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    args.out_md.write_text(render_md(report), encoding="utf-8")


if __name__ == "__main__":
    run()
