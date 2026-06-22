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

SCHEMA = "q3_psdpd_step33_a1_sub0_combined_cancellation_interval_certificate.v4"
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
    source_model_bridge_present = (
        source_model_smooth_present and source_model_center_jet_present
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
            "highOrderCenterJetRowsPresent": False,
            "highOrderOrder16RowsPresent": False,
            "highOrderHornerRangeRowsPresent": False,
            "highOrderTargetBudgetRowsPresent": False,
            "wholeExpressionSourceModelPresent": source_model_bridge_present,
            "centerJetSourceModelPresent": source_model_center_jet_present,
            "order16SourceModelPresent": False,
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
                "a concrete Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid "
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
                "uniform order16Abs on Set.Icc 0 (1/10)",
                "remainderBudget proof",
                "polyLower and polyUpper for the degree-15 polynomial",
                "Step33Sub0CombinedCancellationHornerRangeCert.Valid",
                "target lower budget proof",
                "target upper budget proof",
            ],
            "adapterChain": [
                HIGH_ORDER_REMAINDER,
                HIGH_ORDER_TO_INTERVAL,
                HIGH_ORDER_TO_HCOMBINED,
                HIGH_ORDER_TO_RESIDUAL,
            ],
        },
        "sourceModelInventory": {
            "status": (
                "source_model_bridge_checked_payload_rows_missing"
                if source_model_bridge_present
                else "fail_closed_source_model_gap"
            ),
            "firstSourceFailure": (
                NEXT_PAYLOAD_FAILURE
                if source_model_bridge_present
                else SOURCE_MODEL_FAILURE
            ),
            "centerJetFailure": (
                None
                if source_model_center_jet_present
                else CENTER_JET_SOURCE_MODEL_FAILURE
            ),
            "order16Failure": ORDER16_SOURCE_MODEL_FAILURE,
            "checkedBridge": {
                "file": SOURCE_MODEL_BRIDGE_FILE,
                "smoothTheorem": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_SMOOTH_THEOREM
                ),
                "centerJetTheorem": symbol_ref(
                    SOURCE_MODEL_BRIDGE_FILE, SOURCE_MODEL_CENTER_JET_THEOREM
                ),
                "smoothPresent": source_model_smooth_present,
                "centerJetPresent": source_model_center_jet_present,
                "status": (
                    "checked_source_model_support"
                    if source_model_bridge_present
                    else "missing_or_incomplete"
                ),
                "whyNotEnough": (
                    "This proves the whole-expression smooth bridge and all-row "
                    "component-source center-jet crosswalk. It still does not "
                    "emit rational coeff rows, a uniform order16Abs bound, "
                    "Horner range rows, target-budget rows, or a Valid payload."
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
                    "source_model_checked_for_center_jets"
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
                    "proof-grade uniform order16 bound for ScaledCancellationRhs in the combined expression",
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
            },
            "requiredBridgeShape": [
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
                "Generate/prove the concrete HighOrderTaylorCert payload rows "
                "from the checked source-model bridge."
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
        ],
        "rejectedRoutes": {
            "independentTriangleSplit": (
                "killed: residualTaylor polynomial alone exceeds final slope at the center"
            ),
            "rowsProductBudgetRefinement": (
                "not a closure path while it preserves the independent product-budget style"
            ),
            "sampledSegmentPayload": "diagnostic only, not proof evidence",
        },
        "nextImplementablePatch": {
            "recommendation": (
                "generate/prove the concrete "
                "Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid payload"
            ),
            "firstFailureIfMissing": NEXT_PAYLOAD_FAILURE,
            "leanPayloadTarget": (
                "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationHighOrderTaylorSource.lean"
            ),
            "checkerTheorem": (
                HIGH_ORDER_TO_HCOMBINED
            ),
            "remainingGap": NEXT_PAYLOAD_FAILURE,
            "doNot": [
                "do not build C1 point-separation first",
                "do not use sampled/probe rows",
                "do not revive component triangle/product split",
                "do not reuse OmegaPrime payload as a certificate for the whole expression",
                "do not mark Valid/finalBudgetPassed before Lean-checked rows",
            ],
        },
        "sourceDefinitionHashes": {
            COMBINED_FILE: file_hash(ROOT / COMBINED_FILE),
            CERT_CHECKER_FILE: file_hash(ROOT / CERT_CHECKER_FILE),
            CONDITIONAL_PAYLOAD_FILE: file_hash(ROOT / CONDITIONAL_PAYLOAD_FILE),
            HIGH_ORDER_SOURCE_FILE: file_hash(ROOT / HIGH_ORDER_SOURCE_FILE),
            SOURCE_MODEL_BRIDGE_FILE: file_hash(ROOT / SOURCE_MODEL_BRIDGE_FILE),
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
