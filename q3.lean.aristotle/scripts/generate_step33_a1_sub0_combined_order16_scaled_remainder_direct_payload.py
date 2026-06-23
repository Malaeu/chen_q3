#!/usr/bin/env python3
"""Fail-closed ledger for the direct nonzero-model scaled-remainder payload.

The target is the same-unit signed residual

    CombinedCancellationOrder16ComponentSource - CombinedOrder16NonzeroModelPoly

on `[0, 1/10]`, at the canonical `BiasedResidualRemainderAbs` budget.  This
script does not emit proof rows and does not claim Step33A.1-A closure.  It
records the exact generator-facing payload surface and the first missing
proof-grade certificate.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_combined_order16_"
    "scaled_remainder_direct_payload.v3"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

DIRECT_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean"
)
ZERO_MODEL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderZeroModelPayload.lean"
)
INTERVAL_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderIntervalPayload.lean"
)
REMAINDER_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerRemainderBridge.lean"
)
P45_FULL_TAYLOR_BRIDGE_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean"
)
ORDER16_NONZERO_MODEL_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean"
)
DIRECT_INTERVAL_PAYLOAD_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectIntervalPayload.lean"
)
DIRECT_MODEL_PAYLOAD_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectModelPayload.lean"
)
BIASED_SOURCE_HORNER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerCert.lean"
)
BIASED_SIGNED_FACTOR_ADAPTER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSignedFactorAdapter.lean"
)

JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.md"
)
ROW_OBLIGATIONS_JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_row_obligations.json"
)
CANCELLATION_DIRECT_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_combined_cancellation_order16_direct_payload.json"
)
SOURCE_INTERVAL_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_combined_order16_source_interval.json"
)
SIGNED_FACTOR_ROWS_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_combined_order16_signed_factor_rows.json"
)

DIRECT_PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_direct_payload",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval",
]

ZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderSourceProp_of_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_zeroModel",
]

INTERVAL_PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert",
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget",
]

REMAINDER_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound",
]

P45_FULL_TAYLOR_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_eq_scaledCancellationRhs",
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_bound_of_scaledCancellationRhs_bound",
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_scaledCancellationRhs_bound",
]

ORDER16_NONZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelSource",
]

DIRECT_INTERVAL_PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget",
    "Step33Sub0CombinedCancellationOrder16DirectIntervalCert",
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_direct_interval_to_source_field",
]

DIRECT_MODEL_PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectInterval_valid_of_horner_remainder",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp",
]

BIASED_SOURCE_HORNER_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert",
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_horner_family",
]

BIASED_SIGNED_FACTOR_ADAPTER_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover",
    "Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert",
]

CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "NONZERO_MODEL_INTERVAL_CERT_GAP"
)
PARENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_"
    "SCALED_REMAINDER_BOUND_GAP"
)
P45_REUSE_FAILURE = (
    "STEP33_A1_SUB0_P45_FULL_TAYLOR_ORDER16_SOURCE_MISMATCH"
)
DIRECT_ROW_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "DIRECT_ROW_SOURCE_GAP"
)
FIRST_GENERATED_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
    "nonzeroModel_interval_generated"
)
FIRST_GENERATED_SOURCE_PROP_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
    "nonzeroModel_sourceProp_generated"
)


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    if not path.exists():
        return {symbol: False for symbol in symbols}
    text = path.read_text(encoding="utf-8")
    return {symbol: symbol in text for symbol in symbols}


def all_true(items: dict[str, bool]) -> bool:
    return all(items.values())


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def summarize_existing_ledger(path: Path, keys: list[str]) -> dict[str, Any]:
    data = load_json(path)
    out: dict[str, Any] = {"path": rel(path), "exists": bool(data)}
    for key in keys:
        out[key] = data.get(key)
    return out


def build_ledger() -> dict[str, Any]:
    direct_symbols = file_contains(DIRECT_PAYLOAD_FILE, DIRECT_PAYLOAD_SYMBOLS)
    zero_model_symbols = file_contains(ZERO_MODEL_FILE, ZERO_MODEL_SYMBOLS)
    interval_symbols = file_contains(INTERVAL_PAYLOAD_FILE, INTERVAL_PAYLOAD_SYMBOLS)
    remainder_bridge_symbols = file_contains(
        REMAINDER_BRIDGE_FILE, REMAINDER_BRIDGE_SYMBOLS
    )
    p45_full_taylor_symbols = file_contains(
        P45_FULL_TAYLOR_BRIDGE_FILE, P45_FULL_TAYLOR_BRIDGE_SYMBOLS
    )
    order16_nonzero_model_symbols = file_contains(
        ORDER16_NONZERO_MODEL_FILE, ORDER16_NONZERO_MODEL_SYMBOLS
    )
    direct_interval_payload_symbols = file_contains(
        DIRECT_INTERVAL_PAYLOAD_FILE, DIRECT_INTERVAL_PAYLOAD_SYMBOLS
    )
    direct_model_payload_symbols = file_contains(
        DIRECT_MODEL_PAYLOAD_FILE, DIRECT_MODEL_PAYLOAD_SYMBOLS
    )
    biased_source_horner_symbols = file_contains(
        BIASED_SOURCE_HORNER_FILE, BIASED_SOURCE_HORNER_SYMBOLS
    )
    biased_signed_factor_adapter_symbols = file_contains(
        BIASED_SIGNED_FACTOR_ADAPTER_FILE, BIASED_SIGNED_FACTOR_ADAPTER_SYMBOLS
    )

    direct_surface_present = all_true(direct_symbols)
    zero_model_bridge_present = all_true(zero_model_symbols)
    interval_surface_present = all_true(interval_symbols)
    remainder_bridge_present = all_true(remainder_bridge_symbols)
    p45_full_taylor_bridge_present = all_true(p45_full_taylor_symbols)
    order16_nonzero_model_bridge_present = all_true(order16_nonzero_model_symbols)
    direct_interval_payload_present = all_true(direct_interval_payload_symbols)
    direct_model_payload_present = all_true(direct_model_payload_symbols)
    biased_source_horner_present = all_true(biased_source_horner_symbols)
    biased_signed_factor_adapter_present = all_true(
        biased_signed_factor_adapter_symbols
    )

    proof_status = (
        "direct_nonzero_model_row_worklist_emitted_missing_interval_cert"
        if direct_surface_present
        and zero_model_bridge_present
        and interval_surface_present
        and remainder_bridge_present
        else "direct_nonzero_model_payload_surface_incomplete"
    )

    prior_ledgers = {
        "biasedScaledRemainderInterval": summarize_existing_ledger(
            REQUEST_DIR
            / "step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.json",
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "nonzeroModelResidualBridgeLeanChecked",
                "nonzeroModelResidualSourceBoundLeanChecked",
            ],
        ),
        "biasedResidualHornerPayload": summarize_existing_ledger(
            REQUEST_DIR / "step33_a1_sub0_biased_residual_horner_payload.json",
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "scaledRemainderBoundLeanChecked",
                "nonzeroModelResidualBridgeLeanChecked",
                "nonzeroModelResidualSourceBoundLeanChecked",
            ],
        ),
    }

    source_availability_audit = [
        {
            "source": "order16_nonzero_model_normal_forms",
            "file": rel(ORDER16_NONZERO_MODEL_FILE),
            "artifactStatus": "lean_surface_present",
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "Exact normal-form names exist for the current residual, but "
                "there is no generated signed interval theorem proving the "
                "whole expression inside BiasedResidualRemainderAbs."
            ),
            "firstMissingProofObject": FIRST_GENERATED_INTERVAL_THEOREM,
            "failureCode": DIRECT_ROW_SOURCE_GAP,
        },
        {
            "source": "direct_scaled_remainder_payload_surface",
            "file": rel(DIRECT_PAYLOAD_FILE),
            "artifactStatus": "lean_receiver_present",
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The receiver can consume a proof-grade direct payload, but "
                "the segment rows and whole-expression range certificate are "
                "still missing."
            ),
            "firstMissingProofObject": FIRST_GENERATED_INTERVAL_THEOREM,
            "failureCode": CURRENT_GAP,
        },
        {
            "source": "combined_cancellation_order16_direct_zero_model_ledger",
            "ledger": rel(CANCELLATION_DIRECT_LEDGER_FILE),
            "artifactStatus": "local_ledger_present"
            if CANCELLATION_DIRECT_LEDGER_FILE.exists()
            else "ledger_missing",
            "sameTarget": False,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "This threshold zero-model route records a checked interface "
                "but is killed by the rawProduct17 centered-Taylor budget and "
                "does not bound ComponentSource - NonzeroModelPoly."
            ),
            "blockingGap": load_json(CANCELLATION_DIRECT_LEDGER_FILE).get(
                "currentGap"
            ),
            "failureCode": load_json(CANCELLATION_DIRECT_LEDGER_FILE).get(
                "failureCodeIfRawProduct17BoundFails"
            ),
        },
        {
            "source": "combined_order16_source_interval_ledger",
            "ledger": rel(SOURCE_INTERVAL_LEDGER_FILE),
            "artifactStatus": "local_ledger_present"
            if SOURCE_INTERVAL_LEDGER_FILE.exists()
            else "ledger_missing",
            "sameTarget": False,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "This is a zero-model whole-source interval receiver; its "
                "current gap is signed-factor/source rows, not the nonzero "
                "model residual interval needed here."
            ),
            "blockingGap": load_json(SOURCE_INTERVAL_LEDGER_FILE).get(
                "currentGap"
            ),
            "failureCode": load_json(SOURCE_INTERVAL_LEDGER_FILE).get(
                "failureCodeIfRowsMissing"
            ),
        },
        {
            "source": "combined_order16_signed_factor_rows_ledger",
            "ledger": rel(SIGNED_FACTOR_ROWS_LEDGER_FILE),
            "artifactStatus": "local_ledger_present"
            if SIGNED_FACTOR_ROWS_LEDGER_FILE.exists()
            else "ledger_missing",
            "sameTarget": False,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The signed Leibniz checker interface is alive, but the "
                "centered-Taylor abs-row route is budget-killed and does not "
                "supply the direct nonzero-model source interval."
            ),
            "blockingGap": load_json(SIGNED_FACTOR_ROWS_LEDGER_FILE).get(
                "currentGap"
            ),
            "failureCode": load_json(SIGNED_FACTOR_ROWS_LEDGER_FILE).get(
                "failureCodeIfCenteredTaylorAbsRowsUsed"
            ),
        },
        {
            "source": "p45_full_taylor_bridge",
            "file": rel(P45_FULL_TAYLOR_BRIDGE_FILE),
            "artifactStatus": "lean_surface_present",
            "sameTarget": False,
            "proofGradeRowsPresent": p45_full_taylor_bridge_present,
            "spendableForCurrentTarget": False,
            "reason": (
                "P45/full-Taylor controls a derivative-level residual error; "
                "no local theorem converts it to the order-16 "
                "ComponentSource - NonzeroModelPoly interval."
            ),
            "failureCode": P45_REUSE_FAILURE,
        },
    ]

    row_obligations = [
        {
            "id": "R0_cell_cover",
            "object": "segment cells cover Set.Icc 0 (1/10)",
            "requiredFor": "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover",
            "status": "interface_ready_rows_missing",
            "proofGrade": False,
        },
        {
            "id": "R1_whole_signed_expression_range",
            "object": FIRST_GENERATED_INTERVAL_THEOREM,
            "statement": (
                "for all eta in [0,1/10], "
                "-BiasedResidualRemainderAbs <= ComponentSource eta - "
                "NonzeroModelPoly eta and ComponentSource eta - "
                "NonzeroModelPoly eta <= BiasedResidualRemainderAbs"
            ),
            "status": "missing_first_proof_object",
            "proofGrade": False,
        },
        {
            "id": "R2_horner_or_interval_rows",
            "object": "proof-grade rational/interval rows for the assembled signed expression",
            "requiredFor": FIRST_GENERATED_INTERVAL_THEOREM,
            "status": "missing",
            "proofGrade": False,
        },
        {
            "id": "R3_budget_rows",
            "object": "lowerBudget and upperBudget against BiasedResidualRemainderAbs",
            "requiredFor": "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert.Valid",
            "status": "missing",
            "proofGrade": False,
        },
        {
            "id": "R4_source_prop_adapter",
            "object": FIRST_GENERATED_SOURCE_PROP_THEOREM,
            "requiredFor": "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp",
            "status": "interface_ready_depends_on_R1",
            "proofGrade": False,
        },
        {
            "id": "R5_zero_model_payload_target",
            "object": "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_direct_payload",
            "requiredFor": "biased residual-Horner zero-model handoff",
            "status": "checked_bridge_depends_on_R4",
            "checkedBridge": bool(zero_model_bridge_present),
            "proofGrade": False,
        },
    ]

    candidate_reuse_routes = [
        {
            "route": "p45_full_taylor",
            "file": rel(P45_FULL_TAYLOR_BRIDGE_FILE),
            "surfacePresent": p45_full_taylor_bridge_present,
            "verdict": "rejected_not_same_expression",
            "failureCode": P45_REUSE_FAILURE,
        },
        {
            "route": "direct_payload_surface",
            "file": rel(DIRECT_PAYLOAD_FILE),
            "surfacePresent": direct_surface_present,
            "verdict": "usable_interface_no_rows",
            "failureCode": CURRENT_GAP,
        },
        {
            "route": "direct_interval_payload",
            "file": rel(DIRECT_INTERVAL_PAYLOAD_FILE),
            "surfacePresent": direct_interval_payload_present,
            "verdict": "old_source_interval_interface_not_scaled_nonzero_model_interval",
            "failureCode": CURRENT_GAP,
        },
        {
            "route": "direct_model_payload",
            "file": rel(DIRECT_MODEL_PAYLOAD_FILE),
            "surfacePresent": direct_model_payload_present,
            "verdict": "conditional_checker_only_hard_remainder_premise_is_current_gap",
            "failureCode": CURRENT_GAP,
        },
        {
            "route": "biased_source_horner",
            "file": rel(BIASED_SOURCE_HORNER_FILE),
            "surfacePresent": biased_source_horner_present,
            "verdict": "not_same_target_without_new_bridge",
            "failureCode": CURRENT_GAP,
        },
        {
            "route": "biased_signed_factor_adapter",
            "file": rel(BIASED_SIGNED_FACTOR_ADAPTER_FILE),
            "surfacePresent": biased_signed_factor_adapter_present,
            "verdict": "adapter_for_biased_route_only_not_direct_nonzero_model_rows",
            "failureCode": CURRENT_GAP,
        },
    ]

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "direct_nonzero_model_scaled_remainder_interval",
        "directPayloadFile": rel(DIRECT_PAYLOAD_FILE),
        "zeroModelPayloadFile": rel(ZERO_MODEL_FILE),
        "intervalPayloadFile": rel(INTERVAL_PAYLOAD_FILE),
        "remainderBridgeFile": rel(REMAINDER_BRIDGE_FILE),
        "p45FullTaylorBridgeFile": rel(P45_FULL_TAYLOR_BRIDGE_FILE),
        "order16NonzeroModelFile": rel(ORDER16_NONZERO_MODEL_FILE),
        "directIntervalPayloadFile": rel(DIRECT_INTERVAL_PAYLOAD_FILE),
        "directModelPayloadFile": rel(DIRECT_MODEL_PAYLOAD_FILE),
        "biasedSourceHornerFile": rel(BIASED_SOURCE_HORNER_FILE),
        "biasedSignedFactorAdapterFile": rel(BIASED_SIGNED_FACTOR_ADAPTER_FILE),
        "directPayloadSymbols": direct_symbols,
        "zeroModelSymbols": zero_model_symbols,
        "intervalPayloadSymbols": interval_symbols,
        "remainderBridgeSymbols": remainder_bridge_symbols,
        "p45FullTaylorBridgeSymbols": p45_full_taylor_symbols,
        "order16NonzeroModelSymbols": order16_nonzero_model_symbols,
        "directIntervalPayloadSymbols": direct_interval_payload_symbols,
        "directModelPayloadSymbols": direct_model_payload_symbols,
        "biasedSourceHornerSymbols": biased_source_horner_symbols,
        "biasedSignedFactorAdapterSymbols": biased_signed_factor_adapter_symbols,
        "directPayloadSurfacePresent": direct_surface_present,
        "zeroModelBridgePresent": zero_model_bridge_present,
        "intervalPayloadSurfacePresent": interval_surface_present,
        "remainderBridgePresent": remainder_bridge_present,
        "p45FullTaylorBridgePresent": p45_full_taylor_bridge_present,
        "order16NonzeroModelBridgePresent": order16_nonzero_model_bridge_present,
        "directIntervalPayloadPresent": direct_interval_payload_present,
        "directModelPayloadPresent": direct_model_payload_present,
        "biasedSourceHornerPresent": biased_source_horner_present,
        "biasedSignedFactorAdapterPresent": biased_signed_factor_adapter_present,
        "proofStatus": proof_status,
        "proofGrade": False,
        "currentGap": CURRENT_GAP,
        "parentGap": PARENT_GAP,
        "firstFailureCode": CURRENT_GAP,
        "firstRowFailureCode": DIRECT_ROW_SOURCE_GAP,
        "firstMissingProofObject": FIRST_GENERATED_INTERVAL_THEOREM,
        "rowWorklistEmitted": True,
        "rowWorklistFile": rel(ROW_OBLIGATIONS_JSON_OUT),
        "rowObligations": row_obligations,
        "candidateReuseRoutes": candidate_reuse_routes,
        "sourceAvailabilityAudit": source_availability_audit,
        "p45FullTaylorReuseVerdict": "not_spendable_for_order16_direct_source_bound",
        "p45FullTaylorReuseFailureCode": P45_REUSE_FAILURE,
        "proshkaRouteReviewDecision": "CHOSEN: A",
        "proshkaRouteReviewQuestion": (
            "Does the existing P45/full-Taylor interval machinery prove the "
            "order-16 ComponentSource - NonzeroModelPoly source bound, or is "
            "a separate direct certificate target still needed?"
        ),
        "proshkaRouteReviewAnswer": (
            "A: proceed with the direct rational/Horner interval generator; "
            "P45/full-Taylor bounds a different derivative-level expression "
            "and does not prove the uniform order-16 source-minus-nonzero-model "
            "interval."
        ),
        "proshkaRowWorklistDecision": "CHOSEN: A",
        "proshkaRowWorklistAnswer": (
            "First patch should emit exact row obligations; an immediate Lean "
            "certificate would still be conditional without proof-grade "
            "whole-expression remainder source rows."
        ),
        "directNonzeroModelIntervalRowsLeanChecked": False,
        "directNonzeroModelSourcePropLeanChecked": False,
        "zeroModelPayloadTargetLeanChecked": zero_model_bridge_present,
        "step33A1ClosedClaimed": False,
        "doNotSplitSummands": True,
        "targetExpression": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16"
            "ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0"
            "CombinedOrder16NonzeroModelPoly eta"
        ),
        "targetBudget": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16Biased"
            "ResidualRemainderAbs"
        ),
        "targetProp": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
            "ScaledRemainderNonzeroModelSourceProp"
        ),
        "targetPayload": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
            "ScaledRemainderDirectPayloadTarget"
        ),
        "firstGeneratedIntervalTheorem": FIRST_GENERATED_INTERVAL_THEOREM,
        "firstGeneratedSourcePropTheorem": FIRST_GENERATED_SOURCE_PROP_THEOREM,
        "whyP45FullTaylorIsNotEnough": (
            "The P45/full-Taylor bridge rewrites a derivative-level residual "
            "error into the scaled cancellation RHS. The current direct target "
            "is the order-16 source residual ComponentSource - NonzeroModelPoly, "
            "which Lean identifies with ActiveScaleCoeff * D^16"
            "(ComponentProductCancellationResidual) plus the same-unit "
            "scale-mismatch nominal-product term. No local theorem converts the "
            "P45/full-Taylor interval into this order-16 source interval."
        ),
        "theoremShape": (
            "prove a signed interval on [0,1/10] for ComponentSource - "
            "NonzeroModelPoly inside +/- BiasedResidualRemainderAbs; then "
            "use primaryFiniteRow0Parent0Split100Sub0_"
            "combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_"
            "full_cell_interval or a direct family payload target"
        ),
        "certificateShape": [
            "segment cells covering [0,1/10]",
            "whole signed expression polynomial/range rows",
            "whole-expression remainder rows",
            "per-segment lower/upper budget rows",
            "global residualAbs = BiasedResidualRemainderAbs",
        ],
        "priorLedgers": prior_ledgers,
        "guard": (
            "This is an interface and fail-closed ledger only.  It does not "
            "prove the interval rows, and it must not be treated as Step33A.1-A "
            "closure until the direct nonzero-model source proposition is "
            "Lean-checked or backed by proof-grade generated rows."
        ),
    }


def render_symbols(title: str, symbols: dict[str, bool]) -> list[str]:
    return ["", f"## {title}", ""] + [
        f"- `{symbol}`: `{present}`" for symbol, present in symbols.items()
    ]


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Direct Scaled-Remainder Payload Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Status",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- directPayloadSurfacePresent: `{ledger['directPayloadSurfacePresent']}`",
        f"- zeroModelBridgePresent: `{ledger['zeroModelBridgePresent']}`",
        f"- intervalPayloadSurfacePresent: `{ledger['intervalPayloadSurfacePresent']}`",
        f"- remainderBridgePresent: `{ledger['remainderBridgePresent']}`",
        f"- p45FullTaylorBridgePresent: `{ledger['p45FullTaylorBridgePresent']}`",
        "- order16NonzeroModelBridgePresent: "
        f"`{ledger['order16NonzeroModelBridgePresent']}`",
        "- directIntervalPayloadPresent: "
        f"`{ledger['directIntervalPayloadPresent']}`",
        f"- directModelPayloadPresent: `{ledger['directModelPayloadPresent']}`",
        f"- biasedSourceHornerPresent: `{ledger['biasedSourceHornerPresent']}`",
        "- biasedSignedFactorAdapterPresent: "
        f"`{ledger['biasedSignedFactorAdapterPresent']}`",
        "- directNonzeroModelIntervalRowsLeanChecked: "
        f"`{ledger['directNonzeroModelIntervalRowsLeanChecked']}`",
        "- directNonzeroModelSourcePropLeanChecked: "
        f"`{ledger['directNonzeroModelSourcePropLeanChecked']}`",
        "- zeroModelPayloadTargetLeanChecked: "
        f"`{ledger['zeroModelPayloadTargetLeanChecked']}`",
        f"- step33A1ClosedClaimed: `{ledger['step33A1ClosedClaimed']}`",
        f"- doNotSplitSummands: `{ledger['doNotSplitSummands']}`",
        f"- rowWorklistEmitted: `{ledger['rowWorklistEmitted']}`",
        f"- rowWorklistFile: `{ledger['rowWorklistFile']}`",
        f"- firstMissingProofObject: `{ledger['firstMissingProofObject']}`",
        f"- firstRowFailureCode: `{ledger['firstRowFailureCode']}`",
        "",
        "## Current Gap",
        "",
        f"`{ledger['currentGap']}`",
        "",
        "Parent gap:",
        "",
        f"`{ledger['parentGap']}`",
        "",
        "First failure code if the direct route fails:",
        "",
        f"`{ledger['firstFailureCode']}`",
        "",
        "First row-source failure code if the row generator fails:",
        "",
        f"`{ledger['firstRowFailureCode']}`",
        "",
        "P45/full-Taylor reuse verdict:",
        "",
        f"`{ledger['p45FullTaylorReuseVerdict']}`",
        "",
        "P45/full-Taylor reuse failure code:",
        "",
        f"`{ledger['p45FullTaylorReuseFailureCode']}`",
        "",
        "## Target",
        "",
        f"- expression: `{ledger['targetExpression']}`",
        f"- budget: `{ledger['targetBudget']}`",
        f"- prop: `{ledger['targetProp']}`",
        f"- payload: `{ledger['targetPayload']}`",
        f"- first interval theorem: `{ledger['firstGeneratedIntervalTheorem']}`",
        f"- first source-prop theorem: `{ledger['firstGeneratedSourcePropTheorem']}`",
        "",
        "## Route Review",
        "",
        f"- decision: `{ledger['proshkaRouteReviewDecision']}`",
        f"- question: {ledger['proshkaRouteReviewQuestion']}",
        f"- answer: {ledger['proshkaRouteReviewAnswer']}",
        f"- row worklist decision: `{ledger['proshkaRowWorklistDecision']}`",
        f"- row worklist answer: {ledger['proshkaRowWorklistAnswer']}",
        "",
        "## Why P45/full-Taylor Is Not Enough",
        "",
        str(ledger["whyP45FullTaylorIsNotEnough"]),
        "",
        "## Theorem Shape",
        "",
        str(ledger["theoremShape"]),
        "",
        "## Certificate Shape",
        "",
    ]
    lines.extend(f"- {item}" for item in ledger["certificateShape"])
    lines.extend(["", "## Row Obligations", ""])
    for row in ledger["rowObligations"]:
        lines.append(f"### {row['id']}")
        lines.append("")
        for key, value in row.items():
            if key == "id":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Candidate Reuse Routes", ""])
    for route in ledger["candidateReuseRoutes"]:
        lines.append(f"### {route['route']}")
        lines.append("")
        for key, value in route.items():
            if key == "route":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Source Availability Audit", ""])
    for item in ledger["sourceAvailabilityAudit"]:
        lines.append(f"### {item['source']}")
        lines.append("")
        for key, value in item.items():
            if key == "source":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(render_symbols("Direct Payload Symbols", ledger["directPayloadSymbols"]))
    lines.extend(render_symbols("Zero Model Symbols", ledger["zeroModelSymbols"]))
    lines.extend(render_symbols("Interval Payload Symbols", ledger["intervalPayloadSymbols"]))
    lines.extend(render_symbols("Remainder Bridge Symbols", ledger["remainderBridgeSymbols"]))
    lines.extend(
        render_symbols(
            "P45/full-Taylor Bridge Symbols", ledger["p45FullTaylorBridgeSymbols"]
        )
    )
    lines.extend(
        render_symbols(
            "Order16 Nonzero-Model Symbols", ledger["order16NonzeroModelSymbols"]
        )
    )
    lines.extend(
        render_symbols(
            "Direct Interval Payload Symbols", ledger["directIntervalPayloadSymbols"]
        )
    )
    lines.extend(
        render_symbols("Direct Model Payload Symbols", ledger["directModelPayloadSymbols"])
    )
    lines.extend(
        render_symbols("Biased Source Horner Symbols", ledger["biasedSourceHornerSymbols"])
    )
    lines.extend(
        render_symbols(
            "Biased Signed-Factor Adapter Symbols",
            ledger["biasedSignedFactorAdapterSymbols"],
        )
    )
    lines.extend(["", "## Prior Ledgers", ""])
    for name, summary in ledger["priorLedgers"].items():
        lines.append(f"### {name}")
        lines.append("")
        for key, value in summary.items():
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Guard", "", str(ledger["guard"]), ""])
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    ROW_OBLIGATIONS_JSON_OUT.write_text(
        json.dumps(
            {
                "schema": f"{SCHEMA}.row_obligations",
                "generatedAt": ledger["generatedAt"],
                "route": ledger["route"],
                "currentGap": ledger["currentGap"],
                "firstRowFailureCode": ledger["firstRowFailureCode"],
                "firstMissingProofObject": ledger["firstMissingProofObject"],
                "targetExpression": ledger["targetExpression"],
                "targetBudget": ledger["targetBudget"],
                "rowObligations": ledger["rowObligations"],
                "candidateReuseRoutes": ledger["candidateReuseRoutes"],
                "sourceAvailabilityAudit": ledger["sourceAvailabilityAudit"],
                "guard": ledger["guard"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(ledger["proofStatus"])
    print(ledger["firstFailureCode"])
    print(ledger["firstRowFailureCode"])
    print(ledger["currentGap"])
    print(ledger["p45FullTaylorReuseVerdict"])


if __name__ == "__main__":
    main()
