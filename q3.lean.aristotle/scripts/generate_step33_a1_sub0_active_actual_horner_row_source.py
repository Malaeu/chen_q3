#!/usr/bin/env python3
"""Fail-closed ledger for active-actual order-16 Horner row sources.

The checked Lean surface now accepts a future
`Step33Sub0ActiveActualOrder16HornerFamilyCert.Valid` object and transports it
into the existing direct Horner receiver.  This script records the exact row
contract that a later rational/interval generator must satisfy.

It does not emit Lean payload rows and does not claim Step33A.1-A closure.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_active_actual_horner_row_source.v6"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

ACTIVE_ACTUAL_HORNER_SEGMENT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean"
)
ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerFamilyBridge.lean"
)
ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualLowDegreeBridge.lean"
)
ACTIVE_ACTUAL_DEGREE0_SOURCE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0Source.lean"
)
DIRECT_HORNER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.lean"
)
DIRECT_HORNER_SOURCE_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean"
)
FUTURE_LEAN_OUT = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerConcretePayload.lean"
)
SMOKE_PAYLOAD_LEAN_OUT = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerPayload.lean"
)
ACTIVE_ACTUAL_CENTER_JET_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean"
)

DIRECT_PAYLOAD_LEDGER = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json"
)
DIRECT_CERTIFICATE_LEDGER = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.json"
)

JSON_OUT = REQUEST_DIR / "step33_a1_sub0_active_actual_horner_row_source.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_active_actual_horner_row_source.md"
SMOKE_PAYLOAD_SCRIPT = (
    ROOT / "scripts" / "generate_step33_a1_sub0_active_actual_order16_horner_payload.py"
)
SMOKE_PAYLOAD_JSON = (
    REQUEST_DIR / "step33_a1_sub0_active_actual_order16_horner_payload.json"
)
SMOKE_PAYLOAD_MD = (
    REQUEST_DIR / "step33_a1_sub0_active_actual_order16_horner_payload.md"
)

ACTIVE_ACTUAL_HORNER_SEGMENT_SYMBOLS = [
    "Step33Sub0ActiveActualOrder16HornerSegmentCert",
    "structure Valid",
    "cellSubset",
    "polyErrorNonneg",
    "remainderBound",
    "theorem to_activeActual_order16_segment_remainder",
    "theorem to_collapsed_segment_remainder",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert",
    "primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner",
]

ACTIVE_ACTUAL_HORNER_FAMILY_SYMBOLS = [
    "Step33Sub0ActiveActualOrder16HornerDirectSegmentCert",
    "Step33Sub0ActiveActualOrder16HornerDirectRangeCert",
    "Step33Sub0ActiveActualOrder16HornerFamilyCert",
    "structure Valid",
    "activeValid",
    "rangeValid",
    "intervalLowerBudget",
    "intervalUpperBudget",
    "segmentResidualNonneg",
    "segmentLowerBudget",
    "segmentUpperBudget",
    "segmentBudget",
    "cover",
    "theorem to_directHornerFamilyValid",
    "primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily",
    "primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily",
    "primaryFiniteRow0Parent0Split100Sub0_nonzeroModelSourceProp_of_activeActualHornerFamily",
]

DIRECT_HORNER_SYMBOLS = [
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerSegmentCover",
    "structure Valid",
    "theorem to_directPayloadTarget",
    "theorem to_nonzeroModelSourceProp",
]

DIRECT_HORNER_SOURCE_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression",
    "theorem of_collapsed_horner_range",
    "theorem valid_of_collapsed_horner_rows",
]

ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29",
    "primaryFiniteRow0Parent0Split100Sub0_activeActualPoly_zeroExtend29_eq",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree",
]

ACTIVE_ACTUAL_DEGREE0_SOURCE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff",
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff17",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_contDiff17",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_checked_contDiff17",
    "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
]

ACTIVE_ACTUAL_SEGMENT_REMAINDER_ROW_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP"
)
ACTIVE_ACTUAL_HORNER_SEGMENT_RECEIVER_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_SEGMENT_RECEIVER_GAP"
)
ACTIVE_ACTUAL_HORNER_FAMILY_ALIGNMENT_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FAMILY_ALIGNMENT_GAP"
)
ACTIVE_ACTUAL_HORNER_STALE_SCHEMA_FAIL = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_ROW_SOURCE_STALE_RECEIVER_SCHEMA_FAIL"
)
ACTIVE_ACTUAL_HORNER_COEFF_ROWS_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_COEFF_ROWS_GAP"
)
ACTIVE_ACTUAL_HORNER_REMAINDER_ROWS_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_REMAINDER_ROWS_GAP"
)
ACTIVE_ACTUAL_HORNER_RANGE_ROWS_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_RANGE_ROWS_GAP"
)
ACTIVE_ACTUAL_HORNER_INTERVAL_BUDGET_ROWS_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_INTERVAL_BUDGET_ROWS_GAP"
)
ACTIVE_ACTUAL_HORNER_COVER_ROWS_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_COVER_ROWS_GAP"
)
ACTIVE_ACTUAL_HORNER_FINAL_BUDGET_ROWS_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FINAL_BUDGET_ROWS_GAP"
)
ACTIVE_ACTUAL_HORNER_LEAN_PAYLOAD_VALIDATION_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_LEAN_PAYLOAD_VALIDATION_GAP"
)
ACTIVE_ACTUAL_HORNER_D46_REMAINDER_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D46_UNIFORM_REMAINDER_SOURCE_GAP"
)
ACTIVE_ACTUAL_HORNER_LOW_DEGREE_REMAINDER_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_LOW_DEGREE_SEGMENT_REMAINDER_SOURCE_GAP"
)
ACTIVE_ACTUAL_HORNER_LOW_DEGREE_ALIGNMENT_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_LOW_DEGREE_TO_FIN30_ALIGNMENT_GAP"
)
ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP"
)
ACTIVE_ACTUAL_HORNER_SMOKE_SEGMENT_PAYLOAD_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_SMOKE_SEGMENT_PAYLOAD_GAP"
)


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


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


def symbol_lines(path: Path, symbols: list[str]) -> dict[str, dict[str, Any]]:
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


def compact_ledger(path: Path, keys: list[str]) -> dict[str, Any]:
    data = load_json(path)
    out: dict[str, Any] = {"path": rel(path), "exists": bool(data)}
    for key in keys:
        out[key] = data.get(key)
    return out


def active_actual_center_jet_status() -> dict[str, Any]:
    text = read_text(ACTIVE_ACTUAL_CENTER_JET_ROWS_FILE)
    return {
        "path": rel(ACTIVE_ACTUAL_CENTER_JET_ROWS_FILE),
        "exists": ACTIVE_ACTUAL_CENTER_JET_ROWS_FILE.exists(),
        "hasFin16CenterRows": "Fin 16" in text,
        "hasActiveActualCenterRowInterval": (
            "primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows"
            in text
        ),
        "availableJetOrders": "0..15",
        "usableAsLowDegreeCoefficientSeedOnly": True,
        "fullDegree29Specialization": {
            "neededForDegree29D16HornerCoeffOrders": "16..45",
            "neededUniformRemainderOrder": 46,
            "failureCode": ACTIVE_ACTUAL_HORNER_D46_REMAINDER_SOURCE_GAP,
        },
        "usableAsUniformSegmentRemainder": False,
        "failureCode": ACTIVE_ACTUAL_HORNER_LOW_DEGREE_REMAINDER_SOURCE_GAP,
    }


def build_ledger() -> dict[str, Any]:
    segment_symbols = symbol_lines(
        ACTIVE_ACTUAL_HORNER_SEGMENT_FILE,
        ACTIVE_ACTUAL_HORNER_SEGMENT_SYMBOLS,
    )
    family_symbols = symbol_lines(
        ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE,
        ACTIVE_ACTUAL_HORNER_FAMILY_SYMBOLS,
    )
    low_degree_symbols = symbol_lines(
        ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_FILE,
        ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_SYMBOLS,
    )
    degree0_symbols = symbol_lines(
        ACTIVE_ACTUAL_DEGREE0_SOURCE_FILE,
        ACTIVE_ACTUAL_DEGREE0_SOURCE_SYMBOLS,
    )
    direct_horner_symbols = symbol_lines(DIRECT_HORNER_FILE, DIRECT_HORNER_SYMBOLS)
    source_bridge_symbols = symbol_lines(
        DIRECT_HORNER_SOURCE_BRIDGE_FILE,
        DIRECT_HORNER_SOURCE_BRIDGE_SYMBOLS,
    )

    segment_receiver_ready = all_present(segment_symbols)
    family_bridge_ready = all_present(family_symbols)
    low_degree_bridge_ready = all_present(low_degree_symbols)
    degree0_source_ready = all_present(degree0_symbols)
    direct_horner_ready = all_present(direct_horner_symbols)
    source_bridge_ready = all_present(source_bridge_symbols)
    interface_ready = (
        segment_receiver_ready
        and family_bridge_ready
        and low_degree_bridge_ready
        and degree0_source_ready
        and direct_horner_ready
        and source_bridge_ready
    )

    if not segment_receiver_ready:
        first_failure = ACTIVE_ACTUAL_HORNER_SEGMENT_RECEIVER_GAP
    elif not family_bridge_ready:
        first_failure = ACTIVE_ACTUAL_HORNER_FAMILY_ALIGNMENT_GAP
    elif not low_degree_bridge_ready:
        first_failure = ACTIVE_ACTUAL_HORNER_LOW_DEGREE_ALIGNMENT_GAP
    elif not degree0_source_ready:
        first_failure = ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP
    elif not source_bridge_ready:
        first_failure = ACTIVE_ACTUAL_HORNER_STALE_SCHEMA_FAIL
    else:
        first_failure = ACTIVE_ACTUAL_SEGMENT_REMAINDER_ROW_SOURCE_GAP

    validation_gates = {
        "interfaceReady": interface_ready,
        "segmentReceiverLeanChecked": segment_receiver_ready,
        "familyBridgeLeanChecked": family_bridge_ready,
        "lowDegreeBridgeLeanChecked": low_degree_bridge_ready,
        "degree0SourceInterfaceLeanChecked": degree0_source_ready,
        "directHornerReceiverLeanChecked": direct_horner_ready,
        "collapsedSourceBridgeLeanChecked": source_bridge_ready,
        "activeActualLowDegreeSegmentRemainderSourceChecked": False,
        "activeActualD16CenterD17UniformSourceChecked": False,
        "activeActualD46UniformRemainderSourceChecked": False,
        "smokeSegmentPayloadAllowed": False,
        "allSegmentsProvided": False,
        "allCoefficientRowsRational": False,
        "activeActualRemainderRowsChecked": False,
        "hornerRangeRowsChecked": False,
        "intervalBudgetRowsChecked": False,
        "segmentCoverChecked": False,
        "finalResidualBudgetRowsChecked": False,
        "residualAbsEqualityChecked": False,
        "exactRationalArithmeticPassed": False,
        "allPayloadObligationsPassed": False,
        "directPayloadTargetChecked": False,
        "outLeanWritten": False,
        "leanValidationStatus": "not_run_rows_missing",
    }

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "active_actual_order16_horner_row_source",
        "proofStatus": (
            "interface_ready_rows_missing"
            if interface_ready
            else "receiver_interface_incomplete"
        ),
        "proofGrade": False,
        "proofSafeClosedFields": 0,
        "interfaceClosedFields": sum(1 for value in validation_gates.values() if value is True),
        "exactRationalArithmeticPassed": validation_gates[
            "exactRationalArithmeticPassed"
        ],
        "allPayloadObligationsPassed": validation_gates[
            "allPayloadObligationsPassed"
        ],
        "directPayloadTargetChecked": validation_gates["directPayloadTargetChecked"],
        "currentGap": first_failure,
        "firstFailureCode": first_failure,
        "firstConcreteSubgap": ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP,
        "outLeanWritten": False,
        "leanValidationStatus": validation_gates["leanValidationStatus"],
        "sourceFileDigests": {
            rel(ACTIVE_ACTUAL_HORNER_SEGMENT_FILE): sha256_file(
                ACTIVE_ACTUAL_HORNER_SEGMENT_FILE
            ),
            rel(ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE): sha256_file(
                ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE
            ),
            rel(ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_FILE): sha256_file(
                ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_FILE
            ),
            rel(ACTIVE_ACTUAL_DEGREE0_SOURCE_FILE): sha256_file(
                ACTIVE_ACTUAL_DEGREE0_SOURCE_FILE
            ),
            rel(DIRECT_HORNER_FILE): sha256_file(DIRECT_HORNER_FILE),
            rel(DIRECT_HORNER_SOURCE_BRIDGE_FILE): sha256_file(
                DIRECT_HORNER_SOURCE_BRIDGE_FILE
            ),
            rel(ACTIVE_ACTUAL_CENTER_JET_ROWS_FILE): sha256_file(
                ACTIVE_ACTUAL_CENTER_JET_ROWS_FILE
            ),
        },
        "targetLeanSurface": {
            "segmentDataObject": "Step33Sub0ActiveActualOrder16HornerSegmentCert",
            "segmentValidPredicate": "Step33Sub0ActiveActualOrder16HornerSegmentCert.Valid",
            "segmentReceiverTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert",
            "collapsedReceiverTheorem": "primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner",
            "familyDataObject": "Step33Sub0ActiveActualOrder16HornerFamilyCert",
            "familyValidPredicate": "Step33Sub0ActiveActualOrder16HornerFamilyCert.Valid",
            "familyBridgeTheorem": "primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily",
            "lowDegreeZeroExtendDef": "primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29",
            "lowDegreeTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree",
            "degree0CoeffDef": "primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff",
            "componentProductActualContDiff17": "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff17",
            "degree0SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder",
            "degree0SegmentTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source",
            "degree0ContDiff17SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_contDiff17",
            "degree0ContDiff17SegmentTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17",
            "degree0CheckedContDiff17SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_checked_contDiff17",
            "degree0CheckedContDiff17SegmentTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
            "payloadTargetTheorem": "primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily",
            "sourcePropTheorem": "primaryFiniteRow0Parent0Split100Sub0_nonzeroModelSourceProp_of_activeActualHornerFamily",
            "targetBudgetConstant": "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs",
            "futureLeanPayloadFileWhenRowsPass": rel(FUTURE_LEAN_OUT),
            "smokePayloadLeanFileWhenRowsPass": rel(SMOKE_PAYLOAD_LEAN_OUT),
        },
        "rowDataContract": {
            "familyFields": ["n", "residualAbs", "seg", "range"],
            "segmentFields": [
                "cellL",
                "cellU",
                "coeff : Fin 30 -> Rat",
                "polyErrorAbs",
                "polyLower",
                "polyUpper",
                "lower",
                "upper",
                "residualAbs",
            ],
            "rangeFields": [
                "stageLower : Fin (degree + 1) -> Rat",
                "stageUpper : Fin (degree + 1) -> Rat",
            ],
            "segmentValidFields": [
                "cellSubset",
                "polyErrorNonneg",
                "remainderBound for activeScale * D^16(ComponentProductActual)",
            ],
            "familyValidFields": [
                "activeValid",
                "rangeValid",
                "intervalLowerBudget",
                "intervalUpperBudget",
                "segmentResidualNonneg",
                "segmentLowerBudget",
                "segmentUpperBudget",
                "segmentBudget",
                "cover",
            ],
            "center": "1/20",
            "degree": 29,
            "cell": "Set.Icc 0 (1/10)",
            "acceptedCoefficientSources": [
                "direct degree-29 coeff : Fin 30 -> Rat",
                "low-degree coeff : Fin (d + 1) -> Rat with d <= 29, zero-extended by primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29",
            ],
        },
        "requiredRows": [
            {
                "id": "A_minus2_degree0_source_interface",
                "object": "checked degree-0 activeActual source bridge from D16 center, D17 uniform bound, and exact budget",
                "leanField": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
                "status": "checked" if degree0_source_ready else "missing",
                "remainingData": [
                    "proof-grade D16 center enclosure",
                    "proof-grade D17 uniform bound",
                    "exact rational budget comparison",
                ],
                "failureCode": ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP,
            },
            {
                "id": "A_minus1_low_degree_segment_remainder_source",
                "object": "proof-grade low-degree Taylor/Horner source for scaled D^16(ComponentProductActual); first route is degree 0",
                "leanField": "Step33Sub0ActiveActualOrder16HornerSegmentCert.Valid.remainderBound",
                "status": "missing",
                "degreePolicy": "try d = 0 before D18/D46; zero-extend into Fin30 via checked bridge",
                "analyticOrderForDegree0": "D16 center plus D17 uniform derivative source",
                "failureCode": ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP,
            },
            {
                "id": "A_minus0_low_degree_to_Fin30_bridge",
                "object": "checked coefficient/remainder transport from low-degree row to the existing degree-29 activeActual container",
                "leanField": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree",
                "status": "checked" if low_degree_bridge_ready else "missing",
                "failureCode": ACTIVE_ACTUAL_HORNER_LOW_DEGREE_ALIGNMENT_GAP,
            },
            {
                "id": "A0_segment_cover",
                "object": "cover of Set.Icc 0 (1/10)",
                "leanField": "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerSegmentCover",
                "status": "missing",
                "failureCode": ACTIVE_ACTUAL_HORNER_COVER_ROWS_GAP,
            },
            {
                "id": "A1_active_actual_coefficients",
                "object": "proof-grade low-degree coeff plus zero-extended coeff : Fin 30 -> Rat for scaled activeActual",
                "leanField": "Step33Sub0ActiveActualOrder16HornerSegmentCert.coeff",
                "status": "missing",
                "failureCode": ACTIVE_ACTUAL_HORNER_COEFF_ROWS_GAP,
            },
            {
                "id": "A2_active_actual_remainder",
                "object": "uniform activeActual order-16 segment remainder bound",
                "leanField": "Step33Sub0ActiveActualOrder16HornerSegmentCert.Valid.remainderBound",
                "status": "missing",
                "failureCode": ACTIVE_ACTUAL_HORNER_REMAINDER_ROWS_GAP,
            },
            {
                "id": "A3_horner_range",
                "object": "stageLower/stageUpper Horner bounds",
                "leanField": "Step33Sub0ActiveActualOrder16HornerDirectRangeCert.Valid",
                "status": "missing",
                "failureCode": ACTIVE_ACTUAL_HORNER_RANGE_ROWS_GAP,
            },
            {
                "id": "A4_interval_budget",
                "object": "polyLower/polyUpper/lower/upper interval budget rows",
                "leanField": "intervalLowerBudget and intervalUpperBudget",
                "status": "missing",
                "failureCode": ACTIVE_ACTUAL_HORNER_INTERVAL_BUDGET_ROWS_GAP,
            },
            {
                "id": "A5_final_budget",
                "object": "segment residualAbs <= family residualAbs and residualAbs equals target budget",
                "leanField": "segmentBudget plus hResidualAbs",
                "status": "missing",
                "failureCode": ACTIVE_ACTUAL_HORNER_FINAL_BUDGET_ROWS_GAP,
            },
        ],
        "validationGates": validation_gates,
        "failurePriority": [
            ACTIVE_ACTUAL_HORNER_STALE_SCHEMA_FAIL,
            ACTIVE_ACTUAL_HORNER_SEGMENT_RECEIVER_GAP,
            ACTIVE_ACTUAL_HORNER_FAMILY_ALIGNMENT_GAP,
            ACTIVE_ACTUAL_HORNER_LOW_DEGREE_ALIGNMENT_GAP,
            ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP,
            ACTIVE_ACTUAL_SEGMENT_REMAINDER_ROW_SOURCE_GAP,
            ACTIVE_ACTUAL_HORNER_LOW_DEGREE_REMAINDER_SOURCE_GAP,
            ACTIVE_ACTUAL_HORNER_D46_REMAINDER_SOURCE_GAP,
            ACTIVE_ACTUAL_HORNER_SMOKE_SEGMENT_PAYLOAD_GAP,
            ACTIVE_ACTUAL_HORNER_COEFF_ROWS_GAP,
            ACTIVE_ACTUAL_HORNER_REMAINDER_ROWS_GAP,
            ACTIVE_ACTUAL_HORNER_RANGE_ROWS_GAP,
            ACTIVE_ACTUAL_HORNER_INTERVAL_BUDGET_ROWS_GAP,
            ACTIVE_ACTUAL_HORNER_COVER_ROWS_GAP,
            ACTIVE_ACTUAL_HORNER_FINAL_BUDGET_ROWS_GAP,
            ACTIVE_ACTUAL_HORNER_LEAN_PAYLOAD_VALIDATION_GAP,
        ],
        "directLedgerInputs": {
            "directPayload": compact_ledger(
                DIRECT_PAYLOAD_LEDGER,
                [
                    "schema",
                    "proofGrade",
                    "currentGap",
                    "firstConcreteUpstreamFailureCode",
                    "firstFailureCode",
                ],
            ),
            "directCertificate": compact_ledger(
                DIRECT_CERTIFICATE_LEDGER,
                [
                    "schema",
                    "proofGrade",
                    "currentGap",
                    "firstConcreteUpstreamFailureCode",
                    "firstFailureCode",
                ],
            ),
        },
        "computerUseDecision": {
            "used": True,
            "advisoryOnly": True,
            "recommendedOption": "A",
            "decision": (
                "Synchronize a fail-closed activeActual Horner row-source "
                "generator with the checked receiver before emitting any Lean "
                "payload."
            ),
            "notProofEvidence": True,
        },
        "latestComputerUsePayloadDecision": {
            "used": True,
            "advisoryOnly": True,
            "recommendedOption": "B",
            "decision": (
                "Add/use a low-degree-to-Fin30 bridge before building any D46 "
                "backend.  The degree-29 container can carry a lower-degree "
                "activeActual source row."
            ),
            "firstFailureCodeIfRowsMissing": (
                ACTIVE_ACTUAL_HORNER_LOW_DEGREE_REMAINDER_SOURCE_GAP
            ),
            "notProofEvidence": True,
        },
        "latestComputerUseDegree0SourceDecision": {
            "used": True,
            "advisoryOnly": True,
            "recommendedOption": "A",
            "decision": (
                "Implement a degree-0 activeActual D16 source bridge before "
                "degree-1, D18, or D46 machinery."
            ),
            "firstFailureCodeIfDataMissing": (
                ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP
            ),
            "notProofEvidence": True,
        },
        "availableUpstreamEvidence": {
            "activeActualCenterJetRows": active_actual_center_jet_status(),
        },
        "degree29ContainerPolicy": {
            "targetFunction": "activeScale * D^16(ComponentProductActual)",
            "containerDegree": 29,
            "containerCoeffType": "Fin 30 -> Rat",
            "lowDegreeAccepted": low_degree_bridge_ready,
            "lowDegreeBridge": rel(ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_FILE),
            "zeroExtendDef": "primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29",
            "transferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree",
            "firstMissingSubgap": ACTIVE_ACTUAL_HORNER_LOW_DEGREE_REMAINDER_SOURCE_GAP,
            "degree0SourceBridge": rel(ACTIVE_ACTUAL_DEGREE0_SOURCE_FILE),
            "componentProductActualContDiff17": "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff17",
            "degree0SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder",
            "degree0SegmentTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source",
            "degree0ContDiff17SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_contDiff17",
            "degree0ContDiff17SegmentTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17",
            "degree0CheckedContDiff17SourceTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_degree0_remainder_of_checked_contDiff17",
            "degree0CheckedContDiff17SegmentTransferTheorem": "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17",
            "firstConcreteSubgap": ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP,
            "fullDegree29Specialization": {
                "coefficientJetOrdersNeeded": "16..45",
                "uniformRemainderDerivativeOrderNeeded": 46,
                "firstMissingSubgapIfChosen": ACTIVE_ACTUAL_HORNER_D46_REMAINDER_SOURCE_GAP,
            },
        },
        "smokeSegmentPayloadGate": {
            "recommendedScript": rel(SMOKE_PAYLOAD_SCRIPT),
            "ledgerJson": rel(SMOKE_PAYLOAD_JSON),
            "ledgerMarkdown": rel(SMOKE_PAYLOAD_MD),
            "targetLeanFileWhenRowsPass": rel(SMOKE_PAYLOAD_LEAN_OUT),
            "firstDataObject": (
                "primaryFiniteRow0Parent0Split100Sub0ActiveActualOrder16HornerSegment0"
            ),
            "firstValidityTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment0_valid"
            ),
            "firstRemainderTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment0_remainder_generated"
            ),
            "status": "blocked_missing_d16_center_d17_uniform_source",
            "payloadAllowed": False,
            "outLeanWritten": False,
            "failureCode": ACTIVE_ACTUAL_HORNER_D16_CENTER_D17_SOURCE_GAP,
        },
        "doNotUseAsProof": [
            "sampled or float rows",
            "activeActual center jets as uniform segment bounds",
            "killed factor-majorant budgets",
            "P45/full-Taylor wrong-target rows",
            "separate activeActual and nominal independent norm budgets",
            "DirectConcretePayload.lean before this ledger has all payload obligations passed",
            "D46 backend as mandatory before the low-degree source is tested",
        ],
        "nextImplementablePatch": (
            "Fill the degree-0 source inputs: a proof-grade D16 center "
            "enclosure, a proof-grade D17 uniform bound, and the exact rational budget comparison; "
            "then instantiate the checked degree-0 theorem and zero-extend into "
            "the existing Fin30 Horner family."
        ),
    }


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Active-Actual Horner Row-Source Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Verdict",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- proofSafeClosedFields: `{ledger['proofSafeClosedFields']}`",
        f"- interfaceClosedFields: `{ledger['interfaceClosedFields']}`",
        f"- outLeanWritten: `{ledger['outLeanWritten']}`",
        f"- leanValidationStatus: `{ledger['leanValidationStatus']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- firstFailureCode: `{ledger['firstFailureCode']}`",
        f"- firstConcreteSubgap: `{ledger['firstConcreteSubgap']}`",
        "",
        "## Target Lean Surface",
        "",
    ]
    for key, value in ledger["targetLeanSurface"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Row Data Contract", ""])
    contract = ledger["rowDataContract"]
    for key, value in contract.items():
        if isinstance(value, list):
            lines.append(f"### {key}")
            lines.append("")
            for item in value:
                lines.append(f"- {item}")
            lines.append("")
        else:
            lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Required Rows", ""])
    for row in ledger["requiredRows"]:
        lines.append(f"### {row['id']}")
        lines.append("")
        for key, value in row.items():
            if key == "id":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")

    lines.extend(["## Validation Gates", ""])
    for key, value in ledger["validationGates"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Failure Priority", ""])
    for code in ledger["failurePriority"]:
        lines.append(f"- `{code}`")

    lines.extend(["", "## Symbol Audit", ""])
    for path, symbols in {
        rel(ACTIVE_ACTUAL_HORNER_SEGMENT_FILE): symbol_lines(
            ACTIVE_ACTUAL_HORNER_SEGMENT_FILE,
            ACTIVE_ACTUAL_HORNER_SEGMENT_SYMBOLS,
        ),
        rel(ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE): symbol_lines(
            ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE,
            ACTIVE_ACTUAL_HORNER_FAMILY_SYMBOLS,
        ),
        rel(ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_FILE): symbol_lines(
            ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_FILE,
            ACTIVE_ACTUAL_LOW_DEGREE_BRIDGE_SYMBOLS,
        ),
        rel(ACTIVE_ACTUAL_DEGREE0_SOURCE_FILE): symbol_lines(
            ACTIVE_ACTUAL_DEGREE0_SOURCE_FILE,
            ACTIVE_ACTUAL_DEGREE0_SOURCE_SYMBOLS,
        ),
        rel(DIRECT_HORNER_FILE): symbol_lines(DIRECT_HORNER_FILE, DIRECT_HORNER_SYMBOLS),
        rel(DIRECT_HORNER_SOURCE_BRIDGE_FILE): symbol_lines(
            DIRECT_HORNER_SOURCE_BRIDGE_FILE,
            DIRECT_HORNER_SOURCE_BRIDGE_SYMBOLS,
        ),
    }.items():
        lines.append(f"### {path}")
        lines.append("")
        for symbol, info in symbols.items():
            lines.append(
                f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
            )
        lines.append("")

    lines.extend(["## Source File Digests", ""])
    for path, digest in ledger["sourceFileDigests"].items():
        lines.append(f"- `{path}`: `{digest}`")

    lines.extend(["", "## Direct Ledger Inputs", ""])
    for name, data in ledger["directLedgerInputs"].items():
        lines.append(f"### {name}")
        lines.append("")
        for key, value in data.items():
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")

    decision = ledger["computerUseDecision"]
    lines.extend(
        [
            "## Computer Use Decision",
            "",
            f"- used: `{decision['used']}`",
            f"- advisoryOnly: `{decision['advisoryOnly']}`",
            f"- recommendedOption: `{decision['recommendedOption']}`",
            f"- decision: {decision['decision']}",
            f"- notProofEvidence: `{decision['notProofEvidence']}`",
            "",
            "## Do Not Use As Proof",
            "",
        ]
    )
    for item in ledger["doNotUseAsProof"]:
        lines.append(f"- {item}")

    latest = ledger["latestComputerUsePayloadDecision"]
    lines.extend(
        [
            "",
            "## Latest Computer Use Payload Decision",
            "",
            f"- used: `{latest['used']}`",
            f"- advisoryOnly: `{latest['advisoryOnly']}`",
            f"- recommendedOption: `{latest['recommendedOption']}`",
            f"- decision: {latest['decision']}",
            f"- firstFailureCodeIfRowsMissing: `{latest['firstFailureCodeIfRowsMissing']}`",
            f"- notProofEvidence: `{latest['notProofEvidence']}`",
            "",
            "## Degree-29 Container Policy",
            "",
        ]
    )
    for key, value in ledger["degree29ContainerPolicy"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Smoke Segment Payload Gate", ""])
    for key, value in ledger["smokeSegmentPayloadGate"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Available Upstream Evidence", ""])
    active = ledger["availableUpstreamEvidence"]["activeActualCenterJetRows"]
    lines.append("### activeActualCenterJetRows")
    lines.append("")
    for key, value in active.items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(
        [
            "",
            "## Next Implementable Patch",
            "",
            str(ledger["nextImplementablePatch"]),
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(f"wrote {rel(JSON_OUT)}")
    print(f"wrote {rel(MD_OUT)}")
    print(ledger["proofStatus"])
    print(ledger["firstFailureCode"])

    if ledger["validationGates"]["allPayloadObligationsPassed"]:
        raise SystemExit(
            "payload obligations are marked passed, but Lean emission is not "
            "implemented in this fail-closed ledger"
        )


if __name__ == "__main__":
    main()
