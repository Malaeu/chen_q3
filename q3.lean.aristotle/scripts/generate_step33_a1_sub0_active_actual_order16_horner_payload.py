#!/usr/bin/env python3
"""Fail-closed activeActual order-16 Horner payload entrypoint.

This is the first generator-facing surface for the payload requested by the
activeActual Horner family bridge.  It deliberately refuses to emit Lean until a
proof-grade rational/interval source supplies the degree-29 coefficient row for
`activeScale * D^16(ComponentProductActual)` and a uniform order-46 remainder
bound on the smoke segment.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_active_actual_order16_horner_payload.v1"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

ROW_SOURCE_JSON = REQUEST_DIR / "step33_a1_sub0_active_actual_horner_row_source.json"
JSON_OUT = REQUEST_DIR / "step33_a1_sub0_active_actual_order16_horner_payload.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_active_actual_order16_horner_payload.md"

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
FUTURE_PAYLOAD_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerPayload.lean"
)

ROW_SOURCE_GAP = "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP"
D46_SOURCE_GAP = "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D46_UNIFORM_REMAINDER_SOURCE_GAP"
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
        "neededCoefficientOrders": "16..45",
        "neededRemainderOrder": 46,
        "usableForSmokeSegmentRemainder": False,
    }


def build_ledger() -> dict[str, Any]:
    row_source = load_json(ROW_SOURCE_JSON)
    segment_symbols = symbol_audit(SEGMENT_RECEIVER_LEAN, REQUIRED_SEGMENT_SYMBOLS)
    family_symbols = symbol_audit(FAMILY_BRIDGE_LEAN, REQUIRED_FAMILY_SYMBOLS)
    segment_ready = all_present(segment_symbols)
    family_ready = all_present(family_symbols)
    interface_ready = segment_ready and family_ready

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
            "id": "S1_activeActual_coefficients",
            "status": "missing",
            "required": "Rat coefficients for activeScale * D^16(ComponentProductActual)",
            "orders": "16..45",
            "failureCode": D46_SOURCE_GAP,
        },
        {
            "id": "S2_uniform_remainder",
            "status": "missing",
            "required": "uniform segment remainder for the degree-29 D16 Taylor/Horner row",
            "derivativeOrder": 46,
            "failureCode": D46_SOURCE_GAP,
        },
        {
            "id": "S3_horner_range_rows",
            "status": "blocked_on_S1_S2",
            "required": "stageLower/stageUpper rows for the converted direct segment",
            "failureCode": ROW_SOURCE_GAP,
        },
        {
            "id": "S4_budget_rows",
            "status": "blocked_on_S1_S2",
            "required": "polyLower/polyUpper/lower/upper/residualAbs rows",
            "failureCode": ROW_SOURCE_GAP,
        },
    ]

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "active_actual_order16_horner_payload_smoke_segment",
        "proofStatus": "blocked_missing_D46_uniform_remainder_source",
        "proofGrade": False,
        "proofSafeClosedFields": 0,
        "interfaceReady": interface_ready,
        "outLeanWritten": False,
        "targetLeanFileWhenRowsPass": rel(FUTURE_PAYLOAD_LEAN),
        "currentGap": ROW_SOURCE_GAP,
        "firstFailureCode": ROW_SOURCE_GAP,
        "firstConcreteSubgap": D46_SOURCE_GAP,
        "leanValidationStatus": "not_run_payload_not_emitted",
        "sourceFileDigests": {
            rel(SEGMENT_RECEIVER_LEAN): sha256_file(SEGMENT_RECEIVER_LEAN),
            rel(FAMILY_BRIDGE_LEAN): sha256_file(FAMILY_BRIDGE_LEAN),
            rel(ACTIVE_CENTER_ROWS_LEAN): sha256_file(ACTIVE_CENTER_ROWS_LEAN),
            rel(ROW_SOURCE_JSON): sha256_file(ROW_SOURCE_JSON),
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
        },
        "degree29D16Requirement": {
            "targetFunction": "activeScale * D^16(ComponentProductActual)",
            "coefficientJetOrdersNeeded": "16..45",
            "uniformRemainderDerivativeOrderNeeded": 46,
            "currentProofGradeCenterRows": "0..15 only",
            "firstMissingCoefficientOrder": 16,
            "whyCenterJetsAreNotEnough": (
                "The available activeActual center rows are center-jet interval "
                "facts through Fin 16; the smoke payload needs a uniform "
                "degree-29 row for D16(actual), hence coefficients through "
                "order 45 and a remainder bound at order 46."
            ),
        },
        "availableUpstreamEvidence": {
            "activeActualCenterJetRows": center_row_status(),
        },
        "requiredInputs": required_inputs,
        "validationGates": {
            "segmentReceiverReady": segment_ready,
            "familyBridgeReady": family_ready,
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
            "decision": (
                "Build a rational/interval activeActual coefficient+remainder "
                "row generator directly against "
                "Step33Sub0ActiveActualOrder16HornerFamilyCert.Valid."
            ),
            "notProofEvidence": True,
        },
        "doNotUseAsProof": [
            "sampled activeActual rows",
            "center-jet rows as uniform segment remainder rows",
            "coarse P45/factor-majorant route",
            "separate activeActual and nominal error budgets",
            "Lean payload file before S1/S2 proof-grade inputs exist",
        ],
        "nextImplementablePatch": (
            "Produce a proof-grade source for the smoke segment: rational "
            "coefficients for orders 16..45 of activeScale * "
            "D^16(ComponentProductActual), plus a uniform order-46 remainder "
            "bound.  Then this generator may emit the isolated Lean payload."
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

    lines.extend(["", "## Degree-29 D16 Requirement", ""])
    for key, value in ledger["degree29D16Requirement"].items():
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

    lines.extend(["", "## Do Not Use As Proof", ""])
    for item in ledger["doNotUseAsProof"]:
        lines.append(f"- {item}")

    lines.extend(["", "## Next Implementable Patch", ""])
    lines.append(ledger["nextImplementablePatch"])
    lines.append("")
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
    print(ledger["firstConcreteSubgap"])

    if ledger["validationGates"]["allPayloadObligationsPassed"]:
        raise SystemExit(
            "payload obligations are marked passed, but Lean emission is not "
            "implemented in this fail-closed gate"
        )


if __name__ == "__main__":
    main()
