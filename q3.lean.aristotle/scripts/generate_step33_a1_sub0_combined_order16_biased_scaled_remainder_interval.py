#!/usr/bin/env python3
"""Fail-closed ledger for the biased scaled-remainder interval route.

The target is the complete signed expression

    ActiveScaleCoeff * D^16(ComponentProductCancellationResidual)
      + (ActiveScaleCoeff - NominalScaleCoeff) * D^16(ComponentProductNominal)

as exposed by the residual-Horner remainder bridge.  This script does not emit
proof rows and does not claim Step33A.1-A closure.  It records the exact
generator-facing surface and reports the first missing proof-grade certificate.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_combined_order16_"
    "biased_scaled_remainder_interval.v1"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderIntervalPayload.lean"
)
REMAINDER_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerRemainderBridge.lean"
)

HORNER_LEDGER_JSON = REQUEST_DIR / "step33_a1_sub0_biased_residual_horner_payload.json"
SEGMENTED_RESIDUAL_JSON = (
    REQUEST_DIR / "step33_a1_sub0_segmented_residual_deriv_interval_payload.json"
)
ORDER16_DIRECT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_combined_cancellation_order16_direct_payload.json"
)
SIGNED_FACTOR_JSON = (
    REQUEST_DIR / "step33_a1_sub0_combined_order16_signed_factor_rows.json"
)
BIASED_SIGNED_FACTOR_JSON = (
    REQUEST_DIR / "step33_a1_sub0_biased_residual_signed_factor_segments.json"
)

JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.md"
)

PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert",
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCover",
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderSourceProp_of_interval_payload_target",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_interval_payload",
]

REMAINDER_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound",
]

CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_"
    "SCALED_REMAINDER_BOUND_GAP"
)
PARENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_"
    "REMAINDER_ROWS_GAP"
)
FIRST_FAILURE = "INTERVAL_CERT_GAP"


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


def summarize_ledger(path: Path, keys: list[str]) -> dict[str, Any]:
    data = load_json(path)
    summary: dict[str, Any] = {
        "path": rel(path),
        "exists": bool(data),
    }
    for key in keys:
        summary[key] = data.get(key)
    return summary


def summarize_segmented_residual_ledger(path: Path) -> dict[str, Any]:
    data = load_json(path)
    arithmetic = data.get("candidateArithmeticStatus", {})
    if not isinstance(arithmetic, dict):
        arithmetic = {}
    return {
        "path": rel(path),
        "exists": bool(data),
        "status": data.get("status"),
        "proofMode": data.get("proofMode"),
        "budgetPassedExactRational": arithmetic.get("budgetPassedExactRational"),
        "candidateReadyForLeanShape": arithmetic.get("candidateReadyForLeanShape"),
        "sameExpressionResidualIntervalProofPresent": arithmetic.get(
            "sameExpressionResidualIntervalProofPresent"
        ),
        "proofGradeFullTaylorResidualBoundsPresent": arithmetic.get(
            "proofGradeFullTaylorResidualBoundsPresent"
        ),
        "proofGradeResidualBoundsPresent": arithmetic.get(
            "proofGradeResidualBoundsPresent"
        ),
    }


def build_ledger() -> dict[str, Any]:
    payload_symbols = file_contains(PAYLOAD_FILE, PAYLOAD_SYMBOLS)
    remainder_bridge_symbols = file_contains(
        REMAINDER_BRIDGE_FILE, REMAINDER_BRIDGE_SYMBOLS
    )
    payload_interface_ready = all_true(payload_symbols)
    remainder_bridge_ready = all_true(remainder_bridge_symbols)

    upstream = {
        "residualHornerLedger": summarize_ledger(
            HORNER_LEDGER_JSON,
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "scaledRemainderBoundLeanChecked",
                "residualRemainderInterfaceLeanChecked",
            ],
        ),
        "segmentedResidualDerivativeLedger": summarize_segmented_residual_ledger(
            SEGMENTED_RESIDUAL_JSON
        ),
        "order16DirectLedger": summarize_ledger(
            ORDER16_DIRECT_JSON,
            [
                "proofStatus",
                "currentGap",
                "sourceIntervalCertValidClaimed",
                "step33A1ClosedClaimed",
            ],
        ),
        "signedFactorLedger": summarize_ledger(
            SIGNED_FACTOR_JSON,
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "signedFactorRowsLeanChecked",
                "sourceAssemblyRowsLeanChecked",
            ],
        ),
        "biasedSignedFactorLedger": summarize_ledger(
            BIASED_SIGNED_FACTOR_JSON,
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "concreteSegmentsLeanChecked",
                "residualSourcePropClaimed",
            ],
        ),
    }

    proof_status = (
        "biased_scaled_remainder_interval_surface_checked_missing_interval_cert"
        if payload_interface_ready and remainder_bridge_ready
        else "biased_scaled_remainder_interval_surface_incomplete"
    )

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "biased_scaled_remainder_whole_expression_interval",
        "payloadFile": rel(PAYLOAD_FILE),
        "remainderBridgeFile": rel(REMAINDER_BRIDGE_FILE),
        "payloadSymbols": payload_symbols,
        "remainderBridgeSymbols": remainder_bridge_symbols,
        "payloadInterfacePresent": payload_interface_ready,
        "remainderBridgePresent": remainder_bridge_ready,
        "proofStatus": proof_status,
        "currentGap": CURRENT_GAP,
        "parentGap": PARENT_GAP,
        "firstFailureCode": FIRST_FAILURE,
        "proofGrade": False,
        "wholeExpressionIntervalRowsLeanChecked": False,
        "segmentCoverLeanChecked": False,
        "budgetRowsLeanChecked": False,
        "scaledRemainderSourcePropClaimed": False,
        "residualRemainderRowsClaimed": False,
        "step33A1ClosedClaimed": False,
        "doNotSplitSummands": True,
        "certificateShape": [
            "per segment: cellL, cellU, lower, upper, remainderAbs",
            "proof-grade interval for the complete signed scaled remainder",
            "-remainderAbs <= lower",
            "upper <= remainderAbs",
            "finite segment cover of [0, 1/10]",
            "global residualAbs equal to BiasedResidualRemainderAbs",
        ],
        "targetProp": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHorner"
            "ScaledRemainderSourceProp"
        ),
        "targetPayload": (
            "primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderInterval"
            "PayloadTarget"
        ),
        "upstreamEvidence": upstream,
        "guard": (
            "This ledger is not proof evidence.  Do not split the two analytic "
            "summands as the primary route and do not claim residual-Horner "
            "family Valid until a proof-grade whole-expression interval "
            "certificate instantiates the payload target."
        ),
        "nextProofObject": (
            "A rational/interval certificate for the complete signed scaled "
            "remainder expression on [0,1/10], feeding "
            "primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderInterval"
            "PayloadTarget."
        ),
    }


def render_symbols(title: str, symbols: dict[str, bool]) -> list[str]:
    lines = ["", f"## {title}", ""]
    lines.extend(f"- `{symbol}`: `{present}`" for symbol, present in symbols.items())
    return lines


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Biased Scaled-Remainder Interval Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Status",
        "",
        f"- payloadInterfacePresent: `{ledger['payloadInterfacePresent']}`",
        f"- remainderBridgePresent: `{ledger['remainderBridgePresent']}`",
        f"- proofGrade: `{ledger['proofGrade']}`",
        "- wholeExpressionIntervalRowsLeanChecked: "
        f"`{ledger['wholeExpressionIntervalRowsLeanChecked']}`",
        f"- segmentCoverLeanChecked: `{ledger['segmentCoverLeanChecked']}`",
        f"- budgetRowsLeanChecked: `{ledger['budgetRowsLeanChecked']}`",
        "- scaledRemainderSourcePropClaimed: "
        f"`{ledger['scaledRemainderSourcePropClaimed']}`",
        "- residualRemainderRowsClaimed: "
        f"`{ledger['residualRemainderRowsClaimed']}`",
        f"- step33A1ClosedClaimed: `{ledger['step33A1ClosedClaimed']}`",
        f"- doNotSplitSummands: `{ledger['doNotSplitSummands']}`",
    ]

    lines.extend(render_symbols("Payload Symbols", ledger["payloadSymbols"]))
    lines.extend(
        render_symbols("Remainder Bridge Symbols", ledger["remainderBridgeSymbols"])
    )

    lines.extend(
        [
            "",
            "## Current Gap",
            "",
            f"`{ledger['currentGap']}`",
            "",
            "Parent gap:",
            "",
            f"`{ledger['parentGap']}`",
            "",
            "First failure code if the new route fails:",
            "",
            f"`{ledger['firstFailureCode']}`",
            "",
            "## Certificate Shape",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in ledger["certificateShape"])

    lines.extend(
        [
            "",
            "## Upstream Evidence",
            "",
        ]
    )
    for name, summary in ledger["upstreamEvidence"].items():
        lines.append(f"### {name}")
        lines.append("")
        for key, value in summary.items():
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")

    lines.extend(
        [
            "## Next Proof Object",
            "",
            str(ledger["nextProofObject"]),
            "",
            "## Guard",
            "",
            str(ledger["guard"]),
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(ledger["proofStatus"])
    print(ledger["firstFailureCode"])
    print(ledger["currentGap"])


if __name__ == "__main__":
    main()
