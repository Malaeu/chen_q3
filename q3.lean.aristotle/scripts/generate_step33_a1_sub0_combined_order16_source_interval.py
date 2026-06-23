#!/usr/bin/env python3
"""Fail-closed ledger for the Step33A.1-A direct order-16 source interval route.

This records the route-review choice after the direct zero-model bridge:
build proof-grade signed interval rows for the whole assembled order-16 source,
then feed the resulting absolute bound into the existing zero-model
`hRemainder` bridge.

The script does not emit concrete rows and does not claim Step33A.1-A closure.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path


SCHEMA = "q3_psdpd_step33_a1_sub0_combined_order16_source_interval.v1"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

CERT_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SourceIntervalCert.lean"
PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SourceIntervalPayload.lean"
)
DIRECT_MODEL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectModelPayload.lean"
)
JSON_OUT = REQUEST_DIR / "step33_a1_sub0_combined_order16_source_interval.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_combined_order16_source_interval.md"

CERT_SYMBOLS = [
    "Step33Sub0CombinedCancellationOrder16SourceSegmentCert",
    "structure Valid",
    "to_componentSource_abs_on_segment",
    "Step33Sub0CombinedCancellationOrder16SourceSegmentCover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_abs_of_segment_cover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_segment_cover",
]

DIRECT_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_componentSource_abs",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_remainder",
]

PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegment",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegments",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16SourceWholeCell_cover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16SourceWholeCell_valid_of_direct_interval",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_wholeCell_direct_interval",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_wholeCell_direct_interval",
]


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    if not path.exists():
        return {symbol: False for symbol in symbols}
    text = path.read_text(encoding="utf-8")
    return {symbol: symbol in text for symbol in symbols}


def all_true(items: dict[str, bool]) -> bool:
    return all(items.values())


def build_ledger() -> dict[str, object]:
    cert_symbols = file_contains(CERT_FILE, CERT_SYMBOLS)
    payload_symbols = file_contains(PAYLOAD_FILE, PAYLOAD_SYMBOLS)
    direct_bridge_symbols = file_contains(DIRECT_MODEL_FILE, DIRECT_BRIDGE_SYMBOLS)
    checker_present = all_true(cert_symbols)
    whole_cell_payload_present = all_true(payload_symbols)
    direct_bridge_present = all_true(direct_bridge_symbols)

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "certFile": str(CERT_FILE.relative_to(ROOT)),
        "payloadFile": str(PAYLOAD_FILE.relative_to(ROOT)),
        "directModelFile": str(DIRECT_MODEL_FILE.relative_to(ROOT)),
        "route": "direct_signed_whole_source_interval_for_zero_model",
        "proofStatus": "whole_cell_receiver_checked_missing_signed_source_interval",
        "sourceIntervalCheckerPresent": checker_present,
        "wholeCellPayloadPresent": whole_cell_payload_present,
        "zeroModelRemainderBridgePresent": direct_bridge_present,
        "certSymbols": cert_symbols,
        "payloadSymbols": payload_symbols,
        "directBridgeSymbols": direct_bridge_symbols,
        "signedFactorRowsLeanChecked": False,
        "wholeSourceAssemblyLeanChecked": False,
        "globalCoverLeanChecked": whole_cell_payload_present,
        "zeroModelAbsBoundLeanChecked": False,
        "zeroModelIntervalDataValidReceiverPresent": whole_cell_payload_present,
        "directIntervalValidClaimed": False,
        "sourceIntervalCertValidClaimed": False,
        "step33A1ClosedClaimed": False,
        "proofGrade": False,
        "currentGap": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP"
        ),
        "nextProofObject": (
            "proof-grade signed factor derivative rows, exact Leibniz term interval "
            "rows, and active-scale sourceAssembly rows instantiating the signed "
            "whole-source interval for the concrete whole-cell zero-model segment"
        ),
        "refinedByLedger": (
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_combined_order16_signed_factor_rows.json"
        ),
        "failureCodeIfRowsMissing": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP"
        ),
        "failureCodeIfZeroModelTooSmall": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_ZERO_MODEL_CONSTANT_FAIL"
        ),
        "guard": (
            "Do not use sampled intervals or independent product-summand norm "
            "bounds as proof; the source intervals must bound the whole assembled "
            "signed expression."
        ),
    }


def render_markdown(ledger: dict[str, object]) -> str:
    cert_symbols = ledger["certSymbols"]
    payload_symbols = ledger["payloadSymbols"]
    bridge_symbols = ledger["directBridgeSymbols"]
    assert isinstance(cert_symbols, dict)
    assert isinstance(payload_symbols, dict)
    assert isinstance(bridge_symbols, dict)

    lines = [
        "# Step33A.1-A Combined Order16 Source Interval Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Present",
        "",
        f"- sourceIntervalCheckerPresent: `{ledger['sourceIntervalCheckerPresent']}`",
        f"- wholeCellPayloadPresent: `{ledger['wholeCellPayloadPresent']}`",
        f"- zeroModelRemainderBridgePresent: `{ledger['zeroModelRemainderBridgePresent']}`",
        "",
        "## Checker Symbols",
        "",
    ]
    for symbol, present in cert_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Whole-Cell Payload Symbols", ""])
    for symbol, present in payload_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Direct Bridge Symbols", ""])
    for symbol, present in bridge_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(
        [
            "",
            "## Missing Proof Payload",
            "",
            f"- signedFactorRowsLeanChecked: `{ledger['signedFactorRowsLeanChecked']}`",
            f"- wholeSourceAssemblyLeanChecked: `{ledger['wholeSourceAssemblyLeanChecked']}`",
            f"- globalCoverLeanChecked: `{ledger['globalCoverLeanChecked']}`",
            f"- zeroModelAbsBoundLeanChecked: `{ledger['zeroModelAbsBoundLeanChecked']}`",
            "- zeroModelIntervalDataValidReceiverPresent: "
            f"`{ledger['zeroModelIntervalDataValidReceiverPresent']}`",
            f"- directIntervalValidClaimed: `{ledger['directIntervalValidClaimed']}`",
            f"- sourceIntervalCertValidClaimed: `{ledger['sourceIntervalCertValidClaimed']}`",
            f"- step33A1ClosedClaimed: `{ledger['step33A1ClosedClaimed']}`",
            f"- proofGrade: `{ledger['proofGrade']}`",
            "",
            "## Current Gap",
            "",
            f"`{ledger['currentGap']}`",
            "",
            "## Next Proof Object",
            "",
            str(ledger["nextProofObject"]),
            "",
            "## Refined By",
            "",
            str(ledger["refinedByLedger"]),
            "",
            "## Failure Codes",
            "",
            f"- rows missing: `{ledger['failureCodeIfRowsMissing']}`",
            f"- zero-model too small: `{ledger['failureCodeIfZeroModelTooSmall']}`",
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
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(JSON_OUT)
    print(MD_OUT)


if __name__ == "__main__":
    main()
