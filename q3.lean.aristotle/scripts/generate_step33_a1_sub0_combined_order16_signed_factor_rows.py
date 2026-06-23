#!/usr/bin/env python3
"""Fail-closed ledger for the Step33A.1-A order-16 signed-factor route.

The Lean checker now knows how to derive signed Leibniz term rows from
proof-grade signed factor rows plus endpoint corner arithmetic, then assemble
one segment into the existing whole-source segment certificate.  This script
records that checked interface and makes the remaining payload gap explicit.

It does not emit numerical rows and does not claim Step33A.1-A closure.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path


SCHEMA = "q3_psdpd_step33_a1_sub0_combined_order16_signed_factor_rows.v1"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

CHECKER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SignedFactorChecker.lean"
)
ABS_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SignedFactorAbsBridge.lean"
)
SOURCE_INTERVAL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SourceIntervalCert.lean"
)
PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SourceIntervalPayload.lean"
)
BUDGET_AUDIT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean"
)
JSON_OUT = REQUEST_DIR / "step33_a1_sub0_combined_order16_signed_factor_rows.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_combined_order16_signed_factor_rows.md"

CHECKER_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm",
    "primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm",
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_signedLeibniz",
    "Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert",
    "leftTermCornerRows",
    "rightTermCornerRows",
    "toSourceSegment",
    "structure Valid",
    "factorRows",
    "leftTermCorners",
    "rightTermCorners",
    "sourceAssembly",
    "zeroModelBudget",
    "theorem to_leftTermRows",
    "theorem to_rightTermRows",
    "theorem to_sourceInterval",
    "theorem to_sourceSegmentValid",
    "Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_signedFactor_segment_cover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_signedFactor_segment_cover",
]

ABS_BRIDGE_SYMBOLS = [
    "centeredTaylorAbsEnclosures",
    "factorRows_of_centeredTaylorAbsEnclosures",
]

SOURCE_INTERVAL_SYMBOLS = [
    "Step33Sub0CombinedCancellationOrder16SourceSegmentCert",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_segment_cover",
]

PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_wholeCell_direct_interval",
]

BUDGET_KILL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail_rat",
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail",
]


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    if not path.exists():
        return {symbol: False for symbol in symbols}
    text = path.read_text(encoding="utf-8")
    return {symbol: symbol in text for symbol in symbols}


def all_true(items: dict[str, bool]) -> bool:
    return all(items.values())


def build_ledger() -> dict[str, object]:
    checker_symbols = file_contains(CHECKER_FILE, CHECKER_SYMBOLS)
    abs_bridge_symbols = file_contains(ABS_BRIDGE_FILE, ABS_BRIDGE_SYMBOLS)
    source_interval_symbols = file_contains(SOURCE_INTERVAL_FILE, SOURCE_INTERVAL_SYMBOLS)
    payload_symbols = file_contains(PAYLOAD_FILE, PAYLOAD_SYMBOLS)
    budget_kill_symbols = file_contains(BUDGET_AUDIT_FILE, BUDGET_KILL_SYMBOLS)
    checker_present = all_true(checker_symbols)
    abs_bridge_present = all_true(abs_bridge_symbols)
    budget_kill_present = all_true(budget_kill_symbols)

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "checkerFile": str(CHECKER_FILE.relative_to(ROOT)),
        "absBridgeFile": str(ABS_BRIDGE_FILE.relative_to(ROOT)),
        "budgetAuditFile": str(BUDGET_AUDIT_FILE.relative_to(ROOT)),
        "sourceIntervalFile": str(SOURCE_INTERVAL_FILE.relative_to(ROOT)),
        "payloadFile": str(PAYLOAD_FILE.relative_to(ROOT)),
        "route": "signed_leibniz_checker_then_signed_factor_rows",
        "proofStatus": (
            "abs_to_signed_factor_bridge_checked_but_centered_taylor_budget_killed"
            if checker_present and abs_bridge_present and budget_kill_present
            else "abs_to_signed_factor_checker_checked_missing_concrete_rows"
            if checker_present and abs_bridge_present
            else "factor_to_leibniz_term_checker_checked_missing_concrete_rows"
            if checker_present
            else "signed_leibniz_checker_missing"
        ),
        "signedLeibnizCheckerPresent": checker_present,
        "factorToLeibnizTermCheckerPresent": checker_present,
        "absToSignedFactorRowsBridgePresent": abs_bridge_present,
        "sourceSegmentReceiverPresent": all_true(source_interval_symbols),
        "zeroModelValidReceiverPresent": all_true(payload_symbols),
        "signedFactorCoverReceiverPresent": checker_present,
        "zeroModelValidOfSignedFactorCoverPresent": checker_present,
        "checkerSymbols": checker_symbols,
        "absBridgeSymbols": abs_bridge_symbols,
        "sourceIntervalSymbols": source_interval_symbols,
        "payloadSymbols": payload_symbols,
        "budgetKillSymbols": budget_kill_symbols,
        "signedFactorRowsLeanChecked": False,
        "factorAbsMajorantRowsLeanChecked": False,
        "centeredTaylorAbsRowsBudgetKilled": budget_kill_present,
        "factorAbsMajorantRowsThresholdViable": (
            False if budget_kill_present else None
        ),
        "leibnizCornerRowsLeanChecked": False,
        "leibnizTermRowsDerivedByLean": checker_present,
        "sourceAssemblyRowsLeanChecked": False,
        "sourceAssemblyCheckerPresent": checker_present,
        "sourceSegmentValidClaimed": False,
        "zeroModelAbsBoundLeanChecked": False,
        "directIntervalValidClaimed": False,
        "step33A1ClosedClaimed": False,
        "proofGrade": False,
        "currentGap": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_TAYLOR_SOURCE_GAP"
            if budget_kill_present
            else "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP"
        ),
        "closedFailureCode": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_LEIBNIZ_CHECKER_GAP"
        ),
        "closedFactorToTermCheckerCode": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_FACTOR_TO_LEIBNIZ_TERM_CHECKER_CLOSED"
        ),
        "closedAbsToSignedFactorRowsCode": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_ABS_TO_SIGNED_FACTOR_ROWS_BRIDGE_CLOSED"
        ),
        "failureCodeIfCenteredTaylorAbsRowsUsed": (
            "STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL"
        ),
        "failureCodeIfRowsMissing": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP"
        ),
        "failureCodeIfZeroModelTooSmall": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_ZERO_MODEL_CONSTANT_FAIL"
        ),
        "nextProofObject": (
            "proof-grade direct hRemainder for the threshold zero-model, or "
            "a sharper cancellation-preserving polynomial source model"
            if budget_kill_present
            else "rational enclosures of the existing centered-Taylor absolute "
            "factor majorants, exact Leibniz term corner arithmetic rows, "
            "and active-scale sourceAssembly rows for each segment"
        ),
        "guard": (
            "No sampled intervals and no independent product-summand norm "
            "budget may be treated as proof.  The centered-Taylor absolute "
            "majorant row route is not spendable after the exact budget-kill "
            "audit; the live route is direct cancellation-preserving source "
            "control."
            if budget_kill_present
            else "No sampled intervals and no independent product-summand norm "
            "budget may be treated as proof; rows must instantiate the signed "
            "Leibniz checker."
        ),
    }


def render_markdown(ledger: dict[str, object]) -> str:
    checker_symbols = ledger["checkerSymbols"]
    abs_bridge_symbols = ledger["absBridgeSymbols"]
    source_interval_symbols = ledger["sourceIntervalSymbols"]
    payload_symbols = ledger["payloadSymbols"]
    budget_kill_symbols = ledger["budgetKillSymbols"]
    assert isinstance(checker_symbols, dict)
    assert isinstance(abs_bridge_symbols, dict)
    assert isinstance(source_interval_symbols, dict)
    assert isinstance(payload_symbols, dict)
    assert isinstance(budget_kill_symbols, dict)

    lines = [
        "# Step33A.1-A Combined Order16 Signed Factor Rows Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Present",
        "",
        f"- signedLeibnizCheckerPresent: `{ledger['signedLeibnizCheckerPresent']}`",
        "- factorToLeibnizTermCheckerPresent: "
        f"`{ledger['factorToLeibnizTermCheckerPresent']}`",
        "- absToSignedFactorRowsBridgePresent: "
        f"`{ledger['absToSignedFactorRowsBridgePresent']}`",
        f"- sourceSegmentReceiverPresent: `{ledger['sourceSegmentReceiverPresent']}`",
        f"- zeroModelValidReceiverPresent: `{ledger['zeroModelValidReceiverPresent']}`",
        "- signedFactorCoverReceiverPresent: "
        f"`{ledger['signedFactorCoverReceiverPresent']}`",
        "- zeroModelValidOfSignedFactorCoverPresent: "
        f"`{ledger['zeroModelValidOfSignedFactorCoverPresent']}`",
        "",
        "## Checker Symbols",
        "",
    ]
    for symbol, present in checker_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Abs Bridge Symbols", ""])
    for symbol, present in abs_bridge_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Source Segment Symbols", ""])
    for symbol, present in source_interval_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Payload Receiver Symbols", ""])
    for symbol, present in payload_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Budget Kill Symbols", ""])
    for symbol, present in budget_kill_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(
        [
            "",
            "## Missing Proof Payload",
            "",
            f"- signedFactorRowsLeanChecked: `{ledger['signedFactorRowsLeanChecked']}`",
            "- factorAbsMajorantRowsLeanChecked: "
            f"`{ledger['factorAbsMajorantRowsLeanChecked']}`",
            "- centeredTaylorAbsRowsBudgetKilled: "
            f"`{ledger['centeredTaylorAbsRowsBudgetKilled']}`",
            "- factorAbsMajorantRowsThresholdViable: "
            f"`{ledger['factorAbsMajorantRowsThresholdViable']}`",
            f"- leibnizCornerRowsLeanChecked: `{ledger['leibnizCornerRowsLeanChecked']}`",
            f"- leibnizTermRowsDerivedByLean: `{ledger['leibnizTermRowsDerivedByLean']}`",
            f"- sourceAssemblyRowsLeanChecked: `{ledger['sourceAssemblyRowsLeanChecked']}`",
            f"- sourceAssemblyCheckerPresent: `{ledger['sourceAssemblyCheckerPresent']}`",
            f"- sourceSegmentValidClaimed: `{ledger['sourceSegmentValidClaimed']}`",
            f"- zeroModelAbsBoundLeanChecked: `{ledger['zeroModelAbsBoundLeanChecked']}`",
            f"- directIntervalValidClaimed: `{ledger['directIntervalValidClaimed']}`",
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
            "## Failure Codes",
            "",
            f"- closed checker gap: `{ledger['closedFailureCode']}`",
            "- closed factor-to-term checker: "
            f"`{ledger['closedFactorToTermCheckerCode']}`",
            "- closed abs-to-signed-factor bridge: "
            f"`{ledger['closedAbsToSignedFactorRowsCode']}`",
            "- centered-Taylor abs rows budget kill: "
            f"`{ledger['failureCodeIfCenteredTaylorAbsRowsUsed']}`",
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
