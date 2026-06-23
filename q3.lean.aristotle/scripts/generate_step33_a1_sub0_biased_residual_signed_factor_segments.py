#!/usr/bin/env python3
"""Fail-closed ledger for the biased residual signed-factor segment route.

The current Step33A.1-A biased residual receiver consumes source-only
signed-factor segment certificates.  This ledger records the checked Lean
interfaces and the exact remaining payload gap without reusing the old
direct-zero `zeroModelBudget` route.

It does not emit numerical rows and does not claim Step33A.1-A closure.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path


SCHEMA = "q3_psdpd_step33_a1_sub0_biased_residual_signed_factor_segments.v1"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

CHECKER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SignedFactorChecker.lean"
)
ADAPTER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSignedFactorAdapter.lean"
)
BIASED_INTERVAL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval.lean"
)
NONZERO_MODEL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean"
)
BUDGET_AUDIT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean"
)
OLD_SIGNED_FACTOR_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_combined_order16_signed_factor_rows.json"
)
JSON_OUT = (
    REQUEST_DIR / "step33_a1_sub0_biased_residual_signed_factor_segments.json"
)
MD_OUT = (
    REQUEST_DIR / "step33_a1_sub0_biased_residual_signed_factor_segments.md"
)

CHECKER_SYMBOLS = [
    "Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert",
    "structure SourceIntervalValid",
    "namespace SourceIntervalValid",
    "theorem to_leftTermRows",
    "theorem to_rightTermRows",
    "theorem to_sourceInterval",
    "theorem to_sourceIntervalValid",
    "sourceAssembly",
    "zeroModelBudget",
]

ADAPTER_SYMBOLS = [
    "toBiasedResidualSourceSegment",
    "to_biasedResidualSourceSegmentValid",
    "Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentCover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_signedFactor_segment_cover",
    "Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert",
    "structure Valid",
    "theorem to_residualSourceProp",
    "theorem to_order16DirectIntervalValid",
]

BIASED_INTERVAL_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert",
    "namespace Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert",
    "structure Valid",
    "theorem to_residual_bound_on_segment",
    "Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_segment_cover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_source_segment_cover",
]

NONZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData",
    "polyLower",
    "polyUpper",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_poly_range",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound",
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


def load_old_ledger() -> dict[str, object]:
    if not OLD_SIGNED_FACTOR_LEDGER.exists():
        return {}
    return json.loads(OLD_SIGNED_FACTOR_LEDGER.read_text(encoding="utf-8"))


def build_ledger() -> dict[str, object]:
    checker_symbols = file_contains(CHECKER_FILE, CHECKER_SYMBOLS)
    adapter_symbols = file_contains(ADAPTER_FILE, ADAPTER_SYMBOLS)
    biased_interval_symbols = file_contains(
        BIASED_INTERVAL_FILE, BIASED_INTERVAL_SYMBOLS
    )
    nonzero_model_symbols = file_contains(NONZERO_MODEL_FILE, NONZERO_MODEL_SYMBOLS)
    budget_kill_symbols = file_contains(BUDGET_AUDIT_FILE, BUDGET_KILL_SYMBOLS)
    old_ledger = load_old_ledger()

    checker_present = all_true(checker_symbols)
    adapter_present = all_true(adapter_symbols)
    biased_interval_present = all_true(biased_interval_symbols)
    nonzero_model_present = all_true(nonzero_model_symbols)
    old_zero_model_budget_killed = bool(
        old_ledger.get("centeredTaylorAbsRowsBudgetKilled")
    ) or all_true(budget_kill_symbols)

    interface_ready = (
        checker_present
        and adapter_present
        and biased_interval_present
        and nonzero_model_present
    )

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "checkerFile": str(CHECKER_FILE.relative_to(ROOT)),
        "adapterFile": str(ADAPTER_FILE.relative_to(ROOT)),
        "biasedIntervalFile": str(BIASED_INTERVAL_FILE.relative_to(ROOT)),
        "nonzeroModelFile": str(NONZERO_MODEL_FILE.relative_to(ROOT)),
        "budgetAuditFile": str(BUDGET_AUDIT_FILE.relative_to(ROOT)),
        "oldSignedFactorLedger": str(OLD_SIGNED_FACTOR_LEDGER.relative_to(ROOT)),
        "route": "biased_residual_source_only_signed_factor_segments",
        "proofStatus": (
            "biased_residual_signed_factor_source_only_interface_checked_missing_segment_payload"
            if interface_ready
            else "biased_residual_signed_factor_interface_incomplete"
        ),
        "sourceOnlySignedFactorCheckerPresent": checker_present,
        "biasedResidualSignedFactorAdapterPresent": adapter_present,
        "biasedResidualSourceSegmentReceiverPresent": biased_interval_present,
        "biasedModelBudgetSurfacePresent": nonzero_model_present,
        "checkerSymbols": checker_symbols,
        "adapterSymbols": adapter_symbols,
        "biasedIntervalSymbols": biased_interval_symbols,
        "nonzeroModelSymbols": nonzero_model_symbols,
        "budgetKillSymbols": budget_kill_symbols,
        "oldZeroModelBudgetKilled": old_zero_model_budget_killed,
        "oldZeroModelBudgetSpendableForBiasedResidual": False,
        "sourceOnlyInterfaceReady": interface_ready,
        "generatorFacingFamilyCertPresent": all_true(adapter_symbols),
        "concreteSegmentsLeanChecked": False,
        "factorRowsLeanChecked": False,
        "leibnizCornerRowsLeanChecked": False,
        "sourceAssemblyRowsLeanChecked": False,
        "biasedBudgetRowsLeanChecked": False,
        "globalCoverLeanChecked": False,
        "residualSlackComparisonLeanChecked": False,
        "residualSourcePropClaimed": False,
        "order16DirectIntervalValidClaimed": False,
        "step33A1ClosedClaimed": False,
        "proofGrade": False,
        "currentGap": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_SEGMENT_PAYLOAD_GAP"
        ),
        "closedInterfaceCode": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_TO_SOURCE_SEGMENT_RECEIVER_CLOSED"
        ),
        "failureCodeIfOldBudgetReused": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_OLD_ZERO_MODEL_BUDGET_REUSE_INVALID"
        ),
        "failureCodeIfRowsMissing": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_SEGMENT_PAYLOAD_GAP"
        ),
        "failureCodeIfBudgetRowsFail": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_BUDGET_CONSTANT_FAIL"
        ),
        "nextProofObject": (
            "concrete signed-factor segment family proving SourceIntervalValid, "
            "a cover of [0,1/10], exact per-segment biased-model lower/upper "
            "budget rows, and residualAbs <= ResidualSlackRat"
        ),
        "guard": (
            "Do not reuse Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert.Valid "
            "or its zeroModelBudget row for the biased residual.  The live route "
            "uses SourceIntervalValid plus fresh same-unit budget rows against "
            "the checked biased nonzero-model polynomial range."
        ),
    }


def render_markdown(ledger: dict[str, object]) -> str:
    checker_symbols = ledger["checkerSymbols"]
    adapter_symbols = ledger["adapterSymbols"]
    biased_interval_symbols = ledger["biasedIntervalSymbols"]
    nonzero_model_symbols = ledger["nonzeroModelSymbols"]
    budget_kill_symbols = ledger["budgetKillSymbols"]
    assert isinstance(checker_symbols, dict)
    assert isinstance(adapter_symbols, dict)
    assert isinstance(biased_interval_symbols, dict)
    assert isinstance(nonzero_model_symbols, dict)
    assert isinstance(budget_kill_symbols, dict)

    lines = [
        "# Step33A.1-A Biased Residual Signed-Factor Segment Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Present",
        "",
        "- sourceOnlySignedFactorCheckerPresent: "
        f"`{ledger['sourceOnlySignedFactorCheckerPresent']}`",
        "- biasedResidualSignedFactorAdapterPresent: "
        f"`{ledger['biasedResidualSignedFactorAdapterPresent']}`",
        "- biasedResidualSourceSegmentReceiverPresent: "
        f"`{ledger['biasedResidualSourceSegmentReceiverPresent']}`",
        "- biasedModelBudgetSurfacePresent: "
        f"`{ledger['biasedModelBudgetSurfacePresent']}`",
        f"- sourceOnlyInterfaceReady: `{ledger['sourceOnlyInterfaceReady']}`",
        "- generatorFacingFamilyCertPresent: "
        f"`{ledger['generatorFacingFamilyCertPresent']}`",
        "",
        "## Checker Symbols",
        "",
    ]
    for symbol, present in checker_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Adapter Symbols", ""])
    for symbol, present in adapter_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Biased Residual Source-Segment Symbols", ""])
    for symbol, present in biased_interval_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Biased Model Budget Symbols", ""])
    for symbol, present in nonzero_model_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Old Zero-Model Budget Guard", ""])
    for symbol, present in budget_kill_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(
        [
            f"- oldZeroModelBudgetKilled: `{ledger['oldZeroModelBudgetKilled']}`",
            "- oldZeroModelBudgetSpendableForBiasedResidual: "
            f"`{ledger['oldZeroModelBudgetSpendableForBiasedResidual']}`",
            "",
            "## Missing Proof Payload",
            "",
            f"- concreteSegmentsLeanChecked: `{ledger['concreteSegmentsLeanChecked']}`",
            f"- factorRowsLeanChecked: `{ledger['factorRowsLeanChecked']}`",
            "- leibnizCornerRowsLeanChecked: "
            f"`{ledger['leibnizCornerRowsLeanChecked']}`",
            "- sourceAssemblyRowsLeanChecked: "
            f"`{ledger['sourceAssemblyRowsLeanChecked']}`",
            f"- biasedBudgetRowsLeanChecked: `{ledger['biasedBudgetRowsLeanChecked']}`",
            f"- globalCoverLeanChecked: `{ledger['globalCoverLeanChecked']}`",
            "- residualSlackComparisonLeanChecked: "
            f"`{ledger['residualSlackComparisonLeanChecked']}`",
            f"- residualSourcePropClaimed: `{ledger['residualSourcePropClaimed']}`",
            "- order16DirectIntervalValidClaimed: "
            f"`{ledger['order16DirectIntervalValidClaimed']}`",
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
            f"- closed interface: `{ledger['closedInterfaceCode']}`",
            f"- old budget reuse invalid: `{ledger['failureCodeIfOldBudgetReused']}`",
            f"- rows missing: `{ledger['failureCodeIfRowsMissing']}`",
            f"- budget rows fail: `{ledger['failureCodeIfBudgetRowsFail']}`",
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
