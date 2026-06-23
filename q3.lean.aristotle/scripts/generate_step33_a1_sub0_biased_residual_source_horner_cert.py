#!/usr/bin/env python3
"""Fail-closed ledger for the biased residual source-Horner family route.

The Lean receiver now accepts a finite family of direct source-Horner
segments and transports it into the existing biased nonzero-model order-16
interval receiver.  This script records that checked interface and the exact
missing proof payload rows.

It does not emit numerical rows and does not claim Step33A.1-A closure.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path


SCHEMA = "q3_psdpd_step33_a1_sub0_biased_residual_source_horner_cert.v1"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

SOURCE_HORNER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerCert.lean"
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
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualBudgetAudit.lean"
)
DIRECT_ADAPTER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload.lean"
)
RESIDUAL_HORNER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerCert.lean"
)

JSON_OUT = (
    REQUEST_DIR / "step33_a1_sub0_biased_residual_source_horner_cert.json"
)
MD_OUT = REQUEST_DIR / "step33_a1_sub0_biased_residual_source_horner_cert.md"

SOURCE_HORNER_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert",
    "def poly",
    "def toSourceSegment",
    "structure Valid",
    "source_remainder",
    "poly_range",
    "theorem sourceInterval",
    "theorem to_sourceSegmentValid",
    "def hornerTail",
    "theorem hornerTail_zero_eq_poly",
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert",
    "theorem poly_range",
    "theorem of_horner_range",
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerSegmentCover",
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert",
    "theorem to_segmentValid",
    "theorem to_residualSourceProp",
    "theorem to_order16DirectIntervalValid",
]

BIASED_INTERVAL_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert",
    "Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_segment_cover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_source_segment_cover",
]

NONZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_poly_range",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_biasedNonzeroModelPoly",
]

BUDGET_KILL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorNeededAbsRat",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidual_centeredTaylorNeededAbs_budget_fail_rat",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_centeredTaylor_not_spendable",
]

DIRECT_ADAPTER_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs",
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_remainder_bound",
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound",
]

RESIDUAL_HORNER_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualHornerCert",
    "Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert",
    "Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert",
    "theorem to_residualSourceProp",
    "theorem to_order16DirectIntervalValid",
]


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    if not path.exists():
        return {symbol: False for symbol in symbols}
    text = path.read_text(encoding="utf-8")
    return {symbol: symbol in text for symbol in symbols}


def all_true(items: dict[str, bool]) -> bool:
    return all(items.values())


def build_ledger() -> dict[str, object]:
    source_horner_symbols = file_contains(SOURCE_HORNER_FILE, SOURCE_HORNER_SYMBOLS)
    biased_interval_symbols = file_contains(
        BIASED_INTERVAL_FILE, BIASED_INTERVAL_SYMBOLS
    )
    nonzero_model_symbols = file_contains(NONZERO_MODEL_FILE, NONZERO_MODEL_SYMBOLS)
    budget_kill_symbols = file_contains(BUDGET_AUDIT_FILE, BUDGET_KILL_SYMBOLS)
    direct_adapter_symbols = file_contains(DIRECT_ADAPTER_FILE, DIRECT_ADAPTER_SYMBOLS)
    residual_horner_symbols = file_contains(
        RESIDUAL_HORNER_FILE, RESIDUAL_HORNER_SYMBOLS
    )

    source_horner_receiver_present = all_true(source_horner_symbols)
    biased_interval_receiver_present = all_true(biased_interval_symbols)
    biased_model_budget_present = all_true(nonzero_model_symbols)
    killed_centered_taylor_present = all_true(budget_kill_symbols)
    direct_adapter_present = all_true(direct_adapter_symbols)
    residual_horner_receiver_present = all_true(residual_horner_symbols)
    interface_ready = (
        source_horner_receiver_present
        and biased_interval_receiver_present
        and biased_model_budget_present
    )

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "sourceHornerFile": str(SOURCE_HORNER_FILE.relative_to(ROOT)),
        "biasedIntervalFile": str(BIASED_INTERVAL_FILE.relative_to(ROOT)),
        "nonzeroModelFile": str(NONZERO_MODEL_FILE.relative_to(ROOT)),
        "budgetAuditFile": str(BUDGET_AUDIT_FILE.relative_to(ROOT)),
        "directAdapterFile": str(DIRECT_ADAPTER_FILE.relative_to(ROOT)),
        "residualHornerFile": str(RESIDUAL_HORNER_FILE.relative_to(ROOT)),
        "route": "biased_residual_direct_source_horner_family",
        "proofStatus": (
            "direct_residual_adapter_checked_missing_residual_bound"
            if direct_adapter_present
            else "source_horner_family_receiver_checked_missing_payload_rows"
            if interface_ready
            else "source_horner_family_receiver_interface_incomplete"
        ),
        "sourceHornerReceiverPresent": source_horner_receiver_present,
        "biasedResidualSourceSegmentReceiverPresent": biased_interval_receiver_present,
        "biasedModelBudgetSurfacePresent": biased_model_budget_present,
        "centeredTaylorAbsBudgetKilled": killed_centered_taylor_present,
        "directResidualAdapterPresent": direct_adapter_present,
        "residualHornerReceiverPresent": residual_horner_receiver_present,
        "sourceHornerFamilyDirectSpendableFromRemainderOnly": False,
        "sourceHornerSymbols": source_horner_symbols,
        "biasedIntervalSymbols": biased_interval_symbols,
        "nonzeroModelSymbols": nonzero_model_symbols,
        "budgetKillSymbols": budget_kill_symbols,
        "directAdapterSymbols": direct_adapter_symbols,
        "residualHornerSymbols": residual_horner_symbols,
        "concreteSourceHornerSegmentsLeanChecked": False,
        "sourceCoefficientsLeanChecked": False,
        "hornerStageBoundsLeanChecked": False,
        "sourceRemainderBoundLeanChecked": False,
        "sourceLowerUpperRowsLeanChecked": False,
        "biasedBudgetRowsLeanChecked": False,
        "globalCoverLeanChecked": False,
        "residualSlackComparisonLeanChecked": False,
        "residualSourcePropClaimed": False,
        "order16DirectIntervalValidClaimed": False,
        "step33A1ClosedClaimed": False,
        "proofGrade": False,
        "currentGap": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_NONZERO_MODEL_RESIDUAL_BOUND_GAP"
            if direct_adapter_present
            else "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_PAYLOAD_ROWS_GAP"
        ),
        "closedInterfaceCode": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_FAMILY_RECEIVER_CLOSED"
        ),
        "failureCodeIfRowsMissing": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_PAYLOAD_ROWS_GAP"
        ),
        "failureCodeIfRemainderMissing": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_REMAINDER_BOUND_GAP"
        ),
        "failureCodeIfBudgetRowsFail": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_BUDGET_CONSTANT_FAIL"
        ),
        "failureCodeIfNormalizationMismatch": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_NORMALIZATION_MISMATCH_GAP"
        ),
        "nextProofObject": (
            "a proof-grade bound for "
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp "
            "at residualAbs <= ResidualSlackRat"
            if direct_adapter_present
            else "a concrete SourceHornerFamilyCert with source coefficients, Horner "
            "stage lower/upper rows, proof-grade whole-source remainderBound, "
            "same-unit biased residual budget rows, a cover of [0,1/10], and "
            "residualAbs <= ResidualSlackRat"
        ),
        "guard": (
            "Do not reuse the old zero-model budget or centeredTaylor rows.  "
            "Do not force SourceHornerFamilyCert.Valid from a pointwise "
            "ComponentSource - BiasedNonzeroModelPoly bound: that source-segment "
            "normalization pays independent global extrema.  Spend residual "
            "bounds through the direct biased nonzero-model receiver instead."
        ),
    }


def render_markdown(ledger: dict[str, object]) -> str:
    source_horner_symbols = ledger["sourceHornerSymbols"]
    biased_interval_symbols = ledger["biasedIntervalSymbols"]
    nonzero_model_symbols = ledger["nonzeroModelSymbols"]
    budget_kill_symbols = ledger["budgetKillSymbols"]
    direct_adapter_symbols = ledger["directAdapterSymbols"]
    residual_horner_symbols = ledger["residualHornerSymbols"]
    assert isinstance(source_horner_symbols, dict)
    assert isinstance(biased_interval_symbols, dict)
    assert isinstance(nonzero_model_symbols, dict)
    assert isinstance(budget_kill_symbols, dict)
    assert isinstance(direct_adapter_symbols, dict)
    assert isinstance(residual_horner_symbols, dict)

    lines = [
        "# Step33A.1-A Biased Residual Source-Horner Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Present",
        "",
        f"- sourceHornerReceiverPresent: `{ledger['sourceHornerReceiverPresent']}`",
        f"- biasedResidualSourceSegmentReceiverPresent: `{ledger['biasedResidualSourceSegmentReceiverPresent']}`",
        f"- biasedModelBudgetSurfacePresent: `{ledger['biasedModelBudgetSurfacePresent']}`",
        f"- centeredTaylorAbsBudgetKilled: `{ledger['centeredTaylorAbsBudgetKilled']}`",
        f"- directResidualAdapterPresent: `{ledger['directResidualAdapterPresent']}`",
        f"- residualHornerReceiverPresent: `{ledger['residualHornerReceiverPresent']}`",
        f"- sourceHornerFamilyDirectSpendableFromRemainderOnly: `{ledger['sourceHornerFamilyDirectSpendableFromRemainderOnly']}`",
        "",
        "## Source-Horner Symbols",
        "",
    ]
    lines.extend(f"- `{k}`: `{v}`" for k, v in source_horner_symbols.items())
    lines.extend(["", "## Biased Residual Source-Segment Symbols", ""])
    lines.extend(f"- `{k}`: `{v}`" for k, v in biased_interval_symbols.items())
    lines.extend(["", "## Biased Model Budget Symbols", ""])
    lines.extend(f"- `{k}`: `{v}`" for k, v in nonzero_model_symbols.items())
    lines.extend(["", "## CenteredTaylor Budget Guard", ""])
    lines.extend(f"- `{k}`: `{v}`" for k, v in budget_kill_symbols.items())
    lines.extend(["", "## Direct Residual Adapter Symbols", ""])
    lines.extend(f"- `{k}`: `{v}`" for k, v in direct_adapter_symbols.items())
    lines.extend(["", "## Residual-Horner Receiver Symbols", ""])
    lines.extend(f"- `{k}`: `{v}`" for k, v in residual_horner_symbols.items())
    lines.extend(
        [
            "",
            "## Missing Proof Payload",
            "",
            f"- concreteSourceHornerSegmentsLeanChecked: `{ledger['concreteSourceHornerSegmentsLeanChecked']}`",
            f"- sourceCoefficientsLeanChecked: `{ledger['sourceCoefficientsLeanChecked']}`",
            f"- hornerStageBoundsLeanChecked: `{ledger['hornerStageBoundsLeanChecked']}`",
            f"- sourceRemainderBoundLeanChecked: `{ledger['sourceRemainderBoundLeanChecked']}`",
            f"- sourceLowerUpperRowsLeanChecked: `{ledger['sourceLowerUpperRowsLeanChecked']}`",
            f"- biasedBudgetRowsLeanChecked: `{ledger['biasedBudgetRowsLeanChecked']}`",
            f"- globalCoverLeanChecked: `{ledger['globalCoverLeanChecked']}`",
            f"- residualSlackComparisonLeanChecked: `{ledger['residualSlackComparisonLeanChecked']}`",
            f"- residualSourcePropClaimed: `{ledger['residualSourcePropClaimed']}`",
            f"- order16DirectIntervalValidClaimed: `{ledger['order16DirectIntervalValidClaimed']}`",
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
            f"- rows missing: `{ledger['failureCodeIfRowsMissing']}`",
            f"- remainder missing: `{ledger['failureCodeIfRemainderMissing']}`",
            f"- budget rows fail: `{ledger['failureCodeIfBudgetRowsFail']}`",
            f"- normalization mismatch: `{ledger['failureCodeIfNormalizationMismatch']}`",
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
    print(f"wrote {JSON_OUT.relative_to(ROOT)}")
    print(f"wrote {MD_OUT.relative_to(ROOT)}")
    print(ledger["proofStatus"])
    print(ledger["currentGap"])


if __name__ == "__main__":
    main()
