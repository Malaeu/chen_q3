#!/usr/bin/env python3
"""Fail-closed ledger for the biased residual local-model segment route.

The checked Lean receiver consumes source and biased-model bounds on the same
segment, avoiding the global-extrema width loss of the older source-segment
surface.  This script records that receiver and the exact remaining concrete
payload rows.

It does not emit numerical rows and does not claim Step33A.1-A closure.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path


SCHEMA = "q3_psdpd_step33_a1_sub0_biased_residual_local_model_segments.v1"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

LOCAL_MODEL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualLocalModelSegmentCert.lean"
)
BIASED_INTERVAL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval.lean"
)
NONZERO_MODEL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean"
)
DIRECT_ADAPTER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload.lean"
)

JSON_OUT = REQUEST_DIR / "step33_a1_sub0_biased_residual_local_model_segments.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_biased_residual_local_model_segments.md"

LOCAL_MODEL_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert",
    "structure Valid",
    "sourceInterval",
    "modelInterval",
    "lowerBudget",
    "upperBudget",
    "theorem to_residual_bound_on_segment",
    "Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_local_model_segment_cover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_local_model_segment_cover",
    "Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert",
    "namespace Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert",
    "theorem to_residualSourceProp",
    "theorem to_order16DirectIntervalValid",
]

BIASED_INTERVAL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp",
    "Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert",
    "Step33Sub0CombinedOrder16BiasedResidualActiveActualSignedIntervalCert",
]

NONZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound",
]

DIRECT_ADAPTER_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_remainder_bound",
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound",
]


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    if not path.exists():
        return {symbol: False for symbol in symbols}
    text = path.read_text(encoding="utf-8")
    return {symbol: symbol in text for symbol in symbols}


def all_true(items: dict[str, bool]) -> bool:
    return all(items.values())


def build_ledger() -> dict[str, object]:
    local_model_symbols = file_contains(LOCAL_MODEL_FILE, LOCAL_MODEL_SYMBOLS)
    biased_interval_symbols = file_contains(
        BIASED_INTERVAL_FILE, BIASED_INTERVAL_SYMBOLS
    )
    nonzero_model_symbols = file_contains(NONZERO_MODEL_FILE, NONZERO_MODEL_SYMBOLS)
    direct_adapter_symbols = file_contains(DIRECT_ADAPTER_FILE, DIRECT_ADAPTER_SYMBOLS)

    receiver_present = all_true(local_model_symbols)
    bridge_present = all_true(biased_interval_symbols)
    nonzero_model_present = all_true(nonzero_model_symbols)
    direct_adapter_present = all_true(direct_adapter_symbols)
    interface_ready = (
        receiver_present and bridge_present and nonzero_model_present
        and direct_adapter_present
    )

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "localModelFile": str(LOCAL_MODEL_FILE.relative_to(ROOT)),
        "biasedIntervalFile": str(BIASED_INTERVAL_FILE.relative_to(ROOT)),
        "nonzeroModelFile": str(NONZERO_MODEL_FILE.relative_to(ROOT)),
        "directAdapterFile": str(DIRECT_ADAPTER_FILE.relative_to(ROOT)),
        "route": "biased_residual_local_model_segments",
        "proofStatus": (
            "biased_residual_local_model_segment_family_receiver_checked_missing_payload"
            if interface_ready
            else "biased_residual_local_model_segment_interface_incomplete"
        ),
        "localModelSegmentReceiverPresent": receiver_present,
        "biasedResidualBridgePresent": bridge_present,
        "biasedNonzeroModelDirectReceiverPresent": nonzero_model_present,
        "directResidualAdapterPresent": direct_adapter_present,
        "localModelSymbols": local_model_symbols,
        "biasedIntervalSymbols": biased_interval_symbols,
        "nonzeroModelSymbols": nonzero_model_symbols,
        "directAdapterSymbols": direct_adapter_symbols,
        "concreteSegmentsLeanChecked": False,
        "sourceRowsLeanChecked": False,
        "modelRowsLeanChecked": False,
        "localBudgetRowsLeanChecked": False,
        "segmentBudgetRowsLeanChecked": False,
        "globalCoverLeanChecked": False,
        "globalSlackComparisonLeanChecked": False,
        "residualSourcePropClaimed": False,
        "order16DirectIntervalValidClaimed": False,
        "step33A1ClosedClaimed": False,
        "proofGrade": False,
        "currentGap": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_PAYLOAD_GAP"
        ),
        "closedInterfaceCode": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_FAMILY_RECEIVER_CLOSED"
        ),
        "failureCodeIfRowsMissing": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_PAYLOAD_GAP"
        ),
        "failureCodeIfBudgetRowsFail": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_BUDGET_CONSTANT_FAIL"
        ),
        "failureCodeIfCoverFails": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_COVER_GAP"
        ),
        "nextProofObject": (
            "a concrete Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert.Valid "
            "payload: source/model same-cell interval rows, local residual "
            "budget rows, segment residualAbs <= global residualAbs, global "
            "residualAbs <= ResidualSlackRat, and cover of [0,1/10]"
        ),
        "guard": (
            "Do not spend source rows against global BiasedNonzeroModelData "
            "polyLower/polyUpper when local model rows are available.  The "
            "live target compares source and model on the same segment and "
            "then uses the existing direct biased nonzero-model receiver."
        ),
    }


def render_symbol_section(title: str, symbols: dict[str, bool]) -> list[str]:
    lines = ["", f"## {title}", ""]
    lines.extend(f"- `{symbol}`: `{present}`" for symbol, present in symbols.items())
    return lines


def render_markdown(ledger: dict[str, object]) -> str:
    local_model_symbols = ledger["localModelSymbols"]
    biased_interval_symbols = ledger["biasedIntervalSymbols"]
    nonzero_model_symbols = ledger["nonzeroModelSymbols"]
    direct_adapter_symbols = ledger["directAdapterSymbols"]
    assert isinstance(local_model_symbols, dict)
    assert isinstance(biased_interval_symbols, dict)
    assert isinstance(nonzero_model_symbols, dict)
    assert isinstance(direct_adapter_symbols, dict)

    lines = [
        "# Step33A.1-A Biased Residual Local-Model Segment Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Present",
        "",
        "- localModelSegmentReceiverPresent: "
        f"`{ledger['localModelSegmentReceiverPresent']}`",
        "- biasedResidualBridgePresent: "
        f"`{ledger['biasedResidualBridgePresent']}`",
        "- biasedNonzeroModelDirectReceiverPresent: "
        f"`{ledger['biasedNonzeroModelDirectReceiverPresent']}`",
        "- directResidualAdapterPresent: "
        f"`{ledger['directResidualAdapterPresent']}`",
    ]
    lines.extend(render_symbol_section("Local-Model Segment Symbols", local_model_symbols))
    lines.extend(render_symbol_section("Biased Residual Bridge Symbols", biased_interval_symbols))
    lines.extend(render_symbol_section("Biased Nonzero-Model Symbols", nonzero_model_symbols))
    lines.extend(render_symbol_section("Direct Adapter Symbols", direct_adapter_symbols))
    lines.extend(
        [
            "",
            "## Missing Proof Payload",
            "",
            f"- concreteSegmentsLeanChecked: `{ledger['concreteSegmentsLeanChecked']}`",
            f"- sourceRowsLeanChecked: `{ledger['sourceRowsLeanChecked']}`",
            f"- modelRowsLeanChecked: `{ledger['modelRowsLeanChecked']}`",
            f"- localBudgetRowsLeanChecked: `{ledger['localBudgetRowsLeanChecked']}`",
            f"- segmentBudgetRowsLeanChecked: `{ledger['segmentBudgetRowsLeanChecked']}`",
            f"- globalCoverLeanChecked: `{ledger['globalCoverLeanChecked']}`",
            "- globalSlackComparisonLeanChecked: "
            f"`{ledger['globalSlackComparisonLeanChecked']}`",
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
            "## Guard",
            "",
            str(ledger["guard"]),
            "",
            "## Failure Codes",
            "",
            f"- rowsMissing: `{ledger['failureCodeIfRowsMissing']}`",
            f"- budgetRowsFail: `{ledger['failureCodeIfBudgetRowsFail']}`",
            f"- coverFails: `{ledger['failureCodeIfCoverFails']}`",
            f"- closedInterface: `{ledger['closedInterfaceCode']}`",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    JSON_OUT.write_text(
        json.dumps(ledger, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(ledger["proofStatus"])
    print(ledger["currentGap"])


if __name__ == "__main__":
    main()
