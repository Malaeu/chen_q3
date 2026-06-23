#!/usr/bin/env python3
"""Fail-closed ledger for the Step33A.1-A direct order-16 payload.

This script does not turn numerical probes into proof.  It records whether the
Lean-side conditional checker for the cancellation-preserving direct model is
present, and it keeps the concrete polynomial/Horner payload marked open until
generated proof-grade rows exist.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
import hashlib
from pathlib import Path


SCHEMA = "q3_psdpd_step33_a1_sub0_combined_order16_direct_payload.v1"

ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"
LEAN_MODEL = (
    ROOT
    / "Q3"
    / "Proofs"
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectModelPayload.lean"
)
LEAN_ADAPTER = (
    ROOT
    / "Q3"
    / "Proofs"
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectIntervalPayload.lean"
)
NORMAL_FORM = (
    ROOT
    / "Q3"
    / "Proofs"
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NormalForm.lean"
)
BUDGET_AUDIT = (
    ROOT
    / "Q3"
    / "Proofs"
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16RawProduct17BudgetAudit.lean"
)
SOURCE_MODEL_BRIDGE = (
    ROOT
    / "Q3"
    / "Proofs"
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean"
)
JSON_OUT = REQUEST_DIR / "step33_a1_sub0_combined_cancellation_order16_direct_payload.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_combined_cancellation_order16_direct_payload.md"

MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectIntervalData",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectInterval_valid_of_horner_remainder",
]

CONCRETE_ZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelHornerRangeData",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelIntervalData",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_componentSource_abs",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_horner_valid",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_source_lower_budget",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_source_upper_budget",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_order16_budget",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_order16_remainder_width_pass_rat",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_remainder",
]

ADAPTER_SYMBOLS = [
    "Step33Sub0CombinedCancellationOrder16DirectIntervalCert",
    "structure Valid",
    "to_order16SourceInterval",
    "to_order16Budget",
    "to_componentSource_abs_bound",
    "to_combinedCancellation_order16_abs_bound",
]

NORMAL_FORM_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0RawProductActual",
    "primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant",
    "primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17",
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17",
    "step22OmegaArchWeight_contDiff17_normalForm",
    "primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs17",
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs17",
    "primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_factor_derivative_abs",
    "primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_centeredTaylor17",
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_eq_rawProductDeriv",
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_rawProduct17",
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_rawProduct17",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_rawProduct17_abs",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_centeredTaylor_rawProduct17_budget",
]

BUDGET_AUDIT_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17MajorantRat",
    "primaryFiniteRow0Parent0Split100Sub0RawProduct17LowerScaleBudgetRat",
    "primaryFiniteRow0Parent0Split100Sub0RawProduct17NominalScaleBudgetRat",
    "primaryFiniteRow0Parent0Split100Sub0_rawProduct17_lowerScaleBudget_fail_rat",
    "primaryFiniteRow0Parent0Split100Sub0_rawProduct17_nominalScaleBudget_fail_rat",
]


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    if not path.exists():
        return {symbol: False for symbol in symbols}
    text = path.read_text(encoding="utf-8")
    return {symbol: symbol in text for symbol in symbols}


def all_true(items: dict[str, bool]) -> bool:
    return all(items.values())


def source_expression_hash() -> str | None:
    if not SOURCE_MODEL_BRIDGE.exists():
        return None
    text = SOURCE_MODEL_BRIDGE.read_text(encoding="utf-8")
    marker = "def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource"
    start = text.find(marker)
    if start < 0:
        return None
    next_marker = "\n/--\nExact order-16 source-model bridge"
    end = text.find(next_marker, start)
    if end < 0:
        end = start + 2000
    block = text[start:end].strip()
    return hashlib.sha256(block.encode("utf-8")).hexdigest()


def build_ledger() -> dict[str, object]:
    model_symbols = file_contains(LEAN_MODEL, MODEL_SYMBOLS)
    zero_model_symbols = file_contains(LEAN_MODEL, CONCRETE_ZERO_MODEL_SYMBOLS)
    adapter_symbols = file_contains(LEAN_ADAPTER, ADAPTER_SYMBOLS)
    normal_form_symbols = file_contains(NORMAL_FORM, NORMAL_FORM_SYMBOLS)
    budget_audit_symbols = file_contains(BUDGET_AUDIT, BUDGET_AUDIT_SYMBOLS)
    conditional_checker_present = all_true(model_symbols)
    concrete_zero_model_present = all_true(zero_model_symbols)
    adapter_present = all_true(adapter_symbols)
    normal_form_present = all_true(normal_form_symbols)
    raw_product17_budget_killed = normal_form_present and all_true(budget_audit_symbols)
    expr_hash = source_expression_hash()

    if raw_product17_budget_killed:
        proof_status = "raw_product17_centeredTaylor_bound_checked_but_budget_killed"
        remaining_premise = (
            "centeredTaylor rawProduct17 budget is killed even with TightScaleLower; "
            "need a sharper segmented/polynomial certificate for D^17(RawProductActual) "
            "or a nonzero cancellation-preserving source model"
        )
        current_gap = (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BUDGET_CONSTANT_FAIL"
        )
        next_patch = (
            "Do not spend the centeredTaylor rawProduct17 majorant. Choose a sharper "
            "segmented interval/Horner certificate for D^17(RawProductActual), or a "
            "nonzero cancellation-preserving polynomial model after route review."
        )
    elif normal_form_present:
        proof_status = "raw_product17_centeredTaylor_bound_checked_missing_budget_row"
        remaining_premise = (
            "prove exact budget row: |activeScale| * "
            "RawProductActualOrder17Majorant(OmegaActualDerivativeMajorant17,"
            " ShapeSqActualDerivativeMajorant17) <= DirectZeroModelOrder16Abs"
        )
        current_gap = (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BUDGET_ROW_GAP"
        )
        next_patch = (
            "Evaluate and prove the exact rational budget inequality for the "
            "Lean-checked centeredTaylor rawProduct17 majorant. If it fails, "
            "switch to a sharper segment/polynomial certificate for "
            "D^17(RawProductActual)."
        )
    else:
        proof_status = "conditional_threshold_zero_model_missing_hRemainder"
        remaining_premise = (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp"
        )
        current_gap = (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_TAYLOR_SOURCE_GAP"
        )
        next_patch = (
            "Prove the analytic hRemainder for the threshold zero-model, or "
            "replace it with a sharper cancellation-preserving polynomial model "
            "if that premise is too strong."
        )

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "leanModelFile": str(LEAN_MODEL.relative_to(ROOT)),
        "leanAdapterFile": str(LEAN_ADAPTER.relative_to(ROOT)),
        "leanNormalFormFile": str(NORMAL_FORM.relative_to(ROOT)),
        "leanBudgetAuditFile": str(BUDGET_AUDIT.relative_to(ROOT)),
        "proofStatus": proof_status,
        "concretePayloadKind": "threshold_zero_model",
        "directIntervalAdapterPresent": adapter_present,
        "directModelConditionalCheckerPresent": conditional_checker_present,
        "directZeroModelConcreteRowsPresent": concrete_zero_model_present,
        "rawProduct17NormalFormPresent": normal_form_present,
        "rawProduct17CenteredTaylorBudgetKilled": raw_product17_budget_killed,
        "modelSymbols": model_symbols,
        "concreteZeroModelSymbols": zero_model_symbols,
        "zeroModelRemainderAbsBridgePresent": zero_model_symbols[
            "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_componentSource_abs"
        ],
        "adapterSymbols": adapter_symbols,
        "normalFormSymbols": normal_form_symbols,
        "budgetAuditSymbols": budget_audit_symbols,
        "concretePolynomialDataPresent": concrete_zero_model_present,
        "hornerStageRowsPresent": concrete_zero_model_present,
        "polyRangeRowsPresent": concrete_zero_model_present,
        "sourceLowerUpperRowsPresent": concrete_zero_model_present,
        "order16AbsArithmeticPresent": concrete_zero_model_present,
        "sourceExpressionHashPresent": expr_hash is not None,
        "sourceExpressionHash": expr_hash,
        "sourceIntervalCertValidClaimed": False,
        "step33A1ClosedClaimed": False,
        "remainingAnalyticPremise": remaining_premise,
        "currentGap": current_gap,
        "closedSubgap": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BOUND_INTERFACE_CLOSED"
            if normal_form_present
            else None
        ),
        "failureCodeIfConcreteHornerBudgetFails": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_CONCRETE_HORNER_BUDGET_GAP"
        ),
        "failureCodeIfRawProduct17BoundFails": (
            "STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BUDGET_CONSTANT_FAIL"
        ),
        "nextPatch": next_patch,
    }


def render_markdown(ledger: dict[str, object]) -> str:
    model_symbols = ledger["modelSymbols"]
    adapter_symbols = ledger["adapterSymbols"]
    normal_form_symbols = ledger["normalFormSymbols"]
    budget_audit_symbols = ledger["budgetAuditSymbols"]
    assert isinstance(model_symbols, dict)
    assert isinstance(adapter_symbols, dict)
    assert isinstance(normal_form_symbols, dict)
    assert isinstance(budget_audit_symbols, dict)

    lines = [
        "# Step33A.1-A Direct Order16 Payload Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        f"concretePayloadKind: `{ledger['concretePayloadKind']}`",
        "",
        "## Present",
        "",
        f"- directIntervalAdapterPresent: `{ledger['directIntervalAdapterPresent']}`",
        (
            "- directModelConditionalCheckerPresent: "
            f"`{ledger['directModelConditionalCheckerPresent']}`"
        ),
        f"- directZeroModelConcreteRowsPresent: `{ledger['directZeroModelConcreteRowsPresent']}`",
        f"- zeroModelRemainderAbsBridgePresent: `{ledger['zeroModelRemainderAbsBridgePresent']}`",
        f"- rawProduct17NormalFormPresent: `{ledger['rawProduct17NormalFormPresent']}`",
        (
            "- rawProduct17CenteredTaylorBudgetKilled: "
            f"`{ledger['rawProduct17CenteredTaylorBudgetKilled']}`"
        ),
        "",
        "## Model Symbols",
        "",
    ]
    for symbol, present in model_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    zero_symbols = ledger["concreteZeroModelSymbols"]
    assert isinstance(zero_symbols, dict)
    lines.extend(["", "## Concrete Zero-Model Symbols", ""])
    for symbol, present in zero_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Adapter Symbols", ""])
    for symbol, present in adapter_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## Normal-Form Symbols", ""])
    for symbol, present in normal_form_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(["", "## RawProduct17 Budget-Audit Symbols", ""])
    for symbol, present in budget_audit_symbols.items():
        lines.append(f"- `{symbol}`: `{present}`")
    lines.extend(
        [
            "",
            "## Concrete Payload Fields",
            "",
            f"- concretePolynomialDataPresent: `{ledger['concretePolynomialDataPresent']}`",
            f"- hornerStageRowsPresent: `{ledger['hornerStageRowsPresent']}`",
            f"- polyRangeRowsPresent: `{ledger['polyRangeRowsPresent']}`",
            f"- sourceLowerUpperRowsPresent: `{ledger['sourceLowerUpperRowsPresent']}`",
            f"- order16AbsArithmeticPresent: `{ledger['order16AbsArithmeticPresent']}`",
            f"- sourceExpressionHashPresent: `{ledger['sourceExpressionHashPresent']}`",
            f"- sourceExpressionHash: `{ledger['sourceExpressionHash']}`",
            "",
            "## Boundary",
            "",
            f"- sourceIntervalCertValidClaimed: `{ledger['sourceIntervalCertValidClaimed']}`",
            f"- step33A1ClosedClaimed: `{ledger['step33A1ClosedClaimed']}`",
            "",
            "## Closed Subgap",
            "",
            f"`{ledger['closedSubgap']}`",
            "",
            "## Remaining Analytic Premise",
            "",
            str(ledger["remainingAnalyticPremise"]),
            "",
            "## Current Gap",
            "",
            f"`{ledger['currentGap']}`",
            "",
            "## Failure Code If Concrete Horner Budget Fails",
            "",
            f"`{ledger['failureCodeIfConcreteHornerBudgetFails']}`",
            "",
            "## Failure Code If RawProduct17 Bound Fails",
            "",
            f"`{ledger['failureCodeIfRawProduct17BoundFails']}`",
            "",
            "## Next Patch",
            "",
            str(ledger["nextPatch"]),
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    ledger = build_ledger()
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(JSON_OUT)
    print(MD_OUT)


if __name__ == "__main__":
    main()
