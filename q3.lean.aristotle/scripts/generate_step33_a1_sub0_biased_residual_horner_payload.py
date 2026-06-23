#!/usr/bin/env python3
"""Fail-closed ledger for the biased residual-Horner family payload route.

This script records the checked Lean payload interface and the exact concrete
rows that are still missing.  It emits no numerical rows and does not claim
Step33A.1-A closure.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path


SCHEMA = "q3_psdpd_step33_a1_sub0_biased_residual_horner_payload.v4"

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerPayload.lean"
)
HORNER_CERT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerCert.lean"
)
DIRECT_ADAPTER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload.lean"
)
CONCRETE_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerConcretePayload.lean"
)
REMAINDER_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerRemainderBridge.lean"
)
SCALED_REMAINDER_INTERVAL_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderIntervalPayload.lean"
)

JSON_OUT = REQUEST_DIR / "step33_a1_sub0_biased_residual_horner_payload.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_biased_residual_horner_payload.md"

PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0BiasedResidualHornerFamilyPayloadTarget",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerFamily_residualSourceProp_of_payload_target",
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_biasedResidualHornerFamily_payload",
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_biasedResidualHornerFamily_valid",
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP",
]

HORNER_CERT_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualHornerCert",
    "Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert",
    "Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert",
    "theorem to_residualSourceProp",
    "theorem to_order16DirectIntervalValid",
]

DIRECT_ADAPTER_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs",
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_remainder_bound",
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound",
]

CONCRETE_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_eq_neg_biasCoeff",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_poly_eq_nonzero_sub_biased",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_poly_eq_neg_bias",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_eq_hornerPoly_add_scaledRemainder",
]

REMAINDER_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_sub_hornerPoly_eq_scaledRemainder",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_segmentResidualRemainder_of_scaledRemainder_bound",
]

SCALED_REMAINDER_INTERVAL_PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert",
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderSourceProp_of_interval_payload_target",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_interval_payload",
]


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    if not path.exists():
        return {symbol: False for symbol in symbols}
    text = path.read_text(encoding="utf-8")
    return {symbol: symbol in text for symbol in symbols}


def all_true(items: dict[str, bool]) -> bool:
    return all(items.values())


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def build_ledger() -> dict[str, object]:
    payload_symbols = file_contains(PAYLOAD_FILE, PAYLOAD_SYMBOLS)
    horner_cert_symbols = file_contains(HORNER_CERT_FILE, HORNER_CERT_SYMBOLS)
    direct_adapter_symbols = file_contains(DIRECT_ADAPTER_FILE, DIRECT_ADAPTER_SYMBOLS)
    concrete_bridge_symbols = file_contains(
        CONCRETE_BRIDGE_FILE, CONCRETE_BRIDGE_SYMBOLS
    )
    remainder_bridge_symbols = file_contains(
        REMAINDER_BRIDGE_FILE, REMAINDER_BRIDGE_SYMBOLS
    )
    scaled_remainder_interval_payload_symbols = file_contains(
        SCALED_REMAINDER_INTERVAL_PAYLOAD_FILE,
        SCALED_REMAINDER_INTERVAL_PAYLOAD_SYMBOLS,
    )

    interface_ready = (
        all_true(payload_symbols)
        and all_true(horner_cert_symbols)
        and all_true(direct_adapter_symbols)
    )
    concrete_bridge_ready = all_true(concrete_bridge_symbols)
    remainder_bridge_ready = all_true(remainder_bridge_symbols)
    scaled_remainder_interval_payload_ready = all_true(
        scaled_remainder_interval_payload_symbols
    )

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "biased_residual_horner_family_payload",
        "payloadFile": rel(PAYLOAD_FILE),
        "hornerCertFile": rel(HORNER_CERT_FILE),
        "directAdapterFile": rel(DIRECT_ADAPTER_FILE),
        "concreteBridgeFile": rel(CONCRETE_BRIDGE_FILE),
        "remainderBridgeFile": rel(REMAINDER_BRIDGE_FILE),
        "scaledRemainderIntervalPayloadFile": rel(
            SCALED_REMAINDER_INTERVAL_PAYLOAD_FILE
        ),
        "proofStatus": (
            "biased_residual_horner_remainder_bridge_checked_missing_scaled_remainder_bound"
            if interface_ready and concrete_bridge_ready and remainder_bridge_ready
            else
            "biased_residual_horner_coefficient_bridge_checked_missing_remainder_rows"
            if interface_ready and concrete_bridge_ready
            else "biased_residual_horner_payload_interface_checked_missing_family_rows"
            if interface_ready
            else "biased_residual_horner_payload_interface_incomplete"
        ),
        "payloadInterfacePresent": all_true(payload_symbols),
        "hornerFamilyReceiverPresent": all_true(horner_cert_symbols),
        "directResidualAdapterPresent": all_true(direct_adapter_symbols),
        "coefficientBridgePresent": concrete_bridge_ready,
        "remainderBridgePresent": remainder_bridge_ready,
        "payloadSymbols": payload_symbols,
        "hornerCertSymbols": horner_cert_symbols,
        "directAdapterSymbols": direct_adapter_symbols,
        "concreteBridgeSymbols": concrete_bridge_symbols,
        "remainderBridgeSymbols": remainder_bridge_symbols,
        "scaledRemainderIntervalPayloadSymbols": (
            scaled_remainder_interval_payload_symbols
        ),
        "coefficientBridgeLeanChecked": concrete_bridge_ready,
        "residualRemainderInterfaceLeanChecked": remainder_bridge_ready,
        "scaledRemainderIntervalPayloadInterfacePresent": (
            scaled_remainder_interval_payload_ready
        ),
        "concreteFamilyDataLeanChecked": False,
        "segmentRowsLeanChecked": False,
        "hornerRangeRowsLeanChecked": False,
        "residualRemainderRowsLeanChecked": False,
        "scaledRemainderBoundLeanChecked": False,
        "scaledRemainderIntervalRowsLeanChecked": False,
        "residualBudgetRowsLeanChecked": False,
        "coverLeanChecked": False,
        "canonicalResidualAbsLeanChecked": False,
        "payloadTargetClaimed": False,
        "residualSourcePropClaimed": False,
        "order16DirectIntervalValidClaimed": False,
        "step33A1ClosedClaimed": False,
        "proofGrade": False,
        "currentGap": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP"
            if remainder_bridge_ready
            else
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP"
            if concrete_bridge_ready
            else "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP"
        ),
        "parentGap": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP"
        ),
        "closedInterfaceCode": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_PAYLOAD_INTERFACE_CLOSED"
        ),
        "failureCodeIfFamilyRowsMissing": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP"
        ),
        "failureCodeIfRemainderRowsMissing": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP"
        ),
        "failureCodeIfScaledRemainderBoundMissing": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP"
        ),
        "failureCodeIfScaledRemainderIntervalCertMissing": "INTERVAL_CERT_GAP",
        "failureCodeIfBudgetRowsFail": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_BUDGET_CONSTANT_FAIL"
        ),
        "nextProofObject": (
            "proof-grade bound for "
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp; "
            "the generator-facing whole-expression interval target is "
            "primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget; "
            "then a concrete Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert "
            "with Horner range rows, residual budget rows, cover of [0,1/10], "
            "and residualAbs equal to "
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs"
        ),
        "guard": (
            "Do not claim Step33A.1-A from the interface alone.  The payload "
            "must prove the residual-Horner family Valid predicate and the "
            "canonical residual budget in Lean."
        ),
    }


def render_symbol_section(title: str, symbols: dict[str, bool]) -> list[str]:
    lines = ["", f"## {title}", ""]
    lines.extend(f"- `{symbol}`: `{present}`" for symbol, present in symbols.items())
    return lines


def render_markdown(ledger: dict[str, object]) -> str:
    payload_symbols = ledger["payloadSymbols"]
    horner_cert_symbols = ledger["hornerCertSymbols"]
    direct_adapter_symbols = ledger["directAdapterSymbols"]
    concrete_bridge_symbols = ledger["concreteBridgeSymbols"]
    remainder_bridge_symbols = ledger["remainderBridgeSymbols"]
    scaled_remainder_interval_payload_symbols = ledger[
        "scaledRemainderIntervalPayloadSymbols"
    ]
    assert isinstance(payload_symbols, dict)
    assert isinstance(horner_cert_symbols, dict)
    assert isinstance(direct_adapter_symbols, dict)
    assert isinstance(concrete_bridge_symbols, dict)
    assert isinstance(remainder_bridge_symbols, dict)
    assert isinstance(scaled_remainder_interval_payload_symbols, dict)

    lines = [
        "# Step33A.1-A Biased Residual-Horner Payload Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Present",
        "",
        f"- payloadInterfacePresent: `{ledger['payloadInterfacePresent']}`",
        f"- hornerFamilyReceiverPresent: `{ledger['hornerFamilyReceiverPresent']}`",
        f"- directResidualAdapterPresent: `{ledger['directResidualAdapterPresent']}`",
        f"- coefficientBridgePresent: `{ledger['coefficientBridgePresent']}`",
        f"- remainderBridgePresent: `{ledger['remainderBridgePresent']}`",
        "- scaledRemainderIntervalPayloadInterfacePresent: "
        f"`{ledger['scaledRemainderIntervalPayloadInterfacePresent']}`",
    ]
    lines.extend(render_symbol_section("Payload Interface Symbols", payload_symbols))
    lines.extend(render_symbol_section("Residual-Horner Receiver Symbols", horner_cert_symbols))
    lines.extend(render_symbol_section("Direct Residual Adapter Symbols", direct_adapter_symbols))
    lines.extend(render_symbol_section("Concrete Coefficient Bridge Symbols", concrete_bridge_symbols))
    lines.extend(render_symbol_section("Remainder Bridge Symbols", remainder_bridge_symbols))
    lines.extend(
        render_symbol_section(
            "Scaled Remainder Interval Payload Symbols",
            scaled_remainder_interval_payload_symbols,
        )
    )
    lines.extend(
        [
            "",
            "## Missing Proof Payload",
            "",
            "- coefficientBridgeLeanChecked: "
            f"`{ledger['coefficientBridgeLeanChecked']}`",
            "- residualRemainderInterfaceLeanChecked: "
            f"`{ledger['residualRemainderInterfaceLeanChecked']}`",
            f"- concreteFamilyDataLeanChecked: `{ledger['concreteFamilyDataLeanChecked']}`",
            f"- segmentRowsLeanChecked: `{ledger['segmentRowsLeanChecked']}`",
            f"- hornerRangeRowsLeanChecked: `{ledger['hornerRangeRowsLeanChecked']}`",
            "- residualRemainderRowsLeanChecked: "
            f"`{ledger['residualRemainderRowsLeanChecked']}`",
            "- scaledRemainderBoundLeanChecked: "
            f"`{ledger['scaledRemainderBoundLeanChecked']}`",
            "- scaledRemainderIntervalRowsLeanChecked: "
            f"`{ledger['scaledRemainderIntervalRowsLeanChecked']}`",
            "- residualBudgetRowsLeanChecked: "
            f"`{ledger['residualBudgetRowsLeanChecked']}`",
            f"- coverLeanChecked: `{ledger['coverLeanChecked']}`",
            "- canonicalResidualAbsLeanChecked: "
            f"`{ledger['canonicalResidualAbsLeanChecked']}`",
            f"- payloadTargetClaimed: `{ledger['payloadTargetClaimed']}`",
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
            "Parent gap:",
            "",
            f"`{ledger['parentGap']}`",
            "",
            "## Next Proof Object",
            "",
            str(ledger["nextProofObject"]),
            "",
            "## Failure Codes",
            "",
            f"- closedInterface: `{ledger['closedInterfaceCode']}`",
            f"- familyRowsMissing: `{ledger['failureCodeIfFamilyRowsMissing']}`",
            f"- remainderRowsMissing: `{ledger['failureCodeIfRemainderRowsMissing']}`",
            "- scaledRemainderBoundMissing: "
            f"`{ledger['failureCodeIfScaledRemainderBoundMissing']}`",
            "- scaledRemainderIntervalCertMissing: "
            f"`{ledger['failureCodeIfScaledRemainderIntervalCertMissing']}`",
            f"- budgetRowsFail: `{ledger['failureCodeIfBudgetRowsFail']}`",
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
    print(ledger["currentGap"])


if __name__ == "__main__":
    main()
