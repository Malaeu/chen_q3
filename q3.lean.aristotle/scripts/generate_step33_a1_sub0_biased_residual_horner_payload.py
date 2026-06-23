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


SCHEMA = "q3_psdpd_step33_a1_sub0_biased_residual_horner_payload.v1"

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

    interface_ready = (
        all_true(payload_symbols)
        and all_true(horner_cert_symbols)
        and all_true(direct_adapter_symbols)
    )

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "biased_residual_horner_family_payload",
        "payloadFile": rel(PAYLOAD_FILE),
        "hornerCertFile": rel(HORNER_CERT_FILE),
        "directAdapterFile": rel(DIRECT_ADAPTER_FILE),
        "proofStatus": (
            "biased_residual_horner_payload_interface_checked_missing_family_rows"
            if interface_ready
            else "biased_residual_horner_payload_interface_incomplete"
        ),
        "payloadInterfacePresent": all_true(payload_symbols),
        "hornerFamilyReceiverPresent": all_true(horner_cert_symbols),
        "directResidualAdapterPresent": all_true(direct_adapter_symbols),
        "payloadSymbols": payload_symbols,
        "hornerCertSymbols": horner_cert_symbols,
        "directAdapterSymbols": direct_adapter_symbols,
        "concreteFamilyDataLeanChecked": False,
        "segmentRowsLeanChecked": False,
        "hornerRangeRowsLeanChecked": False,
        "residualRemainderRowsLeanChecked": False,
        "residualBudgetRowsLeanChecked": False,
        "coverLeanChecked": False,
        "canonicalResidualAbsLeanChecked": False,
        "payloadTargetClaimed": False,
        "residualSourcePropClaimed": False,
        "order16DirectIntervalValidClaimed": False,
        "step33A1ClosedClaimed": False,
        "proofGrade": False,
        "currentGap": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP"
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
        "failureCodeIfBudgetRowsFail": (
            "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_BUDGET_CONSTANT_FAIL"
        ),
        "nextProofObject": (
            "a concrete Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert "
            "with segment data, Horner range rows, residual remainder rows, "
            "residual budget rows, cover of [0,1/10], and residualAbs equal "
            "to primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs"
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
    assert isinstance(payload_symbols, dict)
    assert isinstance(horner_cert_symbols, dict)
    assert isinstance(direct_adapter_symbols, dict)

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
    ]
    lines.extend(render_symbol_section("Payload Interface Symbols", payload_symbols))
    lines.extend(render_symbol_section("Residual-Horner Receiver Symbols", horner_cert_symbols))
    lines.extend(render_symbol_section("Direct Residual Adapter Symbols", direct_adapter_symbols))
    lines.extend(
        [
            "",
            "## Missing Proof Payload",
            "",
            f"- concreteFamilyDataLeanChecked: `{ledger['concreteFamilyDataLeanChecked']}`",
            f"- segmentRowsLeanChecked: `{ledger['segmentRowsLeanChecked']}`",
            f"- hornerRangeRowsLeanChecked: `{ledger['hornerRangeRowsLeanChecked']}`",
            "- residualRemainderRowsLeanChecked: "
            f"`{ledger['residualRemainderRowsLeanChecked']}`",
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
            "## Next Proof Object",
            "",
            str(ledger["nextProofObject"]),
            "",
            "## Failure Codes",
            "",
            f"- closedInterface: `{ledger['closedInterfaceCode']}`",
            f"- familyRowsMissing: `{ledger['failureCodeIfFamilyRowsMissing']}`",
            f"- remainderRowsMissing: `{ledger['failureCodeIfRemainderRowsMissing']}`",
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
