#!/usr/bin/env python3
"""Fail-closed ledger for the direct nonzero-model scaled-remainder payload.

The target is the same-unit signed residual

    CombinedCancellationOrder16ComponentSource - CombinedOrder16NonzeroModelPoly

on `[0, 1/10]`, at the canonical `BiasedResidualRemainderAbs` budget.  This
script does not emit proof rows and does not claim Step33A.1-A closure.  It
records the exact generator-facing payload surface and the first missing
proof-grade certificate.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_combined_order16_"
    "scaled_remainder_direct_payload.v2"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

DIRECT_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean"
)
ZERO_MODEL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderZeroModelPayload.lean"
)
INTERVAL_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderIntervalPayload.lean"
)
REMAINDER_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerRemainderBridge.lean"
)
P45_FULL_TAYLOR_BRIDGE_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean"
)
ORDER16_NONZERO_MODEL_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean"
)

JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.md"
)

DIRECT_PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_direct_payload",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval",
]

ZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderSourceProp_of_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_zeroModel",
]

INTERVAL_PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert",
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget",
]

REMAINDER_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound",
]

P45_FULL_TAYLOR_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_eq_scaledCancellationRhs",
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_bound_of_scaledCancellationRhs_bound",
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_scaledCancellationRhs_bound",
]

ORDER16_NONZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelSource",
]

CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "NONZERO_MODEL_INTERVAL_CERT_GAP"
)
PARENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_"
    "SCALED_REMAINDER_BOUND_GAP"
)
P45_REUSE_FAILURE = (
    "STEP33_A1_SUB0_P45_FULL_TAYLOR_ORDER16_SOURCE_MISMATCH"
)
FIRST_GENERATED_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
    "nonzeroModel_interval_generated"
)
FIRST_GENERATED_SOURCE_PROP_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
    "nonzeroModel_sourceProp_generated"
)


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


def summarize_existing_ledger(path: Path, keys: list[str]) -> dict[str, Any]:
    data = load_json(path)
    out: dict[str, Any] = {"path": rel(path), "exists": bool(data)}
    for key in keys:
        out[key] = data.get(key)
    return out


def build_ledger() -> dict[str, Any]:
    direct_symbols = file_contains(DIRECT_PAYLOAD_FILE, DIRECT_PAYLOAD_SYMBOLS)
    zero_model_symbols = file_contains(ZERO_MODEL_FILE, ZERO_MODEL_SYMBOLS)
    interval_symbols = file_contains(INTERVAL_PAYLOAD_FILE, INTERVAL_PAYLOAD_SYMBOLS)
    remainder_bridge_symbols = file_contains(
        REMAINDER_BRIDGE_FILE, REMAINDER_BRIDGE_SYMBOLS
    )
    p45_full_taylor_symbols = file_contains(
        P45_FULL_TAYLOR_BRIDGE_FILE, P45_FULL_TAYLOR_BRIDGE_SYMBOLS
    )
    order16_nonzero_model_symbols = file_contains(
        ORDER16_NONZERO_MODEL_FILE, ORDER16_NONZERO_MODEL_SYMBOLS
    )

    direct_surface_present = all_true(direct_symbols)
    zero_model_bridge_present = all_true(zero_model_symbols)
    interval_surface_present = all_true(interval_symbols)
    remainder_bridge_present = all_true(remainder_bridge_symbols)
    p45_full_taylor_bridge_present = all_true(p45_full_taylor_symbols)
    order16_nonzero_model_bridge_present = all_true(order16_nonzero_model_symbols)

    proof_status = (
        "direct_nonzero_model_payload_surface_checked_missing_interval_cert"
        if direct_surface_present
        and zero_model_bridge_present
        and interval_surface_present
        and remainder_bridge_present
        else "direct_nonzero_model_payload_surface_incomplete"
    )

    prior_ledgers = {
        "biasedScaledRemainderInterval": summarize_existing_ledger(
            REQUEST_DIR
            / "step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.json",
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "nonzeroModelResidualBridgeLeanChecked",
                "nonzeroModelResidualSourceBoundLeanChecked",
            ],
        ),
        "biasedResidualHornerPayload": summarize_existing_ledger(
            REQUEST_DIR / "step33_a1_sub0_biased_residual_horner_payload.json",
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "scaledRemainderBoundLeanChecked",
                "nonzeroModelResidualBridgeLeanChecked",
                "nonzeroModelResidualSourceBoundLeanChecked",
            ],
        ),
    }

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "direct_nonzero_model_scaled_remainder_interval",
        "directPayloadFile": rel(DIRECT_PAYLOAD_FILE),
        "zeroModelPayloadFile": rel(ZERO_MODEL_FILE),
        "intervalPayloadFile": rel(INTERVAL_PAYLOAD_FILE),
        "remainderBridgeFile": rel(REMAINDER_BRIDGE_FILE),
        "p45FullTaylorBridgeFile": rel(P45_FULL_TAYLOR_BRIDGE_FILE),
        "order16NonzeroModelFile": rel(ORDER16_NONZERO_MODEL_FILE),
        "directPayloadSymbols": direct_symbols,
        "zeroModelSymbols": zero_model_symbols,
        "intervalPayloadSymbols": interval_symbols,
        "remainderBridgeSymbols": remainder_bridge_symbols,
        "p45FullTaylorBridgeSymbols": p45_full_taylor_symbols,
        "order16NonzeroModelSymbols": order16_nonzero_model_symbols,
        "directPayloadSurfacePresent": direct_surface_present,
        "zeroModelBridgePresent": zero_model_bridge_present,
        "intervalPayloadSurfacePresent": interval_surface_present,
        "remainderBridgePresent": remainder_bridge_present,
        "p45FullTaylorBridgePresent": p45_full_taylor_bridge_present,
        "order16NonzeroModelBridgePresent": order16_nonzero_model_bridge_present,
        "proofStatus": proof_status,
        "proofGrade": False,
        "currentGap": CURRENT_GAP,
        "parentGap": PARENT_GAP,
        "firstFailureCode": CURRENT_GAP,
        "p45FullTaylorReuseVerdict": "not_spendable_for_order16_direct_source_bound",
        "p45FullTaylorReuseFailureCode": P45_REUSE_FAILURE,
        "proshkaRouteReviewDecision": "CHOSEN: A",
        "proshkaRouteReviewQuestion": (
            "Does the existing P45/full-Taylor interval machinery prove the "
            "order-16 ComponentSource - NonzeroModelPoly source bound, or is "
            "a separate direct certificate target still needed?"
        ),
        "proshkaRouteReviewAnswer": (
            "A: proceed with the direct rational/Horner interval generator; "
            "P45/full-Taylor bounds a different derivative-level expression "
            "and does not prove the uniform order-16 source-minus-nonzero-model "
            "interval."
        ),
        "directNonzeroModelIntervalRowsLeanChecked": False,
        "directNonzeroModelSourcePropLeanChecked": False,
        "zeroModelPayloadTargetLeanChecked": zero_model_bridge_present,
        "step33A1ClosedClaimed": False,
        "doNotSplitSummands": True,
        "targetExpression": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16"
            "ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0"
            "CombinedOrder16NonzeroModelPoly eta"
        ),
        "targetBudget": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16Biased"
            "ResidualRemainderAbs"
        ),
        "targetProp": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
            "ScaledRemainderNonzeroModelSourceProp"
        ),
        "targetPayload": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
            "ScaledRemainderDirectPayloadTarget"
        ),
        "firstGeneratedIntervalTheorem": FIRST_GENERATED_INTERVAL_THEOREM,
        "firstGeneratedSourcePropTheorem": FIRST_GENERATED_SOURCE_PROP_THEOREM,
        "whyP45FullTaylorIsNotEnough": (
            "The P45/full-Taylor bridge rewrites a derivative-level residual "
            "error into the scaled cancellation RHS. The current direct target "
            "is the order-16 source residual ComponentSource - NonzeroModelPoly, "
            "which Lean identifies with ActiveScaleCoeff * D^16"
            "(ComponentProductCancellationResidual) plus the same-unit "
            "scale-mismatch nominal-product term. No local theorem converts the "
            "P45/full-Taylor interval into this order-16 source interval."
        ),
        "theoremShape": (
            "prove a signed interval on [0,1/10] for ComponentSource - "
            "NonzeroModelPoly inside +/- BiasedResidualRemainderAbs; then "
            "use primaryFiniteRow0Parent0Split100Sub0_"
            "combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_"
            "full_cell_interval or a direct family payload target"
        ),
        "certificateShape": [
            "segment cells covering [0,1/10]",
            "whole signed expression polynomial/range rows",
            "whole-expression remainder rows",
            "per-segment lower/upper budget rows",
            "global residualAbs = BiasedResidualRemainderAbs",
        ],
        "priorLedgers": prior_ledgers,
        "guard": (
            "This is an interface and fail-closed ledger only.  It does not "
            "prove the interval rows, and it must not be treated as Step33A.1-A "
            "closure until the direct nonzero-model source proposition is "
            "Lean-checked or backed by proof-grade generated rows."
        ),
    }


def render_symbols(title: str, symbols: dict[str, bool]) -> list[str]:
    return ["", f"## {title}", ""] + [
        f"- `{symbol}`: `{present}`" for symbol, present in symbols.items()
    ]


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Direct Scaled-Remainder Payload Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Status",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- directPayloadSurfacePresent: `{ledger['directPayloadSurfacePresent']}`",
        f"- zeroModelBridgePresent: `{ledger['zeroModelBridgePresent']}`",
        f"- intervalPayloadSurfacePresent: `{ledger['intervalPayloadSurfacePresent']}`",
        f"- remainderBridgePresent: `{ledger['remainderBridgePresent']}`",
        f"- p45FullTaylorBridgePresent: `{ledger['p45FullTaylorBridgePresent']}`",
        "- order16NonzeroModelBridgePresent: "
        f"`{ledger['order16NonzeroModelBridgePresent']}`",
        "- directNonzeroModelIntervalRowsLeanChecked: "
        f"`{ledger['directNonzeroModelIntervalRowsLeanChecked']}`",
        "- directNonzeroModelSourcePropLeanChecked: "
        f"`{ledger['directNonzeroModelSourcePropLeanChecked']}`",
        "- zeroModelPayloadTargetLeanChecked: "
        f"`{ledger['zeroModelPayloadTargetLeanChecked']}`",
        f"- step33A1ClosedClaimed: `{ledger['step33A1ClosedClaimed']}`",
        f"- doNotSplitSummands: `{ledger['doNotSplitSummands']}`",
        "",
        "## Current Gap",
        "",
        f"`{ledger['currentGap']}`",
        "",
        "Parent gap:",
        "",
        f"`{ledger['parentGap']}`",
        "",
        "First failure code if the direct route fails:",
        "",
        f"`{ledger['firstFailureCode']}`",
        "",
        "P45/full-Taylor reuse verdict:",
        "",
        f"`{ledger['p45FullTaylorReuseVerdict']}`",
        "",
        "P45/full-Taylor reuse failure code:",
        "",
        f"`{ledger['p45FullTaylorReuseFailureCode']}`",
        "",
        "## Target",
        "",
        f"- expression: `{ledger['targetExpression']}`",
        f"- budget: `{ledger['targetBudget']}`",
        f"- prop: `{ledger['targetProp']}`",
        f"- payload: `{ledger['targetPayload']}`",
        f"- first interval theorem: `{ledger['firstGeneratedIntervalTheorem']}`",
        f"- first source-prop theorem: `{ledger['firstGeneratedSourcePropTheorem']}`",
        "",
        "## Route Review",
        "",
        f"- decision: `{ledger['proshkaRouteReviewDecision']}`",
        f"- question: {ledger['proshkaRouteReviewQuestion']}",
        f"- answer: {ledger['proshkaRouteReviewAnswer']}",
        "",
        "## Why P45/full-Taylor Is Not Enough",
        "",
        str(ledger["whyP45FullTaylorIsNotEnough"]),
        "",
        "## Theorem Shape",
        "",
        str(ledger["theoremShape"]),
        "",
        "## Certificate Shape",
        "",
    ]
    lines.extend(f"- {item}" for item in ledger["certificateShape"])
    lines.extend(render_symbols("Direct Payload Symbols", ledger["directPayloadSymbols"]))
    lines.extend(render_symbols("Zero Model Symbols", ledger["zeroModelSymbols"]))
    lines.extend(render_symbols("Interval Payload Symbols", ledger["intervalPayloadSymbols"]))
    lines.extend(render_symbols("Remainder Bridge Symbols", ledger["remainderBridgeSymbols"]))
    lines.extend(
        render_symbols(
            "P45/full-Taylor Bridge Symbols", ledger["p45FullTaylorBridgeSymbols"]
        )
    )
    lines.extend(
        render_symbols(
            "Order16 Nonzero-Model Symbols", ledger["order16NonzeroModelSymbols"]
        )
    )
    lines.extend(["", "## Prior Ledgers", ""])
    for name, summary in ledger["priorLedgers"].items():
        lines.append(f"### {name}")
        lines.append("")
        for key, value in summary.items():
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Guard", "", str(ledger["guard"]), ""])
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(ledger["proofStatus"])
    print(ledger["firstFailureCode"])
    print(ledger["currentGap"])
    print(ledger["p45FullTaylorReuseVerdict"])


if __name__ == "__main__":
    main()
