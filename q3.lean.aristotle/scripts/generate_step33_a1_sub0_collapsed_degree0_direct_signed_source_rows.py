#!/usr/bin/env python3
"""Fail-closed gatekeeper for direct collapsed degree-0 signed-source rows.

The active v21 direct contract selects the already-subtracted signed source

    ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)

as the next proof-producing object.  This script records the exact row payload
surface and refuses to emit Lean unless proof-grade uniform segment rows and
the exact rational budgets are present.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_collapsed_degree0_"
    "direct_signed_source_payload_gate.v6"
)
ROUTE = "collapsed_degree0_direct_signed_source_payload_gate"
PROOF_STATUS = "fail_closed_missing_direct_signed_source_payload"
CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POLY_DERIV_SIGNED_SOURCE_GAP"
)
BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "BUDGET_CONSTANT_FAIL"
)
PARENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "DIRECT_ROW_SOURCE_GAP"
)
UNIFORM_SEGMENT_ROWS_SUBGAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP"
)
SEGMENT0_TAYLOR_MODEL_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "DIRECT_SIGNED_SEGMENT0_TAYLOR_MODEL_SOURCE_GAP"
)

PROSHKA_FIRST_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "collapsedDegree0_signedSource_segment0_interval_generated"
)
PROSHKA_ROUTE_REVIEW = {
    "used": True,
    "source": "in-app Browser/Computer Use Proshka route review",
    "latestStatus": "answered",
    "recommendedChoice": "A",
    "exactNextPatchScript": (
        "scripts/generate_step33_a1_sub0_collapsed_degree0_signed_source.py"
    ),
    "targetLeanFile": (
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
        "CollapsedDegree0DirectSignedSourcePayload.lean"
    ),
    "firstTheorem": PROSHKA_FIRST_THEOREM,
    "firstFailureCode": CURRENT_GAP,
}
PROSHKA_FOLLOW_UP_REVIEW = {
    "used": True,
    "source": "in-app Browser/Computer Use Proshka route review",
    "latestRequest": (
        "Step33A.1-A direct signed-source segment0 payload source rows"
    ),
    "latestStatus": "answered",
    "recommendedChoice": "A",
    "firstFile": (
        "scripts/generate_step33_a1_sub0_collapsed_degree0_signed_source.py"
    ),
    "targetLeanFile": (
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
        "CollapsedDegree0DirectSignedSourcePayload.lean"
    ),
    "firstTheoremOrObject": (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_directSignedSourceFamily_valid"
    ),
    "firstSegmentTheorem": PROSHKA_FIRST_THEOREM,
    "question": (
        "Choose the smallest proof-grade source for "
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_signedSource_segment0_interval_generated."
    ),
    "sourceRowsNeeded": [
        "exact segment cover",
        (
            "signed lower/upper rows for the complete ActiveScaleCoeff * "
            "D17(ComponentProductActual) - deriv(NominalOrder16Poly)"
        ),
        "derivAbs = max(-lower, upper)",
        "exact degree-0 remainder budget",
        "collapsed segment remainder",
        "DirectHorner/final budget rows",
    ],
    "whyProofGrade": (
        "The already checked degree-0 receiver, center row, nominal "
        "polynomial derivative rows, and segment-family adapter can consume "
        "a rational/interval certificate for the whole subtracted derivative. "
        "The new proof cargo must be those exact rows, not a point probe or "
        "a scalar diagnostic."
    ),
    "currentLocalDecision": (
        "build_direct_rational_interval_generator_for_complete_signed_expression"
    ),
    "currentFailureCode": CURRENT_GAP,
    "doNotUse": [
        "raw-D17 factorwise or two-segment payloads",
        "RawProduct18 absolute majorant",
        "activeActual-alone budget",
        "P45 or zero-model budgets",
        "sampled/float intervals",
        "center jets as uniform cell rows",
        "new alias/receiver wrappers",
    ],
}
PROSHKA_SEGMENT0_TAYLOR_REVIEW = {
    "used": True,
    "source": "in-app Browser/Computer Use Proshka route review",
    "latestStatus": "answered",
    "nextPatch": (
        "direct segment-0 Taylor-model certificate for the complete "
        "already-subtracted signed expression"
    ),
    "firstScript": (
        "scripts/generate_step33_a1_sub0_collapsed_degree0_"
        "direct_signed_segment0.py"
    ),
    "firstGeneratedArtifact": (
        "ACTIVE/requests/step33_bootstrap/"
        "step33_a1_sub0_collapsed_degree0_direct_signed_segment0_"
        "taylor_model.json"
    ),
    "targetLeanFile": (
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
        "CollapsedDegree0DirectSignedSourceSegment0Payload.lean"
    ),
    "modelRemainderTheorem": (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_signedSource_segment0_model_remainder_generated"
    ),
    "firstSegmentTheorem": PROSHKA_FIRST_THEOREM,
    "failureCode": SEGMENT0_TAYLOR_MODEL_GAP,
    "stopRule": (
        "Do not emit Payload.lean with a conditional field. Stop if no "
        "Lean-checkable whole-expression remainder theorem can be produced "
        "from local signed jets and order18 bounds."
    ),
}

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

SIGNED_SOURCE_RECEIVER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0SignedSourcePayload.lean"
)
NOMINAL_POLY_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0NominalPolyDerivRows.lean"
)
POINT_RAT_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0PointSlopeRatPayload.lean"
)
POINT_RAT_AUDIT_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rat_audit.json"
)
RAW_D17_SHARP_BUDGET_KILL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SharpTwoSegmentBudgetKill.lean"
)
RAW_D17_TWO_SEGMENT_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean"
)
DIRECT_V21_LEDGER = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json"
)
SIGNED_SOURCE_V10_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_signed_source.json"
)
SEGMENT0_TAYLOR_MODEL_LEDGER = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_direct_signed_segment0_taylor_model.json"
)
SEGMENT0_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0DirectSignedSourceSegment0Payload.lean"
)
TARGET_LEAN_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0DirectSignedSourcePayload.lean"
)

JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_direct_signed_source_rows.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_direct_signed_source_rows.md"
)

SUPPORT_SYMBOLS: dict[Path, list[str]] = {
    SIGNED_SOURCE_RECEIVER_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr",
        "Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsed_degree0_remainder_of_signed_segment_family_cert"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_signedSegmentValid_of_raw_poly_intervals"
        ),
    ],
    NOMINAL_POLY_ROWS_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "nominalOrder16Poly_deriv_segment_interval_generated"
        ),
    ],
    POINT_RAT_PAYLOAD_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_pointRow_generated"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "componentProductActual_order17_point_interval_rat_generated"
        ),
    ],
    RAW_D17_SHARP_BUDGET_KILL_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_sharp_twoSegment_budget_not_spendable"
        ),
    ],
    RAW_D17_TWO_SEGMENT_PAYLOAD_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_twoSegment_budget_not_spendable"
        ),
    ],
}

TARGET_SYMBOLS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_directSignedSource_segment_family_generated"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_directSignedSource_derivAbs_budget_pass_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_directSignedSource_degree0_budget_pass_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "combinedOrder16ScaledRemainder_collapsed_segment_remainder"
    ),
]
SEGMENT0_SYMBOLS = [
    PROSHKA_FIRST_THEOREM,
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_directSignedSource_segment0_valid_generated"
    ),
]
PARENT_SURFACE_SYMBOLS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0"
        "DirectSignedSourceSegment0OnlyFamily"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_directSignedSource_segment0_parent_valid"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_directSignedSource_segment0_only_family_not_cover"
    ),
]
RAW_D17_SHARP_SUPPORT_SYMBOLS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0"
        "DirectSignedSourceRawD17SharpTwoSegmentFamily"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "directSignedSource_rawD17SharpTwoSegment_segment_rows_valid"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "directSignedSource_rawD17SharpTwoSegment_cover"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "directSignedSource_rawD17SharpTwoSegment_budget_not_spendable"
    ),
]


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected JSON object root")
    return data


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def line_of(text: str, needle: str) -> int | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        if needle in line:
            return idx
    return None


def symbol_audit(path: Path, symbols: list[str]) -> dict[str, dict[str, Any]]:
    text = read_text(path)
    return {
        symbol: {
            "present": symbol in text,
            "line": line_of(text, symbol),
        }
        for symbol in symbols
    }


def all_present(audit: dict[str, dict[str, Any]]) -> bool:
    return all(row["present"] for row in audit.values())


def direct_v21_active(direct: dict[str, Any]) -> bool:
    contract = direct.get("preferredCollapsedLowDegreeRowSourceContract")
    if not isinstance(contract, dict):
        return False
    return (
        direct.get("schema")
        == "q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.v21"
        and contract.get("firstFailureCodeIfRowsMissing") == CURRENT_GAP
        and contract.get("parentFailureCodeIfRowsMissing") == PARENT_GAP
    )


def build_ledger() -> dict[str, Any]:
    direct_ledger = load_json(DIRECT_V21_LEDGER)
    signed_source_ledger = load_json(SIGNED_SOURCE_V10_LEDGER)
    point_rat_audit = load_json(POINT_RAT_AUDIT_LEDGER)
    segment0_taylor_ledger = load_json(SEGMENT0_TAYLOR_MODEL_LEDGER)

    support: dict[str, Any] = {}
    for path, symbols in SUPPORT_SYMBOLS.items():
        audit = symbol_audit(path, symbols)
        support[rel(path)] = {
            "exists": path.exists(),
            "sha256": sha256_file(path),
            "allSymbolsPresent": all_present(audit),
            "symbols": audit,
        }

    target_audit = symbol_audit(TARGET_LEAN_FILE, TARGET_SYMBOLS)
    segment0_audit = symbol_audit(SEGMENT0_PAYLOAD_FILE, SEGMENT0_SYMBOLS)
    parent_surface_audit = symbol_audit(TARGET_LEAN_FILE, PARENT_SURFACE_SYMBOLS)
    raw_d17_sharp_support_audit = symbol_audit(
        TARGET_LEAN_FILE, RAW_D17_SHARP_SUPPORT_SYMBOLS
    )
    target_present = all_present(target_audit)
    segment0_present = all_present(segment0_audit)
    parent_surface_present = all_present(parent_surface_audit)
    raw_d17_sharp_support_present = all_present(raw_d17_sharp_support_audit)
    active_contract = direct_v21_active(direct_ledger)
    receiver_ready = support[rel(SIGNED_SOURCE_RECEIVER_FILE)]["allSymbolsPresent"]
    nominal_poly_ready = support[rel(NOMINAL_POLY_ROWS_FILE)]["allSymbolsPresent"]
    point_rows_present = support[rel(POINT_RAT_PAYLOAD_FILE)]["allSymbolsPresent"]
    raw_d17_budget_killed = (
        support[rel(RAW_D17_SHARP_BUDGET_KILL_FILE)]["allSymbolsPresent"]
        or support[rel(RAW_D17_TWO_SEGMENT_PAYLOAD_FILE)]["allSymbolsPresent"]
    )

    if target_present:
        proof_status = "direct_signed_source_rows_payload_present"
        current_gap = None
        first_failure = None
    elif segment0_present and parent_surface_present:
        proof_status = "segment0_checked_missing_uniform_family_budget"
        current_gap = UNIFORM_SEGMENT_ROWS_SUBGAP
        first_failure = UNIFORM_SEGMENT_ROWS_SUBGAP
    elif not active_contract:
        proof_status = "fail_closed_missing_v21_direct_contract"
        current_gap = PARENT_GAP
        first_failure = PARENT_GAP
    elif not receiver_ready:
        proof_status = "fail_closed_missing_signed_source_receiver"
        current_gap = CURRENT_GAP
        first_failure = CURRENT_GAP
    else:
        proof_status = PROOF_STATUS
        current_gap = CURRENT_GAP
        first_failure = CURRENT_GAP

    should_emit_lean_payload = (
        active_contract
        and receiver_ready
        and nominal_poly_ready
        and target_present
        and False
    )

    return {
        "schema": SCHEMA,
        "route": ROUTE,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "proofGrade": False,
        "proofStatus": proof_status,
        "currentGap": current_gap,
        "parentGap": PARENT_GAP,
        "firstFailureCode": first_failure,
        "uniformSegmentRowsSubgap": UNIFORM_SEGMENT_ROWS_SUBGAP,
        "budgetFailureCode": BUDGET_FAIL,
        "computerUseRouteReview": PROSHKA_ROUTE_REVIEW,
        "computerUseFollowUpReview": PROSHKA_FOLLOW_UP_REVIEW,
        "computerUseSegment0TaylorReview": PROSHKA_SEGMENT0_TAYLOR_REVIEW,
        "selectedProofGradeSource": (
            "direct_rational_interval_generator_for_complete_signed_expression"
        ),
        "selectedFirstRowSource": (
            "direct_segment0_taylor_model_certificate_for_complete_signed_expression"
        ),
        "activeDirectV21Contract": active_contract,
        "directV21Ledger": rel(DIRECT_V21_LEDGER),
        "signedSourceV10Ledger": rel(SIGNED_SOURCE_V10_LEDGER),
        "signedSourceV10SelectedNextPatch": signed_source_ledger.get(
            "selectedNextPatch"
        ),
        "segment0TaylorModelLedger": rel(SEGMENT0_TAYLOR_MODEL_LEDGER),
        "segment0TaylorModelGateProofStatus": segment0_taylor_ledger.get(
            "proofStatus"
        ),
        "segment0TaylorModelGateGap": segment0_taylor_ledger.get("currentGap"),
        "segment0TaylorModelTargetPayloadPresent": segment0_taylor_ledger.get(
            "targetPayloadPresent"
        ),
        "targetLeanFile": rel(TARGET_LEAN_FILE),
        "targetLeanFileExists": TARGET_LEAN_FILE.exists(),
        "targetSymbols": target_audit,
        "segment0PayloadFile": rel(SEGMENT0_PAYLOAD_FILE),
        "segment0PayloadFileExists": SEGMENT0_PAYLOAD_FILE.exists(),
        "segment0Symbols": segment0_audit,
        "segment0PayloadPresent": segment0_present,
        "parentSegment0OnlySurfaceSymbols": parent_surface_audit,
        "parentSegment0OnlySurfacePresent": parent_surface_present,
        "rawD17SharpSupportSymbols": raw_d17_sharp_support_audit,
        "rawD17SharpSupportPresent": raw_d17_sharp_support_present,
        "rawD17SharpSupportMeaning": (
            "Lean proves this support-only two-segment class has valid segment "
            "rows and full cover, but also proves its collapsed degree-0 "
            "budget is not spendable.  It is a kill certificate, not closure."
        ),
        "targetPayloadPresent": target_present,
        "shouldEmitLeanPayload": should_emit_lean_payload,
        "receiverReady": receiver_ready,
        "nominalPolyRowsReady": nominal_poly_ready,
        "pointRowsPresentButInsufficient": point_rows_present,
        "pointRowsReason": (
            "Point-row Rat payload is checked support, but it is not a "
            "uniform segment-family certificate."
        ),
        "pointRatAuditProofStatus": point_rat_audit.get("proofStatus"),
        "rawD17FactorRouteBudgetKilled": raw_d17_budget_killed,
        "rawD17FactorRouteReason": (
            "The sharp/two-segment raw-D17 factorwise class is retained as "
            "support evidence only; its exact budget-not-spendable theorem "
            "prevents using it as the active v21 next patch."
        ),
        "supportSurfaces": support,
        "requiredRowsBeforeLean": [
            {
                "id": "L0_segment_cover",
                "object": (
                    "generated proof-grade cover for Set.Icc 0 (1/10)"
                ),
                "status": "missing",
                "failureCode": UNIFORM_SEGMENT_ROWS_SUBGAP,
            },
            {
                "id": "L0a_segment0_interval",
                "object": (
                    "exact Rat interval theorem for the whole signed "
                    "expression on the first generated segment"
                ),
                "status": "checked" if segment0_present else "missing",
                "targetTheorem": PROSHKA_FIRST_THEOREM,
                "failureCode": None if segment0_present else SEGMENT0_TAYLOR_MODEL_GAP,
            },
            {
                "id": "L0a_source_segment0_taylor_model",
                "object": (
                    "direct segment0 Taylor-model source: modelCoeff, "
                    "remainderAbs, and whole-expression remainder theorem"
                ),
                "status": (
                    "closed_by_local_factor_taylor18_payload"
                    if segment0_present
                    else "missing"
                ),
                "targetTheorem": (
                    "primaryFiniteRow0Parent0Split100Sub0_"
                    "collapsedDegree0_signedSource_segment0_"
                    "model_remainder_generated"
                ),
                "failureCode": None if segment0_present else SEGMENT0_TAYLOR_MODEL_GAP,
            },
            {
                "id": "L1_uniform_direct_signed_source_segment_rows",
                "object": (
                    "uniform lower/upper rows for ActiveScaleCoeff * "
                    "D17(ComponentProductActual) - "
                    "deriv(NominalOrder16Poly) on every generated segment"
                ),
                "status": "missing",
                "failureCode": UNIFORM_SEGMENT_ROWS_SUBGAP,
            },
            {
                "id": "L2_deriv_abs_budget",
                "object": "exact rational lower/upper containment in [-derivAbs, derivAbs]",
                "status": "missing",
                "failureCode": BUDGET_FAIL,
            },
            {
                "id": "L3_degree0_budget",
                "object": (
                    "exact rational proof that coeffErrorAbs + "
                    "derivAbs * (1/20) <= polyErrorAbs"
                ),
                "status": "missing",
                "failureCode": BUDGET_FAIL,
            },
        ],
        "doNotUse": [
            "point rows as uniform segment rows",
            "raw-D17 factorwise/two-segment rows",
            "raw-D17 sharp/two-segment budget-killed factor route as closure",
            "RawProduct18 absolute majorant",
            "activeActual-alone budget",
            "P45/zero-model budgets",
            "sampled diagnostics as proof",
            "center jets as uniform bounds",
            "new alias/receiver wrappers before source rows exist",
            "DirectConcretePayload.lean before L0-L3 and downstream Horner rows pass",
        ],
        "nextImplementablePatch": (
            "Generate/prove the remaining direct signed-source segment rows "
            "covering the rest of Set.Icc 0 (1/10), then prove the exact "
            "derivAbs and degree-0 budget rows.  Segment0 is checked, and "
            "the parent surface now Lean-proves that segment0-only is not a "
            "cover."
        ),
    }


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Direct Signed Source Rows Gate",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Verdict",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- parentGap: `{ledger['parentGap']}`",
        f"- firstFailureCode: `{ledger['firstFailureCode']}`",
        f"- uniformSegmentRowsSubgap: `{ledger['uniformSegmentRowsSubgap']}`",
        f"- budgetFailureCode: `{ledger['budgetFailureCode']}`",
        f"- computerUseChoice: `{ledger['computerUseRouteReview']['recommendedChoice']}`",
        f"- computerUseFirstTheorem: `{ledger['computerUseRouteReview']['firstTheorem']}`",
        f"- computerUseFollowUpStatus: `{ledger['computerUseFollowUpReview']['latestStatus']}`",
        f"- computerUseFollowUpChoice: `{ledger['computerUseFollowUpReview']['recommendedChoice']}`",
        f"- computerUseSegment0TaylorStatus: `{ledger['computerUseSegment0TaylorReview']['latestStatus']}`",
        f"- selectedProofGradeSource: `{ledger['selectedProofGradeSource']}`",
        f"- selectedFirstRowSource: `{ledger['selectedFirstRowSource']}`",
        f"- activeDirectV21Contract: `{ledger['activeDirectV21Contract']}`",
        f"- segment0TaylorModelGateProofStatus: `{ledger['segment0TaylorModelGateProofStatus']}`",
        f"- segment0TaylorModelGateGap: `{ledger['segment0TaylorModelGateGap']}`",
        f"- segment0TaylorModelTargetPayloadPresent: `{ledger['segment0TaylorModelTargetPayloadPresent']}`",
        f"- targetLeanFileExists: `{ledger['targetLeanFileExists']}`",
        f"- segment0PayloadFileExists: `{ledger['segment0PayloadFileExists']}`",
        f"- segment0PayloadPresent: `{ledger['segment0PayloadPresent']}`",
        f"- parentSegment0OnlySurfacePresent: `{ledger['parentSegment0OnlySurfacePresent']}`",
        f"- rawD17SharpSupportPresent: `{ledger['rawD17SharpSupportPresent']}`",
        f"- targetPayloadPresent: `{ledger['targetPayloadPresent']}`",
        f"- shouldEmitLeanPayload: `{ledger['shouldEmitLeanPayload']}`",
        f"- pointRowsPresentButInsufficient: `{ledger['pointRowsPresentButInsufficient']}`",
        f"- pointRatAuditProofStatus: `{ledger['pointRatAuditProofStatus']}`",
        f"- rawD17FactorRouteBudgetKilled: `{ledger['rawD17FactorRouteBudgetKilled']}`",
        "",
        "## Target Lean Surface",
        "",
        f"- file: `{ledger['targetLeanFile']}`",
        "",
    ]
    for symbol, info in ledger["targetSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", "## Segment0 Payload Surface", ""])
    lines.append(f"- file: `{ledger['segment0PayloadFile']}`")
    lines.append("")
    for symbol, info in ledger["segment0Symbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", "## Parent Segment0-Only Obstruction", ""])
    for symbol, info in ledger["parentSegment0OnlySurfaceSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", "## Raw-D17 Sharp Support-Only Kill", ""])
    lines.append(ledger["rawD17SharpSupportMeaning"])
    lines.append("")
    for symbol, info in ledger["rawD17SharpSupportSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", "## Required Rows Before Lean", ""])
    for row in ledger["requiredRowsBeforeLean"]:
        lines.extend(
            [
                f"### {row['id']}",
                "",
                f"- object: {row['object']}",
                f"- status: `{row['status']}`",
                f"- failureCode: `{row['failureCode']}`",
                "",
            ]
        )
    lines.extend(
        [
            "## Browser Follow-Up",
            "",
            f"- status: `{ledger['computerUseFollowUpReview']['latestStatus']}`",
            f"- choice: `{ledger['computerUseFollowUpReview']['recommendedChoice']}`",
            f"- firstFile: `{ledger['computerUseFollowUpReview']['firstFile']}`",
            f"- targetLeanFile: `{ledger['computerUseFollowUpReview']['targetLeanFile']}`",
            f"- firstTheoremOrObject: `{ledger['computerUseFollowUpReview']['firstTheoremOrObject']}`",
            f"- firstSegmentTheorem: `{ledger['computerUseFollowUpReview']['firstSegmentTheorem']}`",
            f"- whyProofGrade: {ledger['computerUseFollowUpReview']['whyProofGrade']}",
            "",
            "Latest segment0 Taylor-model source review:",
            "",
            f"- nextPatch: {ledger['computerUseSegment0TaylorReview']['nextPatch']}",
            f"- firstScript: `{ledger['computerUseSegment0TaylorReview']['firstScript']}`",
            f"- firstGeneratedArtifact: `{ledger['computerUseSegment0TaylorReview']['firstGeneratedArtifact']}`",
            f"- targetLeanFile: `{ledger['computerUseSegment0TaylorReview']['targetLeanFile']}`",
            f"- modelRemainderTheorem: `{ledger['computerUseSegment0TaylorReview']['modelRemainderTheorem']}`",
            f"- failureCode: `{ledger['computerUseSegment0TaylorReview']['failureCode']}`",
            f"- stopRule: {ledger['computerUseSegment0TaylorReview']['stopRule']}",
            "",
            "Source rows needed:",
            "",
        ]
    )
    for row in ledger["computerUseFollowUpReview"]["sourceRowsNeeded"]:
        lines.append(f"- {row}")
    lines.extend(["", "Do not use:", ""])
    for row in ledger["computerUseFollowUpReview"]["doNotUse"]:
        lines.append(f"- {row}")
    lines.append("")
    lines.extend(["## Support Surfaces", ""])
    for path, info in ledger["supportSurfaces"].items():
        lines.extend(
            [
                f"### `{path}`",
                "",
                f"- exists: `{info['exists']}`",
                f"- allSymbolsPresent: `{info['allSymbolsPresent']}`",
                f"- sha256: `{info['sha256']}`",
                "",
            ]
        )
        for symbol, symbol_info in info["symbols"].items():
            lines.append(
                f"- `{symbol}`: present=`{symbol_info['present']}`, "
                f"line=`{symbol_info['line']}`"
            )
        lines.append("")
    lines.extend(
        [
            "## Boundary",
            "",
            f"- {ledger['pointRowsReason']}",
            f"- {ledger['rawD17FactorRouteReason']}",
        ]
    )
    for item in ledger["doNotUse"]:
        lines.append(f"- Do not use {item}.")
    lines.extend(
        [
            "",
            "## Next Implementable Patch",
            "",
            ledger["nextImplementablePatch"],
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    ledger = build_ledger()
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(ledger["proofStatus"])
    print(ledger["currentGap"])
    print(ledger["firstFailureCode"])
    print(f"wrote {rel(JSON_OUT)}")
    print(f"wrote {rel(MD_OUT)}")


if __name__ == "__main__":
    main()
