#!/usr/bin/env python3
"""Fail-closed ledger for the collapsed degree-0 signed source route.

The checked Lean surface accepts a future lower/upper interval certificate for

    ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)

and routes it into the direct collapsed degree-0 receiver.  This script records
that exact contract.  It does not emit interval rows, does not write a concrete
Lean payload, and does not claim Step33A.1-A closure.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_collapsed_degree0_signed_source.v11"
ROUTE = "collapsed_degree0_signed_poly_deriv_source"
PROOF_STATUS = "fail_closed_missing_raw_d17_local_interval_rows"
CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_LOCAL_INTERVAL_ROWS_GAP"
)
DIRECT_ROW_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "DIRECT_ROW_SOURCE_GAP"
)
COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POLY_DERIV_SIGNED_SOURCE_GAP"
)
COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "BUDGET_CONSTANT_FAIL"
)
RAW_D17_SIGNED_FACTOR_ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_ROWS_GAP"
)
RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_CONSTANT_FAIL"
)
RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_ROWS_GAP"
)
RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_CONSTANT_FAIL"
)
BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "BUDGET_CONSTANT_FAIL"
)
COARSE_TRIANGLE_AUDIT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "COARSE_TRIANGLE_BUDGET_AUDIT_GAP"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

SIGNED_SOURCE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload.lean"
)
CENTER_AUDIT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0CenterAudit.lean"
)
BUDGET_AUDIT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourceBudgetAudit.lean"
)
NOMINAL_POLY_DERIV_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows.lean"
)
RAW_D17_SIGNED_FACTOR_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean"
)
RAW_D17_SIGNED_FACTOR_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorPayload.lean"
)
DIRECT_PAYLOAD_LEDGER = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json"
)
RAW_D17_SIGNED_FACTOR_PAYLOAD_LEDGER = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_payload.json"
)
DIRECT_SIGNED_SOURCE_ROWS_GATE_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_direct_signed_source_rows.json"
)
JSON_OUT = REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_signed_source.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_signed_source.md"

DIRECT_SEGMENTED_SIGNED_SOURCE_ROWS_SCRIPT = (
    "scripts/generate_step33_a1_sub0_collapsed_degree0_signed_source.py"
)
DIRECT_SEGMENTED_SIGNED_SOURCE_ROWS_LEAN_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0DirectSignedSourcePayload.lean"
)
DIRECT_SIGNED_SOURCE_GATE_SCRIPT = (
    "scripts/generate_step33_a1_sub0_collapsed_degree0_"
    "direct_signed_source_rows.py"
)
PROSHKA_FIRST_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "collapsedDegree0_signedSource_segment0_interval_generated"
)

SIGNED_SOURCE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr",
    "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceTarget",
    "Step33Sub0CollapsedDegree0SignedSourceCert",
    "structure Valid",
    "sourceInterval",
    "derivAbsBudget",
    "degree0Budget",
    "theorem valid_of_signed_interval_and_budget",
    "theorem to_hSignedD17PolyDeriv",
    "theorem to_collapsed_degree0_remainder",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_hSignedD17PolyDeriv_of_signed_interval"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_degree0_remainder_of_signed_interval_and_budget"
    ),
    "Step33Sub0CollapsedDegree0SignedSourceSegmentCert",
    "Step33Sub0CollapsedDegree0RawPolySegmentCert where",
    "def toSignedSegmentCert",
    "namespace Step33Sub0CollapsedDegree0RawPolySegmentCert",
    "theorem valid_of_raw_poly_intervals",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_signedSegmentValid_of_raw_poly_intervals"
    ),
    "Step33Sub0CollapsedDegree0SignedSourceSegmentCover",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_degree0_remainder_of_signed_segment_cover_and_budget"
    ),
    "Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert",
    "Step33Sub0CollapsedDegree0RawPolySegmentCover",
    "Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert",
    "theorem to_signedSegmentFamilyValid",
    "theorem to_collapsed_degree0_remainder",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_degree0_remainder_of_raw_poly_segment_family_cert"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_degree0_remainder_of_signed_segment_family_cert"
    ),
    "primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_source_cert",
]

CENTER_AUDIT_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0",
    "primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs",
    "primaryFiniteRow0Parent0Split100Sub0_directCollapsed_degree0_hCenter_generated",
    (
        "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
        "collapsed_degree0_remainder_of_center_and_polyDeriv_source"
    ),
]

NOMINAL_POLY_DERIV_ROWS_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff",
    "primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "nominalOrder16Poly_deriv_eq_poly"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "nominalOrder16Poly_deriv_abs_le"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0"
        "NominalOrder16PolyDerivSegmentCount"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "nominalOrder16Poly_deriv_segment_cover"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "nominalOrder16Poly_deriv_segment_interval_generated"
    ),
]

BUDGET_AUDIT_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0TriangleDerivAbsRat",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_triangle_budget_fail_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_triangle_budget_not_spendable"
    ),
]

RAW_D17_SIGNED_FACTOR_ROWS_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawProductActual_order18_eq_signedLeibniz"
    ),
    "Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert",
    "def termCornerRows",
    "def toRawPolySegmentCert",
    "structure Valid",
    "factorRows",
    "termCorners",
    "rawAssembly",
    "theorem to_termRows",
    "theorem to_rawInterval",
    "theorem to_rawPolySegmentValid",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_rawD17_interval_of_signed_factor_segment"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment"
    ),
]

RAW_D17_SIGNED_FACTOR_PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_segment0_valid"
    ),
    "primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawPolySegment0",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_rawPoly_segment0_valid"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_segment0_budget_fail_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_segment0_budget_not_spendable"
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
        raise ValueError(f"{path}: expected object root")
    return data


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def symbol_lines(path: Path, symbols: list[str]) -> dict[str, dict[str, Any]]:
    text = read_text(path)
    lines = text.splitlines()
    out: dict[str, dict[str, Any]] = {}
    for symbol in symbols:
        found = False
        line_no = None
        for idx, line in enumerate(lines, start=1):
            if symbol in line:
                found = True
                line_no = idx
                break
        out[symbol] = {"present": found, "line": line_no}
    return out


def all_present(lines: dict[str, dict[str, Any]]) -> bool:
    return all(entry["present"] for entry in lines.values())


def v21_direct_contract_active(direct_payload: dict[str, Any]) -> bool:
    contract = direct_payload.get("preferredCollapsedLowDegreeRowSourceContract")
    if not isinstance(contract, dict):
        return False
    return (
        direct_payload.get("schema")
        == "q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.v21"
        and contract.get("firstFailureCodeIfRowsMissing")
        == COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP
        and contract.get("parentFailureCodeIfRowsMissing") == DIRECT_ROW_SOURCE_GAP
    )


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Collapsed Degree-0 Signed Source Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Verdict",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- leanPayloadWritten: `{ledger['leanPayloadWritten']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- firstFailureCode: `{ledger['firstFailureCode']}`",
        f"- activeDirectV21Contract: `{ledger['activeDirectV21Contract']}`",
        f"- signedSourceSurfacePresent: `{ledger['signedSourceSurfacePresent']}`",
        f"- signedSourceSurfaceLeanChecked: `{ledger['signedSourceSurfaceLeanChecked']}`",
        f"- centerAuditLeanChecked: `{ledger['centerAuditLeanChecked']}`",
        f"- nominalPolyDerivRowsLeanChecked: `{ledger['nominalPolyDerivRowsLeanChecked']}`",
        f"- rawD17SignedFactorRowsLeanChecked: `{ledger['rawD17SignedFactorRowsLeanChecked']}`",
        f"- rawD17SignedFactorPayloadLeanChecked: `{ledger['rawD17SignedFactorPayloadLeanChecked']}`",
        f"- rawD17SignedFactorSegment0Valid: `{ledger['rawD17SignedFactorSegment0Valid']}`",
        f"- rawD17SignedFactorRawPolySegment0Valid: `{ledger['rawD17SignedFactorRawPolySegment0Valid']}`",
        f"- rawD17SignedFactorSegment0BudgetSpendable: `{ledger['rawD17SignedFactorSegment0BudgetSpendable']}`",
        f"- rawD17FactorRouteActiveNextPatch: `{ledger['rawD17FactorRouteActiveNextPatch']}`",
        f"- rawD17FactorRouteStatus: `{ledger['rawD17FactorRouteStatus']}`",
        f"- coarseTriangleBudgetAuditLeanChecked: `{ledger['coarseTriangleBudgetAuditLeanChecked']}`",
        f"- coarseTriangleBudgetPassed: `{ledger['coarseTriangleBudgetPassed']}`",
        f"- selectedNextPatch: `{ledger['selectedNextPatch']}`",
        f"- firstConcreteSubgap: `{ledger['firstConcreteSubgap']}`",
        "",
        "## Next Patch",
        "",
        f"- script: `{ledger['nextPatchScript']}`",
        f"- leanFile: `{ledger['nextPatchLeanFile']}`",
        f"- segments: `{ledger['nextPatchSegments']}`",
        f"- rowsFailureCode: `{ledger['nextFailureCodeIfRowsMissing']}`",
        f"- budgetFailureCode: `{ledger['nextFailureCodeIfBudgetFalse']}`",
        f"- directRowsGateProofStatus: "
        f"`{ledger['directSignedSourceRowsGateProofStatus']}`",
        f"- directRowsGateFirstFailureCode: "
        f"`{ledger['directSignedSourceRowsGateFirstFailureCode']}`",
        f"- directRowsGateFollowUpStatus: "
        f"`{ledger['directSignedSourceRowsGateFollowUpStatus']}`",
        f"- directRowsGateFollowUpChoice: "
        f"`{ledger['directSignedSourceRowsGateFollowUpChoice']}`",
        f"- computerUseChoice: "
        f"`{ledger['computerUseRouteReview']['recommendedOption']}`",
        f"- computerUseFirstTheorem: "
        f"`{ledger['computerUseRouteReview']['firstTheorem']}`",
        "",
        "First required theorem names:",
            "",
    ]
    for theorem in ledger["nextPatchTheorems"]:
        lines.append(f"- `{theorem}`")
    lines.extend(
        [
            "",
            "## Direct v21 Handoff",
            "",
            f"- sourceLedger: `{ledger['directV21ContractSource']}`",
            f"- active: `{ledger['activeDirectV21Contract']}`",
            f"- firstFailureCodeIfRowsMissing: "
            f"`{ledger['directV21Contract'].get('firstFailureCodeIfRowsMissing')}`",
            f"- parentFailureCodeIfRowsMissing: "
            f"`{ledger['directV21Contract'].get('parentFailureCodeIfRowsMissing')}`",
            f"- budgetFailureCode: "
            f"`{ledger['directV21Contract'].get('budgetFailureCode')}`",
            "",
            "Required direct rows before any concrete Lean payload:",
            "",
        ]
    )
    for row in ledger["directV21RequiredRows"]:
        lines.extend(
            [
                f"- `{row.get('id')}`: {row.get('object')}",
                f"  status=`{row.get('status')}`, "
                f"failureCode=`{row.get('failureCode')}`",
            ]
        )
    lines.extend(
        [
            "",
        "## Target",
        "",
        "- expression:",
        "",
        "```text",
        "ActiveScaleCoeff * iteratedDeriv 17 ComponentProductActual eta",
        "  - deriv NominalOrder16Poly eta",
        "```",
        "",
        "- interval theorem expected from a future generated payload:",
        "",
        "```text",
        "forall eta in Set.Icc 0 (1/10),",
        "  lower <= signedExpr eta and signedExpr eta <= upper",
        "```",
        "",
        "## Generator Contract",
        "",
        "The next proof-producing patch must emit proof-grade segment-local",
        "rows.  It may either emit direct lower/upper rows for the already",
        "subtracted whole expression or use the checked same-segment raw/poly",
        "interval subtraction bridge.  A separate direct-norm receiver is not",
        "the selected route because the checked `Valid.to_hSignedD17PolyDeriv`",
        "and segment-family bridges already convert lower/upper rows to the",
        "required norm bound.",
        "",
        f"- interval theorem: `{ledger['expectedGeneratedTheorem']}`",
        f"- segmented theorem: `{ledger['expectedSegmentGeneratedTheorem']}`",
        f"- raw/poly subtraction bridge: `{ledger['expectedRawPolySubtractionBridgeTheorem']}`",
        f"- raw/poly family bridge: `{ledger['expectedRawPolyFamilyBridgeTheorem']}`",
        f"- raw-D17 signed-factor bridge: `{ledger['expectedRawD17SignedFactorBridgeTheorem']}`",
        f"- raw/poly signed-factor bridge: `{ledger['expectedRawPolySignedFactorBridgeTheorem']}`",
        f"- abs theorem bridge: `{ledger['expectedAbsTheorem']}`",
        f"- segmented abs bridge: `{ledger['expectedSegmentAbsTheorem']}`",
        f"- budget theorem: `{ledger['expectedBudgetTheorem']}`",
        f"- final bridge: `{ledger['expectedFinalBridgeTheorem']}`",
        f"- segmented final bridge: `{ledger['expectedSegmentFinalBridgeTheorem']}`",
        "",
        "Required generated constants:",
        "",
    ]
    )
    for item in ledger["expectedGeneratedConstants"]:
        lines.append(f"- `{item}`")
    lines.extend(
        [
            "",
        "## Required Rows",
        "",
        ]
    )
    for row in ledger["requiredRows"]:
        lines.extend(
            [
                f"### {row['id']}",
                "",
                f"- object: `{row['object']}`",
                f"- status: `{row['status']}`",
                f"- failureCode: `{row['failureCode']}`",
                "",
            ]
        )
    lines.extend(
        [
            "## Guard",
            "",
        ]
    )
    for item in ledger["doNotSpend"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Raw-D17 Signed-Factor Smoke Payload",
            "",
            f"- file: `{ledger['rawD17SignedFactorPayloadFile']}`",
            f"- payloadLedger: `{ledger['rawD17SignedFactorPayloadLedgerFile']}`",
            f"- segment0Valid: `{ledger['rawD17SignedFactorSegment0Valid']}`",
            f"- rawPolySegment0Valid: `{ledger['rawD17SignedFactorRawPolySegment0Valid']}`",
            f"- segment0BudgetSpendable: `{ledger['rawD17SignedFactorSegment0BudgetSpendable']}`",
            f"- activeNextPatch: `{ledger['rawD17FactorRouteActiveNextPatch']}`",
            f"- routeStatus: `{ledger['rawD17FactorRouteStatus']}`",
            f"- segment0BudgetFailureCode: `{ledger['rawD17SignedFactorSegment0BudgetFailureCode']}`",
            f"- segment0BudgetFailureTheorem: `{ledger['rawD17SignedFactorSegment0BudgetFailureTheorem']}`",
            "",
            "The smoke payload validates the receiver and raw/poly bridge for one",
            "full-cell segment, but its exact budget theorem proves this coarse",
            "segment is not spendable.  Under the active v21 direct contract this",
            "payload is retained only as support evidence; it is not the selected",
            "next patch and must not resurrect the factorwise route as closure.",
            "",
            "## Coarse Triangle Budget Audit",
            "",
            f"- file: `{ledger['coarseTriangleBudgetAuditFile']}`",
            f"- candidateClass: `{ledger['coarseTriangleCandidateClass']}`",
            f"- budgetPassed: `{ledger['coarseTriangleBudgetPassed']}`",
            f"- auditFailureIfMissing: `{ledger['coarseTriangleAuditFailureCode']}`",
            f"- liveGapAfterAudit: `{ledger['currentGap']}`",
            "",
        "This audit kills only the independent absolute/triangle estimate.",
        "It does not prove that the true signed whole-expression row fails.",
        "",
        "## Computer Use Route Review",
        "",
        f"- used: `{ledger['computerUseRouteReview']['used']}`",
        f"- latestRequest: `{ledger['computerUseRouteReview']['latestRequest']}`",
        f"- latestStatus: `{ledger['computerUseRouteReview']['latestStatus']}`",
        f"- recommendedOption: `{ledger['computerUseRouteReview']['recommendedOption']}`",
        f"- localDecision: `{ledger['computerUseRouteReview']['localDecision']}`",
        f"- decision: {ledger['computerUseRouteReview']['decision']}",
        "",
    ]
    )
    for symbol, info in ledger["coarseTriangleBudgetAuditSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(
        [
            "",
            "## Symbol Audit",
            "",
            f"### {ledger['signedSourceFile']}",
            "",
        ]
    )
    for symbol, info in ledger["signedSourceSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", f"### {ledger['centerAuditFile']}", ""])
    for symbol, info in ledger["centerAuditSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", f"### {ledger['nominalPolyDerivRowsFile']}", ""])
    for symbol, info in ledger["nominalPolyDerivRowsSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", f"### {ledger['rawD17SignedFactorRowsFile']}", ""])
    for symbol, info in ledger["rawD17SignedFactorRowsSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", f"### {ledger['rawD17SignedFactorPayloadFile']}", ""])
    for symbol, info in ledger["rawD17SignedFactorPayloadSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "This ledger is not a proof-grade source row certificate.  It records",
            "the exact Lean surface and keeps the node fail-closed until the",
            "lower/upper interval theorem and exact rational budget rows exist.",
            "",
        ]
    )
    return "\n".join(lines)


def build_ledger() -> dict[str, Any]:
    signed_symbols = symbol_lines(SIGNED_SOURCE_FILE, SIGNED_SOURCE_SYMBOLS)
    center_symbols = symbol_lines(CENTER_AUDIT_FILE, CENTER_AUDIT_SYMBOLS)
    nominal_poly_deriv_rows_symbols = symbol_lines(
        NOMINAL_POLY_DERIV_ROWS_FILE, NOMINAL_POLY_DERIV_ROWS_SYMBOLS
    )
    budget_audit_symbols = symbol_lines(BUDGET_AUDIT_FILE, BUDGET_AUDIT_SYMBOLS)
    raw_d17_signed_factor_rows_symbols = symbol_lines(
        RAW_D17_SIGNED_FACTOR_ROWS_FILE, RAW_D17_SIGNED_FACTOR_ROWS_SYMBOLS
    )
    raw_d17_signed_factor_payload_symbols = symbol_lines(
        RAW_D17_SIGNED_FACTOR_PAYLOAD_FILE, RAW_D17_SIGNED_FACTOR_PAYLOAD_SYMBOLS
    )
    direct_payload = load_json(DIRECT_PAYLOAD_LEDGER)
    raw_d17_signed_factor_payload = load_json(RAW_D17_SIGNED_FACTOR_PAYLOAD_LEDGER)
    direct_signed_source_rows_gate = load_json(DIRECT_SIGNED_SOURCE_ROWS_GATE_LEDGER)
    direct_contract = direct_payload.get("preferredCollapsedLowDegreeRowSourceContract")
    if not isinstance(direct_contract, dict):
        direct_contract = {}
    direct_v21_active = v21_direct_contract_active(direct_payload)
    direct_v21_required_rows = direct_contract.get(
        "requiredExactRowsBeforeLeanEmission",
        [],
    )

    signed_present = all_present(signed_symbols)
    center_present = all_present(center_symbols)
    nominal_poly_deriv_rows_present = all_present(nominal_poly_deriv_rows_symbols)
    budget_audit_present = all_present(budget_audit_symbols)
    raw_d17_signed_factor_rows_present = all_present(
        raw_d17_signed_factor_rows_symbols
    )
    raw_d17_signed_factor_payload_present = all_present(
        raw_d17_signed_factor_payload_symbols
    )
    raw_d17_signed_factor_segment0_valid = raw_d17_signed_factor_payload_symbols[
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_valid"
        )
    ]["present"]
    raw_d17_signed_factor_raw_poly_segment0_valid = (
        raw_d17_signed_factor_payload_symbols[
            (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "rawD17_signedFactor_rawPoly_segment0_valid"
            )
        ]["present"]
    )
    raw_d17_signed_factor_segment0_budget_not_spendable = (
        raw_d17_signed_factor_payload_symbols[
            (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "rawD17_signedFactor_segment0_budget_not_spendable"
            )
        ]["present"]
    )
    raw_d17_signed_factor_segment0_budget_spendable = (
        False if raw_d17_signed_factor_segment0_budget_not_spendable else None
    )
    current_gap = (
        COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP
        if direct_v21_active
        else RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_FAIL
        if raw_d17_signed_factor_segment0_budget_not_spendable
        else CURRENT_GAP
    )
    first_failure_code = (
        COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP
        if direct_v21_active
        else RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_FAIL
        if raw_d17_signed_factor_segment0_budget_not_spendable
        else RAW_D17_SIGNED_FACTOR_ROWS_GAP
    )
    proof_status = (
        "fail_closed_missing_v21_direct_signed_source_segment_rows"
        if direct_v21_active
        else "fail_closed_raw_d17_signed_factor_segment0_budget_not_spendable"
        if raw_d17_signed_factor_segment0_budget_not_spendable
        else PROOF_STATUS
    )
    selected_next_patch = (
        "emit_first_direct_signed_source_segment0_interval"
        if direct_v21_active
        else "build_two_segment_raw_d17_signed_factor_payload"
        if raw_d17_signed_factor_segment0_budget_not_spendable
        else "build_raw_d17_signed_factor_interval_rows_for_collapsed_degree0_raw_poly_family"
    )
    raw_d17_factor_route_active_next_patch = (
        raw_d17_signed_factor_segment0_budget_not_spendable and not direct_v21_active
    )
    next_patch_script = (
        DIRECT_SEGMENTED_SIGNED_SOURCE_ROWS_SCRIPT
        if direct_v21_active
        else (
            "scripts/generate_step33_a1_sub0_collapsed_degree0_"
            "raw_d17_signed_factor_segments.py"
        )
    )
    next_patch_lean_file = (
        DIRECT_SEGMENTED_SIGNED_SOURCE_ROWS_LEAN_FILE
        if direct_v21_active
        else (
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
            "CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean"
        )
    )
    next_patch_segments = (
        ["generated proof-grade cover of Set.Icc 0 (1/10)"]
        if direct_v21_active
        else ["[0, 1/20]", "[1/20, 1/10]"]
    )
    next_patch_theorems = (
        [
            PROSHKA_FIRST_THEOREM,
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
        if direct_v21_active
        else [
            (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "rawD17_signedFactor_left_valid"
            ),
            (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "rawD17_signedFactor_right_valid"
            ),
            (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "rawD17_signedFactor_twoSegment_family_valid"
            ),
        ]
    )
    next_failure_code_if_rows_missing = (
        COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP
        if direct_v21_active
        else RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_ROWS_GAP
    )
    next_failure_code_if_budget_false = (
        COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL
        if direct_v21_active
        else RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_FAIL
    )

    ledger: dict[str, Any] = {
        "schema": SCHEMA,
        "route": ROUTE,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "proofStatus": proof_status,
        "proofGrade": False,
        "leanPayloadWritten": raw_d17_signed_factor_payload_present,
        "currentGap": current_gap,
        "firstFailureCode": first_failure_code,
        "firstConcreteSubgap": first_failure_code,
        "budgetFailureCode": BUDGET_FAIL,
        "selectedNextPatch": selected_next_patch,
        "activeDirectV21Contract": direct_v21_active,
        "directV21ContractSource": rel(DIRECT_PAYLOAD_LEDGER),
        "directV21Contract": direct_contract,
        "directV21RequiredRows": direct_v21_required_rows,
        "directSignedSourceRowsGateLedgerFile": rel(
            DIRECT_SIGNED_SOURCE_ROWS_GATE_LEDGER
        ),
        "directSignedSourceRowsGateProofStatus": (
            direct_signed_source_rows_gate.get("proofStatus")
        ),
        "directSignedSourceRowsGateCurrentGap": (
            direct_signed_source_rows_gate.get("currentGap")
        ),
        "directSignedSourceRowsGateFirstFailureCode": (
            direct_signed_source_rows_gate.get("firstFailureCode")
        ),
        "directSignedSourceRowsGateTargetPayloadPresent": (
            direct_signed_source_rows_gate.get("targetPayloadPresent")
        ),
        "directSignedSourceRowsGateFollowUpStatus": (
            direct_signed_source_rows_gate.get("computerUseFollowUpReview", {})
            .get("latestStatus")
        ),
        "directSignedSourceRowsGateFollowUpChoice": (
            direct_signed_source_rows_gate.get("computerUseFollowUpReview", {})
            .get("recommendedChoice")
        ),
        "rawD17FactorRouteActiveNextPatch": raw_d17_factor_route_active_next_patch,
        "rawD17FactorRouteStatus": (
            "superseded_by_v21_direct_whole_expression_row_source"
            if direct_v21_active
            else "active_legacy_candidate"
        ),
        "signedSourceFile": rel(SIGNED_SOURCE_FILE),
        "signedSourceFileSha256": sha256_file(SIGNED_SOURCE_FILE),
        "signedSourceSymbols": signed_symbols,
        "signedSourceSurfacePresent": signed_present,
        "signedSourceSurfaceLeanChecked": signed_present,
        "centerAuditFile": rel(CENTER_AUDIT_FILE),
        "centerAuditFileSha256": sha256_file(CENTER_AUDIT_FILE),
        "centerAuditSymbols": center_symbols,
        "centerAuditPresent": center_present,
        "centerAuditLeanChecked": center_present,
        "nominalPolyDerivRowsFile": rel(NOMINAL_POLY_DERIV_ROWS_FILE),
        "nominalPolyDerivRowsFileSha256": sha256_file(
            NOMINAL_POLY_DERIV_ROWS_FILE
        ),
        "nominalPolyDerivRowsSymbols": nominal_poly_deriv_rows_symbols,
        "nominalPolyDerivRowsPresent": nominal_poly_deriv_rows_present,
        "nominalPolyDerivRowsLeanChecked": nominal_poly_deriv_rows_present,
        "coarseTriangleBudgetAuditFile": rel(BUDGET_AUDIT_FILE),
        "coarseTriangleBudgetAuditFileSha256": sha256_file(BUDGET_AUDIT_FILE),
        "coarseTriangleBudgetAuditSymbols": budget_audit_symbols,
        "coarseTriangleBudgetAuditPresent": budget_audit_present,
        "coarseTriangleBudgetAuditLeanChecked": budget_audit_present,
        "coarseTriangleAuditFailureCode": COARSE_TRIANGLE_AUDIT_GAP,
        "coarseTriangleCandidateClass": "independent_abs_triangle",
        "coarseTriangleBudgetPassed": False,
        "coarseTriangleBudgetKillTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_triangle_budget_fail_rat"
        ),
        "signedWholeExpressionRowsPresent": False,
        "rawD17SignedFactorRowsFile": rel(RAW_D17_SIGNED_FACTOR_ROWS_FILE),
        "rawD17SignedFactorRowsFileSha256": sha256_file(
            RAW_D17_SIGNED_FACTOR_ROWS_FILE
        ),
        "rawD17SignedFactorRowsSymbols": raw_d17_signed_factor_rows_symbols,
        "rawD17SignedFactorRowsPresent": raw_d17_signed_factor_rows_present,
        "rawD17SignedFactorRowsLeanChecked": raw_d17_signed_factor_rows_present,
        "rawD17SignedFactorPayloadFile": rel(RAW_D17_SIGNED_FACTOR_PAYLOAD_FILE),
        "rawD17SignedFactorPayloadFileSha256": sha256_file(
            RAW_D17_SIGNED_FACTOR_PAYLOAD_FILE
        ),
        "rawD17SignedFactorPayloadLedgerFile": rel(
            RAW_D17_SIGNED_FACTOR_PAYLOAD_LEDGER
        ),
        "rawD17SignedFactorPayloadLedgerCurrentGap": (
            raw_d17_signed_factor_payload.get("currentGap")
        ),
        "rawD17SignedFactorPayloadSymbols": raw_d17_signed_factor_payload_symbols,
        "rawD17SignedFactorPayloadPresent": raw_d17_signed_factor_payload_present,
        "rawD17SignedFactorPayloadLeanChecked": (
            raw_d17_signed_factor_payload_present
        ),
        "rawD17SignedFactorSegment0Valid": raw_d17_signed_factor_segment0_valid,
        "rawD17SignedFactorRawPolySegment0Valid": (
            raw_d17_signed_factor_raw_poly_segment0_valid
        ),
        "rawD17SignedFactorSegment0BudgetSpendable": (
            raw_d17_signed_factor_segment0_budget_spendable
        ),
        "rawD17SignedFactorSegment0BudgetFailureCode": (
            RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_FAIL
        ),
        "rawD17SignedFactorSegment0BudgetFailureTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_budget_not_spendable"
        ),
        "nextPatchScript": next_patch_script,
        "nextPatchLeanFile": next_patch_lean_file,
        "nextPatchSegments": next_patch_segments,
        "nextPatchTheorems": next_patch_theorems,
        "nextFailureCodeIfRowsMissing": next_failure_code_if_rows_missing,
        "nextFailureCodeIfBudgetFalse": next_failure_code_if_budget_false,
        "directPayloadCurrentGap": direct_payload.get("currentGap"),
        "directPayloadProofGrade": direct_payload.get("proofGrade"),
        "targetExpression": (
            "ActiveScaleCoeff * iteratedDeriv 17 ComponentProductActual "
            "- deriv NominalOrder16Poly"
        ),
        "expectedGeneratedTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_polyDeriv_signed_interval_generated"
        ),
        "expectedSegmentGeneratedTheorem": (
            PROSHKA_FIRST_THEOREM
        ),
        "expectedRawPolySubtractionBridgeTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_signedSegmentValid_of_raw_poly_intervals"
        ),
        "expectedRawPolyFamilyBridgeTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsed_degree0_remainder_of_raw_poly_segment_family_cert"
        ),
        "expectedRawD17SignedFactorBridgeTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_rawD17_interval_of_signed_factor_segment"
        ),
        "expectedRawPolySignedFactorBridgeTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment"
        ),
        "expectedGeneratedConstants": [
            (
                "primaryFiniteRow0Parent0Split100Sub0"
                "CollapsedDegree0DerivLower"
            ),
            (
                "primaryFiniteRow0Parent0Split100Sub0"
                "CollapsedDegree0DerivUpper"
            ),
            (
                "primaryFiniteRow0Parent0Split100Sub0"
                "CollapsedDegree0DerivAbs"
            ),
            (
                "primaryFiniteRow0Parent0Split100Sub0"
                "DirectCollapsedDegree0PolyErrorAbs"
            ),
        ],
        "expectedAbsTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_hSignedD17PolyDeriv_generated"
        ),
        "expectedSegmentAbsTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover"
        ),
        "expectedBudgetTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_budget_pass_rat"
        ),
        "expectedFinalBridgeTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsed_degree0_remainder_of_signed_interval_and_budget"
        ),
        "expectedSegmentFinalBridgeTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsed_degree0_remainder_of_signed_segment_family_cert"
        ),
        "signedIntervalBridgeTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_hSignedD17PolyDeriv_of_signed_interval"
        ),
        "signedSegmentBridgeTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover"
        ),
        "requiredRows": [
            {
                "id": "A0_raw_d17_signed_factor_rows",
                "object": (
                    "segment-local signed factor interval rows for "
                    "OmegaActual and ShapeSqActual derivatives through order 18"
                ),
                "status": (
                    "checked_full_cell_smoke_payload_not_budget_spendable"
                    if raw_d17_signed_factor_segment0_budget_not_spendable
                    else
                    "checked_receiver_present_missing_concrete_rows"
                    if raw_d17_signed_factor_rows_present
                    else "missing_receiver"
                ),
                "failureCode": first_failure_code,
            },
            {
                "id": "A0b_raw_d17_term_corner_rows",
                "object": (
                    "exact corner rows for choose(18,k) * "
                    "D^(18-k)OmegaActual * D^kShapeSqActual"
                ),
                "status": (
                    "checked_for_full_cell_smoke_only_missing_tighter_local_rows"
                    if raw_d17_signed_factor_segment0_budget_not_spendable
                    else "missing"
                ),
                "failureCode": first_failure_code,
            },
            {
                "id": "A0c_scaled_raw_d17_assembly_rows",
                "object": (
                    "rawLower <= ActiveScaleCoeff * sum termLower and "
                    "ActiveScaleCoeff * sum termUpper <= rawUpper"
                ),
                "status": (
                    "checked_for_full_cell_smoke_only_missing_tighter_local_rows"
                    if raw_d17_signed_factor_segment0_budget_not_spendable
                    else "missing"
                ),
                "failureCode": first_failure_code,
            },
            {
                "id": "A1_poly_segment_interval_rows",
                "object": (
                    "segment-local lower/upper interval theorems for "
                    "deriv(NominalOrder16Poly)"
                ),
                "status": (
                    "checked_proof_grade_full_cell_row"
                    if nominal_poly_deriv_rows_present
                    else "missing"
                ),
                "failureCode": "NONE" if nominal_poly_deriv_rows_present else CURRENT_GAP,
            },
            {
                "id": "A2_signed_subtraction_rows",
                "object": (
                    "exact rational rows lower <= rawLower - polyUpper and "
                    "rawUpper - polyLower <= upper"
                ),
                "status": (
                    "checked_for_full_cell_smoke_only_not_budget_spendable"
                    if raw_d17_signed_factor_raw_poly_segment0_valid
                    else "missing"
                ),
                "failureCode": first_failure_code,
            },
            {
                "id": "A3_segment_cover",
                "object": "exact cover of Set.Icc 0 (1/10) by generated segments",
                "status": (
                    "missing_tighter_local_family"
                    if raw_d17_signed_factor_segment0_budget_not_spendable
                    else "missing"
                ),
                "failureCode": first_failure_code,
            },
            {
                "id": "B_deriv_abs_budget",
                "object": "for every segment, -derivAbs <= lower_i and upper_i <= derivAbs",
                "status": (
                    "failed_for_full_cell_smoke_segment0"
                    if raw_d17_signed_factor_segment0_budget_not_spendable
                    else "missing"
                ),
                "failureCode": first_failure_code,
            },
            {
                "id": "C_degree0_budget",
                "object": "coeffErrorAbs + derivAbs / 20 <= polyErrorAbs",
                "status": (
                    "failed_for_full_cell_smoke_segment0"
                    if raw_d17_signed_factor_segment0_budget_not_spendable
                    else "missing"
                ),
                "failureCode": first_failure_code,
            },
            {
                "id": "D_final_bridge",
                "object": (
                    "apply "
                    "primaryFiniteRow0Parent0Split100Sub0_"
                    "collapsed_degree0_remainder_of_signed_segment_family_cert"
                ),
                "status": "checked_receiver_present" if signed_present else "missing",
                "failureCode": first_failure_code,
            },
        ],
        "doNotSpend": [
            "activeActual-alone D17 norm budget",
            "separate deriv(NominalOrder16Poly) norm budget",
            "raw-D17 factorwise/two-segment rows",
            "RawProduct18 absolute majorant",
            "factor/P45/zero-model killed budgets",
            "sampled rows or center jets as uniform full-cell bounds",
        ],
        "computerUseRouteReview": {
            "used": True,
            "destination": "in-app ChatGPT Pro / Louise browser",
            "latestRequest": "Step33A.1-A direct row-source gate after v21",
            "latestStatus": "answered",
            "recommendedOption": "A",
            "localDecision": "A",
            "exactNextPatchScript": DIRECT_SEGMENTED_SIGNED_SOURCE_ROWS_SCRIPT,
            "gateScript": DIRECT_SIGNED_SOURCE_GATE_SCRIPT,
            "targetLeanFile": DIRECT_SEGMENTED_SIGNED_SOURCE_ROWS_LEAN_FILE,
            "firstTheorem": PROSHKA_FIRST_THEOREM,
            "firstFailureCode": COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP,
            "decision": (
                "Build the first Lean-checkable direct signed-source segment "
                "for the already-subtracted expression.  Keep the raw-D17 "
                "smoke payload as support evidence, but do not use it as the "
                "active next patch after its budget failure."
            ),
            "note": (
                "The next missing proof object is the exact Rat interval row "
                "for segment0 of ActiveScaleCoeff * "
                "D17(ComponentProductActual) - deriv(NominalOrder16Poly) in "
                "the same target normalization.  Then lift segment interval "
                "to SegmentCert.Valid, derivAbs, exact budget, and the "
                "collapsed segment remainder."
            ),
            "doNotUse": [
                "raw-D17 factorwise/two-segment rows",
                "RawProduct18 absolute majorant",
                "activeActual-alone budget",
                "P45/zero-model budgets",
                "sampled or float intervals",
                "center jets as uniform bounds",
                "new alias/receiver wrappers before source rows exist",
            ],
        },
    }
    return ledger


def main() -> None:
    ledger = build_ledger()
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(ledger["proofStatus"])
    print(ledger["currentGap"])
    print(f"wrote {rel(JSON_OUT)}")
    print(f"wrote {rel(MD_OUT)}")


if __name__ == "__main__":
    main()
