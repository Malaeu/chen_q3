#!/usr/bin/env python3
"""Fail-closed combined cancellation interval certificate ledger.

This script records the exact proof-grade interface for the current
Step33A.1-A sub0 gate:

    P45 residualTaylor polynomial + ScaledCancellationRhs

on [0, 1/10].  It deliberately does not emit Lean or mark the node closed
until a proof-grade interval/rational certificate is available.  Sampled
diagnostic intervals may be copied into the ledger, but they remain diagnostic.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

DEFAULT_SEGMENTED_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_segmented_residual_deriv_interval_payload.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_combined_cancellation_interval_certificate.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_combined_cancellation_interval_certificate.md"
)

COMBINED_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval.lean"
)
CERT_CHECKER_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalCert.lean"
)
BOUND_INPUTS_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean"
)
NORM_RECEIVER_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean"
)
P45_BRIDGE_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationP45Bridge.lean"
)
LANDING_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean"

SCHEMA = "q3_psdpd_step33_a1_sub0_combined_cancellation_interval_certificate.v1"
ROUTE_ID = "STEP33_A1_SUB0_COMBINED_CANCELLATION_INTERVAL"
STATUS = "fail_closed_missing_proof_grade_combined_interval_certificate"
FIRST_FAILURE = "STEP33_A1_SUB0_COMBINED_CANCELLATION_INTERVAL_CERT_GAP"
SAMPLED_STATUS = "sampled_candidate_not_lean_proof"
TARGET_LOWER = "-94119513411/500000000000000000000000000000"
TARGET_UPPER = "1866608532757/500000000000000000000000000000"
CELL_L = "0"
CELL_U = "1/10"

TARGET_EXPR = "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr"
TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_combined_bounds"
)
TARGET_CLOSED_FORM_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_closedForm_residual_bounds_of_combined_bounds"
)
TARGET_PROOF_DATA = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_combined_bounds"
)


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def file_hash(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def parse_rat(value: str | int) -> Fraction:
    if isinstance(value, int):
        return Fraction(value, 1)
    text = str(value)
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def rat_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def normalize_segments(segmented: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not segmented:
        return []
    segments: list[dict[str, Any]] = []
    for item in segmented.get("segments", []):
        if not isinstance(item, dict):
            continue
        lower = item.get("residualLower")
        upper = item.get("residualUpper")
        budget_passes = False
        if lower is not None and upper is not None:
            budget_passes = (
                parse_rat(TARGET_LOWER) <= parse_rat(lower)
                and parse_rat(upper) <= parse_rat(TARGET_UPPER)
            )
        proof_status = item.get("sourceProofStatus")
        segments.append(
            {
                "cell": item.get("cell"),
                "segmentL": item.get("segmentL"),
                "segmentU": item.get("segmentU"),
                "combinedLower": lower,
                "combinedUpper": upper,
                "sourceProofStatus": proof_status,
                "budgetPassesExactRational": budget_passes,
                "isProofGrade": proof_status
                not in (None, SAMPLED_STATUS, "probe", "diagnostic"),
                "proofGradeCombinedBounds": "missing",
            }
        )
    return segments


def coverage_report(segments: list[dict[str, Any]]) -> dict[str, Any]:
    if not segments:
        return {
            "coveragePassedExactRational": False,
            "adjacencyPassedExactRational": False,
            "segmentNonemptyPassedExactRational": False,
            "firstFailure": "STEP33_A1_SUB0_COMBINED_SEGMENT_INPUTS_MISSING",
        }
    lefts = [parse_rat(str(item["segmentL"])) for item in segments]
    rights = [parse_rat(str(item["segmentU"])) for item in segments]
    nonempty = all(left <= right for left, right in zip(lefts, rights))
    endpoint = lefts[0] == parse_rat(CELL_L) and rights[-1] == parse_rat(CELL_U)
    adjacency = all(rights[i] == lefts[i + 1] for i in range(len(segments) - 1))
    coverage = nonempty and endpoint and adjacency
    return {
        "coveragePassedExactRational": coverage,
        "adjacencyPassedExactRational": adjacency,
        "segmentNonemptyPassedExactRational": nonempty,
        "leftEndpoint": rat_text(lefts[0]),
        "rightEndpoint": rat_text(rights[-1]),
        "expectedLeftEndpoint": CELL_L,
        "expectedRightEndpoint": CELL_U,
        "firstFailure": None if coverage else "STEP33_A1_SUB0_COMBINED_SEGMENT_COVERAGE_FAIL",
    }


def build_report(segmented_path: Path) -> dict[str, Any]:
    segmented = load_json(segmented_path)
    segments = normalize_segments(segmented)
    coverage = coverage_report(segments)
    budget_passed = bool(segments) and all(
        segment["budgetPassesExactRational"] for segment in segments
    )
    proof_grade_segments = bool(segments) and all(
        segment["isProofGrade"] for segment in segments
    )
    target_width = parse_rat(TARGET_UPPER) - parse_rat(TARGET_LOWER)

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": STATUS,
        "firstFailure": FIRST_FAILURE,
        "failureCodes": [
            FIRST_FAILURE,
            "STEP33_A1_SUB0_COMBINED_INTERVAL_PROOF_GRADE_SOURCE_MISSING",
            "STEP33_A1_SUB0_COMBINED_INTERVAL_LEAN_PAYLOAD_MISSING",
            "STEP33_A1_SUB0_CANCELLATION_PRESERVING_TAYLOR_REMAINDER_GAP",
        ],
        "proofStatus": {
            "isLeanProofData": False,
            "outLeanWritten": False,
            "proofSafeClosedFields": 0,
            "combinedReceiverCheckedInLean": True,
            "combinedExpressionDefinedInLean": True,
            "combinedIntervalTheoremCheckedInLean": True,
            "proofGradeCombinedBoundsPresent": False,
            "sampledCandidateIsProof": False,
            "segmentCoveragePassedExactRational": coverage[
                "coveragePassedExactRational"
            ],
            "allSegmentsBudgetPassedExactRational": budget_passed,
            "allSegmentsProofGrade": proof_grade_segments,
        },
        "cell": {
            "cellL": CELL_L,
            "cellU": CELL_U,
            "targetLower": TARGET_LOWER,
            "targetUpper": TARGET_UPPER,
            "targetWidth": rat_text(target_width),
        },
        "targetLeanSurface": {
            "file": COMBINED_FILE,
            "certCheckerFile": CERT_CHECKER_FILE,
            "certStructure": "Step33Sub0CombinedCancellationIntervalCert",
            "certValidPredicate": "Step33Sub0CombinedCancellationIntervalCert.Valid",
            "certToHCombined": "Step33Sub0CombinedCancellationIntervalCert.Valid.to_hCombined",
            "expression": TARGET_EXPR,
            "consumerTheorem": TARGET_THEOREM,
            "closedFormTheorem": TARGET_CLOSED_FORM_THEOREM,
            "proofDataWrapper": TARGET_PROOF_DATA,
            "boundInputsFile": BOUND_INPUTS_FILE,
            "normReceiverFile": NORM_RECEIVER_FILE,
            "p45BridgeFile": P45_BRIDGE_FILE,
            "landingFile": LANDING_FILE,
        },
        "targetStatement": (
            "forall eta in Set.Icc (0 : Real) ((1 : Real) / 10), "
            f"({TARGET_LOWER}) <= {TARGET_EXPR} eta and "
            f"{TARGET_EXPR} eta <= ({TARGET_UPPER})"
        ),
        "combinedExpressionMeaning": (
            "rawOmegaATaylorPolynomial assembledDegree 1/20 ResidualTaylorCoeff eta "
            "+ ScaledCancellationRhs eta"
        ),
        "requiredCertificate": {
            "kind": "proof_grade_interval_or_rational_certificate",
            "mustProve": "same-expression lower/upper bound for the whole combined expression",
            "mayUse": [
                "rational interval arithmetic",
                "Lean-verifiable matrix/free polynomial interval certificate",
                "independently checkable generated rational output",
            ],
            "mustNotUse": [
                "sampled JSON as proof",
                "separate norm bounds for residualTaylor polynomial and ScaledCancellationRhs",
                "independent raw/poly interval subtraction",
                "product-budget rows route after width-fail",
            ],
        },
        "candidateSegmentSource": {
            "path": str(segmented_path),
            "exists": segmented is not None,
            "schema": segmented.get("schema") if segmented else None,
            "status": segmented.get("status") if segmented else None,
            "proofMode": segmented.get("proofMode") if segmented else None,
            "sourceIsProofGrade": False,
            "interpretation": (
                "The candidate records exact rational coverage and budget checks, "
                "but its sourceProofStatus remains sampled_candidate_not_lean_proof."
            ),
        },
        "segments": segments,
        "candidateArithmeticStatus": {
            "coverage": coverage,
            "budgetPassedExactRational": budget_passed,
            "candidateReadyForLeanShape": coverage["coveragePassedExactRational"]
            and budget_passed,
            "proofGradeCombinedBoundsPresent": proof_grade_segments,
        },
        "closedLocalFacts": [
            "OmegaPrime generated Taylor remainder cert is Valid and has a public bound.",
            "Omega Taylor bound is obtained by integrating OmegaPrime plus anchor interval.",
            "rawDeriv - assembledPoly equals the scaled cancellation RHS.",
            "deriv residual equals residualTaylor P45 polynomial plus ScaledCancellationRhs.",
            "triangle split is killed by checked residualTaylor final-slope failures.",
            "rows0..11 independent product budget is width-killed.",
        ],
        "rejectedRoutes": {
            "independentTriangleSplit": (
                "killed: residualTaylor polynomial alone exceeds final slope at the center"
            ),
            "rowsProductBudgetRefinement": (
                "not a closure path while it preserves the independent product-budget style"
            ),
            "sampledSegmentPayload": "diagnostic only, not proof evidence",
        },
        "nextImplementablePatch": {
            "recommendation": (
                "build a proof-grade combined interval backend that emits a Lean "
                "certificate proving Step33Sub0CombinedCancellationIntervalCert.Valid"
            ),
            "firstFailureIfMissing": FIRST_FAILURE,
            "leanPayloadTarget": (
                "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload.lean"
            ),
            "checkerTheorem": (
                "Step33Sub0CombinedCancellationIntervalCert.Valid.to_hCombined"
            ),
        },
        "sourceDefinitionHashes": {
            COMBINED_FILE: file_hash(ROOT / COMBINED_FILE),
            CERT_CHECKER_FILE: file_hash(ROOT / CERT_CHECKER_FILE),
            BOUND_INPUTS_FILE: file_hash(ROOT / BOUND_INPUTS_FILE),
            NORM_RECEIVER_FILE: file_hash(ROOT / NORM_RECEIVER_FILE),
            P45_BRIDGE_FILE: file_hash(ROOT / P45_BRIDGE_FILE),
            LANDING_FILE: file_hash(ROOT / LANDING_FILE),
            str(segmented_path.relative_to(ROOT)): file_hash(segmented_path),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Sub0 Combined Cancellation Interval Certificate",
        "",
        "Fail-closed certificate ledger.  This is not Lean proof data and does",
        "not close Step33A.1-A.",
        "",
        "## Summary",
        "",
        f"- schema: `{report['schema']}`",
        f"- route: `{report['routeId']}`",
        f"- status: `{report['status']}`",
        f"- first failure: `{report['firstFailure']}`",
        f"- target lower: `{report['cell']['targetLower']}`",
        f"- target upper: `{report['cell']['targetUpper']}`",
        f"- target width: `{report['cell']['targetWidth']}`",
        "",
        "## Lean Surface",
        "",
    ]
    for key, value in report["targetLeanSurface"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "Target statement:",
            "",
            "```text",
            report["targetStatement"],
            "```",
            "",
            "Combined expression:",
            "",
            f"`{report['combinedExpressionMeaning']}`",
            "",
            "## Proof Status",
            "",
        ]
    )
    for key, value in report["proofStatus"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Candidate Segments", ""])
    if report["segments"]:
        for segment in report["segments"]:
            lines.extend(
                [
                    f"- cell `{segment['cell']}`:",
                    f"  segment = `[{segment['segmentL']}, {segment['segmentU']}]`",
                    f"  combined = `[{segment['combinedLower']}, {segment['combinedUpper']}]`",
                    f"  budgetPassesExactRational = `{segment['budgetPassesExactRational']}`",
                    f"  sourceProofStatus = `{segment['sourceProofStatus']}`",
                    f"  isProofGrade = `{segment['isProofGrade']}`",
                    f"  proofGradeCombinedBounds = `{segment['proofGradeCombinedBounds']}`",
                ]
            )
    else:
        lines.append("- no candidate segments found")
    lines.extend(["", "## Candidate Arithmetic", ""])
    arithmetic = report["candidateArithmeticStatus"]
    coverage = arithmetic["coverage"]
    for key, value in coverage.items():
        lines.append(f"- coverage.{key}: `{value}`")
    lines.extend(
        [
            f"- budgetPassedExactRational: `{arithmetic['budgetPassedExactRational']}`",
            f"- candidateReadyForLeanShape: `{arithmetic['candidateReadyForLeanShape']}`",
            f"- proofGradeCombinedBoundsPresent: `{arithmetic['proofGradeCombinedBoundsPresent']}`",
            "",
            "## Required Certificate",
            "",
        ]
    )
    cert = report["requiredCertificate"]
    lines.extend(
        [
            f"- kind: `{cert['kind']}`",
            f"- must prove: `{cert['mustProve']}`",
            "",
            "May use:",
        ]
    )
    for item in cert["mayUse"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("Must not use:")
    for item in cert["mustNotUse"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Closed Local Facts", ""])
    for item in report["closedLocalFacts"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Rejected Routes", ""])
    for key, value in report["rejectedRoutes"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Candidate Source", ""])
    for key, value in report["candidateSegmentSource"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Next Implementable Patch", ""])
    for key, value in report["nextImplementablePatch"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Failure Codes", ""])
    for code in report["failureCodes"]:
        lines.append(f"- `{code}`")
    lines.extend(["", "## Source Hashes", ""])
    for key, value in report["sourceDefinitionHashes"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--segmented-payload", type=Path, default=DEFAULT_SEGMENTED_PAYLOAD)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(args.segmented_payload)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    args.out_md.write_text(render_md(report), encoding="utf-8")


if __name__ == "__main__":
    run()
