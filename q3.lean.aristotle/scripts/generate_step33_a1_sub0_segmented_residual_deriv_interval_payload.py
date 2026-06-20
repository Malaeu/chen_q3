#!/usr/bin/env python3
"""Fail-closed segmented residual-derivative certificate contract for Step33A.1-A.

This script is a control-plane artifact.  It records the exact Lean interface
for the first-subchunk same-unit segmented residual-derivative certificate and
the proof obligations a future exact interval generator must close before any
Lean payload theorem may be emitted.

It deliberately does not trust sampled direct-derivative overlays as proof
data.  Broad raw/poly subtraction is recorded only as diagnostic context; the
spendable field is a direct residual derivative interval per segment.
"""

from __future__ import annotations

import argparse
from decimal import Decimal
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_INTERPOLATION_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_residual_deriv_interpolation_payload.json"
)
DEFAULT_DIRECT_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0_denom1e30.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_segmented_residual_deriv_interval_payload.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_segmented_residual_deriv_interval_payload.md"
)

SCHEMA = "q3_psdpd_step33_a1_sub0_segmented_residual_deriv_interval_payload.v4"
ROUTE_ID = "STEP33_A1_SUB0_SEGMENTED_RESIDUAL_DERIV"
FAILURE_CODE = "STEP33_A1_SUB0_RESIDUAL_DERIV_SAME_UNIT_SEGMENT_CERT_FAIL"
CLOSED_FORM_FAILURE_CODE = "STEP33_A1_SUB0_CLOSED_FORM_RESIDUAL_INTERVAL_BOUNDS_MISSING"
FULL_TAYLOR_FAILURE_CODE = (
    "STEP33_A1_SUB0_FULL_TAYLOR_RESIDUAL_INTERVAL_BOUNDS_MISSING"
)
DERIVMODEL_ADAPTER_MISMATCH_CODE = (
    "STEP33_A1_SUB0_DERIVMODEL_ADAPTER_POLYNOMIAL_MISMATCH"
)
TARGET_SLOPE = "1866608532757/500000000000000000000000000000"
CELL_L = "0"
CELL_U = "1/10"

CHECKER_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean"
LANDING_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean"


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
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return digest[:16]


def parse_rat(value: str | int | float) -> Fraction:
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        raise TypeError("float input is not accepted for exact rational parsing")
    text = str(value)
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def rat_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def first_subchunk_item(overlay: dict[str, Any] | None) -> dict[str, Any] | None:
    if not overlay:
        return None
    for item in overlay.get("subchunks") or []:
        if isinstance(item, dict) and item.get("subchunk") == 0:
            return item
    return None


def first_subchunk_candidate(overlay: dict[str, Any] | None) -> dict[str, Any] | None:
    item = first_subchunk_item(overlay)
    if not item:
        return None
    return {
        "proofStatus": item.get("proofStatus"),
        "remainingAnalyticFields": item.get("remainingAnalyticFields"),
        "residualDerivativeIntervalCandidates": item.get(
            "residualDerivativeIntervalCandidates"
        ),
        "seededScalars": item.get("seededScalars"),
    }


def candidate_segments(overlay: dict[str, Any] | None) -> list[dict[str, Any]]:
    item = first_subchunk_item(overlay)
    if not item:
        return []
    segments: list[dict[str, Any]] = []
    for candidate in item.get("residualDerivativeIntervalCandidates") or []:
        if not isinstance(candidate, dict):
            continue
        left = parse_rat(candidate["left"])
        right = parse_rat(candidate["right"])
        lower = parse_rat(candidate["derivLower"])
        upper = parse_rat(candidate["derivUpper"])
        target = parse_rat(TARGET_SLOPE)
        budget_passes = -target <= lower and upper <= target
        segments.append(
            {
                "cell": candidate.get("cell"),
                "segmentL": rat_text(left),
                "segmentU": rat_text(right),
                "rawLower": None,
                "rawUpper": None,
                "polyLower": None,
                "polyUpper": None,
                "residualLower": rat_text(lower),
                "residualUpper": rat_text(upper),
                "sourceProofStatus": candidate.get("proofStatus"),
                "budgetPassesExactRational": budget_passes,
                "analyticResidualBoundsProof": "missing",
            }
        )
    return sorted(segments, key=lambda item: item.get("cell") or 0)


def coverage_report(segments: list[dict[str, Any]]) -> dict[str, Any]:
    if not segments:
        return {
            "coveragePassedExactRational": False,
            "adjacencyPassedExactRational": False,
            "firstFailure": "STEP33_A1_SUB0_SEGMENT_PROOF_INPUTS_MISSING",
        }
    cell_l = parse_rat(CELL_L)
    cell_u = parse_rat(CELL_U)
    lefts = [parse_rat(item["segmentL"]) for item in segments]
    rights = [parse_rat(item["segmentU"]) for item in segments]
    nonempty = all(left <= right for left, right in zip(lefts, rights))
    endpoint = lefts[0] == cell_l and rights[-1] == cell_u
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
        "firstFailure": None if coverage else "STEP33_A1_SUB0_SEGMENT_COVERAGE_FAIL",
    }


def build_report(
    interpolation_payload_path: Path,
    direct_overlay_path: Path,
) -> dict[str, Any]:
    interpolation_payload = load_json(interpolation_payload_path)
    direct_overlay = load_json(direct_overlay_path)
    prior_status = interpolation_payload.get("status") if interpolation_payload else None
    prior_first_danger = (
        interpolation_payload.get("firstDangerPoint") if interpolation_payload else None
    )
    segments = candidate_segments(direct_overlay)
    coverage = coverage_report(segments)
    budget_passed = bool(segments) and all(
        segment["budgetPassesExactRational"] for segment in segments
    )
    candidate_ready = coverage["coveragePassedExactRational"] and budget_passed
    status = (
        "fail_closed_missing_full_taylor_residual_interval_proof"
        if candidate_ready
        else "fail_closed_missing_segment_cert"
    )

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": status,
        "failureCodes": [
            FAILURE_CODE,
            "STEP33_A1_SUB0_RESIDUAL_INTERVAL_PROOF_MISSING",
            FULL_TAYLOR_FAILURE_CODE,
            DERIVMODEL_ADAPTER_MISMATCH_CODE,
        ],
        "proofMode": "exact_rational_same_expression_interval",
        "target": {
            "family": "primary_finite",
            "row": 0,
            "parentChunk": 0,
            "subchunk": 0,
        },
        "cell": {
            "cellL": CELL_L,
            "cellU": CELL_U,
            "targetSlope": TARGET_SLOPE,
        },
        "segmentCount": len(segments),
        "segments": segments,
        "coveragePassed": coverage["coveragePassedExactRational"],
        "adjacencyPassed": coverage["adjacencyPassedExactRational"],
        "segmentNonemptyPassed": coverage.get("segmentNonemptyPassedExactRational"),
        "allSegmentsBudgetPassed": budget_passed,
        "candidateArithmeticStatus": {
            "coverage": coverage,
            "budgetPassedExactRational": budget_passed,
            "candidateReadyForLeanShape": candidate_ready,
            "proofGradeResidualBoundsPresent": False,
            "proofGradeClosedFormResidualBoundsPresent": False,
            "proofGradeFullTaylorResidualBoundsPresent": False,
            "fullTaylorPolynomialDerivativeCrosswalkPresent": True,
            "fullTaylorResidualDerivativeCrosswalkPresent": True,
        },
        "proofSafeClosedFields": 0,
        "outLeanWritten": False,
        "leanInterfaces": {
            "checkerFile": CHECKER_FILE,
            "checkerStructure": "ResidualDerivativeSegmentIntervalCert",
            "checkerSingleConstructor": "ResidualDerivativeSegmentIntervalCert.single",
            "checkerPreferredValidity": (
                "ResidualDerivativeSegmentIntervalCert.DirectValid"
            ),
            "checkerPreferredSingleValidityConstructor": (
                "ResidualDerivativeSegmentIntervalCert.DirectValid.of_single_residual_bounds"
            ),
            "checkerPreferredTheorem": (
                "ResidualDerivativeSegmentIntervalCert.DirectValid.residual_norm_le"
            ),
            "checkerLedgerValidity": "ResidualDerivativeSegmentIntervalCert.Valid",
            "checkerLedgerSingleValidityConstructor": (
                "ResidualDerivativeSegmentIntervalCert.Valid.of_single_bounds"
            ),
            "landingFile": LANDING_FILE,
            "sub0ClosedFormResidualDerivativeBridge": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "residual_deriv_eq_closedForm_sub_polynomial_deriv"
            ),
            "sub0DerivmodelAdapterMismatchFence": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "derivmodel_coeff_zero_mismatch_current_adapter_coeff"
            ),
            "sub0FullTaylorCoeff": (
                "primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeff"
            ),
            "sub0FullTaylorCert": (
                "primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert"
            ),
            "sub0FullTaylorPolynomialDerivativeCrosswalk": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "fullTaylor_polynomial_deriv_eq_derivmodel"
            ),
            "sub0FullTaylorResidualDerivativeCrosswalk": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "fullTaylor_residual_deriv_eq_closedForm"
            ),
            "sub0ConcreteSegmentData": (
                "primaryFiniteRow0Parent0Split100Sub0DirectResidualSegmentCert"
            ),
            "sub0ClosedFormValidityBridge": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "direct_segment_cert_valid_of_closedForm_residual_bounds"
            ),
            "sub0ClosedFormProofDataWrapper": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_"
                "and_closedForm_residual_bounds"
            ),
            "sub0PreferredNormWrapper": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "residual_deriv_norm_bound_of_direct_segment_cert"
            ),
            "sub0PreferredProofDataWrapper": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_"
                "and_direct_segment_interval_cert"
            ),
            "sub0LedgerProofDataWrapper": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_"
                "and_segment_interval_cert"
            ),
        },
        "certFields": [
            "segmentCount",
            "segmentL",
            "segmentU",
            "rawLower",
            "rawUpper",
            "polyLower",
            "polyUpper",
            "residualLower",
            "residualUpper",
        ],
        "rationalProofObligations": [
            "exact segment coverage of Set.Icc 0 (1/10) (candidate passes)",
            "exact segment adjacency/no-gap proof (candidate passes)",
            (
                "proof-grade bounds for "
                "primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta "
                "- rawOmegaATaylorPolynomial 15 (1/20) "
                "primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta "
                "on Set.Icc 0 (1/10) (missing)"
            ),
            (
                "do not replace deriv current-adapter polynomial by the generated "
                "degree-15 derivmodel polynomial: Lean checks a coefficient mismatch; "
                "use the full Taylor cert crosswalk instead"
            ),
            f"for every segment: -{TARGET_SLOPE} <= residualLower (candidate passes)",
            f"for every segment: residualUpper <= {TARGET_SLOPE} (candidate passes)",
            (
                "checked full Taylor bridge: deriv residual equals the closed-form "
                "raw derivative minus the generated degree-15 derivative model"
            ),
            (
                "current-adapter closed-form bridge is checked but is not the sampled "
                "full Taylor residual source"
            ),
            "optional ledger: proof-grade raw derivative enclosure per segment",
            "optional ledger: proof-grade polynomial derivative enclosure per segment",
        ],
        "guard": [
            "not Lean proof data",
            "do not trust sampled direct-derivative overlay as proof",
            "do not spend bounds for RawCenterCoeffOnlyCert as bounds for the full Taylor candidate",
            "do not spend independent raw/poly boxes unless the residual interval itself fits",
            "do not emit generated Lean payload until all segment obligations close",
            "the spendable field is the direct same-unit residual derivative interval",
        ],
        "sourceStatus": {
            "interpolationPayloadPath": str(interpolation_payload_path),
            "interpolationPayloadExists": interpolation_payload is not None,
            "interpolationPayloadStatus": prior_status,
            "interpolationFirstDangerPoint": prior_first_danger,
            "directOverlayPath": str(direct_overlay_path),
            "directOverlayExists": direct_overlay is not None,
            "directOverlayStatus": direct_overlay.get("status") if direct_overlay else None,
            "diagnosticSub0Candidate": first_subchunk_candidate(direct_overlay),
            "derivmodelAdapterPolynomialCrosswalkStatus": (
                "blocked_for_current_adapter_closed_by_full_taylor_cert"
            ),
            "fullTaylorResidualCrosswalkStatus": "checked_in_lean",
        },
        "sourceDefinitionHashes": {
            CHECKER_FILE: file_hash(ROOT / CHECKER_FILE),
            LANDING_FILE: file_hash(ROOT / LANDING_FILE),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Sub0 Segmented Residual-Derivative Payload",
        "",
        "Fail-closed skeleton.  This is not Lean proof data.",
        "",
        "## Summary",
        "",
        f"- schema: `{report['schema']}`",
        f"- route: `{report['routeId']}`",
        f"- status: `{report['status']}`",
        f"- proof mode: `{report['proofMode']}`",
        f"- target slope: `{report['cell']['targetSlope']}`",
        f"- segment count: `{report['segmentCount']}`",
        f"- coverage passed: `{report['coveragePassed']}`",
        f"- adjacency passed: `{report['adjacencyPassed']}`",
        f"- budget passed: `{report['allSegmentsBudgetPassed']}`",
        f"- proof-safe closed fields: `{report['proofSafeClosedFields']}`",
        f"- Lean emitted: `{report['outLeanWritten']}`",
        "",
        "## Lean Interfaces",
        "",
    ]
    for key, value in report["leanInterfaces"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Certificate Fields", ""])
    for field in report["certFields"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "## Candidate Segments", ""])
    if report["segments"]:
        for segment in report["segments"]:
            lines.extend(
                [
                    f"- cell `{segment['cell']}`:",
                    f"  segment = `[{segment['segmentL']}, {segment['segmentU']}]`",
                    f"  residual = `[{segment['residualLower']}, {segment['residualUpper']}]`",
                    f"  budgetPassesExactRational = `{segment['budgetPassesExactRational']}`",
                    f"  sourceProofStatus = `{segment['sourceProofStatus']}`",
                    f"  analyticResidualBoundsProof = `{segment['analyticResidualBoundsProof']}`",
                ]
            )
    else:
        lines.append("- no candidate segments extracted")
    lines.extend(["", "## Candidate Arithmetic", ""])
    arithmetic = report["candidateArithmeticStatus"]
    lines.extend(
        [
            f"- coveragePassedExactRational: `{arithmetic['coverage']['coveragePassedExactRational']}`",
            f"- adjacencyPassedExactRational: `{arithmetic['coverage']['adjacencyPassedExactRational']}`",
            f"- segmentNonemptyPassedExactRational: `{arithmetic['coverage']['segmentNonemptyPassedExactRational']}`",
            f"- budgetPassedExactRational: `{arithmetic['budgetPassedExactRational']}`",
            f"- candidateReadyForLeanShape: `{arithmetic['candidateReadyForLeanShape']}`",
            f"- proofGradeResidualBoundsPresent: `{arithmetic['proofGradeResidualBoundsPresent']}`",
            f"- proofGradeClosedFormResidualBoundsPresent: `{arithmetic['proofGradeClosedFormResidualBoundsPresent']}`",
            f"- proofGradeFullTaylorResidualBoundsPresent: `{arithmetic['proofGradeFullTaylorResidualBoundsPresent']}`",
            f"- fullTaylorPolynomialDerivativeCrosswalkPresent: `{arithmetic['fullTaylorPolynomialDerivativeCrosswalkPresent']}`",
            f"- fullTaylorResidualDerivativeCrosswalkPresent: `{arithmetic['fullTaylorResidualDerivativeCrosswalkPresent']}`",
        ]
    )
    lines.extend(["", "## Rational Proof Obligations", ""])
    for item in report["rationalProofObligations"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Failure Codes", ""])
    for code in report["failureCodes"]:
        lines.append(f"- `{code}`")
    lines.extend(["", "## Guard", ""])
    for item in report["guard"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Source Status",
            "",
            f"- interpolation payload status: `{report['sourceStatus']['interpolationPayloadStatus']}`",
            f"- interpolation first danger point: `{report['sourceStatus']['interpolationFirstDangerPoint']}`",
            f"- direct overlay status: `{report['sourceStatus']['directOverlayStatus']}`",
            f"- full Taylor residual crosswalk: `{report['sourceStatus']['fullTaylorResidualCrosswalkStatus']}`",
            "",
            "The diagnostic direct-overlay candidate now supplies a one-segment",
            "candidate whose exact rational coverage and budget arithmetic pass.",
            "The full Taylor residual derivative crosswalk is now checked in Lean.",
            "The candidate remains non-spendable because the proof-grade interval",
            "bound for that full Taylor residual expression is still missing; only",
            "a proof-grade `ResidualDerivativeSegmentIntervalCert.DirectValid`",
            "witness can close the preferred receiver.  The richer `Valid` witness",
            "remains available only when a separate raw/poly ledger is also proved.",
            "",
        ]
    )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--interpolation-payload",
        type=Path,
        default=DEFAULT_INTERPOLATION_PAYLOAD,
    )
    parser.add_argument("--direct-overlay", type=Path, default=DEFAULT_DIRECT_OVERLAY)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(args.interpolation_payload, args.direct_overlay)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} proof_safe={proof_safe} lean={lean} out_json={out_json}".format(
            status=report["status"],
            proof_safe=report["proofSafeClosedFields"],
            lean=report["outLeanWritten"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
