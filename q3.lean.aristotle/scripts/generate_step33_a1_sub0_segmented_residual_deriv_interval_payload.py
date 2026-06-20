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

SCHEMA = "q3_psdpd_step33_a1_sub0_segmented_residual_deriv_interval_payload.v1"
ROUTE_ID = "STEP33_A1_SUB0_SEGMENTED_RESIDUAL_DERIV"
FAILURE_CODE = "STEP33_A1_SUB0_RESIDUAL_DERIV_SAME_UNIT_SEGMENT_CERT_FAIL"
TARGET_SLOPE = "1866608532757/500000000000000000000000000000"

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


def first_subchunk_candidate(overlay: dict[str, Any] | None) -> dict[str, Any] | None:
    if not overlay:
        return None
    for item in overlay.get("subchunks") or []:
        if isinstance(item, dict) and item.get("subchunk") == 0:
            return {
                "proofStatus": item.get("proofStatus"),
                "remainingAnalyticFields": item.get("remainingAnalyticFields"),
                "residualDerivativeIntervalCandidates": item.get(
                    "residualDerivativeIntervalCandidates"
                ),
                "seededScalars": item.get("seededScalars"),
            }
    return None


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

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": "fail_closed_missing_segment_cert",
        "failureCodes": [
            FAILURE_CODE,
            "STEP33_A1_SUB0_SEGMENT_PROOF_INPUTS_MISSING",
        ],
        "proofMode": "exact_rational_same_expression_interval",
        "target": {
            "family": "primary_finite",
            "row": 0,
            "parentChunk": 0,
            "subchunk": 0,
        },
        "cell": {
            "cellL": "0",
            "cellU": "1/10",
            "targetSlope": TARGET_SLOPE,
        },
        "segmentCount": 0,
        "segments": [],
        "coveragePassed": False,
        "adjacencyPassed": False,
        "allSegmentsBudgetPassed": False,
        "proofSafeClosedFields": 0,
        "outLeanWritten": False,
        "leanInterfaces": {
            "checkerFile": CHECKER_FILE,
            "checkerStructure": "ResidualDerivativeSegmentIntervalCert",
            "checkerValidity": "ResidualDerivativeSegmentIntervalCert.Valid",
            "checkerTheorem": (
                "ResidualDerivativeSegmentIntervalCert.Valid.residual_norm_le"
            ),
            "landingFile": LANDING_FILE,
            "sub0NormWrapper": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "residual_deriv_norm_bound_of_segment_cert"
            ),
            "sub0ProofDataWrapper": (
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
            "exact segment coverage of Set.Icc 0 (1/10)",
            "exact segment adjacency/no-gap proof",
            "residualDeriv eta = rawDeriv eta - polyDeriv eta on the cell",
            "proof-grade raw derivative enclosure per segment",
            "proof-grade polynomial derivative enclosure per segment",
            "same-expression direct residual derivative enclosure per segment",
            f"for every segment: -{TARGET_SLOPE} <= residualLower",
            f"for every segment: residualUpper <= {TARGET_SLOPE}",
        ],
        "guard": [
            "not Lean proof data",
            "do not trust sampled direct-derivative overlay as proof",
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
            "",
            "The diagnostic direct-overlay candidate remains non-spendable unless",
            "a proof-grade same-expression segment certificate supplies the",
            "`ResidualDerivativeSegmentIntervalCert.Valid` witness.",
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
