#!/usr/bin/env python3
"""Fail-closed Step33A.1-A sub0 residual-derivative interpolation skeleton.

This script is a control-plane artifact, not Lean proof data.  It checks the
current direct proof-input worklist, extracts the concrete first-subchunk
direct-norm target, and records the exact rational budget required by

    ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound

It deliberately does not read sampled derivative JSON as proof evidence and
does not emit Lean.  Until a future exact-rational interval routine derives
both a model-derivative norm bound and an interpolation/error bound on
`Set.Icc 0 (1/10)`, the output remains fail-closed.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_proof_input_worklist.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_residual_deriv_interpolation_payload.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_residual_deriv_interpolation_payload.md"
)

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_proof_input_worklist.v20"
)
OUTPUT_SCHEMA = "q3_psdpd_step33_a1_sub0_residual_deriv_interpolation_payload.v4"
RAW_POLY_CANDIDATE_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30.json"
)
DIRECT_DERIVATIVE_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0_denom1e30.json"
)
DERIVATIVE_BOUND_AUDIT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30.json"
)
EXPECTED_DERIVATIVE_MODEL_CANDIDATE = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30_derivfit.json"
)

TARGET = {
    "family": "primary_finite",
    "row": 0,
    "parentChunk": 0,
    "subchunk": 0,
}

DIRECT_NORM_INTERPOLATION_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound"
)
SUB0_INTERPOLATION_LANDING_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "primaryFiniteRow0Parent0Split100Sub0_"
    "cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_"
    "and_deriv_interpolation_error_bound"
)
SUB0_POLYNOMIAL_MODEL_LANDING_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "primaryFiniteRow0Parent0Split100Sub0_"
    "cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_"
    "and_deriv_polynomial_model_error_bound"
)

CERT_NAME = (
    "primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert"
)


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def validate_schema(data: dict[str, Any], *, path: Path, schema: str) -> None:
    found = data.get("schema")
    if found != schema:
        raise ValueError(f"{path}: expected schema {schema!r}, found {found!r}")


def parse_fraction(raw: str | int | None) -> Fraction | None:
    if raw is None:
        return None
    if isinstance(raw, int):
        return Fraction(raw, 1)
    text = str(raw).strip()
    if not text:
        return None
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    if "E" in text or "e" in text or "." in text:
        return Fraction(text)
    return Fraction(int(text), 1)


def format_fraction(value: Fraction | None) -> str | None:
    if value is None:
        return None
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def decimal_string(value: Fraction | None, digits: int = 24) -> str | None:
    if value is None:
        return None
    sign = "-" if value < 0 else ""
    value = abs(value)
    integer = value.numerator // value.denominator
    remainder = value.numerator % value.denominator
    if remainder == 0:
        return f"{sign}{integer}"
    out = []
    for _ in range(digits):
        remainder *= 10
        out.append(str(remainder // value.denominator))
        remainder %= value.denominator
    return f"{sign}{integer}.{''.join(out)}"


def find_target_subchunk(worklist: dict[str, Any]) -> dict[str, Any]:
    hits: list[dict[str, Any]] = []
    for parent in worklist.get("parents") or []:
        for item in parent.get("subchunks") or []:
            if all(item.get(key) == value for key, value in TARGET.items()):
                hits.append(item)
    if len(hits) != 1:
        raise ValueError(f"expected one target subchunk, found {len(hits)}")
    return hits[0]


def find_subchunk_item(items: list[Any], subchunk: int) -> dict[str, Any] | None:
    hits = [
        item for item in items
        if isinstance(item, dict) and item.get("subchunk") == subchunk
    ]
    if len(hits) > 1:
        raise ValueError(f"expected at most one subchunk {subchunk}, found {len(hits)}")
    return hits[0] if hits else None


def first_or_value(value: Any) -> Any:
    if isinstance(value, list):
        if len(value) != 1:
            raise ValueError(f"expected one value, found {value!r}")
        return value[0]
    return value


def derivative_model_candidate_inventory() -> dict[str, Any]:
    raw_candidate: dict[str, Any] = {
        "path": str(RAW_POLY_CANDIDATE_OVERLAY),
        "exists": RAW_POLY_CANDIDATE_OVERLAY.exists(),
        "usableAsDerivativeModelSource": False,
    }
    if RAW_POLY_CANDIDATE_OVERLAY.exists():
        raw_data = load_json(RAW_POLY_CANDIDATE_OVERLAY)
        item = find_subchunk_item(raw_data.get("candidates") or [], 0)
        raw_candidate.update(
            {
                "schema": raw_data.get("schema"),
                "status": raw_data.get("status"),
                "subchunkFound": item is not None,
                "functionKind": (
                    "raw_integrand_taylor_polynomial_candidate_not_derivative_model"
                ),
                "proofUseStatus": (
                    "not_allowed_as_modelDeriv_source_for_deriv_residual"
                ),
            }
        )
        if item is not None:
            raw_candidate.update(
                {
                    "degree": item.get("degree"),
                    "center": item.get("center"),
                    "radius": item.get("radius"),
                    "coeffCount": len(item.get("coeff") or []),
                    "polyAbs": item.get("polyAbs"),
                    "candidateGuard": item.get("candidateGuard"),
                }
            )

    direct_overlay: dict[str, Any] = {
        "path": str(DIRECT_DERIVATIVE_OVERLAY),
        "exists": DIRECT_DERIVATIVE_OVERLAY.exists(),
        "usableAsDerivativeModelSource": False,
    }
    if DIRECT_DERIVATIVE_OVERLAY.exists():
        overlay_data = load_json(DIRECT_DERIVATIVE_OVERLAY)
        item = find_subchunk_item(overlay_data.get("subchunks") or [], 0)
        seeded = (item or {}).get("seededFields") or {}
        direct_overlay.update(
            {
                "schema": overlay_data.get("schema"),
                "status": overlay_data.get("status"),
                "subchunkFound": item is not None,
                "functionKind": (
                    "sampled_residual_derivative_interval_candidate_not_polynomial_model"
                ),
                "proofUseStatus": (
                    "not_allowed_as_modelDeriv_source_without_universal_Lean_proof"
                ),
                "sourceDerivativeAuditStatus": overlay_data.get(
                    "sourceDerivativeAuditStatus"
                ),
            }
        )
        if item is not None:
            direct_overlay.update(
                {
                    "blockedOn": item.get("blockedOn"),
                    "remainingAnalyticFields": item.get("remainingAnalyticFields"),
                    "seededDerivLower": seeded.get("derivLower"),
                    "seededDerivUpper": seeded.get("derivUpper"),
                    "seededDerivSlope": seeded.get("derivSlope"),
                    "residualDerivativeIntervalCandidates": item.get(
                        "residualDerivativeIntervalCandidates"
                    ),
                }
            )

    audit: dict[str, Any] = {
        "path": str(DERIVATIVE_BOUND_AUDIT),
        "exists": DERIVATIVE_BOUND_AUDIT.exists(),
        "usableAsDerivativeModelSource": False,
    }
    if DERIVATIVE_BOUND_AUDIT.exists():
        audit_data = load_json(DERIVATIVE_BOUND_AUDIT)
        item = find_subchunk_item(audit_data.get("subchunks") or [], 0)
        audit.update(
            {
                "schema": audit_data.get("schema"),
                "status": audit_data.get("status"),
                "subchunkFound": item is not None,
                "functionKind": "diagnostic_sampled_derivative_audit_not_proof_data",
                "proofUseStatus": "not_allowed_as_Lean_payload",
            }
        )
        if item is not None:
            audit.update(
                {
                    "sampledSlope": item.get("sampledSlope"),
                    "derivSlope": item.get("derivSlope"),
                    "rawPolyEnvelopePasses": item.get("rawPolyEnvelopePasses"),
                    "intervalEnvelopePasses": item.get("intervalEnvelopePasses"),
                    "jetEnvelopePasses": item.get("jetEnvelopePasses"),
                    "secondDerivativeEnvelopePasses": item.get(
                        "secondDerivativeEnvelopePasses"
                    ),
                }
            )

    expected_derivfit = {
        "path": str(EXPECTED_DERIVATIVE_MODEL_CANDIDATE),
        "exists": EXPECTED_DERIVATIVE_MODEL_CANDIDATE.exists(),
        "usableAsDerivativeModelSource": EXPECTED_DERIVATIVE_MODEL_CANDIDATE.exists(),
        "expectedFunctionKind": "derivative_residual_polynomial_model_candidate",
    }

    has_source = bool(expected_derivfit["usableAsDerivativeModelSource"])
    return {
        "status": (
            "blocked_no_proof_grade_derivative_model_source_for_sub0"
            if not has_source
            else "derivative_model_source_candidate_present_not_lean_checked"
        ),
        "hasProofGradeDerivativeModelSource": False,
        "hasDerivativeModelCandidateFile": has_source,
        "rawPolynomialCandidate": raw_candidate,
        "directDerivativeOverlay": direct_overlay,
        "derivativeBoundAudit": audit,
        "expectedDerivativeModelCandidate": expected_derivfit,
        "decision": (
            "Do not use raw Taylor coefficients or sampled derivative intervals "
            "as modelDeriv.  Generate a derivative-residual polynomial source "
            "or prove the interpolation error directly."
        ),
    }


def build_report(
    *,
    worklist_path: Path,
    model_bound: Fraction | None,
    interpolation_error: Fraction | None,
) -> dict[str, Any]:
    worklist = load_json(worklist_path)
    validate_schema(worklist, path=worklist_path, schema=WORKLIST_SCHEMA)
    target = find_target_subchunk(worklist)
    norm_work = target.get("hResidualDerivNormWork") or {}
    seeded = target.get("seededScalars") or {}

    receiver = norm_work.get("directNormCertValidInterpolationReceiver")
    if receiver != DIRECT_NORM_INTERPOLATION_RECEIVER:
        raise ValueError(
            "target subchunk does not expose the checked interpolation receiver"
        )

    deriv_slope = parse_fraction(first_or_value(seeded.get("derivSlope")))
    if deriv_slope is None:
        raise ValueError("target subchunk missing derivSlope")

    source_inventory = derivative_model_candidate_inventory()

    exact_lhs = (
        None
        if model_bound is None or interpolation_error is None
        else model_bound + interpolation_error
    )
    budget_margin = None if exact_lhs is None else deriv_slope - exact_lhs
    budget_passes = None if budget_margin is None else budget_margin >= 0

    missing_inputs: list[str] = []
    if not source_inventory["hasProofGradeDerivativeModelSource"]:
        missing_inputs.append("STEP33_A1_SUB0_DERIVATIVE_MODEL_SOURCE_GAP")
    if model_bound is None:
        missing_inputs.append("STEP33_A1_SUB0_POLYNOMIAL_MODEL_EXACT_ARITHMETIC_GAP")
    if interpolation_error is None:
        missing_inputs.append("STEP33_A1_SUB0_INTERPOLATION_ERROR_EXACT_REMAINDER_GAP")
    if budget_passes is False:
        missing_inputs.append("STEP33_A1_SUB0_INTERPOLATION_BUDGET_FAIL")

    if missing_inputs:
        status = "blocked_missing_exact_interpolation_inputs"
    elif budget_passes:
        status = "exact_budget_arithmetic_pass_no_lean_emitted"
    else:
        status = "exact_budget_arithmetic_fail_no_lean_emitted"

    proof_safe_closed_fields = 0
    return {
        "schema": OUTPUT_SCHEMA,
        "status": status,
        "meaning": (
            "Fail-closed direct interpolation payload skeleton for the first "
            "Step33A.1-A residual-derivative cell.  This is not Lean proof "
            "data and does not emit a theorem."
        ),
        "target": TARGET,
        "worklistSource": str(worklist_path),
        "worklistSchema": worklist.get("schema"),
        "cert": CERT_NAME,
        "cell": {
            "set": "Set.Icc (0 : Real) ((1 : Real) / 10)",
            "cellL": seeded.get("cellL"),
            "cellU": seeded.get("cellU"),
            "derivSlope": format_fraction(deriv_slope),
            "derivSlopeDecimal": decimal_string(deriv_slope),
        },
        "receiver": {
            "validReceiver": receiver,
            "sub0LandingReceiver": SUB0_INTERPOLATION_LANDING_RECEIVER,
            "sub0PolynomialModelLandingReceiver": (
                SUB0_POLYNOMIAL_MODEL_LANDING_RECEIVER
            ),
            "leanShape": (
                "modelDeriv : Real -> Real, "
                "hModel : forall eta in cell, ||modelDeriv eta|| <= modelBound, "
                "hError : forall eta in cell, "
                "||deriv cert.residual eta - modelDeriv eta|| <= interpolationError, "
                "hBudget : interpolationError + modelBound <= data.derivSlope"
            ),
            "landingShape": (
                "modelDeriv : Real -> Real, "
                "hModel : forall eta in Set.Icc 0 (1/10), "
                "||modelDeriv eta|| <= modelBound, "
                "hError : forall eta in Set.Icc 0 (1/10), "
                "||deriv cert.residual eta - modelDeriv eta|| <= interpolationError, "
                "hBudget : interpolationError + modelBound <= "
                "1866608532757/500000000000000000000000000000"
            ),
            "polynomialModelLandingShape": (
                "modelDegree : Nat, modelCenter : Rat, "
                "modelCoeff : Fin (modelDegree + 1) -> Rat, "
                "hModelRadius : forall eta in Set.Icc 0 (1/10), "
                "|eta - modelCenter| <= modelRadius, "
                "hModelSum : sum_i |modelCoeff_i| * modelRadius^i <= modelBound, "
                "hError : forall eta in Set.Icc 0 (1/10), "
                "||deriv cert.residual eta - rawOmegaATaylorPolynomial modelDegree modelCenter modelCoeff eta|| <= interpolationError, "
                "hBudget : interpolationError + modelBound <= "
                "1866608532757/500000000000000000000000000000"
            ),
            "modelBoundReduction": (
                "For polynomial modelDeriv = rawOmegaATaylorPolynomial, "
                "the semantic hModel input is reduced to exact rational "
                "radius containment plus sum_abs_coeff arithmetic."
            ),
        },
        "inputs": {
            "modelBound": format_fraction(model_bound),
            "modelBoundDecimal": decimal_string(model_bound),
            "interpolationError": format_fraction(interpolation_error),
            "interpolationErrorDecimal": decimal_string(interpolation_error),
            "inputStatus": (
                "not_provided_exact_rational_bounds"
                if model_bound is None or interpolation_error is None
                else "provided_exact_rational_candidates_not_lean_proof"
            ),
        },
        "candidateSourceInventory": source_inventory,
        "exactBudget": {
            "relation": "interpolationError + modelBound <= derivSlope",
            "lhs": format_fraction(exact_lhs),
            "lhsDecimal": decimal_string(exact_lhs),
            "rhs": format_fraction(deriv_slope),
            "rhsDecimal": decimal_string(deriv_slope),
            "margin": format_fraction(budget_margin),
            "marginDecimal": decimal_string(budget_margin),
            "passes": budget_passes,
        },
        "missingInputs": missing_inputs,
        "firstDangerPoint": "STEP33_A1_SUB0_INTERPOLATION_ERROR_EXACT_REMAINDER_GAP",
        "proofSafeClosedFields": proof_safe_closed_fields,
        "outLeanWritten": False,
        "routeGuard": [
            "not Lean proof data",
            "does not import or trust sampled derivative JSON",
            "does not emit a Lean payload theorem",
            "sub0 landing receiver is checked separately in Lean",
            "polynomial-model landing receiver is checked separately in Lean",
            "raw Taylor polynomial candidates are not derivative-model sources",
            "sampled derivative intervals are not modelDeriv proof data",
            "modelBound must be derived by exact rational interval operations",
            "interpolationError must bound ||deriv residual - modelDeriv|| uniformly on [0, 1/10]",
            "a positive exact budget margin is required before Lean emission is enabled",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Sub0 Residual-Derivative Interpolation Payload",
        "",
        "Fail-closed skeleton.  This is not Lean proof data.",
        "",
        "## Summary",
        "",
        f"- schema: `{report['schema']}`",
        f"- status: `{report['status']}`",
        f"- cert: `{report['cert']}`",
        f"- receiver: `{report['receiver']['validReceiver']}`",
        f"- sub0 landing receiver: `{report['receiver']['sub0LandingReceiver']}`",
        f"- sub0 polynomial-model landing receiver: `{report['receiver']['sub0PolynomialModelLandingReceiver']}`",
        f"- cell: `{report['cell']['set']}`",
        f"- derivSlope: `{report['cell']['derivSlope']}`",
        f"- candidate source status: `{report['candidateSourceInventory']['status']}`",
        f"- proof-safe closed fields: `{report['proofSafeClosedFields']}`",
        f"- Lean emitted: `{report['outLeanWritten']}`",
        "",
        "## Exact Budget",
        "",
        f"- relation: `{report['exactBudget']['relation']}`",
        f"- lhs: `{report['exactBudget']['lhs']}`",
        f"- rhs: `{report['exactBudget']['rhs']}`",
        f"- margin: `{report['exactBudget']['margin']}`",
        f"- passes: `{report['exactBudget']['passes']}`",
        "",
        "## Missing Inputs",
        "",
    ]
    for item in report["missingInputs"]:
        lines.append(f"- `{item}`")
    if not report["missingInputs"]:
        lines.append("- none at exact arithmetic layer; Lean emission is still disabled")
    inventory = report["candidateSourceInventory"]
    lines.extend(
        [
            "",
            "## Candidate Source Inventory",
            "",
            f"- status: `{inventory['status']}`",
            f"- proof-grade derivative model source: `{inventory['hasProofGradeDerivativeModelSource']}`",
            f"- derivative-model candidate file present: `{inventory['hasDerivativeModelCandidateFile']}`",
            f"- decision: `{inventory['decision']}`",
            "",
            "### Raw Polynomial Candidate",
            "",
            f"- path: `{inventory['rawPolynomialCandidate']['path']}`",
            f"- exists: `{inventory['rawPolynomialCandidate']['exists']}`",
            f"- status: `{inventory['rawPolynomialCandidate'].get('status')}`",
            f"- function kind: `{inventory['rawPolynomialCandidate'].get('functionKind')}`",
            f"- proof use: `{inventory['rawPolynomialCandidate'].get('proofUseStatus')}`",
            "",
            "### Direct Derivative Overlay",
            "",
            f"- path: `{inventory['directDerivativeOverlay']['path']}`",
            f"- exists: `{inventory['directDerivativeOverlay']['exists']}`",
            f"- status: `{inventory['directDerivativeOverlay'].get('status')}`",
            f"- source audit status: `{inventory['directDerivativeOverlay'].get('sourceDerivativeAuditStatus')}`",
            f"- function kind: `{inventory['directDerivativeOverlay'].get('functionKind')}`",
            f"- proof use: `{inventory['directDerivativeOverlay'].get('proofUseStatus')}`",
            "",
            "### Expected Derivative Model Candidate",
            "",
            f"- path: `{inventory['expectedDerivativeModelCandidate']['path']}`",
            f"- exists: `{inventory['expectedDerivativeModelCandidate']['exists']}`",
            f"- expected kind: `{inventory['expectedDerivativeModelCandidate']['expectedFunctionKind']}`",
            "",
            "## Receiver Shape",
            "",
            f"`{report['receiver']['leanShape']}`",
            "",
            "## Sub0 Landing Shape",
            "",
            f"`{report['receiver']['landingShape']}`",
            "",
            "## Polynomial Model Landing Shape",
            "",
            f"`{report['receiver']['polynomialModelLandingShape']}`",
            "",
            f"`{report['receiver']['modelBoundReduction']}`",
            "",
            "## Guard",
            "",
        ]
    )
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--model-bound", type=str)
    parser.add_argument("--interpolation-error", type=str)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(
        worklist_path=args.worklist,
        model_bound=parse_fraction(args.model_bound),
        interpolation_error=parse_fraction(args.interpolation_error),
    )
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
