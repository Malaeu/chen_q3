#!/usr/bin/env python3
"""Generate the Step33A.1-A sub0 derivative-model candidate, fail closed.

This is not Lean proof data.  It differentiates the active raw Taylor
polynomial candidate by exact rational arithmetic and records the resulting
polynomial coefficients and radius sum.  The output deliberately does not
claim a proof of

    deriv cert.residual eta = modelDeriv eta + error eta

on the cell.  That uniform residual-derivative remainder/crosswalk remains the
next proof blocker.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

RAW_POLY_CANDIDATE = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30.json"
)
RESIDUALFIT_CANDIDATE = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30_residualfit.json"
)
DERIVFIT_CANDIDATE = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30_derivfit.json"
)

DEFAULT_OUT_JSON = REQUEST_DIR / "step33_a1_sub0_derivmodel_candidate.json"
DEFAULT_OUT_MD = REQUEST_DIR / "step33_a1_sub0_derivmodel_candidate.md"

OUTPUT_SCHEMA = "q3_psdpd_step33_a1_sub0_derivmodel_candidate.v1"
TARGET = {
    "family": "primary_finite",
    "row": 0,
    "parentChunk": 0,
    "subchunk": 0,
}
DERIV_SLOPE = Fraction(
    1866608532757,
    500000000000000000000000000000,
)


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def parse_fraction(raw: str | int) -> Fraction:
    if isinstance(raw, int):
        return Fraction(raw, 1)
    text = str(raw).strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(text)


def format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def decimal_string(value: Fraction, digits: int = 24) -> str:
    sign = "-" if value < 0 else ""
    value = abs(value)
    integer = value.numerator // value.denominator
    remainder = value.numerator % value.denominator
    if remainder == 0:
        return f"{sign}{integer}"
    out: list[str] = []
    for _ in range(digits):
        remainder *= 10
        out.append(str(remainder // value.denominator))
        remainder %= value.denominator
    return f"{sign}{integer}.{''.join(out)}"


def find_subchunk_item(data: dict[str, Any], subchunk: int) -> dict[str, Any]:
    hits = [
        item
        for item in data.get("candidates") or []
        if isinstance(item, dict) and item.get("subchunk") == subchunk
    ]
    if len(hits) != 1:
        raise ValueError(f"expected one candidate for subchunk {subchunk}, found {len(hits)}")
    return hits[0]


def candidate_item(path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    data = load_json(path)
    return data, find_subchunk_item(data, TARGET["subchunk"])


def derive_model(raw_item: dict[str, Any]) -> dict[str, Any]:
    raw_coeff = [parse_fraction(value) for value in raw_item["coeff"]]
    if len(raw_coeff) < 2:
        raise ValueError("raw polynomial must have degree at least one")
    raw_degree = int(raw_item["degree"])
    if raw_degree != len(raw_coeff) - 1:
        raise ValueError(
            f"raw degree {raw_degree} does not match coeff count {len(raw_coeff)}"
        )
    model_coeff = [
        Fraction(index + 1, 1) * raw_coeff[index + 1]
        for index in range(len(raw_coeff) - 1)
    ]
    radius = parse_fraction(raw_item["radius"])
    model_bound = sum(
        abs(coeff) * (radius ** index)
        for index, coeff in enumerate(model_coeff)
    )
    return {
        "rawDegree": raw_degree,
        "modelDegree": raw_degree - 1,
        "modelCoeff": model_coeff,
        "radius": radius,
        "center": raw_item["center"],
        "modelBound": model_bound,
    }


def build_report() -> dict[str, Any]:
    raw_data, raw_item = candidate_item(RAW_POLY_CANDIDATE)
    residualfit_data, residualfit_item = candidate_item(RESIDUALFIT_CANDIDATE)
    derivfit_data, derivfit_item = candidate_item(DERIVFIT_CANDIDATE)
    model = derive_model(raw_item)

    raw_coeff = raw_item["coeff"]
    residualfit_coeff = residualfit_item["coeff"]
    derivfit_coeff = derivfit_item["coeff"]
    raw_coeff_equality = {
        "rawEqualsResidualfit": raw_coeff == residualfit_coeff,
        "rawEqualsDerivfit": raw_coeff == derivfit_coeff,
        "residualfitEqualsDerivfit": residualfit_coeff == derivfit_coeff,
        "meaning": (
            "The existing derivfit candidate is still the raw-integrand "
            "Taylor polynomial coefficients, not the derivative-model "
            "coefficients consumed by modelDeriv."
        ),
    }

    model_coeff: list[Fraction] = model["modelCoeff"]
    budget_margin = DERIV_SLOPE - model["modelBound"]
    budget_passes = budget_margin >= 0
    first_danger = (
        "STEP33_A1_SUB0_DERIVMODEL_TO_RESIDUAL_DERIV_CROSSWALK_GAP"
        if budget_passes
        else "STEP33_A1_SUB0_DERIVMODEL_BUDGET_FAIL"
    )
    return {
        "schema": OUTPUT_SCHEMA,
        "status": (
            "derivmodel_candidate_generated_crosswalk_unproved_not_proof_data"
            if budget_passes
            else "derivmodel_candidate_budget_fail_not_spendable"
        ),
        "meaning": (
            "Exact rational derivative coefficients of the active raw "
            "polynomial candidate.  This is a model candidate only; it does "
            "not prove the uniform residual-derivative remainder.  The direct "
            "triangle receiver is spendable only if modelBound fits inside the "
            "derivSlope budget."
        ),
        "target": TARGET,
        "sources": {
            "rawPolynomialCandidate": str(RAW_POLY_CANDIDATE),
            "rawPolynomialSchema": raw_data.get("schema"),
            "rawPolynomialStatus": raw_data.get("status"),
            "residualfitCandidate": str(RESIDUALFIT_CANDIDATE),
            "residualfitSchema": residualfit_data.get("schema"),
            "residualfitStatus": residualfit_data.get("status"),
            "derivfitCandidate": str(DERIVFIT_CANDIDATE),
            "derivfitSchema": derivfit_data.get("schema"),
            "derivfitStatus": derivfit_data.get("status"),
        },
        "rawCoeffEquality": raw_coeff_equality,
        "derivation": {
            "formula": "modelCoeff[i] = (i + 1) * rawCoeff[i + 1]",
            "rawDegree": model["rawDegree"],
            "rawCoeffCount": len(raw_coeff),
            "modelDegree": model["modelDegree"],
            "modelCoeffCount": len(model_coeff),
            "center": model["center"],
            "radius": raw_item["radius"],
            "modelBoundFormula": "sum_i abs(modelCoeff[i]) * radius^i",
            "modelBound": format_fraction(model["modelBound"]),
            "modelBoundDecimal": decimal_string(model["modelBound"]),
            "modelCoeff": [format_fraction(value) for value in model_coeff],
            "modelCoeffDecimal": [decimal_string(value) for value in model_coeff],
        },
        "leanInterface": {
            "expectedModelDeriv": (
                "rawOmegaATaylorPolynomial modelDegree modelCenter modelCoeff"
            ),
            "modelDegree": model["modelDegree"],
            "modelCenter": model["center"],
            "modelRadius": raw_item["radius"],
            "modelBoundReduction": (
                "abs_rawOmegaATaylorPolynomial_le_sum_abs_coeff_mul_radius "
                "plus exact rational radius/sum arithmetic"
            ),
        },
        "directTriangleBudget": {
            "relation": "modelBound <= derivSlope even before interpolationError",
            "modelBound": format_fraction(model["modelBound"]),
            "modelBoundDecimal": decimal_string(model["modelBound"]),
            "derivSlope": format_fraction(DERIV_SLOPE),
            "derivSlopeDecimal": decimal_string(DERIV_SLOPE),
            "margin": format_fraction(budget_margin),
            "marginDecimal": decimal_string(budget_margin),
            "passes": budget_passes,
            "verdict": (
                "budget_passes_before_interpolation_error"
                if budget_passes
                else "DERIVMODEL_BUDGET_FAIL_modelBound_exceeds_derivSlope"
            ),
            "leanKillTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodel_budget_impossible"
            ),
        },
        "missingInputs": [
            first_danger,
            *(
                [
                    "STEP33_A1_SUB0_DERIVMODEL_LEAN_ARITHMETIC_EMISSION_GAP",
                ]
                if budget_passes
                else []
            ),
        ],
        "firstDangerPoint": first_danger,
        "proofSafeClosedFields": 0,
        "outLeanWritten": False,
        "routeGuard": [
            "not Lean proof data",
            "does not use sampled derivative intervals as proof",
            "does not prove deriv cert.residual is modeled by this polynomial",
            "does not provide interpolationError",
            "existing derivfit raw coefficients remain diagnostic-only",
            "direct triangle receiver is killed when modelBound exceeds derivSlope",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    derivation = report["derivation"]
    equality = report["rawCoeffEquality"]
    budget = report["directTriangleBudget"]
    lines = [
        "# Step33A.1-A Sub0 Derivative-Model Candidate",
        "",
        "Fail-closed candidate.  This is not Lean proof data.",
        "",
        "## Summary",
        "",
        f"- schema: `{report['schema']}`",
        f"- status: `{report['status']}`",
        f"- first danger point: `{report['firstDangerPoint']}`",
        f"- proof-safe closed fields: `{report['proofSafeClosedFields']}`",
        f"- Lean emitted: `{report['outLeanWritten']}`",
        "",
        "## Raw-Coefficient Equality Check",
        "",
        f"- raw equals residualfit: `{equality['rawEqualsResidualfit']}`",
        f"- raw equals derivfit: `{equality['rawEqualsDerivfit']}`",
        f"- residualfit equals derivfit: `{equality['residualfitEqualsDerivfit']}`",
        f"- meaning: `{equality['meaning']}`",
        "",
        "## Generated Model",
        "",
        f"- formula: `{derivation['formula']}`",
        f"- raw degree: `{derivation['rawDegree']}`",
        f"- model degree: `{derivation['modelDegree']}`",
        f"- model coeff count: `{derivation['modelCoeffCount']}`",
        f"- center: `{derivation['center']}`",
        f"- radius: `{derivation['radius']}`",
        f"- modelBound formula: `{derivation['modelBoundFormula']}`",
        f"- modelBound: `{derivation['modelBound']}`",
        f"- modelBound decimal: `{derivation['modelBoundDecimal']}`",
        "",
        "## Direct Triangle Budget",
        "",
        f"- relation: `{budget['relation']}`",
        f"- modelBound: `{budget['modelBound']}`",
        f"- derivSlope: `{budget['derivSlope']}`",
        f"- margin: `{budget['margin']}`",
        f"- passes: `{budget['passes']}`",
        f"- verdict: `{budget['verdict']}`",
        f"- Lean kill theorem: `{budget['leanKillTheorem']}`",
        "",
        "## Missing Inputs",
        "",
    ]
    for item in report["missingInputs"]:
        lines.append(f"- `{item}`")
    lines.extend(["", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    report = build_report()
    DEFAULT_OUT_JSON.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    DEFAULT_OUT_MD.write_text(render_md(report), encoding="utf-8")
    print(
        "status={status} firstDangerPoint={first} modelBound={bound} out_json={out}".format(
            status=report["status"],
            first=report["firstDangerPoint"],
            bound=report["derivation"]["modelBound"],
            out=DEFAULT_OUT_JSON,
        )
    )


if __name__ == "__main__":
    run()
