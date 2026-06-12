#!/usr/bin/env python3
"""Seed a direct residual-derivative overlay for the pilot route.

This is the route-B landing artifact for the active Step33A.1-A blocker.  The
v7 derivative audit says the sampled residual derivative interval is feasible,
while interval-Arb residual-jet second-derivative enclosures destroy the
cancellation.  The active compact route now records the cell-slope receiver:

    ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData

The older lower/upper interval receiver is retained as legacy diagnostic
support.  This output is not Lean proof data.  It seeds only rational
arithmetic and geometry fields, plus the checked structural residual
differentiability theorem.  It leaves direct residual-anchor and derivative-cell
analytic facts open.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_DERIVATIVE_AUDIT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0.json"
)
DEFAULT_CANDIDATE_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0.md"
)

DERIVATIVE_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7"
)
CANDIDATE_OVERLAY_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"
)
DIRECT_OVERLAY_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.v30"
)

CELL_SLOPE_EXACT_INTEGRAL_PROOF_DATA = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData"
)

CELL_SLOPE_DIRECT_ENDPOINT_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance"
)

RAW_CENTER_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_raw_center_coeff_abs_direct_norm_cert_full_cell"
)

RAW_CENTER_DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell"
)

ENDPOINT_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance"
)

LEGACY_INTERVAL_EXACT_INTEGRAL_PROOF_DATA = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData"
)

CELL_SLOPE_REFINED_PAYLOAD_FIN = (
    "RawOmegaAChunkTaylorPayload.CellSlopeDirectEnvelopeRefinedPayloadFin"
)

REFINED_PAYLOAD_FIN = "RawOmegaAChunkTaylorPayload.RefinedPayloadFin"

SEEDED_FIELDS = [
    "coeff",
    "remainder",
    "sampleRadius",
    "mesh",
    "anchor",
    "cellL",
    "cellU",
    "derivLower",
    "derivUpper",
    "derivCellCount",
    "derivCellLeft",
    "derivCellRight",
    "derivSlope",
    "hAnchorIn",
    "hLeftMesh",
    "hRightMesh",
    "hDerivCoverCell",
    "hDerivCoverCells",
    "hResidualDifferentiable",
]

PREFERRED_REMAINING_ANALYTIC_FIELDS = [
    "hRawCenterCoeffAbs",
    "hResidualDerivBoundOnCell",
]

LEGACY_INTERVAL_REMAINING_ANALYTIC_FIELDS = [
    "hRawCenterCoeffAbs",
    "hResidualDerivLowerOnCell",
    "hResidualDerivUpperOnCell",
]

REMAINING_ANALYTIC_FIELDS = PREFERRED_REMAINING_ANALYTIC_FIELDS

CLOSED_ARITHMETIC_FIELDS = [
    "hEnvelope",
]

LEGACY_INTERVAL_CLOSED_ARITHMETIC_FIELDS = [
    "hDerivLowerAbs",
    "hDerivUpperAbs",
]


def anchor_residual_arithmetic_contract() -> dict[str, Any]:
    direct_raw_center_coeff_abs_bounds = 1
    signed_omega_majorant_bounds = 2
    shape_sq_upper_bounds = 1
    scale_box_comparisons = 3
    majorant_nonneg_comparisons = 2
    raw_scale_abs_comparisons = 2
    center_coeff_comparisons = 3
    residual_radius_comparisons = 2
    legacy_scale_abs_box_obligations = (
        signed_omega_majorant_bounds
        + shape_sq_upper_bounds
        + scale_box_comparisons
        + majorant_nonneg_comparisons
        + raw_scale_abs_comparisons
        + center_coeff_comparisons
        + residual_radius_comparisons
    )
    return {
        "directRawCenterCoeffAbsBounds": direct_raw_center_coeff_abs_bounds,
        "openAnchorAnalyticObligations": direct_raw_center_coeff_abs_bounds,
        "signedOmegaMajorantBounds": signed_omega_majorant_bounds,
        "shapeSqUpperBounds": shape_sq_upper_bounds,
        "scaleBoxComparisons": scale_box_comparisons,
        "majorantNonnegComparisons": majorant_nonneg_comparisons,
        "rawScaleAbsComparisons": raw_scale_abs_comparisons,
        "centerCoeffComparisons": center_coeff_comparisons,
        "residualRadiusComparisons": residual_radius_comparisons,
        "legacyScaleAbsBoxObligations": legacy_scale_abs_box_obligations,
        "totalAnchorResidualArithmeticObligations": direct_raw_center_coeff_abs_bounds,
        "preferredReceiver": (
            "RawOmegaATaylorModelCertificate."
            "anchor_residual_abs_of_raw_center_coeff_abs_bound"
        ),
        "legacyScaleAbsBoxReceiver": (
            "RawOmegaATaylorModelCertificate."
            "anchor_residual_abs_of_scale_abs_box_component_bounds_at_center"
        ),
        "directEnvelopeReceiver": (
            "RawOmegaATaylorModelCertificate."
            "direct_envelope_of_single_cell_residual_bound"
        ),
        "sampleEnvelopeProofData": (
            "RawOmegaATaylorModelCertificate."
            "ResidualAnchorDerivativeSingleCellIntervalSampleEnvelopeFiniteCoverData"
        ),
        "rawCenterCoeffSampleEnvelopeProofData": (
            "RawOmegaATaylorModelCertificate."
            "ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData"
        ),
        "rawIntegrandReceiver": (
            "rawOmegaAIntegrand_value_bounds_at_of_scale_abs_box_bounds"
        ),
        "inactiveReceiverReason": (
            "nonnegative abs-cos route is not active because the first "
            "raw-Omega finite chunk crosses the negative Omega region"
        ),
        "legacyScaleAbsBoxReason": (
            "the scale-abs component box remains compiled support, but it is "
            "too coarse for the tiny anchor residual radius; the active "
            "generator target is the sharp raw-center-minus-coeff0 bound"
        ),
    }


def derivative_arithmetic_contract(coeff: list[Any], deriv_cell_count: int) -> dict[str, Any]:
    degree = len(coeff) - 1
    term_count = len(coeff)
    direct_residual_derivative_bounds = 2 * deriv_cell_count
    residual_derivative_abs_comparisons = 2 * deriv_cell_count
    total = direct_residual_derivative_bounds + residual_derivative_abs_comparisons
    return {
        "degree": degree,
        "termCount": term_count,
        "derivCellCount": deriv_cell_count,
        "directResidualDerivativeBounds": direct_residual_derivative_bounds,
        "residualDerivativeAbsComparisons": residual_derivative_abs_comparisons,
        "preferredDirectResidualDerivativeNormBounds": deriv_cell_count,
        "preferredOpenDerivativeAnalyticObligations": deriv_cell_count,
        "openDerivativeAnalyticObligations": direct_residual_derivative_bounds,
        "closedDerivativeAbsComparisons": residual_derivative_abs_comparisons,
        "totalDerivativeArithmeticObligations": total,
        "preferredProofData": CELL_SLOPE_EXACT_INTEGRAL_PROOF_DATA,
        "preferredDirectEndpointConstructor": CELL_SLOPE_DIRECT_ENDPOINT_CONSTRUCTOR,
        "preferredFullCellDirectNormConstructor": (
            RAW_CENTER_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR
        ),
        "preferredFullCellDirectNormIntervalBoundsConstructor": (
            RAW_CENTER_DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR
        ),
        "endpointFullCellDirectNormFallbackConstructor": (
            ENDPOINT_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR
        ),
        "preferredNormReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_single_cell_of_interval_bounds"
            if deriv_cell_count == 1
            else "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_cells_of_interval_bounds"
        ),
        "preferredReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_single_cell_of_interval_bounds"
            if deriv_cell_count == 1
            else "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_cells_of_interval_bounds"
        ),
        "singleCellReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_single_cell_of_interval_bounds"
        ),
        "cellIndexedReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_cells_of_interval_bounds"
        ),
        "legacyRawPolySingleCellReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_single_cell_of_raw_deriv_and_poly_term_expr_bounds"
        ),
        "legacyRawPolyCellIndexedReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_cells_of_raw_deriv_and_poly_term_expr_bounds"
        ),
        "legacyRawPolyIntervalReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_interval_bounds_on_cells_of_raw_deriv_and_poly_term_expr_bounds"
        ),
        "receiverReason": (
            "current one-cell raw/poly derivative intervals lose cancellation; "
            "proof data must instead provide cancellation-preserving bounds for "
            "deriv cert.residual directly"
        ),
    }


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_derivative_audit(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != DERIVATIVE_AUDIT_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def validate_candidate_overlay(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != CANDIDATE_OVERLAY_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def candidate_by_subchunk(candidate_overlay: dict[str, Any]) -> dict[int, dict[str, Any]]:
    rows = candidate_overlay.get("candidates", [])
    if not isinstance(rows, list):
        raise ValueError("candidate overlay has no candidates array")
    candidates: dict[int, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("candidate overlay contains a malformed candidate")
        subchunk = int(row["subchunk"])
        if subchunk in candidates:
            raise ValueError(f"duplicate candidate for subchunk {subchunk}")
        candidates[subchunk] = row
    return candidates


def singleton_cell(row: dict[str, Any]) -> dict[str, Any]:
    cells = row.get("derivativeIntervalFiniteCoverCells")
    if not isinstance(cells, list) or len(cells) != 1:
        raise ValueError(
            f"subchunk {row.get('subchunk')}: expected exactly one direct cell"
        )
    cell = cells[0]
    if not isinstance(cell, dict):
        raise ValueError(f"subchunk {row.get('subchunk')}: malformed cell")
    return cell


def parse_fraction(value: Any, *, field: str) -> Fraction:
    if value is None:
        raise ValueError(f"missing rational field {field}")
    try:
        return Fraction(str(value))
    except Exception as exc:  # pragma: no cover - diagnostic guard
        raise ValueError(f"invalid rational field {field}: {value!r}") from exc


def fraction_json(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def sample_envelope_arithmetic(seed: dict[str, Any]) -> dict[str, Any]:
    sample_radius = parse_fraction(seed.get("sampleRadius"), field="sampleRadius")
    mesh = parse_fraction(seed.get("mesh"), field="mesh")
    remainder = parse_fraction(seed.get("remainder"), field="remainder")
    deriv_slope_raw = seed.get("derivSlope")
    if not isinstance(deriv_slope_raw, list) or len(deriv_slope_raw) != 1:
        raise ValueError("expected exactly one derivSlope value")
    deriv_slope = parse_fraction(deriv_slope_raw[0], field="derivSlope[0]")
    max_slope = max(Fraction(0), deriv_slope)
    lhs = sample_radius + max_slope * mesh
    excess = lhs - remainder
    return {
        "targetField": "hEnvelope",
        "relation": "sampleRadius + max 0 derivSlope * mesh <= remainder",
        "sampleRadius": fraction_json(sample_radius),
        "mesh": fraction_json(mesh),
        "derivSlope": fraction_json(deriv_slope),
        "maxSlope": fraction_json(max_slope),
        "remainder": fraction_json(remainder),
        "lhs": fraction_json(lhs),
        "excess": fraction_json(excess),
        "passes": lhs <= remainder,
        "derivSlopeNonneg": deriv_slope >= 0,
        "proofHint": "by norm_num",
    }


def derivative_abs_arithmetic(seed: dict[str, Any]) -> dict[str, Any]:
    deriv_lower = parse_fraction(seed.get("derivLower"), field="derivLower")
    deriv_upper = parse_fraction(seed.get("derivUpper"), field="derivUpper")
    deriv_slope_raw = seed.get("derivSlope")
    if not isinstance(deriv_slope_raw, list) or len(deriv_slope_raw) != 1:
        raise ValueError("expected exactly one derivSlope value")
    deriv_slope = parse_fraction(deriv_slope_raw[0], field="derivSlope[0]")
    lower_excess = (-deriv_slope) - deriv_lower
    upper_excess = deriv_upper - deriv_slope
    lower_passes = -deriv_slope <= deriv_lower
    upper_passes = deriv_upper <= deriv_slope
    return {
        "targetFields": ["hDerivLowerAbs", "hDerivUpperAbs"],
        "lowerRelation": "-derivSlope <= derivLower",
        "upperRelation": "derivUpper <= derivSlope",
        "derivLower": fraction_json(deriv_lower),
        "derivUpper": fraction_json(deriv_upper),
        "derivSlope": fraction_json(deriv_slope),
        "lowerExcess": fraction_json(lower_excess),
        "upperExcess": fraction_json(upper_excess),
        "lowerPasses": lower_passes,
        "upperPasses": upper_passes,
        "passes": lower_passes and upper_passes,
        "proofHint": "by norm_num",
    }


def build_subchunk(row: dict[str, Any], candidate: dict[str, Any]) -> dict[str, Any]:
    cell = singleton_cell(row)
    subchunk = int(row["subchunk"])
    if int(candidate.get("subchunk")) != subchunk:
        raise ValueError(
            f"subchunk {subchunk}: candidate subchunk mismatch "
            f"{candidate.get('subchunk')!r}"
        )
    if not row.get("sampledEnvelopePasses"):
        raise ValueError(f"subchunk {row.get('subchunk')}: sampled envelope fails")
    coeff = candidate.get("coeff")
    if not isinstance(coeff, list) or not coeff:
        raise ValueError(f"subchunk {row.get('subchunk')}: missing coeff candidate")
    deriv_cell_count = 1

    seeded = {
        "coeff": coeff,
        "remainder": row["currentRemainder"],
        "sampleRadius": row["sampleRadius"],
        "mesh": row["meshCandidate"],
        "anchor": row["center"],
        "cellL": cell["left"],
        "cellU": cell["right"],
        "derivLower": cell["derivLower"],
        "derivUpper": cell["derivUpper"],
        "derivCellCount": deriv_cell_count,
        "derivCellLeft": [cell["left"]],
        "derivCellRight": [cell["right"]],
        "derivSlope": [row["sampledSlope"]],
        "hAnchorIn": "by norm_num [Set.mem_Ioc]",
        "hLeftMesh": "by norm_num",
        "hRightMesh": "by norm_num",
        "hDerivCoverCell": "by intro eta heta; simpa using heta",
        "hDerivCoverCells": (
            "by intro eta heta; exact <| Exists.intro 0 (by simpa using heta)"
        ),
        "hResidualDifferentiable": (
            "by intro eta heta; exact "
            "RawOmegaATaylorModelCertificate.residual_differentiableAt _ eta"
        ),
    }
    envelope_arithmetic = sample_envelope_arithmetic(seeded)
    if not envelope_arithmetic["passes"]:
        raise ValueError(
            f"subchunk {subchunk}: exact sample-envelope arithmetic fails"
        )
    deriv_abs_arithmetic = derivative_abs_arithmetic(seeded)
    if not deriv_abs_arithmetic["passes"]:
        raise ValueError(
            f"subchunk {subchunk}: exact derivative abs arithmetic fails"
        )
    residual_derivative_interval_candidates = [
        {
            "cell": cell.get("cell", 0),
            "left": cell["left"],
            "right": cell["right"],
            "derivLower": cell["derivLower"],
            "derivUpper": cell["derivUpper"],
            "hDerivLowerAbsWouldPass": cell.get("hDerivLowerAbsWouldPass"),
            "hDerivUpperAbsWouldPass": cell.get("hDerivUpperAbsWouldPass"),
            "proofStatus": cell.get("proofStatus"),
        }
    ]
    return {
        "subchunk": subchunk,
        "left": row["left"],
        "right": row["right"],
        "center": row["center"],
        "candidateSource": "derivative_bound_audit.v7.sampled_direct_interval",
        "subchunkProofShape": CELL_SLOPE_EXACT_INTEGRAL_PROOF_DATA,
        "legacyIntervalSubchunkProofShape": LEGACY_INTERVAL_EXACT_INTEGRAL_PROOF_DATA,
        "seededFields": seeded,
        "seededFieldNames": SEEDED_FIELDS,
        "residualDerivativeIntervalCandidates": (
            residual_derivative_interval_candidates
        ),
        "remainingAnalyticFields": REMAINING_ANALYTIC_FIELDS,
        "legacyIntervalRemainingAnalyticFields": (
            LEGACY_INTERVAL_REMAINING_ANALYTIC_FIELDS
        ),
        "closedArithmeticFields": CLOSED_ARITHMETIC_FIELDS,
        "legacyIntervalClosedArithmeticFields": (
            LEGACY_INTERVAL_CLOSED_ARITHMETIC_FIELDS
        ),
        "hEnvelopeArithmetic": envelope_arithmetic,
        "hResidualDerivAbsArithmetic": deriv_abs_arithmetic,
        "hAnchorResidualReceiver": (
            "RawOmegaATaylorModelCertificate."
            "anchor_residual_abs_of_raw_center_coeff_abs_bound"
        ),
        "hAnchorResidualAbsCosReceiver": (
            "RawOmegaATaylorModelCertificate."
            "anchor_residual_abs_of_nonneg_abs_cos_component_bounds_at_center"
        ),
        "hRawOmegaAtAbsCosReceiver": (
            "rawOmegaAIntegrand_value_bounds_at_of_nonneg_abs_cos_component_bounds"
        ),
        "hAnchorResidualScaleAbsBoxReceiver": (
            "RawOmegaATaylorModelCertificate."
            "anchor_residual_abs_of_scale_abs_box_component_bounds_at_center"
        ),
        "hRawOmegaAtScaleAbsBoxReceiver": (
            "rawOmegaAIntegrand_value_bounds_at_of_scale_abs_box_bounds"
        ),
        "hAnchorResidualRawPolyReceiver": (
            "RawOmegaATaylorModelCertificate."
            "anchor_residual_abs_of_raw_poly_value_bounds_at"
        ),
        "hAnchorPolynomialCenterReceiver": (
            "RawOmegaATaylorModelCertificate.polynomial_center"
        ),
        "hDirectEnvelopeSingleCellReceiver": (
            "RawOmegaATaylorModelCertificate."
            "direct_envelope_of_single_cell_residual_bound"
        ),
        "hResidualDerivEqReceiver": (
            "RawOmegaATaylorModelCertificate.residual_deriv_eq"
        ),
        "hResidualDerivCellRawPolyReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_interval_bounds_on_cell_of_raw_poly_deriv_bounds"
        ),
        "hResidualDerivCellCompositeReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_bounds"
        ),
        "hResidualDerivCellExprCompositeReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_interval_bounds_on_cell_of_raw_deriv_and_poly_term_expr_bounds"
        ),
        "hResidualDerivCellsExprCompositeReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_interval_bounds_on_cells_of_raw_deriv_and_poly_term_expr_bounds"
        ),
        "hResidualDerivSingleCellNormReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_single_cell_of_raw_deriv_and_poly_term_expr_bounds"
        ),
        "hResidualDerivSingleCellIntervalNormReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_single_cell_of_interval_bounds"
        ),
        "hResidualDerivCellsIntervalNormReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_cells_of_interval_bounds"
        ),
        "hPolynomialDerivEqReceiver": (
            "RawOmegaATaylorModelCertificate.polynomial_deriv_eq_term_deriv_sum"
        ),
        "hPolynomialTermDerivEqReceiver": (
            "RawOmegaATaylorModelCertificate.polynomial_term_deriv_eq"
        ),
        "hPolynomialDerivCellTermReceiver": (
            "RawOmegaATaylorModelCertificate."
            "polynomial_deriv_bounds_on_cell_of_term_deriv_bounds"
        ),
        "hPolynomialDerivCellExprReceiver": (
            "RawOmegaATaylorModelCertificate."
            "polynomial_derivative_term_bounds_on_cell_of_expr_bounds"
        ),
        "hAnchorResidualNextInputs": [
            "anchor = cert.center",
            "prove sharp bound |step22PositiveAxisOmegaAIntegrand k ell x anchor - cert.coeff 0| <= sampleRadius",
            "payload field hRawCenterCoeffAbs feeds the sharp-anchor sample-envelope wrapper",
        ],
        "hAnchorResidualLegacyScaleAbsBoxInputs": [
            "-omegaMajorant <= step22OmegaArchWeight anchor",
            "step22OmegaArchWeight anchor <= omegaMajorant",
            "centeredBSplineImagTransformRealClosedForm k ell anchor ^ 2 <= shapeSqUpper",
            "0 <= ell / pi",
            "ell / pi <= scaleUpper",
            "0 <= scaleUpper",
            "0 <= omegaMajorant",
            "0 <= shapeSqUpper",
            "rawLower <= -(scaleUpper * omegaMajorant * shapeSqUpper)",
            "scaleUpper * omegaMajorant * shapeSqUpper <= rawUpper",
            "anchor = cert.center",
            "polyLower <= cert.coeff 0",
            "cert.coeff 0 <= polyUpper",
            "-sampleRadius <= rawLower - polyUpper",
            "rawUpper - polyLower <= sampleRadius",
        ],
        "hEnvelopeNextInputs": [
            "prove sharp anchor raw-center-minus-coeff0 bound",
            "Lean wrapper packages hRawCenterCoeffAbs into hAnchorResidual: |cert.residual anchor| <= sampleRadius",
            "prove scalar direct envelope: sampleRadius + max 0 derivSlope[0] * mesh <= cert.remainder",
            "sample-envelope wrapper packages the direct envelope required by the one-cell receiver",
        ],
        "hResidualDerivCellNextInputs": [
            "legacy interval route only; prefer hResidualDerivBoundOnCell when possible",
            "prove cancellation-preserving derivLower i <= deriv cert.residual eta on cell i",
            "prove cancellation-preserving deriv cert.residual eta <= derivUpper i on cell i",
            "-derivSlope i <= derivLower i",
            "derivUpper i <= derivSlope i",
            "package ‖deriv cert.residual eta‖ <= derivSlope i",
            "legacy interval receiver for one-cell direct subchunks: residual_deriv_bound_on_single_cell_of_interval_bounds",
            "do not use raw/poly derivative subtraction here; feasibility audit reports 0/110 passing",
        ],
            "hResidualDerivNormNextInputs": [
                "prove cancellation-preserving norm bound ‖deriv cert.residual eta‖ <= derivSlope[0] on the one derivative cell",
                "preferred: feed hRawCenterCoeffAbs + ResidualDerivativeDirectNormCert.Valid + cellL=L/cellU=U into ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell",
                "shortcut: feed hRawCenterCoeffAbs + residual-derivative lower/upper bounds + abs-slope comparisons into ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell",
                "fallback: feed hResidualDerivBoundOnCell into ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance",
                "do not emit derivLower/derivUpper interval fields when the norm proof is available",
            ],
        "hResidualDerivCellsNextInputs": [
            "for derivCellCount = 1, prefer the scalar cell-slope proof-data route",
            "cell-indexed direct residual-derivative lower/upper bounds",
            "cell-indexed -derivSlope <= derivLower and derivUpper <= derivSlope comparisons",
            "legacy fallback receiver: residual_deriv_bound_on_cells_of_interval_bounds",
        ],
        "routeBDerivativeArithmeticContract": derivative_arithmetic_contract(
            coeff, deriv_cell_count
        ),
        "routeBAnchorResidualArithmeticContract": (
            anchor_residual_arithmetic_contract()
        ),
        "blockedOn": [
            "hRawCenterCoeffAbs",
            "hResidualDerivBoundOnCell",
        ],
        "legacyIntervalBlockedOn": [
            "hRawCenterCoeffAbs",
            "hResidualDerivLowerOnCell",
            "hResidualDerivUpperOnCell",
        ],
        "sampledEnvelopeExcess": row.get("sampledEnvelopeExcess"),
        "integralLowerCandidate": candidate.get("integralLower"),
        "integralUpperCandidate": candidate.get("integralUpper"),
        "proofStatus": "sampled_direct_interval_candidates_not_lean_proved",
    }


def build_overlay(
    audit: dict[str, Any],
    audit_path: Path,
    candidate_overlay: dict[str, Any],
    candidate_overlay_path: Path,
) -> dict[str, Any]:
    rows = audit.get("subchunks")
    if not isinstance(rows, list):
        raise ValueError("derivative audit has no subchunks array")
    candidates = candidate_by_subchunk(candidate_overlay)
    subchunks = []
    for row in rows:
        subchunk = int(row["subchunk"])
        if subchunk not in candidates:
            raise ValueError(f"missing candidate overlay row for subchunk {subchunk}")
        subchunks.append(build_subchunk(row, candidates[subchunk]))
    totals = {
        "subchunks": len(subchunks),
        "seededFieldsPerSubchunk": len(SEEDED_FIELDS),
        "seededFields": len(subchunks) * len(SEEDED_FIELDS),
        "remainingAnalyticFieldsPerSubchunk": len(REMAINING_ANALYTIC_FIELDS),
        "remainingAnalyticFields": len(subchunks)
        * len(REMAINING_ANALYTIC_FIELDS),
        "legacyIntervalRemainingAnalyticFieldsPerSubchunk": len(
            LEGACY_INTERVAL_REMAINING_ANALYTIC_FIELDS
        ),
        "legacyIntervalRemainingAnalyticFields": len(subchunks)
        * len(LEGACY_INTERVAL_REMAINING_ANALYTIC_FIELDS),
        "closedArithmeticFieldsPerSubchunk": len(CLOSED_ARITHMETIC_FIELDS),
        "closedArithmeticFields": len(subchunks) * len(CLOSED_ARITHMETIC_FIELDS),
        "legacyIntervalClosedArithmeticFieldsPerSubchunk": len(
            LEGACY_INTERVAL_CLOSED_ARITHMETIC_FIELDS
        ),
        "legacyIntervalClosedArithmeticFields": len(subchunks)
        * len(LEGACY_INTERVAL_CLOSED_ARITHMETIC_FIELDS),
        "sampleEnvelopeArithmeticObligations": len(subchunks),
        "sampleEnvelopeArithmeticPassing": sum(
            1 for row in subchunks if row["hEnvelopeArithmetic"]["passes"]
        ),
        "derivativeAbsArithmeticObligations": 2 * len(subchunks),
        "derivativeAbsArithmeticPassing": sum(
            2
            for row in subchunks
            if row["hResidualDerivAbsArithmetic"]["passes"]
        ),
        "routeBAnchorResidualArithmeticObligations": sum(
            int(
                row["routeBAnchorResidualArithmeticContract"][
                    "totalAnchorResidualArithmeticObligations"
                ]
            )
            for row in subchunks
        ),
        "routeBDerivativeArithmeticObligations": sum(
            int(
                row["routeBDerivativeArithmeticContract"][
                    "openDerivativeAnalyticObligations"
                ]
            )
            for row in subchunks
        ),
        "preferredNormRouteDerivativeAnalyticObligations": sum(
            int(
                row["routeBDerivativeArithmeticContract"][
                    "preferredOpenDerivativeAnalyticObligations"
                ]
            )
            for row in subchunks
        ),
        "routeBDerivativeTotalComparisonsIncludingClosed": sum(
            int(
                row["routeBDerivativeArithmeticContract"][
                    "totalDerivativeArithmeticObligations"
                ]
            )
            for row in subchunks
        ),
    }
    pilot = audit.get("pilot") or {}
    family = pilot.get("family", "unknown")
    row = pilot.get("row", "unknown")
    parent_chunk = pilot.get("parentChunk", "unknown")
    return {
        "schema": DIRECT_OVERLAY_SCHEMA,
        "status": "direct_derivative_overlay_seeded_missing_cell_slope_norm_proofs",
        "meaning": (
            f"Fail-closed route-B overlay for {family} row {row} parent "
            f"chunk {parent_chunk}.  It uses the sampled direct derivative "
            "candidate from the v7 audit and targets the checked "
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData "
            "receiver.  Lean first converts the sampled residual-radius "
            "envelope to the direct one-cell envelope, feeds one "
            "cancellation-preserving residual-derivative norm bound into the "
            "cell-slope exact-integral receiver, and then folds the subchunk "
            "through the route-A parent receiver.  The lower/upper interval "
            "route remains recorded as legacy diagnostic support.  "
            "It also carries rational coefficient candidates from "
            "the refined candidate overlay, while subchunk integral comparison "
            "proofs are removed by the exact model-integral receiver.  It "
            "uses the checked structural residual differentiability theorem.  "
            "The residual-anchor field now targets the checked sharp "
            "raw-center-minus-coeff0 receiver; the signed scale-abs-box "
            "receiver is retained only as compiled legacy support.  The "
            "active full payload route now emits "
            "RawOmegaAChunkTaylorPayload.CellSlopeDirectEnvelopeRefinedPayloadFin "
            "and then Lean converts it to RawOmegaAChunkTaylorPayload.RefinedPayloadFin.  "
            "The first raw-Omega finite chunk crosses the negative Omega "
            "region, so the nonnegative abs-cos route is retained only as "
            "inactive support.  The required sharp raw-center-minus-coeff0 "
            "bounds at the anchor are still open generated proof inputs.  "
            "The scalar sample-envelope inequality is checked here by exact "
            "rational arithmetic and remains a future Lean `by norm_num` field, "
            "not an analytic blocker.  The derivative abs comparisons "
            "`-derivSlope <= derivLower` and `derivUpper <= derivSlope` are also "
            "checked here by exact rational arithmetic.  "
            "For the pilot, anchor equals the Taylor center, so the "
            "polynomial anchor value reduces to cert.coeff 0 by "
            "RawOmegaATaylorModelCertificate.polynomial_center.  "
            "It is not Lean proof data: raw-center-coeff and derivative-cell "
            "analytic facts remain open."
        ),
        "sourceDerivativeAudit": str(audit_path),
        "sourceDerivativeAuditStatus": audit.get("status"),
        "sourceCandidateOverlay": str(candidate_overlay_path),
        "sourceCandidateOverlayStatus": candidate_overlay.get("status"),
        "pilot": pilot,
        "leanLandingSurface": CELL_SLOPE_REFINED_PAYLOAD_FIN,
        "downstreamLeanLandingSurface": REFINED_PAYLOAD_FIN,
        "activeSubchunkProofData": CELL_SLOPE_EXACT_INTEGRAL_PROOF_DATA,
        "preferredCellSlopeSubchunkProofData": CELL_SLOPE_EXACT_INTEGRAL_PROOF_DATA,
        "preferredCellSlopeDirectEndpointConstructor": (
            CELL_SLOPE_DIRECT_ENDPOINT_CONSTRUCTOR
        ),
        "preferredFullCellDirectNormConstructor": (
            RAW_CENTER_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR
        ),
        "preferredFullCellDirectNormIntervalBoundsConstructor": (
            RAW_CENTER_DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR
        ),
        "endpointFullCellDirectNormFallbackConstructor": (
            ENDPOINT_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR
        ),
        "legacyIntervalSubchunkProofData": LEGACY_INTERVAL_EXACT_INTEGRAL_PROOF_DATA,
        "totals": totals,
        "seededFieldNames": SEEDED_FIELDS,
        "remainingAnalyticFieldNames": REMAINING_ANALYTIC_FIELDS,
        "legacyIntervalRemainingAnalyticFieldNames": (
            LEGACY_INTERVAL_REMAINING_ANALYTIC_FIELDS
        ),
        "closedArithmeticFieldNames": CLOSED_ARITHMETIC_FIELDS,
        "legacyIntervalClosedArithmeticFieldNames": (
            LEGACY_INTERVAL_CLOSED_ARITHMETIC_FIELDS
        ),
        "subchunks": subchunks,
        "routeGuard": [
            "not Lean proof data",
            "do not emit PayloadFin from this overlay alone",
            "sampled derivative lower/upper values are candidates only",
            "coefficients are rational candidates only until Lean emission checks them",
            "subchunk integral comparisons are eliminated by exact model integral bounds",
            "slope/hSlopeNonneg are eliminated by the scalar one-cell interval wrapper",
            "sampleRadius is seeded; scalar hEnvelope arithmetic passes exactly but is not Lean payload yet",
            "hRawCenterCoeffAbs remains an analytic proof field",
            "derivLower/derivUpper are scalar candidate direct residual-derivative interval endpoints, not raw/poly subtraction outputs",
            "hDerivLowerAbs/hDerivUpperAbs pass exact rational arithmetic but belong to the legacy interval route",
            "preferred route must prove hResidualDerivBoundOnCell by a cancellation-preserving residual-derivative norm generator",
            "hResidualDerivLowerOnCell/hResidualDerivUpperOnCell remain legacy interval fields only",
            "hRawCenterCoeffAbs must be proved as the sharp raw-center-minus-coeff0 analytic bound, not by trusting sampled residuals",
            "scale_abs_box anchor receiver is compiled legacy support, not the active full-payload blocker",
            "anchor raw integrand scale_abs_box receiver is compiled legacy support and may be too coarse for tiny residuals",
            "nonnegative abs-cos anchor route is inactive for the first finite chunk because it requires 0 <= omegaLower",
            "polynomial anchor value should use polynomial_center because pilot anchor equals cert.center",
            "preferred route feeds hRawCenterCoeffAbs plus a full-cell direct norm certificate to the compact raw-center exact-integral constructor",
            "shortcut route feeds hRawCenterCoeffAbs plus residual-derivative interval bounds and abs-slope arithmetic to the compact raw-center interval-bounds constructor",
            "hResidualDerivBoundOnCell direct endpoint constructor remains fallback support",
            "legacy cell-indexed fallback receiver is residual_deriv_bound_on_cells_of_interval_bounds",
            "raw/poly derivative norm receivers are retained only as legacy support for better aligned future cells",
            "next Lean work must prove hRawCenterCoeffAbs, materialize scalar hEnvelope arithmetic, and prove cancellation-preserving residual-derivative norm bounds",
            "do not mutate CSV, ARadius, radius-floor, or LDL data",
            "do not route to H1/PO3 or Q3.Main from this layer",
        ],
    }


def render_md(overlay: dict[str, Any]) -> str:
    totals = overlay["totals"]
    pilot = overlay.get("pilot") or {}
    lines = [
        "# Step33A.1-A Direct Derivative Overlay",
        "",
        (
            "Fail-closed route-B pilot overlay for "
            f"`{pilot.get('family')}` row {pilot.get('row')} "
            f"parent chunk {pilot.get('parentChunk')}`, with cell-slope as "
            "the active derivative route."
        ),
        "",
        "## Verdict",
        "",
        f"- schema: `{overlay['schema']}`",
        f"- status: `{overlay['status']}`",
        f"- source audit status: `{overlay['sourceDerivativeAuditStatus']}`",
        f"- Lean landing surface: `{overlay['leanLandingSurface']}`",
        f"- active subchunk proof data: `{overlay['activeSubchunkProofData']}`",
        f"- legacy interval subchunk proof data: `{overlay.get('legacyIntervalSubchunkProofData')}`",
        f"- preferred direct-endpoint constructor: `{overlay.get('preferredCellSlopeDirectEndpointConstructor')}`",
        f"- preferred full-cell direct-norm constructor: `{overlay.get('preferredFullCellDirectNormConstructor')}`",
        f"- preferred full-cell direct-norm interval-bounds constructor: `{overlay.get('preferredFullCellDirectNormIntervalBoundsConstructor')}`",
        f"- endpoint full-cell direct-norm fallback: `{overlay.get('endpointFullCellDirectNormFallbackConstructor')}`",
        f"- subchunks: `{totals['subchunks']}`",
        f"- seeded fields: `{totals['seededFields']}`",
        f"- remaining analytic fields: `{totals['remainingAnalyticFields']}`",
        f"- legacy interval remaining analytic fields: `{totals['legacyIntervalRemainingAnalyticFields']}`",
        f"- closed arithmetic fields: `{totals['closedArithmeticFields']}`",
        f"- legacy interval closed arithmetic fields: `{totals['legacyIntervalClosedArithmeticFields']}`",
        f"- sample-envelope arithmetic obligations: `{totals['sampleEnvelopeArithmeticObligations']}`",
        f"- sample-envelope arithmetic passing: `{totals['sampleEnvelopeArithmeticPassing']}`",
        f"- derivative abs arithmetic obligations: `{totals['derivativeAbsArithmeticObligations']}`",
        f"- derivative abs arithmetic passing: `{totals['derivativeAbsArithmeticPassing']}`",
        f"- route-B anchor residual arithmetic obligations: `{totals['routeBAnchorResidualArithmeticObligations']}`",
        f"- route-B derivative arithmetic obligations: `{totals['routeBDerivativeArithmeticObligations']}`",
        f"- preferred norm-route derivative analytic obligations: `{totals['preferredNormRouteDerivativeAnalyticObligations']}`",
        f"- route-B derivative comparisons including closed: `{totals['routeBDerivativeTotalComparisonsIncludingClosed']}`",
        "",
        "## Seeded Fields",
        "",
    ]
    for field in overlay["seededFieldNames"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "## Still Missing Per Subchunk", ""])
    for field in overlay["remainingAnalyticFieldNames"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "## Exact Arithmetic Fields", ""])
    for field in overlay["closedArithmeticFieldNames"]:
        lines.append(f"- `{field}`")
    lines.extend(
        [
            "",
            "## hRawCenterCoeffAbs Receiver",
            "",
            f"- preferred sharp receiver: `{overlay['subchunks'][0]['hAnchorResidualReceiver']}`",
            f"- signed scale-abs legacy support: `{overlay['subchunks'][0]['hAnchorResidualScaleAbsBoxReceiver']}`",
            f"- raw integrand scale-abs legacy support: `{overlay['subchunks'][0]['hRawOmegaAtScaleAbsBoxReceiver']}`",
            f"- inactive abs-cos support: `{overlay['subchunks'][0]['hAnchorResidualAbsCosReceiver']}`",
            f"- raw/poly packaging: `{overlay['subchunks'][0]['hAnchorResidualRawPolyReceiver']}`",
            f"- polynomial center: `{overlay['subchunks'][0]['hAnchorPolynomialCenterReceiver']}`",
            "",
            "Required generated inputs for hRawCenterCoeffAbs:",
            "",
        ]
    )
    for item in overlay["subchunks"][0]["hAnchorResidualNextInputs"]:
        lines.append(f"- `{item}`")
    env_arith = overlay["subchunks"][0]["hEnvelopeArithmetic"]
    lines.extend(
        [
            "",
            "## Scalar hEnvelope Arithmetic",
            "",
            f"- relation: `{env_arith['relation']}`",
            f"- first-subchunk lhs: `{env_arith['lhs']}`",
            f"- first-subchunk remainder: `{env_arith['remainder']}`",
            f"- first-subchunk excess: `{env_arith['excess']}`",
            f"- exact pass: `{env_arith['passes']}`",
            f"- proof hint: `{env_arith['proofHint']}`",
        ]
    )
    anchor_contract = overlay["subchunks"][0]["routeBAnchorResidualArithmeticContract"]
    lines.extend(
        [
            "",
            "Raw-center-coeff abs arithmetic contract:",
            "",
            f"- direct raw-center-coeff abs bounds: `{anchor_contract['directRawCenterCoeffAbsBounds']}`",
            f"- open anchor analytic obligations: `{anchor_contract['openAnchorAnalyticObligations']}`",
            f"- signed Omega majorant bounds: `{anchor_contract['signedOmegaMajorantBounds']}`",
            f"- shape-square upper bounds: `{anchor_contract['shapeSqUpperBounds']}`",
            f"- scale box comparisons: `{anchor_contract['scaleBoxComparisons']}`",
            f"- majorant nonnegativity comparisons: `{anchor_contract['majorantNonnegComparisons']}`",
            f"- raw scale-abs comparisons: `{anchor_contract['rawScaleAbsComparisons']}`",
            f"- center/coeff comparisons: `{anchor_contract['centerCoeffComparisons']}`",
            f"- residual-radius comparisons: `{anchor_contract['residualRadiusComparisons']}`",
            f"- legacy scale-abs box obligations: `{anchor_contract['legacyScaleAbsBoxObligations']}`",
            f"- total per subchunk: `{anchor_contract['totalAnchorResidualArithmeticObligations']}`",
        ]
    )
    lines.extend(
        [
            "",
            "## hResidualDeriv Cell-Slope Receiver",
            "",
            f"- preferred proof data: `{overlay.get('preferredCellSlopeSubchunkProofData')}`",
            f"- preferred direct-endpoint constructor: `{overlay.get('preferredCellSlopeDirectEndpointConstructor')}`",
            f"- preferred full-cell direct-norm constructor: `{overlay.get('preferredFullCellDirectNormConstructor')}`",
            f"- preferred full-cell direct-norm interval-bounds constructor: `{overlay.get('preferredFullCellDirectNormIntervalBoundsConstructor')}`",
            f"- endpoint full-cell direct-norm fallback: `{overlay.get('endpointFullCellDirectNormFallbackConstructor')}`",
            f"- active single-cell interval norm receiver: `{overlay['subchunks'][0]['hResidualDerivSingleCellIntervalNormReceiver']}`",
            f"- active all-cells interval norm receiver: `{overlay['subchunks'][0]['hResidualDerivCellsIntervalNormReceiver']}`",
            f"- legacy raw/poly single-cell norm receiver: `{overlay['subchunks'][0]['hResidualDerivSingleCellNormReceiver']}`",
            f"- legacy all-cells expr composite: `{overlay['subchunks'][0]['hResidualDerivCellsExprCompositeReceiver']}`",
            "",
            "Required generated inputs:",
            "",
        ]
    )
    for item in overlay["subchunks"][0]["hResidualDerivNormNextInputs"]:
        lines.append(f"- `{item}`")
    contract = overlay["subchunks"][0]["routeBDerivativeArithmeticContract"]
    deriv_abs = overlay["subchunks"][0]["hResidualDerivAbsArithmetic"]
    lines.extend(
        [
            "",
            "Cell-slope arithmetic contract:",
            "",
            f"- degree: `{contract['degree']}`",
            f"- term count: `{contract['termCount']}`",
            f"- derivative cells: `{contract['derivCellCount']}`",
            f"- preferred direct residual derivative norm bounds: `{contract['preferredDirectResidualDerivativeNormBounds']}`",
            f"- preferred open derivative analytic obligations: `{contract['preferredOpenDerivativeAnalyticObligations']}`",
            f"- legacy direct residual derivative bounds: `{contract['directResidualDerivativeBounds']}`",
            f"- legacy residual derivative abs comparisons: `{contract['residualDerivativeAbsComparisons']}`",
            f"- legacy open derivative analytic obligations: `{contract['openDerivativeAnalyticObligations']}`",
            f"- closed derivative abs comparisons: `{contract['closedDerivativeAbsComparisons']}`",
            f"- total per subchunk: `{contract['totalDerivativeArithmeticObligations']}`",
            "",
            "Legacy derivative abs arithmetic:",
            "",
            f"- lower relation: `{deriv_abs['lowerRelation']}`",
            f"- upper relation: `{deriv_abs['upperRelation']}`",
            f"- lower exact pass: `{deriv_abs['lowerPasses']}`",
            f"- upper exact pass: `{deriv_abs['upperPasses']}`",
        ]
    )
    lines.extend(
        [
            "",
            "## Exact Next Lean Target",
            "",
            "- `hRawCenterCoeffAbs` via sharp raw-center-minus-coeff0 anchor bound; Lean wrapper derives `hAnchorResidual`",
            "- `hResidualDerivBoundOnCell` via a cancellation-preserving direct residual-derivative norm bound",
            "- shortcut: `hRawCenterCoeffAbs` plus derivative interval bounds can now land through `of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell`",
            "- materialize exact scalar arithmetic for `hEnvelope` during payload emission",
            "- legacy interval route may still materialize `hResidualDerivLowerOnCell`, `hResidualDerivUpperOnCell`, `hDerivLowerAbs`, and `hDerivUpperAbs` if the preferred norm route fails",
            "",
            "## Guard",
            "",
        ]
    )
    for item in overlay["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--derivative-audit", type=Path, default=DEFAULT_DERIVATIVE_AUDIT
    )
    parser.add_argument(
        "--candidate-overlay", type=Path, default=DEFAULT_CANDIDATE_OVERLAY
    )
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    audit = load_json(args.derivative_audit)
    validate_derivative_audit(audit, args.derivative_audit)
    candidate_overlay = load_json(args.candidate_overlay)
    validate_candidate_overlay(candidate_overlay, args.candidate_overlay)
    overlay = build_overlay(
        audit,
        args.derivative_audit,
        candidate_overlay,
        args.candidate_overlay,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(overlay, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(overlay), encoding="utf-8")

    totals = overlay["totals"]
    print(
        "status={status} subchunks={subchunks} seeded_fields={seeded} "
        "remaining_analytic_fields={remaining}".format(
            status=overlay["status"],
            subchunks=totals["subchunks"],
            seeded=totals["seededFields"],
            remaining=totals["remainingAnalyticFields"],
        )
    )


if __name__ == "__main__":
    run()
