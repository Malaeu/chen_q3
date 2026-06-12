#!/usr/bin/env python3
"""Guarded Lean emitter report for refined raw-Omega subchunk payloads.

This is the fail-closed front door for the future generated Lean import:

    refined proof-data skeleton
    -> RawOmegaAChunkTaylorPayload.RefinedPayloadFin
    -> RawOmegaADirectTailWindowInputs

For now it only writes an emitter report.  It refuses to create a Lean file
while any analytic field or parent fold comparison is missing.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_PROOF_DATA = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.json"
)
DEFAULT_COVERAGE = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_coverage.json"
)
DEFAULT_DIRECT_DERIVATIVE_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0.json"
)
DEFAULT_LOCAL_COMPONENT_INTERVAL_PROBE = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_local_component_interval_probe.json"
)
DEFAULT_HRAW_CENTER_COEFF_CONTRACT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_hraw_center_coeff_contract.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_lean_emitter.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_lean_emitter.md"
)
DEFAULT_OUT_LEAN = (
    ROOT / "Q3/Proofs/PSD_CenteredCoeffRawOmegaARefinedSubchunkGeneratedPayloadImport.lean"
)

PROOF_DATA_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_proof_data.v17"
DIRECT_COVERAGE_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_coverage.v1"
DIRECT_DERIVATIVE_OVERLAY_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.v27"
)
LOCAL_COMPONENT_INTERVAL_PROBE_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_local_component_interval_probe.v2"
)
HRAW_CENTER_COEFF_CONTRACT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_hraw_center_coeff_contract.v11"
)
EMITTER_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_payload_lean_emitter.v37"

PREFERRED_CELL_SLOPE_SUBCHUNK_PROOF_DATA = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData"
)

PREFERRED_CELL_SLOPE_DIRECT_ENDPOINT_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance"
)

PREFERRED_DIRECT_NORM_CERT_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance"
)

GENERIC_DIRECT_NORM_CERT_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_direct_norm_cert_at_zero_distance"
)

DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_direct_norm_interval_bounds_full_cell_at_zero_distance"
)

LEGACY_INTERVAL_SUBCHUNK_PROOF_DATA = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData"
)


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_proof_data(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != PROOF_DATA_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def validate_direct_derivative_overlay(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != DIRECT_DERIVATIVE_OVERLAY_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def validate_local_component_interval_probe(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != LOCAL_COMPONENT_INTERVAL_PROBE_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def validate_hraw_center_coeff_contract(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != HRAW_CENTER_COEFF_CONTRACT_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def validate_coverage(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != DIRECT_COVERAGE_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def direct_overlay_paths_from_coverage(coverage: dict[str, Any]) -> list[Path]:
    paths: list[Path] = []
    for parent in coverage.get("directParents") or []:
        raw_path = parent.get("path")
        if raw_path:
            paths.append(Path(raw_path))
    return paths


def first_subchunk(payload: dict[str, Any]) -> dict[str, Any]:
    subchunks = payload.get("subchunks") or [{}]
    first = subchunks[0] if subchunks else {}
    return first if isinstance(first, dict) else {}


def direct_overlay_summary(
    payload: dict[str, Any],
    path: Path,
    coverage_parent: dict[str, Any] | None = None,
) -> dict[str, Any]:
    direct_first = first_subchunk(payload)
    pilot = payload.get("pilot") or {}
    totals = payload.get("totals") or {}
    return {
        "path": str(path),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
        "activeSubchunkProofData": payload.get("activeSubchunkProofData"),
        "preferredCellSlopeSubchunkProofData": payload.get(
            "preferredCellSlopeSubchunkProofData"
        ),
        "preferredCellSlopeDirectEndpointConstructor": payload.get(
            "preferredCellSlopeDirectEndpointConstructor"
        ),
        "legacyIntervalSubchunkProofData": payload.get(
            "legacyIntervalSubchunkProofData"
        ),
        "pilot": pilot,
        "coverageParent": coverage_parent,
        "family": (coverage_parent or {}).get("family") or pilot.get("family"),
        "row": (coverage_parent or {}).get("row") or pilot.get("row"),
        "parentChunk": (
            (coverage_parent or {}).get("parentChunk") or pilot.get("parentChunk")
        ),
        "left": (coverage_parent or {}).get("left") or pilot.get("left"),
        "right": (coverage_parent or {}).get("right") or pilot.get("right"),
        "split": (coverage_parent or {}).get("split") or pilot.get("split"),
        "policy": (coverage_parent or {}).get("policy"),
        "totals": totals,
        "remainingAnalyticFieldNames": payload.get("remainingAnalyticFieldNames"),
        "closedArithmeticFieldNames": payload.get("closedArithmeticFieldNames"),
        "hEnvelopeArithmetic": direct_first.get("hEnvelopeArithmetic"),
        "hResidualDerivAbsArithmetic": direct_first.get(
            "hResidualDerivAbsArithmetic"
        ),
        "hAnchorResidualReceiver": direct_first.get("hAnchorResidualReceiver"),
        "hAnchorResidualAbsCosReceiver": direct_first.get(
            "hAnchorResidualAbsCosReceiver"
        ),
        "hRawOmegaAtAbsCosReceiver": direct_first.get("hRawOmegaAtAbsCosReceiver"),
        "hAnchorResidualScaleAbsBoxReceiver": direct_first.get(
            "hAnchorResidualScaleAbsBoxReceiver"
        ),
        "hRawOmegaAtScaleAbsBoxReceiver": direct_first.get(
            "hRawOmegaAtScaleAbsBoxReceiver"
        ),
        "hAnchorResidualRawPolyReceiver": direct_first.get(
            "hAnchorResidualRawPolyReceiver"
        ),
        "hAnchorPolynomialCenterReceiver": direct_first.get(
            "hAnchorPolynomialCenterReceiver"
        ),
        "hDirectEnvelopeSingleCellReceiver": direct_first.get(
            "hDirectEnvelopeSingleCellReceiver"
        ),
        "hAnchorResidualNextInputs": direct_first.get("hAnchorResidualNextInputs"),
        "hEnvelopeNextInputs": direct_first.get("hEnvelopeNextInputs"),
        "hResidualDerivEqReceiver": direct_first.get("hResidualDerivEqReceiver"),
        "hResidualDerivCellRawPolyReceiver": direct_first.get(
            "hResidualDerivCellRawPolyReceiver"
        ),
        "hResidualDerivCellCompositeReceiver": direct_first.get(
            "hResidualDerivCellCompositeReceiver"
        ),
        "hResidualDerivCellExprCompositeReceiver": direct_first.get(
            "hResidualDerivCellExprCompositeReceiver"
        ),
        "hResidualDerivCellsExprCompositeReceiver": direct_first.get(
            "hResidualDerivCellsExprCompositeReceiver"
        ),
        "hResidualDerivSingleCellNormReceiver": direct_first.get(
            "hResidualDerivSingleCellNormReceiver"
        ),
        "hResidualDerivSingleCellIntervalNormReceiver": direct_first.get(
            "hResidualDerivSingleCellIntervalNormReceiver"
        ),
        "hResidualDerivCellsIntervalNormReceiver": direct_first.get(
            "hResidualDerivCellsIntervalNormReceiver"
        ),
        "hResidualDerivCellNextInputs": direct_first.get(
            "hResidualDerivCellNextInputs"
        ),
        "hResidualDerivCellsNextInputs": direct_first.get(
            "hResidualDerivCellsNextInputs"
        ),
        "hPolynomialDerivEqReceiver": direct_first.get("hPolynomialDerivEqReceiver"),
        "hPolynomialTermDerivEqReceiver": direct_first.get(
            "hPolynomialTermDerivEqReceiver"
        ),
        "hPolynomialDerivCellTermReceiver": direct_first.get(
            "hPolynomialDerivCellTermReceiver"
        ),
        "hPolynomialDerivCellExprReceiver": direct_first.get(
            "hPolynomialDerivCellExprReceiver"
        ),
        "routeBDerivativeArithmeticContract": direct_first.get(
            "routeBDerivativeArithmeticContract"
        ),
        "routeBAnchorResidualArithmeticContract": direct_first.get(
            "routeBAnchorResidualArithmeticContract"
        ),
    }


def direct_overlay_aggregate(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    remaining_by_field: dict[str, int] = {}
    total_subchunks = 0
    total_seeded = 0
    total_remaining = 0
    total_closed = 0
    sample_envelope_passing = 0
    derivative_abs_passing = 0
    closed_by_field: dict[str, int] = {}
    for summary in summaries:
        totals = summary.get("totals") or {}
        subchunks = int(totals.get("subchunks") or 0)
        total_subchunks += subchunks
        total_seeded += int(totals.get("seededFields") or 0)
        total_remaining += int(totals.get("remainingAnalyticFields") or 0)
        total_closed += int(totals.get("closedArithmeticFields") or 0)
        sample_envelope_passing += int(
            totals.get("sampleEnvelopeArithmeticPassing") or 0
        )
        derivative_abs_passing += int(
            totals.get("derivativeAbsArithmeticPassing") or 0
        )
        for field in summary.get("remainingAnalyticFieldNames") or []:
            remaining_by_field[field] = remaining_by_field.get(field, 0) + subchunks
        for field in summary.get("closedArithmeticFieldNames") or []:
            closed_by_field[field] = closed_by_field.get(field, 0) + subchunks
    return {
        "overlays": len(summaries),
        "subchunks": total_subchunks,
        "seededFields": total_seeded,
        "remainingAnalyticFields": total_remaining,
        "remainingAnalyticFieldsByName": remaining_by_field,
        "closedArithmeticFields": total_closed,
        "closedArithmeticFieldsByName": closed_by_field,
        "sampleEnvelopeArithmeticPassing": sample_envelope_passing,
        "derivativeAbsArithmeticPassing": derivative_abs_passing,
    }


def local_component_interval_probe_summary(
    payload: dict[str, Any],
    path: Path,
) -> dict[str, Any]:
    totals = payload.get("totals") or {}
    scale_proofs_by_family: dict[str, dict[str, str]] = {}
    for row in payload.get("rows") or []:
        family = row.get("family")
        proofs = row.get("scaleProofs")
        if isinstance(family, str) and isinstance(proofs, dict):
            scale_proofs_by_family.setdefault(family, dict(proofs))
    return {
        "path": str(path),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
        "receiver": payload.get("receiver"),
        "scaleMode": payload.get("scaleMode"),
        "scaleLower": payload.get("scaleLower"),
        "scaleUpper": payload.get("scaleUpper"),
        "scalePad": payload.get("scalePad"),
        "totals": totals,
        "scaleProofsByFamily": scale_proofs_by_family,
        "worstPassingEntry": payload.get("worstPassingEntry"),
    }


def hraw_center_coeff_contract_summary(
    payload: dict[str, Any],
    path: Path,
) -> dict[str, Any]:
    return {
        "path": str(path),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
        "receiver": payload.get("receiver"),
        "zeroDistanceReceiver": payload.get("zeroDistanceReceiver"),
        "compactComponentReceiver": payload.get("compactComponentReceiver"),
        "compactEndpointReceiver": payload.get("compactEndpointReceiver"),
        "compactDirectEndpointReceiver": payload.get("compactDirectEndpointReceiver"),
        "rawCenterCoeffSampleEnvelopeDirectEndpointConstructor": payload.get(
            "rawCenterCoeffSampleEnvelopeDirectEndpointConstructor"
        ),
        "componentBallCertReceiver": payload.get("componentBallCertReceiver"),
        "totals": payload.get("totals"),
        "worstArithmeticRow": payload.get("worstArithmeticRow"),
    }


def build_report(
    *,
    proof_data: dict[str, Any],
    proof_data_path: Path,
    coverage: dict[str, Any] | None,
    coverage_path: Path | None,
    direct_derivative_overlays: list[tuple[Path, dict[str, Any]]],
    local_component_interval_probe: tuple[Path, dict[str, Any]] | None,
    hraw_center_coeff_contract: tuple[Path, dict[str, Any]] | None,
    out_lean: Path,
) -> dict[str, Any]:
    totals = proof_data.get("totals", {})
    missing_sub = int(totals.get("missingSubchunkAnalyticFields", 0))
    missing_parent = int(totals.get("missingParentAnalyticFields", 0))
    missing_row = int(totals.get("missingRowAnalyticFields", 0))
    missing_total = missing_sub + missing_parent + missing_row
    ready = missing_total == 0
    status = (
        "ready_for_refined_payload_lean_emission"
        if ready
        else "missing_analytic_fields_no_lean_emitted"
    )
    reason = (
        "All refined proof-data groups are present.  A future emitter may write "
        "the Lean payload, which still must be checked by Lean."
        if ready
        else "Refined proof data is incomplete; writing a Lean payload now "
        "would turn missing Taylor/model or row-sum facts into a fake trusted import."
    )
    coverage_parents_by_path = {
        str(Path(parent.get("path"))): parent
        for parent in (coverage or {}).get("directParents") or []
        if parent.get("path")
    }
    direct_summaries = [
        direct_overlay_summary(
            payload,
            path,
            coverage_parents_by_path.get(str(path)),
        )
        for path, payload in direct_derivative_overlays
    ]
    direct_aggregate = direct_overlay_aggregate(direct_summaries)
    legacy_direct = direct_summaries[0] if direct_summaries else None
    direct_legacy_interval = (
        legacy_direct.get("legacyIntervalSubchunkProofData")
        if legacy_direct is not None
        else None
    )
    direct_parent_labels = [
        "{family} row {row} parent chunk {parentChunk}".format(
            family=summary.get("family"),
            row=summary.get("row"),
            parentChunk=summary.get("parentChunk"),
        )
        for summary in direct_summaries
    ]
    local_probe_summary = (
        None
        if local_component_interval_probe is None
        else local_component_interval_probe_summary(
            local_component_interval_probe[1],
            local_component_interval_probe[0],
        )
    )
    hraw_contract_summary = (
        None
        if hraw_center_coeff_contract is None
        else hraw_center_coeff_contract_summary(
            hraw_center_coeff_contract[1],
            hraw_center_coeff_contract[0],
        )
    )
    return {
        "schema": EMITTER_SCHEMA,
        "status": status,
        "reason": reason,
        "proofData": str(proof_data_path),
        "coverage": None if coverage_path is None else str(coverage_path),
        "proofDataStatus": proof_data.get("status"),
        "leanLandingSurface": proof_data.get("leanLandingSurface"),
        "leanDirectTailWindowInputs": proof_data.get("leanDirectTailWindowInputs"),
        "outLean": str(out_lean),
        "outLeanWritten": False,
        "missingTotal": missing_total,
        "missingSubchunkAnalyticFields": missing_sub,
        "missingParentAnalyticFields": missing_parent,
        "missingRowAnalyticFields": missing_row,
        "missingGroups": proof_data.get("missingGroups", {}),
        "totals": totals,
        "directDerivativeCoverage": (
            None
            if coverage is None
            else {
                "schema": coverage.get("schema"),
                "path": str(coverage_path),
                "totals": coverage.get("totals"),
                "directParents": coverage.get("directParents"),
            }
        ),
        "routeBDirectDerivativeOverlay": legacy_direct,
        "routeBDirectDerivativeOverlays": direct_summaries,
        "routeBDirectDerivativeAggregate": direct_aggregate,
        "localComponentIntervalProbe": local_probe_summary,
        "hRawCenterCoeffLocalComponentContract": hraw_contract_summary,
        "activeSubchunkProofData": PREFERRED_CELL_SLOPE_SUBCHUNK_PROOF_DATA,
        "legacyIntervalSubchunkProofData": (
            direct_legacy_interval or LEGACY_INTERVAL_SUBCHUNK_PROOF_DATA
        ),
        "preferredCellSlopeSubchunkProofData": (
            PREFERRED_CELL_SLOPE_SUBCHUNK_PROOF_DATA
        ),
        "preferredCellSlopeDirectEndpointConstructor": (
            PREFERRED_CELL_SLOPE_DIRECT_ENDPOINT_CONSTRUCTOR
        ),
        "preferredDirectNormCertConstructor": (
            PREFERRED_DIRECT_NORM_CERT_CONSTRUCTOR
        ),
        "directNormCertGenericConstructor": (
            GENERIC_DIRECT_NORM_CERT_CONSTRUCTOR
        ),
        "preferredDirectNormCertFullCellConstructor": (
            PREFERRED_DIRECT_NORM_CERT_CONSTRUCTOR
        ),
        "directNormIntervalBoundsFullCellConstructor": (
            DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR
        ),
        "nextProofProducingTarget": [
            "covered direct parents: "
            + (", ".join(direct_parent_labels) if direct_parent_labels else "none"),
            "current direct coverage: "
            + "{subchunks} subchunks, {remaining} remaining analytic fields".format(
                subchunks=direct_aggregate["subchunks"],
                remaining=direct_aggregate["remainingAnalyticFields"],
            ),
            "full payload via route-A parent-refined subchunk folding",
            "hRawCenterCoeffAbs via sharp raw-center-minus-coeff0 absolute bound; Lean wrapper derives hAnchorResidual",
            "preferred proof-data constructor for hRawCenterCoeffAbs: ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData.of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance",
            "hRawCenterCoeffAbs local scale-interval probe supplies 110/110 diagnostic rows with shared primary/control scale theorem names",
            "hRawCenterCoeffAbs local component contract supplies 110/110 arithmetic-ready zero-distance rows through one compact LocalRawOmegaComponentIntervalCert per row; preferred cert producer is LocalRawOmegaComponentIntervalCert.of_anchor_abs_bounds with 220 open abs ball facts and arithmetic containment checks",
            "with the direct endpoint constructor, generated rows should supply LocalRawOmegaComponentDirectEndpointIntervalCert plus rational scale/corner/coeff checks instead of a standalone hRawCenterCoeffAbs proof term",
            "scalar hEnvelope exact rational arithmetic already passes in the direct overlays; future Lean emission should materialize it with norm_num",
            "scale_abs_box anchor receiver remains compiled legacy support only",
            "preferred compact route: prove one ResidualDerivativeDirectNormCert.Valid per direct subchunk, prove cellL=L and cellU=U, and feed endpoint cert + direct norm cert to ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance",
            "shortcut compact route: prove residual-derivative lower/upper bounds on the full subchunk cell plus abs-slope comparisons and feed them to ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_direct_norm_interval_bounds_full_cell_at_zero_distance",
            "fallback compact route: extract hResidualDerivBoundOnCell and feed ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance",
            "legacy interval route remains available: direct residual-derivative lower/upper interval bounds via cancellation-preserving generator",
            "derivative abs comparisons already pass exact rational arithmetic; future Lean emission should materialize them with norm_num",
            "single-cell receiver residual_deriv_bound_on_single_cell_of_interval_bounds for current one-cell direct subchunks",
            "cell-indexed receiver residual_deriv_bound_on_cells_of_interval_bounds",
            "parent route-A fold via ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert",
        ],
        "routeBNextProofProducingTarget": [
            "primary_finite row 0 parent chunks 0 and 1",
            "proof-safe close hRawCenterCoeffAbs and the preferred direct residual-derivative norm bounds for the 110 covered direct subchunks",
            "hRawCenterCoeffAbs via sharp raw-center-minus-coeff0 anchor bound; Lean wrapper derives hAnchorResidual",
            "scalar hEnvelope via exact rational sample-envelope arithmetic",
            "do not use the current one-cell raw/poly derivative intervals as proof data; the feasibility audit shows cancellation loss on all 110 subchunks",
            "legacy lower/upper interval bounds may still feed residual_deriv_bound_on_single_cell_of_interval_bounds if the compact norm route fails; derivative abs comparisons are exact-passing metadata",
        ],
        "routeGuard": [
            "do not write Lean while missingTotal is nonzero",
            "parent fold must target RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert",
            "parent fold may land directly at ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralRefinedWindowProofData.toWindowPartBoundsCert",
            "exact-sum parent bounds build RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.of_refinedSubchunkSums",
            "top-level payload must keep the 26 parent chunks",
            "subchunk hIntegralLower/hIntegralUpper are eliminated by exact model integral bounds",
            "global preferred direct skeleton uses ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData and records one scalar residual-derivative norm proof input for hResidualDerivBoundOnCell",
            "legacy interval skeleton remains recorded as ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeExactIntegralChunkProofData",
            "hResidualDifferentiable is seeded globally by a checked Lean theorem in proof-data schema v17",
            "single-anchor geometry is seeded by anchor = center and mesh = radius",
            "derivative finite-cover geometry is seeded as one cell equal to the refined subchunk",
            "active full payload target is RawOmegaAChunkTaylorPayload.RefinedPayloadFin",
            "route-B hRawCenterCoeffAbs must use the sharp raw-center-minus-coeff0 receiver; hAnchorResidual is derived by the Lean wrapper",
            "route-B scalar hEnvelope arithmetic is exact-passing metadata, not Lean payload yet",
            "route-B scale_abs_box receiver is compiled legacy support, not the active full-payload blocker",
            "route-B nonnegative abs-cos anchor receiver is inactive for first finite chunk",
            "route-B polynomial anchor side should use polynomial_center when anchor = cert.center",
            "route-B residual derivative cells should prove hResidualDerivBoundOnCell through residual_deriv_bound_on_cells_of_interval_bounds",
            "route-B raw/poly derivative-cell receivers are legacy support only on this 0/110 feasibility route",
            "route-B scalable preferred derivative norm receiver is residual_deriv_bound_on_cells_of_interval_bounds",
            "route-B one-cell raw/poly derivative norm receiver is not proof-ready with current interval data; direct_receiver_feasibility_audit reports 0/110 passing",
            "route-B residual derivative identity is supplied by residual_deriv_eq",
            "route-B polynomial derivative cells should use polynomial_deriv_bounds_on_cell_of_term_deriv_bounds",
            "route-B polynomial derivative term bounds from explicit expressions should use polynomial_derivative_term_bounds_on_cell_of_expr_bounds",
            "route-B polynomial derivative identity is supplied by polynomial_deriv_eq_term_deriv_sum",
            "route-B monomial derivative identity is supplied by polynomial_term_deriv_eq",
            "route-B direct overlay is a candidate surface only, not proof data",
            "local component interval probe is a candidate surface only, not proof data",
            "hRawCenterCoeffAbs local component contract is a candidate surface only, not proof data",
            "do not fall back to scalePad = 1e-70 as the default scale route",
            "do not treat sampled derivative intervals as Lean proof data",
            "do not import generated refined payload until lake env lean checks it",
            "do not use this report as proof data",
            "do not mutate CSV, ARadius, radius-floor, or LDL data",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Refined Subchunk Lean Emitter Guard",
        "",
        "Guard report only.  No Lean file is written while fields are missing.",
        "",
        "## Verdict",
        "",
        f"- schema: `{report['schema']}`",
        f"- status: `{report['status']}`",
        f"- proof data status: `{report['proofDataStatus']}`",
        f"- Lean landing surface: `{report['leanLandingSurface']}`",
        f"- active subchunk proof data: `{report['activeSubchunkProofData']}`",
        f"- legacy interval subchunk proof data: `{report.get('legacyIntervalSubchunkProofData')}`",
        f"- preferred direct-endpoint constructor: `{report.get('preferredCellSlopeDirectEndpointConstructor')}`",
        f"- preferred direct-norm cert constructor: `{report.get('preferredDirectNormCertConstructor')}`",
        f"- generic direct-norm cert constructor: `{report.get('directNormCertGenericConstructor')}`",
        f"- preferred full-cell direct-norm cert constructor: `{report.get('preferredDirectNormCertFullCellConstructor')}`",
        f"- interval-bounds full-cell direct-norm constructor: `{report.get('directNormIntervalBoundsFullCellConstructor')}`",
        f"- out Lean: `{report['outLean']}`",
        f"- out Lean written: `{report['outLeanWritten']}`",
        f"- missing total: `{report['missingTotal']}`",
        f"- missing subchunk analytic fields: `{report['missingSubchunkAnalyticFields']}`",
        f"- missing parent analytic fields: `{report['missingParentAnalyticFields']}`",
        f"- missing row analytic fields: `{report['missingRowAnalyticFields']}`",
        "",
        "## Missing Groups",
        "",
        "| group | missing fields |",
        "| --- | ---: |",
    ]
    for group, count in sorted(report.get("missingGroups", {}).items()):
        lines.append(f"| `{group}` | `{count}` |")
    lines.extend(["", "## Next Proof-Producing Target", ""])
    for item in report["nextProofProducingTarget"]:
        lines.append(f"- `{item}`")
    coverage = report.get("directDerivativeCoverage")
    aggregate = report.get("routeBDirectDerivativeAggregate") or {}
    overlays = report.get("routeBDirectDerivativeOverlays") or []
    if coverage is not None:
        lines.extend(
            [
                "",
                "## Direct Derivative Coverage",
                "",
                f"- path: `{coverage.get('path')}`",
                f"- schema: `{coverage.get('schema')}`",
                f"- overlay files loaded: `{aggregate.get('overlays')}`",
                f"- direct subchunks loaded: `{aggregate.get('subchunks')}`",
                f"- seeded fields loaded: `{aggregate.get('seededFields')}`",
                f"- remaining analytic fields loaded: `{aggregate.get('remainingAnalyticFields')}`",
                f"- closed arithmetic fields loaded: `{aggregate.get('closedArithmeticFields')}`",
                f"- sample-envelope arithmetic passing: `{aggregate.get('sampleEnvelopeArithmeticPassing')}`",
                f"- derivative abs arithmetic passing: `{aggregate.get('derivativeAbsArithmeticPassing')}`",
                "",
                "| field | remaining covered subchunks |",
                "| --- | ---: |",
            ]
        )
        for field, count in sorted(
            (aggregate.get("remainingAnalyticFieldsByName") or {}).items()
        ):
            lines.append(f"| `{field}` | `{count}` |")
        lines.extend(["", "| field | exact arithmetic covered subchunks |", "| --- | ---: |"])
        for field, count in sorted(
            (aggregate.get("closedArithmeticFieldsByName") or {}).items()
        ):
            lines.append(f"| `{field}` | `{count}` |")
        lines.extend(
            [
                "",
                "| family | row | parent | split | remaining fields | path |",
                "| --- | ---: | ---: | ---: | ---: | --- |",
            ]
        )
        for overlay in overlays:
            totals = overlay.get("totals") or {}
            lines.append(
                "| `{family}` | `{row}` | `{parent}` | `{split}` | `{remaining}` | `{path}` |".format(
                    family=overlay.get("family"),
                    row=overlay.get("row"),
                    parent=overlay.get("parentChunk"),
                    split=overlay.get("split"),
                    remaining=totals.get("remainingAnalyticFields"),
                    path=overlay.get("path"),
                )
            )
    local_probe = report.get("localComponentIntervalProbe")
    if local_probe is not None:
        totals = local_probe.get("totals") or {}
        lines.extend(
            [
                "",
                "## Local Component Interval Probe",
                "",
                f"- path: `{local_probe.get('path')}`",
                f"- schema: `{local_probe.get('schema')}`",
                f"- status: `{local_probe.get('status')}`",
                f"- receiver: `{local_probe.get('receiver')}`",
                f"- scale mode: `{local_probe.get('scaleMode')}`",
                f"- scale lower: `{local_probe.get('scaleLower')}`",
                f"- scale upper: `{local_probe.get('scaleUpper')}`",
                f"- scale pad override: `{local_probe.get('scalePad')}`",
                f"- entries: `{totals.get('entries')}`",
                f"- passed at some width: `{totals.get('passedAnyWidth')}`",
                f"- failed at all widths: `{totals.get('failedAnyWidth')}`",
                f"- proof-safe closed fields: `{totals.get('proofSafeClosedFields')}`",
                "",
                "| family | hScaleLower | hScaleUpper |",
                "| --- | --- | --- |",
            ]
        )
        for family, proofs in sorted(
            (local_probe.get("scaleProofsByFamily") or {}).items()
        ):
            lines.append(
                "| `{family}` | `{lower}` | `{upper}` |".format(
                    family=family,
                    lower=proofs.get("hScaleLower"),
                    upper=proofs.get("hScaleUpper"),
                )
            )
        worst = local_probe.get("worstPassingEntry")
        if worst:
            chosen = worst.get("chosen") or {}
            lines.extend(
                [
                    "",
                    "Worst passing local component row:",
                    "",
                    f"- family: `{worst.get('family')}`",
                    f"- row: `{worst.get('row')}`",
                    f"- parent chunk: `{worst.get('parentChunk')}`",
                    f"- subchunk: `{worst.get('subchunk')}`",
                    f"- largest passing width: `{worst.get('largestPassingWidth')}`",
                    f"- min margin: `{chosen.get('minMarginDecimal')}`",
                ]
            )
    hraw_contract = report.get("hRawCenterCoeffLocalComponentContract")
    if hraw_contract is not None:
        totals = hraw_contract.get("totals") or {}
        lines.extend(
            [
                "",
                "## hRawCenterCoeffAbs Local Component Contract",
                "",
                f"- path: `{hraw_contract.get('path')}`",
                f"- schema: `{hraw_contract.get('schema')}`",
                f"- status: `{hraw_contract.get('status')}`",
                f"- receiver: `{hraw_contract.get('receiver')}`",
                f"- zero-distance receiver: `{hraw_contract.get('zeroDistanceReceiver')}`",
                f"- compact component receiver: `{hraw_contract.get('compactComponentReceiver')}`",
                f"- compact endpoint receiver: `{hraw_contract.get('compactEndpointReceiver')}`",
                f"- compact direct endpoint receiver: `{hraw_contract.get('compactDirectEndpointReceiver')}`",
                "- raw-center sample-envelope direct endpoint constructor: "
                f"`{hraw_contract.get('rawCenterCoeffSampleEnvelopeDirectEndpointConstructor')}`",
                f"- component ball cert receiver: `{hraw_contract.get('componentBallCertReceiver')}`",
                f"- rows: `{totals.get('rows')}`",
                f"- arithmetic-ready rows: `{totals.get('arithmeticReadyRows')}`",
                f"- arithmetic-failed rows: `{totals.get('arithmeticFailedRows')}`",
                f"- anchor memberships passing: `{totals.get('anchorMembershipPassing')}`",
                f"- scale proof references: `{totals.get('scaleProofReferences')}`",
                f"- component interval proofs open: `{totals.get('componentIntervalProofsOpen')}`",
                f"- component interval certs open: `{totals.get('componentIntervalCertsOpen')}`",
                f"- compact component rows: `{totals.get('compactComponentRows')}`",
                f"- component ball certs open: `{totals.get('componentBallCertsOpen')}`",
                f"- component ball abs facts open: `{totals.get('componentBallAbsFactsOpen')}`",
                f"- component ball containment passing: `{totals.get('componentBallContainmentPassing')} / {totals.get('componentBallContainmentComparisons')}`",
                f"- corner arithmetic passing: `{totals.get('cornerArithmeticPassing')} / {totals.get('cornerArithmeticComparisons')}`",
                f"- coeff arithmetic passing: `{totals.get('coeffArithmeticPassing')} / {totals.get('coeffArithmeticComparisons')}`",
                f"- proof-safe closed fields: `{totals.get('proofSafeClosedFields')}`",
            ]
        )
        worst_contract = hraw_contract.get("worstArithmeticRow")
        if worst_contract:
            lines.extend(
                [
                    "",
                    "Worst contract arithmetic row:",
                    "",
                    f"- family: `{worst_contract.get('family')}`",
                    f"- row: `{worst_contract.get('row')}`",
                    f"- parent chunk: `{worst_contract.get('parentChunk')}`",
                    f"- subchunk: `{worst_contract.get('subchunk')}`",
                    f"- min arithmetic margin: `{worst_contract.get('minArithmeticMarginDecimal')}`",
                ]
            )
    direct_overlay = report.get("routeBDirectDerivativeOverlay")
    if direct_overlay is not None:
        lines.extend(
            [
                "",
                "## Route-B First Direct Derivative Overlay Detail",
                "",
                f"- path: `{direct_overlay['path']}`",
                f"- schema: `{direct_overlay['schema']}`",
                f"- status: `{direct_overlay['status']}`",
                f"- active subchunk proof data: `{direct_overlay['activeSubchunkProofData']}`",
                f"- preferred cell-slope proof data: `{report.get('preferredCellSlopeSubchunkProofData')}`",
                f"- preferred cell-slope direct endpoint constructor: `{report.get('preferredCellSlopeDirectEndpointConstructor')}`",
                f"- preferred direct-norm cert constructor: `{report.get('preferredDirectNormCertConstructor')}`",
                f"- generic direct-norm cert constructor: `{report.get('directNormCertGenericConstructor')}`",
                f"- preferred full-cell direct-norm cert constructor: `{report.get('preferredDirectNormCertFullCellConstructor')}`",
                f"- interval-bounds full-cell direct-norm constructor: `{report.get('directNormIntervalBoundsFullCellConstructor')}`",
            ]
        )
        totals = direct_overlay.get("totals") or {}
        lines.extend(
            [
                f"- subchunks: `{totals.get('subchunks')}`",
                f"- seeded fields: `{totals.get('seededFields')}`",
                f"- remaining analytic fields: `{totals.get('remainingAnalyticFields')}`",
            "",
            "hEnvelope receiver support:",
            "",
            f"- signed scale-abs pilot support: `{direct_overlay.get('hAnchorResidualScaleAbsBoxReceiver')}`",
            f"- raw integrand scale-abs pilot support: `{direct_overlay.get('hRawOmegaAtScaleAbsBoxReceiver')}`",
            f"- inactive abs-cos support: `{direct_overlay.get('hAnchorResidualAbsCosReceiver')}`",
            f"- `{direct_overlay.get('hAnchorResidualReceiver')}`",
            f"- raw/poly packaging: `{direct_overlay.get('hAnchorResidualRawPolyReceiver')}`",
            f"- polynomial center: `{direct_overlay.get('hAnchorPolynomialCenterReceiver')}`",
            "",
            "hEnvelope generated inputs:",
            "",
            ]
        )
        for item in direct_overlay.get("hEnvelopeNextInputs") or []:
            lines.append(f"- `{item}`")
        anchor_contract = (
            direct_overlay.get("routeBAnchorResidualArithmeticContract") or {}
        )
        if anchor_contract:
            lines.extend(
                [
                    "",
                    "Route-B anchor residual arithmetic contract:",
                    "",
                    f"- preferred receiver: `{anchor_contract.get('preferredReceiver')}`",
                    f"- direct raw-center-coeff abs bounds: `{anchor_contract.get('directRawCenterCoeffAbsBounds')}`",
                    f"- legacy scale-abs obligations: `{anchor_contract.get('legacyScaleAbsBoxObligations')}`",
                    f"- total per subchunk: `{anchor_contract.get('totalAnchorResidualArithmeticObligations')}`",
                ]
            )
        lines.extend(
            [
                "",
                "hResidualDeriv cell receivers:",
                "",
                f"- active single-cell interval norm: `{direct_overlay.get('hResidualDerivSingleCellIntervalNormReceiver')}`",
                f"- active all-cells interval norm: `{direct_overlay.get('hResidualDerivCellsIntervalNormReceiver')}`",
                f"- legacy raw/poly single-cell norm: `{direct_overlay.get('hResidualDerivSingleCellNormReceiver')}`",
                f"- legacy all-cells expr composite: `{direct_overlay.get('hResidualDerivCellsExprCompositeReceiver')}`",
                "",
                "hResidualDeriv cell generated inputs:",
                "",
            ]
        )
        for item in direct_overlay.get("hResidualDerivCellNextInputs") or []:
            lines.append(f"- `{item}`")
        contract = direct_overlay.get("routeBDerivativeArithmeticContract") or {}
        if contract:
            lines.extend(
                [
                    "",
                    "Route-B derivative arithmetic contract:",
                    "",
                    f"- cell-indexed receiver: `{contract.get('cellIndexedReceiver')}`",
                    f"- degree: `{contract.get('degree')}`",
                    f"- term count: `{contract.get('termCount')}`",
                    f"- derivative cells: `{contract.get('derivCellCount')}`",
                    f"- direct residual derivative bounds: `{contract.get('directResidualDerivativeBounds')}`",
                    f"- residual derivative abs comparisons: `{contract.get('residualDerivativeAbsComparisons')}`",
                    f"- total per subchunk: `{contract.get('totalDerivativeArithmeticObligations')}`",
                ]
            )
        lines.extend(
            [
                "",
                "Route-B next proof-producing target:",
                "",
            ]
        )
        for item in report["routeBNextProofProducingTarget"]:
            lines.append(f"- `{item}`")
    lines.extend(["", "## Reason", "", report["reason"], "", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proof-data", type=Path, default=DEFAULT_PROOF_DATA)
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument(
        "--direct-derivative-overlay",
        type=Path,
        action="append",
        default=[],
    )
    parser.add_argument(
        "--local-component-interval-probe",
        type=Path,
        default=DEFAULT_LOCAL_COMPONENT_INTERVAL_PROBE,
    )
    parser.add_argument(
        "--hraw-center-coeff-contract",
        type=Path,
        default=DEFAULT_HRAW_CENTER_COEFF_CONTRACT,
    )
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--out-lean", type=Path, default=DEFAULT_OUT_LEAN)
    args = parser.parse_args()

    proof_data = load_json(args.proof_data)
    validate_proof_data(proof_data, args.proof_data)
    coverage = None
    coverage_path = None
    direct_overlay_paths: list[Path] = list(args.direct_derivative_overlay)
    if args.coverage.exists():
        coverage = load_json(args.coverage)
        validate_coverage(coverage, args.coverage)
        coverage_path = args.coverage
        if not direct_overlay_paths:
            direct_overlay_paths = direct_overlay_paths_from_coverage(coverage)
    if not direct_overlay_paths and DEFAULT_DIRECT_DERIVATIVE_OVERLAY.exists():
        direct_overlay_paths = [DEFAULT_DIRECT_DERIVATIVE_OVERLAY]
    direct_derivative_overlays: list[tuple[Path, dict[str, Any]]] = []
    seen_paths: set[Path] = set()
    for path in direct_overlay_paths:
        path = path.expanduser()
        if path in seen_paths:
            continue
        seen_paths.add(path)
        if not path.exists():
            raise FileNotFoundError(path)
        overlay = load_json(path)
        validate_direct_derivative_overlay(overlay, path)
        direct_derivative_overlays.append((path, overlay))
    local_component_interval_probe = None
    if args.local_component_interval_probe.exists():
        local_probe = load_json(args.local_component_interval_probe)
        validate_local_component_interval_probe(
            local_probe,
            args.local_component_interval_probe,
        )
        local_component_interval_probe = (
            args.local_component_interval_probe,
            local_probe,
        )
    hraw_center_coeff_contract = None
    if args.hraw_center_coeff_contract.exists():
        hraw_contract = load_json(args.hraw_center_coeff_contract)
        validate_hraw_center_coeff_contract(
            hraw_contract,
            args.hraw_center_coeff_contract,
        )
        hraw_center_coeff_contract = (
            args.hraw_center_coeff_contract,
            hraw_contract,
        )
    report = build_report(
        proof_data=proof_data,
        proof_data_path=args.proof_data,
        coverage=coverage,
        coverage_path=coverage_path,
        direct_derivative_overlays=direct_derivative_overlays,
        local_component_interval_probe=local_component_interval_probe,
        hraw_center_coeff_contract=hraw_center_coeff_contract,
        out_lean=args.out_lean,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} out_lean_written={written} missing_total={missing} direct_subchunks={direct_subchunks}".format(
            status=report["status"],
            written=report["outLeanWritten"],
            missing=report["missingTotal"],
            direct_subchunks=(
                report.get("routeBDirectDerivativeAggregate") or {}
            ).get("subchunks"),
        )
    )


if __name__ == "__main__":
    run()
