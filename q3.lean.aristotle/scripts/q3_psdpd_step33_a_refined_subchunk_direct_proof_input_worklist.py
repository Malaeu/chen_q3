#!/usr/bin/env python3
"""Build the direct proof-input worklist for covered refined subchunks.

This is a fail-closed control-plane artifact for the current Step33A.1-A
raw-Omega route-A payload.  It consumes the refined-subchunk emitter report,
loads every selected direct derivative overlay, and expands the preferred
still-missing analytic proof-safe fields:

* hRawCenterCoeffAbs
* hResidualDerivBoundOnCell

The older hResidualDerivLowerOnCell / hResidualDerivUpperOnCell route is kept
as legacy diagnostic support.

It also records the already exact-passing scalar `hEnvelope` arithmetic
comparison separately; that comparison is not treated as Lean proof data until
future payload emission materializes it with a checked proof.

The output is not Lean proof data.  It records the exact arithmetic input
families a proof-producing generator must emit next.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_EMITTER = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_lean_emitter.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_proof_input_worklist.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_proof_input_worklist.md"
)

EMITTER_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_payload_lean_emitter.v37"
DIRECT_OVERLAY_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.v30"
)
WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_proof_input_worklist.v20"
)

REQUIRED_FIELDS = [
    "hRawCenterCoeffAbs",
    "hResidualDerivBoundOnCell",
]

LEGACY_INTERVAL_REQUIRED_FIELDS = [
    "hRawCenterCoeffAbs",
    "hResidualDerivLowerOnCell",
    "hResidualDerivUpperOnCell",
]

RAW_CENTER_COEFF_VALUE_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_raw_value_bounds_at"
)

RAW_CENTER_COEFF_VALUE_BOUNDS_INPUTS = [
    "rawLower <= step22PositiveAxisOmegaAIntegrand k ell x anchor",
    "step22PositiveAxisOmegaAIntegrand k ell x anchor <= rawUpper",
    "-sampleRadius <= rawLower - cert.coeff 0",
    "rawUpper - cert.coeff 0 <= sampleRadius",
]

CELL_SLOPE_DIRECT_ENDPOINT_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance"
)

CELL_SLOPE_EXACT_INTEGRAL_PROOF_DATA = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData"
)

DIRECT_NORM_CERT_EXACT_INTEGRAL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_direct_norm_cert_at_zero_distance"
)

DIRECT_NORM_CERT_FULL_CELL_EXACT_INTEGRAL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance"
)

RAW_CENTER_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_raw_center_coeff_abs_direct_norm_cert_full_cell"
)

DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell"
)

ENDPOINT_DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData."
    "of_local_direct_endpoint_cert_scale_direct_norm_interval_bounds_full_cell_at_zero_distance"
)

DIRECT_NORM_CERT = (
    "RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert"
)

DIRECT_NORM_CERT_VALID = (
    "RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert.Valid"
)

DIRECT_NORM_CERT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "residualDerivBoundOnCell_of_directNormCert"
)

DIRECT_NORM_CERT_VALID_INTERVAL_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "ResidualDerivativeDirectNormCert.Valid.of_interval_bounds"
)

DIRECT_NORM_CERT_VALID_INTERPOLATION_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound"
)

FIRST_SUBCHUNK_ANCHOR_ENVELOPE_INTERVAL_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "primaryFiniteRow0Parent0Split100Sub0_residual_deriv_interval_bounds_of_anchor_envelope"
)

FIRST_SUBCHUNK_ANCHOR_ENVELOPE_PROOF_DATA_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_anchor_envelope"
)

CELL_SLOPE_REFINED_PAYLOAD_FIN = (
    "RawOmegaAChunkTaylorPayload.CellSlopeDirectEnvelopeRefinedPayloadFin"
)

REFINED_PAYLOAD_FIN = "RawOmegaAChunkTaylorPayload.RefinedPayloadFin"


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_schema(payload: dict[str, Any], *, path: Path, schema: str) -> None:
    found = payload.get("schema")
    if found != schema:
        raise ValueError(f"{path}: expected schema {schema!r}, found {found!r}")


def dec_or_none(value: Any) -> Decimal | None:
    if value is None:
        return None
    return Decimal(str(value))


def sampled_envelope_passes(entry: dict[str, Any]) -> bool | None:
    excess = dec_or_none(entry.get("sampledEnvelopeExcess"))
    if excess is None:
        return None
    return excess <= 0


def is_primary_finite_row0_parent0_sub0(
    *, overlay_summary: dict[str, Any], subchunk: dict[str, Any]
) -> bool:
    return (
        overlay_summary.get("family") == "primary_finite"
        and str(overlay_summary.get("row")) == "0"
        and str(overlay_summary.get("parentChunk")) == "0"
        and str(subchunk.get("subchunk")) == "0"
    )


def first_subchunk_anchor_envelope_work(
    *, overlay_summary: dict[str, Any], subchunk: dict[str, Any]
) -> dict[str, Any] | None:
    if not is_primary_finite_row0_parent0_sub0(
        overlay_summary=overlay_summary, subchunk=subchunk
    ):
        return None
    return {
        "status": "available_first_subchunk_only_receiver_not_payload",
        "targetGap": "STEP33_A1_SUB0_RESIDUAL_DERIV_ANCHOR_ENVELOPE_PAYLOAD_GAP",
        "intervalReceiver": FIRST_SUBCHUNK_ANCHOR_ENVELOPE_INTERVAL_RECEIVER,
        "proofDataReceiver": FIRST_SUBCHUNK_ANCHOR_ENVELOPE_PROOF_DATA_RECEIVER,
        "cell": "Set.Icc (0 : Real) ((1 : Real) / 10)",
        "anchor": "0",
        "mesh": "1/10",
        "requiredInputs": [
            "0 <= derivSlope",
            "derivAnchorLower <= deriv cert.residual 0",
            "deriv cert.residual 0 <= derivAnchorUpper",
            "DifferentiableAt Real (fun t => deriv cert.residual t) on [0, 1/10]",
            "proof-grade second-derivative envelope on [0, 1/10]",
            "lower budget: sampled lower <= derivAnchorLower - derivSlope * (1/10)",
            "upper budget: derivAnchorUpper + derivSlope * (1/10) <= sampled upper",
        ],
        "guard": [
            "first-subchunk concrete adapter only",
            "not reusable for other subchunks",
            "sampled derivative audit remains diagnostic-only",
            "do not emit this route unless all requiredInputs are Lean-checked",
        ],
    }


def overlay_path(summary: dict[str, Any]) -> Path:
    raw = summary.get("path")
    if not raw:
        raise ValueError(f"direct overlay summary missing path: {summary!r}")
    path = Path(str(raw))
    if path.is_absolute():
        return path
    return (ROOT / path).resolve()


def build_subchunk_work(
    *,
    overlay_summary: dict[str, Any],
    subchunk: dict[str, Any],
) -> dict[str, Any]:
    anchor_contract = subchunk.get("routeBAnchorResidualArithmeticContract") or {}
    derivative_contract = subchunk.get("routeBDerivativeArithmeticContract") or {}
    remaining_fields = list(subchunk.get("remainingAnalyticFields") or [])
    missing_required = sorted(set(REQUIRED_FIELDS) - set(remaining_fields))
    seeded_fields = subchunk.get("seededFields") or {}
    sub0_anchor_envelope_work = first_subchunk_anchor_envelope_work(
        overlay_summary=overlay_summary, subchunk=subchunk
    )
    return {
        "family": overlay_summary.get("family"),
        "row": overlay_summary.get("row"),
        "parentChunk": overlay_summary.get("parentChunk"),
        "split": overlay_summary.get("split"),
        "subchunk": subchunk.get("subchunk"),
        "left": subchunk.get("left"),
        "right": subchunk.get("right"),
        "center": subchunk.get("center"),
        "remainingAnalyticFields": remaining_fields,
        "missingRequiredFieldNames": missing_required,
        "proofStatus": subchunk.get("proofStatus"),
        "sampledEnvelopeExcess": subchunk.get("sampledEnvelopeExcess"),
        "sampledEnvelopePasses": sampled_envelope_passes(subchunk),
        "seededFieldNames": subchunk.get("seededFieldNames") or [],
        "seededScalars": {
            "anchor": seeded_fields.get("anchor"),
            "mesh": seeded_fields.get("mesh"),
            "remainder": seeded_fields.get("remainder"),
            "sampleRadius": seeded_fields.get("sampleRadius"),
            "cellL": seeded_fields.get("cellL"),
            "cellU": seeded_fields.get("cellU"),
            "derivLower": seeded_fields.get("derivLower"),
            "derivUpper": seeded_fields.get("derivUpper"),
            "derivSlope": seeded_fields.get("derivSlope"),
            "derivCellCount": seeded_fields.get("derivCellCount"),
            "derivCellLeft": seeded_fields.get("derivCellLeft"),
            "derivCellRight": seeded_fields.get("derivCellRight"),
        },
        "hRawCenterCoeffAbsWork": {
            "targetField": "hRawCenterCoeffAbs",
            "receiver": subchunk.get("hAnchorResidualReceiver"),
            "sampleRadius": seeded_fields.get("sampleRadius"),
            "valueBoundsReceiver": RAW_CENTER_COEFF_VALUE_BOUNDS_RECEIVER,
            "valueBoundsInputs": RAW_CENTER_COEFF_VALUE_BOUNDS_INPUTS,
            "rawPolyReceiver": subchunk.get("hAnchorResidualRawPolyReceiver"),
            "polynomialCenterReceiver": subchunk.get(
                "hAnchorPolynomialCenterReceiver"
            ),
            "rawCenterCoeffAbsInputs": (
                subchunk.get("hAnchorResidualNextInputs") or []
            ),
            "arithmeticContract": anchor_contract,
            "arithmeticObligations": int(
                anchor_contract.get("totalAnchorResidualArithmeticObligations") or 0
            ),
        },
        "hEnvelopeArithmeticWork": {
            "targetField": "hEnvelope",
            "status": "exact_rational_pass_not_lean_payload",
            "directEnvelopeReceiver": subchunk.get(
                "hDirectEnvelopeSingleCellReceiver"
            ),
            "arithmetic": subchunk.get("hEnvelopeArithmetic") or {},
            "arithmeticObligations": 1,
        },
        "hResidualDerivIntervalWork": {
            "targetFields": [
                "hResidualDerivLowerOnCell",
                "hResidualDerivUpperOnCell",
            ],
            "preferredReceiver": derivative_contract.get("preferredReceiver"),
            "singleCellReceiver": derivative_contract.get("singleCellReceiver"),
            "cellIndexedReceiver": derivative_contract.get("cellIndexedReceiver"),
            "residualDerivativeIntervalCandidates": subchunk.get(
                "residualDerivativeIntervalCandidates"
            )
            or [],
            "identityReceiver": subchunk.get("hResidualDerivEqReceiver"),
            "polynomialDerivativeIdentityReceiver": subchunk.get(
                "hPolynomialDerivEqReceiver"
            ),
            "monomialDerivativeIdentityReceiver": subchunk.get(
                "hPolynomialTermDerivEqReceiver"
            ),
            "cellInputs": subchunk.get("hResidualDerivCellNextInputs") or [],
            "arithmeticContract": derivative_contract,
            "arithmeticObligations": int(
                derivative_contract.get("openDerivativeAnalyticObligations") or 0
            ),
        },
        "hResidualDerivNormWork": {
            "targetField": "hResidualDerivBoundOnCell",
            "preferredProofData": CELL_SLOPE_EXACT_INTEGRAL_PROOF_DATA,
            "preferredDirectEndpointConstructor": CELL_SLOPE_DIRECT_ENDPOINT_CONSTRUCTOR,
            "preferredDirectNormCertConstructor": (
                RAW_CENTER_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR
            ),
            "endpointDirectNormCertFullCellConstructor": (
                DIRECT_NORM_CERT_FULL_CELL_EXACT_INTEGRAL_CONSTRUCTOR
            ),
            "directNormCertGenericConstructor": (
                DIRECT_NORM_CERT_EXACT_INTEGRAL_CONSTRUCTOR
            ),
            "preferredDirectNormCertFullCellConstructor": (
                RAW_CENTER_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR
            ),
            "directNormIntervalBoundsFullCellConstructor": (
                DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR
            ),
            "endpointDirectNormIntervalBoundsFullCellFallbackConstructor": (
                ENDPOINT_DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR
            ),
            "directNormCert": DIRECT_NORM_CERT,
            "directNormCertValid": DIRECT_NORM_CERT_VALID,
            "directNormCertReceiver": DIRECT_NORM_CERT_RECEIVER,
            "directNormCertValidIntervalReceiver": (
                DIRECT_NORM_CERT_VALID_INTERVAL_RECEIVER
            ),
            "directNormCertValidInterpolationReceiver": (
                DIRECT_NORM_CERT_VALID_INTERPOLATION_RECEIVER
            ),
            "firstSubchunkAnchorEnvelopeWork": sub0_anchor_envelope_work,
            "singleCellNormReceiver": subchunk.get(
                "hResidualDerivSingleCellIntervalNormReceiver"
            ),
            "legacyIntervalReceiver": derivative_contract.get("singleCellReceiver"),
            "cellInputs": [
                "construct ResidualDerivativeDirectNormCert with cellL, cellU, derivSlope",
                "prove full-cell equalities cellL = L and cellU = U",
                "prove ResidualDerivativeDirectNormCert.Valid",
                "available Lean adapter: prove sharp residual-derivative lower/upper bounds on the same cell, then use ResidualDerivativeDirectNormCert.Valid.of_interval_bounds",
                "available Lean adapter: prove exact model derivative norm + interpolation/error bound on the same cell, then use ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound",
                "first-subchunk-only fallback: for primary_finite row 0 parent 0 subchunk 0, prove the anchor-envelope inputs and use primaryFiniteRow0Parent0Split100Sub0_residual_deriv_interval_bounds_of_anchor_envelope",
                "prove cancellation-preserving norm bound "
                "||deriv cert.residual eta|| <= derivSlope on the one derivative cell",
                "preferred: feed hRawCenterCoeffAbs + DirectNormCert.Valid + full-cell endpoint equalities to of_raw_center_coeff_abs_direct_norm_cert_full_cell",
                "endpoint fallback: feed endpoint cert + DirectNormCert.Valid + full-cell endpoint equalities to of_local_direct_endpoint_cert_scale_direct_norm_cert_full_cell_at_zero_distance",
                "interval shortcut: feed hRawCenterCoeffAbs + residual-derivative lower/upper bounds + abs-slope comparisons to of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell",
                "endpoint interval fallback: feed endpoint cert + residual-derivative lower/upper bounds + abs-slope comparisons to of_local_direct_endpoint_cert_scale_direct_norm_interval_bounds_full_cell_at_zero_distance",
                "fallback: extract hResidualDerivBoundOnCell with residualDerivBoundOnCell_of_directNormCert",
                "fallback: feed the extracted bound directly to the cell-slope direct endpoint exact-integral wrapper",
                "do not emit derivLower/derivUpper when the norm proof is available",
            ],
            "arithmeticObligations": int(
                derivative_contract.get("derivCellCount") or 1
            ),
        },
        "hResidualDerivAbsArithmeticWork": {
            "targetFields": ["hDerivLowerAbs", "hDerivUpperAbs"],
            "status": "exact_rational_pass_not_lean_payload",
            "arithmetic": subchunk.get("hResidualDerivAbsArithmetic") or {},
            "arithmeticObligations": int(
                derivative_contract.get("closedDerivativeAbsComparisons") or 0
            ),
        },
    }


def build_worklist(emitter_path: Path) -> dict[str, Any]:
    emitter = load_json(emitter_path)
    validate_schema(emitter, path=emitter_path, schema=EMITTER_SCHEMA)
    overlay_summaries = emitter.get("routeBDirectDerivativeOverlays") or []
    if not overlay_summaries:
        legacy = emitter.get("routeBDirectDerivativeOverlay")
        overlay_summaries = [legacy] if legacy else []

    parents = []
    totals = {
        "overlays": 0,
        "subchunks": 0,
        "hRawCenterCoeffAbsFields": 0,
        "hEnvelopeArithmeticFields": 0,
        "hEnvelopeArithmeticPassingFields": 0,
        "hResidualDerivLowerOnCellFields": 0,
        "hResidualDerivUpperOnCellFields": 0,
        "hResidualDerivAbsArithmeticFields": 0,
        "hResidualDerivAbsArithmeticPassingFields": 0,
        "hResidualDerivBoundOnCellFields": 0,
        "firstSubchunkAnchorEnvelopeAdapters": 0,
        "preferredNormRouteDerivativeAnalyticObligations": 0,
        "preferredNormRouteOpenAnalyticObligations": 0,
        "rawCenterCoeffAbsArithmeticObligations": 0,
        "sampleEnvelopeArithmeticObligations": 0,
        "derivativeArithmeticObligations": 0,
        "derivativeAbsArithmeticObligations": 0,
        "openArithmeticObligations": 0,
        "totalArithmeticComparisonsIncludingClosed": 0,
        "sampledEnvelopePassingSubchunks": 0,
        "sampledEnvelopeUnknownSubchunks": 0,
        "proofSafeClosedFields": 0,
    }

    for summary in overlay_summaries:
        path = overlay_path(summary)
        overlay = load_json(path)
        validate_schema(overlay, path=path, schema=DIRECT_OVERLAY_SCHEMA)
        subchunk_work = [
            build_subchunk_work(overlay_summary=summary, subchunk=subchunk)
            for subchunk in overlay.get("subchunks") or []
        ]
        parent_totals = {
            "subchunks": len(subchunk_work),
            "hRawCenterCoeffAbsFields": sum(
                1
                for item in subchunk_work
                if "hRawCenterCoeffAbs" in item["remainingAnalyticFields"]
            ),
            "hEnvelopeArithmeticFields": len(subchunk_work),
            "hEnvelopeArithmeticPassingFields": sum(
                1
                for item in subchunk_work
                if item["hEnvelopeArithmeticWork"]["arithmetic"].get("passes")
                is True
            ),
            "hResidualDerivLowerOnCellFields": sum(
                1
                for item in subchunk_work
                if "hResidualDerivLowerOnCell" in item["remainingAnalyticFields"]
            ),
            "hResidualDerivUpperOnCellFields": sum(
                1
                for item in subchunk_work
                if "hResidualDerivUpperOnCell" in item["remainingAnalyticFields"]
            ),
            "hResidualDerivAbsArithmeticFields": 2 * len(subchunk_work),
            "hResidualDerivAbsArithmeticPassingFields": sum(
                2
                for item in subchunk_work
                if item["hResidualDerivAbsArithmeticWork"]["arithmetic"].get("passes")
                is True
            ),
            "hResidualDerivBoundOnCellFields": len(subchunk_work),
            "firstSubchunkAnchorEnvelopeAdapters": sum(
                1
                for item in subchunk_work
                if item["hResidualDerivNormWork"][
                    "firstSubchunkAnchorEnvelopeWork"
                ]
                is not None
            ),
            "preferredNormRouteDerivativeAnalyticObligations": sum(
                item["hResidualDerivNormWork"]["arithmeticObligations"]
                for item in subchunk_work
            ),
            "rawCenterCoeffAbsArithmeticObligations": sum(
                item["hRawCenterCoeffAbsWork"]["arithmeticObligations"]
                for item in subchunk_work
            ),
            "sampleEnvelopeArithmeticObligations": sum(
                item["hEnvelopeArithmeticWork"]["arithmeticObligations"]
                for item in subchunk_work
            ),
            "derivativeArithmeticObligations": sum(
                item["hResidualDerivIntervalWork"]["arithmeticObligations"]
                for item in subchunk_work
            ),
            "derivativeAbsArithmeticObligations": sum(
                item["hResidualDerivAbsArithmeticWork"]["arithmeticObligations"]
                for item in subchunk_work
            ),
            "sampledEnvelopePassingSubchunks": sum(
                1 for item in subchunk_work if item["sampledEnvelopePasses"] is True
            ),
            "sampledEnvelopeUnknownSubchunks": sum(
                1 for item in subchunk_work if item["sampledEnvelopePasses"] is None
            ),
        }
        parent_totals["openArithmeticObligations"] = (
            parent_totals["rawCenterCoeffAbsArithmeticObligations"]
            + parent_totals["derivativeArithmeticObligations"]
        )
        parent_totals["preferredNormRouteOpenAnalyticObligations"] = (
            parent_totals["hRawCenterCoeffAbsFields"]
            + parent_totals["preferredNormRouteDerivativeAnalyticObligations"]
        )
        parent_totals["totalArithmeticComparisonsIncludingClosed"] = (
            parent_totals["openArithmeticObligations"]
            + parent_totals["sampleEnvelopeArithmeticObligations"]
            + parent_totals["derivativeAbsArithmeticObligations"]
        )
        parents.append(
            {
                "family": summary.get("family"),
                "row": summary.get("row"),
                "parentChunk": summary.get("parentChunk"),
                "split": summary.get("split"),
                "path": str(path),
                "status": overlay.get("status"),
                "activeSubchunkProofData": overlay.get("activeSubchunkProofData"),
                "totals": parent_totals,
                "subchunks": subchunk_work,
            }
        )
        totals["overlays"] += 1
        for key in [
            "subchunks",
            "hRawCenterCoeffAbsFields",
            "hEnvelopeArithmeticFields",
            "hEnvelopeArithmeticPassingFields",
            "hResidualDerivLowerOnCellFields",
            "hResidualDerivUpperOnCellFields",
            "hResidualDerivAbsArithmeticFields",
            "hResidualDerivAbsArithmeticPassingFields",
            "hResidualDerivBoundOnCellFields",
            "firstSubchunkAnchorEnvelopeAdapters",
            "rawCenterCoeffAbsArithmeticObligations",
            "sampleEnvelopeArithmeticObligations",
            "derivativeArithmeticObligations",
            "preferredNormRouteDerivativeAnalyticObligations",
            "preferredNormRouteOpenAnalyticObligations",
            "derivativeAbsArithmeticObligations",
            "openArithmeticObligations",
            "totalArithmeticComparisonsIncludingClosed",
            "sampledEnvelopePassingSubchunks",
            "sampledEnvelopeUnknownSubchunks",
        ]:
            totals[key] += parent_totals[key]

    return {
        "schema": WORKLIST_SCHEMA,
        "status": "direct_proof_input_worklist_address_only",
        "meaning": (
            "Address-only direct proof-input worklist for the remaining analytic "
            "proof fields on covered refined raw-Omega subchunks.  Scalar "
            "hEnvelope arithmetic is separated as exact-passing rational metadata.  "
            "This is not Lean proof data and cannot be imported as a trusted payload."
        ),
        "emitterSource": str(emitter_path),
        "emitterSchema": emitter.get("schema"),
        "leanLandingSurface": CELL_SLOPE_REFINED_PAYLOAD_FIN,
        "downstreamLeanLandingSurface": REFINED_PAYLOAD_FIN,
        "sourceLeanLandingSurface": emitter.get("leanLandingSurface"),
        "activeSubchunkProofData": emitter.get("activeSubchunkProofData"),
        "legacyIntervalSubchunkProofData": emitter.get(
            "legacyIntervalSubchunkProofData"
        ),
        "preferredCellSlopeDirectEndpointConstructor": emitter.get(
            "preferredCellSlopeDirectEndpointConstructor"
        ),
        "preferredDirectNormCertConstructor": (
            RAW_CENTER_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR
        ),
        "endpointDirectNormCertFullCellConstructor": (
            DIRECT_NORM_CERT_FULL_CELL_EXACT_INTEGRAL_CONSTRUCTOR
        ),
        "directNormCertGenericConstructor": (
            DIRECT_NORM_CERT_EXACT_INTEGRAL_CONSTRUCTOR
        ),
        "preferredDirectNormCertFullCellConstructor": (
            RAW_CENTER_DIRECT_NORM_CERT_FULL_CELL_CONSTRUCTOR
        ),
        "directNormIntervalBoundsFullCellConstructor": (
            DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR
        ),
        "endpointDirectNormIntervalBoundsFullCellFallbackConstructor": (
            ENDPOINT_DIRECT_NORM_INTERVAL_BOUNDS_FULL_CELL_CONSTRUCTOR
        ),
        "directNormCert": DIRECT_NORM_CERT,
        "directNormCertValid": DIRECT_NORM_CERT_VALID,
        "directNormCertReceiver": DIRECT_NORM_CERT_RECEIVER,
        "directNormCertValidIntervalReceiver": (
            DIRECT_NORM_CERT_VALID_INTERVAL_RECEIVER
        ),
        "directNormCertValidInterpolationReceiver": (
            DIRECT_NORM_CERT_VALID_INTERPOLATION_RECEIVER
        ),
        "firstSubchunkAnchorEnvelopeIntervalReceiver": (
            FIRST_SUBCHUNK_ANCHOR_ENVELOPE_INTERVAL_RECEIVER
        ),
        "firstSubchunkAnchorEnvelopeProofDataReceiver": (
            FIRST_SUBCHUNK_ANCHOR_ENVELOPE_PROOF_DATA_RECEIVER
        ),
        "requiredFields": REQUIRED_FIELDS,
        "legacyIntervalRequiredFields": LEGACY_INTERVAL_REQUIRED_FIELDS,
        "totals": totals,
        "parents": parents,
        "nextProofProducingTarget": [
            "generate pointwise raw-value lower/upper enclosures and cert.coeff0 comparisons, then close hRawCenterCoeffAbs via raw_center_coeff_abs_of_raw_value_bounds_at; Lean wrapper derives hAnchorResidual",
            "materialize scalar hEnvelope exact rational arithmetic as Lean proof data only during payload emission",
            "generate cancellation-preserving residual-derivative lower/upper interval bounds",
            "preferred compact route: generate one ResidualDerivativeDirectNormCert.Valid proof per direct subchunk",
            "interpolation route: prove exact model-derivative norm and interpolation/error bounds on the same cell, then use ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound",
            "first-subchunk-only fallback: for primary_finite row 0 parent 0 subchunk 0, prove the exact anchor interval, differentiability, second-derivative envelope, and two budget inequalities, then use the concrete anchor-envelope adapter",
            "feed hRawCenterCoeffAbs + DirectNormCert.Valid + cellL=L/cellU=U equalities into the raw-center full-cell direct-norm exact-integral constructor",
            "shortcut compact route: feed hRawCenterCoeffAbs + residual-derivative lower/upper bounds + abs-slope comparisons into the raw-center interval-bounds full-cell direct-norm constructor",
            "fallback: extract hResidualDerivBoundOnCell with residualDerivBoundOnCell_of_directNormCert",
            "materialize derivative abs comparisons as Lean proof data only during payload emission",
            "only then convert this worklist into Lean-checked CellSlopeDirectEnvelopeRefinedPayloadFin data",
            "Lean converts CellSlopeDirectEnvelopeRefinedPayloadFin to RefinedPayloadFin and then to DirectTailWindowInputs",
        ],
        "routeGuard": [
            "address-only worklist",
            "not Lean proof data",
            "proofSafeClosedFields remains zero",
            "sampledEnvelopePasses is diagnostic only; hEnvelopeArithmetic recomputes the rational inequality exactly",
            "do not emit CellSlopeDirectEnvelopeRefinedPayloadFin while hRawCenterCoeffAbs or the preferred direct residual-derivative norm bound is missing",
            "preferred cell-slope route may replace the two interval fields by one hResidualDerivBoundOnCell proof per direct subchunk",
            "interpolation diagnostics are non-proof until model and error bounds are emitted as Lean-checked exact hypotheses",
            "first-subchunk anchor-envelope adapter is concrete to subchunk 0 and must not be generalized across the worklist",
            "do not mutate CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3",
        ],
    }


def render_md(worklist: dict[str, Any]) -> str:
    totals = worklist["totals"]
    lines = [
        "# Step33A.1-A Direct Proof-Input Worklist",
        "",
        "Address-only worklist.  This is not Lean proof data.",
        "",
        "## Summary",
        "",
        f"- schema: `{worklist['schema']}`",
        f"- status: `{worklist['status']}`",
        f"- Lean landing surface: `{worklist['leanLandingSurface']}`",
        f"- downstream Lean landing surface: `{worklist['downstreamLeanLandingSurface']}`",
        f"- active subchunk proof data: `{worklist['activeSubchunkProofData']}`",
        f"- legacy interval subchunk proof data: `{worklist.get('legacyIntervalSubchunkProofData')}`",
        f"- preferred direct-endpoint constructor: `{worklist.get('preferredCellSlopeDirectEndpointConstructor')}`",
        f"- preferred direct-norm cert constructor: `{worklist.get('preferredDirectNormCertConstructor')}`",
        f"- endpoint direct-norm full-cell fallback: `{worklist.get('endpointDirectNormCertFullCellConstructor')}`",
        f"- generic direct-norm cert constructor: `{worklist.get('directNormCertGenericConstructor')}`",
        f"- preferred full-cell direct-norm cert constructor: `{worklist.get('preferredDirectNormCertFullCellConstructor')}`",
        f"- interval-bounds full-cell direct-norm constructor: `{worklist.get('directNormIntervalBoundsFullCellConstructor')}`",
        f"- endpoint interval-bounds full-cell fallback: `{worklist.get('endpointDirectNormIntervalBoundsFullCellFallbackConstructor')}`",
        f"- direct norm cert: `{worklist.get('directNormCert')}`",
        f"- direct norm cert validity: `{worklist.get('directNormCertValid')}`",
        f"- direct norm receiver: `{worklist.get('directNormCertReceiver')}`",
        f"- direct norm interval-valid receiver: `{worklist.get('directNormCertValidIntervalReceiver')}`",
        f"- direct norm interpolation-valid receiver: `{worklist.get('directNormCertValidInterpolationReceiver')}`",
        f"- first-subchunk anchor-envelope interval receiver: `{worklist.get('firstSubchunkAnchorEnvelopeIntervalReceiver')}`",
        f"- first-subchunk anchor-envelope proof-data receiver: `{worklist.get('firstSubchunkAnchorEnvelopeProofDataReceiver')}`",
        f"- overlays: `{totals['overlays']}`",
        f"- subchunks: `{totals['subchunks']}`",
        f"- hRawCenterCoeffAbs fields: `{totals['hRawCenterCoeffAbsFields']}`",
        f"- scalar hEnvelope arithmetic fields: `{totals['hEnvelopeArithmeticFields']}`",
        f"- scalar hEnvelope arithmetic passing: `{totals['hEnvelopeArithmeticPassingFields']}`",
        f"- hResidualDerivLowerOnCell fields: `{totals['hResidualDerivLowerOnCellFields']}`",
        f"- hResidualDerivUpperOnCell fields: `{totals['hResidualDerivUpperOnCellFields']}`",
        f"- preferred hResidualDerivBoundOnCell fields: `{totals['hResidualDerivBoundOnCellFields']}`",
        f"- first-subchunk anchor-envelope adapters: `{totals['firstSubchunkAnchorEnvelopeAdapters']}`",
        f"- derivative abs arithmetic fields: `{totals['hResidualDerivAbsArithmeticFields']}`",
        f"- derivative abs arithmetic passing: `{totals['hResidualDerivAbsArithmeticPassingFields']}`",
        f"- raw-center-coeff abs arithmetic obligations: `{totals['rawCenterCoeffAbsArithmeticObligations']}`",
        f"- scalar hEnvelope arithmetic obligations: `{totals['sampleEnvelopeArithmeticObligations']}`",
        f"- derivative arithmetic obligations: `{totals['derivativeArithmeticObligations']}`",
        f"- preferred norm-route derivative analytic obligations: `{totals['preferredNormRouteDerivativeAnalyticObligations']}`",
        f"- preferred norm-route open analytic obligations: `{totals['preferredNormRouteOpenAnalyticObligations']}`",
        f"- derivative abs arithmetic obligations: `{totals['derivativeAbsArithmeticObligations']}`",
        f"- open arithmetic obligations: `{totals['openArithmeticObligations']}`",
        f"- total arithmetic comparisons including closed: `{totals['totalArithmeticComparisonsIncludingClosed']}`",
        f"- sampled envelope passing subchunks: `{totals['sampledEnvelopePassingSubchunks']}`",
        f"- proof-safe closed fields: `{totals['proofSafeClosedFields']}`",
        "",
        "## Parents",
        "",
        "| family | row | parent | split | subchunks | hRawCenterCoeffAbs | hEnvelope arithmetic | deriv lower | deriv upper | norm bound | deriv abs arithmetic | legacy open | preferred open | sampled pass |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for parent in worklist["parents"]:
        parent_totals = parent["totals"]
        lines.append(
            "| `{family}` | `{row}` | `{parent}` | `{split}` | `{subchunks}` | "
            "`{hanchor}` | `{henv}` | `{hderiv_lower}` | `{hderiv_upper}` | `{hnorm}` | `{hderiv_abs}` | `{arith}` | `{preferred}` | `{sampled}` |".format(
                family=parent["family"],
                row=parent["row"],
                parent=parent["parentChunk"],
                split=parent["split"],
                subchunks=parent_totals["subchunks"],
                hanchor=parent_totals["hRawCenterCoeffAbsFields"],
                henv=parent_totals["hEnvelopeArithmeticPassingFields"],
                hderiv_lower=parent_totals["hResidualDerivLowerOnCellFields"],
                hderiv_upper=parent_totals["hResidualDerivUpperOnCellFields"],
                hnorm=parent_totals["hResidualDerivBoundOnCellFields"],
                hderiv_abs=parent_totals["hResidualDerivAbsArithmeticPassingFields"],
                arith=parent_totals["openArithmeticObligations"],
                preferred=parent_totals["preferredNormRouteOpenAnalyticObligations"],
                sampled=parent_totals["sampledEnvelopePassingSubchunks"],
            )
        )
    lines.extend(["", "## Obligation Shape", ""])
    lines.append(
        "- `hRawCenterCoeffAbs`: prove pointwise raw-value lower/upper enclosures, then use `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_raw_value_bounds_at`; Lean wrapper feeds `hAnchorResidual` into the sample-envelope receiver"
    )
    lines.append(
        "- scalar `hEnvelope`: exact rational comparison "
        "`sampleRadius + max 0 derivSlope * mesh <= remainder`; recorded as passing metadata, not Lean payload"
    )
    lines.append(
        "- `hResidualDerivLowerOnCell` / `hResidualDerivUpperOnCell`: cancellation-preserving direct residual-derivative interval bounds"
    )
    lines.append(
        "- preferred compact route: prove `hRawCenterCoeffAbs`, prove `ResidualDerivativeDirectNormCert.Valid`, prove `cellL = L` and `cellU = U`, then feed those directly into `ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_cert_full_cell`"
    )
    lines.append(
        "- interpolation route for `ResidualDerivativeDirectNormCert.Valid`: prove an exact model-derivative norm bound and exact interpolation/error bound on the same cell, prove their sum is at most `derivSlope`, then use `ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound`"
    )
    lines.append(
        "- first-subchunk-only anchor-envelope fallback: for `primary_finite` row `0`, parent `0`, subchunk `0`, prove the exact anchor interval, differentiability, second-derivative envelope, and rational budget inequalities, then use `primaryFiniteRow0Parent0Split100Sub0_residual_deriv_interval_bounds_of_anchor_envelope`"
    )
    lines.append(
        "- shortcut compact derivative route: prove `hRawCenterCoeffAbs`, residual-derivative lower/upper bounds on `[L, U]`, and the two abs-slope comparisons, then feed them directly into `ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_raw_center_coeff_abs_direct_norm_interval_bounds_full_cell`"
    )
    lines.append(
        "- endpoint fallback compact route: use the endpoint full-cell direct-norm constructor when the payload already has direct endpoint component cert fields"
    )
    lines.append(
        "- lower-level fallback route: use the generic direct-norm constructor with an explicit cell-cover proof, or extract `hResidualDerivBoundOnCell` with `residualDerivBoundOnCell_of_directNormCert` and feed `ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.of_local_direct_endpoint_cert_scale_cell_deriv_bound_at_zero_distance`"
    )
    lines.append(
        "- scalar derivative abs comparisons: exact rational comparisons "
        "`-derivSlope <= derivLower` and `derivUpper <= derivSlope`; recorded as passing metadata, not Lean payload"
    )
    lines.extend(["", "## Next Proof-Producing Target", ""])
    for item in worklist["nextProofProducingTarget"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Guard", ""])
    for item in worklist["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--emitter", type=Path, default=DEFAULT_EMITTER)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    worklist = build_worklist(args.emitter)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(worklist, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(worklist), encoding="utf-8")

    totals = worklist["totals"]
    print(
        "status={status} subchunks={subchunks} legacy_arithmetic={legacy} preferred_open={preferred} out_json={out_json}".format(
            status=worklist["status"],
            subchunks=totals["subchunks"],
            legacy=totals["openArithmeticObligations"],
            preferred=totals["preferredNormRouteOpenAnalyticObligations"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
