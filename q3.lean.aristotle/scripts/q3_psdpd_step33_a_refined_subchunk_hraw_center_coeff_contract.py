#!/usr/bin/env python3
"""Build the local-component proof-input contract for hRawCenterCoeffAbs.

This is a fail-closed Step33A.1-A artifact.  It joins the v4 raw-center
worklist with the v2 local component interval probe and records the exact
arithmetic facts that a future Lean emitter can materialize for

    RawOmegaATaylorModelCertificate.
      raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at

The output is still not Lean proof data: omega/shape interval facts remain
analytic proof obligations.  For zero-distance rows, a checked Lean wrapper
replaces cosine interval facts by the arithmetic checks `cosLower <= 1` and
`1 <= cosUpper`.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_raw_center_coeff_value_bounds_worklist.json"
)
DEFAULT_LOCAL_PROBE = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_local_component_interval_probe.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_hraw_center_coeff_contract.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_hraw_center_coeff_contract.md"
)

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_raw_center_coeff_value_bounds_worklist.v4"
)
LOCAL_PROBE_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_local_component_interval_probe.v2"
)
OUTPUT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_hraw_center_coeff_contract.v11"
)
RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at"
)
ZERO_DISTANCE_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at_zero_distance"
)
COMPACT_COMPONENT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_local_component_cert_scale_interval_corner_bounds_at_zero_distance"
)
COMPACT_ENDPOINT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_local_endpoint_cert_scale_interval_corner_bounds_at_zero_distance"
)
COMPACT_DIRECT_ENDPOINT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance"
)
RAW_CENTER_COEFF_SAMPLE_ENVELOPE_DIRECT_ENDPOINT_CONSTRUCTOR = (
    "RawOmegaATaylorModelCertificate."
    "ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData."
    "of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance"
)
COMPONENT_BALL_CERT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentIntervalCert.of_anchor_abs_bounds"
)
COMPONENT_ANCHOR_DEVIATION_CERT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentIntervalCert.of_anchor_deviation_bounds"
)
COMPONENT_LIPSCHITZ_CERT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentIntervalCert.of_anchor_lipschitz_bounds"
)
COMPONENT_DERIV_CERT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds"
)
COMPONENT_AUTO_DIFF_DERIV_CERT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentIntervalCert."
    "of_anchor_deriv_bounds_auto_differentiability"
)
COMPONENT_INTERVAL_DERIV_CERT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentIntervalCert."
    "of_anchor_deriv_interval_enclosures_auto_differentiability"
)

CORNER_NAMES = [
    "LLLL",
    "LLLU",
    "LLUL",
    "LLUU",
    "LULL",
    "LULU",
    "LUUL",
    "LUUU",
    "ULLL",
    "ULLU",
    "ULUL",
    "ULUU",
    "UULL",
    "UULU",
    "UUUL",
    "UUUU",
]


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


def fraction_from_text(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        return Fraction(text)
    return Fraction(Decimal(text))


def fraction_decimal(value: Fraction) -> str:
    decimal = Decimal(value.numerator) / Decimal(value.denominator)
    return format(decimal, ".18E")


def fraction_literal(value: Fraction) -> str:
    decimal = Decimal(value.numerator) / Decimal(value.denominator)
    return format(decimal, "f")


def decimal_literal(value: Any) -> str:
    return format(Decimal(str(value)), "f")


def interval_center_radius(lower: Fraction, upper: Fraction) -> tuple[Fraction, Fraction]:
    return (lower + upper) / 2, (upper - lower) / 2


def key_of(row: dict[str, Any]) -> tuple[str, int, int, int, int]:
    return (
        str(row["family"]),
        int(row["row"]),
        int(row["parentChunk"]),
        int(row["split"]),
        int(row["subchunk"]),
    )


def flatten_worklist(worklist: dict[str, Any]) -> dict[tuple[str, int, int, int, int], dict[str, Any]]:
    rows: dict[tuple[str, int, int, int, int], dict[str, Any]] = {}
    for parent in worklist.get("parents") or []:
        for entry in parent.get("entries") or []:
            row = dict(entry)
            row.setdefault("family", parent.get("family"))
            row.setdefault("row", parent.get("row"))
            row.setdefault("parentChunk", parent.get("parentChunk"))
            row.setdefault("split", parent.get("split"))
            rows[key_of(row)] = row
    return rows


def corner_product(
    *,
    scale: dict[str, Fraction],
    component: dict[str, Fraction],
    corner: str,
) -> Fraction:
    scale_value = scale["scaleLower"] if corner[0] == "L" else scale["scaleUpper"]
    omega = component["omegaLower"] if corner[1] == "L" else component["omegaUpper"]
    shape = component["shapeSqLower"] if corner[2] == "L" else component["shapeSqUpper"]
    cos = component["cosLower"] if corner[3] == "L" else component["cosUpper"]
    return scale_value * omega * shape * cos


def build_row(
    *,
    work_entry: dict[str, Any],
    probe_row: dict[str, Any],
) -> dict[str, Any]:
    chosen = probe_row.get("chosen")
    if not isinstance(chosen, dict):
        raise ValueError(f"{key_of(probe_row)}: missing chosen local interval")
    component_source = chosen.get("component")
    if not isinstance(component_source, dict):
        raise ValueError(f"{key_of(probe_row)}: missing chosen component box")

    raw_lower = fraction_from_text(work_entry["rawLower"])
    raw_upper = fraction_from_text(work_entry["rawUpper"])
    coeff0 = fraction_from_text(work_entry["coeff0"])
    sample_radius = fraction_from_text(work_entry["sampleRadius"])
    scale = {
        "scaleLower": fraction_from_text(probe_row["scale"]["scaleLower"]),
        "scaleUpper": fraction_from_text(probe_row["scale"]["scaleUpper"]),
    }
    distance = fraction_from_text(probe_row["distance"])
    component = {
        name: fraction_from_text(component_source[name])
        for name in [
            "omegaLower",
            "omegaUpper",
            "shapeSqLower",
            "shapeSqUpper",
            "cosLower",
            "cosUpper",
        ]
    }
    omega_center, omega_radius = interval_center_radius(
        component["omegaLower"],
        component["omegaUpper"],
    )
    shape_center, shape_radius = interval_center_radius(
        component["shapeSqLower"],
        component["shapeSqUpper"],
    )

    corners = []
    for corner in CORNER_NAMES:
        product = corner_product(scale=scale, component=component, corner=corner)
        lower_margin = product - raw_lower
        upper_margin = raw_upper - product
        corners.append(
            {
                "corner": corner,
                "hLower": f"hLower{corner}",
                "hUpper": f"hUpper{corner}",
                "productDecimal": fraction_decimal(product),
                "lowerMarginDecimal": fraction_decimal(lower_margin),
                "upperMarginDecimal": fraction_decimal(upper_margin),
                "lowerPasses": lower_margin >= 0,
                "upperPasses": upper_margin >= 0,
            }
        )

    coeff_lower_margin = raw_lower - coeff0 + sample_radius
    coeff_upper_margin = sample_radius - (raw_upper - coeff0)
    cos_lower_one_margin = Fraction(1) - component["cosLower"]
    cos_upper_one_margin = component["cosUpper"] - Fraction(1)
    a = fraction_from_text(chosen["a"])
    anchor = fraction_from_text(probe_row["anchor"])
    b = fraction_from_text(chosen["b"])
    anchor_membership_passes = a < anchor <= b
    zero_distance = distance == 0
    eta_left_radius = anchor - a
    eta_right_radius = b - anchor
    eta_radius = max(eta_left_radius, eta_right_radius)

    lower_passes = sum(1 for corner in corners if corner["lowerPasses"])
    upper_passes = sum(1 for corner in corners if corner["upperPasses"])
    margin_values = (
        [fraction_from_text(corner["lowerMarginDecimal"]) for corner in corners]
        + [fraction_from_text(corner["upperMarginDecimal"]) for corner in corners]
        + [coeff_lower_margin, coeff_upper_margin, anchor - a, b - anchor]
    )
    if zero_distance:
        margin_values.extend([cos_lower_one_margin, cos_upper_one_margin])
    min_margin = min(margin_values)
    component_interval_proofs = [
        {
            "field": "hOmegaLower",
            "status": "missing_analytic_interval_proof",
            "statement": "∀ eta ∈ Set.Ioc a b, omegaLower <= step22OmegaArchWeight eta",
        },
        {
            "field": "hOmegaUpper",
            "status": "missing_analytic_interval_proof",
            "statement": "∀ eta ∈ Set.Ioc a b, step22OmegaArchWeight eta <= omegaUpper",
        },
        {
            "field": "hShapeSqLower",
            "status": "missing_analytic_interval_proof",
            "statement": "∀ eta ∈ Set.Ioc a b, shapeSqLower <= shapeSq eta",
        },
        {
            "field": "hShapeSqUpper",
            "status": "missing_analytic_interval_proof",
            "statement": "∀ eta ∈ Set.Ioc a b, shapeSq eta <= shapeSqUpper",
        },
    ]
    if not zero_distance:
        component_interval_proofs.extend(
            [
                {
                    "field": "hCosLower",
                    "status": "missing_analytic_interval_proof",
                    "statement": "∀ eta ∈ Set.Ioc a b, cosLower <= Real.cos (eta * x)",
                },
                {
                    "field": "hCosUpper",
                    "status": "missing_analytic_interval_proof",
                    "statement": "∀ eta ∈ Set.Ioc a b, Real.cos (eta * x) <= cosUpper",
                },
            ]
        )
    return {
        "family": probe_row["family"],
        "row": probe_row["row"],
        "parentChunk": probe_row["parentChunk"],
        "split": probe_row["split"],
        "subchunk": probe_row["subchunk"],
        "k": probe_row["k"],
        "ell": probe_row["ell"],
        "distance": probe_row["distance"],
        "receiver": ZERO_DISTANCE_RECEIVER if zero_distance else RECEIVER,
        "compactReceiver": COMPACT_COMPONENT_RECEIVER if zero_distance else None,
        "compactEndpointReceiver": COMPACT_ENDPOINT_RECEIVER if zero_distance else None,
        "compactDirectEndpointReceiver": (
            COMPACT_DIRECT_ENDPOINT_RECEIVER if zero_distance else None
        ),
        "componentBallReceiver": (
            COMPONENT_BALL_CERT_RECEIVER if zero_distance else None
        ),
        "zeroDistance": zero_distance,
        "status": (
            "arithmetic_ready_missing_component_interval_derivative_enclosures"
            if anchor_membership_passes
            and lower_passes == 16
            and upper_passes == 16
            and coeff_lower_margin >= 0
            and coeff_upper_margin >= 0
            and (not zero_distance or cos_lower_one_margin >= 0)
            and (not zero_distance or cos_upper_one_margin >= 0)
            else "arithmetic_failed"
        ),
        "constants": {
            "a": decimal_literal(chosen["a"]),
            "anchor": decimal_literal(probe_row["anchor"]),
            "b": decimal_literal(chosen["b"]),
            "scaleLower": decimal_literal(probe_row["scale"]["scaleLower"]),
            "scaleUpper": decimal_literal(probe_row["scale"]["scaleUpper"]),
            "omegaLower": decimal_literal(component_source["omegaLower"]),
            "omegaUpper": decimal_literal(component_source["omegaUpper"]),
            "shapeSqLower": decimal_literal(component_source["shapeSqLower"]),
            "shapeSqUpper": decimal_literal(component_source["shapeSqUpper"]),
            "cosLower": decimal_literal(component_source["cosLower"]),
            "cosUpper": decimal_literal(component_source["cosUpper"]),
            "rawLower": str(work_entry["rawLower"]),
            "rawUpper": str(work_entry["rawUpper"]),
            "coeff0": str(work_entry["coeff0"]),
            "sampleRadius": str(work_entry["sampleRadius"]),
        },
        "anchorMembership": {
            "field": "hAnchorIn",
            "statement": "anchor ∈ Set.Ioc a b",
            "passesArithmetic": anchor_membership_passes,
            "leftMarginDecimal": fraction_decimal(anchor - a),
            "rightMarginDecimal": fraction_decimal(b - anchor),
            "suggestedProof": "by norm_num",
        },
        "scaleProofs": probe_row.get("scaleProofs"),
        "componentIntervalProofs": component_interval_proofs,
        "componentIntervalCert": {
            "field": "component",
            "type": (
                "RawOmegaATaylorModelCertificate."
                "LocalRawOmegaComponentIntervalCert"
            ),
            "status": "missing_analytic_interval_cert",
            "statement": (
                "LocalRawOmegaComponentIntervalCert k ell a b "
                "omegaLower omegaUpper shapeSqLower shapeSqUpper"
            ),
            "coversFields": [
                "hOmegaLower",
                "hOmegaUpper",
                "hShapeSqLower",
                "hShapeSqUpper",
            ],
        }
        if zero_distance
        else None,
        "componentBallCert": {
            "field": "component",
            "receiver": COMPONENT_BALL_CERT_RECEIVER,
            "status": "missing_analytic_abs_ball_bounds",
            "statement": (
                "LocalRawOmegaComponentIntervalCert.of_anchor_abs_bounds "
                "hOmegaAbs hShapeSqAbs hOmegaLower hOmegaUpper "
                "hShapeSqLower hShapeSqUpper"
            ),
            "parameters": {
                "omegaCenter": str(omega_center),
                "omegaRadius": str(omega_radius),
                "shapeSqCenter": str(shape_center),
                "shapeSqRadius": str(shape_radius),
                "omegaCenterDecimal": fraction_literal(omega_center),
                "omegaRadiusDecimal": fraction_literal(omega_radius),
                "shapeSqCenterDecimal": fraction_literal(shape_center),
                "shapeSqRadiusDecimal": fraction_literal(shape_radius),
            },
            "absFacts": [
                {
                    "field": "hOmegaAbs",
                    "status": "missing_analytic_abs_ball_bound",
                    "statement": (
                        "∀ eta ∈ Set.Ioc a b, "
                        "|step22OmegaArchWeight eta - omegaCenter| "
                        "<= omegaRadius"
                    ),
                },
                {
                    "field": "hShapeSqAbs",
                    "status": "missing_analytic_abs_ball_bound",
                    "statement": (
                        "∀ eta ∈ Set.Ioc a b, "
                        "|shapeSq eta - shapeSqCenter| <= shapeSqRadius"
                    ),
                },
            ],
            "containmentArithmetic": {
                "hOmegaLower": {
                    "statement": "omegaLower <= omegaCenter - omegaRadius",
                    "passes": component["omegaLower"] <= omega_center - omega_radius,
                    "marginDecimal": fraction_decimal(
                        omega_center - omega_radius - component["omegaLower"]
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hOmegaUpper": {
                    "statement": "omegaCenter + omegaRadius <= omegaUpper",
                    "passes": omega_center + omega_radius <= component["omegaUpper"],
                    "marginDecimal": fraction_decimal(
                        component["omegaUpper"] - (omega_center + omega_radius)
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hShapeSqLower": {
                    "statement": "shapeSqLower <= shapeSqCenter - shapeSqRadius",
                    "passes": component["shapeSqLower"] <= shape_center - shape_radius,
                    "marginDecimal": fraction_decimal(
                        shape_center - shape_radius - component["shapeSqLower"]
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hShapeSqUpper": {
                    "statement": "shapeSqCenter + shapeSqRadius <= shapeSqUpper",
                    "passes": shape_center + shape_radius <= component["shapeSqUpper"],
                    "marginDecimal": fraction_decimal(
                        component["shapeSqUpper"] - (shape_center + shape_radius)
                    ),
                    "suggestedProof": "by norm_num",
                },
            },
        }
        if zero_distance
        else None,
        "componentAnchorDeviationCert": {
            "field": "component",
            "receiver": COMPONENT_ANCHOR_DEVIATION_CERT_RECEIVER,
            "status": "missing_analytic_anchor_deviation_bounds",
            "statement": (
                "LocalRawOmegaComponentIntervalCert.of_anchor_deviation_bounds "
                "hOmegaDev hOmegaCenter hOmegaContain hShapeSqDev "
                "hShapeSqCenter hShapeSqContain hOmegaLower hOmegaUpper "
                "hShapeSqLower hShapeSqUpper"
            ),
            "usesBallCertReceiver": COMPONENT_BALL_CERT_RECEIVER,
            "parameters": {
                "omegaCenter": str(omega_center),
                "omegaRadius": str(omega_radius),
                "shapeSqCenter": str(shape_center),
                "shapeSqRadius": str(shape_radius),
                "omegaCenterDecimal": fraction_literal(omega_center),
                "omegaRadiusDecimal": fraction_literal(omega_radius),
                "shapeSqCenterDecimal": fraction_literal(shape_center),
                "shapeSqRadiusDecimal": fraction_literal(shape_radius),
            },
            "analyticFacts": [
                {
                    "field": "hOmegaDev",
                    "status": "missing_analytic_anchor_deviation_bound",
                    "statement": (
                        "∀ eta ∈ Set.Ioc a b, "
                        "|step22OmegaArchWeight eta - "
                        "step22OmegaArchWeight anchor| <= omegaLocalRadius"
                    ),
                },
                {
                    "field": "hOmegaCenter",
                    "status": "missing_anchor_value_enclosure",
                    "statement": (
                        "|step22OmegaArchWeight anchor - omegaCenter| "
                        "<= omegaCenterError"
                    ),
                },
                {
                    "field": "hShapeSqDev",
                    "status": "missing_analytic_anchor_deviation_bound",
                    "statement": (
                        "∀ eta ∈ Set.Ioc a b, "
                        "|shapeSq eta - shapeSq anchor| <= shapeSqLocalRadius"
                    ),
                },
                {
                    "field": "hShapeSqCenter",
                    "status": "missing_anchor_value_enclosure",
                    "statement": (
                        "|shapeSq anchor - shapeSqCenter| <= "
                        "shapeSqCenterError"
                    ),
                },
            ],
            "containmentComparisons": [
                {
                    "field": "hOmegaContain",
                    "status": "waiting_for_local_radius_and_center_error",
                    "statement": (
                        "omegaLocalRadius + omegaCenterError <= omegaRadius"
                    ),
                    "suggestedProof": "by norm_num after generator chooses bounds",
                },
                {
                    "field": "hShapeSqContain",
                    "status": "waiting_for_local_radius_and_center_error",
                    "statement": (
                        "shapeSqLocalRadius + shapeSqCenterError <= "
                        "shapeSqRadius"
                    ),
                    "suggestedProof": "by norm_num after generator chooses bounds",
                },
            ],
        }
        if zero_distance
        else None,
        "componentLipschitzCert": {
            "field": "component",
            "receiver": COMPONENT_LIPSCHITZ_CERT_RECEIVER,
            "status": "missing_analytic_lipschitz_and_anchor_value_bounds",
            "statement": (
                "LocalRawOmegaComponentIntervalCert.of_anchor_lipschitz_bounds "
                "hEtaLeft hEtaRight hOmegaLip hOmegaSlopeNonneg "
                "hOmegaLocalContain hOmegaCenter hOmegaContain hShapeSqLip "
                "hShapeSqSlopeNonneg hShapeSqLocalContain hShapeSqCenter "
                "hShapeSqContain hOmegaLower hOmegaUpper hShapeSqLower "
                "hShapeSqUpper"
            ),
            "usesAnchorDeviationCertReceiver": (
                COMPONENT_ANCHOR_DEVIATION_CERT_RECEIVER
            ),
            "parameters": {
                "etaRadius": str(eta_radius),
                "etaRadiusDecimal": fraction_literal(eta_radius),
                "omegaCenter": str(omega_center),
                "omegaRadius": str(omega_radius),
                "shapeSqCenter": str(shape_center),
                "shapeSqRadius": str(shape_radius),
                "omegaCenterDecimal": fraction_literal(omega_center),
                "omegaRadiusDecimal": fraction_literal(omega_radius),
                "shapeSqCenterDecimal": fraction_literal(shape_center),
                "shapeSqRadiusDecimal": fraction_literal(shape_radius),
            },
            "boundChoicesOpen": [
                {
                    "field": "omegaSlope",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "omegaLocalRadius",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "omegaCenterError",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "shapeSqSlope",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "shapeSqLocalRadius",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "shapeSqCenterError",
                    "status": "generator_must_choose_verified_bound",
                },
            ],
            "analyticFacts": [
                {
                    "field": "hOmegaLip",
                    "status": "missing_analytic_lipschitz_bound",
                    "statement": (
                        "∀ eta ∈ Set.Ioc a b, "
                        "|step22OmegaArchWeight eta - "
                        "step22OmegaArchWeight anchor| <= "
                        "omegaSlope * |eta - anchor|"
                    ),
                },
                {
                    "field": "hOmegaCenter",
                    "status": "missing_anchor_value_enclosure",
                    "statement": (
                        "|step22OmegaArchWeight anchor - omegaCenter| "
                        "<= omegaCenterError"
                    ),
                },
                {
                    "field": "hShapeSqLip",
                    "status": "missing_analytic_lipschitz_bound",
                    "statement": (
                        "∀ eta ∈ Set.Ioc a b, "
                        "|shapeSq eta - shapeSq anchor| <= "
                        "shapeSqSlope * |eta - anchor|"
                    ),
                },
                {
                    "field": "hShapeSqCenter",
                    "status": "missing_anchor_value_enclosure",
                    "statement": (
                        "|shapeSq anchor - shapeSqCenter| <= "
                        "shapeSqCenterError"
                    ),
                },
            ],
            "arithmeticComparisons": {
                "hEtaLeft": {
                    "statement": "anchor - a <= etaRadius",
                    "passes": eta_left_radius <= eta_radius,
                    "marginDecimal": fraction_decimal(
                        eta_radius - eta_left_radius
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hEtaRight": {
                    "statement": "b - anchor <= etaRadius",
                    "passes": eta_right_radius <= eta_radius,
                    "marginDecimal": fraction_decimal(
                        eta_radius - eta_right_radius
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hOmegaSlopeNonneg": {
                    "statement": "0 <= omegaSlope",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hOmegaLocalContain": {
                    "statement": "omegaSlope * etaRadius <= omegaLocalRadius",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hOmegaContain": {
                    "statement": (
                        "omegaLocalRadius + omegaCenterError <= omegaRadius"
                    ),
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqSlopeNonneg": {
                    "statement": "0 <= shapeSqSlope",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqLocalContain": {
                    "statement": "shapeSqSlope * etaRadius <= shapeSqLocalRadius",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqContain": {
                    "statement": (
                        "shapeSqLocalRadius + shapeSqCenterError <= "
                        "shapeSqRadius"
                    ),
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
            },
        }
        if zero_distance
        else None,
        "componentDerivativeCert": {
            "field": "component",
            "receiver": COMPONENT_DERIV_CERT_RECEIVER,
            "status": "missing_analytic_derivative_bounds_and_anchor_values",
            "statement": (
                "LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds "
                "hAnchorIn hEtaLeft hEtaRight hOmegaDifferentiable "
                "hOmegaDerivBound hOmegaSlopeNonneg hOmegaLocalContain "
                "hOmegaCenter hOmegaContain hShapeSqDifferentiable "
                "hShapeSqDerivBound hShapeSqSlopeNonneg "
                "hShapeSqLocalContain hShapeSqCenter hShapeSqContain "
                "hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper"
            ),
            "usesLipschitzCertReceiver": COMPONENT_LIPSCHITZ_CERT_RECEIVER,
            "parameters": {
                "etaRadius": str(eta_radius),
                "etaRadiusDecimal": fraction_literal(eta_radius),
                "omegaCenter": str(omega_center),
                "omegaRadius": str(omega_radius),
                "shapeSqCenter": str(shape_center),
                "shapeSqRadius": str(shape_radius),
                "omegaCenterDecimal": fraction_literal(omega_center),
                "omegaRadiusDecimal": fraction_literal(omega_radius),
                "shapeSqCenterDecimal": fraction_literal(shape_center),
                "shapeSqRadiusDecimal": fraction_literal(shape_radius),
            },
            "boundChoicesOpen": [
                {
                    "field": "omegaSlope",
                    "status": "generator_must_choose_verified_derivative_bound",
                },
                {
                    "field": "omegaLocalRadius",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "omegaCenterError",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "shapeSqSlope",
                    "status": "generator_must_choose_verified_derivative_bound",
                },
                {
                    "field": "shapeSqLocalRadius",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "shapeSqCenterError",
                    "status": "generator_must_choose_verified_bound",
                },
            ],
            "analyticFacts": [
                {
                    "field": "hOmegaDifferentiable",
                    "status": "missing_differentiability_proof",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, DifferentiableAt Real "
                        "step22OmegaArchWeight eta"
                    ),
                },
                {
                    "field": "hOmegaDerivBound",
                    "status": "missing_derivative_bound",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, "
                        "‖deriv step22OmegaArchWeight eta‖ <= omegaSlope"
                    ),
                },
                {
                    "field": "hOmegaCenter",
                    "status": "missing_anchor_value_enclosure",
                    "statement": (
                        "|step22OmegaArchWeight anchor - omegaCenter| "
                        "<= omegaCenterError"
                    ),
                },
                {
                    "field": "hShapeSqDifferentiable",
                    "status": "missing_differentiability_proof",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, DifferentiableAt Real "
                        "(fun t => shapeSq t) eta"
                    ),
                },
                {
                    "field": "hShapeSqDerivBound",
                    "status": "missing_derivative_bound",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, "
                        "‖deriv (fun t => shapeSq t) eta‖ <= shapeSqSlope"
                    ),
                },
                {
                    "field": "hShapeSqCenter",
                    "status": "missing_anchor_value_enclosure",
                    "statement": (
                        "|shapeSq anchor - shapeSqCenter| <= "
                        "shapeSqCenterError"
                    ),
                },
            ],
            "arithmeticComparisons": {
                "hAnchorIn": {
                    "statement": "anchor ∈ Set.Ioc a b",
                    "passes": anchor_membership_passes,
                    "leftMarginDecimal": fraction_decimal(anchor - a),
                    "rightMarginDecimal": fraction_decimal(b - anchor),
                    "suggestedProof": "by norm_num",
                },
                "hEtaLeft": {
                    "statement": "anchor - a <= etaRadius",
                    "passes": eta_left_radius <= eta_radius,
                    "marginDecimal": fraction_decimal(
                        eta_radius - eta_left_radius
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hEtaRight": {
                    "statement": "b - anchor <= etaRadius",
                    "passes": eta_right_radius <= eta_radius,
                    "marginDecimal": fraction_decimal(
                        eta_radius - eta_right_radius
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hOmegaSlopeNonneg": {
                    "statement": "0 <= omegaSlope",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hOmegaLocalContain": {
                    "statement": "omegaSlope * etaRadius <= omegaLocalRadius",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hOmegaContain": {
                    "statement": (
                        "omegaLocalRadius + omegaCenterError <= omegaRadius"
                    ),
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqSlopeNonneg": {
                    "statement": "0 <= shapeSqSlope",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqLocalContain": {
                    "statement": "shapeSqSlope * etaRadius <= shapeSqLocalRadius",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqContain": {
                    "statement": (
                        "shapeSqLocalRadius + shapeSqCenterError <= "
                        "shapeSqRadius"
                    ),
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
            },
        }
        if zero_distance
        else None,
        "componentAutoDiffDerivativeCert": {
            "field": "component",
            "receiver": COMPONENT_AUTO_DIFF_DERIV_CERT_RECEIVER,
            "status": "missing_analytic_derivative_bounds_and_anchor_values",
            "statement": (
                "LocalRawOmegaComponentIntervalCert."
                "of_anchor_deriv_bounds_auto_differentiability "
                "hAnchorIn hEtaLeft hEtaRight hOmegaDerivBound "
                "hOmegaSlopeNonneg hOmegaLocalContain hOmegaCenter "
                "hOmegaContain hShapeSqDerivBound hShapeSqSlopeNonneg "
                "hShapeSqLocalContain hShapeSqCenter hShapeSqContain "
                "hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper"
            ),
            "usesDerivativeCertReceiver": COMPONENT_DERIV_CERT_RECEIVER,
            "closedByLean": [
                {
                    "field": "hOmegaDifferentiable",
                    "receiver": (
                        "CenteredCoeffAnalyticABoundsBackend."
                        "step22OmegaArchWeight_differentiableAt"
                    ),
                },
                {
                    "field": "hShapeSqDifferentiable",
                    "receiver": (
                        "CenteredCoeffAnalyticABoundsBackend."
                        "centeredBSplineImagTransformRealClosedForm_differentiableAt"
                    ),
                },
            ],
            "parameters": {
                "etaRadius": str(eta_radius),
                "etaRadiusDecimal": fraction_literal(eta_radius),
                "omegaCenter": str(omega_center),
                "omegaRadius": str(omega_radius),
                "shapeSqCenter": str(shape_center),
                "shapeSqRadius": str(shape_radius),
                "omegaCenterDecimal": fraction_literal(omega_center),
                "omegaRadiusDecimal": fraction_literal(omega_radius),
                "shapeSqCenterDecimal": fraction_literal(shape_center),
                "shapeSqRadiusDecimal": fraction_literal(shape_radius),
            },
            "boundChoicesOpen": [
                {
                    "field": "omegaSlope",
                    "status": "generator_must_choose_verified_derivative_bound",
                },
                {
                    "field": "omegaLocalRadius",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "omegaCenterError",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "shapeSqSlope",
                    "status": "generator_must_choose_verified_derivative_bound",
                },
                {
                    "field": "shapeSqLocalRadius",
                    "status": "generator_must_choose_verified_bound",
                },
                {
                    "field": "shapeSqCenterError",
                    "status": "generator_must_choose_verified_bound",
                },
            ],
            "analyticFacts": [
                {
                    "field": "hOmegaDerivBound",
                    "status": "missing_derivative_bound",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, "
                        "‖deriv step22OmegaArchWeight eta‖ <= omegaSlope"
                    ),
                },
                {
                    "field": "hOmegaCenter",
                    "status": "missing_anchor_value_enclosure",
                    "statement": (
                        "|step22OmegaArchWeight anchor - omegaCenter| "
                        "<= omegaCenterError"
                    ),
                },
                {
                    "field": "hShapeSqDerivBound",
                    "status": "missing_derivative_bound",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, "
                        "‖deriv (fun t => shapeSq t) eta‖ <= shapeSqSlope"
                    ),
                },
                {
                    "field": "hShapeSqCenter",
                    "status": "missing_anchor_value_enclosure",
                    "statement": (
                        "|shapeSq anchor - shapeSqCenter| <= "
                        "shapeSqCenterError"
                    ),
                },
            ],
            "arithmeticComparisons": {
                "hAnchorIn": {
                    "statement": "anchor ∈ Set.Ioc a b",
                    "passes": anchor_membership_passes,
                    "leftMarginDecimal": fraction_decimal(anchor - a),
                    "rightMarginDecimal": fraction_decimal(b - anchor),
                    "suggestedProof": "by norm_num",
                },
                "hEtaLeft": {
                    "statement": "anchor - a <= etaRadius",
                    "passes": eta_left_radius <= eta_radius,
                    "marginDecimal": fraction_decimal(
                        eta_radius - eta_left_radius
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hEtaRight": {
                    "statement": "b - anchor <= etaRadius",
                    "passes": eta_right_radius <= eta_radius,
                    "marginDecimal": fraction_decimal(
                        eta_radius - eta_right_radius
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hOmegaSlopeNonneg": {
                    "statement": "0 <= omegaSlope",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hOmegaLocalContain": {
                    "statement": "omegaSlope * etaRadius <= omegaLocalRadius",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hOmegaContain": {
                    "statement": (
                        "omegaLocalRadius + omegaCenterError <= omegaRadius"
                    ),
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqSlopeNonneg": {
                    "statement": "0 <= shapeSqSlope",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqLocalContain": {
                    "statement": "shapeSqSlope * etaRadius <= shapeSqLocalRadius",
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
                "hShapeSqContain": {
                    "statement": (
                        "shapeSqLocalRadius + shapeSqCenterError <= "
                        "shapeSqRadius"
                    ),
                    "status": "waiting_for_generator_bound_choice",
                    "suggestedProof": "by norm_num after bound choice",
                },
            },
        }
        if zero_distance
        else None,
        "componentIntervalDerivativeCert": {
            "field": "component",
            "receiver": COMPONENT_INTERVAL_DERIV_CERT_RECEIVER,
            "status": (
                "missing_derivative_and_anchor_endpoint_interval_enclosures"
            ),
            "statement": (
                "LocalRawOmegaComponentIntervalCert."
                "of_anchor_deriv_interval_enclosures_auto_differentiability "
                "hAnchorIn hEtaLeft hEtaRight hOmegaDerivLower "
                "hOmegaDerivUpper hOmegaAnchorLower hOmegaAnchorUpper "
                "hOmegaContain hShapeSqDerivLower hShapeSqDerivUpper "
                "hShapeSqAnchorLower hShapeSqAnchorUpper hShapeSqContain "
                "hOmegaLower hOmegaUpper hShapeSqLower hShapeSqUpper"
            ),
            "usesAutoDiffDerivativeReceiver": (
                COMPONENT_AUTO_DIFF_DERIV_CERT_RECEIVER
            ),
            "autoDefinitions": {
                "omegaSlope": (
                    "intervalAutoAbsBound omegaDerivLower "
                    "omegaDerivUpper"
                ),
                "omegaLocalRadius": "omegaSlope * etaRadius",
                "omegaCenterError": (
                    "intervalAutoCenterError omegaAnchorLower "
                    "omegaAnchorUpper omegaCenter"
                ),
                "shapeSqSlope": (
                    "intervalAutoAbsBound shapeSqDerivLower "
                    "shapeSqDerivUpper"
                ),
                "shapeSqLocalRadius": "shapeSqSlope * etaRadius",
                "shapeSqCenterError": (
                    "intervalAutoCenterError shapeSqAnchorLower "
                    "shapeSqAnchorUpper shapeSqCenter"
                ),
            },
            "closedByLean": [
                {
                    "field": "hOmegaDifferentiable",
                    "receiver": (
                        "CenteredCoeffAnalyticABoundsBackend."
                        "step22OmegaArchWeight_differentiableAt"
                    ),
                },
                {
                    "field": "hShapeSqDifferentiable",
                    "receiver": (
                        "CenteredCoeffAnalyticABoundsBackend."
                        "centeredBSplineImagTransformRealClosedForm_differentiableAt"
                    ),
                },
                {
                    "field": "hOmegaSlopeNonneg",
                    "receiver": "intervalAutoAbsBound_nonneg",
                },
                {
                    "field": "hOmegaLocalContain",
                    "receiver": "le_rfl after omegaLocalRadius auto-definition",
                },
                {
                    "field": "hOmegaCenter",
                    "receiver": (
                        "abs_sub_center_le_intervalAutoCenterError_"
                        "of_interval_bounds"
                    ),
                },
                {
                    "field": "hShapeSqSlopeNonneg",
                    "receiver": "intervalAutoAbsBound_nonneg",
                },
                {
                    "field": "hShapeSqLocalContain",
                    "receiver": (
                        "le_rfl after shapeSqLocalRadius auto-definition"
                    ),
                },
                {
                    "field": "hShapeSqCenter",
                    "receiver": (
                        "abs_sub_center_le_intervalAutoCenterError_"
                        "of_interval_bounds"
                    ),
                },
            ],
            "parameters": {
                "etaRadius": str(eta_radius),
                "etaRadiusDecimal": fraction_literal(eta_radius),
                "omegaCenter": str(omega_center),
                "omegaRadius": str(omega_radius),
                "shapeSqCenter": str(shape_center),
                "shapeSqRadius": str(shape_radius),
                "omegaCenterDecimal": fraction_literal(omega_center),
                "omegaRadiusDecimal": fraction_literal(omega_radius),
                "shapeSqCenterDecimal": fraction_literal(shape_center),
                "shapeSqRadiusDecimal": fraction_literal(shape_radius),
            },
            "endpointFactsOpen": [
                {
                    "field": "hOmegaDerivLower",
                    "status": "missing_derivative_lower_enclosure",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, omegaDerivLower <= "
                        "deriv step22OmegaArchWeight eta"
                    ),
                },
                {
                    "field": "hOmegaDerivUpper",
                    "status": "missing_derivative_upper_enclosure",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, "
                        "deriv step22OmegaArchWeight eta <= omegaDerivUpper"
                    ),
                },
                {
                    "field": "hOmegaAnchorLower",
                    "status": "missing_anchor_value_lower_enclosure",
                    "statement": (
                        "omegaAnchorLower <= step22OmegaArchWeight anchor"
                    ),
                },
                {
                    "field": "hOmegaAnchorUpper",
                    "status": "missing_anchor_value_upper_enclosure",
                    "statement": (
                        "step22OmegaArchWeight anchor <= omegaAnchorUpper"
                    ),
                },
                {
                    "field": "hShapeSqDerivLower",
                    "status": "missing_derivative_lower_enclosure",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, shapeSqDerivLower <= "
                        "deriv (fun t => shapeSq t) eta"
                    ),
                },
                {
                    "field": "hShapeSqDerivUpper",
                    "status": "missing_derivative_upper_enclosure",
                    "statement": (
                        "∀ eta ∈ Set.Icc a b, "
                        "deriv (fun t => shapeSq t) eta <= "
                        "shapeSqDerivUpper"
                    ),
                },
                {
                    "field": "hShapeSqAnchorLower",
                    "status": "missing_anchor_value_lower_enclosure",
                    "statement": "shapeSqAnchorLower <= shapeSq anchor",
                },
                {
                    "field": "hShapeSqAnchorUpper",
                    "status": "missing_anchor_value_upper_enclosure",
                    "statement": "shapeSq anchor <= shapeSqAnchorUpper",
                },
            ],
            "arithmeticComparisons": {
                "hAnchorIn": {
                    "statement": "anchor ∈ Set.Ioc a b",
                    "passes": anchor_membership_passes,
                    "leftMarginDecimal": fraction_decimal(anchor - a),
                    "rightMarginDecimal": fraction_decimal(b - anchor),
                    "suggestedProof": "by norm_num",
                },
                "hEtaLeft": {
                    "statement": "anchor - a <= etaRadius",
                    "passes": eta_left_radius <= eta_radius,
                    "marginDecimal": fraction_decimal(
                        eta_radius - eta_left_radius
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hEtaRight": {
                    "statement": "b - anchor <= etaRadius",
                    "passes": eta_right_radius <= eta_radius,
                    "marginDecimal": fraction_decimal(
                        eta_radius - eta_right_radius
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hOmegaContain": {
                    "statement": (
                        "intervalAutoAbsBound omegaDerivLower "
                        "omegaDerivUpper * etaRadius + "
                        "intervalAutoCenterError omegaAnchorLower "
                        "omegaAnchorUpper omegaCenter <= omegaRadius"
                    ),
                    "status": "waiting_for_generator_endpoint_choices",
                    "suggestedProof": "by norm_num after endpoint choices",
                },
                "hShapeSqContain": {
                    "statement": (
                        "intervalAutoAbsBound shapeSqDerivLower "
                        "shapeSqDerivUpper * etaRadius + "
                        "intervalAutoCenterError shapeSqAnchorLower "
                        "shapeSqAnchorUpper shapeSqCenter <= shapeSqRadius"
                    ),
                    "status": "waiting_for_generator_endpoint_choices",
                    "suggestedProof": "by norm_num after endpoint choices",
                },
                "hOmegaLower": {
                    "statement": "omegaLower <= omegaCenter - omegaRadius",
                    "passes": component["omegaLower"] <= omega_center - omega_radius,
                    "marginDecimal": fraction_decimal(
                        (omega_center - omega_radius) - component["omegaLower"]
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hOmegaUpper": {
                    "statement": "omegaCenter + omegaRadius <= omegaUpper",
                    "passes": omega_center + omega_radius <= component["omegaUpper"],
                    "marginDecimal": fraction_decimal(
                        component["omegaUpper"] - (omega_center + omega_radius)
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hShapeSqLower": {
                    "statement": (
                        "shapeSqLower <= shapeSqCenter - shapeSqRadius"
                    ),
                    "passes": (
                        component["shapeSqLower"] <= shape_center - shape_radius
                    ),
                    "marginDecimal": fraction_decimal(
                        (shape_center - shape_radius) -
                        component["shapeSqLower"]
                    ),
                    "suggestedProof": "by norm_num",
                },
                "hShapeSqUpper": {
                    "statement": (
                        "shapeSqCenter + shapeSqRadius <= shapeSqUpper"
                    ),
                    "passes": (
                        shape_center + shape_radius <= component["shapeSqUpper"]
                    ),
                    "marginDecimal": fraction_decimal(
                        component["shapeSqUpper"] -
                        (shape_center + shape_radius)
                    ),
                    "suggestedProof": "by norm_num",
                },
            },
        }
        if zero_distance
        else None,
        "cosArithmetic": {
            "enabledByZeroDistanceReceiver": zero_distance,
            "hCosLowerOne": {
                "statement": "cosLower <= 1",
                "passes": (not zero_distance) or cos_lower_one_margin >= 0,
                "marginDecimal": fraction_decimal(cos_lower_one_margin),
                "suggestedProof": "by norm_num",
            },
            "hCosUpperOne": {
                "statement": "1 <= cosUpper",
                "passes": (not zero_distance) or cos_upper_one_margin >= 0,
                "marginDecimal": fraction_decimal(cos_upper_one_margin),
                "suggestedProof": "by norm_num",
            },
        },
        "cornerArithmetic": {
            "lowerPassing": lower_passes,
            "upperPassing": upper_passes,
            "totalPassing": lower_passes + upper_passes,
            "totalComparisons": 32,
            "corners": corners,
        },
        "coeffArithmetic": {
            "hCoeffLower": {
                "statement": "-sampleRadius <= rawLower - coeff0",
                "passes": coeff_lower_margin >= 0,
                "marginDecimal": fraction_decimal(coeff_lower_margin),
                "suggestedProof": "by norm_num",
            },
            "hCoeffUpper": {
                "statement": "rawUpper - coeff0 <= sampleRadius",
                "passes": coeff_upper_margin >= 0,
                "marginDecimal": fraction_decimal(coeff_upper_margin),
                "suggestedProof": "by norm_num",
            },
        },
        "minArithmeticMarginDecimal": fraction_decimal(min_margin),
    }


def build_contract(args: argparse.Namespace) -> dict[str, Any]:
    getcontext().prec = args.decimal_prec
    worklist = load_json(args.worklist)
    validate_schema(worklist, path=args.worklist, schema=WORKLIST_SCHEMA)
    probe = load_json(args.local_probe)
    validate_schema(probe, path=args.local_probe, schema=LOCAL_PROBE_SCHEMA)

    work_rows = flatten_worklist(worklist)
    rows = []
    for probe_row in probe.get("rows") or []:
        key = key_of(probe_row)
        if key not in work_rows:
            raise ValueError(f"local probe row missing in worklist: {key}")
        rows.append(build_row(work_entry=work_rows[key], probe_row=probe_row))

    status_counts = Counter(row["status"] for row in rows)
    family_counts = Counter(row["family"] for row in rows)
    corner_total = sum(row["cornerArithmetic"]["totalComparisons"] for row in rows)
    corner_passing = sum(row["cornerArithmetic"]["totalPassing"] for row in rows)
    coeff_total = 2 * len(rows)
    coeff_passing = sum(
        int(row["coeffArithmetic"]["hCoeffLower"]["passes"])
        + int(row["coeffArithmetic"]["hCoeffUpper"]["passes"])
        for row in rows
    )
    anchor_passing = sum(
        int(row["anchorMembership"]["passesArithmetic"]) for row in rows
    )
    component_open = sum(len(row["componentIntervalProofs"]) for row in rows)
    zero_distance_rows = sum(int(row["zeroDistance"]) for row in rows)
    cos_total = sum(2 for row in rows if row["zeroDistance"])
    cos_passing = sum(
        int(row["cosArithmetic"]["hCosLowerOne"]["passes"])
        + int(row["cosArithmetic"]["hCosUpperOne"]["passes"])
        for row in rows
        if row["zeroDistance"]
    )
    arithmetic_ready = status_counts.get(
        "arithmetic_ready_missing_component_interval_derivative_enclosures", 0
    )
    compact_cert_open = sum(int(row["componentIntervalCert"] is not None) for row in rows)
    ball_cert_rows = [row for row in rows if row["componentBallCert"] is not None]
    ball_cert_open = len(ball_cert_rows)
    ball_abs_open = sum(len(row["componentBallCert"]["absFacts"]) for row in ball_cert_rows)
    ball_containment_total = sum(
        len(row["componentBallCert"]["containmentArithmetic"])
        for row in ball_cert_rows
    )
    ball_containment_passing = sum(
        int(item["passes"])
        for row in ball_cert_rows
        for item in row["componentBallCert"]["containmentArithmetic"].values()
    )
    anchor_deviation_cert_rows = [
        row for row in rows if row["componentAnchorDeviationCert"] is not None
    ]
    anchor_deviation_cert_open = len(anchor_deviation_cert_rows)
    anchor_deviation_analytic_open = sum(
        len(row["componentAnchorDeviationCert"]["analyticFacts"])
        for row in anchor_deviation_cert_rows
    )
    anchor_deviation_containment_open = sum(
        len(row["componentAnchorDeviationCert"]["containmentComparisons"])
        for row in anchor_deviation_cert_rows
    )
    lipschitz_cert_rows = [
        row for row in rows if row["componentLipschitzCert"] is not None
    ]
    lipschitz_cert_open = len(lipschitz_cert_rows)
    lipschitz_bound_choices_open = sum(
        len(row["componentLipschitzCert"]["boundChoicesOpen"])
        for row in lipschitz_cert_rows
    )
    lipschitz_analytic_open = sum(
        len(row["componentLipschitzCert"]["analyticFacts"])
        for row in lipschitz_cert_rows
    )
    lipschitz_endpoint_total = 2 * len(lipschitz_cert_rows)
    lipschitz_endpoint_passing = sum(
        int(row["componentLipschitzCert"]["arithmeticComparisons"]["hEtaLeft"]["passes"])
        + int(row["componentLipschitzCert"]["arithmeticComparisons"]["hEtaRight"]["passes"])
        for row in lipschitz_cert_rows
    )
    lipschitz_bound_arithmetic_open = 6 * len(lipschitz_cert_rows)
    derivative_cert_rows = [
        row for row in rows if row["componentDerivativeCert"] is not None
    ]
    derivative_cert_open = len(derivative_cert_rows)
    derivative_bound_choices_open = sum(
        len(row["componentDerivativeCert"]["boundChoicesOpen"])
        for row in derivative_cert_rows
    )
    derivative_analytic_open = sum(
        len(row["componentDerivativeCert"]["analyticFacts"])
        for row in derivative_cert_rows
    )
    derivative_anchor_endpoint_total = 3 * len(derivative_cert_rows)
    derivative_anchor_endpoint_passing = sum(
        int(row["componentDerivativeCert"]["arithmeticComparisons"]["hAnchorIn"]["passes"])
        + int(row["componentDerivativeCert"]["arithmeticComparisons"]["hEtaLeft"]["passes"])
        + int(row["componentDerivativeCert"]["arithmeticComparisons"]["hEtaRight"]["passes"])
        for row in derivative_cert_rows
    )
    derivative_bound_arithmetic_open = 6 * len(derivative_cert_rows)
    auto_diff_derivative_cert_rows = [
        row for row in rows if row["componentAutoDiffDerivativeCert"] is not None
    ]
    auto_diff_derivative_cert_open = len(auto_diff_derivative_cert_rows)
    auto_diff_closed_by_lean = sum(
        len(row["componentAutoDiffDerivativeCert"]["closedByLean"])
        for row in auto_diff_derivative_cert_rows
    )
    auto_diff_bound_choices_open = sum(
        len(row["componentAutoDiffDerivativeCert"]["boundChoicesOpen"])
        for row in auto_diff_derivative_cert_rows
    )
    auto_diff_analytic_open = sum(
        len(row["componentAutoDiffDerivativeCert"]["analyticFacts"])
        for row in auto_diff_derivative_cert_rows
    )
    auto_diff_anchor_endpoint_total = 3 * len(auto_diff_derivative_cert_rows)
    auto_diff_anchor_endpoint_passing = sum(
        int(row["componentAutoDiffDerivativeCert"]["arithmeticComparisons"]["hAnchorIn"]["passes"])
        + int(row["componentAutoDiffDerivativeCert"]["arithmeticComparisons"]["hEtaLeft"]["passes"])
        + int(row["componentAutoDiffDerivativeCert"]["arithmeticComparisons"]["hEtaRight"]["passes"])
        for row in auto_diff_derivative_cert_rows
    )
    auto_diff_bound_arithmetic_open = 6 * len(auto_diff_derivative_cert_rows)
    interval_derivative_cert_rows = [
        row for row in rows if row["componentIntervalDerivativeCert"] is not None
    ]
    interval_derivative_cert_open = len(interval_derivative_cert_rows)
    interval_derivative_closed_by_lean = sum(
        len(row["componentIntervalDerivativeCert"]["closedByLean"])
        for row in interval_derivative_cert_rows
    )
    interval_derivative_endpoint_open = sum(
        len(row["componentIntervalDerivativeCert"]["endpointFactsOpen"])
        for row in interval_derivative_cert_rows
    )
    interval_derivative_arithmetic_total = 9 * len(interval_derivative_cert_rows)
    interval_derivative_arithmetic_passing = sum(
        int(row["componentIntervalDerivativeCert"]["arithmeticComparisons"][name]["passes"])
        for row in interval_derivative_cert_rows
        for name in [
            "hAnchorIn",
            "hEtaLeft",
            "hEtaRight",
            "hOmegaLower",
            "hOmegaUpper",
            "hShapeSqLower",
            "hShapeSqUpper",
        ]
    )
    interval_derivative_containment_open = 2 * len(interval_derivative_cert_rows)
    return {
        "schema": OUTPUT_SCHEMA,
        "status": (
            "arithmetic_ready_missing_component_interval_derivative_enclosures_not_lean_proof"
            if arithmetic_ready == len(rows)
            else "arithmetic_failures_not_lean_proof"
        ),
        "meaning": (
            "Fail-closed contract for hRawCenterCoeffAbs local component "
            "receiver inputs.  Arithmetic constants are checked here for "
            "emitter readiness; analytic omega/shape interval proofs remain "
            "open.  Zero-distance rows use a checked Lean wrapper that "
            "replaces cosine interval proofs by cosLower <= 1 <= cosUpper."
        ),
        "worklist": str(args.worklist),
        "worklistSchema": worklist.get("schema"),
        "localProbe": str(args.local_probe),
        "localProbeSchema": probe.get("schema"),
        "receiver": RECEIVER,
        "zeroDistanceReceiver": ZERO_DISTANCE_RECEIVER,
        "compactComponentReceiver": COMPACT_COMPONENT_RECEIVER,
        "compactEndpointReceiver": COMPACT_ENDPOINT_RECEIVER,
        "compactDirectEndpointReceiver": COMPACT_DIRECT_ENDPOINT_RECEIVER,
        "rawCenterCoeffSampleEnvelopeDirectEndpointConstructor": (
            RAW_CENTER_COEFF_SAMPLE_ENVELOPE_DIRECT_ENDPOINT_CONSTRUCTOR
        ),
        "componentBallCertReceiver": COMPONENT_BALL_CERT_RECEIVER,
        "componentAnchorDeviationCertReceiver": (
            COMPONENT_ANCHOR_DEVIATION_CERT_RECEIVER
        ),
        "componentLipschitzCertReceiver": COMPONENT_LIPSCHITZ_CERT_RECEIVER,
        "componentDerivativeCertReceiver": COMPONENT_DERIV_CERT_RECEIVER,
        "componentAutoDiffDerivativeCertReceiver": (
            COMPONENT_AUTO_DIFF_DERIV_CERT_RECEIVER
        ),
        "componentIntervalDerivativeCertReceiver": (
            COMPONENT_INTERVAL_DERIV_CERT_RECEIVER
        ),
        "totals": {
            "rows": len(rows),
            "rowsByFamily": dict(sorted(family_counts.items())),
            "arithmeticReadyRows": arithmetic_ready,
            "arithmeticFailedRows": len(rows) - arithmetic_ready,
            "anchorMembershipPassing": anchor_passing,
            "zeroDistanceRows": zero_distance_rows,
            "scaleProofReferences": 2 * len(rows),
            "cosArithmeticComparisons": cos_total,
            "cosArithmeticPassing": cos_passing,
            "componentIntervalProofsOpen": component_open,
            "componentIntervalCertsOpen": compact_cert_open,
            "compactComponentRows": compact_cert_open,
            "componentBallCertsOpen": ball_cert_open,
            "componentBallAbsFactsOpen": ball_abs_open,
            "componentBallContainmentComparisons": ball_containment_total,
            "componentBallContainmentPassing": ball_containment_passing,
            "componentAnchorDeviationCertsOpen": anchor_deviation_cert_open,
            "componentAnchorDeviationAnalyticFactsOpen": (
                anchor_deviation_analytic_open
            ),
            "componentAnchorDeviationContainmentComparisonsOpen": (
                anchor_deviation_containment_open
            ),
            "componentLipschitzCertsOpen": lipschitz_cert_open,
            "componentLipschitzBoundChoicesOpen": lipschitz_bound_choices_open,
            "componentLipschitzAnalyticFactsOpen": lipschitz_analytic_open,
            "componentLipschitzEndpointComparisons": lipschitz_endpoint_total,
            "componentLipschitzEndpointComparisonsPassing": (
                lipschitz_endpoint_passing
            ),
            "componentLipschitzBoundArithmeticComparisonsOpen": (
                lipschitz_bound_arithmetic_open
            ),
            "componentDerivativeCertsOpen": derivative_cert_open,
            "componentDerivativeBoundChoicesOpen": derivative_bound_choices_open,
            "componentDerivativeAnalyticFactsOpen": derivative_analytic_open,
            "componentDerivativeAnchorEndpointComparisons": (
                derivative_anchor_endpoint_total
            ),
            "componentDerivativeAnchorEndpointComparisonsPassing": (
                derivative_anchor_endpoint_passing
            ),
            "componentDerivativeBoundArithmeticComparisonsOpen": (
                derivative_bound_arithmetic_open
            ),
            "componentAutoDiffDerivativeCertsOpen": (
                auto_diff_derivative_cert_open
            ),
            "componentAutoDiffClosedByLean": auto_diff_closed_by_lean,
            "componentAutoDiffDerivativeBoundChoicesOpen": (
                auto_diff_bound_choices_open
            ),
            "componentAutoDiffDerivativeAnalyticFactsOpen": (
                auto_diff_analytic_open
            ),
            "componentAutoDiffDerivativeAnchorEndpointComparisons": (
                auto_diff_anchor_endpoint_total
            ),
            "componentAutoDiffDerivativeAnchorEndpointComparisonsPassing": (
                auto_diff_anchor_endpoint_passing
            ),
            "componentAutoDiffDerivativeBoundArithmeticComparisonsOpen": (
                auto_diff_bound_arithmetic_open
            ),
            "componentIntervalDerivativeCertsOpen": (
                interval_derivative_cert_open
            ),
            "componentIntervalDerivativeClosedByLean": (
                interval_derivative_closed_by_lean
            ),
            "componentIntervalDerivativeEndpointFactsOpen": (
                interval_derivative_endpoint_open
            ),
            "componentIntervalDerivativeArithmeticComparisons": (
                interval_derivative_arithmetic_total
            ),
            "componentIntervalDerivativeArithmeticComparisonsPassing": (
                interval_derivative_arithmetic_passing
            ),
            "componentIntervalDerivativeContainmentComparisonsOpen": (
                interval_derivative_containment_open
            ),
            "cornerArithmeticComparisons": corner_total,
            "cornerArithmeticPassing": corner_passing,
            "coeffArithmeticComparisons": coeff_total,
            "coeffArithmeticPassing": coeff_passing,
            "proofSafeClosedFields": 0,
        },
        "worstArithmeticRow": min(
            rows, key=lambda row: Decimal(row["minArithmeticMarginDecimal"])
        )
        if rows
        else None,
        "rows": rows,
        "routeGuard": [
            "not Lean proof data",
            "component interval proofs remain analytic obligations",
            "zero-distance rows expose one LocalRawOmegaComponentIntervalCert obligation instead of four scattered top-level omega/shape fields",
            "LocalRawOmegaComponentIntervalCert can now be built from two abs ball bounds plus four norm_num containment comparisons",
            "preferred v4 route builds those abs ball bounds from anchor-deviation and anchor-value enclosures",
            "preferred v5 route builds anchor-deviation from local Lipschitz bounds plus endpoint-radius arithmetic",
            "preferred v6 route builds Lipschitz bounds from derivative bounds on Set.Icc a b",
            "preferred v7 route discharges component differentiability via existing backend differentiability lemmas",
            "preferred v8 route converts derivative and anchor endpoint intervals into Lean-computed slope/error bounds",
            "arithmetic readiness only means future Lean emitter should be able to use norm_num on these constants",
            "uses d29_pi_p30_decimal_bounds scale mode",
            "does not emit RefinedPayloadFin",
            "does not touch CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3",
        ],
    }


def render_md(contract: dict[str, Any]) -> str:
    totals = contract["totals"]
    lines = [
        "# Step33A.1-A hRawCenterCoeffAbs Local Component Contract",
        "",
        "Fail-closed contract only.  This is not Lean proof data.",
        "",
        "## Summary",
        "",
        f"- schema: `{contract['schema']}`",
        f"- status: `{contract['status']}`",
        f"- receiver: `{contract['receiver']}`",
        f"- zero-distance receiver: `{contract['zeroDistanceReceiver']}`",
        f"- compact component receiver: `{contract['compactComponentReceiver']}`",
        f"- compact endpoint receiver: `{contract['compactEndpointReceiver']}`",
        f"- compact direct endpoint receiver: `{contract['compactDirectEndpointReceiver']}`",
        "- raw-center sample-envelope direct endpoint constructor: "
        f"`{contract['rawCenterCoeffSampleEnvelopeDirectEndpointConstructor']}`",
        f"- component ball cert receiver: `{contract['componentBallCertReceiver']}`",
        f"- component anchor-deviation cert receiver: `{contract['componentAnchorDeviationCertReceiver']}`",
        f"- component Lipschitz cert receiver: `{contract['componentLipschitzCertReceiver']}`",
        f"- component derivative cert receiver: `{contract['componentDerivativeCertReceiver']}`",
        f"- component auto-diff derivative cert receiver: `{contract['componentAutoDiffDerivativeCertReceiver']}`",
        f"- component interval-derivative cert receiver: `{contract['componentIntervalDerivativeCertReceiver']}`",
        f"- rows: `{totals['rows']}`",
        f"- arithmetic-ready rows: `{totals['arithmeticReadyRows']}`",
        f"- arithmetic-failed rows: `{totals['arithmeticFailedRows']}`",
        f"- anchor memberships passing: `{totals['anchorMembershipPassing']}`",
        f"- zero-distance rows: `{totals['zeroDistanceRows']}`",
        f"- scale proof references: `{totals['scaleProofReferences']}`",
        f"- cos arithmetic passing: `{totals['cosArithmeticPassing']} / {totals['cosArithmeticComparisons']}`",
        f"- component interval proofs open: `{totals['componentIntervalProofsOpen']}`",
        f"- component interval certs open: `{totals['componentIntervalCertsOpen']}`",
        f"- compact component rows: `{totals['compactComponentRows']}`",
        f"- component ball certs open: `{totals['componentBallCertsOpen']}`",
        f"- component ball abs facts open: `{totals['componentBallAbsFactsOpen']}`",
        f"- component ball containment passing: `{totals['componentBallContainmentPassing']} / {totals['componentBallContainmentComparisons']}`",
        f"- component anchor-deviation certs open: `{totals['componentAnchorDeviationCertsOpen']}`",
        f"- component anchor-deviation analytic facts open: `{totals['componentAnchorDeviationAnalyticFactsOpen']}`",
        f"- component anchor-deviation containment comparisons open: `{totals['componentAnchorDeviationContainmentComparisonsOpen']}`",
        f"- component Lipschitz certs open: `{totals['componentLipschitzCertsOpen']}`",
        f"- component Lipschitz bound choices open: `{totals['componentLipschitzBoundChoicesOpen']}`",
        f"- component Lipschitz analytic facts open: `{totals['componentLipschitzAnalyticFactsOpen']}`",
        f"- component Lipschitz endpoint arithmetic passing: `{totals['componentLipschitzEndpointComparisonsPassing']} / {totals['componentLipschitzEndpointComparisons']}`",
        f"- component Lipschitz bound arithmetic comparisons open: `{totals['componentLipschitzBoundArithmeticComparisonsOpen']}`",
        f"- component derivative certs open: `{totals['componentDerivativeCertsOpen']}`",
        f"- component derivative bound choices open: `{totals['componentDerivativeBoundChoicesOpen']}`",
        f"- component derivative analytic facts open: `{totals['componentDerivativeAnalyticFactsOpen']}`",
        f"- component derivative anchor/endpoint arithmetic passing: `{totals['componentDerivativeAnchorEndpointComparisonsPassing']} / {totals['componentDerivativeAnchorEndpointComparisons']}`",
        f"- component derivative bound arithmetic comparisons open: `{totals['componentDerivativeBoundArithmeticComparisonsOpen']}`",
        f"- component auto-diff derivative certs open: `{totals['componentAutoDiffDerivativeCertsOpen']}`",
        f"- component auto-diff fields closed by Lean: `{totals['componentAutoDiffClosedByLean']}`",
        f"- component auto-diff derivative bound choices open: `{totals['componentAutoDiffDerivativeBoundChoicesOpen']}`",
        f"- component auto-diff derivative analytic facts open: `{totals['componentAutoDiffDerivativeAnalyticFactsOpen']}`",
        f"- component auto-diff derivative anchor/endpoint arithmetic passing: `{totals['componentAutoDiffDerivativeAnchorEndpointComparisonsPassing']} / {totals['componentAutoDiffDerivativeAnchorEndpointComparisons']}`",
        f"- component auto-diff derivative bound arithmetic comparisons open: `{totals['componentAutoDiffDerivativeBoundArithmeticComparisonsOpen']}`",
        f"- component interval-derivative certs open: `{totals['componentIntervalDerivativeCertsOpen']}`",
        f"- component interval-derivative fields closed by Lean: `{totals['componentIntervalDerivativeClosedByLean']}`",
        f"- component interval-derivative endpoint facts open: `{totals['componentIntervalDerivativeEndpointFactsOpen']}`",
        f"- component interval-derivative arithmetic passing: `{totals['componentIntervalDerivativeArithmeticComparisonsPassing']} / {totals['componentIntervalDerivativeArithmeticComparisons']}`",
        f"- component interval-derivative containment comparisons open: `{totals['componentIntervalDerivativeContainmentComparisonsOpen']}`",
        f"- corner arithmetic passing: `{totals['cornerArithmeticPassing']} / {totals['cornerArithmeticComparisons']}`",
        f"- coeff arithmetic passing: `{totals['coeffArithmeticPassing']} / {totals['coeffArithmeticComparisons']}`",
        f"- proof-safe closed fields: `{totals['proofSafeClosedFields']}`",
        "",
        "## Rows By Family",
        "",
        "| family | rows |",
        "| --- | ---: |",
    ]
    for family, count in totals["rowsByFamily"].items():
        lines.append(f"| `{family}` | `{count}` |")
    worst = contract.get("worstArithmeticRow")
    if worst:
        lines.extend(
            [
                "",
                "## Worst Arithmetic Row",
                "",
                f"- family: `{worst['family']}`",
                f"- row: `{worst['row']}`",
                f"- parent chunk: `{worst['parentChunk']}`",
                f"- subchunk: `{worst['subchunk']}`",
                f"- status: `{worst['status']}`",
                f"- min arithmetic margin: `{worst['minArithmeticMarginDecimal']}`",
            ]
        )
    lines.extend(
        [
            "",
            "## Open Analytic Fields Per Row",
            "",
            "```text",
            "hOmegaLower",
            "hOmegaUpper",
            "hShapeSqLower",
            "hShapeSqUpper",
            "```",
            "",
            "These four fields are now grouped per zero-distance row by",
            "`LocalRawOmegaComponentIntervalCert`; the underlying analytic work is",
            "unchanged, but the payload-facing interface is one cert per row.",
            "",
            "The preferred proof-producing route for those certs is now",
            "`LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_auto_differentiability`:",
            "generated code proves ordinary two-sided endpoint intervals for",
            "the Omega derivative, Omega anchor value, shape-square derivative,",
            "and shape-square anchor value.  Lean converts those intervals into",
            "nonnegative derivative slopes, local-radius definitions, and",
            "center-error balls, then feeds",
            "`of_anchor_deriv_bounds_auto_differentiability` internally.",
            "",
            "For zero-distance rows, cosine fields are handled by the checked",
            "`raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`",
            "wrapper using the generated direct endpoint package plus",
            "`cosLower <= 1` and `1 <= cosUpper`.",
            "",
            "## Guard",
            "",
        ]
    )
    for item in contract["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--local-probe", type=Path, default=DEFAULT_LOCAL_PROBE)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--decimal-prec", type=int, default=180)
    args = parser.parse_args()

    contract = build_contract(args)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(contract, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.write_text(render_md(contract), encoding="utf-8")
    print(
        "hraw_center_coeff_contract: "
        f"rows={contract['totals']['rows']} "
        f"arithmetic_ready={contract['totals']['arithmeticReadyRows']} "
        f"component_open={contract['totals']['componentIntervalProofsOpen']} "
        f"out={args.out_json}"
    )


if __name__ == "__main__":
    main()
