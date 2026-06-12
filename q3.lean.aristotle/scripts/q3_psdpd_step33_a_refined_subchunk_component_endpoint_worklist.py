#!/usr/bin/env python3
"""Build endpoint interval obligations for the v19 endpoint receiver.

This is a fail-closed Step33A.1-A artifact.  It consumes the v11
`hRawCenterCoeffAbs` contract and computes Arb/acb-backed candidate intervals
for the endpoint facts required by

    LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds

The output is not Lean proof data.  It records direct endpoint derivative and
anchor value intervals, then checks the two rational containment comparisons
that will become `by norm_num` after a later Lean emitter materializes the
endpoint facts.  v19 uses the corrected closed-form shape route: endpoint rows
bound `E` and the checked closed-form derivative receiver for `E'`, derive
`E^2` derivative bounds by four corner comparisons for `2 * E * E'`, and then
instantiate the independent Omega and shape-square endpoint packages before the
row constructor.  Anchor endpoint facts are widened by rational proof pads
capped by the available containment slack, so they do not assert exact rational
values of transcendental functions.
v20 keeps raw Arb Omega derivative intervals as audit data, but uses a local
relaxed proof target `0 <= omega' <= 2` for the generated Omega endpoint
facts.  This is deliberate: endpoint containment depends on an absolute slope
times the tiny local eta radius, so the relaxed derivative target keeps all
containment rows passing while avoiding a proof-data path that tries to certify
irrelevant 1e-21 derivative widths.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

try:
    from flint import acb, arb
except ImportError as exc:  # pragma: no cover - environment guard
    raise SystemExit(
        "python-flint is required. Run from the repo root with:\n"
        "  ./.venv/bin/python q3.lean.aristotle/scripts/"
        "q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.py"
    ) from exc

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    set_precision,
    spline_packet_ball,
)
from q3_psdpd_step22_arch_interval import sinc_acb


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_CONTRACT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_hraw_center_coeff_contract.json"
)
DEFAULT_LOCAL_PROBE = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_local_component_interval_probe.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_component_endpoint_worklist.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_component_endpoint_worklist.md"
)

CONTRACT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_hraw_center_coeff_contract.v11"
)
LOCAL_PROBE_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_local_component_interval_probe.v2"
)
OUTPUT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.v21"
)
ENDPOINT_MODE = "closed_form_shape_value_deriv_endpoint"
ANCHOR_PROOF_PAD = Fraction(1, 10**21)
SHAPE_ANCHOR_VALUE_PROOF_PAD = Fraction(1, 10**90)
OMEGA_DERIVATIVE_PROOF_MODE = "relaxed_positive_abs_slope_interval"
OMEGA_DERIVATIVE_RELAXED_LOWER = Fraction(0)
OMEGA_DERIVATIVE_RELAXED_UPPER = Fraction(2)
RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentDirectEndpointIntervalCert."
    "of_omega_shape_endpoint_bounds"
)
ENDPOINT_CERT = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentDirectEndpointIntervalCert"
)
ENDPOINT_CERT_RECEIVER = (
    "RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert."
    "toComponentIntervalCert"
)
SHAPE_SQ_DERIVATIVE_REDUCTION = (
    "RawOmegaATaylorModelCertificate."
    "deriv_centeredBSplineImagTransformRealClosedForm_sq"
)
SHAPE_SQ_DERIVATIVE_INTERVAL_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "shapeSqDeriv_interval_bounds_of_closedForm_value_deriv_intervals"
)
SHAPE_SQ_DERIVATIVE_Icc_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "shapeSqDeriv_interval_bounds_on_Icc_of_closedForm_value_deriv_intervals"
)
LOCAL_COMPONENT_SHAPE_RECEIVER = (
    "RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert."
    "of_anchor_deriv_interval_enclosures_shapeSq_closedForm_auto_differentiability"
)
OMEGA_ENDPOINT_CERT = (
    "RawOmegaATaylorModelCertificate.Step22OmegaEndpointIntervalCert"
)
LOCAL_COMPONENT_OMEGA_SHAPE_RECEIVER = (
    "RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert."
    "of_omega_endpoint_cert_shapeSq_closedForm_auto_differentiability"
)
LOCAL_COMPONENT_CLOSED_FORM_ENDPOINT_CERT = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentClosedFormEndpointIntervalCert"
)
LOCAL_COMPONENT_CLOSED_FORM_ENDPOINT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentClosedFormEndpointIntervalCert."
    "toComponentIntervalCert"
)
LOCAL_COMPONENT_RAW_ENDPOINT_CERT = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentEndpointIntervalCert"
)
LOCAL_COMPONENT_RAW_ENDPOINT_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentEndpointIntervalCert.toComponentIntervalCert"
)
OMEGA_ENDPOINT_CLOSED_FORM_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeight_endpointValueDerivIntervalCert_of_closedForm_bounds"
)
OMEGA_CLOSED_FORM_ENDPOINT_BOUNDS_CERT = (
    "RawOmegaATaylorModelCertificate."
    "Step22OmegaClosedFormEndpointBoundsCert"
)
OMEGA_CLOSED_FORM_ENDPOINT_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "Step22OmegaClosedFormEndpointBoundsCert."
    "toStep22OmegaEndpointIntervalCert"
)
SHAPE_SQ_ENDPOINT_BOUNDS_CERT = (
    "RawOmegaATaylorModelCertificate.ShapeSqEndpointBoundsCert"
)
SHAPE_SQ_ENDPOINT_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals"
)
SHAPE_SQ_ENDPOINT_BOUNDS_ANCHOR_VALUE_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "ShapeSqEndpointBoundsCert."
    "of_closedForm_value_derivClosedForm_intervals_anchorValueBounds"
)
LOCAL_COMPONENT_DIRECT_ENDPOINT_FROM_OMEGA_SHAPE_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "LocalRawOmegaComponentDirectEndpointIntervalCert."
    "of_omega_shape_endpoint_bounds"
)
OMEGA_DERIV_CLOSED_FORM = (
    "RawOmegaATaylorModelCertificate.step22OmegaArchWeightDerivClosedForm"
)
OMEGA_DERIV_CLOSED_FORM_THEOREM = (
    "RawOmegaATaylorModelCertificate.step22OmegaArchWeight_deriv_eq_closedForm"
)
OMEGA_DERIV_CLOSED_FORM_Icc_THEOREM = (
    "RawOmegaATaylorModelCertificate.step22OmegaArchWeight_deriv_eq_closedForm_on_Icc"
)
SHAPE_DERIV_CLOSED_FORM = (
    "RawOmegaATaylorModelCertificate."
    "centeredBSplineImagTransformRealClosedFormDerivClosedForm"
)
SHAPE_DERIV_CLOSED_FORM_THEOREM = (
    "RawOmegaATaylorModelCertificate."
    "centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm"
)
SHAPE_DERIV_CLOSED_FORM_Icc_THEOREM = (
    "RawOmegaATaylorModelCertificate."
    "centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm_on_Icc"
)


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


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        return Fraction(text)
    return Fraction(Decimal(text))


def decimal_to_fraction(value: Decimal) -> Fraction:
    return Fraction(value)


def rational_string(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def fraction_decimal(value: Fraction) -> str:
    decimal = Decimal(value.numerator) / Decimal(value.denominator)
    return format(decimal, ".30E")


def decimal_payload(value: Decimal | Fraction) -> str:
    if isinstance(value, Fraction):
        value = Decimal(value.numerator) / Decimal(value.denominator)
    return format(value, ".90E")


def endpoint_payload(value: Decimal) -> dict[str, str]:
    fraction = decimal_to_fraction(value)
    return {
        "decimal": decimal_payload(value),
        "rational": rational_string(fraction),
    }


def endpoint_payload_fraction(value: Fraction) -> dict[str, str]:
    return {
        "decimal": decimal_payload(value),
        "rational": rational_string(value),
    }


def interval_payload_fraction(lower: Fraction, upper: Fraction) -> dict[str, Any]:
    return {
        "lower": endpoint_payload_fraction(lower),
        "upper": endpoint_payload_fraction(upper),
        "widthDecimal": fraction_decimal(upper - lower),
    }


def arb_interval_from_endpoints(a: Fraction, b: Fraction) -> acb:
    if b < a:
        raise ValueError(f"invalid interval endpoints: {a} > {b}")
    mid = (a + b) / 2
    radius = (b - a) / 2
    return acb(arb(str(Decimal(mid.numerator) / Decimal(mid.denominator)),
                   str(Decimal(radius.numerator) / Decimal(radius.denominator))))


def arb_point(value: Fraction) -> acb:
    return acb(arb(str(Decimal(value.numerator) / Decimal(value.denominator))))


def sinc_series_deriv_acb(x: acb, terms: int) -> acb:
    total = acb(0)
    x2 = x * x
    power = acb(1)
    for n in range(1, terms):
        coeff = arb((-1) ** n * (2 * n)) / arb(math.factorial(2 * n + 1))
        total += acb(coeff) * power
        power *= x2
    return x * total


class ComponentEndpointEvaluator:
    def __init__(self, *, sinc_terms: int) -> None:
        self.sinc_terms = sinc_terms
        self.log_pi = arb.pi().log()
        self.i_unit = acb(0, 1)

    def omega_value(self, eta: acb) -> arb:
        z = acb(arb("0.25")) + self.i_unit * eta / acb(2)
        return z.digamma().real - self.log_pi

    def omega_derivative(self, eta: acb) -> arb:
        z = acb(arb("0.25")) + self.i_unit * eta / acb(2)
        dz_deta = self.i_unit / acb(2)
        return (z.polygamma(1) * dz_deta).real

    def shape_sq_value(self, *, k: int, ell: Fraction, eta: acb) -> arb:
        return self.shape_value(k=k, ell=ell, eta=eta).real

    def shape_closed_form_value(self, *, k: int, ell: Fraction, eta: acb) -> acb:
        s_k, c_k = spline_packet_ball(k)
        ell_acb = acb(arb(str(Decimal(ell.numerator) / Decimal(ell.denominator))))
        shape_arg = ell_acb * eta / (acb(2) * acb(s_k))
        return (
            acb((arb(1) / (s_k * c_k)).sqrt())
            * (sinc_acb(shape_arg, self.sinc_terms) ** (k + 1))
        )

    def shape_closed_form_derivative(
        self, *, k: int, ell: Fraction, eta: acb
    ) -> acb:
        s_k, c_k = spline_packet_ball(k)
        ell_acb = acb(arb(str(Decimal(ell.numerator) / Decimal(ell.denominator))))
        x_scale = ell_acb / (acb(2) * acb(s_k))
        shape_arg = x_scale * eta
        sinc = sinc_acb(shape_arg, self.sinc_terms)
        sinc_deriv_eta = sinc_series_deriv_acb(shape_arg, self.sinc_terms) * x_scale
        return (
            acb((arb(1) / (s_k * c_k)).sqrt())
            * acb(k + 1)
            * (sinc ** k)
            * sinc_deriv_eta
        )

    def shape_value(self, *, k: int, ell: Fraction, eta: acb) -> acb:
        s_k, c_k = spline_packet_ball(k)
        ell_acb = acb(arb(str(Decimal(ell.numerator) / Decimal(ell.denominator))))
        shape_arg = ell_acb * eta / (acb(2) * acb(s_k))
        return (
            acb(arb(1) / (s_k * c_k))
            * (sinc_acb(shape_arg, self.sinc_terms) ** (2 * k + 2))
        )

    def shape_derivative(self, *, k: int, ell: Fraction, eta: acb) -> acb:
        s_k, c_k = spline_packet_ball(k)
        ell_acb = acb(arb(str(Decimal(ell.numerator) / Decimal(ell.denominator))))
        x_scale = ell_acb / (acb(2) * acb(s_k))
        shape_arg = x_scale * eta
        power = 2 * k + 2
        sinc = sinc_acb(shape_arg, self.sinc_terms)
        sinc_deriv_eta = sinc_series_deriv_acb(shape_arg, self.sinc_terms) * x_scale
        return (
            acb(arb(1) / (s_k * c_k))
            * acb(power)
            * (sinc ** (power - 1))
            * sinc_deriv_eta
        )

    def shape_sq_derivative(self, *, k: int, ell: Fraction, eta: acb) -> arb:
        return self.shape_derivative(k=k, ell=ell, eta=eta).real


def interval_auto_abs_bound(lower: Fraction, upper: Fraction) -> Fraction:
    return max(Fraction(0), max(-lower, upper))


def interval_auto_center_error(
    lower: Fraction,
    upper: Fraction,
    center: Fraction,
) -> Fraction:
    return max(Fraction(0), max(center - lower, upper - center))


def interval_from_arb(value: arb) -> tuple[Decimal, Decimal]:
    return arb_lower_decimal(value), arb_upper_decimal(value)


def interval_payload(lower: Decimal, upper: Decimal) -> dict[str, Any]:
    lower_fraction = decimal_to_fraction(lower)
    upper_fraction = decimal_to_fraction(upper)
    return {
        "lower": endpoint_payload(lower),
        "upper": endpoint_payload(upper),
        "widthDecimal": fraction_decimal(upper_fraction - lower_fraction),
    }


def corner_interval_payload(corners: list[Fraction]) -> dict[str, Any]:
    lower = min(corners)
    upper = max(corners)
    return {
        "lower": {
            "decimal": decimal_payload(lower),
            "rational": rational_string(lower),
        },
        "upper": {
            "decimal": decimal_payload(upper),
            "rational": rational_string(upper),
        },
        "corners": {
            "LL": rational_string(corners[0]),
            "LU": rational_string(corners[1]),
            "UL": rational_string(corners[2]),
            "UU": rational_string(corners[3]),
        },
        "widthDecimal": fraction_decimal(upper - lower),
    }


def fact_payload(
    *,
    field: str,
    statement: str,
    endpoint: str,
    value: Decimal,
) -> dict[str, str]:
    return {
        "field": field,
        "statement": statement,
        "endpoint": endpoint,
        "candidateDecimal": decimal_payload(value),
        "candidateRational": rational_string(decimal_to_fraction(value)),
        "status": "candidate_interval_generated_not_lean_proof",
    }


def fact_payload_fraction(
    *,
    field: str,
    statement: str,
    endpoint: str,
    value: Fraction,
) -> dict[str, str]:
    return {
        "field": field,
        "statement": statement,
        "endpoint": endpoint,
        "candidateDecimal": decimal_payload(value),
        "candidateRational": rational_string(value),
        "status": "candidate_interval_generated_not_lean_proof",
    }


def anchor_proof_pad(margin: Fraction) -> Fraction:
    if margin <= 0:
        return Fraction(0)
    return min(ANCHOR_PROOF_PAD, margin / 4)


def shape_anchor_value_proof_pad(shape_sq_anchor_pad: Fraction) -> Fraction:
    if shape_sq_anchor_pad <= 0:
        return Fraction(0)
    return min(SHAPE_ANCHOR_VALUE_PROOF_PAD, shape_sq_anchor_pad / 1000)


def build_row(
    *,
    row: dict[str, Any],
    evaluator: ComponentEndpointEvaluator,
) -> dict[str, Any]:
    cert = row.get("componentIntervalDerivativeCert")
    if not isinstance(cert, dict):
        raise ValueError(f"row {row.get('row')}: missing componentIntervalDerivativeCert")
    params = cert.get("parameters")
    if not isinstance(params, dict):
        raise ValueError(f"row {row.get('row')}: missing componentIntervalDerivativeCert.parameters")
    constants = row.get("constants")
    if not isinstance(constants, dict):
        raise ValueError(f"row {row.get('row')}: missing constants")

    a = parse_fraction(constants["a"])
    anchor = parse_fraction(constants["anchor"])
    b = parse_fraction(constants["b"])
    eta_radius = parse_fraction(params["etaRadius"])
    omega_center = parse_fraction(params["omegaCenter"])
    omega_radius = parse_fraction(params["omegaRadius"])
    shape_sq_center = parse_fraction(params["shapeSqCenter"])
    shape_sq_radius = parse_fraction(params["shapeSqRadius"])
    ell = parse_fraction(row["ell"])
    k = int(row["k"])

    eta_interval = arb_interval_from_endpoints(a, b)
    eta_anchor = arb_point(anchor)

    omega_deriv_raw_lower, omega_deriv_raw_upper = interval_from_arb(
        evaluator.omega_derivative(eta_interval)
    )
    omega_anchor_lower, omega_anchor_upper = interval_from_arb(
        evaluator.omega_value(eta_anchor)
    )
    shape_closed_value_lower, shape_closed_value_upper = interval_from_arb(
        evaluator.shape_closed_form_value(k=k, ell=ell, eta=eta_interval).real
    )
    shape_closed_deriv_lower, shape_closed_deriv_upper = interval_from_arb(
        evaluator.shape_closed_form_derivative(k=k, ell=ell, eta=eta_interval).real
    )
    shape_anchor_value_lower, shape_anchor_value_upper = interval_from_arb(
        evaluator.shape_closed_form_value(k=k, ell=ell, eta=eta_anchor).real
    )
    shape_sq_value_probe_lower, shape_sq_value_probe_upper = interval_from_arb(
        evaluator.shape_value(k=k, ell=ell, eta=eta_interval).real
    )
    shape_sq_deriv_probe_lower, shape_sq_deriv_probe_upper = interval_from_arb(
        evaluator.shape_derivative(k=k, ell=ell, eta=eta_interval).real
    )
    shape_sq_deriv_direct_lower, shape_sq_deriv_direct_upper = interval_from_arb(
        evaluator.shape_sq_derivative(k=k, ell=ell, eta=eta_interval)
    )
    shape_sq_anchor_lower, shape_sq_anchor_upper = interval_from_arb(
        evaluator.shape_sq_value(k=k, ell=ell, eta=eta_anchor)
    )

    omega_deriv_raw_lower_q = decimal_to_fraction(omega_deriv_raw_lower)
    omega_deriv_raw_upper_q = decimal_to_fraction(omega_deriv_raw_upper)
    omega_deriv_lower_q = OMEGA_DERIVATIVE_RELAXED_LOWER
    omega_deriv_upper_q = OMEGA_DERIVATIVE_RELAXED_UPPER
    omega_deriv_lower = (
        Decimal(omega_deriv_lower_q.numerator)
        / Decimal(omega_deriv_lower_q.denominator)
    )
    omega_deriv_upper = (
        Decimal(omega_deriv_upper_q.numerator)
        / Decimal(omega_deriv_upper_q.denominator)
    )
    omega_anchor_lower_q = decimal_to_fraction(omega_anchor_lower)
    omega_anchor_upper_q = decimal_to_fraction(omega_anchor_upper)
    shape_closed_value_lower_q = decimal_to_fraction(shape_closed_value_lower)
    shape_closed_value_upper_q = decimal_to_fraction(shape_closed_value_upper)
    shape_closed_deriv_lower_q = decimal_to_fraction(shape_closed_deriv_lower)
    shape_closed_deriv_upper_q = decimal_to_fraction(shape_closed_deriv_upper)
    shape_anchor_value_lower_q = decimal_to_fraction(shape_anchor_value_lower)
    shape_anchor_value_upper_q = decimal_to_fraction(shape_anchor_value_upper)
    shape_sq_value_probe_lower_q = decimal_to_fraction(shape_sq_value_probe_lower)
    shape_sq_value_probe_upper_q = decimal_to_fraction(shape_sq_value_probe_upper)
    shape_sq_deriv_probe_lower_q = decimal_to_fraction(shape_sq_deriv_probe_lower)
    shape_sq_deriv_probe_upper_q = decimal_to_fraction(shape_sq_deriv_probe_upper)
    shape_sq_deriv_direct_lower_q = decimal_to_fraction(
        shape_sq_deriv_direct_lower
    )
    shape_sq_deriv_direct_upper_q = decimal_to_fraction(
        shape_sq_deriv_direct_upper
    )
    shape_sq_deriv_corners = [
        2 * shape_closed_value_lower_q * shape_closed_deriv_lower_q,
        2 * shape_closed_value_lower_q * shape_closed_deriv_upper_q,
        2 * shape_closed_value_upper_q * shape_closed_deriv_lower_q,
        2 * shape_closed_value_upper_q * shape_closed_deriv_upper_q,
    ]
    shape_sq_deriv_corner_lower_q = min(shape_sq_deriv_corners)
    shape_sq_deriv_corner_upper_q = max(shape_sq_deriv_corners)
    shape_sq_deriv_lower_q = shape_sq_deriv_corner_lower_q
    shape_sq_deriv_upper_q = shape_sq_deriv_corner_upper_q
    shape_sq_anchor_lower_q = decimal_to_fraction(shape_sq_anchor_lower)
    shape_sq_anchor_upper_q = decimal_to_fraction(shape_sq_anchor_upper)

    shape_sq_slope = interval_auto_abs_bound(
        shape_sq_deriv_lower_q,
        shape_sq_deriv_upper_q,
    )
    omega_slope = interval_auto_abs_bound(omega_deriv_lower_q, omega_deriv_upper_q)
    omega_center_error = interval_auto_center_error(
        omega_anchor_lower_q,
        omega_anchor_upper_q,
        omega_center,
    )
    shape_sq_center_error = interval_auto_center_error(
        shape_sq_anchor_lower_q,
        shape_sq_anchor_upper_q,
        shape_sq_center,
    )
    omega_consumed = omega_slope * eta_radius + omega_center_error
    shape_sq_consumed = shape_sq_slope * eta_radius + shape_sq_center_error
    omega_margin = omega_radius - omega_consumed
    shape_sq_margin = shape_sq_radius - shape_sq_consumed

    omega_anchor_pad = anchor_proof_pad(omega_margin)
    shape_sq_anchor_pad = anchor_proof_pad(shape_sq_margin)
    shape_anchor_value_pad = shape_anchor_value_proof_pad(shape_sq_anchor_pad)
    omega_anchor_lower_q -= omega_anchor_pad
    omega_anchor_upper_q += omega_anchor_pad
    shape_sq_anchor_lower_q -= shape_sq_anchor_pad
    shape_sq_anchor_upper_q += shape_sq_anchor_pad
    shape_anchor_value_lower_q -= shape_anchor_value_pad
    shape_anchor_value_upper_q += shape_anchor_value_pad

    omega_center_error = interval_auto_center_error(
        omega_anchor_lower_q,
        omega_anchor_upper_q,
        omega_center,
    )
    shape_sq_center_error = interval_auto_center_error(
        shape_sq_anchor_lower_q,
        shape_sq_anchor_upper_q,
        shape_sq_center,
    )
    omega_consumed = omega_slope * eta_radius + omega_center_error
    shape_sq_consumed = shape_sq_slope * eta_radius + shape_sq_center_error
    omega_margin = omega_radius - omega_consumed
    shape_sq_margin = shape_sq_radius - shape_sq_consumed

    omega_passes = omega_margin >= 0
    shape_sq_passes = shape_sq_margin >= 0

    endpoint_facts = [
        fact_payload(
            field="hOmegaDerivLower",
            statement=(
                "∀ eta ∈ Set.Icc a b, omegaDerivLower <= "
                "step22OmegaArchWeightDerivClosedForm eta"
            ),
            endpoint="omegaDerivLower",
            value=omega_deriv_lower,
        ),
        fact_payload(
            field="hOmegaDerivUpper",
            statement=(
                "∀ eta ∈ Set.Icc a b, "
                "step22OmegaArchWeightDerivClosedForm eta <= omegaDerivUpper"
            ),
            endpoint="omegaDerivUpper",
            value=omega_deriv_upper,
        ),
        fact_payload_fraction(
            field="hOmegaAnchorLower",
            statement="omegaAnchorLower <= step22OmegaArchWeight anchor",
            endpoint="omegaAnchorLower",
            value=omega_anchor_lower_q,
        ),
        fact_payload_fraction(
            field="hOmegaAnchorUpper",
            statement="step22OmegaArchWeight anchor <= omegaAnchorUpper",
            endpoint="omegaAnchorUpper",
            value=omega_anchor_upper_q,
        ),
        fact_payload(
            field="hShapeValueLower",
            statement=(
                "∀ eta ∈ Set.Icc a b, shapeValueLower <= "
                "centeredBSplineImagTransformRealClosedForm k ell eta"
            ),
            endpoint="shapeValueLower",
            value=shape_closed_value_lower,
        ),
        fact_payload(
            field="hShapeValueUpper",
            statement=(
                "∀ eta ∈ Set.Icc a b, "
                "centeredBSplineImagTransformRealClosedForm k ell eta <= shapeValueUpper"
            ),
            endpoint="shapeValueUpper",
            value=shape_closed_value_upper,
        ),
        fact_payload(
            field="hShapeDerivLower",
            statement=(
                "∀ eta ∈ Set.Icc a b, shapeDerivLower <= "
                "centeredBSplineImagTransformRealClosedFormDerivClosedForm k ell eta"
            ),
            endpoint="shapeDerivLower",
            value=shape_closed_deriv_lower,
        ),
        fact_payload(
            field="hShapeDerivUpper",
            statement=(
                "∀ eta ∈ Set.Icc a b, "
                "centeredBSplineImagTransformRealClosedFormDerivClosedForm k ell eta "
                "<= shapeDerivUpper"
            ),
            endpoint="shapeDerivUpper",
            value=shape_closed_deriv_upper,
        ),
        fact_payload_fraction(
            field="hShapeAnchorValueLower",
            statement=(
                "shapeAnchorValueLower <= "
                "centeredBSplineImagTransformRealClosedForm k ell anchor"
            ),
            endpoint="shapeAnchorValueLower",
            value=shape_anchor_value_lower_q,
        ),
        fact_payload_fraction(
            field="hShapeAnchorValueUpper",
            statement=(
                "centeredBSplineImagTransformRealClosedForm k ell anchor "
                "<= shapeAnchorValueUpper"
            ),
            endpoint="shapeAnchorValueUpper",
            value=shape_anchor_value_upper_q,
        ),
        fact_payload_fraction(
            field="hShapeSqAnchorLower",
            statement="shapeSqAnchorLower <= shapeSq anchor",
            endpoint="shapeSqAnchorLower",
            value=shape_sq_anchor_lower_q,
        ),
        fact_payload_fraction(
            field="hShapeSqAnchorUpper",
            statement="shapeSq anchor <= shapeSqAnchorUpper",
            endpoint="shapeSqAnchorUpper",
            value=shape_sq_anchor_upper_q,
        ),
    ]

    return {
        "family": row["family"],
        "row": row["row"],
        "parentChunk": row["parentChunk"],
        "split": row["split"],
        "subchunk": row["subchunk"],
        "k": k,
        "ell": row["ell"],
        "distance": row["distance"],
        "receiver": RECEIVER,
        "endpointMode": ENDPOINT_MODE,
        "endpointCertType": ENDPOINT_CERT,
        "endpointCertReceiver": ENDPOINT_CERT_RECEIVER,
        "status": (
            "endpoint_candidates_containment_passed_not_lean_proof"
            if omega_passes and shape_sq_passes
            else "endpoint_candidates_containment_failed_not_lean_proof"
        ),
        "interval": {
            "a": rational_string(a),
            "anchor": rational_string(anchor),
            "b": rational_string(b),
            "etaRadius": rational_string(eta_radius),
            "aDecimal": fraction_decimal(a),
            "anchorDecimal": fraction_decimal(anchor),
            "bDecimal": fraction_decimal(b),
            "etaRadiusDecimal": fraction_decimal(eta_radius),
        },
        "parameters": {
            "omegaCenter": rational_string(omega_center),
            "omegaRadius": rational_string(omega_radius),
            "shapeSqCenter": rational_string(shape_sq_center),
            "shapeSqRadius": rational_string(shape_sq_radius),
            "omegaCenterDecimal": fraction_decimal(omega_center),
            "omegaRadiusDecimal": fraction_decimal(omega_radius),
            "shapeSqCenterDecimal": fraction_decimal(shape_sq_center),
            "shapeSqRadiusDecimal": fraction_decimal(shape_sq_radius),
        },
        "endpointIntervals": {
            "omegaDerivative": interval_payload(
                omega_deriv_lower,
                omega_deriv_upper,
            ),
            "omegaDerivativeRawProbeAuditOnly": interval_payload(
                omega_deriv_raw_lower,
                omega_deriv_raw_upper,
            ),
            "omegaAnchor": interval_payload(
                omega_anchor_lower,
                omega_anchor_upper,
            ),
            "omegaAnchorProof": interval_payload_fraction(
                omega_anchor_lower_q,
                omega_anchor_upper_q,
            ),
            "shapeSqDerivative": interval_payload(
                Decimal(shape_sq_deriv_corner_lower_q.numerator)
                / Decimal(shape_sq_deriv_corner_lower_q.denominator),
                Decimal(shape_sq_deriv_corner_upper_q.numerator)
                / Decimal(shape_sq_deriv_corner_upper_q.denominator),
            ),
            "shapeValue": interval_payload(
                shape_closed_value_lower,
                shape_closed_value_upper,
            ),
            "shapeDerivative": interval_payload(
                shape_closed_deriv_lower,
                shape_closed_deriv_upper,
            ),
            "shapeAnchorValue": interval_payload(
                shape_anchor_value_lower,
                shape_anchor_value_upper,
            ),
            "shapeAnchorValueProof": interval_payload_fraction(
                shape_anchor_value_lower_q,
                shape_anchor_value_upper_q,
            ),
            "shapeSqValueProbeAuditOnly": interval_payload(
                shape_sq_value_probe_lower,
                shape_sq_value_probe_upper,
            ),
            "shapeSqDerivativeDirectProbeAuditOnly": interval_payload(
                shape_sq_deriv_direct_lower,
                shape_sq_deriv_direct_upper,
            ),
            "shapeSqDerivativeHelperProbeAuditOnly": interval_payload(
                shape_sq_deriv_probe_lower,
                shape_sq_deriv_probe_upper,
            ),
            "shapeSqDerivativeCorners": corner_interval_payload(
                shape_sq_deriv_corners
            ),
            "shapeSqAnchor": interval_payload(
                shape_sq_anchor_lower,
                shape_sq_anchor_upper,
            ),
            "shapeSqAnchorProof": interval_payload_fraction(
                shape_sq_anchor_lower_q,
                shape_sq_anchor_upper_q,
            ),
        },
        "shapeSqDerivativeCornerComparisons": {
            "statement": (
                "Active corrected shape lift.  The generated shape endpoint "
                "route proves E and checked closed-form E' intervals, then "
                "derives E^2 derivative bounds from the four corners of "
                "2 * E * E'."
            ),
            "status": "active_closed_form_shape_route",
            "reason": (
                "v19 uses separate closed-form E and checked closed-form E' "
                "interval probes.  The older v11 issue came from feeding an "
                "already squared value into the 2 * E * E' corner lift."
            ),
            "corners": {
                "LL": rational_string(shape_sq_deriv_corners[0]),
                "LU": rational_string(shape_sq_deriv_corners[1]),
                "UL": rational_string(shape_sq_deriv_corners[2]),
                "UU": rational_string(shape_sq_deriv_corners[3]),
            },
            "directProbeContained": (
                shape_sq_deriv_corner_lower_q <= shape_sq_deriv_direct_lower_q
                and shape_sq_deriv_direct_upper_q <= shape_sq_deriv_corner_upper_q
            ),
            "directProbeLower": rational_string(shape_sq_deriv_direct_lower_q),
            "directProbeUpper": rational_string(shape_sq_deriv_direct_upper_q),
            "lower": rational_string(shape_sq_deriv_corner_lower_q),
            "upper": rational_string(shape_sq_deriv_corner_upper_q),
        },
        "directShapeSqDerivativeEndpointRoute": {
            "status": "audit_only_direct_probe",
            "lower": rational_string(shape_sq_deriv_direct_lower_q),
            "upper": rational_string(shape_sq_deriv_direct_upper_q),
            "receiver": ENDPOINT_CERT_RECEIVER,
        },
        "autoDefinitions": {
            "omegaDerivativeProofMode": OMEGA_DERIVATIVE_PROOF_MODE,
            "omegaDerivativeRawLower": rational_string(omega_deriv_raw_lower_q),
            "omegaDerivativeRawUpper": rational_string(omega_deriv_raw_upper_q),
            "omegaDerivativeRelaxedLower": rational_string(
                OMEGA_DERIVATIVE_RELAXED_LOWER
            ),
            "omegaDerivativeRelaxedUpper": rational_string(
                OMEGA_DERIVATIVE_RELAXED_UPPER
            ),
            "omegaSlope": rational_string(omega_slope),
            "omegaLocalRadius": rational_string(omega_slope * eta_radius),
            "omegaCenterError": rational_string(omega_center_error),
            "omegaAnchorProofPad": rational_string(omega_anchor_pad),
            "shapeSqSlope": rational_string(shape_sq_slope),
            "shapeSqLocalRadius": rational_string(shape_sq_slope * eta_radius),
            "shapeSqCenterError": rational_string(shape_sq_center_error),
            "shapeSqAnchorProofPad": rational_string(shape_sq_anchor_pad),
            "shapeAnchorValueProofPad": rational_string(shape_anchor_value_pad),
            "omegaSlopeDecimal": fraction_decimal(omega_slope),
            "omegaLocalRadiusDecimal": fraction_decimal(omega_slope * eta_radius),
            "omegaCenterErrorDecimal": fraction_decimal(omega_center_error),
            "omegaAnchorProofPadDecimal": fraction_decimal(omega_anchor_pad),
            "shapeSqSlopeDecimal": fraction_decimal(shape_sq_slope),
            "shapeSqLocalRadiusDecimal": fraction_decimal(shape_sq_slope * eta_radius),
            "shapeSqCenterErrorDecimal": fraction_decimal(shape_sq_center_error),
            "shapeSqAnchorProofPadDecimal": fraction_decimal(shape_sq_anchor_pad),
            "shapeAnchorValueProofPadDecimal": fraction_decimal(
                shape_anchor_value_pad
            ),
        },
        "endpointFacts": endpoint_facts,
        "endpointIntervalCert": {
            "type": ENDPOINT_CERT,
            "receiver": ENDPOINT_CERT_RECEIVER,
            "constructor": LOCAL_COMPONENT_DIRECT_ENDPOINT_FROM_OMEGA_SHAPE_RECEIVER,
            "status": "missing_omega_shape_endpoint_cert_lean_payload",
            "fields": [
                "omegaDerivLower",
                "omegaDerivUpper",
                "omegaAnchorLower",
                "omegaAnchorUpper",
                "shapeSqDerivLower",
                "shapeSqDerivUpper",
                "shapeSqAnchorLower",
                "shapeSqAnchorUpper",
                "hAnchorIn",
                "hEtaLeft",
                "hEtaRight",
                "hOmega",
                "hOmegaContain",
                "hShape",
                "hShapeSqContain",
                "hOmegaLower",
                "hOmegaUpper",
                "hShapeSqLower",
                "hShapeSqUpper",
            ],
        },
        "omegaClosedFormEndpointBoundsCert": {
            "type": OMEGA_CLOSED_FORM_ENDPOINT_BOUNDS_CERT,
            "receiver": OMEGA_CLOSED_FORM_ENDPOINT_BOUNDS_RECEIVER,
            "status": "missing_closed_form_endpoint_fact_lean_payload",
            "targetGeneratedTheorem": "rawOmegaEndpointClosedFormBounds_generated",
            "nextGeneratedTheorem": "rawOmegaEndpointValueDerivIntervalCert_generated",
            "fields": [
                "hOmegaDerivLowerClosedForm",
                "hOmegaDerivUpperClosedForm",
                "hOmegaAnchorLower",
                "hOmegaAnchorUpper",
            ],
        },
        "shapeSqEndpointBoundsCert": {
            "type": SHAPE_SQ_ENDPOINT_BOUNDS_CERT,
            "receiver": SHAPE_SQ_ENDPOINT_BOUNDS_RECEIVER,
            "anchorValueReceiver": SHAPE_SQ_ENDPOINT_BOUNDS_ANCHOR_VALUE_RECEIVER,
            "status": "missing_shapeSq_endpoint_fact_lean_payload",
            "targetGeneratedTheorem": "rawShapeSqEndpointBounds_generated",
            "nextGeneratedTheorem": "rawOmegaEndpointValueDerivIntervalCert_generated",
            "fields": [
                "hShapeValueLower",
                "hShapeValueUpper",
                "hShapeDerivLower",
                "hShapeDerivUpper",
                "hShapeAnchorValueLower",
                "hShapeAnchorValueUpper",
                "hShapeSqDerivLowerLL",
                "hShapeSqDerivLowerLU",
                "hShapeSqDerivLowerUL",
                "hShapeSqDerivLowerUU",
                "hShapeSqDerivUpperLL",
                "hShapeSqDerivUpperLU",
                "hShapeSqDerivUpperUL",
                "hShapeSqDerivUpperUU",
                "hShapeSqAnchorLower",
                "hShapeSqAnchorUpper",
            ],
        },
            "localComponentClosedFormEndpointIntervalCert": {
            "type": LOCAL_COMPONENT_CLOSED_FORM_ENDPOINT_CERT,
            "receiver": LOCAL_COMPONENT_CLOSED_FORM_ENDPOINT_RECEIVER,
            "status": "legacy_receiver_available_not_active_v19_row_target",
            "targetGeneratedTheorem": None,
            "dependsOn": [
                "rawOmegaEndpointClosedFormBounds_generated",
                "shape value/derivative endpoint interval facts",
                "shapeSq derivative four-corner comparisons",
                "Omega/shape containment comparisons",
            ],
        },
        "containmentComparisons": {
            "hOmegaContain": {
                "statement": (
                    "intervalAutoAbsBound omegaDerivLower omegaDerivUpper * "
                    "etaRadius + intervalAutoCenterError omegaAnchorLower "
                    "omegaAnchorUpper omegaCenter <= omegaRadius"
                ),
                "passes": omega_passes,
                "consumed": rational_string(omega_consumed),
                "radius": rational_string(omega_radius),
                "margin": rational_string(omega_margin),
                "consumedDecimal": fraction_decimal(omega_consumed),
                "radiusDecimal": fraction_decimal(omega_radius),
                "marginDecimal": fraction_decimal(omega_margin),
                "suggestedProof": (
                    "by norm_num after endpoint facts are materialized"
                    if omega_passes
                    else "blocked: endpoint candidates exceed omegaRadius"
                ),
            },
            "hShapeSqContain": {
                "statement": (
                    "intervalAutoAbsBound shapeSqDerivLower shapeSqDerivUpper * "
                    "etaRadius + intervalAutoCenterError shapeSqAnchorLower "
                    "shapeSqAnchorUpper shapeSqCenter <= shapeSqRadius"
                ),
                "passes": shape_sq_passes,
                "consumed": rational_string(shape_sq_consumed),
                "radius": rational_string(shape_sq_radius),
                "margin": rational_string(shape_sq_margin),
                "consumedDecimal": fraction_decimal(shape_sq_consumed),
                "radiusDecimal": fraction_decimal(shape_sq_radius),
                "marginDecimal": fraction_decimal(shape_sq_margin),
                "suggestedProof": (
                    "by norm_num after endpoint facts are materialized"
                    if shape_sq_passes
                    else "blocked: endpoint candidates exceed shapeSqRadius"
                ),
            },
        },
    }


def build_worklist(args: argparse.Namespace) -> dict[str, Any]:
    contract = load_json(args.contract)
    validate_schema(contract, path=args.contract, schema=CONTRACT_SCHEMA)
    if args.local_probe is not None and args.local_probe.exists():
        local_probe = load_json(args.local_probe)
        validate_schema(local_probe, path=args.local_probe, schema=LOCAL_PROBE_SCHEMA)
        local_probe_schema = local_probe.get("schema")
    else:
        local_probe_schema = None

    set_precision(args.arb_prec)
    getcontext().prec = max(160, args.arb_prec // 3)
    evaluator = ComponentEndpointEvaluator(sinc_terms=args.sinc_terms)

    rows = [
        build_row(row=row, evaluator=evaluator)
        for row in contract.get("rows") or []
        if isinstance(row.get("componentIntervalDerivativeCert"), dict)
    ]
    omega_pass = sum(
        1 for row in rows if row["containmentComparisons"]["hOmegaContain"]["passes"]
    )
    shape_sq_pass = sum(
        1 for row in rows if row["containmentComparisons"]["hShapeSqContain"]["passes"]
    )
    containment_pass = sum(
        int(row["containmentComparisons"]["hOmegaContain"]["passes"])
        + int(row["containmentComparisons"]["hShapeSqContain"]["passes"])
        for row in rows
    )
    endpoint_facts_open = sum(len(row["endpointFacts"]) for row in rows)

    worst_omega = None
    worst_shape_sq = None
    if rows:
        worst_omega = min(
            rows,
            key=lambda row: parse_fraction(
                row["containmentComparisons"]["hOmegaContain"]["margin"]
            ),
        )
        worst_shape_sq = min(
            rows,
            key=lambda row: parse_fraction(
                row["containmentComparisons"]["hShapeSqContain"]["margin"]
            ),
        )

    all_pass = containment_pass == 2 * len(rows)
    return {
        "schema": OUTPUT_SCHEMA,
        "status": (
            "component_endpoint_worklist_containment_passed_not_lean_proof"
            if all_pass
            else "component_endpoint_worklist_containment_failed_not_lean_proof"
        ),
        "meaning": (
            "Fail-closed endpoint candidate worklist for the v19 corrected "
            "closed-form shape endpoint receiver.  Arb/acb gives candidate "
            "intervals; Lean still needs generated endpoint enclosure facts.  "
            "Anchor endpoint facts use nonzero rational proof pads so they "
            "do not demand exact rational values of transcendental functions. "
            "The worklist also records tight one-point E(anchor) bounds for "
            "the checked anchor-value receiver."
        ),
        "contract": str(args.contract),
        "contractSchema": contract.get("schema"),
        "localProbe": str(args.local_probe) if args.local_probe is not None else None,
        "localProbeSchema": local_probe_schema,
        "receiver": RECEIVER,
        "endpointMode": ENDPOINT_MODE,
        "endpointCertType": ENDPOINT_CERT,
        "endpointCertReceiver": ENDPOINT_CERT_RECEIVER,
        "proofReductions": {
            "shapeSqDerivativeFormula": SHAPE_SQ_DERIVATIVE_REDUCTION,
            "localComponentEndpointCert": ENDPOINT_CERT,
            "localComponentEndpointReceiver": ENDPOINT_CERT_RECEIVER,
            "localComponentRawEndpointCertAuditOnly": (
                LOCAL_COMPONENT_RAW_ENDPOINT_CERT
            ),
            "localComponentRawEndpointReceiverAuditOnly": (
                LOCAL_COMPONENT_RAW_ENDPOINT_RECEIVER
            ),
            "shapeSqDerivativeIntervalReceiverAuditOnly": (
                SHAPE_SQ_DERIVATIVE_INTERVAL_RECEIVER
            ),
            "shapeSqDerivativeIccReceiverAuditOnly": (
                SHAPE_SQ_DERIVATIVE_Icc_RECEIVER
            ),
            "localComponentShapeReceiver": LOCAL_COMPONENT_SHAPE_RECEIVER,
            "omegaEndpointCert": OMEGA_ENDPOINT_CERT,
            "localComponentOmegaShapeReceiver": (
                LOCAL_COMPONENT_OMEGA_SHAPE_RECEIVER
            ),
            "localComponentClosedFormEndpointCert": (
                LOCAL_COMPONENT_CLOSED_FORM_ENDPOINT_CERT
            ),
            "localComponentClosedFormEndpointReceiver": (
                LOCAL_COMPONENT_CLOSED_FORM_ENDPOINT_RECEIVER
            ),
            "localComponentClosedFormEndpointStatus": (
                "available_not_active_v19_row_target"
            ),
            "omegaEndpointClosedFormReceiver": (
                OMEGA_ENDPOINT_CLOSED_FORM_RECEIVER
            ),
            "omegaClosedFormEndpointBoundsCert": (
                OMEGA_CLOSED_FORM_ENDPOINT_BOUNDS_CERT
            ),
            "omegaClosedFormEndpointBoundsReceiver": (
                OMEGA_CLOSED_FORM_ENDPOINT_BOUNDS_RECEIVER
            ),
            "shapeSqEndpointBoundsCert": SHAPE_SQ_ENDPOINT_BOUNDS_CERT,
            "shapeSqEndpointBoundsReceiver": SHAPE_SQ_ENDPOINT_BOUNDS_RECEIVER,
            "shapeSqEndpointBoundsAnchorValueReceiver": (
                SHAPE_SQ_ENDPOINT_BOUNDS_ANCHOR_VALUE_RECEIVER
            ),
            "localComponentDirectEndpointFromOmegaShapeReceiver": (
                LOCAL_COMPONENT_DIRECT_ENDPOINT_FROM_OMEGA_SHAPE_RECEIVER
            ),
            "omegaDerivativeClosedForm": OMEGA_DERIV_CLOSED_FORM,
            "omegaDerivativeClosedFormTheorem": OMEGA_DERIV_CLOSED_FORM_THEOREM,
            "omegaDerivativeClosedFormIccTheorem": (
                OMEGA_DERIV_CLOSED_FORM_Icc_THEOREM
            ),
            "shapeDerivativeClosedForm": SHAPE_DERIV_CLOSED_FORM,
            "shapeDerivativeClosedFormTheorem": SHAPE_DERIV_CLOSED_FORM_THEOREM,
            "shapeDerivativeClosedFormIccTheorem": (
                SHAPE_DERIV_CLOSED_FORM_Icc_THEOREM
            ),
        },
        "arbPrec": args.arb_prec,
        "sincTerms": args.sinc_terms,
        "totals": {
            "rows": len(rows),
            "componentEndpointIntervalCertsOpen": len(rows),
            "componentIntervalDerivativeEndpointFactsOpen": endpoint_facts_open,
            "componentIntervalDerivativeClosedByLean": 8 * len(rows),
            "shapeSqDerivativeFormulaClosedByLean": len(rows),
            "shapeSqDerivativeIntervalReceiverClosedByLean": len(rows),
            "shapeSqDerivativeIccReceiverClosedByLean": len(rows),
            "localComponentShapeReceiverClosedByLean": len(rows),
            "omegaEndpointCertSurfaceClosedByLean": len(rows),
            "localComponentOmegaShapeReceiverClosedByLean": len(rows),
            "localComponentClosedFormEndpointCertSurfaceClosedByLean": len(rows),
            "omegaEndpointClosedFormReceiverClosedByLean": len(rows),
            "omegaClosedFormEndpointBoundsCertSurfaceClosedByLean": len(rows),
            "shapeSqEndpointBoundsCertSurfaceClosedByLean": len(rows),
            "shapeSqEndpointBoundsReceiverClosedByLean": len(rows),
            "shapeSqEndpointBoundsAnchorValueReceiverClosedByLean": len(rows),
            "localComponentDirectEndpointFromOmegaShapeReceiverClosedByLean": (
                len(rows)
            ),
            "omegaDerivativeClosedFormClosedByLean": len(rows),
            "omegaDerivativeClosedFormIccClosedByLean": len(rows),
            "shapeDerivativeClosedFormClosedByLean": len(rows),
            "shapeDerivativeClosedFormIccClosedByLean": len(rows),
            "componentIntervalDerivativeContainmentComparisons": 2 * len(rows),
            "componentIntervalDerivativeContainmentComparisonsPassing": (
                containment_pass
            ),
            "omegaContainmentPassing": omega_pass,
            "shapeSqContainmentPassing": shape_sq_pass,
            "proofSafeClosedFields": 0,
            "anchorProofPadRows": sum(
                1
                for row in rows
                if parse_fraction(row["autoDefinitions"]["omegaAnchorProofPad"]) > 0
                or parse_fraction(row["autoDefinitions"]["shapeSqAnchorProofPad"]) > 0
            ),
            "shapeAnchorValueProofPadRows": sum(
                1
                for row in rows
                if parse_fraction(
                    row["autoDefinitions"]["shapeAnchorValueProofPad"]
                ) > 0
            ),
        },
        "worstOmegaRow": worst_omega,
        "worstShapeSqRow": worst_shape_sq,
        "rows": rows,
        "routeGuard": [
            "diagnostic endpoint worklist only; not Lean proof data",
            "do not edit A CSV, ARadius, radius-floor, or LDL from this artifact",
            "do not route to Q3.Main, H1, or PO3",
            "shape derivative facts target the checked closed-form derivative receiver",
            "active shapeSq derivative facts are derived from closed-form E/E' endpoint intervals",
            "active v19 shape endpoint facts bound E and the checked closed-form E' receiver, then derive E^2 derivative bounds by four corners",
            "active v19 anchor-value facts can derive E(anchor)^2 from tight E(anchor) bounds by four corners",
            "direct E^2 derivative interval probes are audit-only sanity data",
            "legacy raw endpoint cert is audit-only; active v19 rows instantiate LocalRawOmegaComponentDirectEndpointIntervalCert through Omega/Shape packages",
            "Omega endpoint value/derivative facts target a single proof-bearing Step22OmegaEndpointIntervalCert per row",
            "Omega derivative facts should use the checked closed-form receiver before row-index theorem generation",
            "Omega derivative closed form is Lean-checked as -Im(trigamma(1/4 + i eta/2)) / 2",
            "Omega closed-form endpoint rows should first instantiate Step22OmegaClosedFormEndpointBoundsCert",
            "shape-square endpoint rows should instantiate ShapeSqEndpointBoundsCert via of_closedForm_value_deriv_intervals",
            "shape-square endpoint rows may instead instantiate the anchor-value receiver when tight E(anchor) bounds are available",
            "component endpoint rows should instantiate LocalRawOmegaComponentDirectEndpointIntervalCert via of_omega_shape_endpoint_bounds",
            "next proof steps are rawOmegaEndpointClosedFormBounds_generated, rawShapeSqEndpointBounds_generated, then rawOmegaEndpointValueDerivIntervalCert_generated",
        ],
    }


def row_label(row: dict[str, Any] | None) -> str:
    if row is None:
        return "n/a"
    return (
        f"{row['family']} row={row['row']} parent={row['parentChunk']} "
        f"split={row['split']} sub={row['subchunk']}"
    )


def render_md(worklist: dict[str, Any]) -> str:
    totals = worklist["totals"]
    lines = [
        "# Step33A.1-A Component Endpoint Worklist",
        "",
        f"- Schema: `{worklist['schema']}`",
        f"- Status: `{worklist['status']}`",
        f"- Receiver: `{worklist['receiver']}`",
        f"- Endpoint mode: `{worklist['endpointMode']}`",
        f"- Endpoint cert receiver: `{worklist['endpointCertReceiver']}`",
        f"- ShapeSq derivative reduction: "
        f"`{worklist['proofReductions']['shapeSqDerivativeFormula']}`",
        f"- Local component endpoint cert: "
        f"`{worklist['proofReductions']['localComponentEndpointCert']}`",
        f"- Local component endpoint receiver: "
        f"`{worklist['proofReductions']['localComponentEndpointReceiver']}`",
        f"- ShapeSq derivative interval receiver audit-only: "
        f"`{worklist['proofReductions']['shapeSqDerivativeIntervalReceiverAuditOnly']}`",
        f"- ShapeSq derivative Icc receiver audit-only: "
        f"`{worklist['proofReductions']['shapeSqDerivativeIccReceiverAuditOnly']}`",
        f"- Local component shape receiver: "
        f"`{worklist['proofReductions']['localComponentShapeReceiver']}`",
        f"- Omega endpoint cert: "
        f"`{worklist['proofReductions']['omegaEndpointCert']}`",
        f"- Local component Omega/shape receiver: "
        f"`{worklist['proofReductions']['localComponentOmegaShapeReceiver']}`",
        f"- Local component closed-form endpoint cert: "
        f"`{worklist['proofReductions']['localComponentClosedFormEndpointCert']}`",
        f"- Local component closed-form endpoint receiver: "
        f"`{worklist['proofReductions']['localComponentClosedFormEndpointReceiver']}`",
        f"- Local component closed-form endpoint status: "
        f"`{worklist['proofReductions']['localComponentClosedFormEndpointStatus']}`",
        f"- Omega endpoint closed-form receiver: "
        f"`{worklist['proofReductions']['omegaEndpointClosedFormReceiver']}`",
        f"- Omega closed-form endpoint bounds cert: "
        f"`{worklist['proofReductions']['omegaClosedFormEndpointBoundsCert']}`",
        f"- Omega closed-form endpoint bounds receiver: "
        f"`{worklist['proofReductions']['omegaClosedFormEndpointBoundsReceiver']}`",
        f"- ShapeSq endpoint bounds cert: "
        f"`{worklist['proofReductions']['shapeSqEndpointBoundsCert']}`",
        f"- ShapeSq endpoint bounds receiver: "
        f"`{worklist['proofReductions']['shapeSqEndpointBoundsReceiver']}`",
        f"- ShapeSq endpoint bounds anchor-value receiver: "
        f"`{worklist['proofReductions']['shapeSqEndpointBoundsAnchorValueReceiver']}`",
        f"- Local component direct endpoint from Omega/Shape receiver: "
        f"`{worklist['proofReductions']['localComponentDirectEndpointFromOmegaShapeReceiver']}`",
        f"- Omega derivative closed form: "
        f"`{worklist['proofReductions']['omegaDerivativeClosedForm']}`",
        f"- Omega derivative closed-form theorem: "
        f"`{worklist['proofReductions']['omegaDerivativeClosedFormTheorem']}`",
        f"- Omega derivative closed-form Icc theorem: "
        f"`{worklist['proofReductions']['omegaDerivativeClosedFormIccTheorem']}`",
        f"- Shape derivative closed form: "
        f"`{worklist['proofReductions']['shapeDerivativeClosedForm']}`",
        f"- Shape derivative closed-form theorem: "
        f"`{worklist['proofReductions']['shapeDerivativeClosedFormTheorem']}`",
        f"- Shape derivative closed-form Icc theorem: "
        f"`{worklist['proofReductions']['shapeDerivativeClosedFormIccTheorem']}`",
        f"- Rows: `{totals['rows']}`",
        f"- Endpoint certs open: `{totals['componentEndpointIntervalCertsOpen']}`",
        f"- Endpoint facts open: `{totals['componentIntervalDerivativeEndpointFactsOpen']}`",
        f"- Containment comparisons passing: "
        f"`{totals['componentIntervalDerivativeContainmentComparisonsPassing']}/"
        f"{totals['componentIntervalDerivativeContainmentComparisons']}`",
        f"- Omega containment passing: `{totals['omegaContainmentPassing']}`",
        f"- ShapeSq containment passing: `{totals['shapeSqContainmentPassing']}`",
        f"- ShapeSq derivative formula closed by Lean: "
        f"`{totals['shapeSqDerivativeFormulaClosedByLean']}`",
        f"- ShapeSq derivative interval receiver closed by Lean: "
        f"`{totals['shapeSqDerivativeIntervalReceiverClosedByLean']}`",
        f"- ShapeSq derivative Icc receiver closed by Lean: "
        f"`{totals['shapeSqDerivativeIccReceiverClosedByLean']}`",
        f"- Local component shape receiver closed by Lean: "
        f"`{totals['localComponentShapeReceiverClosedByLean']}`",
        f"- Omega endpoint cert surface closed by Lean: "
        f"`{totals['omegaEndpointCertSurfaceClosedByLean']}`",
        f"- Local component Omega/shape receiver closed by Lean: "
        f"`{totals['localComponentOmegaShapeReceiverClosedByLean']}`",
        f"- Local component closed-form endpoint cert surface closed by Lean: "
        f"`{totals['localComponentClosedFormEndpointCertSurfaceClosedByLean']}`",
        f"- Omega endpoint closed-form receiver closed by Lean: "
        f"`{totals['omegaEndpointClosedFormReceiverClosedByLean']}`",
        f"- Omega closed-form endpoint bounds cert surface closed by Lean: "
        f"`{totals['omegaClosedFormEndpointBoundsCertSurfaceClosedByLean']}`",
        f"- ShapeSq endpoint bounds cert surface closed by Lean: "
        f"`{totals['shapeSqEndpointBoundsCertSurfaceClosedByLean']}`",
        f"- ShapeSq endpoint bounds receiver closed by Lean: "
        f"`{totals['shapeSqEndpointBoundsReceiverClosedByLean']}`",
        f"- ShapeSq endpoint bounds anchor-value receiver closed by Lean: "
        f"`{totals['shapeSqEndpointBoundsAnchorValueReceiverClosedByLean']}`",
        f"- Local component direct endpoint from Omega/Shape receiver closed by Lean: "
        f"`{totals['localComponentDirectEndpointFromOmegaShapeReceiverClosedByLean']}`",
        f"- Omega derivative closed form closed by Lean: "
        f"`{totals['omegaDerivativeClosedFormClosedByLean']}`",
        f"- Omega derivative closed-form Icc theorem closed by Lean: "
        f"`{totals['omegaDerivativeClosedFormIccClosedByLean']}`",
        f"- Shape derivative closed form closed by Lean: "
        f"`{totals['shapeDerivativeClosedFormClosedByLean']}`",
        f"- Shape derivative closed-form Icc theorem closed by Lean: "
        f"`{totals['shapeDerivativeClosedFormIccClosedByLean']}`",
        f"- Proof-safe closed fields: `{totals['proofSafeClosedFields']}`",
        "",
        "## Worst Rows",
        "",
    ]
    worst_omega = worklist.get("worstOmegaRow")
    worst_shape = worklist.get("worstShapeSqRow")
    if worst_omega is not None:
        comp = worst_omega["containmentComparisons"]["hOmegaContain"]
        lines.extend(
            [
                f"- Worst Omega: `{row_label(worst_omega)}`",
                f"  - margin: `{comp['marginDecimal']}`",
                f"  - consumed: `{comp['consumedDecimal']}`",
                f"  - radius: `{comp['radiusDecimal']}`",
            ]
        )
    if worst_shape is not None:
        comp = worst_shape["containmentComparisons"]["hShapeSqContain"]
        lines.extend(
            [
                f"- Worst ShapeSq: `{row_label(worst_shape)}`",
                f"  - margin: `{comp['marginDecimal']}`",
                f"  - consumed: `{comp['consumedDecimal']}`",
                f"  - radius: `{comp['radiusDecimal']}`",
            ]
        )
    lines.extend(
        [
            "",
            "## Endpoint Obligations Per Row",
            "",
            "```text",
            "hOmegaDerivLower",
            "hOmegaDerivUpper",
            "hOmegaAnchorLower",
            "hOmegaAnchorUpper",
            "hShapeValueLower",
            "hShapeValueUpper",
            "hShapeDerivLower",
            "hShapeDerivUpper",
            "hShapeAnchorValueLower",
            "hShapeAnchorValueUpper",
            "hShapeSqAnchorLower",
            "hShapeSqAnchorUpper",
            "```",
            "",
            "The shape-square derivative bounds are derived by",
            "`ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals`",
            "from the four corners of `2 * E * E'`.",
            "The optional anchor-value receiver additionally derives",
            "`E(anchor)^2` from tight one-point `E(anchor)` bounds.",
            "",
            "## Generated Theorem Targets",
            "",
            "- `rawOmegaEndpointClosedFormBounds_generated`",
            "- `rawShapeSqEndpointBounds_generated`",
            "- `rawOmegaEndpointValueDerivIntervalCert_generated`",
            "",
            "## Guard",
            "",
        ]
    )
    for item in worklist["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--local-probe", type=Path, default=DEFAULT_LOCAL_PROBE)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--arb-prec", type=int, default=1024)
    parser.add_argument("--sinc-terms", type=int, default=128)
    args = parser.parse_args()

    worklist = build_worklist(args)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(worklist, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.write_text(render_md(worklist), encoding="utf-8")
    print(
        "component_endpoint_worklist: "
        f"rows={worklist['totals']['rows']} "
        "containment="
        f"{worklist['totals']['componentIntervalDerivativeContainmentComparisonsPassing']}/"
        f"{worklist['totals']['componentIntervalDerivativeContainmentComparisons']} "
        f"status={worklist['status']} "
        f"out={args.out_json}"
    )


if __name__ == "__main__":
    main()
