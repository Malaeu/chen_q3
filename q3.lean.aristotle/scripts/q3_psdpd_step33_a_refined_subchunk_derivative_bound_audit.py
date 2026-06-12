#!/usr/bin/env python3
"""Audit derivative residual bounds for refined subchunk candidates.

This is a fail-closed pilot for the Step33A.1-A raw-Omega route.  It checks
why the rejected single-envelope derivative receivers are too wide:

    |residual anchor| + slope * mesh <= remainder
    |deriv residual anchor| + derivSlope * mesh <= slope

The current active skeleton targets a derivative finite-cover receiver instead.
This audit records why a single second-derivative envelope, raw/poly
subtraction, and broad interval derivative bounds are not enough, while
preserving the sampled direct-derivative feasibility signal.

The output is diagnostic generator evidence, not Lean proof data.  It records
candidate `sampleRadius`, `slope`, `mesh`, `derivSampleRadius`, `derivSlope`,
and the scalar envelope comparisons that motivated the finite-cover derivative
receiver.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal, InvalidOperation, ROUND_CEILING, ROUND_FLOOR, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

try:
    from flint import acb, arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required. Run with the repo venv, for example:\n"
        "  .venv/bin/python q3.lean.aristotle/scripts/"
        "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.py"
    ) from exc

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    set_precision,
)
from q3_psdpd_step33_a_chunk_integral_probe import (
    DEFAULT_WORKLIST,
    decimal_str,
    load_worklist,
    make_builder,
    selected_families,
)


getcontext().prec = 100

ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0.json"
)
DEFAULT_RESIDUAL_AUDIT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_rational_residual_audit_primary_finite_0_0.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0.md"
)

OVERLAY_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"
RESIDUAL_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_rational_residual_audit.v1"
)


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def decimal_from_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def ceil_decimal_to_denom(value: Decimal, denom: int) -> Fraction:
    scaled = (max(Decimal(0), value) * Decimal(denom)).to_integral_value(
        rounding=ROUND_CEILING
    )
    return Fraction(int(scaled), denom)


def floor_signed_decimal_to_denom(value: Decimal, denom: int) -> Fraction:
    scaled = (value * Decimal(denom)).to_integral_value(rounding=ROUND_FLOOR)
    return Fraction(int(scaled), denom)


def ceil_signed_decimal_to_denom(value: Decimal, denom: int) -> Fraction:
    scaled = (value * Decimal(denom)).to_integral_value(rounding=ROUND_CEILING)
    return Fraction(int(scaled), denom)


def rational_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_sci(value: Decimal) -> str:
    return format(value, ".18E")


def fraction_arb(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def parse_split_schedule(text: str) -> list[int]:
    out: list[int] = []
    for part in text.split(","):
        part = part.strip()
        if not part:
            continue
        value = int(part)
        if value <= 0:
            raise ValueError("split counts must be positive")
        out.append(value)
    if not out:
        raise ValueError("empty split schedule")
    return out


def sample_points(left: Decimal, right: Decimal, count: int) -> list[Decimal]:
    if count < 2:
        raise ValueError("sample count must be at least 2")
    step = (right - left) / Decimal(count - 1)
    return [left + Decimal(i) * step for i in range(count)]


def residual_by_subchunk(residual_audit: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {
        int(row["subchunk"]): row
        for row in residual_audit.get("subchunks", [])
    }


def sinc_series_acb(x: acb, terms: int) -> acb:
    total = acb(0)
    x2 = x * x
    power = acb(1)
    for n in range(terms):
        coeff = arb((-1) ** n) / arb(math.factorial(2 * n + 1))
        total += acb(coeff) * power
        power *= x2
    return total


def sinc_series_deriv_acb(x: acb, terms: int) -> acb:
    total = acb(0)
    x2 = x * x
    power = acb(1)
    for n in range(1, terms):
        coeff = arb((-1) ** n * (2 * n)) / arb(math.factorial(2 * n + 1))
        total += acb(coeff) * power
        power *= x2
    return x * total


def sinc_series_second_deriv_acb(x: acb, terms: int) -> acb:
    total = acb(0)
    x2 = x * x
    power = acb(1)
    for n in range(1, terms):
        coeff = (
            arb((-1) ** n * (2 * n) * (2 * n - 1))
            / arb(math.factorial(2 * n + 1))
        )
        total += acb(coeff) * power
        power *= x2
    return total


def raw_step22_integrand_and_derivatives(builder: Any, d: Decimal):
    d_acb = acb(arb(str(d)))
    ell_acb = acb(builder.ell)
    pi_acb = acb(builder.pi)
    norm_acb = acb(builder.norm)
    two = acb(2)
    s_acb = acb(builder.s_k)
    x_scale = ell_acb / (two * s_acb)
    prefactor = ell_acb / pi_acb
    sinc_power = int(builder.sinc_power)
    sinc_terms = int(builder.sinc_terms)

    def pieces(t: acb) -> tuple[acb, acb, acb, acb, acb, acb, acb, acb, acb]:
        z = acb(arb("0.25")) + builder.i_unit * t / two
        omega = acb(z.digamma().real - builder.log_pi)
        dz_dt = builder.i_unit / two
        omega_deriv = acb((z.polygamma(1) * dz_dt).real)
        omega_second = acb((z.polygamma(2) * dz_dt * dz_dt).real)
        x = x_scale * t
        sinc = sinc_series_acb(x, sinc_terms)
        sinc_deriv_t = sinc_series_deriv_acb(x, sinc_terms) * x_scale
        sinc_second_t = (
            sinc_series_second_deriv_acb(x, sinc_terms) * x_scale * x_scale
        )
        e2 = norm_acb * (sinc ** sinc_power)
        e2_deriv = (
            norm_acb
            * acb(sinc_power)
            * (sinc ** (sinc_power - 1))
            * sinc_deriv_t
        )
        if sinc_power == 1:
            e2_second = norm_acb * sinc_second_t
        else:
            e2_second = norm_acb * acb(sinc_power) * (
                acb(sinc_power - 1)
                * (sinc ** (sinc_power - 2))
                * sinc_deriv_t
                * sinc_deriv_t
                + (sinc ** (sinc_power - 1)) * sinc_second_t
            )
        cos = (t * d_acb).cos()
        cos_deriv = -d_acb * (t * d_acb).sin()
        cos_second = -(d_acb * d_acb) * cos
        return (
            omega,
            omega_deriv,
            omega_second,
            e2,
            e2_deriv,
            e2_second,
            cos,
            cos_deriv,
            cos_second,
        )

    def f(t: acb) -> acb:
        omega, _omega_deriv, _omega_second, e2, _e2_deriv, _e2_second, cos, _cos_deriv, _cos_second = pieces(t)
        return prefactor * omega * e2 * cos

    def f_deriv(t: acb) -> acb:
        omega, omega_deriv, _omega_second, e2, e2_deriv, _e2_second, cos, cos_deriv, _cos_second = pieces(t)
        return prefactor * (
            omega_deriv * e2 * cos
            + omega * e2_deriv * cos
            + omega * e2 * cos_deriv
        )

    def f_second_deriv(t: acb) -> acb:
        (
            omega,
            omega_deriv,
            omega_second,
            e2,
            e2_deriv,
            e2_second,
            cos,
            cos_deriv,
            cos_second,
        ) = pieces(t)
        return prefactor * (
            omega_second * e2 * cos
            + omega * e2_second * cos
            + omega * e2 * cos_second
            + acb(2) * omega_deriv * e2_deriv * cos
            + acb(2) * omega_deriv * e2 * cos_deriv
            + acb(2) * omega * e2_deriv * cos_deriv
        )

    return f, f_deriv, f_second_deriv


def polynomial_eval_ball(coeff: list[Fraction], *, eta: arb, center: Decimal) -> arb:
    shifted = eta - arb(str(center))
    total = arb(0)
    power = arb(1)
    for coeff_i in coeff:
        total += fraction_arb(coeff_i) * power
        power *= shifted
    return total


def polynomial_deriv_ball(coeff: list[Fraction], *, eta: arb, center: Decimal) -> arb:
    shifted = eta - arb(str(center))
    total = arb(0)
    power = arb(1)
    for index, coeff_i in enumerate(coeff[1:], start=1):
        total += arb(index) * fraction_arb(coeff_i) * power
        power *= shifted
    return total


def polynomial_second_deriv_ball(
    coeff: list[Fraction], *, eta: arb, center: Decimal
) -> arb:
    shifted = eta - arb(str(center))
    total = arb(0)
    power = arb(1)
    for index, coeff_i in enumerate(coeff[2:], start=2):
        total += arb(index * (index - 1)) * fraction_arb(coeff_i) * power
        power *= shifted
    return total


def arb_abs_upper_decimal(value: arb) -> Decimal:
    lower = arb_lower_decimal(value)
    upper = arb_upper_decimal(value)
    if not lower.is_finite() or not upper.is_finite():
        raise ValueError(f"non-finite Arb bound lower={lower!s} upper={upper!s}")
    return max(abs(lower), abs(upper))


def build_residual_jet_cells(
    *,
    f_deriv: Any,
    f_second_deriv: Any,
    coeff: list[Fraction],
    left: Decimal,
    right: Decimal,
    center: Decimal,
    split_count: int,
    denominator: int,
    slope_guard: Decimal,
) -> dict[str, Any]:
    """Build one residual-jet derivative finite-cover candidate.

    The output is still diagnostic candidate data.  It chooses the derivative
    lower/upper cell interval from the signed derivative-anchor interval plus
    a local second-derivative/Lipschitz enclosure on the same derivative cell.
    """
    step = (right - left) / Decimal(split_count)
    cells: list[dict[str, Any]] = []
    max_abs_deriv_bound = Decimal(0)
    worst_second_deriv = Decimal(0)
    worst_cell = 0
    for piece in range(split_count):
        cell_left = left + Decimal(piece) * step
        cell_right = cell_left + step
        cell_center = (cell_left + cell_right) / Decimal(2)
        cell_radius = (cell_right - cell_left) / Decimal(2)
        deriv_mesh = ceil_decimal_to_denom(cell_radius, denominator)
        deriv_mesh_decimal = decimal_from_fraction(deriv_mesh)

        anchor_eta = arb(str(cell_center))
        anchor_deriv_residual = f_deriv(
            acb(anchor_eta)
        ).real - polynomial_deriv_ball(coeff, eta=anchor_eta, center=center)
        anchor_lower_decimal = arb_lower_decimal(anchor_deriv_residual)
        anchor_upper_decimal = arb_upper_decimal(anchor_deriv_residual)
        deriv_anchor_lower = floor_signed_decimal_to_denom(
            anchor_lower_decimal
            - abs(anchor_lower_decimal) * slope_guard
            - Decimal("1e-90"),
            denominator,
        )
        deriv_anchor_upper = ceil_signed_decimal_to_denom(
            anchor_upper_decimal
            + abs(anchor_upper_decimal) * slope_guard
            + Decimal("1e-90"),
            denominator,
        )
        deriv_anchor_lower_decimal = decimal_from_fraction(deriv_anchor_lower)
        deriv_anchor_upper_decimal = decimal_from_fraction(deriv_anchor_upper)

        eta = arb(str(cell_center), str(cell_radius))
        second_deriv_residual = f_second_deriv(
            acb(eta)
        ).real - polynomial_second_deriv_ball(coeff, eta=eta, center=center)
        second_deriv_abs = arb_abs_upper_decimal(second_deriv_residual)
        if second_deriv_abs > worst_second_deriv:
            worst_second_deriv = second_deriv_abs
            worst_cell = piece
        deriv_slope = ceil_decimal_to_denom(
            second_deriv_abs * (Decimal(1) + slope_guard) + Decimal("1e-90"),
            denominator,
        )
        deriv_slope_decimal = decimal_from_fraction(deriv_slope)
        deriv_lower = floor_signed_decimal_to_denom(
            deriv_anchor_lower_decimal
            - deriv_slope_decimal * deriv_mesh_decimal,
            denominator,
        )
        deriv_upper = ceil_signed_decimal_to_denom(
            deriv_anchor_upper_decimal
            + deriv_slope_decimal * deriv_mesh_decimal,
            denominator,
        )
        deriv_lower_decimal = decimal_from_fraction(deriv_lower)
        deriv_upper_decimal = decimal_from_fraction(deriv_upper)
        max_abs_deriv_bound = max(
            max_abs_deriv_bound,
            abs(deriv_lower_decimal),
            abs(deriv_upper_decimal),
        )
        cells.append(
            {
                "cell": piece,
                "left": decimal_str(cell_left),
                "right": decimal_str(cell_right),
                "derivLower": rational_string(deriv_lower),
                "derivLowerDecimal": decimal_sci(deriv_lower_decimal),
                "derivUpper": rational_string(deriv_upper),
                "derivUpperDecimal": decimal_sci(deriv_upper_decimal),
                "derivAnchor": decimal_str(cell_center),
                "derivAnchorLower": rational_string(deriv_anchor_lower),
                "derivAnchorLowerDecimal": decimal_sci(
                    deriv_anchor_lower_decimal
                ),
                "derivAnchorUpper": rational_string(deriv_anchor_upper),
                "derivAnchorUpperDecimal": decimal_sci(
                    deriv_anchor_upper_decimal
                ),
                "derivMesh": rational_string(deriv_mesh),
                "derivMeshDecimal": decimal_sci(deriv_mesh_decimal),
                "derivSlope": rational_string(deriv_slope),
                "derivSlopeDecimal": decimal_sci(deriv_slope_decimal),
                "secondDerivativeResidualAbsUpper": decimal_sci(
                    second_deriv_abs
                ),
                "proofStatus": "residual_jet_candidate_not_lean_proof",
            }
        )
    cover_slope = ceil_decimal_to_denom(
        max_abs_deriv_bound * (Decimal(1) + slope_guard) + Decimal("1e-90"),
        denominator,
    )
    cover_slope_decimal = decimal_from_fraction(cover_slope)
    for cell in cells:
        deriv_lower_decimal = Decimal(cell["derivLowerDecimal"])
        deriv_upper_decimal = Decimal(cell["derivUpperDecimal"])
        cell["hDerivLowerAbsWouldPass"] = (
            -cover_slope_decimal <= deriv_lower_decimal
        )
        cell["hDerivUpperAbsWouldPass"] = (
            deriv_upper_decimal <= cover_slope_decimal
        )
    return {
        "splits": split_count,
        "cellCount": split_count,
        "coverSlope": rational_string(cover_slope),
        "coverSlopeDecimal": decimal_sci(cover_slope_decimal),
        "maxAbsDerivativeCellBound": decimal_sci(max_abs_deriv_bound),
        "maxSecondDerivativeResidualAbsUpper": decimal_sci(worst_second_deriv),
        "worstSecondDerivativeCell": worst_cell,
        "cells": cells,
    }


def find_family(worklist: dict[str, Any], family_id: str) -> dict[str, Any]:
    matches = selected_families(worklist, family_id)
    if len(matches) != 1:
        raise ValueError(f"expected one family {family_id!r}, found {len(matches)}")
    return matches[0]


def find_row_distance(family: dict[str, Any], row_index: int) -> Decimal:
    rows = family.get("distances", [])
    if row_index < 0 or row_index >= len(rows):
        raise ValueError(f"row {row_index} outside family row count {len(rows)}")
    return Decimal(str(rows[row_index]["distance"]))


def audit_candidate(
    *,
    f: Any,
    f_deriv: Any,
    f_second_deriv: Any,
    candidate: dict[str, Any],
    residual_info: dict[str, Any] | None,
    split_schedule: list[int],
    check_samples: int,
    denominator: int,
    slope_guard: Decimal,
    sample_guard: Decimal,
) -> dict[str, Any]:
    coeff = [parse_fraction(value) for value in candidate.get("coeff", [])]
    left = Decimal(str(candidate["left"]))
    right = Decimal(str(candidate["right"]))
    center = Decimal(str(candidate["center"]))
    mesh = max(center - left, right - center)
    remainder = parse_fraction(candidate["remainder"])
    remainder_decimal = decimal_from_fraction(remainder)

    anchor_eta = arb(str(center))
    anchor_residual = f(acb(anchor_eta)).real - polynomial_eval_ball(
        coeff, eta=anchor_eta, center=center
    )
    anchor_deriv_residual = f_deriv(acb(anchor_eta)).real - polynomial_deriv_ball(
        coeff, eta=anchor_eta, center=center
    )
    anchor_radius_decimal = arb_abs_upper_decimal(anchor_residual)
    anchor_deriv_lower_decimal = arb_lower_decimal(anchor_deriv_residual)
    anchor_deriv_upper_decimal = arb_upper_decimal(anchor_deriv_residual)
    anchor_deriv_radius_decimal = arb_abs_upper_decimal(anchor_deriv_residual)
    sampled_residual_decimal = Decimal(
        str((residual_info or {}).get("sampledMaxResidual", "0"))
    )
    required_sample_radius = (
        max(anchor_radius_decimal, sampled_residual_decimal)
        * (Decimal(1) + sample_guard)
        + Decimal("1e-90")
    )
    sample_radius = ceil_decimal_to_denom(required_sample_radius, denominator)
    sample_radius_decimal = decimal_from_fraction(sample_radius)
    required_deriv_sample_radius = (
        anchor_deriv_radius_decimal * (Decimal(1) + slope_guard)
        + Decimal("1e-90")
    )
    deriv_sample_radius = ceil_decimal_to_denom(
        required_deriv_sample_radius, denominator
    )
    deriv_sample_radius_decimal = decimal_from_fraction(deriv_sample_radius)
    deriv_anchor_lower = floor_signed_decimal_to_denom(
        anchor_deriv_lower_decimal
        - abs(anchor_deriv_lower_decimal) * slope_guard
        - Decimal("1e-90"),
        denominator,
    )
    deriv_anchor_upper = ceil_signed_decimal_to_denom(
        anchor_deriv_upper_decimal
        + abs(anchor_deriv_upper_decimal) * slope_guard
        + Decimal("1e-90"),
        denominator,
    )
    deriv_anchor_lower_decimal = decimal_from_fraction(deriv_anchor_lower)
    deriv_anchor_upper_decimal = decimal_from_fraction(deriv_anchor_upper)

    sampled_deriv_max = Decimal(0)
    sampled_deriv_lower: Decimal | None = None
    sampled_deriv_upper: Decimal | None = None
    sampled_raw_deriv_lower: Decimal | None = None
    sampled_raw_deriv_upper: Decimal | None = None
    sampled_poly_deriv_lower: Decimal | None = None
    sampled_poly_deriv_upper: Decimal | None = None
    sampled_deriv_worst_eta = left
    sampled_second_deriv_max = Decimal(0)
    sampled_second_deriv_worst_eta = left
    for eta_decimal in sample_points(left, right, check_samples):
        eta = arb(str(eta_decimal))
        raw_deriv = f_deriv(acb(eta)).real
        raw_second_deriv = f_second_deriv(acb(eta)).real
        poly_deriv = polynomial_deriv_ball(coeff, eta=eta, center=center)
        poly_second_deriv = polynomial_second_deriv_ball(
            coeff, eta=eta, center=center
        )
        diff_deriv = raw_deriv - poly_deriv
        diff_second_deriv = raw_second_deriv - poly_second_deriv
        raw_lower = arb_lower_decimal(raw_deriv)
        raw_upper = arb_upper_decimal(raw_deriv)
        poly_lower = arb_lower_decimal(poly_deriv)
        poly_upper = arb_upper_decimal(poly_deriv)
        deriv_lower = arb_lower_decimal(diff_deriv)
        deriv_upper = arb_upper_decimal(diff_deriv)
        if (
            sampled_raw_deriv_lower is None
            or raw_lower < sampled_raw_deriv_lower
        ):
            sampled_raw_deriv_lower = raw_lower
        if (
            sampled_raw_deriv_upper is None
            or raw_upper > sampled_raw_deriv_upper
        ):
            sampled_raw_deriv_upper = raw_upper
        if (
            sampled_poly_deriv_lower is None
            or poly_lower < sampled_poly_deriv_lower
        ):
            sampled_poly_deriv_lower = poly_lower
        if (
            sampled_poly_deriv_upper is None
            or poly_upper > sampled_poly_deriv_upper
        ):
            sampled_poly_deriv_upper = poly_upper
        if sampled_deriv_lower is None or deriv_lower < sampled_deriv_lower:
            sampled_deriv_lower = deriv_lower
        if sampled_deriv_upper is None or deriv_upper > sampled_deriv_upper:
            sampled_deriv_upper = deriv_upper
        local = max(abs(deriv_lower), abs(deriv_upper))
        if local > sampled_deriv_max:
            sampled_deriv_max = local
            sampled_deriv_worst_eta = eta_decimal
        local_second = arb_abs_upper_decimal(diff_second_deriv)
        if local_second > sampled_second_deriv_max:
            sampled_second_deriv_max = local_second
            sampled_second_deriv_worst_eta = eta_decimal

    assert sampled_deriv_lower is not None and sampled_deriv_upper is not None
    assert sampled_raw_deriv_lower is not None and sampled_raw_deriv_upper is not None
    assert sampled_poly_deriv_lower is not None and sampled_poly_deriv_upper is not None
    sampled_deriv_lower_guarded = (
        sampled_deriv_lower
        - abs(sampled_deriv_lower) * slope_guard
        - Decimal("1e-90")
    )
    sampled_deriv_upper_guarded = (
        sampled_deriv_upper
        + abs(sampled_deriv_upper) * slope_guard
        + Decimal("1e-90")
    )
    sampled_deriv_lower_candidate = floor_signed_decimal_to_denom(
        sampled_deriv_lower_guarded, denominator
    )
    sampled_deriv_upper_candidate = ceil_signed_decimal_to_denom(
        sampled_deriv_upper_guarded, denominator
    )
    sampled_deriv_lower_decimal = decimal_from_fraction(sampled_deriv_lower_candidate)
    sampled_deriv_upper_decimal = decimal_from_fraction(sampled_deriv_upper_candidate)
    sampled_raw_deriv_lower_candidate = floor_signed_decimal_to_denom(
        sampled_raw_deriv_lower
        - abs(sampled_raw_deriv_lower) * slope_guard
        - Decimal("1e-90"),
        denominator,
    )
    sampled_raw_deriv_upper_candidate = ceil_signed_decimal_to_denom(
        sampled_raw_deriv_upper
        + abs(sampled_raw_deriv_upper) * slope_guard
        + Decimal("1e-90"),
        denominator,
    )
    sampled_poly_deriv_lower_candidate = floor_signed_decimal_to_denom(
        sampled_poly_deriv_lower
        - abs(sampled_poly_deriv_lower) * slope_guard
        - Decimal("1e-90"),
        denominator,
    )
    sampled_poly_deriv_upper_candidate = ceil_signed_decimal_to_denom(
        sampled_poly_deriv_upper
        + abs(sampled_poly_deriv_upper) * slope_guard
        + Decimal("1e-90"),
        denominator,
    )
    sampled_raw_deriv_lower_decimal = decimal_from_fraction(
        sampled_raw_deriv_lower_candidate
    )
    sampled_raw_deriv_upper_decimal = decimal_from_fraction(
        sampled_raw_deriv_upper_candidate
    )
    sampled_poly_deriv_lower_decimal = decimal_from_fraction(
        sampled_poly_deriv_lower_candidate
    )
    sampled_poly_deriv_upper_decimal = decimal_from_fraction(
        sampled_poly_deriv_upper_candidate
    )
    raw_poly_deriv_lower_candidate = (
        sampled_raw_deriv_lower_candidate - sampled_poly_deriv_upper_candidate
    )
    raw_poly_deriv_upper_candidate = (
        sampled_raw_deriv_upper_candidate - sampled_poly_deriv_lower_candidate
    )
    raw_poly_deriv_lower_decimal = decimal_from_fraction(
        raw_poly_deriv_lower_candidate
    )
    raw_poly_deriv_upper_decimal = decimal_from_fraction(
        raw_poly_deriv_upper_candidate
    )
    raw_poly_slope_required = (
        max(abs(raw_poly_deriv_lower_decimal), abs(raw_poly_deriv_upper_decimal))
        * (Decimal(1) + slope_guard)
        + Decimal("1e-90")
    )
    raw_poly_slope = ceil_decimal_to_denom(raw_poly_slope_required, denominator)
    raw_poly_slope_decimal = decimal_from_fraction(raw_poly_slope)
    raw_poly_deriv_lower_abs_passes = (
        -raw_poly_slope_decimal <= raw_poly_deriv_lower_decimal
    )
    raw_poly_deriv_upper_abs_passes = (
        raw_poly_deriv_upper_decimal <= raw_poly_slope_decimal
    )
    raw_poly_envelope_lhs = sample_radius_decimal + raw_poly_slope_decimal * mesh
    raw_poly_envelope_excess = raw_poly_envelope_lhs - remainder_decimal
    raw_poly_envelope_passes = raw_poly_envelope_excess <= 0
    sampled_slope_required = (
        sampled_deriv_max * (Decimal(1) + slope_guard) + Decimal("1e-90")
    )
    sampled_slope = ceil_decimal_to_denom(sampled_slope_required, denominator)
    sampled_slope_decimal = decimal_from_fraction(sampled_slope)
    sampled_deriv_lower_abs_passes = -sampled_slope_decimal <= sampled_deriv_lower_decimal
    sampled_deriv_upper_abs_passes = sampled_deriv_upper_decimal <= sampled_slope_decimal
    sampled_envelope_lhs = sample_radius_decimal + sampled_slope_decimal * mesh
    sampled_envelope_excess = sampled_envelope_lhs - remainder_decimal
    sampled_envelope_passes = sampled_envelope_excess <= 0

    split_rows = []
    best_interval_slope_decimal: Decimal | None = None
    best_split = None
    second_deriv_split_rows = []
    best_second_deriv_slope_decimal: Decimal | None = None
    best_second_deriv_split = None
    nonfinite_interval_errors = []
    for split_count in split_schedule:
        step = (right - left) / Decimal(split_count)
        max_deriv = Decimal(0)
        max_second_deriv = Decimal(0)
        worst_piece = 0
        worst_second_piece = 0
        split_error = None
        for piece in range(split_count):
            piece_left = left + Decimal(piece) * step
            piece_right = piece_left + step
            piece_center = (piece_left + piece_right) / Decimal(2)
            piece_radius = (piece_right - piece_left) / Decimal(2)
            eta = arb(str(piece_center), str(piece_radius))
            diff_deriv = f_deriv(acb(eta)).real - polynomial_deriv_ball(
                coeff, eta=eta, center=center
            )
            diff_second_deriv = f_second_deriv(
                acb(eta)
            ).real - polynomial_second_deriv_ball(coeff, eta=eta, center=center)
            try:
                local = arb_abs_upper_decimal(diff_deriv)
                local_second = arb_abs_upper_decimal(diff_second_deriv)
            except ValueError as exc:
                split_error = {
                    "splits": split_count,
                    "piece": piece,
                    "left": decimal_str(piece_left),
                    "right": decimal_str(piece_right),
                    "error": type(exc).__name__,
                    "message": str(exc),
                }
                break
            if local > max_deriv:
                max_deriv = local
                worst_piece = piece
            if local_second > max_second_deriv:
                max_second_deriv = local_second
                worst_second_piece = piece
        if split_error is not None:
            nonfinite_interval_errors.append(split_error)
            split_rows.append(
                {
                    "splits": split_count,
                    "status": "nonfinite_bound",
                    "maxDerivativeResidual": "NaN",
                    "guardedSlope": "NaN",
                    "worstPiece": split_error["piece"],
                    "message": split_error["message"],
                }
            )
            second_deriv_split_rows.append(
                {
                    "splits": split_count,
                    "status": "nonfinite_bound",
                    "maxSecondDerivativeResidual": "NaN",
                    "guardedDerivSlope": "NaN",
                    "worstPiece": split_error["piece"],
                    "message": split_error["message"],
                }
            )
            continue
        guarded = max_deriv * (Decimal(1) + slope_guard) + Decimal("1e-90")
        split_rows.append(
            {
                "splits": split_count,
                "maxDerivativeResidual": decimal_sci(max_deriv),
                "guardedSlope": decimal_sci(guarded),
                "worstPiece": worst_piece,
            }
        )
        if best_interval_slope_decimal is None or guarded < best_interval_slope_decimal:
            best_interval_slope_decimal = guarded
            best_split = split_count
        second_guarded = (
            max_second_deriv * (Decimal(1) + slope_guard) + Decimal("1e-90")
        )
        second_deriv_split_rows.append(
            {
                "splits": split_count,
                "maxSecondDerivativeResidual": decimal_sci(max_second_deriv),
                "guardedDerivSlope": decimal_sci(second_guarded),
                "worstPiece": worst_second_piece,
            }
        )
        if (
            best_second_deriv_slope_decimal is None
            or second_guarded < best_second_deriv_slope_decimal
        ):
            best_second_deriv_slope_decimal = second_guarded
            best_second_deriv_split = split_count

    if (
        best_interval_slope_decimal is None
        or best_split is None
        or best_second_deriv_slope_decimal is None
        or best_second_deriv_split is None
    ):
        return {
            "subchunk": int(candidate["subchunk"]),
            "left": candidate["left"],
            "right": candidate["right"],
            "center": candidate["center"],
            "mesh": decimal_str(mesh),
            "meshCandidate": rational_string(ceil_decimal_to_denom(mesh, denominator)),
            "currentRemainder": rational_string(remainder),
            "sampleRadius": rational_string(sample_radius),
            "sampleRadiusDecimal": decimal_sci(sample_radius_decimal),
            "anchorResidualAbsUpper": decimal_sci(anchor_radius_decimal),
            "anchorDerivativeResidualAbsUpper": decimal_sci(
                anchor_deriv_radius_decimal
            ),
            "anchorDerivativeResidualLower": decimal_sci(
                anchor_deriv_lower_decimal
            ),
            "anchorDerivativeResidualUpper": decimal_sci(
                anchor_deriv_upper_decimal
            ),
            "derivSampleRadius": rational_string(deriv_sample_radius),
            "derivSampleRadiusDecimal": decimal_sci(deriv_sample_radius_decimal),
            "derivAnchorLower": rational_string(deriv_anchor_lower),
            "derivAnchorLowerDecimal": decimal_sci(deriv_anchor_lower_decimal),
            "derivAnchorUpper": rational_string(deriv_anchor_upper),
            "derivAnchorUpperDecimal": decimal_sci(deriv_anchor_upper_decimal),
            "sampledResidualAbsUpper": decimal_sci(sampled_residual_decimal),
            "sampledDerivativeResidualAbsUpper": decimal_sci(sampled_deriv_max),
            "sampledDerivativeWorstEta": decimal_str(sampled_deriv_worst_eta),
            "sampledSecondDerivativeResidualAbsUpper": decimal_sci(
                sampled_second_deriv_max
            ),
            "sampledSecondDerivativeWorstEta": decimal_str(
                sampled_second_deriv_worst_eta
            ),
            "sampledDerivLower": rational_string(sampled_deriv_lower_candidate),
            "sampledDerivLowerDecimal": decimal_sci(sampled_deriv_lower_decimal),
            "sampledDerivUpper": rational_string(sampled_deriv_upper_candidate),
            "sampledDerivUpperDecimal": decimal_sci(sampled_deriv_upper_decimal),
            "derivativeIntervalFiniteCoverCellCount": 1,
            "derivativeIntervalFiniteCoverCells": [
                {
                    "cell": 0,
                    "left": candidate["left"],
                    "right": candidate["right"],
                    "derivLower": rational_string(sampled_deriv_lower_candidate),
                    "derivLowerDecimal": decimal_sci(sampled_deriv_lower_decimal),
                    "derivUpper": rational_string(sampled_deriv_upper_candidate),
                    "derivUpperDecimal": decimal_sci(sampled_deriv_upper_decimal),
                    "hDerivLowerAbsWouldPass": sampled_deriv_lower_abs_passes,
                    "hDerivUpperAbsWouldPass": sampled_deriv_upper_abs_passes,
                    "proofStatus": "sampled_candidate_not_lean_proof",
                }
            ],
            "sampledRawDerivLower": rational_string(sampled_raw_deriv_lower_candidate),
            "sampledRawDerivLowerDecimal": decimal_sci(sampled_raw_deriv_lower_decimal),
            "sampledRawDerivUpper": rational_string(sampled_raw_deriv_upper_candidate),
            "sampledRawDerivUpperDecimal": decimal_sci(sampled_raw_deriv_upper_decimal),
            "sampledPolyDerivLower": rational_string(sampled_poly_deriv_lower_candidate),
            "sampledPolyDerivLowerDecimal": decimal_sci(sampled_poly_deriv_lower_decimal),
            "sampledPolyDerivUpper": rational_string(sampled_poly_deriv_upper_candidate),
            "sampledPolyDerivUpperDecimal": decimal_sci(sampled_poly_deriv_upper_decimal),
            "rawPolyDerivLower": rational_string(raw_poly_deriv_lower_candidate),
            "rawPolyDerivLowerDecimal": decimal_sci(raw_poly_deriv_lower_decimal),
            "rawPolyDerivUpper": rational_string(raw_poly_deriv_upper_candidate),
            "rawPolyDerivUpperDecimal": decimal_sci(raw_poly_deriv_upper_decimal),
            "rawPolySlope": rational_string(raw_poly_slope),
            "rawPolySlopeDecimal": decimal_sci(raw_poly_slope_decimal),
            "rawPolyDerivLowerAbsPasses": raw_poly_deriv_lower_abs_passes,
            "rawPolyDerivUpperAbsPasses": raw_poly_deriv_upper_abs_passes,
            "rawPolyEnvelopeLhs": decimal_sci(raw_poly_envelope_lhs),
            "rawPolyEnvelopeExcess": decimal_sci(raw_poly_envelope_excess),
            "rawPolyEnvelopePasses": raw_poly_envelope_passes,
            "sampledSlope": rational_string(sampled_slope),
            "sampledSlopeDecimal": decimal_sci(sampled_slope_decimal),
            "sampledDerivLowerAbsPasses": sampled_deriv_lower_abs_passes,
            "sampledDerivUpperAbsPasses": sampled_deriv_upper_abs_passes,
            "sampledEnvelopeLhs": decimal_sci(sampled_envelope_lhs),
            "sampledEnvelopeExcess": decimal_sci(sampled_envelope_excess),
            "sampledEnvelopePasses": sampled_envelope_passes,
            "intervalSlope": "0/1",
            "intervalSlopeDecimal": "NaN",
            "bestSplit": None,
            "intervalEnvelopeLhs": "NaN",
            "intervalEnvelopeExcess": "Infinity",
            "intervalEnvelopePasses": False,
            "derivSlope": "0/1",
            "derivSlopeDecimal": "NaN",
            "secondDerivativeSlope": "0/1",
            "secondDerivativeSlopeDecimal": "NaN",
            "bestSecondDerivativeSplit": None,
            "secondDerivativeDerivEnvelopeLhs": "NaN",
            "secondDerivativeDerivEnvelopeExcess": "Infinity",
            "secondDerivativeEnvelopeLhs": "NaN",
            "secondDerivativeEnvelopeExcess": "Infinity",
            "secondDerivativeEnvelopePasses": False,
            "jetFiniteCoverCellCount": 0,
            "jetFiniteCoverSplit": None,
            "jetCoverSlope": "0/1",
            "jetCoverSlopeDecimal": "NaN",
            "jetEnvelopeLhs": "NaN",
            "jetEnvelopeExcess": "Infinity",
            "jetEnvelopePasses": False,
            "jetMaxAbsDerivativeCellBound": "NaN",
            "jetMaxSecondDerivativeResidualAbsUpper": "NaN",
            "jetWorstSecondDerivativeCell": None,
            "jetDerivativeIntervalFiniteCoverCells": [],
            "jetFiniteCoverCandidates": [],
            "splitRows": split_rows,
            "secondDerivativeSplitRows": second_deriv_split_rows,
            "numericIntervalErrors": nonfinite_interval_errors,
            "guard": [
                "sampled derivative candidate preserved",
                "interval derivative route hit non-finite Arb bounds",
                "not Lean proof data",
            ],
        }
    interval_slope = ceil_decimal_to_denom(best_interval_slope_decimal, denominator)
    interval_slope_decimal = decimal_from_fraction(interval_slope)
    interval_envelope_lhs = sample_radius_decimal + interval_slope_decimal * mesh
    interval_envelope_excess = interval_envelope_lhs - remainder_decimal
    interval_envelope_passes = interval_envelope_excess <= 0
    deriv_slope = ceil_decimal_to_denom(
        best_second_deriv_slope_decimal, denominator
    )
    deriv_slope_decimal = decimal_from_fraction(deriv_slope)
    required_second_derivative_slope = (
        deriv_sample_radius_decimal + deriv_slope_decimal * mesh
    )
    second_derivative_slope = ceil_decimal_to_denom(
        required_second_derivative_slope, denominator
    )
    second_derivative_slope_decimal = decimal_from_fraction(second_derivative_slope)
    second_derivative_deriv_envelope_lhs = (
        deriv_sample_radius_decimal + deriv_slope_decimal * mesh
    )
    second_derivative_deriv_envelope_excess = (
        second_derivative_deriv_envelope_lhs - second_derivative_slope_decimal
    )
    second_derivative_envelope_lhs = (
        sample_radius_decimal + second_derivative_slope_decimal * mesh
    )
    second_derivative_envelope_excess = (
        second_derivative_envelope_lhs - remainder_decimal
    )
    second_derivative_envelope_passes = second_derivative_envelope_excess <= 0
    jet_candidates = []
    for split_count in split_schedule:
        try:
            candidate_jet = build_residual_jet_cells(
                f_deriv=f_deriv,
                f_second_deriv=f_second_deriv,
                coeff=coeff,
                left=left,
                right=right,
                center=center,
                split_count=split_count,
                denominator=denominator,
                slope_guard=slope_guard,
            )
        except ValueError as exc:
            jet_candidates.append(
                {
                    "splits": split_count,
                    "cellCount": 0,
                    "coverSlope": "0/1",
                    "coverSlopeDecimal": "NaN",
                    "maxAbsDerivativeCellBound": "NaN",
                    "maxSecondDerivativeResidualAbsUpper": "NaN",
                    "worstSecondDerivativeCell": None,
                    "cells": [],
                    "envelopeLhs": "NaN",
                    "envelopeExcess": "Infinity",
                    "envelopePasses": False,
                    "status": "nonfinite_bound",
                    "message": str(exc),
                }
            )
            continue
        cover_slope_decimal = decimal_from_fraction(
            parse_fraction(candidate_jet["coverSlope"])
        )
        envelope_lhs = sample_radius_decimal + cover_slope_decimal * mesh
        envelope_excess = envelope_lhs - remainder_decimal
        candidate_jet["envelopeLhs"] = decimal_sci(envelope_lhs)
        candidate_jet["envelopeExcess"] = decimal_sci(envelope_excess)
        candidate_jet["envelopePasses"] = envelope_excess <= 0
        jet_candidates.append(candidate_jet)
    passing_jet_candidates = [
        candidate_jet
        for candidate_jet in jet_candidates
        if candidate_jet["envelopePasses"]
    ]
    if passing_jet_candidates:
        active_jet_candidate = min(
            passing_jet_candidates,
            key=lambda candidate_jet: int(candidate_jet["splits"]),
        )
    else:
        active_jet_candidate = min(
            jet_candidates,
            key=lambda candidate_jet: Decimal(candidate_jet["envelopeExcess"]),
        )
    return {
        "subchunk": int(candidate["subchunk"]),
        "left": candidate["left"],
        "right": candidate["right"],
        "center": candidate["center"],
        "mesh": decimal_str(mesh),
        "meshCandidate": rational_string(ceil_decimal_to_denom(mesh, denominator)),
        "currentRemainder": rational_string(remainder),
        "sampleRadius": rational_string(sample_radius),
        "sampleRadiusDecimal": decimal_sci(sample_radius_decimal),
        "anchorResidualAbsUpper": decimal_sci(anchor_radius_decimal),
        "anchorDerivativeResidualAbsUpper": decimal_sci(
            anchor_deriv_radius_decimal
        ),
        "anchorDerivativeResidualLower": decimal_sci(anchor_deriv_lower_decimal),
        "anchorDerivativeResidualUpper": decimal_sci(anchor_deriv_upper_decimal),
        "derivSampleRadius": rational_string(deriv_sample_radius),
        "derivSampleRadiusDecimal": decimal_sci(deriv_sample_radius_decimal),
        "derivAnchorLower": rational_string(deriv_anchor_lower),
        "derivAnchorLowerDecimal": decimal_sci(deriv_anchor_lower_decimal),
        "derivAnchorUpper": rational_string(deriv_anchor_upper),
        "derivAnchorUpperDecimal": decimal_sci(deriv_anchor_upper_decimal),
        "sampledResidualAbsUpper": decimal_sci(sampled_residual_decimal),
        "sampledDerivativeResidualAbsUpper": decimal_sci(sampled_deriv_max),
        "sampledDerivativeWorstEta": decimal_str(sampled_deriv_worst_eta),
        "sampledSecondDerivativeResidualAbsUpper": decimal_sci(
            sampled_second_deriv_max
        ),
        "sampledSecondDerivativeWorstEta": decimal_str(
            sampled_second_deriv_worst_eta
        ),
        "sampledDerivLower": rational_string(sampled_deriv_lower_candidate),
        "sampledDerivLowerDecimal": decimal_sci(sampled_deriv_lower_decimal),
        "sampledDerivUpper": rational_string(sampled_deriv_upper_candidate),
        "sampledDerivUpperDecimal": decimal_sci(sampled_deriv_upper_decimal),
        "derivativeIntervalFiniteCoverCellCount": 1,
        "derivativeIntervalFiniteCoverCells": [
            {
                "cell": 0,
                "left": candidate["left"],
                "right": candidate["right"],
                "derivLower": rational_string(sampled_deriv_lower_candidate),
                "derivLowerDecimal": decimal_sci(sampled_deriv_lower_decimal),
                "derivUpper": rational_string(sampled_deriv_upper_candidate),
                "derivUpperDecimal": decimal_sci(sampled_deriv_upper_decimal),
                "hDerivLowerAbsWouldPass": sampled_deriv_lower_abs_passes,
                "hDerivUpperAbsWouldPass": sampled_deriv_upper_abs_passes,
                "proofStatus": "sampled_candidate_not_lean_proof",
            }
        ],
        "sampledRawDerivLower": rational_string(sampled_raw_deriv_lower_candidate),
        "sampledRawDerivLowerDecimal": decimal_sci(sampled_raw_deriv_lower_decimal),
        "sampledRawDerivUpper": rational_string(sampled_raw_deriv_upper_candidate),
        "sampledRawDerivUpperDecimal": decimal_sci(sampled_raw_deriv_upper_decimal),
        "sampledPolyDerivLower": rational_string(sampled_poly_deriv_lower_candidate),
        "sampledPolyDerivLowerDecimal": decimal_sci(sampled_poly_deriv_lower_decimal),
        "sampledPolyDerivUpper": rational_string(sampled_poly_deriv_upper_candidate),
        "sampledPolyDerivUpperDecimal": decimal_sci(sampled_poly_deriv_upper_decimal),
        "rawPolyDerivLower": rational_string(raw_poly_deriv_lower_candidate),
        "rawPolyDerivLowerDecimal": decimal_sci(raw_poly_deriv_lower_decimal),
        "rawPolyDerivUpper": rational_string(raw_poly_deriv_upper_candidate),
        "rawPolyDerivUpperDecimal": decimal_sci(raw_poly_deriv_upper_decimal),
        "rawPolySlope": rational_string(raw_poly_slope),
        "rawPolySlopeDecimal": decimal_sci(raw_poly_slope_decimal),
        "rawPolyDerivLowerAbsPasses": raw_poly_deriv_lower_abs_passes,
        "rawPolyDerivUpperAbsPasses": raw_poly_deriv_upper_abs_passes,
        "rawPolyEnvelopeLhs": decimal_sci(raw_poly_envelope_lhs),
        "rawPolyEnvelopeExcess": decimal_sci(raw_poly_envelope_excess),
        "rawPolyEnvelopePasses": raw_poly_envelope_passes,
        "sampledSlope": rational_string(sampled_slope),
        "sampledSlopeDecimal": decimal_sci(sampled_slope_decimal),
        "sampledDerivLowerAbsPasses": sampled_deriv_lower_abs_passes,
        "sampledDerivUpperAbsPasses": sampled_deriv_upper_abs_passes,
        "sampledEnvelopeLhs": decimal_sci(sampled_envelope_lhs),
        "sampledEnvelopeExcess": decimal_sci(sampled_envelope_excess),
        "sampledEnvelopePasses": sampled_envelope_passes,
        "intervalSlope": rational_string(interval_slope),
        "intervalSlopeDecimal": decimal_sci(interval_slope_decimal),
        "bestSplit": best_split,
        "intervalEnvelopeLhs": decimal_sci(interval_envelope_lhs),
        "intervalEnvelopeExcess": decimal_sci(interval_envelope_excess),
        "intervalEnvelopePasses": interval_envelope_passes,
        "derivSlope": rational_string(deriv_slope),
        "derivSlopeDecimal": decimal_sci(deriv_slope_decimal),
        "secondDerivativeSlope": rational_string(second_derivative_slope),
        "secondDerivativeSlopeDecimal": decimal_sci(
            second_derivative_slope_decimal
        ),
        "bestSecondDerivativeSplit": best_second_deriv_split,
        "secondDerivativeDerivEnvelopeLhs": decimal_sci(
            second_derivative_deriv_envelope_lhs
        ),
        "secondDerivativeDerivEnvelopeExcess": decimal_sci(
            second_derivative_deriv_envelope_excess
        ),
        "secondDerivativeEnvelopeLhs": decimal_sci(
            second_derivative_envelope_lhs
        ),
        "secondDerivativeEnvelopeExcess": decimal_sci(
            second_derivative_envelope_excess
        ),
        "secondDerivativeEnvelopePasses": second_derivative_envelope_passes,
        "jetFiniteCoverCellCount": active_jet_candidate["cellCount"],
        "jetFiniteCoverSplit": active_jet_candidate["splits"],
        "jetCoverSlope": active_jet_candidate["coverSlope"],
        "jetCoverSlopeDecimal": active_jet_candidate["coverSlopeDecimal"],
        "jetEnvelopeLhs": active_jet_candidate["envelopeLhs"],
        "jetEnvelopeExcess": active_jet_candidate["envelopeExcess"],
        "jetEnvelopePasses": active_jet_candidate["envelopePasses"],
        "jetMaxAbsDerivativeCellBound": active_jet_candidate[
            "maxAbsDerivativeCellBound"
        ],
        "jetMaxSecondDerivativeResidualAbsUpper": active_jet_candidate[
            "maxSecondDerivativeResidualAbsUpper"
        ],
        "jetWorstSecondDerivativeCell": active_jet_candidate[
            "worstSecondDerivativeCell"
        ],
        "jetDerivativeIntervalFiniteCoverCells": active_jet_candidate["cells"],
        "jetFiniteCoverCandidates": [
            {
                key: value
                for key, value in candidate_jet.items()
                if key != "cells"
            }
            for candidate_jet in jet_candidates
        ],
        "splitRows": split_rows,
        "secondDerivativeSplitRows": second_deriv_split_rows,
        "guard": [
            "diagnostic rejected second-derivative single-cover audit only",
            "not Lean proof data",
            "active skeleton targets derivative finite-cover proof data instead",
            "second-derivative interval candidates are route-comparison data",
            ],
    }


def build_report(
    *,
    args: argparse.Namespace,
    overlay: dict[str, Any],
    residual_audit: dict[str, Any],
    overlay_path: Path,
    residual_path: Path,
    worklist: dict[str, Any],
) -> dict[str, Any]:
    if overlay.get("schema") != OVERLAY_SCHEMA:
        raise ValueError(
            f"{overlay_path}: unexpected schema {overlay.get('schema')!r}"
        )
    if residual_audit.get("schema") != RESIDUAL_AUDIT_SCHEMA:
        raise ValueError(
            f"{residual_path}: unexpected schema {residual_audit.get('schema')!r}"
        )
    pilot = overlay["pilot"]
    family_id = str(pilot["family"])
    row_index = int(pilot["row"])
    family = find_family(worklist, family_id)
    builder = make_builder(args, family=family)
    distance = find_row_distance(family, row_index)
    f, f_deriv, f_second_deriv = raw_step22_integrand_and_derivatives(
        builder, distance
    )
    residual_rows = residual_by_subchunk(residual_audit)
    split_schedule = parse_split_schedule(args.derivative_splits)
    slope_guard = Decimal(str(args.slope_guard))
    sample_guard = Decimal(str(args.sample_guard))

    rows = []
    numeric_errors = []
    for candidate in overlay.get("candidates", []):
        try:
            rows.append(
                audit_candidate(
                    f=f,
                    f_deriv=f_deriv,
                    f_second_deriv=f_second_deriv,
                    candidate=candidate,
                    residual_info=residual_rows.get(int(candidate["subchunk"])),
                    split_schedule=split_schedule,
                    check_samples=args.check_samples,
                    denominator=args.denominator,
                    slope_guard=slope_guard,
                    sample_guard=sample_guard,
                )
            )
        except (InvalidOperation, ValueError) as exc:
            numeric_errors.append(
                {
                    "subchunk": int(candidate["subchunk"]),
                    "left": candidate.get("left"),
                    "right": candidate.get("right"),
                    "error": type(exc).__name__,
                    "message": str(exc),
                }
            )
    if numeric_errors:
        return {
            "schema": "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7",
            "status": "derivative_audit_numeric_nonfinite_bounds_no_proof",
            "meaning": (
                "Diagnostic derivative residual audit failed closed because "
                "at least one Arb derivative bound was non-finite or could not "
                "be converted to a Decimal.  This is not Lean proof data."
            ),
            "overlay": str(overlay_path),
            "residualAudit": str(residual_path),
            "sourceWorklist": str(args.worklist),
            "parameters": {
                "source": "raw_step22",
                "ell": args.ell,
                "arbPrec": args.arb_prec,
                "sincTerms": args.sinc_terms,
                "denominator": args.denominator,
                "checkSamples": args.check_samples,
                "derivativeSplits": split_schedule,
                "slopeGuard": str(slope_guard),
                "sampleGuard": str(sample_guard),
            },
            "pilot": {
                "family": family_id,
                "row": row_index,
                "parentChunk": int(pilot["parentChunk"]),
                "degree": int(pilot["degree"]),
                "split": int(pilot["split"]),
                "left": pilot.get("left"),
                "right": pilot.get("right"),
            },
            "counts": {
                "subchunks": len(overlay.get("candidates", [])),
                "checkedSubchunksBeforeError": len(rows),
                "numericErrorSubchunks": len(numeric_errors),
                "proofSafeClosedFields": 0,
            },
            "numericErrors": numeric_errors,
            "worst": None,
            "secondDerivativeFailures": [],
            "sampledFailures": [],
            "rawPolyFailures": [],
            "intervalFailures": [],
            "jetFiniteCoverFailures": [],
            "subchunks": rows,
            "routeGuard": [
                "do not emit Lean from this derivative audit",
                "non-finite Arb derivative bounds are a diagnostic blocker, not proof data",
                "rerun with sharper local bounds or adjusted precision/split before direct overlay emission",
                "proofSafeClosedFields remains zero",
            ],
        }
    interval_pass_rows = [row for row in rows if row["intervalEnvelopePasses"]]
    interval_fail_rows = [row for row in rows if not row["intervalEnvelopePasses"]]
    raw_poly_pass_rows = [row for row in rows if row["rawPolyEnvelopePasses"]]
    raw_poly_fail_rows = [row for row in rows if not row["rawPolyEnvelopePasses"]]
    second_derivative_pass_rows = [
        row for row in rows if row["secondDerivativeEnvelopePasses"]
    ]
    second_derivative_fail_rows = [
        row for row in rows if not row["secondDerivativeEnvelopePasses"]
    ]
    sampled_pass_rows = [row for row in rows if row["sampledEnvelopePasses"]]
    sampled_fail_rows = [row for row in rows if not row["sampledEnvelopePasses"]]
    jet_pass_rows = [row for row in rows if row["jetEnvelopePasses"]]
    jet_fail_rows = [row for row in rows if not row["jetEnvelopePasses"]]
    worst = (
        max(rows, key=lambda row: Decimal(row["jetEnvelopeExcess"]))
        if rows
        else None
    )
    if not jet_fail_rows:
        status = "residual_jet_finite_cover_candidate_passed_not_proof"
    elif not second_derivative_fail_rows:
        status = "second_derivative_single_cover_envelope_passed_not_proof"
    elif not interval_fail_rows:
        status = "interval_derivative_envelope_passed_not_proof"
    elif not raw_poly_fail_rows:
        status = "raw_poly_sampled_derivative_envelope_passed_interval_overestimated"
    elif not sampled_fail_rows:
        status = (
            "sampled_interval_finite_cover_candidate_passed_"
            "rejected_envelopes_overestimated"
        )
    else:
        status = "derivative_envelope_candidate_failed"
    return {
        "schema": "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7",
        "status": status,
        "meaning": (
            "Diagnostic derivative residual audit for the rejected "
            "single-envelope derivative routes and the active residual-jet "
            "finite-cover candidate.  The active skeleton targets "
            "ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData.  "
            "This is not Lean proof data."
        ),
        "overlay": str(overlay_path),
        "residualAudit": str(residual_path),
        "sourceWorklist": str(args.worklist),
        "parameters": {
            "source": "raw_step22",
            "ell": args.ell,
            "arbPrec": args.arb_prec,
            "sincTerms": args.sinc_terms,
            "denominator": args.denominator,
            "checkSamples": args.check_samples,
            "derivativeSplits": split_schedule,
            "slopeGuard": args.slope_guard,
            "sampleGuard": args.sample_guard,
        },
        "pilot": pilot,
        "counts": {
            "candidateSubchunks": len(rows),
            "secondDerivativeEnvelopePasses": len(second_derivative_pass_rows),
            "secondDerivativeEnvelopeFails": len(second_derivative_fail_rows),
            "sampledEnvelopePasses": len(sampled_pass_rows),
            "sampledEnvelopeFails": len(sampled_fail_rows),
            "rawPolyEnvelopePasses": len(raw_poly_pass_rows),
            "rawPolyEnvelopeFails": len(raw_poly_fail_rows),
            "intervalEnvelopePasses": len(interval_pass_rows),
            "intervalEnvelopeFails": len(interval_fail_rows),
            "jetFiniteCoverEnvelopePasses": len(jet_pass_rows),
            "jetFiniteCoverEnvelopeFails": len(jet_fail_rows),
            "proofSafeClosedFields": 0,
            "candidateFieldsForDerivativeIntervalFiniteCover": len(rows) * 14,
            "candidateFieldsForDerivativeSecondDerivativeSingleCover": len(rows) * 12,
            "candidateFieldsForDerivativeRawPolyIntervalSingleCover": len(rows) * 15,
            "candidateFieldsForResidualJetFiniteCover": sum(
                int(row["jetFiniteCoverCellCount"]) * 15 for row in rows
            ),
        },
        "worst": worst,
        "secondDerivativeFailures": second_derivative_fail_rows[:20],
        "sampledFailures": sampled_fail_rows[:20],
        "rawPolyFailures": raw_poly_fail_rows[:20],
        "intervalFailures": interval_fail_rows[:20],
        "jetFiniteCoverFailures": jet_fail_rows[:20],
        "subchunks": rows,
        "routeGuard": [
            "do not emit Lean from derivative audit alone",
            "active route is the residual-jet derivative finite-cover receiver",
            "second-derivative interval candidates are rejected route-comparison data",
            "sampled derivative cells are candidates, not Lean proofs",
            "proof-producing emitters should target hDerivAnchorLower/hDerivAnchorUpper and hResidualSecondDerivBoundOnCell",
            "raw/poly derivative diagnostics are route comparison only",
            "if envelope fails, reduce mesh/increase degree/recompute remainder before payload generation",
            "if sampled feasibility holds, next target is a proof-producing local derivative-residual emitter",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    counts = report["counts"]
    pilot = report["pilot"]
    worst = report.get("worst") or {}
    lines = [
        "# Step33A.1-A Refined Subchunk Derivative Bound Audit",
        "",
        "Diagnostic derivative audit.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
        f"- family: `{pilot['family']}`",
        f"- row: `{pilot['row']}`",
        f"- parent chunk: `{pilot['parentChunk']}`",
        f"- degree: `{pilot['degree']}`",
        f"- split: `{pilot['split']}`",
        "",
        "## Counts",
        "",
        "| item | count |",
        "| --- | ---: |",
    ]
    for key, value in counts.items():
        lines.append(f"| `{key}` | `{value}` |")
    if report.get("numericErrors"):
        lines.extend(
            [
                "",
                "## Numeric Errors",
                "",
                "| subchunk | left | right | error | message |",
                "| ---: | ---: | ---: | --- | --- |",
            ]
        )
        for item in report["numericErrors"]:
            lines.append(
                f"| {item['subchunk']} | `{item['left']}` | `{item['right']}` | "
                f"`{item['error']}` | `{item['message']}` |"
            )
    if worst:
        lines.extend(
            [
                "",
                "## Worst Envelope",
                "",
                f"- subchunk: `{worst['subchunk']}`",
                f"- mesh: `{worst['mesh']}`",
                f"- sample radius: `{worst['sampleRadiusDecimal']}`",
                f"- sampled derivative lower: `{worst['sampledDerivLowerDecimal']}`",
                f"- sampled derivative upper: `{worst['sampledDerivUpperDecimal']}`",
                f"- interval finite-cover cells: `{worst['derivativeIntervalFiniteCoverCellCount']}`",
                f"- residual-jet finite-cover cells: `{worst['jetFiniteCoverCellCount']}`",
                f"- residual-jet split: `{worst['jetFiniteCoverSplit']}`",
                f"- anchor derivative residual: `{worst['anchorDerivativeResidualAbsUpper']}`",
                f"- deriv sample radius: `{worst['derivSampleRadiusDecimal']}`",
                f"- second derivative residual sampled max: `{worst['sampledSecondDerivativeResidualAbsUpper']}`",
                f"- residual-jet cover slope: `{worst['jetCoverSlopeDecimal']}`",
                f"- residual-jet envelope excess: `{worst['jetEnvelopeExcess']}`",
                f"- residual-jet max second derivative residual: `{worst['jetMaxSecondDerivativeResidualAbsUpper']}`",
                f"- deriv slope: `{worst['derivSlopeDecimal']}`",
                f"- second-derivative-derived slope: `{worst['secondDerivativeSlopeDecimal']}`",
                f"- best second derivative split: `{worst['bestSecondDerivativeSplit']}`",
                f"- second derivative envelope excess: `{worst['secondDerivativeEnvelopeExcess']}`",
                f"- raw/poly derivative lower: `{worst['rawPolyDerivLowerDecimal']}`",
                f"- raw/poly derivative upper: `{worst['rawPolyDerivUpperDecimal']}`",
                f"- sampled slope: `{worst['sampledSlopeDecimal']}`",
                f"- raw/poly slope: `{worst['rawPolySlopeDecimal']}`",
                f"- interval slope: `{worst['intervalSlopeDecimal']}`",
                f"- best split: `{worst['bestSplit']}`",
                f"- sampled envelope excess: `{worst['sampledEnvelopeExcess']}`",
                f"- raw/poly envelope excess: `{worst['rawPolyEnvelopeExcess']}`",
                f"- interval envelope excess: `{worst['intervalEnvelopeExcess']}`",
            ]
        )
        cells = worst.get("derivativeIntervalFiniteCoverCells") or []
        if cells:
            lines.extend(
                [
                    "",
                    "## Worst Active Candidate Cell",
                    "",
                    "| cell | left | right | deriv lower | deriv upper | lower abs | upper abs |",
                    "| ---: | ---: | ---: | ---: | ---: | :---: | :---: |",
                ]
            )
            for cell in cells[:5]:
                lines.append(
                    f"| {cell['cell']} | `{cell['left']}` | `{cell['right']}` | "
                    f"`{cell['derivLowerDecimal']}` | "
                    f"`{cell['derivUpperDecimal']}` | "
                    f"`{cell['hDerivLowerAbsWouldPass']}` | "
                    f"`{cell['hDerivUpperAbsWouldPass']}` |"
                )
        jet_cells = worst.get("jetDerivativeIntervalFiniteCoverCells") or []
        if jet_cells:
            lines.extend(
                [
                    "",
                    "## Worst Residual-Jet Candidate Cells",
                    "",
                    "| cell | left | right | anchor | deriv lower | deriv upper | deriv slope | lower abs | upper abs |",
                    "| ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: | :---: |",
                ]
            )
            for cell in jet_cells[:8]:
                lines.append(
                    f"| {cell['cell']} | `{cell['left']}` | `{cell['right']}` | "
                    f"`{cell['derivAnchor']}` | "
                    f"`{cell['derivLowerDecimal']}` | "
                    f"`{cell['derivUpperDecimal']}` | "
                    f"`{cell['derivSlopeDecimal']}` | "
                    f"`{cell['hDerivLowerAbsWouldPass']}` | "
                    f"`{cell['hDerivUpperAbsWouldPass']}` |"
                )
    if report.get("jetFiniteCoverFailures"):
        lines.extend(
            [
                "",
                "## First Residual-Jet Finite-Cover Failures",
                "",
                "| subchunk | cells | cover slope | envelope excess |",
                "| ---: | ---: | ---: | ---: |",
            ]
        )
        for failure in report["jetFiniteCoverFailures"]:
            lines.append(
                f"| {failure['subchunk']} | `{failure['jetFiniteCoverCellCount']}` | "
                f"`{failure['jetCoverSlopeDecimal']}` | "
                f"`{failure['jetEnvelopeExcess']}` |"
            )
    if report.get("secondDerivativeFailures"):
        lines.extend(
            [
                "",
                "## First Second-Derivative Failures",
                "",
                "| subchunk | deriv sample radius | deriv slope | derived slope | envelope excess | best split |",
                "| ---: | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for failure in report["secondDerivativeFailures"]:
            lines.append(
                f"| {failure['subchunk']} | `{failure['derivSampleRadiusDecimal']}` | "
                f"`{failure['derivSlopeDecimal']}` | "
                f"`{failure['secondDerivativeSlopeDecimal']}` | "
                f"`{failure['secondDerivativeEnvelopeExcess']}` | "
                f"`{failure['bestSecondDerivativeSplit']}` |"
            )
    if report.get("sampledFailures"):
        lines.extend(
            [
                "",
                "## First Sampled Failures",
                "",
                "| subchunk | sample radius | sampled slope | sampled envelope excess |",
                "| ---: | ---: | ---: | ---: |",
            ]
        )
        for failure in report["sampledFailures"]:
            lines.append(
                f"| {failure['subchunk']} | `{failure['sampleRadiusDecimal']}` | "
                f"`{failure['sampledSlopeDecimal']}` | "
                f"`{failure['sampledEnvelopeExcess']}` |"
            )
    if report.get("rawPolyFailures"):
        lines.extend(
            [
                "",
                "## First Raw/Poly Failures",
                "",
                "| subchunk | sample radius | raw/poly slope | raw/poly envelope excess |",
                "| ---: | ---: | ---: | ---: |",
            ]
        )
        for failure in report["rawPolyFailures"]:
            lines.append(
                f"| {failure['subchunk']} | `{failure['sampleRadiusDecimal']}` | "
                f"`{failure['rawPolySlopeDecimal']}` | "
                f"`{failure['rawPolyEnvelopeExcess']}` |"
            )
    if report.get("intervalFailures"):
        lines.extend(
            [
                "",
                "## First Interval Failures",
                "",
                "| subchunk | sample radius | interval slope | interval envelope excess | best split |",
                "| ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for failure in report["intervalFailures"]:
            lines.append(
                f"| {failure['subchunk']} | `{failure['sampleRadiusDecimal']}` | "
                f"`{failure['intervalSlopeDecimal']}` | "
                f"`{failure['intervalEnvelopeExcess']}` | "
                f"`{failure['bestSplit']}` |"
            )
    lines.extend(["", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--overlay", type=Path, default=DEFAULT_OVERLAY)
    parser.add_argument("--residual-audit", type=Path, default=DEFAULT_RESIDUAL_AUDIT)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--rel-tol", type=str, default="1e-40")
    parser.add_argument("--abs-tol", type=str, default="1e-40")
    parser.add_argument("--deg-limit", type=int, default=64)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=20)
    parser.add_argument("--sinc-terms", type=int, default=90)
    parser.add_argument("--omega-factor", type=str, default="10")
    parser.add_argument("--radius-floor", type=str, default="1e-30")
    parser.add_argument("--arb-prec", type=int, default=224)
    parser.add_argument("--denominator", type=int, default=10**30)
    parser.add_argument("--check-samples", type=int, default=61)
    parser.add_argument("--derivative-splits", type=str, default="1,4,16,64")
    parser.add_argument("--slope-guard", type=str, default="0.10")
    parser.add_argument("--sample-guard", type=str, default="0.10")
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    overlay = load_json(args.overlay)
    residual_audit = load_json(args.residual_audit)
    worklist = load_worklist(args.worklist)
    report = build_report(
        args=args,
        overlay=overlay,
        residual_audit=residual_audit,
        overlay_path=args.overlay,
        residual_path=args.residual_audit,
        worklist=worklist,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    counts = report["counts"]
    print(
        "status={status} subchunks={subchunks} sampled_passes={sampled_passes} "
        "sampled_fails={sampled_fails} interval_passes={interval_passes} "
        "interval_fails={interval_fails} jet_passes={jet_passes} "
        "jet_fails={jet_fails} numeric_errors={numeric_errors}".format(
            status=report["status"],
            subchunks=counts.get("candidateSubchunks", counts.get("subchunks", 0)),
            sampled_passes=counts.get("sampledEnvelopePasses", 0),
            sampled_fails=counts.get("sampledEnvelopeFails", 0),
            interval_passes=counts.get("intervalEnvelopePasses", 0),
            interval_fails=counts.get("intervalEnvelopeFails", 0),
            jet_passes=counts.get("jetFiniteCoverEnvelopePasses", 0),
            jet_fails=counts.get("jetFiniteCoverEnvelopeFails", 0),
            numeric_errors=counts.get("numericErrorSubchunks", 0),
        )
    )


if __name__ == "__main__":
    run()
