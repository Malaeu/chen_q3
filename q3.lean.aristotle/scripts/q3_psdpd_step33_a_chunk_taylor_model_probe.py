#!/usr/bin/env python3
"""Probe rational Taylor/model candidates for Step33 raw-Omega chunks.

This is diagnostic search only.  It uses Arb/acb point evaluation to discover
candidate polynomial models and reports whether the induced
`lowerModelIntegral` / `upperModelIntegral` interval could fit the existing
chunk target bounds.  It does not emit Lean proof data and must not be treated
as a trusted certificate.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal, ROUND_CEILING, getcontext
from pathlib import Path
from typing import Any

import numpy as np

try:
    from flint import acb, arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required. Run with the repo venv, for example:\n"
        "  .venv/bin/python q3.lean.aristotle/scripts/"
        "q3_psdpd_step33_a_chunk_taylor_model_probe.py"
    ) from exc

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    set_precision,
)
from q3_psdpd_step33_a_chunk_integral_probe import (
    DEFAULT_WORKLIST,
    chunk_integrand,
    decimal_str,
    load_worklist,
    make_builder,
    selected_chunks,
    selected_distance_rows,
    selected_families,
)
from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    PROOF_DATA_SCHEMA,
    load_json,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_PROOF_DATA = REQUEST_DIR / "a_chunk_taylor_payload_product_abs_seed.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_model_probe.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_model_probe.md"


def parse_int_csv(text: str) -> list[int]:
    out: list[int] = []
    for part in text.split(","):
        part = part.strip()
        if part:
            out.append(int(part))
    if not out:
        raise ValueError("expected at least one integer")
    return out


def decimal_from_any(value: Any) -> Decimal:
    if value is None:
        raise ValueError("missing decimal value")
    return Decimal(str(value))


def proof_data_cell_map(payload: dict[str, Any]) -> dict[tuple[str, int, int], dict[str, Any]]:
    if payload.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {payload.get('schema')!r}")
    cells: dict[tuple[str, int, int], dict[str, Any]] = {}
    for family in payload.get("families", []):
        family_id = str(family["id"])
        for row in family.get("distances", []):
            row_index = int(row["index"])
            for chunk in row.get("chunks", []):
                cells[(family_id, row_index, int(chunk["index"]))] = chunk
    return cells


def sample_points(left: Decimal, right: Decimal, count: int) -> list[Decimal]:
    if count < 2:
        raise ValueError("sample count must be at least 2")
    step = (right - left) / Decimal(count - 1)
    return [left + Decimal(i) * step for i in range(count)]


def arb_mid_radius(value: arb) -> tuple[float, float]:
    lower = arb_lower_decimal(value)
    upper = arb_upper_decimal(value)
    mid = (lower + upper) / Decimal(2)
    radius = max(upper - mid, mid - lower)
    return float(mid), float(radius)


def arb_mid_radius_decimal(value: arb) -> tuple[Decimal, Decimal]:
    lower = arb_lower_decimal(value)
    upper = arb_upper_decimal(value)
    mid = (lower + upper) / Decimal(2)
    radius = max(upper - mid, mid - lower)
    return mid, radius


def eval_integrand_mid_radius(f: Any, eta: Decimal) -> tuple[float, float]:
    value = f(acb(arb(str(eta))), True).real
    return arb_mid_radius(value)


def eval_integrand_mid_radius_decimal(f: Any, eta: Decimal) -> tuple[Decimal, Decimal]:
    value = f(acb(arb(str(eta))), True).real
    return arb_mid_radius_decimal(value)


def fit_centered_polynomial(
    xs: list[Decimal],
    ys: list[float],
    *,
    center: Decimal,
    degree: int,
) -> list[float]:
    shifted = np.array([float(x - center) for x in xs], dtype=float)
    values = np.array(ys, dtype=float)
    coeff = np.polynomial.polynomial.polyfit(shifted, values, deg=degree)
    return [float(c) for c in coeff]


def solve_decimal_linear_system(
    matrix: list[list[Decimal]], rhs: list[Decimal]
) -> list[Decimal]:
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if aug[pivot][col] == 0:
            raise ValueError("singular decimal interpolation matrix")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pivot_value = aug[col][col]
        for j in range(col, n + 1):
            aug[col][j] /= pivot_value
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0:
                continue
            for j in range(col, n + 1):
                aug[row][j] -= factor * aug[col][j]
    return [aug[row][n] for row in range(n)]


def fit_centered_polynomial_decimal(
    xs: list[Decimal],
    ys: list[Decimal],
    *,
    center: Decimal,
    degree: int,
) -> list[Decimal]:
    if len(xs) != degree + 1 or len(ys) != degree + 1:
        raise ValueError("decimal interpolation expects degree + 1 samples")
    matrix = []
    for x in xs:
        shifted = x - center
        row = []
        power = Decimal(1)
        for _ in range(degree + 1):
            row.append(power)
            power *= shifted
        matrix.append(row)
    return solve_decimal_linear_system(matrix, ys)


def eval_poly(coeff: list[float], shifted: float) -> float:
    total = 0.0
    power = 1.0
    for c in coeff:
        total += c * power
        power *= shifted
    return total


def eval_poly_decimal(coeff: list[Decimal], shifted: Decimal) -> Decimal:
    total = Decimal(0)
    power = Decimal(1)
    for c in coeff:
        total += c * power
        power *= shifted
    return total


def polynomial_integral(coeff: list[float], *, left: Decimal, right: Decimal, center: Decimal) -> float:
    a = float(left - center)
    b = float(right - center)
    total = 0.0
    for i, c in enumerate(coeff):
        total += c * ((b ** (i + 1) - a ** (i + 1)) / float(i + 1))
    return total


def polynomial_integral_decimal(
    coeff: list[Decimal], *, left: Decimal, right: Decimal, center: Decimal
) -> Decimal:
    a = left - center
    b = right - center
    total = Decimal(0)
    for i, c in enumerate(coeff):
        n = i + 1
        total += c * ((b ** n - a ** n) / Decimal(n))
    return total


def rationalize_float(value: float, denom: int) -> str:
    if not math.isfinite(value):
        return "nan"
    scaled = round(value * denom)
    return f"{scaled}/{denom}"


def rationalize_float_ceil_nonneg(value: float, denom: int) -> str:
    if not math.isfinite(value):
        return "nan"
    scaled = math.ceil(max(0.0, value) * denom)
    return f"{scaled}/{denom}"


def rationalize_decimal(value: Decimal, denom: int) -> str:
    scaled = int((value * Decimal(denom)).to_integral_value())
    return f"{scaled}/{denom}"


def rationalize_decimal_ceil_nonneg(value: Decimal, denom: int) -> str:
    scaled = int(
        (max(Decimal(0), value) * Decimal(denom)).to_integral_value(
            rounding=ROUND_CEILING
        )
    )
    return f"{scaled}/{denom}"


def probe_degree_decimal(
    *,
    f: Any,
    left: Decimal,
    right: Decimal,
    center: Decimal,
    degree: int,
    check_samples: int,
    rational_denominator: int,
    residual_guard: Decimal,
) -> dict[str, Any]:
    fit_xs = sample_points(left, right, degree + 1)
    fit_values = [eval_integrand_mid_radius_decimal(f, eta)[0] for eta in fit_xs]
    coeff = fit_centered_polynomial_decimal(
        fit_xs, fit_values, center=center, degree=degree
    )

    max_residual = Decimal(0)
    max_eval_radius = Decimal(0)
    worst_eta = left
    for eta in sample_points(left, right, check_samples):
        mid, radius = eval_integrand_mid_radius_decimal(f, eta)
        shifted = eta - center
        residual = abs(mid - eval_poly_decimal(coeff, shifted)) + radius
        if residual > max_residual:
            max_residual = residual
            worst_eta = eta
        max_eval_radius = max(max_eval_radius, radius)

    remainder = max_residual * (Decimal(1) + residual_guard) + Decimal("1e-90")
    poly_int = polynomial_integral_decimal(coeff, left=left, right=right, center=center)
    width = right - left
    lower_model_integral = poly_int - width * remainder
    upper_model_integral = poly_int + width * remainder
    model_interval_width = upper_model_integral - lower_model_integral

    return {
        "degree": degree,
        "coeff_float": [float(c) for c in coeff],
        "coeff_decimal": [format(c, ".36E") for c in coeff],
        "coeff_rational_candidate": [
            rationalize_decimal(c, rational_denominator) for c in coeff
        ],
        "sampled_max_residual": format(max_residual, ".18E"),
        "sampled_max_eval_radius": format(max_eval_radius, ".18E"),
        "residual_guard": format(residual_guard, ".18E"),
        "remainder_candidate": format(remainder, ".18E"),
        "remainder_rational_candidate": rationalize_decimal_ceil_nonneg(
            remainder, rational_denominator
        ),
        "polynomial_integral": format(poly_int, ".18E"),
        "lower_model_integral": format(lower_model_integral, ".18E"),
        "upper_model_integral": format(upper_model_integral, ".18E"),
        "model_interval_width": format(model_interval_width, ".18E"),
        "worst_eta": decimal_str(worst_eta),
        "left": decimal_str(left),
        "right": decimal_str(right),
        "center": decimal_str(center),
        "fit_backend": "decimal_interpolation",
    }


def model_interval_for_degree(
    *,
    f: Any,
    left: Decimal,
    right: Decimal,
    center: Decimal,
    degree: int,
    fit_samples: int,
    check_samples: int,
    rational_denominator: int,
    residual_guard: float,
    fit_backend: str,
) -> dict[str, Any]:
    if fit_backend == "decimal":
        return probe_degree_decimal(
            f=f,
            left=left,
            right=right,
            center=center,
            degree=degree,
            check_samples=check_samples,
            rational_denominator=rational_denominator,
            residual_guard=Decimal(str(residual_guard)),
        )
    if fit_backend != "float":
        raise ValueError(f"unknown fit backend {fit_backend!r}")

    fit_xs = sample_points(left, right, fit_samples)
    fit_values = [eval_integrand_mid_radius(f, eta)[0] for eta in fit_xs]
    coeff = fit_centered_polynomial(fit_xs, fit_values, center=center, degree=degree)

    max_residual = 0.0
    max_eval_radius = 0.0
    worst_eta = left
    for eta in sample_points(left, right, check_samples):
        mid, radius = eval_integrand_mid_radius(f, eta)
        shifted = float(eta - center)
        residual = abs(mid - eval_poly(coeff, shifted)) + radius
        if residual > max_residual:
            max_residual = residual
            worst_eta = eta
        max_eval_radius = max(max_eval_radius, radius)

    remainder = max_residual * (1.0 + residual_guard) + 1e-45
    poly_int = polynomial_integral(coeff, left=left, right=right, center=center)
    width = float(right - left)
    lower_model_integral = poly_int - width * remainder
    upper_model_integral = poly_int + width * remainder
    model_interval_width = upper_model_integral - lower_model_integral

    return {
        "degree": degree,
        "coeff_float": coeff,
        "coeff_rational_candidate": [
            rationalize_float(c, rational_denominator) for c in coeff
        ],
        "sampled_max_residual": f"{max_residual:.18e}",
        "sampled_max_eval_radius": f"{max_eval_radius:.18e}",
        "residual_guard": f"{residual_guard:.18e}",
        "remainder_candidate": f"{remainder:.18e}",
        "remainder_rational_candidate": rationalize_float_ceil_nonneg(
            remainder, rational_denominator
        ),
        "polynomial_integral": f"{poly_int:.18e}",
        "lower_model_integral": f"{lower_model_integral:.18e}",
        "upper_model_integral": f"{upper_model_integral:.18e}",
        "model_interval_width": f"{model_interval_width:.18e}",
        "worst_eta": decimal_str(worst_eta),
        "left": decimal_str(left),
        "right": decimal_str(right),
        "center": decimal_str(center),
    }


def probe_degree(
    *,
    f: Any,
    left: Decimal,
    right: Decimal,
    center: Decimal,
    chunk_lower: Decimal,
    chunk_upper: Decimal,
    degree: int,
    fit_samples: int,
    check_samples: int,
    rational_denominator: int,
    residual_guard: float,
    fit_backend: str,
) -> dict[str, Any]:
    model = model_interval_for_degree(
        f=f,
        left=left,
        right=right,
        center=center,
        degree=degree,
        fit_samples=fit_samples,
        check_samples=check_samples,
        rational_denominator=rational_denominator,
        residual_guard=residual_guard,
        fit_backend=fit_backend,
    )
    poly_int = float(model["polynomial_integral"])
    lower_model_integral = float(model["lower_model_integral"])
    upper_model_integral = float(model["upper_model_integral"])
    current_chunk_width = float(chunk_upper - chunk_lower)
    model_interval_width = float(model["model_interval_width"])
    width = float(right - left)
    remainder = float(model["remainder_candidate"])
    lower_margin = lower_model_integral - float(chunk_lower)
    upper_margin = float(chunk_upper) - upper_model_integral
    required_remainder_cap = min(
        (poly_int - float(chunk_lower)) / width,
        (float(chunk_upper) - poly_int) / width,
    )
    fits_integral_interval = lower_margin >= 0.0 and upper_margin >= 0.0
    fits_sampled_residual_and_integral = fits_integral_interval and remainder <= required_remainder_cap

    return {
        "degree": degree,
        "coeff_float": model["coeff_float"],
        "coeff_rational_candidate": model["coeff_rational_candidate"],
        "sampled_max_residual": model["sampled_max_residual"],
        "sampled_max_eval_radius": model["sampled_max_eval_radius"],
        "residual_guard": model["residual_guard"],
        "remainder_candidate": model["remainder_candidate"],
        "remainder_rational_candidate": model["remainder_rational_candidate"],
        "polynomial_integral": model["polynomial_integral"],
        "lower_model_integral": model["lower_model_integral"],
        "upper_model_integral": model["upper_model_integral"],
        "current_chunk_width": f"{current_chunk_width:.18e}",
        "model_interval_width": model["model_interval_width"],
        "extra_chunk_width_needed": f"{max(0.0, model_interval_width - current_chunk_width):.18e}",
        "chunk_lower": decimal_str(chunk_lower),
        "chunk_upper": decimal_str(chunk_upper),
        "lower_integral_margin": f"{lower_margin:.18e}",
        "upper_integral_margin": f"{upper_margin:.18e}",
        "required_remainder_cap": f"{required_remainder_cap:.18e}",
        "worst_eta": model["worst_eta"],
        "fits_integral_interval": fits_integral_interval,
        "fits_sampled_residual_and_integral": fits_sampled_residual_and_integral,
        "failure_mode": (
            "model_interval_wider_than_current_chunk_interval"
            if not fits_sampled_residual_and_integral
            and model_interval_width > current_chunk_width
            else "candidate_not_sampled_feasible"
            if not fits_sampled_residual_and_integral
            else "sampled_feasible"
        ),
    }


def virtual_subchunk_edges(left: Decimal, right: Decimal, count: int) -> list[tuple[Decimal, Decimal]]:
    if count < 1:
        raise ValueError("virtual subchunk count must be positive")
    step = (right - left) / Decimal(count)
    return [
        (left + Decimal(i) * step, left + Decimal(i + 1) * step)
        for i in range(count)
    ]


def probe_virtual_subchunks(
    *,
    f: Any,
    left: Decimal,
    right: Decimal,
    chunk_lower: Decimal,
    chunk_upper: Decimal,
    degrees: list[int],
    subchunk_count: int,
    fit_samples: int,
    check_samples: int,
    rational_denominator: int,
    residual_guard: float,
    fit_backend: str,
    preview_limit: int,
) -> list[dict[str, Any]]:
    if subchunk_count <= 1:
        return []
    parent_width = float(chunk_upper - chunk_lower)
    out = []
    for degree in degrees:
        sub_results = []
        total_lower = Decimal(0)
        total_upper = Decimal(0)
        max_residual = Decimal(0)
        for sub_left, sub_right in virtual_subchunk_edges(left, right, subchunk_count):
            center = (sub_left + sub_right) / Decimal(2)
            model = model_interval_for_degree(
                f=f,
                left=sub_left,
                right=sub_right,
                center=center,
                degree=degree,
                fit_samples=fit_samples,
                check_samples=check_samples,
                rational_denominator=rational_denominator,
                residual_guard=residual_guard,
                fit_backend=fit_backend,
            )
            total_lower += Decimal(model["lower_model_integral"])
            total_upper += Decimal(model["upper_model_integral"])
            max_residual = max(max_residual, Decimal(model["sampled_max_residual"]))
            sub_results.append(model)
        total_width = total_upper - total_lower
        parent_width = chunk_upper - chunk_lower
        fits_parent = total_lower >= chunk_lower and total_upper <= chunk_upper
        preview = sub_results if preview_limit < 0 else sub_results[:preview_limit]
        out.append(
            {
                "degree": degree,
                "virtual_subchunks": subchunk_count,
                "total_lower_model_integral": format(total_lower, ".18E"),
                "total_upper_model_integral": format(total_upper, ".18E"),
                "total_model_interval_width": format(total_width, ".18E"),
                "parent_current_chunk_width": format(parent_width, ".18E"),
                "extra_parent_width_needed": format(
                    max(Decimal(0), total_width - parent_width), ".18E"
                ),
                "max_subchunk_sampled_residual": format(max_residual, ".18E"),
                "fits_parent_interval": fits_parent,
                "failure_mode": (
                    "split_model_interval_wider_than_parent_chunk_interval"
                    if total_width > parent_width
                    else "split_integral_center_mismatch"
                    if not fits_parent
                    else "sampled_feasible"
                ),
                "subchunk_preview_count": len(preview),
                "subchunk_total_count": len(sub_results),
                "subchunk_preview": preview,
            }
        )
    return out


def probe_cell(
    *,
    args: argparse.Namespace,
    family: dict[str, Any],
    row: dict[str, Any],
    chunk: dict[str, Any],
    proof_cell: dict[str, Any],
) -> dict[str, Any]:
    builder = make_builder(args, family=family)
    d = Decimal(row["distance"])
    f = chunk_integrand(args=args, builder=builder, family=family, d=d)
    left = Decimal(chunk["left"])
    right = Decimal(chunk["right"])
    center = decimal_from_any(proof_cell.get("center"))
    chunk_lower = decimal_from_any(proof_cell.get("chunkLower"))
    chunk_upper = decimal_from_any(proof_cell.get("chunkUpper"))

    degree_results = [
        probe_degree(
            f=f,
            left=left,
            right=right,
            center=center,
            chunk_lower=chunk_lower,
            chunk_upper=chunk_upper,
            degree=degree,
            fit_samples=args.fit_samples,
            check_samples=args.check_samples,
            rational_denominator=args.rational_denominator,
            residual_guard=args.residual_guard,
            fit_backend=args.fit_backend,
        )
        for degree in parse_int_csv(args.degrees)
    ]
    feasible = [
        result
        for result in degree_results
        if result["fits_sampled_residual_and_integral"]
    ]
    virtual_results = probe_virtual_subchunks(
        f=f,
        left=left,
        right=right,
        chunk_lower=chunk_lower,
        chunk_upper=chunk_upper,
        degrees=parse_int_csv(args.degrees),
        subchunk_count=args.virtual_subchunks,
        fit_samples=args.fit_samples,
        check_samples=args.check_samples,
        rational_denominator=args.rational_denominator,
        residual_guard=args.residual_guard,
        fit_backend=args.fit_backend,
        preview_limit=args.virtual_preview_limit,
    )
    best = min(
        degree_results,
        key=lambda result: abs(float(result["lower_integral_margin"]))
        + abs(float(result["upper_integral_margin"])),
    )
    return {
        "family_id": family["id"],
        "distance_index": int(row["index"]),
        "distance": row["distance"],
        "chunk_index": int(chunk["index"]),
        "left": decimal_str(left),
        "right": decimal_str(right),
        "center": decimal_str(center),
        "radius": proof_cell.get("radius"),
        "chunk_lower": decimal_str(chunk_lower),
        "chunk_upper": decimal_str(chunk_upper),
        "feasible_degrees": [result["degree"] for result in feasible],
        "best_degree_by_integral_margin": best["degree"],
        "degree_results": degree_results,
        "virtual_subchunk_results": virtual_results,
    }


def render_md(result: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Taylor Model Probe",
        "",
        "Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model",
        "data.  This is not a Lean proof and does not emit payload declarations.",
        "",
        "## Summary",
        "",
        f"- source: `{result['parameters']['source']}`",
        f"- cells checked: {result['totals']['cells_checked']}",
        f"- cells with sampled feasible degree: {result['totals']['cells_with_feasible_degree']}",
        f"- degrees: `{result['parameters']['degrees']}`",
        f"- fit samples: {result['parameters']['fit_samples']}",
        f"- check samples: {result['parameters']['check_samples']}",
        "",
    ]
    aggregates = result.get("degree_aggregates", [])
    if aggregates:
        lines.extend(
            [
                "## Degree Aggregates",
                "",
                "| degree | parent total width | virtual total width | worst virtual chunk |",
                "| ---: | ---: | ---: | ---: |",
            ]
        )
        for item in aggregates:
            lines.append(
                f"| {item['degree']} | `{item['parent_total_model_width']}` | "
                f"`{item['virtual_total_model_width']}` | "
                f"{item['virtual_worst_chunk_index']} |"
            )
        lines.append("")
    lines.extend(
        [
            "## Cells",
            "",
            "| family | row | d | chunk | feasible degrees | best margin degree |",
            "| --- | ---: | ---: | ---: | --- | ---: |",
        ]
    )
    for cell in result["cells"]:
        feasible = ",".join(str(d) for d in cell["feasible_degrees"]) or "-"
        lines.append(
            f"| `{cell['family_id']}` | {cell['distance_index']} | "
            f"`{cell['distance']}` | {cell['chunk_index']} | `{feasible}` | "
            f"{cell['best_degree_by_integral_margin']} |"
        )
    lines.extend(["", "## Best Degree Details", ""])
    for cell in result["cells"]:
        best_degree = cell["best_degree_by_integral_margin"]
        best = next(r for r in cell["degree_results"] if r["degree"] == best_degree)
        lines.extend(
            [
                f"### {cell['family_id']} row {cell['distance_index']} chunk {cell['chunk_index']}",
                "",
                f"- chunk interval: `[{cell['chunk_lower']}, {cell['chunk_upper']}]`",
                f"- degree: `{best_degree}`",
                f"- sampled max residual: `{best['sampled_max_residual']}`",
                f"- remainder candidate: `{best['remainder_candidate']}`",
                f"- lower model integral: `{best['lower_model_integral']}`",
                f"- upper model integral: `{best['upper_model_integral']}`",
                f"- current chunk width: `{best['current_chunk_width']}`",
                f"- model interval width: `{best['model_interval_width']}`",
                f"- extra chunk width needed: `{best['extra_chunk_width_needed']}`",
                f"- lower margin: `{best['lower_integral_margin']}`",
                f"- upper margin: `{best['upper_integral_margin']}`",
                f"- required remainder cap: `{best['required_remainder_cap']}`",
                f"- failure mode: `{best['failure_mode']}`",
                f"- fits sampled residual and integral: `{best['fits_sampled_residual_and_integral']}`",
                "",
            ]
        )
        virtual = cell.get("virtual_subchunk_results", [])
        if virtual:
            lines.extend(
                [
                    "#### Virtual Subchunk Summary",
                    "",
                    "| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |",
                    "| ---: | ---: | ---: | ---: | ---: | --- |",
                ]
            )
            for item in virtual:
                lines.append(
                    f"| {item['degree']} | {item['virtual_subchunks']} | "
                    f"`{item['total_model_interval_width']}` | "
                    f"`{item['extra_parent_width_needed']}` | "
                    f"`{item['max_subchunk_sampled_residual']}` | "
                    f"`{item['failure_mode']}` |"
                )
            lines.append("")
    return "\n".join(lines)


def degree_aggregates(cells: list[dict[str, Any]]) -> list[dict[str, Any]]:
    degrees = sorted(
        {
            result["degree"]
            for cell in cells
            for result in cell.get("degree_results", [])
        }
    )
    out = []
    for degree in degrees:
        parent_total = Decimal(0)
        virtual_total = Decimal(0)
        virtual_worst_width = Decimal(0)
        virtual_worst_chunk_index = None
        virtual_count = 0
        for cell in cells:
            parent = next(
                (
                    result
                    for result in cell.get("degree_results", [])
                    if result["degree"] == degree
                ),
                None,
            )
            if parent is not None:
                parent_total += Decimal(parent["model_interval_width"])
            virtual = next(
                (
                    result
                    for result in cell.get("virtual_subchunk_results", [])
                    if result["degree"] == degree
                ),
                None,
            )
            if virtual is not None:
                width = Decimal(virtual["total_model_interval_width"])
                virtual_total += width
                virtual_count += 1
                if width > virtual_worst_width:
                    virtual_worst_width = width
                    virtual_worst_chunk_index = cell["chunk_index"]
        out.append(
            {
                "degree": degree,
                "parent_total_model_width": format(parent_total, ".18E"),
                "virtual_total_model_width": (
                    format(virtual_total, ".18E") if virtual_count else None
                ),
                "virtual_cells_counted": virtual_count,
                "virtual_worst_chunk_index": virtual_worst_chunk_index,
                "virtual_worst_chunk_width": (
                    format(virtual_worst_width, ".18E") if virtual_count else None
                ),
            }
        )
    return out


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--proof-data", type=Path, default=DEFAULT_PROOF_DATA)
    parser.add_argument("--families", type=str, default="primary_finite")
    parser.add_argument("--indices", type=str, default="0")
    parser.add_argument("--chunk-indices", type=str, default="0")
    parser.add_argument("--source", choices=["raw_step22", "centered_receiver"], default="raw_step22")
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--rel-tol", type=str, default="1e-40")
    parser.add_argument("--abs-tol", type=str, default="1e-40")
    parser.add_argument("--deg-limit", type=int, default=64)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=20)
    parser.add_argument("--sinc-terms", type=int, default=90)
    parser.add_argument("--omega-factor", type=str, default="10")
    parser.add_argument("--radius-floor", type=str, default="1e-30")
    parser.add_argument("--arb-prec", type=int, default=192)
    parser.add_argument("--degrees", type=str, default="0,1,2,3,4,5,6")
    parser.add_argument("--fit-samples", type=int, default=17)
    parser.add_argument("--check-samples", type=int, default=81)
    parser.add_argument("--rational-denominator", type=int, default=10**18)
    parser.add_argument("--residual-guard", type=float, default=0.10)
    parser.add_argument(
        "--fit-backend",
        choices=["decimal", "float"],
        default="decimal",
        help=(
            "Polynomial fit backend. Decimal interpolation avoids the double "
            "precision floor that is too coarse for row slack near 1e-18."
        ),
    )
    parser.add_argument(
        "--virtual-subchunks",
        type=int,
        default=1,
        help=(
            "Diagnostic-only split of each selected worklist chunk into this "
            "many equal virtual subchunks.  This does not mutate the worklist."
        ),
    )
    parser.add_argument(
        "--virtual-preview-limit",
        type=int,
        default=3,
        help=(
            "How many virtual subchunk diagnostics to store per degree.  Use -1 "
            "for all subchunks in small pilot runs.  Still diagnostic only."
        ),
    )
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    worklist = load_worklist(args.worklist)
    proof_data = load_json(args.proof_data)
    proof_cells = proof_data_cell_map(proof_data)

    cells = []
    for family in selected_families(worklist, args.families):
        selected_chunk_rows, _full_chunk_row = selected_chunks(family, args.chunk_indices)
        selected_chunk_by_index = {
            int(chunk["index"]): chunk for chunk in selected_chunk_rows
        }
        for row in selected_distance_rows(family, args.indices):
            for chunk_index, chunk in selected_chunk_by_index.items():
                key = (str(family["id"]), int(row["index"]), chunk_index)
                proof_cell = proof_cells.get(key)
                if proof_cell is None:
                    raise ValueError(f"missing proof-data cell {key}")
                cells.append(
                    probe_cell(
                        args=args,
                        family=family,
                        row=row,
                        chunk=chunk,
                        proof_cell=proof_cell,
                    )
                )

    result = {
        "schema": "q3_psdpd_step33_a_chunk_taylor_model_probe.v1",
        "meaning": (
            "Diagnostic sampled Taylor/model feasibility probe for the raw-Omega "
            "PayloadFin backend.  Arb/acb point values are search evidence only; "
            "this file is not a proof artifact and must not be imported by Lean."
        ),
        "source_worklist": str(args.worklist),
        "source_proof_data": str(args.proof_data),
        "parameters": {
            "families": args.families,
            "indices": args.indices,
            "chunk_indices": args.chunk_indices,
            "source": args.source,
            "degrees": args.degrees,
            "fit_samples": args.fit_samples,
            "check_samples": args.check_samples,
            "arb_prec": args.arb_prec,
            "residual_guard": args.residual_guard,
            "rational_denominator": args.rational_denominator,
            "virtual_subchunks": args.virtual_subchunks,
            "virtual_preview_limit": args.virtual_preview_limit,
            "fit_backend": args.fit_backend,
        },
        "totals": {
            "cells_checked": len(cells),
            "cells_with_feasible_degree": sum(
                1 for cell in cells if cell["feasible_degrees"]
            ),
        },
        "degree_aggregates": degree_aggregates(cells),
        "cells": cells,
        "route_guard": [
            "diagnostic only",
            "do not emit Lean payload from this file",
            "Arb/acb point samples may guide coefficient choice only",
            "Lean must still prove raw bounds, polynomial bounds, diff bounds, and integral comparisons",
        ],
    }

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(result) + "\n", encoding="utf-8")

    print(
        "status=taylor_model_probe cells={cells} feasible={feasible} out_json={out_json}".format(
            cells=result["totals"]["cells_checked"],
            feasible=result["totals"]["cells_with_feasible_degree"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
