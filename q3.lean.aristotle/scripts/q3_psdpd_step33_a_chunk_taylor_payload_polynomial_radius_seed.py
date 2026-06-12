#!/usr/bin/env python3
"""Seed direct polynomial value bounds from Taylor coeff/radius data.

This pass is intentionally fail-closed.  It only fills the direct polynomial
fields consumed by `ComponentValueChunkProofData` when a cell already has
proof-bearing Taylor model data:

  degree, coeff, radius, radiusLeft, radiusRight

For such cells it uses the checked Lean helper:

  RawOmegaATaylorModelCertificate.polynomial_value_bounds_of_sum_abs_coeff_mul_radius

The pass does not invent Taylor coefficients or remainders.  If those fields
are missing, it reports the missing inputs and leaves the payload unchanged.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, InvalidOperation
from fractions import Fraction
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    PROOF_DATA_SCHEMA,
    load_json,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_PROOF_DATA = REQUEST_DIR / "a_chunk_taylor_payload_product_abs_seed.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_polynomial_radius_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_polynomial_radius_seed.md"

POLYNOMIAL_FIELDS = [
    "polyLower",
    "polyUpper",
    "polynomialLowerBound",
    "polynomialUpperBound",
]

INPUT_FIELDS = [
    "degree",
    "coeff",
    "radius",
    "radiusLeft",
    "radiusRight",
]

FAMILY_PREFIX = {
    "primary_finite": "primaryFinite",
    "primary_tail": "primaryTail",
    "control_finite": "controlFinite",
    "control_tail": "controlTail",
}


def parse_decimal_fraction(value: Any) -> Fraction | None:
    if isinstance(value, int):
        return Fraction(value, 1)
    if not isinstance(value, str):
        return None
    stripped = value.strip()
    try:
        decimal = Decimal(stripped)
    except InvalidOperation:
        return None
    if not decimal.is_finite():
        return None
    return Fraction(decimal)


def lean_rat_expr(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : Rat)"
    return f"(({value.numerator} : Rat) / ({value.denominator} : Rat))"


def lean_real_expr(value: Fraction) -> str:
    return f"({lean_rat_expr(value)} : Real)"


def missing_inputs(chunk: dict[str, Any]) -> list[str]:
    return [field for field in INPUT_FIELDS if chunk.get(field) is None]


def polynomial_abs_bound(chunk: dict[str, Any]) -> Fraction | None:
    degree_raw = chunk.get("degree")
    coeff_raw = chunk.get("coeff")
    radius_raw = chunk.get("radius")
    if not isinstance(degree_raw, int):
        try:
            degree = int(str(degree_raw))
        except (TypeError, ValueError):
            return None
    else:
        degree = degree_raw
    if not isinstance(coeff_raw, list) or len(coeff_raw) != degree + 1:
        return None
    radius = parse_decimal_fraction(radius_raw)
    if radius is None:
        return None
    total = Fraction(0, 1)
    for index, coeff_value in enumerate(coeff_raw):
        coeff = parse_decimal_fraction(coeff_value)
        if coeff is None:
            return None
        total += abs(coeff) * (radius ** index)
    return total


def polynomial_bound_proof(*, prefix: str, side: str, hsum: str,
                           hleft: Any, hright: Any) -> str:
    projection = "1" if side == "lower" else "2"
    return (
        "by\n"
        "  intro eta heta\n"
        "  exact\n"
        "    (RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
        "polynomial_value_bounds_of_sum_abs_coeff_mul_radius\n"
        f"        ({prefix}Cert n i)\n"
        f"        ({hleft})\n"
        f"        ({hright})\n"
        f"        ({hsum})\n"
        "        (by exact le_rfl)\n"
        "        (by exact le_rfl))."
        f"{projection} eta heta"
    )


def seed_chunk(family_id: str, chunk: dict[str, Any], *, overwrite: bool) -> tuple[dict[str, Any], str]:
    seeded = dict(chunk)
    if all(seeded.get(field) is not None for field in POLYNOMIAL_FIELDS) and not overwrite:
        return seeded, "already_present"

    missing = missing_inputs(seeded)
    if missing:
        seeded["polynomialRadiusSeedStatus"] = "missing_inputs"
        seeded["polynomialRadiusMissingInputs"] = missing
        return seeded, "missing_inputs"

    poly_abs = polynomial_abs_bound(seeded)
    if poly_abs is None:
        seeded["polynomialRadiusSeedStatus"] = "unsupported_numeric_input"
        return seeded, "unsupported_numeric_input"

    prefix = FAMILY_PREFIX.get(family_id)
    if prefix is None:
        raise ValueError(f"unknown family id {family_id!r}")

    poly_abs_expr = lean_real_expr(poly_abs)
    hsum = f"by\n          norm_num [{prefix}Cert]"
    hleft = str(seeded["radiusLeft"])
    hright = str(seeded["radiusRight"])

    seeded["polyLower"] = f"(-{poly_abs_expr})"
    seeded["polyUpper"] = poly_abs_expr
    seeded["polynomialLowerBound"] = polynomial_bound_proof(
        prefix=prefix,
        side="lower",
        hsum=hsum,
        hleft=hleft,
        hright=hright,
    )
    seeded["polynomialUpperBound"] = polynomial_bound_proof(
        prefix=prefix,
        side="upper",
        hsum=hsum,
        hleft=hleft,
        hright=hright,
    )
    seeded["polynomialRadiusAbsBound"] = str(poly_abs)
    seeded["polynomialRadiusSeedSource"] = (
        "RawOmegaATaylorModelCertificate.polynomial_value_bounds_of_sum_abs_coeff_mul_radius"
    )
    seeded["polynomialRadiusSeedStatus"] = "seeded"
    return seeded, "seeded"


def seed_payload(payload: dict[str, Any], *, overwrite: bool) -> dict[str, Any]:
    if payload.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {payload.get('schema')!r}")

    counts = {
        "families": 0,
        "distanceRows": 0,
        "chunkCells": 0,
        "seededCells": 0,
        "alreadyPresentCells": 0,
        "missingInputCells": 0,
        "unsupportedNumericInputCells": 0,
    }
    missing_field_counts = {field: 0 for field in INPUT_FIELDS}
    families = []

    for family in payload.get("families", []):
        family_id = str(family["id"])
        rows = []
        family_counts = {
            "families": 1,
            "distanceRows": 0,
            "chunkCells": 0,
            "seededCells": 0,
            "alreadyPresentCells": 0,
            "missingInputCells": 0,
            "unsupportedNumericInputCells": 0,
        }
        for row in family.get("distances", []):
            chunks = []
            for chunk in row.get("chunks", []):
                seeded_chunk, status = seed_chunk(family_id, chunk, overwrite=overwrite)
                chunks.append(seeded_chunk)
                counts["chunkCells"] += 1
                family_counts["chunkCells"] += 1
                if status == "seeded":
                    counts["seededCells"] += 1
                    family_counts["seededCells"] += 1
                elif status == "already_present":
                    counts["alreadyPresentCells"] += 1
                    family_counts["alreadyPresentCells"] += 1
                elif status == "missing_inputs":
                    counts["missingInputCells"] += 1
                    family_counts["missingInputCells"] += 1
                    for field in seeded_chunk.get("polynomialRadiusMissingInputs", []):
                        missing_field_counts[field] += 1
                elif status == "unsupported_numeric_input":
                    counts["unsupportedNumericInputCells"] += 1
                    family_counts["unsupportedNumericInputCells"] += 1
            seeded_row = dict(row)
            seeded_row["chunks"] = chunks
            rows.append(seeded_row)
            counts["distanceRows"] += 1
            family_counts["distanceRows"] += 1

        seeded_family = dict(family)
        seeded_family["distances"] = rows
        seeded_family["polynomialRadiusSeedCounts"] = family_counts
        families.append(seeded_family)
        counts["families"] += 1

    result = dict(payload)
    result["families"] = families
    result["status"] = "polynomial_radius_seed_applied"
    result["meaning"] = (
        "Direct polynomial value bounds have been seeded where degree/coeff/"
        "radius data is already present.  Missing Taylor model data is still "
        "reported and Lean emission remains guarded by the inventory."
    )
    result["polynomialRadiusSeedSource"] = (
        "RawOmegaATaylorModelCertificate.polynomial_value_bounds_of_sum_abs_coeff_mul_radius"
    )
    result["totals"] = {
        **counts,
        "missingInputFieldCounts": missing_field_counts,
        "priorTotals": payload.get("totals", {}),
    }
    result["routeGuard"] = list(payload.get("routeGuard", [])) + [
        "polynomial radius seed does not invent degree/coeff/remainder data",
        "do not emit Lean until inventory reports ready_to_generate_lean_payload",
    ]
    return result


def render_md(payload: dict[str, Any]) -> str:
    totals = payload["totals"]
    lines = [
        "# Step33A.1-A Taylor Payload Polynomial Radius Seed",
        "",
        "This seed pass fills direct polynomial value-bound fields only after",
        "`degree`, `coeff`, `radius`, `radiusLeft`, and `radiusRight` already",
        "exist for a cell.",
        "",
        "## Verdict",
        "",
        f"- status: `{payload['status']}`",
        f"- source theorem: `{payload['polynomialRadiusSeedSource']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- seeded cells: `{totals['seededCells']}`",
        f"- already present cells: `{totals['alreadyPresentCells']}`",
        f"- missing input cells: `{totals['missingInputCells']}`",
        f"- unsupported numeric input cells: `{totals['unsupportedNumericInputCells']}`",
        "",
        "## Missing Input Field Counts",
        "",
    ]
    for field, count in totals["missingInputFieldCounts"].items():
        lines.append(f"- `{field}`: `{count}`")
    lines.extend(["", "## Route Guard", ""])
    for item in payload["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proof-data", type=Path, default=DEFAULT_PROOF_DATA)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()

    payload = load_json(args.proof_data)
    seeded = seed_payload(payload, overwrite=args.overwrite)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(seeded, indent=2, sort_keys=True) + "\n")
    args.out_md.write_text(render_md(seeded), encoding="utf-8")
    totals = seeded["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "seeded={seeded_cells} missing_input_cells={missing_inputs} "
        "unsupported={unsupported}".format(
            status=seeded["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            seeded_cells=totals["seededCells"],
            missing_inputs=totals["missingInputCells"],
            unsupported=totals["unsupportedNumericInputCells"],
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(run())
