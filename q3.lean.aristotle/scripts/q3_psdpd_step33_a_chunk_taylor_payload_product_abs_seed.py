#!/usr/bin/env python3
"""Seed direct symmetric product bounds for the Step33 A Taylor payload.

This pass fills the raw-integrand component product layer using the checked
absolute-box helper:

  RawOmegaATaylorModelCertificate.product_bounds_of_scale_abs_box

It deliberately avoids generating the 16-corner scale/product forest.  The
result is still not a complete payload: Taylor coefficients, polynomial value
bounds, diff comparisons, and model integral comparisons remain open.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    PROOF_DATA_SCHEMA,
    load_json,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OMEGA_SMALL_SEED = (
    REQUEST_DIR / "a_chunk_taylor_payload_omega_small_seed.json"
)
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_product_abs_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_product_abs_seed.md"

PRODUCT_FIELDS = [
    "rawLower",
    "rawUpper",
    "componentProductLower",
    "componentProductUpper",
]


FAMILY_CONFIG = {
    "primary_finite": {
        "scale": "primaryK11Ell / Real.pi",
        "scale_nonneg": (
            "RawOmegaAChunkIntegral.primaryK11Ell_div_pi_nonneg"
        ),
        "scale_upper": (
            "RawOmegaAChunkIntegral.primaryK11Ell_div_pi_scaleUpper"
        ),
        "shape_k": "11",
    },
    "primary_tail": {
        "scale": "primaryK11Ell / Real.pi",
        "scale_nonneg": (
            "RawOmegaAChunkIntegral.primaryK11Ell_div_pi_nonneg"
        ),
        "scale_upper": (
            "RawOmegaAChunkIntegral.primaryK11Ell_div_pi_scaleUpper"
        ),
        "shape_k": "11",
    },
    "control_finite": {
        "scale": "controlK9Ell / Real.pi",
        "scale_nonneg": (
            "RawOmegaAChunkIntegral.controlK9Ell_div_pi_nonneg"
        ),
        "scale_upper": (
            "RawOmegaAChunkIntegral.controlK9Ell_div_pi_scaleUpper"
        ),
        "shape_k": "9",
    },
    "control_tail": {
        "scale": "controlK9Ell / Real.pi",
        "scale_nonneg": (
            "RawOmegaAChunkIntegral.controlK9Ell_div_pi_nonneg"
        ),
        "scale_upper": (
            "RawOmegaAChunkIntegral.controlK9Ell_div_pi_scaleUpper"
        ),
        "shape_k": "9",
    },
}


def require_chunk_field(chunk: dict[str, Any], field: str) -> str:
    value = chunk.get(field)
    if value is None:
        raise ValueError(f"chunk is missing required field {field!r}")
    return str(value)


def omega_majorant_nonneg_proof(omega_majorant: str) -> str:
    if "Real.log" not in omega_majorant:
        return "by norm_num"
    return (
        "by\n"
        "  exact mul_nonneg (by norm_num)\n"
        "    (Real.log_nonneg (by norm_num))"
    )


def product_fields_for_chunk(family_id: str, chunk: dict[str, Any]) -> dict[str, str]:
    config = FAMILY_CONFIG.get(family_id)
    if config is None:
        raise ValueError(f"unknown family id {family_id!r}")

    scale_upper = require_chunk_field(chunk, "scaleUpper")
    omega_majorant = require_chunk_field(chunk, "omegaUpper")
    shape_sq_upper = require_chunk_field(chunk, "shapeSqUpper")
    scale = config["scale"]
    scale_nonneg = config["scale_nonneg"]
    scale_upper_proof = config["scale_upper"]
    shape_k = config["shape_k"]
    raw_upper = f"({scale_upper} * {omega_majorant} * {shape_sq_upper})"
    raw_lower = f"(-{raw_upper})"
    common = (
        "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
        "product_bounds_of_scale_abs_box\n"
        f"        (scale := {scale})\n"
        f"        (scaleUpper := {scale_upper})\n"
        f"        (omegaMajorant := {omega_majorant})\n"
        f"        (shapeSqUpper := {shape_sq_upper})\n"
        f"        {scale_nonneg}\n"
        f"        {scale_upper_proof}\n"
        "        (by norm_num)\n"
        f"        {omega_majorant_nonneg_proof(omega_majorant)}\n"
        "        (by\n"
        "          exact RawOmegaAChunkIntegral."
        f"centeredBSplineImagTransformSqGlobalMajorant_nonneg {shape_k})\n"
        "        (by simpa using hOmegaLower)\n"
        "        (by simpa using hOmegaUpper)\n"
        "        (by simpa using hShapeSqLower)\n"
        "        (by simpa using hShapeSqUpper)\n"
        "        (by simpa using hCosLower)\n"
        "        (by simpa using hCosUpper)"
    )
    return {
        "rawLower": raw_lower,
        "rawUpper": raw_upper,
        "componentProductLower": (
            "by\n"
            "  intro omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower\n"
            "    hShapeSqUpper hCosLower hCosUpper\n"
            f"  exact\n"
            f"    ({common}).1"
        ),
        "componentProductUpper": (
            "by\n"
            "  intro omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower\n"
            "    hShapeSqUpper hCosLower hCosUpper\n"
            f"  exact\n"
            f"    ({common}).2"
        ),
    }


def add_product_abs_bounds(seed: dict[str, Any], *, overwrite: bool) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")

    families = []
    total_rows = 0
    total_cells = 0
    seeded_cells = 0
    already_present_cells = 0
    field_seed_counts = {field: 0 for field in PRODUCT_FIELDS}

    for family in seed.get("families", []):
        family_id = str(family["id"])
        rows = []
        family_seeded_cells = 0
        family_already_present_cells = 0
        for row in family.get("distances", []):
            chunks = []
            for chunk in row.get("chunks", []):
                seeded_chunk = dict(chunk)
                already_complete = all(
                    seeded_chunk.get(field) is not None for field in PRODUCT_FIELDS
                )
                if already_complete and not overwrite:
                    family_already_present_cells += 1
                    already_present_cells += 1
                    chunks.append(seeded_chunk)
                    total_cells += 1
                    continue

                fields = product_fields_for_chunk(family_id, seeded_chunk)
                seeded_any = False
                for field, value in fields.items():
                    if seeded_chunk.get(field) is None or overwrite:
                        seeded_chunk[field] = value
                        field_seed_counts[field] += 1
                        seeded_any = True
                if seeded_any:
                    seeded_chunk["productAbsSeedSource"] = (
                        "scale_omega_shape_cos_abs_box_lean_theorem"
                    )
                    seeded_chunk["productAbsProofStatus"] = (
                        "shared_lean_theorem_pending_generated_payload_check"
                    )
                    family_seeded_cells += 1
                    seeded_cells += 1
                chunks.append(seeded_chunk)
                total_cells += 1

            seeded_row = dict(row)
            seeded_row["chunks"] = chunks
            rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = rows
        seeded_family["productAbsSeededCells"] = family_seeded_cells
        seeded_family["productAbsAlreadyPresentCells"] = (
            family_already_present_cells
        )
        families.append(seeded_family)

    product_seed = dict(seed)
    product_seed["status"] = (
        "product_abs_seed_chunk_bounds_geometry_row_sums_scale_cos_shape_omega_and_raw_product"
    )
    product_seed["meaning"] = (
        "Candidate chunk bounds, deterministic chunk geometry, row-sum "
        "arithmetic proof terms, scale/cos/shape/Omega proof terms, and "
        "direct symmetric raw-product proof terms are present. Taylor/model "
        "data, polynomial value bounds, diff comparisons, and integral "
        "comparisons remain open."
    )
    product_seed["families"] = families
    product_seed["productAbsSeedSource"] = (
        "scale_omega_shape_cos_abs_box_lean_theorem"
    )
    product_seed["totals"] = {
        "families": len(families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "productAbsSeededCells": seeded_cells,
        "productAbsAlreadyPresentCells": already_present_cells,
        "productAbsFieldSeedCounts": field_seed_counts,
        "populatedProofCells": total_cells,
        "priorTotals": seed.get("totals", {}),
    }
    product_seed["routeGuard"] = [
        "product bounds use checked absolute-box theorem, not trusted Arb output",
        "direct product fields intentionally bypass 16-corner payload fields",
        "this seed does not contain Taylor polynomial or remainder proof data",
        "do not emit Lean until all proof-data fields are complete",
    ]
    return product_seed


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    field_counts = totals["productAbsFieldSeedCounts"]
    lines = [
        "# Step33A.1-A Taylor Payload Product Abs Seed",
        "",
        "This seed fills direct symmetric raw-product bounds using a checked",
        "absolute-box theorem.  It avoids the generated 16-corner product",
        "payload surface.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- product seeded cells: `{totals['productAbsSeededCells']}`",
        f"- already present cells: `{totals['productAbsAlreadyPresentCells']}`",
        "- theorem: `RawOmegaATaylorModelCertificate.product_bounds_of_scale_abs_box`",
        "",
        "## Populated Fields",
        "",
    ]
    for field in field_counts:
        lines.append(f"- `{field}`: `{field_counts[field]}`")
    lines.extend(
        [
            "",
            "## Families",
            "",
            "| family | rows | chunks | product seeded cells | already present |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for family in seed["families"]:
        lines.append(
            "| {id} | {rows} | {chunks} | {seeded} | {already} |".format(
                id=family["id"],
                rows=family.get("distance_count"),
                chunks=family.get("chunk_count"),
                seeded=family.get("productAbsSeededCells"),
                already=family.get("productAbsAlreadyPresentCells"),
            )
        )
    lines.extend(
        [
            "",
            "## Guard",
            "",
        ]
    )
    for guard in seed["routeGuard"]:
        lines.append(f"- {guard}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_OMEGA_SMALL_SEED)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()

    seed = load_json(args.input)
    product_seed = add_product_abs_bounds(seed, overwrite=args.overwrite)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(product_seed, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.write_text(render_md(product_seed), encoding="utf-8")
    totals = product_seed["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "product_abs_seeded_cells={seeded} already_present={already}".format(
            status=product_seed["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            seeded=totals["productAbsSeededCells"],
            already=totals["productAbsAlreadyPresentCells"],
        )
    )


if __name__ == "__main__":
    main()
