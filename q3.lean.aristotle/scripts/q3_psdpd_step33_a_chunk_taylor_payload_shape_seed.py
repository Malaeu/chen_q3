#!/usr/bin/env python3
"""Seed structural shape-square bounds for the Step33 A Taylor payload.

This pass fills only the centered B-spline transform-square component fields:

* `shapeSqLower = 0`
* `shapeSqUpper = centeredBSplineImagTransformSqGlobalMajorant k`
* Lean proof terms from the checked global sinc envelope

It deliberately leaves Omega enclosures, product corners, Taylor coefficients,
polynomial bounds, and integral comparisons missing.  The output must still
fail the Lean-emitter completeness guard.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_cos_seed import (
    DEFAULT_OUT_JSON as DEFAULT_COS_SEED,
)
from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    PROOF_DATA_SCHEMA,
    load_json,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_shape_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_shape_seed.md"

FAMILY_SHAPE_CONFIG = {
    "primary_finite": {"k": "11", "ell": "primaryK11Ell"},
    "primary_tail": {"k": "11", "ell": "primaryK11Ell"},
    "control_finite": {"k": "9", "ell": "controlK9Ell"},
    "control_tail": {"k": "9", "ell": "controlK9Ell"},
}


def shape_fields_for_family(family_id: str) -> dict[str, str]:
    config = FAMILY_SHAPE_CONFIG.get(family_id)
    if config is None:
        raise ValueError(f"unknown family id {family_id!r}")
    k = config["k"]
    ell = config["ell"]
    return {
        "shapeSqLower": "0",
        "shapeSqUpper": (
            f"RawOmegaAChunkIntegral.centeredBSplineImagTransformSqGlobalMajorant {k}"
        ),
        "shapeSqLowerBound": (
            "by\n"
            "  intro eta heta\n"
            "  exact RawOmegaAChunkIntegral."
            f"centeredBSplineImagTransformRealClosedForm_sq_nonneg {k} {ell} eta"
        ),
        "shapeSqUpperBound": (
            "by\n"
            "  intro eta heta\n"
            "  exact RawOmegaAChunkIntegral."
            f"centeredBSplineImagTransformRealClosedForm_sq_le_globalMajorant {k} {ell} eta"
        ),
    }


def add_shape_square(seed: dict[str, Any], *, overwrite: bool) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")

    families = []
    total_rows = 0
    total_cells = 0
    shape_seeded_cells = 0
    shape_already_present_cells = 0
    field_seed_counts = {
        "shapeSqLower": 0,
        "shapeSqUpper": 0,
        "shapeSqLowerBound": 0,
        "shapeSqUpperBound": 0,
    }

    for family in seed.get("families", []):
        family_id = str(family["id"])
        shape_fields = shape_fields_for_family(family_id)
        rows = []
        family_seeded_cells = 0
        family_already_present_cells = 0
        for row in family.get("distances", []):
            chunks = []
            for chunk in row.get("chunks", []):
                seeded_chunk = dict(chunk)
                seeded_any = False
                already_complete = all(
                    seeded_chunk.get(field) is not None for field in shape_fields
                )
                for field, value in shape_fields.items():
                    if seeded_chunk.get(field) is None or overwrite:
                        seeded_chunk[field] = value
                        field_seed_counts[field] += 1
                        seeded_any = True
                if seeded_any:
                    seeded_chunk["shapeSqSeedSource"] = (
                        "global_sinc_abs_le_one_transform_square_envelope"
                    )
                    seeded_chunk["shapeSqProofStatus"] = (
                        "shared_lean_theorem_pending_generated_payload_check"
                    )
                    family_seeded_cells += 1
                    shape_seeded_cells += 1
                elif already_complete:
                    family_already_present_cells += 1
                    shape_already_present_cells += 1
                chunks.append(seeded_chunk)
                total_cells += 1

            seeded_row = dict(row)
            seeded_row["chunks"] = chunks
            rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = rows
        seeded_family["shapeSqSeededCells"] = family_seeded_cells
        seeded_family["shapeSqAlreadyPresentCells"] = family_already_present_cells
        families.append(seeded_family)

    shape_seed = dict(seed)
    shape_seed["status"] = (
        "shape_square_seed_chunk_bounds_geometry_row_sums_scale_cos_and_shape"
    )
    shape_seed["meaning"] = (
        "Candidate chunk bounds, deterministic chunk geometry, row-sum "
        "arithmetic proof terms, shared family scale interval proofs, "
        "universal cosine envelope proofs, and checked global shape-square "
        "proof terms are present.  Omega/Taylor/model proof data is still "
        "missing."
    )
    shape_seed["families"] = families
    shape_seed["shapeSqSeedSource"] = (
        "global_sinc_abs_le_one_transform_square_envelope"
    )
    shape_seed["totals"] = {
        "families": len(families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "shapeSqSeededCells": shape_seeded_cells,
        "shapeSqAlreadyPresentCells": shape_already_present_cells,
        "shapeSqFieldSeedCounts": field_seed_counts,
        "populatedProofCells": total_cells,
        "rowSumFailures": seed.get("totals", {}).get("rowSumFailures", None),
    }
    shape_seed["routeGuard"] = [
        "shapeSqLower/Upper use checked structural sinc envelope lemmas",
        "this seed does not contain Omega enclosure data",
        "this seed does not contain Taylor polynomial or remainder proof data",
        "do not emit Lean until all proof-data fields are complete",
    ]
    return shape_seed


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    field_counts = totals["shapeSqFieldSeedCounts"]
    lines = [
        "# Step33A.1-A Taylor Payload Shape-Square Seed",
        "",
        "This seed adds structural centered B-spline transform-square bounds on",
        "top of the current cosine seed.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- shape-square seeded cells: `{totals['shapeSqSeededCells']}`",
        "- lower proof: `RawOmegaAChunkIntegral.centeredBSplineImagTransformRealClosedForm_sq_nonneg`",
        "- upper proof: `RawOmegaAChunkIntegral.centeredBSplineImagTransformRealClosedForm_sq_le_globalMajorant`",
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
            "| family | rows | chunks | shape seeded cells | already present |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for family in seed["families"]:
        lines.append(
            "| {id} | {distanceRows} | {chunkCount} | "
            "{shapeSqSeededCells} | {shapeSqAlreadyPresentCells} |".format(
                **family
            )
        )
    lines.extend(["", "## Route Guard", ""])
    for item in seed["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=DEFAULT_COS_SEED)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="replace existing shape-square fields instead of preserving them",
    )
    args = parser.parse_args()

    seed = load_json(args.seed)
    shape_seed = add_shape_square(seed, overwrite=args.overwrite)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(shape_seed, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(shape_seed), encoding="utf-8")

    totals = shape_seed["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "shape_seeded_cells={seeded} already_present={present}".format(
            status=shape_seed["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            seeded=totals["shapeSqSeededCells"],
            present=totals["shapeSqAlreadyPresentCells"],
        )
    )


if __name__ == "__main__":
    run()
