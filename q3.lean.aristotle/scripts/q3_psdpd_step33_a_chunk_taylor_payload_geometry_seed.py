#!/usr/bin/env python3
"""Add deterministic chunk geometry fields to the Step33 A proof-data seed.

This script fills only geometry data derived from each chunk endpoint:

* `center = (left + right) / 2`
* `radius = (right - left) / 2`
* arithmetic proof terms for `radiusNonneg`, `radiusLeft`, and `radiusRight`

It does not add Taylor coefficients, analytic component bounds, polynomial-term
proofs, or row sums.  The output must therefore still fail the Lean-emitter
completeness guard.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    PROOF_DATA_SCHEMA,
    load_json,
)
from q3_psdpd_step33_a_chunk_taylor_payload_seed_from_probe import (
    DEFAULT_OUT_JSON as DEFAULT_PROBE_SEED,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_geometry_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_geometry_seed.md"


def parse_decimal(value: Any, *, label: str) -> Decimal:
    try:
        decimal = Decimal(str(value))
    except InvalidOperation as exc:
        raise ValueError(f"{label}: invalid decimal {value!r}") from exc
    if not decimal.is_finite():
        raise ValueError(f"{label}: non-finite decimal {value!r}")
    return decimal


def decimal_string(value: Decimal) -> str:
    if value == 0:
        return "0"
    return format(value.normalize(), "E")


def arithmetic_proof_for_family(family: dict[str, Any]) -> str:
    if str(family.get("familyKind")) == "tail":
        return "by norm_num [rawOmegaAFiniteTailCutoff]"
    return "by norm_num"


def add_geometry(seed: dict[str, Any]) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")

    families = []
    total_rows = 0
    total_cells = 0
    geometry_cells = 0

    for family in seed.get("families", []):
        proof_term = arithmetic_proof_for_family(family)
        seeded_rows = []
        family_geometry_cells = 0
        for row in family.get("distances", []):
            seeded_chunks = []
            for chunk in row.get("chunks", []):
                left = parse_decimal(chunk.get("left"), label="left")
                right = parse_decimal(chunk.get("right"), label="right")
                if right < left:
                    raise ValueError(
                        f"{family['id']} row {row['index']} chunk {chunk['index']}: "
                        "right endpoint is smaller than left endpoint"
                    )
                center = (left + right) / Decimal(2)
                radius = (right - left) / Decimal(2)
                seeded_chunk = dict(chunk)
                seeded_chunk["center"] = decimal_string(center)
                seeded_chunk["radius"] = decimal_string(radius)
                seeded_chunk["radiusNonneg"] = proof_term
                seeded_chunk["radiusLeft"] = proof_term
                seeded_chunk["radiusRight"] = proof_term
                seeded_chunk["geometrySeedSource"] = "chunk_endpoint_mid_radius"
                seeded_chunk["geometryProofStatus"] = (
                    "arithmetic_norm_num_terms_pending_generated_lean_check"
                )
                seeded_chunks.append(seeded_chunk)
                family_geometry_cells += 1
                geometry_cells += 1
                total_cells += 1

            seeded_row = dict(row)
            seeded_row["chunks"] = seeded_chunks
            seeded_rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = seeded_rows
        seeded_family["geometrySeededCells"] = family_geometry_cells
        families.append(seeded_family)

    geometry_seed = dict(seed)
    geometry_seed["status"] = "geometry_seed_chunk_bounds_and_radius_only"
    geometry_seed["meaning"] = (
        "Candidate chunk bounds plus deterministic chunk midpoint/radius data "
        "and arithmetic proof terms are present.  Analytic Taylor/model proof "
        "fields are still missing."
    )
    geometry_seed["families"] = families
    geometry_seed["geometrySeedSource"] = "chunk_endpoint_mid_radius"
    geometry_seed["totals"] = {
        "families": len(families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "geometrySeededCells": geometry_cells,
        "populatedProofCells": geometry_cells,
    }
    geometry_seed["routeGuard"] = [
        "geometry proof terms are arithmetic only and still need generated Lean check",
        "this seed does not contain Taylor/model analytic proof data",
        "do not emit Lean until all proof-data fields are complete",
    ]
    return geometry_seed


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    lines = [
        "# Step33A.1-A Taylor Payload Geometry Seed",
        "",
        "This seed adds deterministic chunk midpoint/radius data and arithmetic",
        "proof terms on top of the diagnostic chunk-bound seed.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- geometry seeded cells: `{totals['geometrySeededCells']}`",
        f"- populated proof cells: `{totals['populatedProofCells']}`",
        "",
        "## Populated Fields",
        "",
        "- `center`",
        "- `radius`",
        "- `radiusNonneg`",
        "- `radiusLeft`",
        "- `radiusRight`",
        "",
        "## Families",
        "",
        "| family | rows | chunks | geometry seeded cells |",
        "| --- | ---: | ---: | ---: |",
    ]
    for family in seed["families"]:
        lines.append(
            "| {id} | {distanceRows} | {chunkCount} | {geometrySeededCells} |".format(
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
    parser.add_argument("--seed", type=Path, default=DEFAULT_PROBE_SEED)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    seed = load_json(args.seed)
    geometry_seed = add_geometry(seed)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(geometry_seed, indent=2, sort_keys=True) + "\n"
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(geometry_seed), encoding="utf-8")

    totals = geometry_seed["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "geometry_seeded_cells={geometry} populated_proof_cells={proofs}".format(
            status=geometry_seed["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            geometry=totals["geometrySeededCells"],
            proofs=totals["populatedProofCells"],
        )
    )


if __name__ == "__main__":
    run()
