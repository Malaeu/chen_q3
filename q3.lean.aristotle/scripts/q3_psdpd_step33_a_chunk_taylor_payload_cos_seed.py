#!/usr/bin/env python3
"""Seed universal cosine-envelope proofs for the Step33 A Taylor payload.

This pass fills only the cosine component fields for every chunk:

* `cosLower = -1`
* `cosUpper = 1`
* Lean proofs from the universal bounds `-1 <= cos _` and `cos _ <= 1`

It deliberately does not add Taylor coefficients, Omega/shape enclosures,
polynomial bounds, or integral comparisons.  The output must therefore still
fail the Lean-emitter completeness guard.
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
from q3_psdpd_step33_a_chunk_taylor_payload_scale_seed import (
    DEFAULT_OUT_JSON as DEFAULT_SCALE_SEED,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_cos_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_cos_seed.md"

COS_FIELDS = {
    "cosLower": "-1",
    "cosUpper": "1",
    "cosLowerBound": (
        "by\n"
        "  intro eta heta\n"
        "  exact RawOmegaAChunkIntegral.cos_neg_one_le_mul eta ((n.1 : Real) / 4)"
    ),
    "cosUpperBound": (
        "by\n"
        "  intro eta heta\n"
        "  exact RawOmegaAChunkIntegral.cos_mul_le_one eta ((n.1 : Real) / 4)"
    ),
}


def add_cos_envelope(seed: dict[str, Any], *, overwrite: bool) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")

    families = []
    total_rows = 0
    total_cells = 0
    cos_seeded_cells = 0
    cos_already_present_cells = 0
    field_seed_counts = {field: 0 for field in COS_FIELDS}

    for family in seed.get("families", []):
        rows = []
        family_seeded_cells = 0
        family_already_present_cells = 0
        for row in family.get("distances", []):
            chunks = []
            for chunk in row.get("chunks", []):
                seeded_chunk = dict(chunk)
                seeded_any = False
                already_complete = all(
                    seeded_chunk.get(field) is not None for field in COS_FIELDS
                )
                for field, value in COS_FIELDS.items():
                    if seeded_chunk.get(field) is None or overwrite:
                        seeded_chunk[field] = value
                        field_seed_counts[field] += 1
                        seeded_any = True
                if seeded_any:
                    seeded_chunk["cosEnvelopeSeedSource"] = (
                        "universal_real_cos_bounds"
                    )
                    seeded_chunk["cosEnvelopeProofStatus"] = (
                        "shared_lean_theorem_pending_generated_payload_check"
                    )
                    family_seeded_cells += 1
                    cos_seeded_cells += 1
                elif already_complete:
                    family_already_present_cells += 1
                    cos_already_present_cells += 1
                chunks.append(seeded_chunk)
                total_cells += 1

            seeded_row = dict(row)
            seeded_row["chunks"] = chunks
            rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = rows
        seeded_family["cosEnvelopeSeededCells"] = family_seeded_cells
        seeded_family["cosEnvelopeAlreadyPresentCells"] = (
            family_already_present_cells
        )
        families.append(seeded_family)

    cos_seed = dict(seed)
    cos_seed["status"] = (
        "cos_envelope_seed_chunk_bounds_geometry_row_sums_scale_and_cos"
    )
    cos_seed["meaning"] = (
        "Candidate chunk bounds, deterministic chunk geometry, row-sum "
        "arithmetic proof terms, shared family scale nonnegativity proofs, "
        "and universal cosine-envelope proof terms are present.  Analytic "
        "Taylor/model proof data is still missing."
    )
    cos_seed["families"] = families
    cos_seed["cosEnvelopeSeedSource"] = "universal_real_cos_bounds"
    cos_seed["totals"] = {
        "families": len(families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "cosEnvelopeSeededCells": cos_seeded_cells,
        "cosEnvelopeAlreadyPresentCells": cos_already_present_cells,
        "cosFieldSeedCounts": field_seed_counts,
        "populatedProofCells": total_cells,
        "rowSumFailures": seed.get("totals", {}).get("rowSumFailures", None),
    }
    cos_seed["routeGuard"] = [
        "cosEnvelope is the universal -1 <= cos <= 1 Lean theorem envelope",
        "this seed does not contain Omega or shape-square enclosure data",
        "this seed does not contain Taylor polynomial or remainder proof data",
        "do not emit Lean until all proof-data fields are complete",
    ]
    return cos_seed


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    field_counts = totals["cosFieldSeedCounts"]
    lines = [
        "# Step33A.1-A Taylor Payload Cosine Seed",
        "",
        "This seed adds universal cosine-envelope proof terms on top of",
        "the current scale seed.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- cosine-envelope seeded cells: `{totals['cosEnvelopeSeededCells']}`",
        "- lower proof: `RawOmegaAChunkIntegral.cos_neg_one_le_mul`",
        "- upper proof: `RawOmegaAChunkIntegral.cos_mul_le_one`",
        "",
        "## Populated Fields",
        "",
    ]
    for field in COS_FIELDS:
        lines.append(f"- `{field}`: `{field_counts[field]}`")
    lines.extend(
        [
            "",
            "## Families",
            "",
            "| family | rows | chunks | cos seeded cells | already present |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for family in seed["families"]:
        lines.append(
            "| {id} | {distanceRows} | {chunkCount} | "
            "{cosEnvelopeSeededCells} | {cosEnvelopeAlreadyPresentCells} |".format(
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
    parser.add_argument("--seed", type=Path, default=DEFAULT_SCALE_SEED)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="replace existing cosine fields instead of preserving them",
    )
    args = parser.parse_args()

    seed = load_json(args.seed)
    cos_seed = add_cos_envelope(seed, overwrite=args.overwrite)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(cos_seed, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(cos_seed), encoding="utf-8")

    totals = cos_seed["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "cos_seeded_cells={seeded} already_present={present}".format(
            status=cos_seed["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            seeded=totals["cosEnvelopeSeededCells"],
            present=totals["cosEnvelopeAlreadyPresentCells"],
        )
    )


if __name__ == "__main__":
    run()
