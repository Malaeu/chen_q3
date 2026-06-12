#!/usr/bin/env python3
"""Seed shared scale interval proofs for the Step33 A Taylor payload.

This pass fills the family-level `ell / pi` interval fields used by the
scale-interval product receiver:

* `9/100 <= primaryK11Ell / Real.pi <= 1/10`
* `9/100 <= controlK9Ell / Real.pi <= 1/10`

It also preserves the older `scaleNonneg` compatibility proof field when
present in downstream diagnostic reports.

It deliberately does not add Taylor coefficients, component enclosures,
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
from q3_psdpd_step33_a_chunk_taylor_payload_row_sum_seed import (
    DEFAULT_OUT_JSON as DEFAULT_ROW_SUM_SEED,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_scale_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_scale_seed.md"


SCALE_PROOFS = {
    "primary": "by exact RawOmegaAChunkIntegral.primaryK11Ell_div_pi_nonneg",
    "control": "by exact RawOmegaAChunkIntegral.controlK9Ell_div_pi_nonneg",
}

SCALE_INTERVAL = {
    "scaleLower": "((9 : Real) / 100)",
    "scaleUpper": "((1 : Real) / 10)",
}

SCALE_INTERVAL_PROOFS = {
    "primary": {
        "scaleLowerBound": (
            "by exact RawOmegaAChunkIntegral.primaryK11Ell_div_pi_scaleLower"
        ),
        "scaleUpperBound": (
            "by exact RawOmegaAChunkIntegral.primaryK11Ell_div_pi_scaleUpper"
        ),
    },
    "control": {
        "scaleLowerBound": (
            "by exact RawOmegaAChunkIntegral.controlK9Ell_div_pi_scaleLower"
        ),
        "scaleUpperBound": (
            "by exact RawOmegaAChunkIntegral.controlK9Ell_div_pi_scaleUpper"
        ),
    },
}


def family_mode(family_id: str) -> str:
    if family_id.startswith("primary_"):
        return "primary"
    if family_id.startswith("control_"):
        return "control"
    raise ValueError(f"unknown family id {family_id!r}")


def add_scale_nonneg(seed: dict[str, Any], *, overwrite: bool) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")

    families = []
    total_rows = 0
    total_cells = 0
    scale_nonneg_seeded_cells = 0
    scale_interval_seeded_cells = 0
    already_present_cells = 0

    for family in seed.get("families", []):
        family_id = str(family["id"])
        mode = family_mode(family_id)
        proof = SCALE_PROOFS[mode]
        interval_proofs = SCALE_INTERVAL_PROOFS[mode]
        rows = []
        family_nonneg_seeded_cells = 0
        family_interval_seeded_cells = 0
        family_already_present_cells = 0
        for row in family.get("distances", []):
            chunks = []
            for chunk in row.get("chunks", []):
                seeded_chunk = dict(chunk)
                interval_fields_present = all(
                    seeded_chunk.get(field) is not None
                    for field in (
                        "scaleLower",
                        "scaleUpper",
                        "scaleLowerBound",
                        "scaleUpperBound",
                    )
                )
                if not interval_fields_present or overwrite:
                    seeded_chunk["scaleLower"] = SCALE_INTERVAL["scaleLower"]
                    seeded_chunk["scaleUpper"] = SCALE_INTERVAL["scaleUpper"]
                    seeded_chunk["scaleLowerBound"] = interval_proofs[
                        "scaleLowerBound"
                    ]
                    seeded_chunk["scaleUpperBound"] = interval_proofs[
                        "scaleUpperBound"
                    ]
                    seeded_chunk["scaleIntervalSeedSource"] = (
                        "family_ell_div_pi_interval_lean_theorem"
                    )
                    seeded_chunk["scaleIntervalProofStatus"] = (
                        "shared_lean_theorem_pending_generated_payload_check"
                    )
                    family_interval_seeded_cells += 1
                    scale_interval_seeded_cells += 1
                if seeded_chunk.get("scaleNonneg") is None or overwrite:
                    seeded_chunk["scaleNonneg"] = proof
                    seeded_chunk["scaleNonnegSeedSource"] = (
                        "family_scale_nonneg_lean_theorem"
                    )
                    seeded_chunk["scaleNonnegProofStatus"] = (
                        "shared_lean_theorem_pending_generated_payload_check"
                    )
                    family_nonneg_seeded_cells += 1
                    scale_nonneg_seeded_cells += 1
                else:
                    family_already_present_cells += 1
                    already_present_cells += 1
                chunks.append(seeded_chunk)
                total_cells += 1

            seeded_row = dict(row)
            seeded_row["chunks"] = chunks
            rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = rows
        seeded_family["scaleNonnegSeededCells"] = family_nonneg_seeded_cells
        seeded_family["scaleIntervalSeededCells"] = family_interval_seeded_cells
        seeded_family["scaleNonnegAlreadyPresentCells"] = (
            family_already_present_cells
        )
        families.append(seeded_family)

    scale_seed = dict(seed)
    scale_seed["status"] = (
        "scale_interval_seed_chunk_bounds_geometry_row_sums_and_scale"
    )
    scale_seed["meaning"] = (
        "Candidate chunk bounds, deterministic chunk geometry, row-sum "
        "arithmetic proof terms, and shared family ell/pi interval proof terms "
        "are present.  Analytic Taylor/model proof data is still missing."
    )
    scale_seed["families"] = families
    scale_seed["scaleNonnegSeedSource"] = "family_scale_nonneg_lean_theorem"
    scale_seed["scaleIntervalSeedSource"] = "family_ell_div_pi_interval_lean_theorem"
    scale_seed["totals"] = {
        "families": len(families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "scaleNonnegSeededCells": scale_nonneg_seeded_cells,
        "scaleIntervalSeededCells": scale_interval_seeded_cells,
        "scaleNonnegAlreadyPresentCells": already_present_cells,
        "populatedProofCells": total_cells,
        "rowSumFailures": seed.get("totals", {}).get("rowSumFailures", None),
    }
    scale_seed["routeGuard"] = [
        "scaleLower/scaleUpper are shared family values, not cell enclosure data",
        "scaleLowerBound/scaleUpperBound are shared Lean theorem references",
        "scaleNonneg is retained only as compatibility diagnostic data",
        "this seed does not contain Taylor/model analytic proof data",
        "do not emit Lean until all proof-data fields are complete",
    ]
    return scale_seed


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    lines = [
        "# Step33A.1-A Taylor Payload Scale Seed",
        "",
        "This seed adds shared family scale nonnegativity proof terms on top of",
        "the current row-sum seed.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- scale interval seeded cells: `{totals['scaleIntervalSeededCells']}`",
        f"- scaleNonneg seeded cells: `{totals['scaleNonnegSeededCells']}`",
        "- scale interval: `9/100 <= ell / Real.pi <= 1/10`",
        "- primary lower proof: `RawOmegaAChunkIntegral.primaryK11Ell_div_pi_scaleLower`",
        "- primary upper proof: `RawOmegaAChunkIntegral.primaryK11Ell_div_pi_scaleUpper`",
        "- control lower proof: `RawOmegaAChunkIntegral.controlK9Ell_div_pi_scaleLower`",
        "- control upper proof: `RawOmegaAChunkIntegral.controlK9Ell_div_pi_scaleUpper`",
        "- primary proof: `RawOmegaAChunkIntegral.primaryK11Ell_div_pi_nonneg`",
        "- control proof: `RawOmegaAChunkIntegral.controlK9Ell_div_pi_nonneg`",
        "",
        "## Populated Fields",
        "",
        "- `scaleLower`",
        "- `scaleUpper`",
        "- `scaleLowerBound`",
        "- `scaleUpperBound`",
        "- `scaleNonneg`",
        "",
        "## Families",
        "",
        "| family | rows | chunks | scale interval seeded cells | scaleNonneg seeded cells | already present |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for family in seed["families"]:
        lines.append(
            "| {id} | {distanceRows} | {chunkCount} | "
            "{scaleIntervalSeededCells} | {scaleNonnegSeededCells} | "
            "{scaleNonnegAlreadyPresentCells} |".format(**family)
        )
    lines.extend(["", "## Route Guard", ""])
    for item in seed["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=DEFAULT_ROW_SUM_SEED)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="replace existing scaleNonneg fields instead of preserving them",
    )
    args = parser.parse_args()

    seed = load_json(args.seed)
    scale_seed = add_scale_nonneg(seed, overwrite=args.overwrite)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(scale_seed, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(scale_seed), encoding="utf-8")

    totals = scale_seed["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "scale_interval_seeded_cells={interval} "
        "scale_nonneg_seeded_cells={seeded} already_present={present}".format(
            status=scale_seed["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            interval=totals["scaleIntervalSeededCells"],
            seeded=totals["scaleNonnegSeededCells"],
            present=totals["scaleNonnegAlreadyPresentCells"],
        )
    )


if __name__ == "__main__":
    run()
