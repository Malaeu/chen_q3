#!/usr/bin/env python3
"""Fill the first finite raw-Omega chunk with the checked compact bound.

This pass is intentionally narrow.  The log-Omega seed fills all chunks with
left endpoint at least 10; this script fills only the finite `(0,10]` chunk
using:

* `step22OmegaArchWeight_neg_twoHundred_le_on_Ioc_zero_ten`
* `step22OmegaArchWeight_le_twoHundred_on_Ioc_zero_ten`

It does not populate Taylor/model, product-corner, polynomial, or integral
comparison fields.  The downstream Lean emitter must remain fail-closed until
those fields are supplied.
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


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OMEGA_LOG_SEED = REQUEST_DIR / "a_chunk_taylor_payload_omega_log_seed.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_omega_small_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_omega_small_seed.md"

OMEGA_FIELDS = [
    "omegaLower",
    "omegaUpper",
    "omegaLowerBound",
    "omegaUpperBound",
]


def decimal_value(value: Any) -> Decimal:
    try:
        return Decimal(str(value))
    except InvalidOperation as exc:
        raise ValueError(f"not a decimal endpoint: {value!r}") from exc


def small_window_omega_fields() -> dict[str, str]:
    return {
        "omegaLower": "(-(200 : Real))",
        "omegaUpper": "((200 : Real))",
        "omegaLowerBound": (
            "by\n"
            "  intro eta heta\n"
            "  exact RawOmegaAChunkIntegral."
            "step22OmegaArchWeight_neg_twoHundred_le_on_Ioc_zero_ten\n"
            "    (eta := eta) (by simpa using heta)"
        ),
        "omegaUpperBound": (
            "by\n"
            "  intro eta heta\n"
            "  exact RawOmegaAChunkIntegral."
            "step22OmegaArchWeight_le_twoHundred_on_Ioc_zero_ten\n"
            "    (eta := eta) (by simpa using heta)"
        ),
    }


def is_first_finite_chunk(family_id: str, chunk: dict[str, Any]) -> bool:
    if family_id not in {"primary_finite", "control_finite"}:
        return False
    left = decimal_value(chunk.get("left"))
    right = decimal_value(chunk.get("right"))
    return left == Decimal("0") and right == Decimal("10")


def add_small_window_omega_bounds(
    seed: dict[str, Any], *, overwrite: bool
) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")

    families = []
    total_rows = 0
    total_cells = 0
    omega_small_seeded_cells = 0
    omega_small_already_present_cells = 0
    omega_small_not_target_cells = 0
    field_seed_counts = {field: 0 for field in OMEGA_FIELDS}

    for family in seed.get("families", []):
        family_id = str(family.get("id"))
        rows = []
        family_seeded_cells = 0
        family_already_present_cells = 0
        family_not_target_cells = 0
        for row in family.get("distances", []):
            chunks = []
            for chunk in row.get("chunks", []):
                seeded_chunk = dict(chunk)
                already_complete = all(
                    seeded_chunk.get(field) is not None for field in OMEGA_FIELDS
                )
                if not is_first_finite_chunk(family_id, seeded_chunk):
                    family_not_target_cells += 1
                    omega_small_not_target_cells += 1
                    chunks.append(seeded_chunk)
                    total_cells += 1
                    continue

                if already_complete and not overwrite:
                    family_already_present_cells += 1
                    omega_small_already_present_cells += 1
                    chunks.append(seeded_chunk)
                    total_cells += 1
                    continue

                fields = small_window_omega_fields()
                for field, value in fields.items():
                    if seeded_chunk.get(field) is None or overwrite:
                        seeded_chunk[field] = value
                        field_seed_counts[field] += 1
                seeded_chunk["omegaSeedSource"] = (
                    "stieltjes_compact_small_window_two_hundred"
                )
                seeded_chunk["omegaProofStatus"] = (
                    "shared_lean_theorem_pending_generated_payload_check"
                )
                family_seeded_cells += 1
                omega_small_seeded_cells += 1
                chunks.append(seeded_chunk)
                total_cells += 1

            seeded_row = dict(row)
            seeded_row["chunks"] = chunks
            rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = rows
        seeded_family["omegaSmallSeededCells"] = family_seeded_cells
        seeded_family["omegaSmallAlreadyPresentCells"] = family_already_present_cells
        seeded_family["omegaSmallNotTargetCells"] = family_not_target_cells
        families.append(seeded_family)

    omega_seed = dict(seed)
    omega_seed["status"] = (
        "omega_small_seed_chunk_bounds_geometry_row_sums_scale_cos_shape_and_all_omega"
    )
    omega_seed["meaning"] = (
        "Candidate chunk bounds, deterministic chunk geometry, row-sum "
        "arithmetic proof terms, scale/cos/shape proof terms, log-Omega "
        "proof terms after 10, and compact small-window Omega proof terms "
        "for the first finite chunk are present.  Taylor/model data, product "
        "corners, and integral comparisons remain open."
    )
    omega_seed["families"] = families
    omega_seed["omegaSmallSeedSource"] = (
        "stieltjes_compact_small_window_two_hundred"
    )
    omega_seed["totals"] = {
        "families": len(families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "omegaSmallSeededCells": omega_small_seeded_cells,
        "omegaSmallAlreadyPresentCells": omega_small_already_present_cells,
        "omegaSmallNotTargetCells": omega_small_not_target_cells,
        "omegaSmallFieldSeedCounts": field_seed_counts,
        "populatedProofCells": total_cells,
        "priorTotals": seed.get("totals", {}),
    }
    omega_seed["routeGuard"] = [
        "small Omega seed applies only to primary/control finite first chunk (0,10]",
        "do not use this as Step33A.1-A closure",
        "this seed does not contain Taylor polynomial or remainder proof data",
        "do not emit Lean until all proof-data fields are complete",
    ]
    return omega_seed


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    field_counts = totals["omegaSmallFieldSeedCounts"]
    lines = [
        "# Step33A.1-A Taylor Payload Omega Small-Window Seed",
        "",
        "This seed fills the first finite `(0,10]` raw-Omega chunk using a",
        "checked compact Stieltjes bound.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- Omega small-window seeded cells: `{totals['omegaSmallSeededCells']}`",
        f"- already present target cells: `{totals['omegaSmallAlreadyPresentCells']}`",
        "- lower proof: `RawOmegaAChunkIntegral.step22OmegaArchWeight_neg_twoHundred_le_on_Ioc_zero_ten`",
        "- upper proof: `RawOmegaAChunkIntegral.step22OmegaArchWeight_le_twoHundred_on_Ioc_zero_ten`",
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
            "| family | rows | chunks | seeded | already present | not target |",
            "| --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for family in seed["families"]:
        lines.append(
            "| {id} | {distanceRows} | {chunkCount} | "
            "{omegaSmallSeededCells} | {omegaSmallAlreadyPresentCells} | "
            "{omegaSmallNotTargetCells} |".format(**family)
        )
    lines.extend(["", "## Route Guard", ""])
    for item in seed["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=DEFAULT_OMEGA_LOG_SEED)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="replace existing first-window Omega fields instead of only filling blanks",
    )
    args = parser.parse_args()

    seed = load_json(args.seed)
    omega_seed = add_small_window_omega_bounds(seed, overwrite=args.overwrite)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(omega_seed, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.write_text(render_md(omega_seed), encoding="utf-8")

    totals = omega_seed["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "omega_small_seeded_cells={seeded} already_present={already} "
        "not_target={not_target}".format(
            status=omega_seed["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            seeded=totals["omegaSmallSeededCells"],
            already=totals["omegaSmallAlreadyPresentCells"],
            not_target=totals["omegaSmallNotTargetCells"],
        )
    )


if __name__ == "__main__":
    run()
