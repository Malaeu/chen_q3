#!/usr/bin/env python3
"""Seed Step33 raw-Omega Taylor payload Omega bounds after the first chunk.

This pass fills `omegaLower`/`omegaUpper` and their Lean proof terms only for
chunks whose left endpoint is at least 10.  The proof terms use the checked
log-Omega receiver:

* `step22OmegaArchWeight_neg_ten_logOmega_right_le_on_Ioc`
* `step22OmegaArchWeight_le_ten_logOmega_right_on_Ioc`

The first finite chunk `(0,10]` is intentionally left open; it needs a compact
small-window Omega certificate, not the after-10 Stieltjes/log route.
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
from q3_psdpd_step33_a_chunk_taylor_payload_lean import lean_expr


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_SHAPE_SEED = REQUEST_DIR / "a_chunk_taylor_payload_shape_seed.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_omega_log_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_omega_log_seed.md"


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


def omega_fields(left: Any, right: Any) -> dict[str, str]:
    left_expr = lean_expr(left)
    right_expr = lean_expr(right)
    majorant = f"(10 * Real.log (3 * {right_expr}))"
    return {
        "omegaLower": f"-{majorant}",
        "omegaUpper": majorant,
        "omegaLowerBound": (
            "by\n"
            "  intro eta heta\n"
            "  exact RawOmegaAChunkIntegral."
            "step22OmegaArchWeight_neg_ten_logOmega_right_le_on_Ioc\n"
            f"    (L := {left_expr}) (U := {right_expr}) "
            "(eta := eta) (by norm_num) heta"
        ),
        "omegaUpperBound": (
            "by\n"
            "  intro eta heta\n"
            "  exact RawOmegaAChunkIntegral."
            "step22OmegaArchWeight_le_ten_logOmega_right_on_Ioc\n"
            f"    (L := {left_expr}) (U := {right_expr}) "
            "(eta := eta) (by norm_num) heta"
        ),
    }


def add_omega_log_bounds(seed: dict[str, Any], *, overwrite: bool) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")

    families = []
    total_rows = 0
    total_cells = 0
    omega_seeded_cells = 0
    omega_skipped_first_chunk_cells = 0
    omega_already_present_cells = 0
    field_seed_counts = {field: 0 for field in OMEGA_FIELDS}

    for family in seed.get("families", []):
        rows = []
        family_seeded_cells = 0
        family_skipped_cells = 0
        family_already_present_cells = 0
        for row in family.get("distances", []):
            chunks = []
            for chunk in row.get("chunks", []):
                seeded_chunk = dict(chunk)
                left = seeded_chunk.get("left")
                right = seeded_chunk.get("right")
                if left is None or right is None:
                    raise ValueError("chunk is missing left/right endpoints")

                already_complete = all(
                    seeded_chunk.get(field) is not None for field in OMEGA_FIELDS
                )
                if decimal_value(left) < Decimal("10"):
                    if already_complete:
                        family_already_present_cells += 1
                        omega_already_present_cells += 1
                    else:
                        family_skipped_cells += 1
                        omega_skipped_first_chunk_cells += 1
                    chunks.append(seeded_chunk)
                    total_cells += 1
                    continue

                fields = omega_fields(left, right)
                seeded_any = False
                for field, value in fields.items():
                    if seeded_chunk.get(field) is None or overwrite:
                        seeded_chunk[field] = value
                        field_seed_counts[field] += 1
                        seeded_any = True

                if seeded_any:
                    seeded_chunk["omegaSeedSource"] = (
                        "stieltjes_log_omega_after_ten_right_endpoint_majorant"
                    )
                    seeded_chunk["omegaProofStatus"] = (
                        "shared_lean_theorem_pending_generated_payload_check"
                    )
                    family_seeded_cells += 1
                    omega_seeded_cells += 1
                elif already_complete:
                    family_already_present_cells += 1
                    omega_already_present_cells += 1

                chunks.append(seeded_chunk)
                total_cells += 1

            seeded_row = dict(row)
            seeded_row["chunks"] = chunks
            rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = rows
        seeded_family["omegaLogSeededCells"] = family_seeded_cells
        seeded_family["omegaLogSkippedFirstChunkCells"] = family_skipped_cells
        seeded_family["omegaLogAlreadyPresentCells"] = family_already_present_cells
        families.append(seeded_family)

    omega_seed = dict(seed)
    omega_seed["status"] = (
        "omega_log_seed_chunk_bounds_geometry_row_sums_scale_cos_shape_and_omega_after_ten"
    )
    omega_seed["meaning"] = (
        "Candidate chunk bounds, deterministic chunk geometry, row-sum "
        "arithmetic proof terms, scale/cos/shape proof terms, and checked "
        "log-Omega proof terms for chunks with left endpoint at least 10 are "
        "present.  The first compact finite chunk, Taylor/model data, product "
        "corners, and integral comparisons remain open."
    )
    omega_seed["families"] = families
    omega_seed["omegaSeedSource"] = (
        "stieltjes_log_omega_after_ten_right_endpoint_majorant"
    )
    omega_seed["totals"] = {
        "families": len(families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "omegaLogSeededCells": omega_seeded_cells,
        "omegaLogSkippedFirstChunkCells": omega_skipped_first_chunk_cells,
        "omegaLogAlreadyPresentCells": omega_already_present_cells,
        "omegaLogFieldSeedCounts": field_seed_counts,
        "populatedProofCells": total_cells,
        "rowSumFailures": seed.get("totals", {}).get("rowSumFailures", None),
    }
    omega_seed["routeGuard"] = [
        "Omega log seed applies only when chunk left endpoint is at least 10",
        "first finite chunk (0,10] remains open for compact small-window Omega",
        "this seed does not contain Taylor polynomial or remainder proof data",
        "do not emit Lean until all proof-data fields are complete",
    ]
    return omega_seed


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    field_counts = totals["omegaLogFieldSeedCounts"]
    lines = [
        "# Step33A.1-A Taylor Payload Omega Log Seed",
        "",
        "This seed adds checked log-Omega component bounds for every chunk with",
        "left endpoint at least `10`.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- Omega seeded cells: `{totals['omegaLogSeededCells']}`",
        f"- skipped first-chunk cells: `{totals['omegaLogSkippedFirstChunkCells']}`",
        "- lower proof: `RawOmegaAChunkIntegral.step22OmegaArchWeight_neg_ten_logOmega_right_le_on_Ioc`",
        "- upper proof: `RawOmegaAChunkIntegral.step22OmegaArchWeight_le_ten_logOmega_right_on_Ioc`",
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
            "| family | rows | chunks | Omega seeded cells | skipped | already present |",
            "| --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for family in seed["families"]:
        lines.append(
            "| {id} | {distanceRows} | {chunkCount} | "
            "{omegaLogSeededCells} | {omegaLogSkippedFirstChunkCells} | "
            "{omegaLogAlreadyPresentCells} |".format(**family)
        )
    lines.extend(["", "## Route Guard", ""])
    for item in seed["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=DEFAULT_SHAPE_SEED)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="replace existing Omega fields instead of only filling blanks",
    )
    args = parser.parse_args()

    seed = load_json(args.seed)
    omega_seed = add_omega_log_bounds(seed, overwrite=args.overwrite)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(omega_seed, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.write_text(render_md(omega_seed), encoding="utf-8")

    totals = omega_seed["totals"]
    print(
        f"status={omega_seed['status']} "
        f"families={totals['families']} rows={totals['distanceRows']} "
        f"cells={totals['chunkCells']} "
        f"omega_seeded_cells={totals['omegaLogSeededCells']} "
        f"skipped_first_chunk_cells={totals['omegaLogSkippedFirstChunkCells']}"
    )


if __name__ == "__main__":
    run()
