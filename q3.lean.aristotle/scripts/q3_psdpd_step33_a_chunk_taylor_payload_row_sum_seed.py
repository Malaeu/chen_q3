#!/usr/bin/env python3
"""Add row-sum arithmetic proof-term candidates to the Step33 A proof-data seed.

This pass uses the already seeded `chunkLower` / `chunkUpper` values and the
current row target bounds.  It fills `lowerSum` / `upperSum` only when the
decimal check

  targetLower <= sum chunkLower
  sum chunkUpper <= targetUpper

passes.  The stored proof terms are Lean arithmetic scripts intended for the
future generated payload file; they are still not accepted until that file is
emitted and checked by Lean.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_geometry_seed import (
    DEFAULT_OUT_JSON as DEFAULT_GEOMETRY_SEED,
)
from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    PROOF_DATA_SCHEMA,
    load_json,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_row_sum_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_row_sum_seed.md"


FAMILY_CONFIGS = {
    "primary_finite": {
        "prefix": "primaryFinite",
        "target_lower": "primaryK11RawOmegaAFiniteLower",
        "target_lower_rat": "primaryK11RawOmegaAFiniteLowerRat",
        "target_upper": "primaryK11RawOmegaAFiniteUpper",
        "target_upper_rat": "primaryK11RawOmegaAFiniteUpperRat",
    },
    "primary_tail": {
        "prefix": "primaryTail",
        "target_lower": "primaryK11RawOmegaATailWindowLower",
        "target_lower_rat": "primaryK11RawOmegaATailWindowLowerRat",
        "target_upper": "primaryK11RawOmegaATailWindowUpper",
        "target_upper_rat": "primaryK11RawOmegaATailWindowUpperRat",
    },
    "control_finite": {
        "prefix": "controlFinite",
        "target_lower": "controlK9RawOmegaAFiniteLower",
        "target_lower_rat": "controlK9RawOmegaAFiniteLowerRat",
        "target_upper": "controlK9RawOmegaAFiniteUpper",
        "target_upper_rat": "controlK9RawOmegaAFiniteUpperRat",
    },
    "control_tail": {
        "prefix": "controlTail",
        "target_lower": "controlK9RawOmegaATailWindowLower",
        "target_lower_rat": "controlK9RawOmegaATailWindowLowerRat",
        "target_upper": "controlK9RawOmegaATailWindowUpper",
        "target_upper_rat": "controlK9RawOmegaATailWindowUpperRat",
    },
}


def parse_decimal(value: Any, *, label: str) -> Decimal:
    try:
        decimal = Decimal(str(value))
    except InvalidOperation as exc:
        raise ValueError(f"{label}: invalid decimal {value!r}") from exc
    if not decimal.is_finite():
        raise ValueError(f"{label}: non-finite decimal {value!r}")
    return decimal


def row_sum_proof(config: dict[str, str], *, side: str) -> str:
    if side == "lower":
        chunk_fn = f"{config['prefix']}ChunkLower"
        target = config["target_lower"]
        target_rat = config["target_lower_rat"]
    elif side == "upper":
        chunk_fn = f"{config['prefix']}ChunkUpper"
        target = config["target_upper"]
        target_rat = config["target_upper_rat"]
    else:
        raise ValueError(f"unexpected side {side!r}")
    return (
        "by\n"
        "  norm_num [\n"
        "    RawOmegaAChunkTaylorPayload.chunkValueFromFin26,\n"
        f"    {chunk_fn},\n"
        "    primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated,\n"
        "    controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated,\n"
        f"    {target},\n"
        f"    {target_rat}]"
    )


def add_row_sums(seed: dict[str, Any]) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")

    families = []
    total_rows = 0
    total_cells = 0
    lower_sum_rows = 0
    upper_sum_rows = 0
    failures: list[dict[str, Any]] = []

    for family in seed.get("families", []):
        family_id = str(family["id"])
        config = FAMILY_CONFIGS[family_id]
        rows = []
        family_lower_rows = 0
        family_upper_rows = 0
        for row in family.get("distances", []):
            chunks = row.get("chunks", [])
            total_cells += len(chunks)
            target_lower = parse_decimal(row.get("targetLowerValue"), label="targetLowerValue")
            target_upper = parse_decimal(row.get("targetUpperValue"), label="targetUpperValue")
            sum_lower = sum(
                parse_decimal(chunk["chunkLower"], label="chunkLower")
                for chunk in chunks
            )
            sum_upper = sum(
                parse_decimal(chunk["chunkUpper"], label="chunkUpper")
                for chunk in chunks
            )
            seeded_row = dict(row)
            if target_lower <= sum_lower:
                seeded_row["lowerSum"] = row_sum_proof(config, side="lower")
                seeded_row["lowerSumProofStatus"] = (
                    "arithmetic_norm_num_term_pending_generated_lean_check"
                )
                family_lower_rows += 1
                lower_sum_rows += 1
            else:
                failures.append(
                    {
                        "family": family_id,
                        "row": int(row["index"]),
                        "side": "lower",
                        "targetLower": str(target_lower),
                        "sumLower": str(sum_lower),
                        "deficit": str(target_lower - sum_lower),
                    }
                )
            if sum_upper <= target_upper:
                seeded_row["upperSum"] = row_sum_proof(config, side="upper")
                seeded_row["upperSumProofStatus"] = (
                    "arithmetic_norm_num_term_pending_generated_lean_check"
                )
                family_upper_rows += 1
                upper_sum_rows += 1
            else:
                failures.append(
                    {
                        "family": family_id,
                        "row": int(row["index"]),
                        "side": "upper",
                        "targetUpper": str(target_upper),
                        "sumUpper": str(sum_upper),
                        "excess": str(sum_upper - target_upper),
                    }
                )
            rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = rows
        seeded_family["lowerSumSeededRows"] = family_lower_rows
        seeded_family["upperSumSeededRows"] = family_upper_rows
        families.append(seeded_family)

    row_sum_seed = dict(seed)
    row_sum_seed["status"] = "row_sum_seed_chunk_bounds_geometry_and_row_sums"
    row_sum_seed["meaning"] = (
        "Candidate chunk bounds, deterministic chunk geometry, and row-sum "
        "arithmetic proof terms are present.  Analytic Taylor/model proof data "
        "is still missing."
    )
    row_sum_seed["families"] = families
    row_sum_seed["rowSumSeedSource"] = "decimal_chunk_sum_vs_target_bounds"
    row_sum_seed["totals"] = {
        "families": len(families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "lowerSumSeededRows": lower_sum_rows,
        "upperSumSeededRows": upper_sum_rows,
        "rowSumFailures": len(failures),
        "populatedProofCells": seed.get("totals", {}).get("populatedProofCells", 0),
    }
    row_sum_seed["routeGuard"] = [
        "row-sum proof terms are arithmetic candidates pending generated Lean check",
        "this seed does not contain Taylor/model analytic proof data",
        "do not emit Lean until all proof-data fields are complete",
    ]
    failure_summary: dict[str, int] = {}
    for failure in failures:
        key = f"{failure['family']}:{failure['side']}"
        failure_summary[key] = failure_summary.get(key, 0) + 1
    row_sum_seed["rowSumFailureSummary"] = failure_summary
    row_sum_seed["rowSumFailures"] = failures
    return row_sum_seed


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    lines = [
        "# Step33A.1-A Taylor Payload Row-Sum Seed",
        "",
        "This seed adds row-level arithmetic proof-term candidates for",
        "`lowerSum` / `upperSum` on top of the geometry seed.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- lowerSum seeded rows: `{totals['lowerSumSeededRows']}`",
        f"- upperSum seeded rows: `{totals['upperSumSeededRows']}`",
        f"- row-sum failures: `{totals['rowSumFailures']}`",
        "",
        "## Families",
        "",
        "| family | rows | lowerSum rows | upperSum rows |",
        "| --- | ---: | ---: | ---: |",
    ]
    for family in seed["families"]:
        lines.append(
            "| {id} | {distanceRows} | {lowerSumSeededRows} | {upperSumSeededRows} |".format(
                **family
            )
        )
    lines.extend(["", "## Route Guard", ""])
    for item in seed["routeGuard"]:
        lines.append(f"- {item}")
    if seed.get("rowSumFailureSummary"):
        lines.extend(["", "## Failure Summary", ""])
        for key, count in sorted(seed["rowSumFailureSummary"].items()):
            lines.append(f"- `{key}`: `{count}`")
    if seed.get("rowSumFailures"):
        lines.extend(["", "## Failures", ""])
        for failure in seed["rowSumFailures"]:
            lines.append(f"- `{failure}`")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=DEFAULT_GEOMETRY_SEED)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    seed = load_json(args.seed)
    row_sum_seed = add_row_sums(seed)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(row_sum_seed, indent=2, sort_keys=True) + "\n")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(row_sum_seed), encoding="utf-8")

    totals = row_sum_seed["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "lower_sum_rows={lower} upper_sum_rows={upper} failures={failures}".format(
            status=row_sum_seed["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            lower=totals["lowerSumSeededRows"],
            upper=totals["upperSumSeededRows"],
            failures=totals["rowSumFailures"],
        )
    )


if __name__ == "__main__":
    run()
