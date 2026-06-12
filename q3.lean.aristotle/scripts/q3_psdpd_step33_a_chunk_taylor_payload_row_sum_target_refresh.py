#!/usr/bin/env python3
"""Build a local target-refresh audit from serialized row-sum proof data.

The Arb/acb probe row aggregates may fit the target interval while the emitted
rational `chunkLower` / `chunkUpper` strings sum to a value just outside it.
This pass compares the serialized proof-data sums against the current worklist
targets and emits a probe-compatible refresh JSON.  Existing target-refresh
rows are preserved, and any additional serialized-row slack is charged against
the current remaining `tail_radius_slack`.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    DEFAULT_WORKLIST,
    PROOF_DATA_SCHEMA,
    load_json,
    validate_worklist,
)
from q3_psdpd_step33_a_chunk_taylor_payload_row_sum_seed import (
    DEFAULT_OUT_JSON as DEFAULT_ROW_SUM_SEED,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_row_sum_target_refresh.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_row_sum_target_refresh.md"
PRIMARY_FINITE_COMPONENTS = REQUEST_DIR / "a_finite_tail_components_k11.json"
CONTROL_FINITE_COMPONENTS = REQUEST_DIR / "a_finite_tail_components_k9.json"
PRIMARY_TAIL_PROBE = REQUEST_DIR / "a_signed_tail_probe_k11.json"
CONTROL_TAIL_PROBE = REQUEST_DIR / "a_signed_tail_probe_k9.json"
ORIGINAL_CHUNK_PROBE = REQUEST_DIR / "rawomega_a_chunk_integral_probe_all_256.json"


def parse_decimal(value: Any, *, label: str) -> Decimal:
    try:
        decimal = Decimal(str(value))
    except InvalidOperation as exc:
        raise ValueError(f"{label}: invalid decimal {value!r}") from exc
    if not decimal.is_finite():
        raise ValueError(f"{label}: non-finite decimal {value!r}")
    return decimal


def decimal_str(value: Decimal) -> str:
    if value == 0:
        return "0.000000000000000000E+0"
    return format(value, ".18E")


def refresh_guard(*values: Decimal) -> Decimal:
    scale = max((abs(value) for value in values), default=Decimal("0"))
    return max(scale * Decimal("1e-18"), Decimal("1e-45"))


def serialize_lower_at_most(value: Decimal, ceiling: Decimal) -> tuple[str, Decimal]:
    """Serialize `value` so the parsed decimal is still <= `ceiling`."""
    guard = refresh_guard(value, ceiling)
    current = value
    for _ in range(16):
        text = decimal_str(current)
        parsed = parse_decimal(text, label="serialized lower")
        if parsed <= ceiling:
            return text, parsed
        current -= guard
    raise ValueError("could not serialize lower target below ceiling")


def serialize_upper_at_least(value: Decimal, floor: Decimal) -> tuple[str, Decimal]:
    """Serialize `value` so the parsed decimal is still >= `floor`."""
    guard = refresh_guard(value, floor)
    current = value
    for _ in range(16):
        text = decimal_str(current)
        parsed = parse_decimal(text, label="serialized upper")
        if floor <= parsed:
            return text, parsed
        current += guard
    raise ValueError("could not serialize upper target above floor")


def row_map_by_family(worklist: dict[str, Any]) -> dict[tuple[str, int], dict[str, Any]]:
    rows: dict[tuple[str, int], dict[str, Any]] = {}
    for family in worklist.get("families", []):
        family_id = str(family["id"])
        for row in family.get("distances", []):
            rows[(family_id, int(row["index"]))] = row
    return rows


def load_base_targets() -> dict[tuple[str, int], tuple[Decimal, Decimal]]:
    targets: dict[tuple[str, int], tuple[Decimal, Decimal]] = {}
    for family_id, path in [
        ("primary_finite", PRIMARY_FINITE_COMPONENTS),
        ("control_finite", CONTROL_FINITE_COMPONENTS),
    ]:
        payload = load_json(path)
        for idx, row in enumerate(payload.get("distances", [])):
            mid = parse_decimal(row["finite_mid"], label=f"{family_id}[{idx}].finite_mid")
            rad = parse_decimal(
                row["finite_radius"],
                label=f"{family_id}[{idx}].finite_radius",
            )
            targets[(family_id, idx)] = (mid - rad, mid + rad)
    for family_id, path in [
        ("primary_tail", PRIMARY_TAIL_PROBE),
        ("control_tail", CONTROL_TAIL_PROBE),
    ]:
        payload = load_json(path)
        for row in payload.get("distances", []):
            idx = int(row["index"])
            targets[(family_id, idx)] = (
                parse_decimal(row["window_lower"], label=f"{family_id}[{idx}].window_lower"),
                parse_decimal(row["window_upper"], label=f"{family_id}[{idx}].window_upper"),
            )
    return targets


def load_original_refresh_needed() -> dict[tuple[str, int], Decimal]:
    payload = load_json(ORIGINAL_CHUNK_PROBE)
    needed: dict[tuple[str, int], Decimal] = {}
    for family in payload.get("families", []):
        family_id = str(family["family"])
        for row in family.get("rows", []):
            if not row.get("fits_after_local_target_refresh"):
                continue
            idx = int(row["distance_index"])
            needed[(family_id, idx)] = parse_decimal(
                row["needed_target_refresh_slack"],
                label=f"{family_id}[{idx}].original_needed",
            )
    return needed


def seed_row_sums(row: dict[str, Any]) -> tuple[Decimal, Decimal]:
    chunks = row.get("chunks", [])
    lower = sum(
        parse_decimal(chunk["chunkLower"], label="chunkLower")
        for chunk in chunks
    )
    upper = sum(
        parse_decimal(chunk["chunkUpper"], label="chunkUpper")
        for chunk in chunks
    )
    return lower, upper


def build_refresh(seed: dict[str, Any], worklist: dict[str, Any]) -> dict[str, Any]:
    if seed.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {seed.get('schema')!r}")
    validate_worklist(worklist, DEFAULT_WORKLIST)
    worklist_rows = row_map_by_family(worklist)
    base_targets = load_base_targets()
    original_needed = load_original_refresh_needed()

    families = []
    total_rows = 0
    refresh_rows = 0
    additional_rows = 0
    preserved_rows = 0
    blocked_rows: list[dict[str, Any]] = []
    serialized_failures: list[dict[str, Any]] = []

    for family in seed.get("families", []):
        family_id = str(family["id"])
        out_rows = []
        for row in family.get("distances", []):
            idx = int(row["index"])
            worklist_row = worklist_rows[(family_id, idx)]
            target_lower = parse_decimal(
                worklist_row["target_lower_value"],
                label=f"{family_id}[{idx}].target_lower_value",
            )
            target_upper = parse_decimal(
                worklist_row["target_upper_value"],
                label=f"{family_id}[{idx}].target_upper_value",
            )
            sum_lower, sum_upper = seed_row_sums(row)
            lower_excess = max(Decimal("0"), target_lower - sum_lower)
            upper_excess = max(Decimal("0"), sum_upper - target_upper)
            extra_guard = refresh_guard(target_lower, target_upper, sum_lower, sum_upper)
            suggested_lower = target_lower
            suggested_upper = target_upper
            if lower_excess > 0:
                suggested_lower = sum_lower - extra_guard
            if upper_excess > 0:
                suggested_upper = sum_upper + extra_guard

            suggested_lower_text, serialized_lower = (
                serialize_lower_at_most(suggested_lower, sum_lower)
                if lower_excess > 0
                else (decimal_str(suggested_lower), suggested_lower)
            )
            suggested_upper_text, serialized_upper = (
                serialize_upper_at_least(suggested_upper, sum_upper)
                if upper_excess > 0
                else (decimal_str(suggested_upper), suggested_upper)
            )
            extra_needed = max(
                Decimal("0"),
                target_lower - serialized_lower,
                serialized_upper - target_upper,
            )

            available_slack = parse_decimal(
                worklist_row.get("tail_radius_slack") or "0",
                label=f"{family_id}[{idx}].tail_radius_slack",
            )
            old_needed = parse_decimal(
                worklist_row.get("target_refresh_needed_slack") or "0",
                label=f"{family_id}[{idx}].old_needed",
            )
            old_needed = max(old_needed, original_needed.get((family_id, idx), Decimal("0")))
            base_lower, base_upper = base_targets[(family_id, idx)]
            total_needed = max(
                Decimal("0"),
                old_needed,
                base_lower - serialized_lower,
                serialized_upper - base_upper,
                extra_needed,
            )
            slack_after = available_slack - total_needed
            already_refreshed = bool(worklist_row.get("target_refresh_applied"))
            needs_extra = extra_needed > 0
            include_row = already_refreshed or needs_extra
            if not include_row:
                continue

            if needs_extra:
                serialized_failures.append(
                    {
                        "family_id": family_id,
                        "distance_index": idx,
                        "lower_excess": decimal_str(lower_excess),
                        "upper_excess": decimal_str(upper_excess),
                        "extra_needed_slack": decimal_str(extra_needed),
                        "remaining_slack_before_extra": decimal_str(remaining_slack),
                    }
                )
            if slack_after < 0:
                blocked_rows.append(
                    {
                        "family_id": family_id,
                        "distance_index": idx,
                        "total_needed_slack": decimal_str(total_needed),
                        "available_target_refresh_slack": decimal_str(available_slack),
                        "shortfall": decimal_str(-slack_after),
                    }
                )

            out_rows.append(
                {
                    "family_id": family_id,
                    "distance_index": idx,
                    "distance": row.get("distance"),
                    "target_lower": decimal_str(target_lower),
                    "target_upper": decimal_str(target_upper),
                    "chunk_sum_lower": decimal_str(sum_lower),
                    "chunk_sum_upper": decimal_str(sum_upper),
                    "fits_target": False,
                    "fits_after_local_target_refresh": slack_after >= 0,
                    "available_target_refresh_slack": decimal_str(available_slack),
                    "target_refresh_guard": decimal_str(
                        max(
                            extra_guard if needs_extra else Decimal("0"),
                            parse_decimal(
                                worklist_row.get("target_refresh_guard") or "0",
                                label=f"{family_id}[{idx}].old_guard",
                            ),
                        )
                    ),
                    "needed_target_refresh_slack": decimal_str(total_needed),
                    "slack_after_suggested_refresh": decimal_str(slack_after),
                    "lower_excess": decimal_str(lower_excess),
                    "upper_excess": decimal_str(upper_excess),
                    "excess": decimal_str(max(lower_excess, upper_excess)),
                    "suggested_target_lower": suggested_lower_text,
                    "suggested_target_upper": suggested_upper_text,
                    "serialized_extra_refresh": needs_extra,
                    "preserved_existing_refresh": already_refreshed,
                }
            )
            total_rows += 1
            refresh_rows += 1
            if needs_extra:
                additional_rows += 1
            else:
                preserved_rows += 1

        if out_rows:
            families.append({"family": family_id, "rows": out_rows})

    worst_extra = max(
        (
            parse_decimal(row["extra_needed_slack"], label="extra_needed_slack")
            for row in serialized_failures
        ),
        default=Decimal("0"),
    )
    return {
        "schema": "q3_psdpd_step33_a_chunk_integral_probe.v1",
        "meaning": (
            "Probe-compatible local target refresh derived from serialized "
            "proof-data row sums. This is not a Lean proof object and does not "
            "mutate A CSV, ARadius, radius-floor, or LDL data."
        ),
        "source_worklist": str(DEFAULT_WORKLIST),
        "source_row_sum_seed": str(DEFAULT_ROW_SUM_SEED),
        "parameters": {
            "source": "serialized_row_sum_seed",
            "families": "all",
            "indices": "all",
            "chunk_indices": "all",
        },
        "totals": {
            "families_checked": len(families),
            "rows_checked": total_rows,
            "rows_failed": len(blocked_rows),
            "rows_slack_absorbable": refresh_rows - len(blocked_rows),
            "refresh_rows": refresh_rows,
            "preserved_existing_refresh_rows": preserved_rows,
            "additional_serialized_refresh_rows": additional_rows,
            "serialized_failure_sides": sum(
                1
                for row in serialized_failures
                for side in ("lower_excess", "upper_excess")
                if parse_decimal(row[side], label=side) > 0
            ),
            "worst_extra_needed_slack": decimal_str(worst_extra),
            "full_chunk_rows": True,
        },
        "family_summaries": [
            {
                "id": family["family"],
                "rows_checked": len(family["rows"]),
                "rows_failed": sum(
                    1
                    for row in family["rows"]
                    if not row["fits_after_local_target_refresh"]
                ),
                "rows_slack_absorbable": sum(
                    1
                    for row in family["rows"]
                    if row["fits_after_local_target_refresh"]
                ),
            }
            for family in families
        ],
        "worst_failures": blocked_rows,
        "serialized_failures": serialized_failures,
        "families": families,
    }


def render_md(result: dict[str, Any]) -> str:
    totals = result["totals"]
    lines = [
        "# Step33A.1-A Serialized Row-Sum Target Refresh",
        "",
        "This audit compares serialized `chunkLower` / `chunkUpper` sums against",
        "the current worklist targets and emits a probe-compatible local refresh.",
        "",
        "## Verdict",
        "",
        f"- schema: `{result['schema']}`",
        f"- refresh rows: `{totals['refresh_rows']}`",
        f"- preserved existing refresh rows: `{totals['preserved_existing_refresh_rows']}`",
        f"- additional serialized refresh rows: `{totals['additional_serialized_refresh_rows']}`",
        f"- serialized failure sides: `{totals['serialized_failure_sides']}`",
        f"- blocked rows: `{totals['rows_failed']}`",
        f"- worst extra needed slack: `{totals['worst_extra_needed_slack']}`",
        "",
        "## Families",
        "",
        "| family | refresh rows | blocked | slack-absorbable |",
        "| --- | ---: | ---: | ---: |",
    ]
    for summary in result["family_summaries"]:
        lines.append(
            "| {id} | {rows_checked} | {rows_failed} | {rows_slack_absorbable} |".format(
                **summary
            )
        )
    if result.get("serialized_failures"):
        lines.extend(
            [
                "",
                "## Serialized Sum Extra Rows",
                "",
                "| family | idx | lower excess | upper excess | extra needed | remaining slack |",
                "| --- | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for row in result["serialized_failures"]:
            lines.append(
                "| {family_id} | {distance_index} | {lower_excess} | {upper_excess} | "
                "{extra_needed_slack} | {remaining_slack_before_extra} |".format(
                    **row
                )
            )
    if result.get("worst_failures"):
        lines.extend(["", "## Blocked Rows", ""])
        for row in result["worst_failures"]:
            lines.append(f"- `{row}`")
    lines.extend(
        [
            "",
            "## Route Guard",
            "",
            "- local target refresh only; no A CSV / ARadius / radius-floor / LDL mutation",
            "- generated arithmetic/worklist must be regenerated from this file before row-sum proof terms are trusted",
            "- generated PayloadFin must still wait for Taylor/model analytic proof data",
            "",
        ]
    )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=DEFAULT_ROW_SUM_SEED)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    seed = load_json(args.seed)
    worklist = load_json(args.worklist)
    result = build_refresh(seed, worklist)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(result), encoding="utf-8")

    totals = result["totals"]
    print(
        "status=serialized_row_sum_target_refresh refresh_rows={refresh} "
        "preserved={preserved} additional={additional} sides={sides} "
        "blocked={blocked}".format(
            refresh=totals["refresh_rows"],
            preserved=totals["preserved_existing_refresh_rows"],
            additional=totals["additional_serialized_refresh_rows"],
            sides=totals["serialized_failure_sides"],
            blocked=totals["rows_failed"],
        )
    )


if __name__ == "__main__":
    run()
