#!/usr/bin/env python3
"""Inventory the missing proof-data layer for Step33 raw-Omega A PayloadFin.

This script is intentionally not a Lean generator.  It checks the current
distance/chunk worklist and any available diagnostic Arb probe, then reports
whether enough proof-data exists to instantiate
`RawOmegaAChunkTaylorPayload.PayloadFin`.

Arb/acb integral probes can confirm that the numeric target intervals are
plausible, but they do not contain the Taylor/model certificates consumed by
Lean.  This inventory keeps that distinction explicit before a later generator
emits a proof-bearing Lean import.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = REQUEST_DIR / "a_distance_payload_worklist.json"
DEFAULT_PROBE = REQUEST_DIR / "rawomega_a_chunk_integral_probe_all_256.json"

PROOF_DATA_SCHEMA = "q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1"

PRODUCT_CORNER_SUFFIXES = [
    "LLL",
    "LLU",
    "LUL",
    "LUU",
    "ULL",
    "ULU",
    "UUL",
    "UUU",
]

PRODUCT_SCALE_CORNER_SUFFIXES = [
    "LLLL",
    "LLLU",
    "LLUL",
    "LLUU",
    "LULL",
    "LULU",
    "LUUL",
    "LUUU",
    "ULLL",
    "ULLU",
    "ULUL",
    "ULUU",
    "UULL",
    "UULU",
    "UUUL",
    "UUUU",
]

DIRECT_PRODUCT_FIELDS = [
    "componentProductLower",
    "componentProductUpper",
]

PRODUCT_CORNER_FIELDS = [
    *(f"componentProductCornerLower{suffix}" for suffix in PRODUCT_CORNER_SUFFIXES),
    *(f"componentProductCornerUpper{suffix}" for suffix in PRODUCT_CORNER_SUFFIXES),
]

SCALE_INTERVAL_PRODUCT_FIELDS = [
    "scaleLower",
    "scaleUpper",
    "scaleLowerBound",
    "scaleUpperBound",
    *(
        f"componentProductScaleCornerLower{suffix}"
        for suffix in PRODUCT_SCALE_CORNER_SUFFIXES
    ),
    *(
        f"componentProductScaleCornerUpper{suffix}"
        for suffix in PRODUCT_SCALE_CORNER_SUFFIXES
    ),
]

POLYNOMIAL_DIRECT_FIELDS = [
    "polyLower",
    "polyUpper",
    "polynomialLowerBound",
    "polynomialUpperBound",
]

POLYNOMIAL_TERM_FIELDS = [
    "termLower",
    "termUpper",
    "polyLower",
    "polyUpper",
    "polynomialTermBounds",
    "polyLowerSum",
    "polyUpperSum",
]

CELL_REQUIRED_FIELDS = [
    "chunkLower",
    "chunkUpper",
    "center",
    "radius",
    "degree",
    "coeff",
    "remainder",
    "omegaLower",
    "omegaUpper",
    "omegaLowerBound",
    "omegaUpperBound",
    "shapeSqLower",
    "shapeSqUpper",
    "shapeSqLowerBound",
    "shapeSqUpperBound",
    "cosLower",
    "cosUpper",
    "cosLowerBound",
    "cosUpperBound",
    "rawLower",
    "rawUpper",
    "radiusNonneg",
    "remainderNonneg",
    "radiusLeft",
    "radiusRight",
    "diffLower",
    "diffUpper",
    "integralLower",
    "integralUpper",
]

ROW_REQUIRED_FIELDS = [
    "lowerSum",
    "upperSum",
]

TAIL_ROW_REQUIRED_FIELDS: list[str] = []

CELL_PROOF_FIELDS = [
    "omegaLowerBound",
    "omegaUpperBound",
    "shapeSqLowerBound",
    "shapeSqUpperBound",
    "cosLowerBound",
    "cosUpperBound",
    "radiusNonneg",
    "remainderNonneg",
    "radiusLeft",
    "radiusRight",
    *DIRECT_PRODUCT_FIELDS,
    *PRODUCT_CORNER_FIELDS,
    *SCALE_INTERVAL_PRODUCT_FIELDS,
    "polynomialLowerBound",
    "polynomialUpperBound",
    *POLYNOMIAL_TERM_FIELDS,
    "diffLower",
    "diffUpper",
    "integralLower",
    "integralUpper",
]

FIELD_GROUPS = {
    "chunk_interval_probe": [
        "cell.chunkLower",
        "cell.chunkUpper",
    ],
    "chunk_geometry": [
        "cell.center",
        "cell.radius",
        "cell.radiusNonneg",
        "cell.radiusLeft",
        "cell.radiusRight",
    ],
    "row_sum_arithmetic": [
        "row.lowerSum",
        "row.upperSum",
    ],
    "taylor_model_data": [
        "cell.degree",
        "cell.coeff",
        "cell.remainder",
        "cell.remainderNonneg",
    ],
    "omega_shape_enclosures": [
        "cell.omegaLower",
        "cell.omegaUpper",
        "cell.omegaLowerBound",
        "cell.omegaUpperBound",
        "cell.shapeSqLower",
        "cell.shapeSqUpper",
        "cell.shapeSqLowerBound",
        "cell.shapeSqUpperBound",
    ],
    "cosine_envelope": [
        "cell.cosLower",
        "cell.cosUpper",
        "cell.cosLowerBound",
        "cell.cosUpperBound",
    ],
    "raw_product_bounds": [
        "cell.rawLower",
        "cell.rawUpper",
        *(f"cell.{field}" for field in DIRECT_PRODUCT_FIELDS),
        *(f"cell.{field}" for field in PRODUCT_CORNER_FIELDS),
        *(f"cell.{field}" for field in SCALE_INTERVAL_PRODUCT_FIELDS),
    ],
    "polynomial_value_bounds": [
        "cell.termLower",
        "cell.termUpper",
        "cell.polyLower",
        "cell.polyUpper",
        "cell.polynomialTermBounds",
        "cell.polyLowerSum",
        "cell.polyUpperSum",
        "cell.polynomialLowerBound",
        "cell.polynomialUpperBound",
    ],
    "diff_integral_comparisons": [
        "cell.diffLower",
        "cell.diffUpper",
        "cell.integralLower",
        "cell.integralUpper",
    ],
}

FIELD_TO_GROUP = {
    field: group
    for group, fields in FIELD_GROUPS.items()
    for field in fields
}

PROBE_NUMERIC_CELL_FIELDS = [
    "lower",
    "upper",
    "width",
]


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_worklist(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != "q3_psdpd_step33_a_distance_payload_worklist.v1":
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def validate_probe(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != "q3_psdpd_step33_a_chunk_integral_probe.v1":
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def family_cell_count(family: dict[str, Any]) -> int:
    return int(family["distance_count"]) * int(family["chunk_count"])


def family_id_from_probe(raw_id: str) -> str:
    return raw_id.replace("_finite", "_finite").replace("_tail", "_tail")


def probe_summary(probe: dict[str, Any] | None) -> dict[str, Any]:
    if probe is None:
        return {
            "available": False,
            "families": 0,
            "rows": 0,
            "chunk_cells": 0,
            "has_numeric_chunk_intervals": False,
            "has_taylor_proof_data": False,
        }
    families = probe.get("families", [])
    row_count = 0
    cell_count = 0
    numeric_cells = 0
    taylor_cells = 0
    for family in families:
        rows = family.get("rows", [])
        row_count += len(rows)
        for row in rows:
            chunks = row.get("chunks", [])
            cell_count += len(chunks)
            for chunk in chunks:
                if all(field in chunk for field in PROBE_NUMERIC_CELL_FIELDS):
                    numeric_cells += 1
                if any(chunk.get(field) is not None for field in CELL_REQUIRED_FIELDS):
                    taylor_cells += 1
    return {
        "available": True,
        "families": len(families),
        "rows": row_count,
        "chunk_cells": cell_count,
        "numeric_chunk_cells": numeric_cells,
        "has_numeric_chunk_intervals": numeric_cells == cell_count and cell_count > 0,
        "has_taylor_proof_data": taylor_cells > 0,
    }


def proof_family_map(proof_data: dict[str, Any] | None) -> dict[str, dict[str, Any]]:
    if proof_data is None:
        return {}
    return {str(family["id"]): family for family in proof_data.get("families", [])}


def proof_row_map(family: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {int(row["index"]): row for row in family.get("distances", [])}


def proof_chunk_map(row: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {int(chunk["index"]): chunk for chunk in row.get("chunks", [])}


def field_missing(payload: dict[str, Any] | None, field: str) -> bool:
    return payload is None or field not in payload or payload[field] is None


def missing_product_fields(chunk: dict[str, Any] | None) -> list[str]:
    if chunk is None:
        return DIRECT_PRODUCT_FIELDS[:]
    if all(not field_missing(chunk, field) for field in DIRECT_PRODUCT_FIELDS):
        return []
    corner_missing = [
        field for field in PRODUCT_CORNER_FIELDS if field_missing(chunk, field)
    ]
    if not corner_missing:
        return []
    scale_missing = [
        field for field in SCALE_INTERVAL_PRODUCT_FIELDS if field_missing(chunk, field)
    ]
    if not scale_missing:
        return []
    if any(
        field in chunk and chunk[field] is not None
        for field in SCALE_INTERVAL_PRODUCT_FIELDS
    ):
        return scale_missing
    if any(field in chunk and chunk[field] is not None for field in PRODUCT_CORNER_FIELDS):
        return corner_missing
    return DIRECT_PRODUCT_FIELDS[:]


def missing_polynomial_fields(chunk: dict[str, Any] | None) -> list[str]:
    if chunk is None:
        return POLYNOMIAL_DIRECT_FIELDS[:]
    if all(not field_missing(chunk, field) for field in POLYNOMIAL_DIRECT_FIELDS):
        return []
    term_missing = [
        field for field in POLYNOMIAL_TERM_FIELDS if field_missing(chunk, field)
    ]
    if not term_missing:
        return []
    if any(
        field in chunk and chunk[field] is not None
        for field in POLYNOMIAL_TERM_FIELDS
    ):
        return term_missing
    return POLYNOMIAL_DIRECT_FIELDS[:]


def missing_for_chunk(chunk: dict[str, Any] | None) -> list[str]:
    return [
        field for field in CELL_REQUIRED_FIELDS if field_missing(chunk, field)
    ] + missing_product_fields(chunk) + missing_polynomial_fields(chunk)



def missing_for_row(row: dict[str, Any] | None, *, is_tail: bool) -> list[str]:
    required = ROW_REQUIRED_FIELDS + (TAIL_ROW_REQUIRED_FIELDS if is_tail else [])
    return [field for field in required if field_missing(row, field)]


def grouped_missing_counts(missing_counts: Counter[str] | dict[str, int]) -> dict[str, int]:
    grouped: Counter[str] = Counter()
    for field, count in missing_counts.items():
        grouped[FIELD_TO_GROUP.get(field, "other")] += int(count)
    return dict(sorted(grouped.items()))


def proof_data_summary(proof_data: dict[str, Any] | None) -> dict[str, Any]:
    if proof_data is None:
        return {
            "available": False,
            "status": None,
            "families": 0,
            "rows": 0,
            "chunk_cells": 0,
            "cells_with_any_populated_field": 0,
            "cells_with_any_populated_required_field": 0,
            "cells_with_any_populated_proof_field": 0,
        }
    families = proof_data.get("families", [])
    row_count = 0
    cell_count = 0
    populated_required_cells = 0
    populated_proof_cells = 0
    for family in families:
        rows = family.get("distances", [])
        row_count += len(rows)
        for row in rows:
            chunks = row.get("chunks", [])
            cell_count += len(chunks)
            for chunk in chunks:
                if any(chunk.get(field) is not None for field in CELL_REQUIRED_FIELDS):
                    populated_required_cells += 1
                if any(chunk.get(field) is not None for field in CELL_PROOF_FIELDS):
                    populated_proof_cells += 1
    return {
        "available": True,
        "status": proof_data.get("status"),
        "families": len(families),
        "rows": row_count,
        "chunk_cells": cell_count,
        "cells_with_any_populated_field": populated_required_cells,
        "cells_with_any_populated_required_field": populated_required_cells,
        "cells_with_any_populated_proof_field": populated_proof_cells,
    }


def build_inventory(
    worklist: dict[str, Any],
    *,
    probe: dict[str, Any] | None,
    proof_data: dict[str, Any] | None,
    proof_data_source: str | None,
) -> dict[str, Any]:
    families = worklist.get("families", [])
    proof_families = proof_family_map(proof_data)
    missing_counter: Counter[str] = Counter()
    family_reports: list[dict[str, Any]] = []
    total_rows = 0
    total_cells = 0
    complete_cells = 0
    complete_rows = 0

    for family in families:
        family_id = str(family["id"])
        proof_family = proof_families.get(family_id)
        proof_rows = proof_row_map(proof_family) if proof_family is not None else {}
        family_missing_counter: Counter[str] = Counter()
        family_cells = family_cell_count(family)
        family_complete_cells = 0
        family_complete_rows = 0
        row_examples: list[dict[str, Any]] = []
        is_tail = str(family["family_kind"]) == "tail"

        for row in family.get("distances", []):
            row_index = int(row["index"])
            proof_row = proof_rows.get(row_index)
            row_missing = missing_for_row(proof_row, is_tail=is_tail)
            for field in row_missing:
                family_missing_counter[f"row.{field}"] += 1
                missing_counter[f"row.{field}"] += 1

            chunks = family.get("chunks", [])
            proof_chunks = proof_chunk_map(proof_row) if proof_row is not None else {}
            row_complete = not row_missing
            row_complete_cells = 0
            first_chunk_missing: list[str] | None = None
            for chunk in chunks:
                chunk_index = int(chunk["index"])
                missing = missing_for_chunk(proof_chunks.get(chunk_index))
                if missing:
                    row_complete = False
                    if first_chunk_missing is None:
                        first_chunk_missing = missing[:]
                    for field in missing:
                        family_missing_counter[f"cell.{field}"] += 1
                        missing_counter[f"cell.{field}"] += 1
                else:
                    row_complete_cells += 1

            if row_complete:
                family_complete_rows += 1
            family_complete_cells += row_complete_cells
            total_rows += 1
            total_cells += len(chunks)

            if len(row_examples) < 3 and (row_missing or first_chunk_missing):
                row_examples.append(
                    {
                        "index": row_index,
                        "distance": row.get("distance"),
                        "row_missing": row_missing,
                        "first_chunk_missing": first_chunk_missing or [],
                    }
                )

        complete_rows += family_complete_rows
        complete_cells += family_complete_cells
        family_reports.append(
            {
                "id": family_id,
                "block": family.get("block"),
                "family_kind": family.get("family_kind"),
                "lean_valid_constructor": family.get("lean_valid_constructor"),
                "distance_rows": family.get("distance_count"),
                "chunk_count": family.get("chunk_count"),
                "chunk_cells": family_cells,
                "complete_rows": family_complete_rows,
                "complete_cells": family_complete_cells,
                "missing_field_counts": dict(sorted(family_missing_counter.items())),
                "missing_group_counts": grouped_missing_counts(
                    family_missing_counter
                ),
                "examples": row_examples,
            }
        )

    status = "ready_to_generate_lean_payload" if complete_cells == total_cells and complete_rows == total_rows else "missing_proof_data"
    probe_info = probe_summary(probe)
    proof_info = proof_data_summary(proof_data)
    return {
        "schema": "q3_psdpd_step33_a_chunk_taylor_payload_inventory.v1",
        "status": status,
        "meaning": (
            "Inventory for the proof-data required to instantiate "
            "RawOmegaAChunkTaylorPayload.PayloadFin.  Numeric Arb probes are "
            "not accepted as Lean proof data."
        ),
        "worklist_schema": worklist.get("schema"),
        "lean_payload_type": worklist.get("lean_payload_type"),
        "lean_step33a_wrapper": worklist.get("lean_step33a_wrapper"),
        "lean_step33b_wrapper": worklist.get("lean_step33b_wrapper"),
        "proof_data_schema_expected": PROOF_DATA_SCHEMA,
        "proof_data_source": proof_data_source,
        "proof_data_summary": proof_info,
        "probe_summary": probe_info,
        "totals": {
            "families": len(families),
            "distance_rows": total_rows,
            "chunk_cells": total_cells,
            "complete_rows": complete_rows,
            "complete_cells": complete_cells,
            "missing_cells": total_cells - complete_cells,
        },
        "required_cell_fields": CELL_REQUIRED_FIELDS,
        "missing_field_groups": FIELD_GROUPS,
        "product_proof_alternatives": {
            "direct": DIRECT_PRODUCT_FIELDS,
            "corner": PRODUCT_CORNER_FIELDS,
            "corner_receiver": (
                "RawOmegaATaylorModelCertificate.product_bounds_of_eight_corners"
            ),
            "scale_interval": SCALE_INTERVAL_PRODUCT_FIELDS,
            "scale_interval_receiver": (
                "RawOmegaATaylorModelCertificate."
                "product_bounds_of_scale_interval_and_sixteen_corners"
            ),
        },
        "required_row_fields": ROW_REQUIRED_FIELDS,
        "required_tail_row_fields": TAIL_ROW_REQUIRED_FIELDS,
        "missing_field_counts": dict(sorted(missing_counter.items())),
        "missing_group_counts": grouped_missing_counts(missing_counter),
        "families": family_reports,
        "route_guard": [
            "do not emit trusted Arb/acb integral theorems",
            "do not mutate A CSV, ARadius, radius-floor, or LDL",
            "do not route to Q3.Main or H1/PO3",
            "do not call Step33A.1-A closed until PayloadFin compiles",
        ],
    }


def render_md(inventory: dict[str, Any]) -> str:
    totals = inventory["totals"]
    probe = inventory["probe_summary"]
    proof_data = inventory["proof_data_summary"]
    lines = [
        "# Step33A.1-A Taylor Payload Proof-Data Inventory",
        "",
        "This report is a guardrail, not a Lean proof object.",
        "",
        "## Verdict",
        "",
        f"- status: `{inventory['status']}`",
        f"- payload type: `{inventory['lean_payload_type']}`",
        f"- Step33A wrapper: `{inventory['lean_step33a_wrapper']}`",
        f"- Step33B/33C wrapper: `{inventory['lean_step33b_wrapper']}`",
        f"- expected proof-data schema: `{inventory['proof_data_schema_expected']}`",
        f"- proof-data source: `{inventory['proof_data_source']}`",
        "",
        "## Proof Data Source",
        "",
        f"- available: `{proof_data['available']}`",
        f"- status: `{proof_data['status']}`",
        f"- families: `{proof_data['families']}`",
        f"- rows: `{proof_data['rows']}`",
        f"- chunk cells: `{proof_data['chunk_cells']}`",
        f"- cells with any populated required field: `{proof_data['cells_with_any_populated_required_field']}`",
        f"- cells with any populated proof field: `{proof_data['cells_with_any_populated_proof_field']}`",
        "",
        "## Counts",
        "",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distance_rows']}`",
        f"- chunk cells: `{totals['chunk_cells']}`",
        f"- complete rows: `{totals['complete_rows']}`",
        f"- complete cells: `{totals['complete_cells']}`",
        f"- missing cells: `{totals['missing_cells']}`",
        "",
        "## Diagnostic Probe",
        "",
        f"- available: `{probe['available']}`",
        f"- families: `{probe['families']}`",
        f"- rows: `{probe['rows']}`",
        f"- chunk cells: `{probe['chunk_cells']}`",
        f"- numeric chunk intervals complete: `{probe['has_numeric_chunk_intervals']}`",
        f"- Taylor proof data present: `{probe['has_taylor_proof_data']}`",
        "",
        "## Required Cell Fields",
        "",
    ]
    for field in inventory["required_cell_fields"]:
        lines.append(f"- `{field}`")
    product = inventory["product_proof_alternatives"]
    lines.extend(["", "## Product Proof Alternative", ""])
    lines.append(
        "Each cell must provide one of three product proof packets: direct "
        "universal proof fields, all exact-scale eight-corner fields, or a "
        "family-scale interval with all sixteen scale/omega/shape/cos corner "
        "fields.  This stays sign-generic because the raw Step22 omega weight "
        "is negative on early finite chunks."
    )
    lines.append("")
    lines.append("Direct fields:")
    for field in product["direct"]:
        lines.append(f"- `{field}`")
    lines.append("")
    lines.append(f"Corner receiver: `{product['corner_receiver']}`")
    lines.append("")
    lines.append("Corner fields:")
    for field in product["corner"]:
        lines.append(f"- `{field}`")
    lines.append("")
    lines.append(f"Scale-interval receiver: `{product['scale_interval_receiver']}`")
    lines.append("")
    lines.append("Scale-interval fields:")
    for field in product["scale_interval"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "## Required Row Fields", ""])
    for field in inventory["required_row_fields"]:
        lines.append(f"- `{field}`")
    if inventory["required_tail_row_fields"]:
        lines.extend(["", "Tail rows additionally require:"])
        for field in inventory["required_tail_row_fields"]:
            lines.append(f"- `{field}`")

    lines.extend(
        [
            "",
            "## Families",
            "",
            "| family | rows | chunks | cells | complete rows | complete cells | first examples |",
            "| --- | ---: | ---: | ---: | ---: | ---: | --- |",
        ]
    )
    for family in inventory["families"]:
        examples_label = ", ".join(
            f"d{example['index']}" for example in family.get("examples", [])
        ) or "-"
        lines.append(
            "| {id} | {distance_rows} | {chunk_count} | {chunk_cells} | "
            "{complete_rows} | {complete_cells} | {examples_label} |".format(
                examples_label=examples_label, **family
            )
        )

    lines.extend(["", "## Missing Field Counts", ""])
    for field, count in inventory["missing_field_counts"].items():
        lines.append(f"- `{field}`: `{count}`")

    lines.extend(["", "## Missing Field Groups", ""])
    if inventory["missing_group_counts"]:
        for group, count in inventory["missing_group_counts"].items():
            fields = inventory["missing_field_groups"].get(group, [])
            short_fields = ", ".join(f"`{field}`" for field in fields[:8])
            if len(fields) > 8:
                short_fields += ", ..."
            lines.append(f"- `{group}`: `{count}` missing field instances")
            if short_fields:
                lines.append(f"  Fields: {short_fields}")
    else:
        lines.append("- none")

    lines.extend(["", "## Example Missing Rows", ""])
    for family in inventory["families"]:
        if not family.get("examples"):
            continue
        lines.append(f"### {family['id']}")
        for example in family["examples"]:
            lines.append(
                "- row `{index}` d=`{distance}` row_missing=`{row_missing}` "
                "first_chunk_missing=`{first_chunk_missing}`".format(**example)
            )
        lines.append("")

    lines.extend(["## Route Guard", ""])
    for item in inventory["route_guard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--probe", type=Path, default=DEFAULT_PROBE)
    parser.add_argument("--proof-data", type=Path)
    parser.add_argument("--out-json", type=Path)
    parser.add_argument("--out-md", type=Path)
    args = parser.parse_args()

    worklist = load_json(args.worklist)
    validate_worklist(worklist, args.worklist)

    probe = None
    if args.probe is not None and args.probe.exists():
        probe = load_json(args.probe)
        validate_probe(probe, args.probe)

    proof_data = None
    proof_data_source = None
    if args.proof_data is not None:
        proof_data = load_json(args.proof_data)
        proof_data_source = str(args.proof_data)
        schema = proof_data.get("schema")
        if schema != PROOF_DATA_SCHEMA:
            raise ValueError(
                f"{args.proof_data}: unexpected proof-data schema {schema!r}"
            )

    inventory = build_inventory(
        worklist,
        probe=probe,
        proof_data=proof_data,
        proof_data_source=proof_data_source,
    )

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(inventory, indent=2, sort_keys=True) + "\n")
    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_md(inventory), encoding="utf-8")

    totals = inventory["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "complete_cells={complete} missing_cells={missing} "
        "probe_numeric={probe_numeric} probe_taylor={probe_taylor}".format(
            status=inventory["status"],
            families=totals["families"],
            rows=totals["distance_rows"],
            cells=totals["chunk_cells"],
            complete=totals["complete_cells"],
            missing=totals["missing_cells"],
            probe_numeric=inventory["probe_summary"]["has_numeric_chunk_intervals"],
            probe_taylor=inventory["probe_summary"]["has_taylor_proof_data"],
        )
    )


if __name__ == "__main__":
    run()
