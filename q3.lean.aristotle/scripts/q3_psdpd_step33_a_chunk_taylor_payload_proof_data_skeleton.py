#!/usr/bin/env python3
"""Emit the Step33 raw-Omega A Taylor proof-data skeleton.

The output of this script is not Lean proof data yet.  It is an addressed
schema instance for `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`:
all 92 distance rows and all 2392 chunk cells are present, but proof-bearing
fields are intentionally omitted by default.

The inventory script treats omitted and `null` fields as missing.  This
prevents the next generator from confusing an addressed template with a trusted
payload, while still giving it a stable file contract to fill.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    CELL_REQUIRED_FIELDS,
    PROOF_DATA_SCHEMA,
    ROW_REQUIRED_FIELDS,
    TAIL_ROW_REQUIRED_FIELDS,
    DEFAULT_WORKLIST,
    load_json,
    validate_worklist,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_proof_data_skeleton.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_proof_data_skeleton.md"


def empty_cell(chunk: dict[str, Any], *, include_null_fields: bool) -> dict[str, Any]:
    cell: dict[str, Any] = {
        "index": int(chunk["index"]),
        "left": chunk.get("left"),
        "right": chunk.get("right"),
    }
    if include_null_fields:
        for field in CELL_REQUIRED_FIELDS:
            cell[field] = None
    return cell


def empty_row(
    row: dict[str, Any],
    chunks: list[dict[str, Any]],
    *,
    is_tail: bool,
    include_null_fields: bool,
) -> dict[str, Any]:
    proof_row: dict[str, Any] = {
        "index": int(row["index"]),
        "distance": row.get("distance"),
        "targetLowerValue": row.get("target_lower_value"),
        "targetUpperValue": row.get("target_upper_value"),
        "priority": row.get("priority"),
        "targetRefreshApplied": row.get("target_refresh_applied"),
        "targetRefreshSlackAfter": row.get("target_refresh_slack_after"),
        "chunks": [
            empty_cell(chunk, include_null_fields=include_null_fields)
            for chunk in chunks
        ],
    }
    if include_null_fields:
        for field in ROW_REQUIRED_FIELDS:
            proof_row[field] = None
        if is_tail:
            for field in TAIL_ROW_REQUIRED_FIELDS:
                proof_row[field] = None
    return proof_row


def build_skeleton(worklist: dict[str, Any], *, include_null_fields: bool) -> dict[str, Any]:
    families = []
    total_rows = 0
    total_cells = 0
    for family in worklist.get("families", []):
        chunks = list(family.get("chunks", []))
        is_tail = str(family.get("family_kind")) == "tail"
        rows = [
            empty_row(
                row,
                chunks,
                is_tail=is_tail,
                include_null_fields=include_null_fields,
            )
            for row in family.get("distances", [])
        ]
        total_rows += len(rows)
        total_cells += sum(len(row["chunks"]) for row in rows)
        families.append(
            {
                "id": str(family["id"]),
                "block": family.get("block"),
                "familyKind": family.get("family_kind"),
                "collectionName": family.get("collection_name"),
                "k": family.get("k"),
                "domain": family.get("domain"),
                "leanValidConstructor": family.get("lean_valid_constructor"),
                "distanceRows": len(rows),
                "chunkCount": int(family.get("chunk_count", len(chunks))),
                "distances": rows,
            }
        )

    return {
        "schema": PROOF_DATA_SCHEMA,
        "status": (
            "skeleton_null_missing_values"
            if include_null_fields
            else "skeleton_address_only_missing_values"
        ),
        "meaning": (
            "Addressed proof-data template for RawOmegaAChunkTaylorPayload."
            "PayloadFin.  Null fields are placeholders and must be filled by a"
            " proof-producing generator before Lean emission."
        ),
        "worklistSchema": worklist.get("schema"),
        "leanPayloadType": worklist.get("lean_payload_type"),
        "leanStep33AWrapper": worklist.get("lean_step33a_wrapper"),
        "leanStep33BWrapper": worklist.get("lean_step33b_wrapper"),
        "requiredCellFields": CELL_REQUIRED_FIELDS,
        "requiredRowFields": ROW_REQUIRED_FIELDS,
        "requiredTailRowFields": TAIL_ROW_REQUIRED_FIELDS,
        "includeNullFields": include_null_fields,
        "totals": {
            "families": len(families),
            "distanceRows": total_rows,
            "chunkCells": total_cells,
            "populatedProofCells": 0,
        },
        "families": families,
        "routeGuard": [
            "skeleton addresses are not proof data",
            "do not emit Lean payload from omitted or null fields",
            "do not use Arb/acb numeric probes as trusted proofs",
            "do not call Step33A.1-A closed until PayloadFin compiles",
        ],
    }


def render_md(skeleton: dict[str, Any]) -> str:
    totals = skeleton["totals"]
    lines = [
        "# Step33A.1-A Taylor Payload Proof-Data Skeleton",
        "",
        "This is an addressed schema template, not a Lean proof object.",
        "",
        "## Verdict",
        "",
        f"- schema: `{skeleton['schema']}`",
        f"- status: `{skeleton['status']}`",
        f"- include null fields: `{skeleton['includeNullFields']}`",
        f"- payload type: `{skeleton['leanPayloadType']}`",
        f"- Step33A wrapper: `{skeleton['leanStep33AWrapper']}`",
        f"- Step33B/33C wrapper: `{skeleton['leanStep33BWrapper']}`",
        "",
        "## Counts",
        "",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- populated proof cells: `{totals['populatedProofCells']}`",
        "",
        "## Required Cell Fields",
        "",
    ]
    for field in skeleton["requiredCellFields"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "## Required Row Fields", ""])
    for field in skeleton["requiredRowFields"]:
        lines.append(f"- `{field}`")
    if skeleton["requiredTailRowFields"]:
        lines.extend(["", "Tail rows additionally require:"])
        for field in skeleton["requiredTailRowFields"]:
            lines.append(f"- `{field}`")

    lines.extend(
        [
            "",
            "## Families",
            "",
            "| family | rows | chunks | cells | constructor |",
            "| --- | ---: | ---: | ---: | --- |",
        ]
    )
    for family in skeleton["families"]:
        cells = int(family["distanceRows"]) * int(family["chunkCount"])
        lines.append(
            "| {id} | {distanceRows} | {chunkCount} | {cells} | `{leanValidConstructor}` |".format(
                cells=cells,
                **family,
            )
        )

    lines.extend(["", "## Route Guard", ""])
    for item in skeleton["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument(
        "--include-null-fields",
        action="store_true",
        help="emit every required proof-bearing field with value null",
    )
    args = parser.parse_args()

    worklist = load_json(args.worklist)
    validate_worklist(worklist, args.worklist)
    skeleton = build_skeleton(worklist, include_null_fields=args.include_null_fields)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(skeleton, indent=2, sort_keys=True) + "\n")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(skeleton), encoding="utf-8")

    totals = skeleton["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "populated_proof_cells={populated}".format(
            status=skeleton["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            populated=totals["populatedProofCells"],
        )
    )


if __name__ == "__main__":
    run()
