#!/usr/bin/env python3
"""Seed Step33 raw-Omega Taylor proof-data with diagnostic chunk bounds.

The Arb/acb probe is not proof data.  This script copies only the discovered
chunk lower/upper candidate values into the proof-data schema and keeps every
proof-bearing field missing.  The result is useful as a starting point for the
real Taylor/model proof-data generator, but the Lean emitter must still refuse
to write a payload from this seed.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    DEFAULT_PROBE,
    PROOF_DATA_SCHEMA,
    load_json,
    validate_probe,
)
from q3_psdpd_step33_a_chunk_taylor_payload_proof_data_skeleton import (
    DEFAULT_OUT_JSON as DEFAULT_SKELETON,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_probe_seed.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_probe_seed.md"


def probe_row_map(probe: dict[str, Any]) -> dict[tuple[str, int], dict[str, Any]]:
    rows: dict[tuple[str, int], dict[str, Any]] = {}
    for family in probe.get("families", []):
        for row in family.get("rows", []):
            family_id = str(row["family_id"])
            row_index = int(row["distance_index"])
            rows[(family_id, row_index)] = row
    return rows


def probe_chunk_map(row: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {int(chunk["index"]): chunk for chunk in row.get("chunks", [])}


def seed_from_probe(skeleton: dict[str, Any], probe: dict[str, Any]) -> dict[str, Any]:
    if skeleton.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected skeleton schema {skeleton.get('schema')!r}")
    rows_by_key = probe_row_map(probe)
    seeded_families = []
    total_rows = 0
    total_cells = 0
    seeded_cells = 0
    missing_probe_cells: list[dict[str, Any]] = []

    for family in skeleton.get("families", []):
        family_id = str(family["id"])
        seeded_rows = []
        family_seeded_cells = 0
        for row in family.get("distances", []):
            row_index = int(row["index"])
            probe_row = rows_by_key.get((family_id, row_index))
            probe_chunks = probe_chunk_map(probe_row) if probe_row is not None else {}
            seeded_chunks = []
            for chunk in row.get("chunks", []):
                chunk_index = int(chunk["index"])
                seeded_chunk = dict(chunk)
                probe_chunk = probe_chunks.get(chunk_index)
                if probe_chunk is None:
                    missing_probe_cells.append(
                        {
                            "family": family_id,
                            "row": row_index,
                            "chunk": chunk_index,
                        }
                    )
                else:
                    seeded_chunk["chunkLower"] = probe_chunk["lower"]
                    seeded_chunk["chunkUpper"] = probe_chunk["upper"]
                    seeded_chunk["chunkBoundSource"] = "diagnostic_arb_acb_probe"
                    seeded_chunk["chunkBoundProofStatus"] = "candidate_only_not_proof"
                    family_seeded_cells += 1
                    seeded_cells += 1
                seeded_chunks.append(seeded_chunk)
                total_cells += 1

            seeded_row = dict(row)
            if probe_row is not None:
                seeded_row["chunkSumLowerCandidate"] = probe_row.get("chunk_sum_lower")
                seeded_row["chunkSumUpperCandidate"] = probe_row.get("chunk_sum_upper")
                seeded_row["chunkSumWidthCandidate"] = probe_row.get("chunk_sum_width")
                seeded_row["fitsTargetCandidate"] = probe_row.get("fits_target")
                seeded_row["fitsAfterLocalTargetRefreshCandidate"] = probe_row.get(
                    "fits_after_local_target_refresh"
                )
                seeded_row["probeTargetLower"] = probe_row.get("target_lower")
                seeded_row["probeTargetUpper"] = probe_row.get("target_upper")
                seeded_row["suggestedTargetLower"] = probe_row.get(
                    "suggested_target_lower"
                )
                seeded_row["suggestedTargetUpper"] = probe_row.get(
                    "suggested_target_upper"
                )
            seeded_row["chunks"] = seeded_chunks
            seeded_rows.append(seeded_row)
            total_rows += 1

        seeded_family = dict(family)
        seeded_family["distances"] = seeded_rows
        seeded_family["seededChunkBounds"] = family_seeded_cells
        seeded_families.append(seeded_family)

    seeded = dict(skeleton)
    seeded["status"] = "probe_seed_chunk_bounds_only_missing_proofs"
    seeded["meaning"] = (
        "Diagnostic Arb/acb chunk lower/upper candidates have been copied into "
        "the proof-data schema.  These values are not trusted Lean proof data; "
        "all Taylor/model proof fields must still be generated and checked."
    )
    seeded["families"] = seeded_families
    seeded["probeSource"] = probe.get("source_worklist")
    seeded["seedSource"] = "rawomega_a_chunk_integral_probe_all_256.json"
    seeded["totals"] = {
        "families": len(seeded_families),
        "distanceRows": total_rows,
        "chunkCells": total_cells,
        "seededChunkBounds": seeded_cells,
        "missingProbeCells": len(missing_probe_cells),
        "populatedProofCells": 0,
    }
    seeded["routeGuard"] = [
        "chunk bounds seeded from Arb/acb diagnostics are candidates only",
        "do not treat this seed as trusted proof data",
        "do not emit Lean until Taylor/model proof fields are complete",
    ]
    seeded["missingProbeCells"] = missing_probe_cells[:20]
    return seeded


def render_md(seed: dict[str, Any]) -> str:
    totals = seed["totals"]
    lines = [
        "# Step33A.1-A Taylor Payload Probe Seed",
        "",
        "This file seeds candidate `chunkLower` / `chunkUpper` values from the",
        "diagnostic Arb/acb probe.  It is not a Lean proof object.",
        "",
        "## Verdict",
        "",
        f"- schema: `{seed['schema']}`",
        f"- status: `{seed['status']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distanceRows']}`",
        f"- chunk cells: `{totals['chunkCells']}`",
        f"- seeded chunk bounds: `{totals['seededChunkBounds']}`",
        f"- missing probe cells: `{totals['missingProbeCells']}`",
        f"- populated proof cells: `{totals['populatedProofCells']}`",
        "",
        "## Families",
        "",
        "| family | rows | chunks | seeded chunk bounds |",
        "| --- | ---: | ---: | ---: |",
    ]
    for family in seed["families"]:
        lines.append(
            "| {id} | {distanceRows} | {chunkCount} | {seededChunkBounds} |".format(
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
    parser.add_argument("--skeleton", type=Path, default=DEFAULT_SKELETON)
    parser.add_argument("--probe", type=Path, default=DEFAULT_PROBE)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    skeleton = load_json(args.skeleton)
    probe = load_json(args.probe)
    validate_probe(probe, args.probe)
    seed = seed_from_probe(skeleton, probe)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(seed, indent=2, sort_keys=True) + "\n")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(seed), encoding="utf-8")

    totals = seed["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "seeded_chunk_bounds={seeded} missing_probe_cells={missing}".format(
            status=seed["status"],
            families=totals["families"],
            rows=totals["distanceRows"],
            cells=totals["chunkCells"],
            seeded=totals["seededChunkBounds"],
            missing=totals["missingProbeCells"],
        )
    )


if __name__ == "__main__":
    run()
