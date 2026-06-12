#!/usr/bin/env python3
"""Build the refined-subchunk worklist for Step33 raw-Omega Taylor payloads.

This is a fail-closed address/worklist generator.  It reads the current
parent-chunk proof-data seed and expands each parent chunk into the refined
subchunks selected by the diagnostic route:

* finite chunk 0: split100
* remaining finite chunks: split10
* tail chunks: split20

The output is not Lean proof data.  It records the subchunk addresses and
geometric intervals that a later proof-producing generator must fill with
Taylor/model certificate fields.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    PROOF_DATA_SCHEMA,
    load_json,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_PROOF_DATA = REQUEST_DIR / "a_chunk_taylor_payload_product_abs_seed.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_worklist.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_worklist.md"

DEFAULT_FIRST_FINITE_SPLIT = 100
DEFAULT_REST_FINITE_SPLIT = 10
DEFAULT_TAIL_SPLIT = 20
DEFAULT_DEGREE = 16

SUBCHUNK_REQUIRED_FIELDS = [
    "degree",
    "coeff",
    "remainder",
    "remainderNonneg",
    "polyLower",
    "polyUpper",
    "polynomialLowerBound",
    "polynomialUpperBound",
    "diffLower",
    "diffUpper",
    "integralLower",
    "integralUpper",
]

PARENT_REQUIRED_FIELDS = [
    "RawOmegaAChunkTaylorPayload.RefinedPayloadFin",
    "RawOmegaAChunkTaylorPayload.RefinedPayloadFin.toDirectTailWindowInputs",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.n",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.pts",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.subLower",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.subUpper",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.first_eq",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.last_eq",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.mono",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.hProfileInt",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.subCert",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.lower_le_sum",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.sum_le_upper",
    "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.of_refinedSubchunkSums (exact-sum parent cert)",
    "RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunks",
    "RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunkSums (optional exact-sum parent route)",
]


def dec(value: Any) -> Decimal:
    return Decimal(str(value))


def decimal_str(value: Decimal) -> str:
    if value == 0:
        return "0.000000000000000000E+0"
    return format(value, ".18E")


def proof_family_map(proof_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    if proof_data.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {proof_data.get('schema')!r}")
    return {str(family["id"]): family for family in proof_data.get("families", [])}


def split_for_chunk(
    *,
    family: dict[str, Any],
    chunk_index: int,
    first_finite_split: int,
    rest_finite_split: int,
    tail_split: int,
) -> tuple[int, str]:
    family_kind = str(family.get("familyKind"))
    if family_kind == "tail":
        return tail_split, f"tail_split{tail_split}"
    if family_kind == "finite" and chunk_index == 0:
        return first_finite_split, f"finite_first_split{first_finite_split}"
    if family_kind == "finite":
        return rest_finite_split, f"finite_rest_split{rest_finite_split}"
    raise ValueError(
        f"unexpected family kind {family_kind!r} for {family.get('id')!r}"
    )


def build_subchunks(
    *,
    family: dict[str, Any],
    row: dict[str, Any],
    chunk: dict[str, Any],
    split: int,
    policy: str,
    degree: int,
) -> list[dict[str, Any]]:
    left = dec(chunk["left"])
    right = dec(chunk["right"])
    step = (right - left) / Decimal(split)
    records = []
    for sub_index in range(split):
        sub_left = left + step * Decimal(sub_index)
        sub_right = left + step * Decimal(sub_index + 1)
        center = (sub_left + sub_right) / Decimal(2)
        radius = (sub_right - sub_left) / Decimal(2)
        records.append(
            {
                "family": family["id"],
                "domain": family.get("domain"),
                "k": family.get("k"),
                "distanceRow": int(row["index"]),
                "distance": row.get("distance"),
                "parentChunk": int(chunk["index"]),
                "subchunk": sub_index,
                "split": split,
                "policy": policy,
                "left": decimal_str(sub_left),
                "right": decimal_str(sub_right),
                "center": decimal_str(center),
                "radius": decimal_str(radius),
                "degreeCandidate": degree,
                "status": "address_only_missing_taylor_model_certificate",
            }
        )
    return records


def build_worklist(
    *,
    proof_data: dict[str, Any],
    proof_data_source: Path,
    first_finite_split: int,
    rest_finite_split: int,
    tail_split: int,
    degree: int,
) -> dict[str, Any]:
    families = []
    totals = {
        "families": 0,
        "rows": 0,
        "parentChunks": 0,
        "subchunks": 0,
    }
    policy_counts: dict[str, int] = {}

    for family in proof_data.get("families", []):
        family_rows = []
        family_totals = {
            "rows": 0,
            "parentChunks": 0,
            "subchunks": 0,
        }
        for row in family.get("distances", []):
            parent_chunks = []
            for chunk in row.get("chunks", []):
                split, policy = split_for_chunk(
                    family=family,
                    chunk_index=int(chunk["index"]),
                    first_finite_split=first_finite_split,
                    rest_finite_split=rest_finite_split,
                    tail_split=tail_split,
                )
                subchunks = build_subchunks(
                    family=family,
                    row=row,
                    chunk=chunk,
                    split=split,
                    policy=policy,
                    degree=degree,
                )
                policy_counts[policy] = policy_counts.get(policy, 0) + len(subchunks)
                step = (dec(chunk["right"]) - dec(chunk["left"])) / Decimal(split)
                points = [
                    decimal_str(dec(chunk["left"]) + step * Decimal(i))
                    for i in range(split + 1)
                ]
                parent_chunks.append(
                    {
                        "parentChunk": int(chunk["index"]),
                        "left": chunk["left"],
                        "right": chunk["right"],
                        "parentLower": chunk.get("chunkLower"),
                        "parentUpper": chunk.get("chunkUpper"),
                        "split": split,
                        "policy": policy,
                        "step": decimal_str(step),
                        "points": points,
                        "subchunkCount": len(subchunks),
                        "subchunks": subchunks,
                        "parentProofShape": (
                            "RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert"
                        ),
                        "parentReceiver": (
                            "RawOmegaAChunkIntegral."
                            "WindowPartBoundsCert.of_refinedSubchunks"
                        ),
                    }
                )
                family_totals["parentChunks"] += 1
                family_totals["subchunks"] += len(subchunks)
            family_rows.append(
                {
                    "row": int(row["index"]),
                    "distance": row.get("distance"),
                    "targetLower": row.get("targetLowerValue"),
                    "targetUpper": row.get("targetUpperValue"),
                    "parentChunkCount": len(parent_chunks),
                    "subchunkCount": sum(
                        parent["subchunkCount"] for parent in parent_chunks
                    ),
                    "parentChunks": parent_chunks,
                }
            )
            family_totals["rows"] += 1
        families.append(
            {
                "id": family["id"],
                "domain": family.get("domain"),
                "familyKind": family.get("familyKind"),
                "k": family.get("k"),
                "leanValidConstructor": family.get("leanValidConstructor"),
                "totals": family_totals,
                "distances": family_rows,
            }
        )
        totals["families"] += 1
        totals["rows"] += family_totals["rows"]
        totals["parentChunks"] += family_totals["parentChunks"]
        totals["subchunks"] += family_totals["subchunks"]

    return {
        "schema": "q3_psdpd_step33_a_refined_subchunk_worklist.v2",
        "meaning": (
            "Address-only refined-subchunk worklist for the raw-Omega "
            "Taylor/model PayloadFin route.  Parent 26-chunk shape is kept; "
            "refined subchunks only feed RefinedWindowPartBoundsCert below "
            "each parent.  This is not Lean proof data."
        ),
        "proofDataSource": str(proof_data_source),
        "leanLandingSurface": "RawOmegaAChunkTaylorPayload.RefinedPayloadFin",
        "leanDirectTailWindowInputs": (
            "RawOmegaAChunkTaylorPayload.RefinedPayloadFin.toDirectTailWindowInputs"
        ),
        "parameters": {
            "degreeCandidate": degree,
            "firstFiniteSplit": first_finite_split,
            "restFiniteSplit": rest_finite_split,
            "tailSplit": tail_split,
        },
        "totals": totals,
        "policyCounts": policy_counts,
        "subchunkRequiredFields": SUBCHUNK_REQUIRED_FIELDS,
        "parentRequiredFields": PARENT_REQUIRED_FIELDS,
        "routeGuard": [
            "address-only worklist",
            "not Lean proof data",
            "do not import this file as a trusted payload",
            "outer parent chunk shape remains unchanged",
            "parent closure must go through RefinedWindowPartBoundsCert",
            "exact-sum parent bounds build RefinedWindowPartBoundsCert.of_refinedSubchunkSums",
            "do not replace the top-level 26 parent chunks by a fully refined payload",
        ],
        "families": families,
    }


def render_md(worklist: dict[str, Any]) -> str:
    params = worklist["parameters"]
    totals = worklist["totals"]
    lines = [
        "# Step33A.1-A Refined Subchunk Worklist",
        "",
        "Address-only worklist.  This file does not close any Lean theorem and",
        "must not be imported as trusted proof data.",
        "",
        "## Summary",
        "",
        f"- degree candidate: `{params['degreeCandidate']}`",
        f"- first finite chunk split: `{params['firstFiniteSplit']}`",
        f"- remaining finite chunk split: `{params['restFiniteSplit']}`",
        f"- tail chunk split: `{params['tailSplit']}`",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['rows']}`",
        f"- parent chunks: `{totals['parentChunks']}`",
        f"- refined subchunks: `{totals['subchunks']}`",
        f"- Lean landing surface: `{worklist['leanLandingSurface']}`",
        "",
        "| family | domain | rows | parent chunks | subchunks |",
        "| --- | --- | ---: | ---: | ---: |",
    ]
    for family in worklist["families"]:
        ft = family["totals"]
        lines.append(
            f"| `{family['id']}` | `{family['domain']}` | "
            f"`{ft['rows']}` | `{ft['parentChunks']}` | `{ft['subchunks']}` |"
        )

    lines.extend(
        [
            "",
            "## Missing Proof Fields",
            "",
            "Each refined subchunk still needs:",
            "",
        ]
    )
    for field in worklist["subchunkRequiredFields"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "Each parent fold still needs:", ""])
    for field in worklist["parentRequiredFields"]:
        lines.append(f"- `{field}`")

    lines.extend(["", "## Guard", ""])
    for guard in worklist["routeGuard"]:
        lines.append(f"- {guard}")
    lines.append("")
    return "\n".join(lines)


def positive_int(value: int, name: str) -> int:
    if value <= 0:
        raise ValueError(f"{name} must be positive, got {value}")
    return value


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proof-data", type=Path, default=DEFAULT_PROOF_DATA)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--degree", type=int, default=DEFAULT_DEGREE)
    parser.add_argument("--first-finite-split", type=int, default=DEFAULT_FIRST_FINITE_SPLIT)
    parser.add_argument("--rest-finite-split", type=int, default=DEFAULT_REST_FINITE_SPLIT)
    parser.add_argument("--tail-split", type=int, default=DEFAULT_TAIL_SPLIT)
    args = parser.parse_args()

    getcontext().prec = 100
    first_finite_split = positive_int(args.first_finite_split, "--first-finite-split")
    rest_finite_split = positive_int(args.rest_finite_split, "--rest-finite-split")
    tail_split = positive_int(args.tail_split, "--tail-split")

    proof_data = load_json(args.proof_data)
    proof_family_map(proof_data)
    worklist = build_worklist(
        proof_data=proof_data,
        proof_data_source=args.proof_data,
        first_finite_split=first_finite_split,
        rest_finite_split=rest_finite_split,
        tail_split=tail_split,
        degree=args.degree,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(worklist, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(worklist), encoding="utf-8")

    totals = worklist["totals"]
    print(
        "status=refined_subchunk_worklist families={families} rows={rows} "
        "parent_chunks={parents} subchunks={subchunks} out_json={out_json}".format(
            families=totals["families"],
            rows=totals["rows"],
            parents=totals["parentChunks"],
            subchunks=totals["subchunks"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
