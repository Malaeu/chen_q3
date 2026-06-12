#!/usr/bin/env python3
"""Fail-closed audit for mapping Taylor probe output into refined proof data.

This script does not mutate the refined skeleton and does not emit Lean.  It
checks one pilot parent chunk and reports which diagnostic probe fields resemble
future proof-data fields, while keeping sampled Arb/acb evidence out of the
trusted Lean path.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_SKELETON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.json"
)
DEFAULT_PROBE = (
    REQUEST_DIR / "a_chunk_taylor_model_probe_primary_finite_0_0_split100_decimal_full.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_probe_seed_audit.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_probe_seed_audit.md"
)

SKELETON_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_proof_data.v3"
PROBE_SCHEMA = "q3_psdpd_step33_a_chunk_taylor_model_probe.v1"

ANALYTIC_FIELDS = [
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

CANDIDATE_FIELD_MAP = {
    "coeff_rational_candidate": "coeff",
    "remainder_rational_candidate": "remainder",
    "lower_model_integral": "integralLower",
    "upper_model_integral": "integralUpper",
}


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate(payload: dict[str, Any], *, schema: str, path: Path) -> None:
    found = payload.get("schema")
    if found != schema:
        raise ValueError(f"{path}: expected schema {schema!r}, found {found!r}")


def decimal_equal(a: Any, b: Any) -> bool:
    return Decimal(str(a)) == Decimal(str(b))


def find_skeleton_parent(
    skeleton: dict[str, Any], *, family_id: str, row: int, parent_chunk: int
) -> dict[str, Any]:
    for family in skeleton.get("families", []):
        if str(family.get("id")) != family_id:
            continue
        for distance in family.get("distances", []):
            if int(distance.get("row")) != row:
                continue
            for parent in distance.get("parentChunks", []):
                if int(parent.get("parentChunk")) == parent_chunk:
                    return parent
    raise ValueError(
        f"missing skeleton parent family={family_id} row={row} parent={parent_chunk}"
    )


def find_probe_cell(
    probe: dict[str, Any], *, family_id: str, row: int, parent_chunk: int
) -> dict[str, Any]:
    for cell in probe.get("cells", []):
        if (
            str(cell.get("family_id")) == family_id
            and int(cell.get("distance_index")) == row
            and int(cell.get("chunk_index")) == parent_chunk
        ):
            return cell
    raise ValueError(
        f"missing probe cell family={family_id} row={row} parent={parent_chunk}"
    )


def find_virtual_result(cell: dict[str, Any], *, degree: int, split: int) -> dict[str, Any]:
    for result in cell.get("virtual_subchunk_results", []):
        if int(result.get("degree")) == degree and int(result.get("virtual_subchunks")) == split:
            return result
    raise ValueError(f"missing virtual result degree={degree} split={split}")


def rational_zero_with_positive_residual(subchunk: dict[str, Any]) -> bool:
    remainder = str(subchunk.get("remainder_rational_candidate", ""))
    try:
        residual = Decimal(str(subchunk.get("sampled_max_residual", "0")))
    except Exception:
        return False
    return remainder.startswith("0/") and residual > 0


def build_report(
    *,
    skeleton: dict[str, Any],
    probe: dict[str, Any],
    skeleton_path: Path,
    probe_path: Path,
    family_id: str,
    row: int,
    parent_chunk: int,
    degree: int,
) -> dict[str, Any]:
    parent = find_skeleton_parent(
        skeleton, family_id=family_id, row=row, parent_chunk=parent_chunk
    )
    cell = find_probe_cell(probe, family_id=family_id, row=row, parent_chunk=parent_chunk)
    virtual = find_virtual_result(cell, degree=degree, split=int(parent["split"]))
    preview = list(virtual.get("subchunk_preview", []))
    skeleton_subchunks = list(parent.get("subchunks", []))
    expected = len(skeleton_subchunks)
    preview_count = len(preview)

    endpoint_matches = 0
    candidate_field_count = 0
    zero_remainder_positive_residual = 0
    mismatches: list[dict[str, Any]] = []
    for index, candidate in enumerate(preview):
        if index >= expected:
            mismatches.append({"subchunk": index, "reason": "probe has extra preview row"})
            continue
        target = skeleton_subchunks[index]
        matches = (
            decimal_equal(candidate.get("left"), target.get("left"))
            and decimal_equal(candidate.get("right"), target.get("right"))
            and decimal_equal(candidate.get("center"), target.get("center"))
        )
        if matches:
            endpoint_matches += 1
        else:
            mismatches.append(
                {
                    "subchunk": index,
                    "reason": "left/right/center mismatch",
                    "probe": {
                        "left": candidate.get("left"),
                        "right": candidate.get("right"),
                        "center": candidate.get("center"),
                    },
                    "skeleton": {
                        "left": target.get("left"),
                        "right": target.get("right"),
                        "center": target.get("center"),
                    },
                }
            )
        for source_field in CANDIDATE_FIELD_MAP:
            if candidate.get(source_field) is not None:
                candidate_field_count += 1
        if rational_zero_with_positive_residual(candidate):
            zero_remainder_positive_residual += 1

    proof_fields_total = expected * len(ANALYTIC_FIELDS)
    missing_preview_subchunks = max(0, expected - preview_count)
    proof_safe_closed_fields = 0
    status = "diagnostic_probe_not_proof_data"
    if preview_count < expected:
        blocker = "probe stores only a preview of the refined subchunks"
    elif zero_remainder_positive_residual:
        blocker = "probe rationalized positive sampled remainders to zero"
    else:
        blocker = "probe lacks universal raw/poly value and diff-bound proofs"

    return {
        "schema": "q3_psdpd_step33_a_refined_subchunk_probe_seed_audit.v1",
        "status": status,
        "meaning": (
            "Fail-closed pilot audit. Candidate probe data may guide the future "
            "proof-producing generator, but this report closes no Lean fields."
        ),
        "skeleton": str(skeleton_path),
        "probe": str(probe_path),
        "pilot": {
            "family": family_id,
            "row": row,
            "parentChunk": parent_chunk,
            "degree": degree,
            "split": int(parent["split"]),
            "left": parent.get("left"),
            "right": parent.get("right"),
        },
        "counts": {
            "expectedSubchunks": expected,
            "probePreviewSubchunks": preview_count,
            "missingPreviewSubchunks": missing_preview_subchunks,
            "endpointMatchesInPreview": endpoint_matches,
            "endpointMismatches": len(mismatches),
            "candidateMappedFields": candidate_field_count,
            "proofSafeClosedFields": proof_safe_closed_fields,
            "proofFieldsRequiredForParent": proof_fields_total,
            "zeroRemainderWithPositiveSampledResidual": zero_remainder_positive_residual,
        },
        "candidateFieldMap": CANDIDATE_FIELD_MAP,
        "mismatches": mismatches[:20],
        "blocker": blocker,
        "routeGuard": [
            "do not mutate the refined skeleton from this audit",
            "do not emit Lean from sampled probe data",
            "coefficients and model integrals are diagnostic candidates only",
            "future proof-data must use outward rationalization for remainders",
            "future proof-data must provide universal raw/poly value bounds or a checked replacement theorem",
            "future proof-data must still provide row hLowerSum/hUpperSum comparisons",
        ],
        "nextGeneratorContract": [
            "emit all refined subchunks, not preview rows",
            "emit outward-rational coeff/remainder/integralLower/integralUpper candidates",
            "emit polynomial value bounds accepted by the checked polynomial-radius helper",
            "emit raw-integrand value bounds or a checked analytic enclosure helper",
            "emit diffLower/diffUpper and integral comparisons as Lean-checkable rational inequalities",
            "then rerun the existing refined emitter guard",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    pilot = report["pilot"]
    counts = report["counts"]
    lines = [
        "# Step33A.1-A Refined Subchunk Probe Seed Audit",
        "",
        "Fail-closed pilot audit.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
        f"- blocker: `{report['blocker']}`",
        f"- family: `{pilot['family']}`",
        f"- row: `{pilot['row']}`",
        f"- parent chunk: `{pilot['parentChunk']}`",
        f"- degree: `{pilot['degree']}`",
        f"- split: `{pilot['split']}`",
        "",
        "## Counts",
        "",
        "| item | count |",
        "| --- | ---: |",
    ]
    for key, value in counts.items():
        lines.append(f"| `{key}` | `{value}` |")
    lines.extend(
        [
            "",
            "## Candidate Field Map",
            "",
            "| probe field | skeleton field |",
            "| --- | --- |",
        ]
    )
    for source, target in report["candidateFieldMap"].items():
        lines.append(f"| `{source}` | `{target}` |")
    lines.extend(["", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Next Generator Contract", ""])
    for item in report["nextGeneratorContract"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--skeleton", type=Path, default=DEFAULT_SKELETON)
    parser.add_argument("--probe", type=Path, default=DEFAULT_PROBE)
    parser.add_argument("--family", type=str, default="primary_finite")
    parser.add_argument("--row", type=int, default=0)
    parser.add_argument("--parent-chunk", type=int, default=0)
    parser.add_argument("--degree", type=int, default=16)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    skeleton = load_json(args.skeleton)
    validate(skeleton, schema=SKELETON_SCHEMA, path=args.skeleton)
    probe = load_json(args.probe)
    validate(probe, schema=PROBE_SCHEMA, path=args.probe)
    report = build_report(
        skeleton=skeleton,
        probe=probe,
        skeleton_path=args.skeleton,
        probe_path=args.probe,
        family_id=args.family,
        row=args.row,
        parent_chunk=args.parent_chunk,
        degree=args.degree,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} expected_subchunks={expected} preview_subchunks={preview} proof_safe_closed={closed}".format(
            status=report["status"],
            expected=report["counts"]["expectedSubchunks"],
            preview=report["counts"]["probePreviewSubchunks"],
            closed=report["counts"]["proofSafeClosedFields"],
        )
    )


if __name__ == "__main__":
    run()
