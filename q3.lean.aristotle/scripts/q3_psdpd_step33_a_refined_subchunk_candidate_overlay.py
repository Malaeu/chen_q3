#!/usr/bin/env python3
"""Build a fail-closed refined-subchunk candidate overlay from a full probe.

This is the next generator-format pilot after the probe-seed audit.  It maps a
single parent chunk's full virtual-subchunk diagnostic output into candidate
fields shaped like the refined proof-data skeleton:

  coeff/remainder/integral candidates
  direct polynomial-radius value-bound candidates

The output is intentionally not proof data.  It does not mutate the skeleton,
does not emit Lean, and records that universal raw/diff bounds are still
missing.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_SKELETON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.json"
)
DEFAULT_WORKLIST = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_worklist.json"
)
DEFAULT_PROBE = (
    REQUEST_DIR / "a_chunk_taylor_model_probe_primary_finite_0_0_split100_decimal_full.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0.md"
)

SKELETON_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_proof_data.v17"
WORKLIST_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_worklist.v2"
PROBE_SCHEMA = "q3_psdpd_step33_a_chunk_taylor_model_probe.v1"

SEEDED_FIELDS = [
    "coeff",
    "remainder",
    "remainderNonneg",
    "polyLower",
    "polyUpper",
    "polynomialLowerBound",
    "polynomialUpperBound",
    "integralLower",
    "integralUpper",
]

STILL_MISSING_FIELDS = [
    "diffLower",
    "diffUpper",
]


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


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def rational_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_floor_fraction(value: Any, denom: int) -> Fraction:
    scaled = (Decimal(str(value)) * Decimal(denom)).to_integral_value(
        rounding=ROUND_FLOOR
    )
    return Fraction(int(scaled), denom)


def decimal_ceil_fraction(value: Any, denom: int) -> Fraction:
    scaled = (Decimal(str(value)) * Decimal(denom)).to_integral_value(
        rounding=ROUND_CEILING
    )
    return Fraction(int(scaled), denom)


def fraction_ceil_to_denom(value: Fraction, denom: int) -> Fraction:
    scaled = (value.numerator * denom + value.denominator - 1) // value.denominator
    return Fraction(scaled, denom)


def decimal_equal(a: Any, b: Any) -> bool:
    return Decimal(str(a)) == Decimal(str(b))


def find_worklist_parent(
    worklist: dict[str, Any], *, family_id: str, row: int, parent_chunk: int
) -> dict[str, Any]:
    for family in worklist.get("families", []):
        if str(family.get("id")) != family_id:
            continue
        for distance in family.get("distances", []):
            if int(distance.get("row")) != row:
                continue
            for parent in distance.get("parentChunks", []):
                if int(parent.get("parentChunk")) == parent_chunk:
                    return parent
    raise ValueError(
        f"missing worklist parent family={family_id} row={row} parent={parent_chunk}"
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


def polynomial_abs_bound(*, coeff: list[str], radius: Any) -> Fraction:
    radius_fraction = parse_fraction(radius)
    total = Fraction(0, 1)
    for index, raw_coeff in enumerate(coeff):
        total += abs(parse_fraction(raw_coeff)) * (radius_fraction ** index)
    return total


def make_candidate_subchunk(
    *,
    skeleton_subchunk: dict[str, Any],
    probe_subchunk: dict[str, Any],
    denominator: int,
) -> tuple[dict[str, Any], list[str]]:
    mismatches: list[str] = []
    for field in ["left", "right", "center"]:
        if not decimal_equal(skeleton_subchunk.get(field), probe_subchunk.get(field)):
            mismatches.append(field)

    coeff = list(probe_subchunk.get("coeff_rational_candidate") or [])
    degree = int(skeleton_subchunk.get("degree", skeleton_subchunk["degreeCandidate"]))
    if len(coeff) != degree + 1:
        mismatches.append("coeff_length")
    remainder = parse_fraction(probe_subchunk["remainder_rational_candidate"])
    poly_abs = fraction_ceil_to_denom(
        polynomial_abs_bound(coeff=coeff, radius=skeleton_subchunk["radius"]),
        denominator,
    )
    integral_lower = decimal_floor_fraction(
        probe_subchunk["lower_model_integral"], denominator
    )
    integral_upper = decimal_ceil_fraction(
        probe_subchunk["upper_model_integral"], denominator
    )

    candidate = {
        "subchunk": int(skeleton_subchunk["subchunk"]),
        "left": skeleton_subchunk["left"],
        "right": skeleton_subchunk["right"],
        "center": skeleton_subchunk["center"],
        "radius": skeleton_subchunk["radius"],
        "degree": degree,
        "coeff": coeff,
        "remainder": rational_string(remainder),
        "remainderNonneg": "by norm_num",
        "polyAbs": rational_string(poly_abs),
        "polyLower": rational_string(-poly_abs),
        "polyUpper": rational_string(poly_abs),
        "polynomialLowerBound": {
            "source": (
                "RawOmegaATaylorModelCertificate."
                "polynomial_value_bounds_of_sum_abs_coeff_mul_radius"
            ),
            "status": "candidate_rational_arithmetic_not_lean_checked",
        },
        "polynomialUpperBound": {
            "source": (
                "RawOmegaATaylorModelCertificate."
                "polynomial_value_bounds_of_sum_abs_coeff_mul_radius"
            ),
            "status": "candidate_rational_arithmetic_not_lean_checked",
        },
        "integralLower": rational_string(integral_lower),
        "integralUpper": rational_string(integral_upper),
        "sampledMaxResidual": probe_subchunk.get("sampled_max_residual"),
        "sampledRemainderCandidate": probe_subchunk.get("remainder_candidate"),
        "candidateGuard": [
            "coefficients are rational candidates, not yet residual-rechecked",
            "integral bounds come from diagnostic model integral candidates",
            "polynomial bounds are exact rational-radius candidates but not emitted Lean proofs",
            "diffLower/diffUpper remain missing",
        ],
        "seededFields": SEEDED_FIELDS,
        "stillMissingFields": STILL_MISSING_FIELDS,
        "endpointMismatches": mismatches,
    }
    return candidate, mismatches


def build_overlay(
    *,
    skeleton: dict[str, Any],
    worklist: dict[str, Any],
    probe: dict[str, Any],
    skeleton_path: Path,
    worklist_path: Path,
    probe_path: Path,
    family_id: str,
    row: int,
    parent_chunk: int,
    degree: int,
    denominator: int,
) -> dict[str, Any]:
    parent = find_worklist_parent(
        worklist, family_id=family_id, row=row, parent_chunk=parent_chunk
    )
    cell = find_probe_cell(probe, family_id=family_id, row=row, parent_chunk=parent_chunk)
    virtual = find_virtual_result(cell, degree=degree, split=int(parent["split"]))
    probe_subchunks = list(virtual.get("subchunk_preview", []))
    skeleton_subchunks = list(parent.get("subchunks", []))
    if len(probe_subchunks) != len(skeleton_subchunks):
        status = "incomplete_probe_preview_no_overlay"
    else:
        status = "candidate_overlay_not_proof_data"

    candidates: list[dict[str, Any]] = []
    endpoint_mismatch_count = 0
    if status == "candidate_overlay_not_proof_data":
        for skeleton_subchunk, probe_subchunk in zip(skeleton_subchunks, probe_subchunks):
            candidate, mismatches = make_candidate_subchunk(
                skeleton_subchunk=skeleton_subchunk,
                probe_subchunk=probe_subchunk,
                denominator=denominator,
            )
            endpoint_mismatch_count += 1 if mismatches else 0
            candidates.append(candidate)

    seeded_candidate_fields = len(candidates) * len(SEEDED_FIELDS)
    still_missing_fields = len(candidates) * len(STILL_MISSING_FIELDS)
    proof_safe_closed_fields = 0
    return {
        "schema": "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1",
        "status": status,
        "meaning": (
            "Candidate overlay for one refined parent chunk.  This file is not "
            "proof data and must not be imported by Lean."
        ),
        "skeleton": str(skeleton_path),
        "worklist": str(worklist_path),
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
            "expectedSubchunks": len(skeleton_subchunks),
            "probeSubchunks": len(probe_subchunks),
            "candidateSubchunks": len(candidates),
            "endpointMismatchSubchunks": endpoint_mismatch_count,
            "seededCandidateFields": seeded_candidate_fields,
            "stillMissingFields": still_missing_fields,
            "proofSafeClosedFields": proof_safe_closed_fields,
        },
        "seededFields": SEEDED_FIELDS,
        "stillMissingFields": STILL_MISSING_FIELDS,
        "candidates": candidates,
        "routeGuard": [
            "do not mutate the refined skeleton or worklist from this overlay",
            "do not emit Lean from this overlay",
            "sampled residuals must be replaced by universal checked bounds",
            "rational coefficients must be residual-rechecked after rounding",
            "raw-integrand value bounds or direct diff bounds remain required",
            "row hLowerSum/hUpperSum comparisons remain required",
        ],
        "nextGeneratorContract": [
            "recompute residual bounds against the rational polynomial candidates",
            "generate universal raw-integrand value bounds or direct diff bounds",
            "turn polynomial-radius arithmetic into Lean-checkable proof terms",
            "then lift this overlay shape from one parent chunk to shardable refined worklists",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    pilot = report["pilot"]
    counts = report["counts"]
    lines = [
        "# Step33A.1-A Refined Subchunk Candidate Overlay",
        "",
        "Fail-closed candidate overlay.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
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
    lines.extend(["", "## Seeded Candidate Fields", ""])
    for field in report["seededFields"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "## Still Missing Fields", ""])
    for field in report["stillMissingFields"]:
        lines.append(f"- `{field}`")
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
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--probe", type=Path, default=DEFAULT_PROBE)
    parser.add_argument("--family", type=str, default="primary_finite")
    parser.add_argument("--row", type=int, default=0)
    parser.add_argument("--parent-chunk", type=int, default=0)
    parser.add_argument("--degree", type=int, default=16)
    parser.add_argument("--denominator", type=int, default=10**18)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    skeleton = load_json(args.skeleton)
    validate(skeleton, schema=SKELETON_SCHEMA, path=args.skeleton)
    worklist = load_json(args.worklist)
    validate(worklist, schema=WORKLIST_SCHEMA, path=args.worklist)
    probe = load_json(args.probe)
    validate(probe, schema=PROBE_SCHEMA, path=args.probe)
    report = build_overlay(
        skeleton=skeleton,
        worklist=worklist,
        probe=probe,
        skeleton_path=args.skeleton,
        worklist_path=args.worklist,
        probe_path=args.probe,
        family_id=args.family,
        row=args.row,
        parent_chunk=args.parent_chunk,
        degree=args.degree,
        denominator=args.denominator,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} candidates={candidates} seeded_candidate_fields={seeded} still_missing={missing}".format(
            status=report["status"],
            candidates=report["counts"]["candidateSubchunks"],
            seeded=report["counts"]["seededCandidateFields"],
            missing=report["counts"]["stillMissingFields"],
        )
    )


if __name__ == "__main__":
    run()
