#!/usr/bin/env python3
"""Build the refined exact-sum row obligation worklist.

This is a fail-closed address/worklist generator for the current Step33A.1-A
raw-Omega refined route.  The refined parent layer now uses exact subchunk
sums, so parent fold comparisons are no longer the active missing group.  The
remaining non-subchunk obligations are row-level `hLowerSum` and `hUpperSum`
facts for the four `RefinedPayloadFin` families.

This file does not emit Lean proof terms.  It records the 184 row obligations
that a future proof-producing generator must fill after the refined subchunk
integral bounds exist.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_REFINED_SKELETON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.json"
)
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_refined_row_sum_worklist.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_refined_row_sum_worklist.md"

REFINED_SKELETON_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_proof_data.v17"
ROW_WORKLIST_SCHEMA = "q3_psdpd_step33_a_refined_row_sum_worklist.v1"

FAMILY_ROW_FIELDS = {
    "primary_finite": {
        "lower": "PrimaryFiniteRefinedFin.hLowerSum",
        "upper": "PrimaryFiniteRefinedFin.hUpperSum",
        "targetLower": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower",
        "targetUpper": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper",
    },
    "primary_tail": {
        "lower": "PrimaryTailRefinedFin.hLowerSum",
        "upper": "PrimaryTailRefinedFin.hUpperSum",
        "targetLower": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower",
        "targetUpper": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper",
    },
    "control_finite": {
        "lower": "ControlFiniteRefinedFin.hLowerSum",
        "upper": "ControlFiniteRefinedFin.hUpperSum",
        "targetLower": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower",
        "targetUpper": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper",
    },
    "control_tail": {
        "lower": "ControlTailRefinedFin.hLowerSum",
        "upper": "ControlTailRefinedFin.hUpperSum",
        "targetLower": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower",
        "targetUpper": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper",
    },
}


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_skeleton(skeleton: dict[str, Any], path: Path) -> None:
    schema = skeleton.get("schema")
    if schema != REFINED_SKELETON_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")
    totals = skeleton.get("totals", {})
    missing_parent = int(totals.get("missingParentAnalyticFields", -1))
    missing_row = int(totals.get("missingRowAnalyticFields", -1))
    if missing_parent != 0:
        raise ValueError(f"{path}: expected exact-sum parent mode, got {missing_parent}")
    if missing_row != 184:
        raise ValueError(f"{path}: expected 184 row obligations, got {missing_row}")


def row_sum_expression(*, side: str) -> str:
    if side == "lower":
        sub_field = "subLower"
    elif side == "upper":
        sub_field = "subUpper"
    else:
        raise ValueError(f"unexpected side {side!r}")
    return (
        "sum parent i in Finset.range 26 of "
        f"sum sub j in Finset.range (parent[i].n) parent[i].{sub_field}(j)"
    )


def family_records_from_compact_skeleton(
    skeleton: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Build address-only row obligations from a compact v17 skeleton.

    The compact skeleton intentionally omits the full family/row/parent tree to
    keep generated artifacts reviewable.  It still carries enough summary data
    to rebuild the row-sum obligation addresses: each family has one lower and
    one upper `RefinedPayloadFin` row obligation per `CoeffIndex23` row.
    """
    families: list[dict[str, Any]] = []
    totals = {
        "families": 0,
        "rows": 0,
        "lowerObligations": 0,
        "upperObligations": 0,
        "totalObligations": 0,
    }

    for summary in skeleton.get("familySummaries", []):
        family_id = str(summary["id"])
        if family_id not in FAMILY_ROW_FIELDS:
            raise ValueError(f"unsupported family {family_id!r}")
        field_config = FAMILY_ROW_FIELDS[family_id]
        family_totals = summary.get("totals", {})
        row_count = int(family_totals.get("rows", 0))
        obligations = []
        for row_index in range(row_count):
            common = {
                "family": family_id,
                "domain": summary.get("domain"),
                "familyKind": summary.get("familyKind"),
                "k": summary.get("k"),
                "row": row_index,
                "distance": None,
                "parentChunkCount": 26,
                "subchunkCount": None,
                "parentBoundsMode": "exact_model_integral_subchunk_sums",
                "compactSkeleton": True,
                "status": "missing_refined_row_sum_proof",
            }
            obligations.append(
                {
                    **common,
                    "side": "lower",
                    "payloadField": field_config["lower"],
                    "targetDeclaration": field_config["targetLower"],
                    "targetValue": None,
                    "sumExpression": row_sum_expression(side="lower"),
                }
            )
            obligations.append(
                {
                    **common,
                    "side": "upper",
                    "payloadField": field_config["upper"],
                    "targetDeclaration": field_config["targetUpper"],
                    "targetValue": None,
                    "sumExpression": row_sum_expression(side="upper"),
                }
            )
            totals["rows"] += 1
            totals["lowerObligations"] += 1
            totals["upperObligations"] += 1
        family_record = {
            "id": family_id,
            "domain": summary.get("domain"),
            "familyKind": summary.get("familyKind"),
            "k": summary.get("k"),
            "rows": row_count,
            "compactSkeleton": True,
            "obligations": obligations,
        }
        family_record["lowerObligations"] = sum(
            1 for item in obligations if item["side"] == "lower"
        )
        family_record["upperObligations"] = sum(
            1 for item in obligations if item["side"] == "upper"
        )
        families.append(family_record)
        totals["families"] += 1

    totals["totalObligations"] = totals["lowerObligations"] + totals["upperObligations"]
    return families, totals


def build_worklist(skeleton: dict[str, Any], *, skeleton_path: Path) -> dict[str, Any]:
    compact_mode = "families" not in skeleton
    if compact_mode:
        families, totals = family_records_from_compact_skeleton(skeleton)
    else:
        families = []
        totals = {
            "families": 0,
            "rows": 0,
            "lowerObligations": 0,
            "upperObligations": 0,
            "totalObligations": 0,
        }

        for family in skeleton.get("families", []):
            family_id = str(family["id"])
            if family_id not in FAMILY_ROW_FIELDS:
                raise ValueError(f"unsupported family {family_id!r}")
            field_config = FAMILY_ROW_FIELDS[family_id]
            obligations = []
            for row in family.get("distances", []):
                row_index = int(row["row"])
                common = {
                    "family": family_id,
                    "domain": family.get("domain"),
                    "familyKind": family.get("familyKind"),
                    "k": family.get("k"),
                    "row": row_index,
                    "distance": row.get("distance"),
                    "parentChunkCount": int(row["parentChunkCount"]),
                    "subchunkCount": int(row["subchunkCount"]),
                    "parentBoundsMode": row.get("parentBoundsMode"),
                    "compactSkeleton": False,
                    "status": "missing_refined_row_sum_proof",
                }
                obligations.append(
                    {
                        **common,
                        "side": "lower",
                        "payloadField": field_config["lower"],
                        "targetDeclaration": field_config["targetLower"],
                        "targetValue": row.get("targetLower"),
                        "sumExpression": row_sum_expression(side="lower"),
                    }
                )
                obligations.append(
                    {
                        **common,
                        "side": "upper",
                        "payloadField": field_config["upper"],
                        "targetDeclaration": field_config["targetUpper"],
                        "targetValue": row.get("targetUpper"),
                        "sumExpression": row_sum_expression(side="upper"),
                    }
                )
                totals["rows"] += 1
                totals["lowerObligations"] += 1
                totals["upperObligations"] += 1
            family_record = {
                "id": family_id,
                "domain": family.get("domain"),
                "familyKind": family.get("familyKind"),
                "k": family.get("k"),
                "rows": len(family.get("distances", [])),
                "compactSkeleton": False,
                "obligations": obligations,
            }
            family_record["lowerObligations"] = sum(
                1 for item in obligations if item["side"] == "lower"
            )
            family_record["upperObligations"] = sum(
                1 for item in obligations if item["side"] == "upper"
            )
            families.append(family_record)
            totals["families"] += 1

        totals["totalObligations"] = (
            totals["lowerObligations"] + totals["upperObligations"]
        )

    return {
        "schema": ROW_WORKLIST_SCHEMA,
        "status": "refined_row_sum_worklist_address_only",
        "meaning": (
            "Address-only refined row-sum worklist for exact-sum parent mode. "
            "This is not Lean proof data and must not be imported as a trusted payload."
        ),
        "skeletonSource": str(skeleton_path),
        "skeletonSchema": skeleton.get("schema"),
        "compactSkeleton": compact_mode,
        "leanLandingSurface": skeleton.get("leanLandingSurface"),
        "parentBoundsMode": "exact_subchunk_sums",
        "totals": totals,
        "routeGuard": [
            "address-only worklist",
            "not Lean proof data",
            "do not use old parent-chunk row_sum_seed as proof for refined exact sums",
            "row proofs depend on generated refined subchunk integralLower/integralUpper data",
            "do not emit RefinedPayloadFin while row or subchunk analytic fields are missing",
        ],
        "families": families,
    }


def render_md(worklist: dict[str, Any]) -> str:
    totals = worklist["totals"]
    lines = [
        "# Step33A.1-A Refined Row-Sum Worklist",
        "",
        "Address-only worklist for the exact-sum parent refined route.",
        "This is not Lean proof data.",
        "",
        "## Summary",
        "",
        f"- schema: `{worklist['schema']}`",
        f"- status: `{worklist['status']}`",
        f"- parent bounds mode: `{worklist['parentBoundsMode']}`",
        f"- families: `{totals['families']}`",
        f"- rows: `{totals['rows']}`",
        f"- lower obligations: `{totals['lowerObligations']}`",
        f"- upper obligations: `{totals['upperObligations']}`",
        f"- total obligations: `{totals['totalObligations']}`",
        "",
        "## Families",
        "",
        "| family | kind | rows | lower | upper |",
        "| --- | --- | ---: | ---: | ---: |",
    ]
    for family in worklist["families"]:
        lines.append(
            f"| `{family['id']}` | `{family['familyKind']}` | "
            f"`{family['rows']}` | `{family['lowerObligations']}` | "
            f"`{family['upperObligations']}` |"
        )
    lines.extend(["", "## Obligation Shape", ""])
    lines.append("- lower: target lower <= nested sum of refined subchunk lower bounds")
    lines.append("- upper: nested sum of refined subchunk upper bounds <= target upper")
    lines.extend(["", "## Guard", ""])
    for item in worklist["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--skeleton", type=Path, default=DEFAULT_REFINED_SKELETON)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    skeleton = load_json(args.skeleton)
    validate_skeleton(skeleton, args.skeleton)
    worklist = build_worklist(skeleton, skeleton_path=args.skeleton)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(worklist, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(worklist), encoding="utf-8")

    totals = worklist["totals"]
    print(
        "status={status} rows={rows} obligations={obligations} out_json={out_json}".format(
            status=worklist["status"],
            rows=totals["rows"],
            obligations=totals["totalObligations"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
