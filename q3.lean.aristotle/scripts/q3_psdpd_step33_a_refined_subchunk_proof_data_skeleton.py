#!/usr/bin/env python3
"""Emit a fail-closed refined-subchunk proof-data skeleton.

This script consumes the refined-subchunk worklist and writes the next
proof-data overlay for the active Step33A.1-A raw-Omega route:

    Refined residual-anchor Taylor/model fields
    -> ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData under each 26-wide parent chunk
    -> RawOmegaAChunkTaylorPayload.RefinedPayloadFin

The output is not a trusted Lean payload.  It deliberately records which
analytic fields are still missing and seeds only structural geometry/proof
templates that must later be checked by Lean.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_worklist.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.md"

WORKLIST_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_worklist.v2"
PROOF_DATA_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_proof_data.v17"

SUBCHUNK_STRUCTURAL_FIELDS = [
    "center",
    "radius",
    "degree",
    "hLU",
    "radiusNonneg",
    "radiusLeft",
    "radiusRight",
    "hProfileInt",
    "hResidualDifferentiable",
    "mesh",
    "anchor",
    "hAnchorIn",
    "hLeftMesh",
    "hRightMesh",
    "derivCellCount",
    "derivCellLeft",
    "derivCellRight",
    "hDerivCoverCells",
]

SUBCHUNK_ANALYTIC_FIELDS = [
    "coeff",
    "remainder",
    "derivSlope",
    "hResidualDerivBoundOnCell",
    "hEnvelope",
]

PARENT_STRUCTURAL_FIELDS = [
    "parentBoundsMode",
    "n",
    "pts",
    "first_eq",
    "last_eq",
    "mono",
    "hProfileInt",
    "subLowerSource",
    "subUpperSource",
    "subCertSource",
]

ROW_ANALYTIC_FIELDS = [
    "hLowerSum",
    "hUpperSum",
]

FIELD_GROUPS = {
    "coeff": "taylor_model_data",
    "remainder": "taylor_model_data",
    "mesh": "residual_anchor_envelope",
    "anchor": "single_anchor_cover_data",
    "derivCellCount": "residual_derivative_finite_cover_data",
    "derivCellLeft": "residual_derivative_finite_cover_data",
    "derivCellRight": "residual_derivative_finite_cover_data",
    "derivSlope": "residual_derivative_cell_slope_data",
    "hAnchorIn": "single_anchor_cover_proofs",
    "hLeftMesh": "single_anchor_cover_proofs",
    "hRightMesh": "single_anchor_cover_proofs",
    "hDerivCoverCells": "residual_derivative_finite_cover_proofs",
    "hResidualDerivBoundOnCell": "residual_derivative_cell_norm_proofs",
    "hEnvelope": "residual_anchor_envelope",
    "hLowerSum": "row_sum_comparisons",
    "hUpperSum": "row_sum_comparisons",
}


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_worklist(worklist: dict[str, Any], path: Path) -> None:
    schema = worklist.get("schema")
    if schema != WORKLIST_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def family_integrable_proof(family: dict[str, Any]) -> str:
    family_id = str(family["id"])
    if family_id.startswith("primary_"):
        lemma = "primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left"
    elif family_id.startswith("control_"):
        lemma = "controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left"
    else:
        raise ValueError(f"unsupported family id {family_id!r}")
    if str(family.get("familyKind")) == "tail":
        hleft = "by norm_num [rawOmegaAFiniteTailCutoff]"
    else:
        hleft = "by norm_num"
    return f"by exact RawOmegaAChunkIntegral.{lemma} n _ _ ({hleft})"


def skeleton_subchunk(
    subchunk: dict[str, Any],
    *,
    degree: int,
    h_profile_int: str,
    include_null_fields: bool,
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "subchunk": int(subchunk["subchunk"]),
        "left": subchunk["left"],
        "right": subchunk["right"],
        "center": subchunk["center"],
        "radius": subchunk["radius"],
        "degree": degree,
        "hLU": "by norm_num",
        "radiusNonneg": "by norm_num",
        "radiusLeft": "by norm_num",
        "radiusRight": "by norm_num",
        "hProfileInt": h_profile_int,
        "hResidualDifferentiable": (
            "by intro eta _heta; exact "
            "RawOmegaATaylorModelCertificate.residual_differentiableAt _ eta"
        ),
        "mesh": subchunk["radius"],
        "anchor": subchunk["center"],
        "hAnchorIn": "by norm_num [Set.mem_Ioc]",
        "hLeftMesh": "by norm_num",
        "hRightMesh": "by norm_num",
        "derivCellCount": 1,
        "derivCellLeft": [subchunk["left"]],
        "derivCellRight": [subchunk["right"]],
        "hDerivCoverCells": (
            "by intro eta heta; exact <| Exists.intro 0 (by simpa using heta)"
        ),
        "subchunkProofShape": (
            "RawOmegaATaylorModelCertificate."
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData"
        ),
        "subchunkWindowReceiver": (
            "RawOmegaATaylorModelCertificate."
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.windowPartBoundsCert"
        ),
        "missing": SUBCHUNK_ANALYTIC_FIELDS[:],
    }
    if include_null_fields:
        for field in SUBCHUNK_ANALYTIC_FIELDS:
            record[field] = None
    return record


def skeleton_parent(
    family: dict[str, Any],
    parent: dict[str, Any],
    *,
    include_null_fields: bool,
) -> dict[str, Any]:
    h_profile_int = family_integrable_proof(family)
    degree = int(parent["subchunks"][0].get("degreeCandidate", 16))
    subchunks = [
        skeleton_subchunk(
            subchunk,
            degree=degree,
            h_profile_int=h_profile_int,
            include_null_fields=include_null_fields,
        )
        for subchunk in parent.get("subchunks", [])
    ]
    points = list(parent.get("points") or [])
    if not points and subchunks:
        points = [subchunks[0]["left"]] + [subchunk["right"] for subchunk in subchunks]
    record: dict[str, Any] = {
        "parentChunk": int(parent["parentChunk"]),
        "left": parent["left"],
        "right": parent["right"],
        "split": int(parent["split"]),
        "step": parent["step"],
        "recordedParentLower": parent.get("parentLower"),
        "recordedParentUpper": parent.get("parentUpper"),
        "parentBoundsMode": "exact_model_integral_subchunk_sums",
        "parentLowerSource": "sum over subchunks[i].cert.lowerModelIntegral",
        "parentUpperSource": "sum over subchunks[i].cert.upperModelIntegral",
        "parentProofShape": (
            "RawOmegaAChunkIntegral."
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData"
        ),
        "parentReceiver": (
            "RawOmegaAChunkIntegral."
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData."
            "toRefinedWindowPartBoundsCert"
        ),
        "n": len(subchunks),
        "pts": points,
        "subchunkCount": len(subchunks),
        "first_eq": "by norm_num",
        "last_eq": "by norm_num",
        "mono": "generated from adjacent point list; must Lean-check per branch",
        "hProfileInt": h_profile_int,
        "subLowerSource": "fun i => (subchunks[i].cert).lowerModelIntegral",
        "subUpperSource": "fun i => (subchunks[i].cert).upperModelIntegral",
        "subCertSource": (
            "fun i => subchunks[i]."
            "derivativeCellSlopeDirectEnvelopeExactIntegralProofData.windowPartBoundsCert"
        ),
        "subchunks": subchunks,
        "missing": [],
    }
    return record


def grouped_counts(counter: Counter[str]) -> dict[str, int]:
    grouped: Counter[str] = Counter()
    for field, count in counter.items():
        grouped[FIELD_GROUPS.get(field, "other")] += count
    return dict(sorted(grouped.items()))


def compact_skeleton(skeleton: dict[str, Any]) -> dict[str, Any]:
    """Drop the full 40k-subchunk tree unless a detailed dump was requested."""
    compact = dict(skeleton)
    families = skeleton.get("families", [])
    summaries = []
    examples = []
    for family in families:
        summary = {
            "id": family.get("id"),
            "domain": family.get("domain"),
            "familyKind": family.get("familyKind"),
            "k": family.get("k"),
            "worklistLeanValidConstructor": family.get("leanValidConstructor"),
            "leanWindowReceiver": (
            "RawOmegaATaylorModelCertificate."
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.windowPartBoundsCert"
        ),
            "hProfileIntTemplate": family.get("hProfileIntTemplate"),
            "totals": family.get("totals"),
        }
        summaries.append(summary)
        rows = family.get("distances", [])
        if rows:
            row = rows[0]
            parents = row.get("parentChunks", [])
            parent = parents[0] if parents else {}
            subchunks = parent.get("subchunks", [])
            examples.append(
                {
                    "family": family.get("id"),
                    "row": row.get("row"),
                    "distance": row.get("distance"),
                    "parentChunk": parent.get("parentChunk"),
                    "parentLeft": parent.get("left"),
                    "parentRight": parent.get("right"),
                    "subchunkCount": parent.get("subchunkCount"),
                    "firstSubchunk": subchunks[0] if subchunks else None,
                }
            )
    compact.pop("families", None)
    compact["familySummaries"] = summaries
    compact["examples"] = examples
    compact["detailMode"] = "compact"
    compact["detailHint"] = (
        "Run this script with --include-detail to emit the full family/row/"
        "parent/subchunk tree.  The default output is compact to keep git "
        "artifacts reviewable."
    )
    return compact


def build_skeleton(worklist: dict[str, Any], *, include_null_fields: bool) -> dict[str, Any]:
    families = []
    missing_subchunk_fields: Counter[str] = Counter()
    missing_row_fields: Counter[str] = Counter()
    totals = {
        "families": 0,
        "rows": 0,
        "parentChunks": 0,
        "subchunks": 0,
        "seededSubchunkStructuralFields": 0,
        "seededParentStructuralFields": 0,
        "missingSubchunkAnalyticFields": 0,
        "missingParentAnalyticFields": 0,
        "missingRowAnalyticFields": 0,
    }

    for family in worklist.get("families", []):
        h_profile_int = family_integrable_proof(family)
        rows = []
        family_totals = {
            "rows": 0,
            "parentChunks": 0,
            "subchunks": 0,
            "missingSubchunkAnalyticFields": 0,
            "missingParentAnalyticFields": 0,
            "missingRowAnalyticFields": 0,
        }
        for row in family.get("distances", []):
            parents = [
                skeleton_parent(
                    family,
                    parent,
                    include_null_fields=include_null_fields,
                )
                for parent in row.get("parentChunks", [])
            ]
            parent_count = len(parents)
            subchunk_count = sum(parent["subchunkCount"] for parent in parents)
            rows.append(
                {
                    "row": int(row["row"]),
                    "distance": row.get("distance"),
                    "targetLower": row.get("targetLower"),
                    "targetUpper": row.get("targetUpper"),
                    "parentChunkCount": parent_count,
                    "subchunkCount": subchunk_count,
                    "parentChunks": parents,
                    "parentBoundsMode": "exact_model_integral_subchunk_sums",
                    "rowLowerSumSource": (
                        "sum over parent exact subchunk lower model integrals"
                    ),
                    "rowUpperSumSource": (
                        "sum over parent exact subchunk upper model integrals"
                    ),
                    "missing": ROW_ANALYTIC_FIELDS[:],
                }
            )
            family_totals["rows"] += 1
            family_totals["parentChunks"] += parent_count
            family_totals["subchunks"] += subchunk_count
            for field in ROW_ANALYTIC_FIELDS:
                missing_row_fields[field] += 1
                family_totals["missingRowAnalyticFields"] = (
                    family_totals.get("missingRowAnalyticFields", 0) + 1
                )
            for _parent in parents:
                for _subchunk in _parent["subchunks"]:
                    for field in SUBCHUNK_ANALYTIC_FIELDS:
                        missing_subchunk_fields[field] += 1
                        family_totals["missingSubchunkAnalyticFields"] += 1
        families.append(
            {
                "id": family["id"],
                "domain": family.get("domain"),
                "familyKind": family.get("familyKind"),
                "k": family.get("k"),
                "worklistLeanValidConstructor": family.get("leanValidConstructor"),
                "leanWindowReceiver": (
                    "RawOmegaATaylorModelCertificate."
                    "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData.windowPartBoundsCert"
                ),
                "hProfileIntTemplate": h_profile_int,
                "totals": family_totals,
                "distances": rows,
            }
        )
        totals["families"] += 1
        totals["rows"] += family_totals["rows"]
        totals["parentChunks"] += family_totals["parentChunks"]
        totals["subchunks"] += family_totals["subchunks"]
        totals["missingSubchunkAnalyticFields"] += family_totals[
            "missingSubchunkAnalyticFields"
        ]
        totals["missingParentAnalyticFields"] += family_totals[
            "missingParentAnalyticFields"
        ]
        totals["missingRowAnalyticFields"] += family_totals[
            "missingRowAnalyticFields"
        ]

    totals["seededSubchunkStructuralFields"] = (
        totals["subchunks"] * len(SUBCHUNK_STRUCTURAL_FIELDS)
    )
    totals["seededParentStructuralFields"] = (
        totals["parentChunks"] * len(PARENT_STRUCTURAL_FIELDS)
    )

    status = (
        "ready_for_refined_lean_emitter"
        if totals["missingSubchunkAnalyticFields"] == 0
        and totals["missingParentAnalyticFields"] == 0
        and totals["missingRowAnalyticFields"] == 0
        else "structural_skeleton_seeded_missing_analytic_fields"
    )
    return {
        "schema": PROOF_DATA_SCHEMA,
        "status": status,
        "meaning": (
            "Fail-closed proof-data skeleton for the refined raw-Omega "
            "Taylor/model route.  The top-level payload remains the 26 parent "
            "chunks; refined subchunks feed residual-anchor parent data below "
            "each parent.  Structural fields are seeded as generator templates; "
            "checked residual differentiability is seeded globally from "
            "RawOmegaATaylorModelCertificate.residual_differentiableAt; "
            "the single residual anchor is seeded at the Taylor center with "
            "mesh equal to the Taylor radius; and the derivative finite cover "
            "is seeded as one derivative cell equal to the refined subchunk.  "
            "Subchunk lower/upper bounds are exact Taylor/model integrals, so "
            "the generator no longer emits hIntegralLower/hIntegralUpper per "
            "refined subchunk.  The anchor residual is folded directly into "
            "the envelope comparison, so the generator no longer emits a "
            "separate sampleRadius datum or hAnchorResidual proof.  "
            "The derivative finite cover uses one derivative norm slope per "
            "cell instead of lower/upper derivative interval endpoints, so "
            "the generator no longer emits derivLower/derivUpper or "
            "hResidualDerivLowerOnCell/hResidualDerivUpperOnCell.  "
            "Other analytic fields remain missing until a proof-producing "
            "residual-anchor generator fills them and Lean checks the result.  Parent "
            "bounds use exact subchunk sums through "
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData."
            "toRefinedWindowPartBoundsCert. "
            "Each subchunk uses "
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData, "
            "so the generator supplies one residual anchor plus mesh coverage "
            "for the value residual as one direct anchor-envelope proof, and "
            "a finite cover of direct residual-derivative norm cell bounds.  "
            "Lean computes the global derivative slope from those per-cell "
            "norm slopes, packages the cell bounds into the "
            "residual-variation premise, then expands the one-anchor packet "
            "to the finite-cover receiver. "
            "The remaining non-subchunk comparisons are row-level hLowerSum and "
            "hUpperSum fields for RefinedPayloadFin."
        ),
        "worklistSchema": worklist.get("schema"),
        "worklistSource": str(DEFAULT_WORKLIST),
        "worklistLeanLandingSurface": worklist.get("leanLandingSurface"),
        "leanLandingSurface": (
            "RawOmegaAChunkTaylorPayload.RefinedPayloadFin"
        ),
        "leanDirectTailWindowInputs": (
            "RawOmegaAChunkTaylorPayload.RefinedPayloadFin."
            "toDirectTailWindowInputs"
        ),
        "leanParentBridge": (
            "RawOmegaAChunkIntegral."
            "ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData."
            "toRefinedWindowPartBoundsCert"
        ),
        "includeNullFields": include_null_fields,
        "subchunkStructuralFields": SUBCHUNK_STRUCTURAL_FIELDS,
        "subchunkAnalyticFields": SUBCHUNK_ANALYTIC_FIELDS,
        "parentStructuralFields": PARENT_STRUCTURAL_FIELDS,
        "parentAnalyticFields": [],
        "rowAnalyticFields": ROW_ANALYTIC_FIELDS,
        "totals": totals,
        "missingSubchunkFields": dict(sorted(missing_subchunk_fields.items())),
        "missingParentFields": {},
        "missingRowFields": dict(sorted(missing_row_fields.items())),
        "missingGroups": grouped_counts(missing_subchunk_fields + missing_row_fields),
        "routeGuard": [
            "not Lean proof data",
            "do not emit RefinedPayloadFin while analytic fields are missing",
            "do not replace the top-level 26 parent chunks by a fully refined payload",
            "parent fold must target RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData",
            "parent bounds build RawOmegaAChunkIntegral.ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralRefinedWindowProofData.toRefinedWindowPartBoundsCert",
            "subchunk proof data must use ResidualAnchorDerivativeCellSlopeDirectEnvelopeExactIntegralChunkProofData",
            "subchunk hIntegralLower/hIntegralUpper are eliminated by exact model integral bounds",
            "subchunk slope/hSlopeNonneg/hDerivLowerAbs/hDerivUpperAbs are eliminated by auto-slope interval packaging",
            "subchunk sampleRadius/hAnchorResidual are eliminated by direct anchor-envelope packaging",
            "subchunk derivLower/derivUpper/hResidualDerivLowerOnCell/hResidualDerivUpperOnCell are eliminated by cell-slope derivative norm packaging",
            "hResidualDifferentiable is a checked structural seed, not generated numeric proof data",
            "single-anchor geometry uses anchor = center and mesh = radius",
            "derivative finite cover geometry uses one cell equal to the refined subchunk",
            "row hLowerSum/hUpperSum comparisons remain required for RefinedPayloadFin",
            "structural proof templates must still be Lean-checked in generated code",
            "do not mutate CSV, ARadius, radius-floor, or LDL data",
            "do not route to H1/PO3 or Q3.Main from this layer",
        ],
        "families": families,
    }


def render_md(skeleton: dict[str, Any]) -> str:
    totals = skeleton["totals"]
    lines = [
        "# Step33A.1-A Residual-Anchor Refined Subchunk Proof-Data Skeleton",
        "",
        "Fail-closed skeleton.  This is not a Lean payload.",
        "",
        "## Verdict",
        "",
        f"- schema: `{skeleton['schema']}`",
        f"- status: `{skeleton['status']}`",
        f"- Lean landing surface: `{skeleton['leanLandingSurface']}`",
        f"- include null fields: `{skeleton['includeNullFields']}`",
        "",
        "## Counts",
        "",
        f"- families: `{totals['families']}`",
        f"- rows: `{totals['rows']}`",
        f"- parent chunks: `{totals['parentChunks']}`",
        f"- refined subchunks: `{totals['subchunks']}`",
        f"- seeded subchunk structural fields: `{totals['seededSubchunkStructuralFields']}`",
        f"- seeded parent structural fields: `{totals['seededParentStructuralFields']}`",
        f"- missing subchunk analytic fields: `{totals['missingSubchunkAnalyticFields']}`",
        f"- missing parent analytic fields: `{totals['missingParentAnalyticFields']}`",
        f"- missing row analytic fields: `{totals['missingRowAnalyticFields']}`",
        "",
        "## Missing Groups",
        "",
        "| group | missing fields |",
        "| --- | ---: |",
    ]
    for group, count in skeleton["missingGroups"].items():
        lines.append(f"| `{group}` | `{count}` |")

    lines.extend(
        [
            "",
            "## Family Counts",
            "",
        "| family | kind | rows | parent chunks | subchunks | missing analytic fields |",
            "| --- | --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for family in skeleton.get("families", skeleton.get("familySummaries", [])):
        ft = family["totals"]
        missing = (
            ft["missingSubchunkAnalyticFields"]
            + ft["missingParentAnalyticFields"]
            + ft["missingRowAnalyticFields"]
        )
        lines.append(
            f"| `{family['id']}` | `{family['familyKind']}` | "
            f"`{ft['rows']}` | `{ft['parentChunks']}` | "
            f"`{ft['subchunks']}` | `{missing}` |"
        )

    lines.extend(["", "## Seeded Structural Fields", ""])
    for field in skeleton["subchunkStructuralFields"]:
        lines.append(f"- subchunk `{field}`")
    for field in skeleton["parentStructuralFields"]:
        lines.append(f"- parent `{field}`")
    for field in skeleton["rowAnalyticFields"]:
        lines.append(f"- row missing `{field}`")

    lines.extend(["", "## Guard", ""])
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
        help="emit missing analytic fields explicitly as null",
    )
    parser.add_argument(
        "--include-detail",
        action="store_true",
        help="emit the full family/row/parent/subchunk tree",
    )
    args = parser.parse_args()

    worklist = load_json(args.worklist)
    validate_worklist(worklist, args.worklist)
    skeleton = build_skeleton(worklist, include_null_fields=args.include_null_fields)
    skeleton["worklistSource"] = str(args.worklist)
    if not args.include_detail:
        skeleton = compact_skeleton(skeleton)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(skeleton, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(skeleton), encoding="utf-8")

    totals = skeleton["totals"]
    print(
        "status={status} families={families} rows={rows} parent_chunks={parents} "
        "subchunks={subchunks} missing_subchunk_analytic_fields={missing_sub} "
        "missing_parent_analytic_fields={missing_parent}".format(
            status=skeleton["status"],
            families=totals["families"],
            rows=totals["rows"],
            parents=totals["parentChunks"],
            subchunks=totals["subchunks"],
            missing_sub=totals["missingSubchunkAnalyticFields"],
            missing_parent=totals["missingParentAnalyticFields"],
        )
    )


if __name__ == "__main__":
    run()
