#!/usr/bin/env python3
"""Seed the first v10 refined-subchunk proof-data pilot overlay.

The derivative audit contains useful rational candidates for the active
`ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData` receiver.  This
script turns those candidates into an explicit fail-closed overlay for the
pilot parent chunk:

    primary_finite, row 0, parent chunk 0

It does not claim the sampled derivative bounds as Lean proofs.  It only seeds
the arithmetic and geometry fields that can later be rendered as rational
`norm_num` obligations, and leaves the analytic derivative-cell propositions
as the exact next proof-producing target.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_DERIVATIVE_AUDIT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_pilot_overlay_primary_finite_0_0.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_pilot_overlay_primary_finite_0_0.md"
)

DERIVATIVE_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7"
)
PILOT_OVERLAY_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_pilot_overlay.v3"
)

SEEDED_FIELDS = [
    "remainder",
    "sampleRadius",
    "slope",
    "mesh",
    "anchor",
    "derivCellCount",
    "derivCellLeft",
    "derivCellRight",
    "derivLower",
    "derivUpper",
    "derivAnchor",
    "derivAnchorLower",
    "derivAnchorUpper",
    "derivMesh",
    "derivSlope",
    "hSlopeNonneg",
    "hAnchorIn",
    "hLeftMesh",
    "hRightMesh",
    "hDerivSlopeNonneg",
    "hDerivAnchorIn",
    "hDerivLeftMesh",
    "hDerivRightMesh",
    "hDerivLowerFromAnchor",
    "hDerivUpperFromAnchor",
    "hDerivLowerAbs",
    "hDerivUpperAbs",
    "hEnvelope",
]

REMAINING_ANALYTIC_FIELDS = [
    "coeff",
    "hAnchorResidual",
    "hResidualDifferentiable",
    "hDerivCoverCells",
    "hDerivAnchorLower",
    "hDerivAnchorUpper",
    "hResidualDerivDifferentiableOnCell",
    "hResidualSecondDerivBoundOnCell",
    "hIntegralLower",
    "hIntegralUpper",
]


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_derivative_audit(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != DERIVATIVE_AUDIT_SCHEMA:
        raise ValueError(f"{path}: unexpected schema {schema!r}")


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if text.startswith("-(") and text.endswith(")"):
        return -parse_fraction(text[2:-1])
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def jet_cells(row: dict[str, Any]) -> list[dict[str, Any]]:
    cells = row.get("jetDerivativeIntervalFiniteCoverCells")
    if not isinstance(cells, list) or not cells:
        raise ValueError(
            f"subchunk {row.get('subchunk')}: expected residual-jet cells"
        )
    for cell in cells:
        if not isinstance(cell, dict):
            raise ValueError(f"subchunk {row.get('subchunk')}: malformed cell")
    return cells


def build_subchunk(row: dict[str, Any]) -> dict[str, Any]:
    cells = jet_cells(row)
    if not row.get("jetEnvelopePasses"):
        raise ValueError(f"subchunk {row.get('subchunk')}: jet envelope fails")
    if not row.get("sampledEnvelopePasses"):
        raise ValueError(f"subchunk {row.get('subchunk')}: sampled envelope fails")
    for cell in cells:
        if not cell.get("hDerivLowerAbsWouldPass"):
            raise ValueError(
                f"subchunk {row.get('subchunk')} cell {cell.get('cell')}: "
                "lower abs check fails"
            )
        if not cell.get("hDerivUpperAbsWouldPass"):
            raise ValueError(
                f"subchunk {row.get('subchunk')} cell {cell.get('cell')}: "
                "upper abs check fails"
            )
        deriv_lower = parse_fraction(cell["derivLower"])
        deriv_upper = parse_fraction(cell["derivUpper"])
        deriv_anchor_lower = parse_fraction(cell["derivAnchorLower"])
        deriv_anchor_upper = parse_fraction(cell["derivAnchorUpper"])
        deriv_mesh = parse_fraction(cell["derivMesh"])
        deriv_slope = parse_fraction(cell["derivSlope"])
        if deriv_lower > deriv_anchor_lower - deriv_slope * deriv_mesh:
            raise ValueError(
                f"subchunk {row.get('subchunk')} cell {cell.get('cell')}: "
                "lower anchor comparison fails"
            )
        if deriv_anchor_upper + deriv_slope * deriv_mesh > deriv_upper:
            raise ValueError(
                f"subchunk {row.get('subchunk')} cell {cell.get('cell')}: "
                "upper anchor comparison fails"
            )

    seeded = {
        "remainder": row["currentRemainder"],
        "sampleRadius": row["sampleRadius"],
        "slope": row["jetCoverSlope"],
        "mesh": row["meshCandidate"],
        "anchor": row["center"],
        "derivCellCount": len(cells),
        "derivCellLeft": [cell["left"] for cell in cells],
        "derivCellRight": [cell["right"] for cell in cells],
        "derivLower": [cell["derivLower"] for cell in cells],
        "derivUpper": [cell["derivUpper"] for cell in cells],
        "derivAnchor": [cell["derivAnchor"] for cell in cells],
        "derivAnchorLower": [cell["derivAnchorLower"] for cell in cells],
        "derivAnchorUpper": [cell["derivAnchorUpper"] for cell in cells],
        "derivMesh": [cell["derivMesh"] for cell in cells],
        "derivSlope": [cell["derivSlope"] for cell in cells],
        "hSlopeNonneg": "by norm_num",
        "hAnchorIn": "by norm_num [Set.mem_Ioc]",
        "hLeftMesh": "by norm_num",
        "hRightMesh": "by norm_num",
        "hDerivSlopeNonneg": "by intro i; fin_cases i <;> norm_num",
        "hDerivAnchorIn": "by intro i; fin_cases i <;> norm_num",
        "hDerivLeftMesh": "by intro i; fin_cases i <;> norm_num",
        "hDerivRightMesh": "by intro i; fin_cases i <;> norm_num",
        "hDerivLowerFromAnchor": "by intro i; fin_cases i <;> norm_num",
        "hDerivUpperFromAnchor": "by intro i; fin_cases i <;> norm_num",
        "hDerivLowerAbs": "by intro i; fin_cases i <;> norm_num",
        "hDerivUpperAbs": "by intro i; fin_cases i <;> norm_num",
        "hEnvelope": "by norm_num",
    }
    return {
        "subchunk": int(row["subchunk"]),
        "left": row["left"],
        "right": row["right"],
        "center": row["center"],
        "candidateSource": "derivative_bound_audit.v6.sampled_interval_finite_cover",
        "subchunkProofShape": (
            "RawOmegaATaylorModelCertificate."
            "ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData"
        ),
        "seededFields": seeded,
        "seededFieldNames": SEEDED_FIELDS,
        "remainingAnalyticFields": REMAINING_ANALYTIC_FIELDS,
        "blockedOn": [
            "hDerivCoverCells",
            "hDerivAnchorLower",
            "hDerivAnchorUpper",
            "hResidualSecondDerivBoundOnCell",
        ],
        "proofStatus": (
            "arithmetic_geometry_seeded_derivative_cell_bounds_not_lean_proved"
        ),
    }


def build_overlay(audit: dict[str, Any], audit_path: Path) -> dict[str, Any]:
    rows = audit.get("subchunks")
    if not isinstance(rows, list):
        raise ValueError("derivative audit has no subchunks array")
    subchunks = []
    blocked_subchunks = []
    for row in rows:
        try:
            subchunks.append(build_subchunk(row))
        except ValueError as exc:
            blocked_subchunks.append(
                {
                    "subchunk": row.get("subchunk"),
                    "reason": str(exc),
                    "jetFiniteCoverSplit": row.get("jetFiniteCoverSplit"),
                    "jetFiniteCoverCellCount": row.get("jetFiniteCoverCellCount"),
                    "jetCoverSlopeDecimal": row.get("jetCoverSlopeDecimal"),
                    "jetEnvelopeExcess": row.get("jetEnvelopeExcess"),
                    "sampledEnvelopeExcess": row.get("sampledEnvelopeExcess"),
                    "jetMaxSecondDerivativeResidualAbsUpper": row.get(
                        "jetMaxSecondDerivativeResidualAbsUpper"
                    ),
                }
            )
    status = (
        "pilot_overlay_seeded_residual_jet_scalar_comparisons"
        if not blocked_subchunks
        else "pilot_overlay_blocked_jet_envelope_failed"
    )
    totals = {
        "subchunks": len(subchunks),
        "blockedSubchunks": len(blocked_subchunks),
        "seededFieldsPerSubchunk": len(SEEDED_FIELDS),
        "seededFields": len(subchunks) * len(SEEDED_FIELDS),
        "remainingAnalyticFieldsPerSubchunk": len(REMAINING_ANALYTIC_FIELDS),
        "remainingAnalyticFields": len(subchunks)
        * len(REMAINING_ANALYTIC_FIELDS),
    }
    return {
        "schema": PILOT_OVERLAY_SCHEMA,
        "status": status,
        "meaning": (
            "Fail-closed pilot overlay for the active v10 refined raw-Omega "
            "route.  If residual-jet finite-cover candidates pass the outer "
            "residual envelope, the overlay seeds rational arithmetic and "
            "geometry fields for primary_finite row 0 parent chunk 0.  If "
            "they fail, this file is a blocker report only and is not "
            "Lean-emittable proof data."
        ),
        "sourceDerivativeAudit": str(audit_path),
        "sourceDerivativeAuditStatus": audit.get("status"),
        "pilot": audit.get("pilot"),
        "leanLandingSurface": (
            "RawOmegaAChunkTaylorPayload.ResidualAnchorRefinedPayloadFin"
        ),
        "activeSubchunkProofData": (
            "RawOmegaATaylorModelCertificate."
            "ResidualAnchorDerivativeJetIntervalFiniteCoverChunkProofData"
        ),
        "totals": totals,
        "seededFieldNames": SEEDED_FIELDS,
        "remainingAnalyticFieldNames": REMAINING_ANALYTIC_FIELDS,
        "subchunks": subchunks,
        "blockedSubchunks": blocked_subchunks,
        "routeGuard": [
            "not Lean proof data",
            "do not emit PayloadFin from this overlay alone",
            "sampled derivative lower/upper values are candidates only",
            "anchor-to-cell scalar comparisons are rational checks, not analytic proofs",
            "next Lean work must prove derivative-anchor intervals and second-derivative cell bounds",
            "do not mutate CSV, ARadius, radius-floor, or LDL data",
            "do not route to H1/PO3 or Q3.Main from this layer",
        ],
    }


def render_md(overlay: dict[str, Any]) -> str:
    totals = overlay["totals"]
    lines = [
        "# Step33A.1-A Refined Subchunk Pilot Overlay",
        "",
        "Fail-closed pilot overlay for `primary_finite` row 0 parent chunk 0.",
        "",
        "## Verdict",
        "",
        f"- schema: `{overlay['schema']}`",
        f"- status: `{overlay['status']}`",
        f"- source audit status: `{overlay['sourceDerivativeAuditStatus']}`",
        f"- Lean landing surface: `{overlay['leanLandingSurface']}`",
        f"- active subchunk proof data: `{overlay['activeSubchunkProofData']}`",
        f"- subchunks: `{totals['subchunks']}`",
        f"- blocked subchunks: `{totals['blockedSubchunks']}`",
        f"- seeded fields: `{totals['seededFields']}`",
        f"- remaining analytic fields: `{totals['remainingAnalyticFields']}`",
        "",
        "## Seeded Fields",
        "",
    ]
    for field in overlay["seededFieldNames"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "## Still Missing Per Subchunk", ""])
    for field in overlay["remainingAnalyticFieldNames"]:
        lines.append(f"- `{field}`")
    if overlay.get("blockedSubchunks"):
        lines.extend(
            [
                "",
                "## First Blockers",
                "",
                "| subchunk | reason | split | cells | cover slope | envelope excess | sampled excess |",
                "| ---: | --- | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for blocker in overlay["blockedSubchunks"][:20]:
            lines.append(
                f"| {blocker['subchunk']} | `{blocker['reason']}` | "
                f"`{blocker['jetFiniteCoverSplit']}` | "
                f"`{blocker['jetFiniteCoverCellCount']}` | "
                f"`{blocker['jetCoverSlopeDecimal']}` | "
                f"`{blocker['jetEnvelopeExcess']}` | "
                f"`{blocker['sampledEnvelopeExcess']}` |"
            )
    lines.extend(
        [
            "",
            "## Exact Next Lean Target",
            "",
            "- `hResidualDerivLowerOnCell` / `hResidualDerivUpperOnCell`",
            "- via `hDerivAnchorLower` / `hDerivAnchorUpper`",
            "- via `hResidualSecondDerivBoundOnCell`",
            "- via `hDerivLowerFromAnchor` / `hDerivUpperFromAnchor`",
            "",
            "## Guard",
            "",
        ]
    )
    for item in overlay["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--derivative-audit",
        type=Path,
        default=DEFAULT_DERIVATIVE_AUDIT,
    )
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    audit = load_json(args.derivative_audit)
    validate_derivative_audit(audit, args.derivative_audit)
    overlay = build_overlay(audit, args.derivative_audit)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(overlay, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(overlay), encoding="utf-8")

    totals = overlay["totals"]
    print(
        "status={status} subchunks={subchunks} blocked_subchunks={blocked} "
        "seeded_fields={seeded} remaining_analytic_fields={remaining}".format(
            status=overlay["status"],
            subchunks=totals["subchunks"],
            blocked=totals["blockedSubchunks"],
            seeded=totals["seededFields"],
            remaining=totals["remainingAnalyticFields"],
        )
    )


if __name__ == "__main__":
    run()
