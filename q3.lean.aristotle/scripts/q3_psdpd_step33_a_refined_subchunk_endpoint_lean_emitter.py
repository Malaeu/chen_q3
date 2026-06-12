#!/usr/bin/env python3
"""Fail-closed Lean emitter report for Step33A.1-A endpoint cert rows.

This script is the front door for the future generated endpoint import:

    endpoint worklist
    -> rawOmegaEndpointClosedFormBounds_generated
    -> rawOmegaEndpointValueDerivIntervalCert_generated
    -> LocalRawOmegaComponentIntervalCert rows

It deliberately does not emit Lean while candidate intervals are not proven
safe or while containment checks fail.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_component_endpoint_worklist.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_endpoint_lean_emitter.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_endpoint_lean_emitter.md"
)
DEFAULT_OUT_LEAN = (
    ROOT
    / "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointGeneratedImport.lean"
)

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.v21"
)
EMITTER_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_endpoint_lean_emitter.v11"
)


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_worklist(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != WORKLIST_SCHEMA:
        raise ValueError(f"{path}: expected schema {WORKLIST_SCHEMA!r}, found {schema!r}")


def parse_fraction(value: Any) -> Fraction:
    return Fraction(str(value))


def row_label(row: dict[str, Any] | None) -> str:
    if row is None:
        return "n/a"
    return (
        f"{row['family']} row={row['row']} parent={row['parentChunk']} "
        f"split={row['split']} sub={row['subchunk']}"
    )


def comparison_margin(row: dict[str, Any], key: str) -> Fraction:
    return parse_fraction(row["containmentComparisons"][key]["margin"])


def build_report(worklist: dict[str, Any], *, out_lean: Path) -> dict[str, Any]:
    rows = [row for row in worklist.get("rows") or [] if isinstance(row, dict)]
    omega_failures = [
        row for row in rows
        if not row["containmentComparisons"]["hOmegaContain"]["passes"]
    ]
    shape_failures = [
        row for row in rows
        if not row["containmentComparisons"]["hShapeSqContain"]["passes"]
    ]
    direct_probe_not_contained = [
        row for row in rows
        if not (row.get("shapeSqDerivativeCornerComparisons") or {}).get(
            "directProbeContained",
            False,
        )
    ]
    proof_safe_closed = int(
        (worklist.get("totals") or {}).get("proofSafeClosedFields") or 0
    )
    if omega_failures or shape_failures:
        status = "blocked_endpoint_candidate_containment_failed_not_lean"
    elif proof_safe_closed == 0:
        status = "blocked_missing_proof_safe_endpoint_bounds"
    else:
        status = "ready_for_future_lean_emission_not_implemented"

    worst_omega = (
        min(rows, key=lambda row: comparison_margin(row, "hOmegaContain"))
        if rows else None
    )
    worst_shape = (
        min(rows, key=lambda row: comparison_margin(row, "hShapeSqContain"))
        if rows else None
    )

    return {
        "schema": EMITTER_SCHEMA,
        "status": status,
        "meaning": (
            "Fail-closed endpoint Lean emitter report.  No Lean file is written "
            "until endpoint rows have proof-safe analytic bounds and all "
            "containment checks pass."
        ),
        "worklist": worklist.get("schema"),
        "targetLeanFile": str(out_lean),
        "generatedTheoremTargets": [
            "rawOmegaEndpointClosedFormBounds_generated",
            "rawShapeSqEndpointBounds_generated",
            "rawOmegaEndpointValueDerivIntervalCert_generated",
        ],
        "receiverTargets": [
            "RawOmegaATaylorModelCertificate.Step22OmegaClosedFormEndpointBoundsCert",
            "RawOmegaATaylorModelCertificate.ShapeSqEndpointBoundsCert",
            "RawOmegaATaylorModelCertificate.ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals",
            "RawOmegaATaylorModelCertificate.ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals_anchorValueBounds",
            "RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert",
            "RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds",
            "RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert.toComponentIntervalCert",
        ],
        "endpointMode": worklist.get("endpointMode"),
        "totals": worklist.get("totals") or {},
        "failures": {
            "omegaContainmentFailures": len(omega_failures),
            "shapeSqContainmentFailures": len(shape_failures),
            "shapeCornerDirectProbeNotContainedAuditOnly": (
                len(direct_probe_not_contained)
            ),
        },
        "worstOmegaRow": worst_omega,
        "worstShapeSqRow": worst_shape,
        "routeFork": {
            "summary": (
                "The active v21 route proves shape endpoint facts for E and "
                "the checked closed-form E' receiver, then derives E^2 "
                "derivative bounds through "
                "ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals."
            ),
            "options": [
                "A. prove the Omega and shape closed-form endpoint packages, then instantiate LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds",
                "A1. for shape anchors, use separate tight E(anchor) bounds plus the generated ShapeSqEndpointBounds_of_value_deriv_anchor_value_bounds wrapper",
                "B. fall back to direct E^2 derivative endpoint facts only if the closed-form E/E' route becomes too expensive",
                "C. add a stronger shape-specific monotonic/sign receiver if direct endpoint facts become too expensive",
            ],
            "codexRecommendation": (
                "Use A plus A1 now: v21 corrected E/E' corner containment "
                "passes for all rows, keeps the shape derivative proof-source "
                "explicit, and lets shape anchors use tight E(anchor) bounds "
                "instead of direct E(anchor)^2 facts."
            ),
        },
        "routeGuard": [
            "do not emit Lean from Arb/acb endpoint candidates",
            "do not call Step33A.1-A or A hbox closed from this report",
            "do not edit A CSV, ARadius, radius-floor, or LDL",
            "do not touch Q3.Main, H1, or PO3",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    totals = report["totals"]
    failures = report["failures"]
    worst_shape = report.get("worstShapeSqRow")
    worst_omega = report.get("worstOmegaRow")
    lines = [
        "# Step33A.1-A Endpoint Lean Emitter Report",
        "",
        f"- Schema: `{report['schema']}`",
        f"- Status: `{report['status']}`",
        f"- Worklist: `{report['worklist']}`",
        f"- Endpoint mode: `{report.get('endpointMode')}`",
        f"- Target Lean file: `{report['targetLeanFile']}`",
        f"- Rows: `{totals.get('rows')}`",
        f"- Endpoint facts open: `{totals.get('componentIntervalDerivativeEndpointFactsOpen')}`",
        f"- Proof-safe closed fields: `{totals.get('proofSafeClosedFields')}`",
        f"- Containment passing: `{totals.get('componentIntervalDerivativeContainmentComparisonsPassing')}/"
        f"{totals.get('componentIntervalDerivativeContainmentComparisons')}`",
        f"- Omega failures: `{failures['omegaContainmentFailures']}`",
        f"- ShapeSq failures: `{failures['shapeSqContainmentFailures']}`",
        f"- Legacy corner direct-probe non-containments audit-only: "
        f"`{failures['shapeCornerDirectProbeNotContainedAuditOnly']}`",
        "",
        "## Theorem Targets",
        "",
    ]
    for target in report["generatedTheoremTargets"]:
        lines.append(f"- `{target}`")
    lines.extend(["", "## Worst Rows", ""])
    if worst_omega is not None:
        comp = worst_omega["containmentComparisons"]["hOmegaContain"]
        lines.extend(
            [
                f"- Worst Omega: `{row_label(worst_omega)}`",
                f"  - margin: `{comp['marginDecimal']}`",
            ]
        )
    if worst_shape is not None:
        comp = worst_shape["containmentComparisons"]["hShapeSqContain"]
        corners = worst_shape.get("shapeSqDerivativeCornerComparisons") or {}
        lines.extend(
            [
                f"- Worst ShapeSq: `{row_label(worst_shape)}`",
                f"  - margin: `{comp['marginDecimal']}`",
                f"  - consumed: `{comp['consumedDecimal']}`",
                f"  - radius: `{comp['radiusDecimal']}`",
                f"  - direct E^2 derivative probe contained by active E/E' corners: "
                f"`{corners.get('directProbeContained')}`",
            ]
        )
    lines.extend(
        [
            "",
            "## Route Fork",
            "",
            report["routeFork"]["summary"],
            "",
        ]
    )
    for option in report["routeFork"]["options"]:
        lines.append(f"- {option}")
    lines.extend(
        [
            "",
            f"Codex recommendation: {report['routeFork']['codexRecommendation']}",
            "",
            "## Guard",
            "",
        ]
    )
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--out-lean", type=Path, default=DEFAULT_OUT_LEAN)
    args = parser.parse_args()

    worklist = load_json(args.worklist)
    validate_worklist(worklist, args.worklist)
    report = build_report(worklist, out_lean=args.out_lean)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    args.out_md.write_text(render_md(report), encoding="utf-8")
    print(
        "endpoint_lean_emitter: "
        f"status={report['status']} "
        f"rows={report['totals'].get('rows')} "
        f"containment={report['totals'].get('componentIntervalDerivativeContainmentComparisonsPassing')}/"
        f"{report['totals'].get('componentIntervalDerivativeContainmentComparisons')} "
        f"out={args.out_json}"
    )


if __name__ == "__main__":
    main()
