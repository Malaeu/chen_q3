#!/usr/bin/env python3
"""Fail-closed Step33A.1-A sub0 asymmetric anchor/curvature audit.

This is a control-plane artifact, not Lean proof data.  It checks whether the
current derivative-bound audit v7 files can supply the live first-subchunk
asymmetric anchor-envelope receiver recorded in worklist v22.

The expected result for the current v7 sources is source-budget failure:
their diagnostic curvature is far above the tiny same-cell budget.  This does
not kill the route, because the zero-curvature asymmetric anchor interval still
has positive rational slack in the current candidate data, and the candidate
data are not proof-grade.
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
    / "a_chunk_taylor_payload_refined_subchunk_direct_proof_input_worklist.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_asymmetric_anchor_curvature_payload.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_asymmetric_anchor_curvature_payload.md"
)

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_proof_input_worklist.v22"
)
DERIVATIVE_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7"
)
OUTPUT_SCHEMA = (
    "q3_psdpd_step33_a1_sub0_asymmetric_anchor_curvature_payload.v1"
)

PAYLOAD_GAP = "STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_PAYLOAD_GAP"
SOURCE_BUDGET_FAIL = (
    "STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_SOURCE_BUDGET_FAIL"
)
CONSTANT_FAIL = "STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_CONSTANT_FAIL"

AUDIT_SOURCES = [
    (
        "denom1e30",
        REQUEST_DIR
        / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30.json",
    ),
    (
        "denom1e30_residualfit",
        REQUEST_DIR
        / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30_residualfit.json",
    ),
    (
        "denom1e30_derivfit",
        REQUEST_DIR
        / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30_derivfit.json",
    ),
]

TARGET = {
    "family": "primary_finite",
    "row": 0,
    "parentChunk": 0,
    "subchunk": 0,
}


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def validate_schema(data: dict[str, Any], *, path: Path, schema: str) -> None:
    found = data.get("schema")
    if found != schema:
        raise ValueError(f"{path}: expected schema {schema!r}, found {found!r}")


def parse_fraction(raw: str | int | None) -> Fraction | None:
    if raw is None:
        return None
    if isinstance(raw, int):
        return Fraction(raw, 1)
    text = str(raw).strip()
    if not text:
        return None
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    if "." in text or "e" in text or "E" in text:
        return Fraction(text)
    return Fraction(int(text), 1)


def format_fraction(value: Fraction | None) -> str | None:
    if value is None:
        return None
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def decimal_string(value: Fraction | None, digits: int = 24) -> str | None:
    if value is None:
        return None
    sign = "-" if value < 0 else ""
    value = abs(value)
    integer = value.numerator // value.denominator
    remainder = value.numerator % value.denominator
    if remainder == 0:
        return f"{sign}{integer}"
    out: list[str] = []
    for _ in range(digits):
        remainder *= 10
        out.append(str(remainder // value.denominator))
        remainder %= value.denominator
    return f"{sign}{integer}.{''.join(out)}"


def find_target_subchunk(worklist: dict[str, Any]) -> dict[str, Any]:
    hits: list[dict[str, Any]] = []
    for parent in worklist.get("parents") or []:
        for item in parent.get("subchunks") or []:
            if all(item.get(key) == value for key, value in TARGET.items()):
                hits.append(item)
    if len(hits) != 1:
        raise ValueError(f"expected one target subchunk, found {len(hits)}")
    return hits[0]


def find_subchunk_item(items: list[Any], subchunk: int) -> dict[str, Any] | None:
    hits = [
        item
        for item in items
        if isinstance(item, dict) and item.get("subchunk") == subchunk
    ]
    if len(hits) > 1:
        raise ValueError(f"expected at most one subchunk {subchunk}, found {len(hits)}")
    return hits[0] if hits else None


def exact_asymmetric_budget(
    *,
    sampled_lower: Fraction,
    sampled_upper: Fraction,
    anchor_lower: Fraction,
    anchor_upper: Fraction,
    curvature: Fraction,
    mesh: Fraction,
) -> dict[str, Any]:
    lower_required = anchor_lower - curvature * mesh
    upper_required = anchor_upper + curvature * mesh
    lower_margin = lower_required - sampled_lower
    upper_margin = sampled_upper - upper_required
    lower_passes = lower_margin >= 0
    upper_passes = upper_margin >= 0

    lower_zero_slack = anchor_lower - sampled_lower
    upper_zero_slack = sampled_upper - anchor_upper
    max_curvature_from_lower = lower_zero_slack / mesh
    max_curvature_from_upper = upper_zero_slack / mesh
    max_allowed_curvature = min(max_curvature_from_lower, max_curvature_from_upper)
    route_death_by_candidate_constants = max_allowed_curvature < 0
    curvature_to_allowed_ratio = (
        None
        if max_allowed_curvature <= 0
        else curvature / max_allowed_curvature
    )

    return {
        "relations": {
            "lower": "sampledLower <= derivAnchorLower - derivSlope * mesh",
            "upper": "derivAnchorUpper + derivSlope * mesh <= sampledUpper",
        },
        "sampledLower": format_fraction(sampled_lower),
        "sampledLowerDecimal": decimal_string(sampled_lower),
        "sampledUpper": format_fraction(sampled_upper),
        "sampledUpperDecimal": decimal_string(sampled_upper),
        "derivAnchorLower": format_fraction(anchor_lower),
        "derivAnchorLowerDecimal": decimal_string(anchor_lower),
        "derivAnchorUpper": format_fraction(anchor_upper),
        "derivAnchorUpperDecimal": decimal_string(anchor_upper),
        "curvature": format_fraction(curvature),
        "curvatureDecimal": decimal_string(curvature),
        "mesh": format_fraction(mesh),
        "lowerRequired": format_fraction(lower_required),
        "lowerRequiredDecimal": decimal_string(lower_required),
        "upperRequired": format_fraction(upper_required),
        "upperRequiredDecimal": decimal_string(upper_required),
        "lowerMargin": format_fraction(lower_margin),
        "lowerMarginDecimal": decimal_string(lower_margin),
        "upperMargin": format_fraction(upper_margin),
        "upperMarginDecimal": decimal_string(upper_margin),
        "lowerPasses": lower_passes,
        "upperPasses": upper_passes,
        "passes": lower_passes and upper_passes,
        "zeroCurvatureSlack": {
            "lower": format_fraction(lower_zero_slack),
            "lowerDecimal": decimal_string(lower_zero_slack),
            "upper": format_fraction(upper_zero_slack),
            "upperDecimal": decimal_string(upper_zero_slack),
        },
        "maxAllowedCurvature": {
            "fromLower": format_fraction(max_curvature_from_lower),
            "fromLowerDecimal": decimal_string(max_curvature_from_lower),
            "fromUpper": format_fraction(max_curvature_from_upper),
            "fromUpperDecimal": decimal_string(max_curvature_from_upper),
            "minimum": format_fraction(max_allowed_curvature),
            "minimumDecimal": decimal_string(max_allowed_curvature),
        },
        "curvatureToAllowedRatio": decimal_string(curvature_to_allowed_ratio),
        "routeDeathByCandidateConstants": route_death_by_candidate_constants,
    }


def audit_source(label: str, path: Path, *, mesh: Fraction) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "label": label,
        "path": str(path),
        "exists": path.exists(),
        "proofUseStatus": "diagnostic_only_not_allowed_as_Lean_payload",
        "rationalAnchorFieldsStatus": "candidate_interval_fields_not_proof_evidence",
        "usableAsAsymmetricAnchorCurvaturePayload": False,
    }
    if not path.exists():
        summary["firstFailure"] = "SOURCE_FILE_MISSING"
        return summary

    data = load_json(path)
    validate_schema(data, path=path, schema=DERIVATIVE_AUDIT_SCHEMA)
    item = find_subchunk_item(data.get("subchunks") or [], 0)
    summary.update(
        {
            "schema": data.get("schema"),
            "status": data.get("status"),
            "counts": data.get("counts") or {},
            "sourceWorklist": data.get("sourceWorklist"),
            "subchunkFound": item is not None,
        }
    )
    if item is None:
        summary["firstFailure"] = "TARGET_SUBCHUNK_MISSING"
        return summary

    sampled_lower = parse_fraction(item.get("sampledDerivLower"))
    sampled_upper = parse_fraction(item.get("sampledDerivUpper"))
    anchor_lower = parse_fraction(item.get("derivAnchorLower"))
    anchor_upper = parse_fraction(item.get("derivAnchorUpper"))
    curvature = parse_fraction(item.get("secondDerivativeSlope"))
    legacy_deriv_slope = parse_fraction(item.get("derivSlope"))

    if (
        sampled_lower is None
        or sampled_upper is None
        or anchor_lower is None
        or anchor_upper is None
        or curvature is None
    ):
        summary["firstFailure"] = "SOURCE_FIELDS_MISSING"
        return summary

    budget = exact_asymmetric_budget(
        sampled_lower=sampled_lower,
        sampled_upper=sampled_upper,
        anchor_lower=anchor_lower,
        anchor_upper=anchor_upper,
        curvature=curvature,
        mesh=mesh,
    )
    summary.update(
        {
            "sourceFieldMapping": {
                "sampledLower": "subchunks[0].sampledDerivLower",
                "sampledUpper": "subchunks[0].sampledDerivUpper",
                "derivAnchorLower": "subchunks[0].derivAnchorLower",
                "derivAnchorUpper": "subchunks[0].derivAnchorUpper",
                "curvature": "subchunks[0].secondDerivativeSlope",
            },
            "decimalOnlyAnchorDiagnostics": {
                "anchorDerivativeResidualLower": item.get(
                    "anchorDerivativeResidualLower"
                ),
                "anchorDerivativeResidualUpper": item.get(
                    "anchorDerivativeResidualUpper"
                ),
                "anchorDerivativeResidualAbsUpper": item.get(
                    "anchorDerivativeResidualAbsUpper"
                ),
                "proofUseStatus": "diagnostic_decimal_only_not_Lean_payload",
            },
            "auditFlags": {
                "secondDerivativeEnvelopePasses": item.get(
                    "secondDerivativeEnvelopePasses"
                ),
                "sampledEnvelopePasses": item.get("sampledEnvelopePasses"),
                "intervalEnvelopePasses": item.get("intervalEnvelopePasses"),
                "jetEnvelopePasses": item.get("jetEnvelopePasses"),
            },
            "legacyDiagnosticDerivSlope": format_fraction(legacy_deriv_slope),
            "legacyDiagnosticDerivSlopeDecimal": decimal_string(legacy_deriv_slope),
            "exactBudget": budget,
            "firstFailure": None if budget["passes"] else SOURCE_BUDGET_FAIL,
        }
    )
    return summary


def build_report(worklist_path: Path) -> dict[str, Any]:
    worklist = load_json(worklist_path)
    validate_schema(worklist, path=worklist_path, schema=WORKLIST_SCHEMA)
    target = find_target_subchunk(worklist)
    norm_work = target.get("hResidualDerivNormWork") or {}
    anchor_work = norm_work.get("firstSubchunkAnchorEnvelopeWork") or {}

    if anchor_work.get("targetGap") != PAYLOAD_GAP:
        raise ValueError(
            f"expected targetGap {PAYLOAD_GAP!r}, found {anchor_work.get('targetGap')!r}"
        )
    mesh = parse_fraction(anchor_work.get("mesh"))
    if mesh is None:
        raise ValueError("target subchunk missing anchor mesh")

    sources = [audit_source(label, path, mesh=mesh) for label, path in AUDIT_SOURCES]
    all_present = all(source.get("exists") and source.get("subchunkFound") for source in sources)
    any_budget_passes = any(((source.get("exactBudget") or {}).get("passes")) is True for source in sources)
    any_candidate_constant_live = any(
        ((source.get("exactBudget") or {}).get("routeDeathByCandidateConstants")) is False
        for source in sources
    )

    if any_budget_passes:
        status = "unexpected_asymmetric_anchor_curvature_source_budget_pass_review_required"
        first_blocker = None
    elif all_present and any_candidate_constant_live:
        status = "asymmetric_anchor_curvature_current_v7_source_budget_fail_not_route_dead"
        first_blocker = SOURCE_BUDGET_FAIL
    elif all_present:
        status = "asymmetric_anchor_curvature_candidate_constants_fail_diagnostic_only"
        first_blocker = SOURCE_BUDGET_FAIL
    else:
        status = "asymmetric_anchor_curvature_source_missing"
        first_blocker = "STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_SOURCE_GAP"

    return {
        "schema": OUTPUT_SCHEMA,
        "status": status,
        "meaning": (
            "Fail-closed audit for the live first-subchunk asymmetric "
            "anchor/curvature receiver.  This checks current derivative_bound_audit.v7 "
            "candidate fields only and does not emit Lean proof data."
        ),
        "target": TARGET,
        "worklistSource": str(worklist_path),
        "worklistSchema": worklist.get("schema"),
        "targetGap": PAYLOAD_GAP,
        "firstBlocker": first_blocker,
        "routeDeathCondition": CONSTANT_FAIL,
        "routeDeathReached": False,
        "routeDeathReachedReason": (
            "not reached: current candidate zero-curvature asymmetric slack is "
            "positive in the denom1e30 source, and these v7 fields are diagnostic "
            "rather than proof-grade constants"
        ),
        "intervalReceiver": anchor_work.get("intervalReceiver"),
        "proofDataReceiver": anchor_work.get("proofDataReceiver"),
        "cell": anchor_work.get("cell"),
        "mesh": format_fraction(mesh),
        "requiredInputs": anchor_work.get("requiredInputs") or [],
        "sourceBudgets": sources,
        "proofSafeClosedFields": 0,
        "outLeanWritten": False,
        "guard": [
            "not Lean proof data",
            "does not emit a Lean payload theorem",
            "uses derivative_bound_audit.v7 only as diagnostic source inventory",
            "rational derivAnchorLower/derivAnchorUpper fields are candidate intervals, not proof evidence",
            "decimal-only anchorDerivativeResidual fields are diagnostics only",
            "current secondDerivativeSlope field is too large for the asymmetric budget",
            "does not kill the checked asymmetric anchor-envelope receiver",
            "does not declare route death; route death requires proof-grade constants",
        ],
        "decision": (
            "The current v7 diagnostic source is not spendable for the live "
            "asymmetric anchor/curvature payload.  The exact zero-curvature "
            "slack is positive for the main source, so the route remains open; "
            "the next proof object must provide proof-grade asymmetric anchor "
            "bounds and a much sharper direct residual curvature bound."
        ),
        "nextRecommendedPatch": (
            "Build a proof-grade generator for asymmetric anchor interval at 0 "
            "and direct residual curvature on [0,1/10], targeting "
            "STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_PAYLOAD_GAP."
        ),
    }


def markdown(report: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Step33A.1-A Sub0 Asymmetric Anchor-Curvature Audit")
    lines.append("")
    lines.append("Fail-closed skeleton.  This is not Lean proof data.")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- schema: `{report['schema']}`")
    lines.append(f"- status: `{report['status']}`")
    lines.append(f"- target gap: `{report['targetGap']}`")
    lines.append(f"- first blocker: `{report['firstBlocker']}`")
    lines.append(f"- route-death condition: `{report['routeDeathCondition']}`")
    lines.append(f"- route death reached: `{report['routeDeathReached']}`")
    lines.append(f"- receiver: `{report['proofDataReceiver']}`")
    lines.append(f"- interval receiver: `{report['intervalReceiver']}`")
    lines.append(f"- cell: `{report['cell']}`")
    lines.append(f"- mesh: `{report['mesh']}`")
    lines.append(f"- proof-safe closed fields: `{report['proofSafeClosedFields']}`")
    lines.append(f"- Lean emitted: `{report['outLeanWritten']}`")
    lines.append("")
    lines.append(report["routeDeathReachedReason"])
    lines.append("")
    lines.append("## Required Inputs")
    lines.append("")
    for item in report["requiredInputs"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Exact Source Budgets")
    lines.append("")
    lines.append(
        "| source | status | curvature | max allowed curvature | ratio | lower slack at 0 | upper slack at 0 | lowerPasses | upperPasses | route-death by candidate constants | firstFailure |"
    )
    lines.append(
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"
    )
    for source in report["sourceBudgets"]:
        budget = source.get("exactBudget") or {}
        zero = budget.get("zeroCurvatureSlack") or {}
        max_allowed = budget.get("maxAllowedCurvature") or {}
        lines.append(
            "| "
            + " | ".join(
                [
                    f"`{source['label']}`",
                    f"`{source.get('status')}`",
                    f"`{budget.get('curvature')}`",
                    f"`{max_allowed.get('minimum')}`",
                    f"`{budget.get('curvatureToAllowedRatio')}`",
                    f"`{zero.get('lower')}`",
                    f"`{zero.get('upper')}`",
                    f"`{budget.get('lowerPasses')}`",
                    f"`{budget.get('upperPasses')}`",
                    f"`{budget.get('routeDeathByCandidateConstants')}`",
                    f"`{source.get('firstFailure')}`",
                ]
            )
            + " |"
        )
    lines.append("")
    lines.append("## Source Notes")
    lines.append("")
    for source in report["sourceBudgets"]:
        lines.append(f"### {source['label']}")
        lines.append("")
        lines.append(f"- path: `{source['path']}`")
        lines.append(f"- exists: `{source['exists']}`")
        lines.append(f"- schema: `{source.get('schema')}`")
        lines.append(f"- status: `{source.get('status')}`")
        lines.append(f"- proof use: `{source['proofUseStatus']}`")
        lines.append(
            f"- rational anchor fields: `{source['rationalAnchorFieldsStatus']}`"
        )
        diagnostics = source.get("decimalOnlyAnchorDiagnostics") or {}
        if diagnostics:
            lines.append(
                "- decimal anchor residual diagnostics: "
                f"`{diagnostics.get('proofUseStatus')}`"
            )
            lines.append(
                "- anchorDerivativeResidualLower: "
                f"`{diagnostics.get('anchorDerivativeResidualLower')}`"
            )
            lines.append(
                "- anchorDerivativeResidualUpper: "
                f"`{diagnostics.get('anchorDerivativeResidualUpper')}`"
            )
        flags = source.get("auditFlags") or {}
        if flags:
            lines.append(f"- sampled envelope passes: `{flags.get('sampledEnvelopePasses')}`")
            lines.append(
                "- second-derivative envelope passes: "
                f"`{flags.get('secondDerivativeEnvelopePasses')}`"
            )
            lines.append(f"- interval envelope passes: `{flags.get('intervalEnvelopePasses')}`")
            lines.append(f"- jet envelope passes: `{flags.get('jetEnvelopePasses')}`")
        if source.get("legacyDiagnosticDerivSlope") is not None:
            lines.append(
                "- legacy diagnostic derivSlope: "
                f"`{source.get('legacyDiagnosticDerivSlope')}`"
            )
        lines.append("")
    lines.append("## Guard")
    lines.append("")
    for item in report["guard"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Decision")
    lines.append("")
    lines.append(report["decision"])
    lines.append("")
    lines.append("## Next Recommended Patch")
    lines.append("")
    lines.append(report["nextRecommendedPatch"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(args.worklist)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    args.out_md.write_text(markdown(report), encoding="utf-8")

    print(
        "status={status} firstBlocker={blocker} routeDeathReached={route_death} out_json={out_json}".format(
            status=report["status"],
            blocker=report["firstBlocker"],
            route_death=report["routeDeathReached"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    main()
