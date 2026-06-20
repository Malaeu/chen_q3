#!/usr/bin/env python3
"""Fail-closed Step33A.1-A sub0 anchor/second-derivative payload audit.

This is a control-plane artifact, not Lean proof data.  It checks whether the
current derivative-bound audit v7 can supply the first-subchunk
anchor-abs/second-derivative receiver recorded in worklist v21.

The answer is expected to be fail-closed for the current v7 audit source: the
diagnostic second-derivative slope is far too large for the tiny sampled
derivative interval budget.  This kills only the current diagnostic source, not
the checked anchor-envelope receiver or the broader direct residual route.
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
    REQUEST_DIR / "step33_a1_sub0_anchor_abs_second_deriv_payload.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_anchor_abs_second_deriv_payload.md"
)

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_proof_input_worklist.v21"
)
DERIVATIVE_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7"
)
OUTPUT_SCHEMA = "q3_psdpd_step33_a1_sub0_anchor_abs_second_deriv_payload.v1"

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

LEAN_KILL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_anchorAbsSecondDeriv_budget_impossible"
)


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
    if "E" in text or "e" in text or "." in text:
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


def first_or_value(value: Any) -> Any:
    if isinstance(value, list):
        if len(value) != 1:
            raise ValueError(f"expected one value, found {value!r}")
        return value[0]
    return value


def exact_budget(
    *,
    sampled_lower: Fraction,
    sampled_upper: Fraction,
    deriv_sample_radius: Fraction,
    second_deriv_slope: Fraction,
    mesh: Fraction,
) -> dict[str, Any]:
    lower_required = -deriv_sample_radius - second_deriv_slope * mesh
    upper_required = deriv_sample_radius + second_deriv_slope * mesh
    lower_margin = lower_required - sampled_lower
    upper_margin = sampled_upper - upper_required
    lower_passes = lower_margin >= 0
    upper_passes = upper_margin >= 0
    return {
        "relations": {
            "lower": "sampledLower <= -derivSampleRadius - secondDerivSlope * mesh",
            "upper": "derivSampleRadius + secondDerivSlope * mesh <= sampledUpper",
        },
        "sampledLower": format_fraction(sampled_lower),
        "sampledLowerDecimal": decimal_string(sampled_lower),
        "sampledUpper": format_fraction(sampled_upper),
        "sampledUpperDecimal": decimal_string(sampled_upper),
        "derivSampleRadius": format_fraction(deriv_sample_radius),
        "derivSampleRadiusDecimal": decimal_string(deriv_sample_radius),
        "secondDerivSlope": format_fraction(second_deriv_slope),
        "secondDerivSlopeDecimal": decimal_string(second_deriv_slope),
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
    }


def audit_budget(
    label: str,
    path: Path,
    *,
    mesh: Fraction,
    worklist_sampled_lower: Fraction,
    worklist_sampled_upper: Fraction,
) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "label": label,
        "path": str(path),
        "exists": path.exists(),
        "proofUseStatus": "diagnostic_only_not_allowed_as_Lean_payload",
        "usableAsAnchorAbsSecondDerivPayload": False,
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

    deriv_sample_radius = parse_fraction(item.get("derivSampleRadius"))
    second_deriv_slope = parse_fraction(item.get("secondDerivativeSlope"))
    sampled_lower = parse_fraction(item.get("sampledDerivLower"))
    sampled_upper = parse_fraction(item.get("sampledDerivUpper"))
    legacy_deriv_slope = parse_fraction(item.get("derivSlope"))
    if (
        deriv_sample_radius is None
        or second_deriv_slope is None
        or sampled_lower is None
        or sampled_upper is None
    ):
        summary["firstFailure"] = "SOURCE_FIELDS_MISSING"
        return summary

    budget = exact_budget(
        sampled_lower=sampled_lower,
        sampled_upper=sampled_upper,
        deriv_sample_radius=deriv_sample_radius,
        second_deriv_slope=second_deriv_slope,
        mesh=mesh,
    )
    summary.update(
        {
            "sourceFieldMapping": {
                "derivSampleRadius": "subchunks[0].derivSampleRadius",
                "secondDerivSlope": "subchunks[0].secondDerivativeSlope",
                "sampledLower": "subchunks[0].sampledDerivLower",
                "sampledUpper": "subchunks[0].sampledDerivUpper",
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
            "sampledMatchesWorklist": {
                "lower": sampled_lower == worklist_sampled_lower,
                "upper": sampled_upper == worklist_sampled_upper,
            },
            "exactBudget": budget,
            "firstFailure": (
                None
                if budget["passes"]
                else "STEP33_A1_SUB0_ANCHOR_ABS_SECOND_DERIV_BUDGET_FAIL"
            ),
        }
    )
    return summary


def build_report(worklist_path: Path) -> dict[str, Any]:
    worklist = load_json(worklist_path)
    validate_schema(worklist, path=worklist_path, schema=WORKLIST_SCHEMA)
    target = find_target_subchunk(worklist)
    norm_work = target.get("hResidualDerivNormWork") or {}
    anchor_work = norm_work.get("firstSubchunkAnchorEnvelopeWork") or {}
    seeded = target.get("seededScalars") or {}

    receiver = anchor_work.get("absoluteAnchorProofDataReceiver")
    if not receiver:
        raise ValueError("target subchunk missing absolute anchor receiver")

    mesh = parse_fraction(anchor_work.get("mesh"))
    sampled_lower = parse_fraction(seeded.get("derivLower"))
    sampled_upper = parse_fraction(seeded.get("derivUpper"))
    if mesh is None or sampled_lower is None or sampled_upper is None:
        raise ValueError("target subchunk missing anchor mesh or derivative interval")

    sources = [
        audit_budget(
            label,
            path,
            mesh=mesh,
            worklist_sampled_lower=sampled_lower,
            worklist_sampled_upper=sampled_upper,
        )
        for label, path in AUDIT_SOURCES
    ]
    budget_passes = [
        (((source.get("exactBudget") or {}).get("passes")) is True)
        for source in sources
    ]
    any_budget_passes = any(budget_passes)
    all_present = all(source.get("exists") and source.get("subchunkFound") for source in sources)

    if any_budget_passes:
        status = "unexpected_anchor_abs_second_deriv_budget_pass_review_required"
        first_blocker = None
    elif all_present:
        status = "anchor_abs_second_deriv_budget_fail_from_current_derivative_audit_not_spendable"
        first_blocker = "STEP33_A1_SUB0_ANCHOR_ABS_SECOND_DERIV_BUDGET_FAIL"
    else:
        status = "anchor_abs_second_deriv_source_missing"
        first_blocker = "STEP33_A1_SUB0_ANCHOR_ABS_SECOND_DERIV_SOURCE_GAP"

    return {
        "schema": OUTPUT_SCHEMA,
        "status": status,
        "meaning": (
            "Fail-closed audit for the first-subchunk anchor-abs/second-deriv "
            "receiver.  This checks exact rational budget arithmetic for the "
            "current derivative_bound_audit.v7 source only."
        ),
        "target": TARGET,
        "worklistSource": str(worklist_path),
        "worklistSchema": worklist.get("schema"),
        "receiver": receiver,
        "anchorWorkStatus": anchor_work.get("status"),
        "cell": anchor_work.get("cell"),
        "mesh": format_fraction(mesh),
        "worklistSampledDerivativeInterval": {
            "derivLower": format_fraction(sampled_lower),
            "derivLowerDecimal": decimal_string(sampled_lower),
            "derivUpper": format_fraction(sampled_upper),
            "derivUpperDecimal": decimal_string(sampled_upper),
        },
        "requiredInputs": anchor_work.get("requiredInputs") or [],
        "sourceBudgets": sources,
        "firstBlocker": first_blocker,
        "leanKillTheorem": LEAN_KILL_THEOREM,
        "leanKillTheoremMeaning": (
            "The symmetric anchor-abs budget is impossible for the current "
            "derivSampleRadius even with secondDerivSlope = 0.  This is a "
            "kill theorem for the current symmetric source shape, not a "
            "payload theorem and not a route kill for asymmetric anchors."
        ),
        "proofSafeClosedFields": 0,
        "outLeanWritten": False,
        "guard": [
            "not Lean proof data",
            "does not emit a Lean payload theorem",
            "uses derivative_bound_audit.v7 only as diagnostic source inventory",
            "does not claim |deriv residual 0| bound is proved",
            "does not claim second-derivative envelope is proved",
            "does not kill the checked anchor-envelope receiver",
            "does not kill direct residual or future cancellation-aware routes",
        ],
        "decision": (
            "The current derivative_bound_audit.v7 source is not spendable for "
            "the v21 anchor-abs/second-deriv payload.  Its second-derivative "
            "slope makes both rational budget comparisons fail by many orders "
            "of magnitude."
        ),
        "nextRecommendedPatch": (
            "Build a sharper proof-grade same-cell second-derivative envelope, "
            "or replace this source with a cancellation-aware direct residual "
            "payload; do not spend the current v7 diagnostic audit."
        ),
    }


def markdown(report: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Step33A.1-A Sub0 Anchor-Abs Second-Deriv Payload Audit")
    lines.append("")
    lines.append("Fail-closed skeleton.  This is not Lean proof data.")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- schema: `{report['schema']}`")
    lines.append(f"- status: `{report['status']}`")
    lines.append(f"- receiver: `{report['receiver']}`")
    lines.append(f"- cell: `{report['cell']}`")
    lines.append(f"- mesh: `{report['mesh']}`")
    lines.append(f"- first blocker: `{report['firstBlocker']}`")
    lines.append(f"- Lean kill theorem: `{report['leanKillTheorem']}`")
    lines.append(f"- proof-safe closed fields: `{report['proofSafeClosedFields']}`")
    lines.append(f"- Lean emitted: `{report['outLeanWritten']}`")
    lines.append("")
    lines.append("## Worklist Derivative Interval")
    lines.append("")
    interval = report["worklistSampledDerivativeInterval"]
    lines.append(f"- sampled lower: `{interval['derivLower']}`")
    lines.append(f"- sampled lower decimal: `{interval['derivLowerDecimal']}`")
    lines.append(f"- sampled upper: `{interval['derivUpper']}`")
    lines.append(f"- sampled upper decimal: `{interval['derivUpperDecimal']}`")
    lines.append("")
    lines.append("## Exact Source Budgets")
    lines.append("")
    lines.append(
        "| source | status | secondDerivSlope | upperRequired | sampledUpper | upperPasses | lowerRequired | sampledLower | lowerPasses | firstFailure |"
    )
    lines.append(
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"
    )
    for source in report["sourceBudgets"]:
        budget = source.get("exactBudget") or {}
        lines.append(
            "| "
            + " | ".join(
                [
                    f"`{source['label']}`",
                    f"`{source.get('status')}`",
                    f"`{budget.get('secondDerivSlope')}`",
                    f"`{budget.get('upperRequired')}`",
                    f"`{budget.get('sampledUpper')}`",
                    f"`{budget.get('upperPasses')}`",
                    f"`{budget.get('lowerRequired')}`",
                    f"`{budget.get('sampledLower')}`",
                    f"`{budget.get('lowerPasses')}`",
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
            "- usable as anchor-abs/second-deriv payload: "
            f"`{source['usableAsAnchorAbsSecondDerivPayload']}`"
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
        matches = source.get("sampledMatchesWorklist") or {}
        if matches:
            lines.append(f"- sampled lower matches worklist: `{matches.get('lower')}`")
            lines.append(f"- sampled upper matches worklist: `{matches.get('upper')}`")
        lines.append("")
    lines.append("## Guard")
    lines.append("")
    for item in report["guard"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Lean Kill Theorem")
    lines.append("")
    lines.append(f"`{report['leanKillTheorem']}`")
    lines.append("")
    lines.append(report["leanKillTheoremMeaning"])
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


if __name__ == "__main__":
    main()
