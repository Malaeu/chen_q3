#!/usr/bin/env python3
"""Audit remainder slack against parent and row bounds for refined candidates.

This is a fail-closed accounting report.  It does not emit Lean and it does not
mutate parent or row targets.  It checks whether the current refined-subchunk
candidate integrals, plus derivative-compatible sampled remainder slack, fit
inside the existing parent and row bounds.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

DEFAULT_WORKLIST = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_worklist.json"
DEFAULT_CANDIDATE = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_1.json"
)
DEFAULT_DERIVATIVE_AUDIT = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_1.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_remainder_slack_audit_primary_finite_0_1.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_remainder_slack_audit_primary_finite_0_1.md"
)

WORKLIST_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_worklist.v2"
CANDIDATE_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"
DERIVATIVE_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7"


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_schema(payload: dict[str, Any], *, path: Path, schema: str) -> None:
    found = payload.get("schema")
    if found != schema:
        raise ValueError(f"{path}: expected schema {schema!r}, found {found!r}")


def parse_decimal(value: Any) -> Decimal:
    return Decimal(str(value))


def parse_fraction_decimal(value: Any) -> Decimal:
    text = str(value).strip()
    if "/" in text:
        return Decimal(Fraction(text).numerator) / Decimal(Fraction(text).denominator)
    return Decimal(text)


def decimal_sci(value: Decimal) -> str:
    return format(value, ".18E")


def find_parent(
    worklist: dict[str, Any], *, family_id: str, row_index: int, parent_chunk: int
) -> tuple[dict[str, Any], dict[str, Any]]:
    for family in worklist.get("families", []):
        if str(family.get("id")) != family_id:
            continue
        for row in family.get("distances", []):
            if int(row.get("row")) != row_index:
                continue
            for parent in row.get("parentChunks", []):
                if int(parent.get("parentChunk")) == parent_chunk:
                    return row, parent
    raise ValueError(
        f"missing parent family={family_id} row={row_index} parent={parent_chunk}"
    )


def derivative_rows_by_subchunk(derivative_audit: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {int(row["subchunk"]): row for row in derivative_audit.get("subchunks", [])}


def build_report(
    *,
    worklist_path: Path,
    candidate_path: Path,
    derivative_audit_path: Path,
) -> dict[str, Any]:
    worklist = load_json(worklist_path)
    validate_schema(worklist, path=worklist_path, schema=WORKLIST_SCHEMA)
    candidate = load_json(candidate_path)
    validate_schema(candidate, path=candidate_path, schema=CANDIDATE_SCHEMA)
    derivative_audit = load_json(derivative_audit_path)
    validate_schema(
        derivative_audit, path=derivative_audit_path, schema=DERIVATIVE_SCHEMA
    )

    pilot = candidate["pilot"]
    family_id = str(pilot["family"])
    row_index = int(pilot["row"])
    parent_chunk = int(pilot["parentChunk"])
    row, parent = find_parent(
        worklist, family_id=family_id, row_index=row_index, parent_chunk=parent_chunk
    )
    derivative_rows = derivative_rows_by_subchunk(derivative_audit)

    subchunks = []
    candidate_lower_sum = Decimal(0)
    candidate_upper_sum = Decimal(0)
    adjusted_lower_sum = Decimal(0)
    adjusted_upper_sum = Decimal(0)
    total_extra_remainder = Decimal(0)
    derivative_failures = 0
    derivative_passes_after_slack = 0

    for item in candidate.get("candidates", []):
        subchunk = int(item["subchunk"])
        left = parse_decimal(item["left"])
        right = parse_decimal(item["right"])
        width = right - left
        lower = parse_fraction_decimal(item["integralLower"])
        upper = parse_fraction_decimal(item["integralUpper"])
        candidate_lower_sum += lower
        candidate_upper_sum += upper

        derivative = derivative_rows.get(subchunk, {})
        excess = parse_decimal(derivative.get("sampledEnvelopeExcess", "0"))
        extra = max(Decimal(0), excess)
        if extra > 0:
            derivative_failures += 1
        adjusted_lower = lower - width * extra
        adjusted_upper = upper + width * extra
        adjusted_lower_sum += adjusted_lower
        adjusted_upper_sum += adjusted_upper
        total_extra_remainder += extra
        derivative_passes_after_slack += 1

        subchunks.append(
            {
                "subchunk": subchunk,
                "left": item["left"],
                "right": item["right"],
                "width": decimal_sci(width),
                "currentRemainder": item.get("remainder"),
                "sampledEnvelopeExcess": decimal_sci(excess),
                "extraRemainderNeeded": decimal_sci(extra),
                "currentIntegralLower": decimal_sci(lower),
                "currentIntegralUpper": decimal_sci(upper),
                "adjustedIntegralLower": decimal_sci(adjusted_lower),
                "adjustedIntegralUpper": decimal_sci(adjusted_upper),
            }
        )

    parent_lower = parse_decimal(parent["parentLower"])
    parent_upper = parse_decimal(parent["parentUpper"])
    row_target_lower = parse_decimal(row["targetLower"])
    row_target_upper = parse_decimal(row["targetUpper"])
    row_parent_lower_sum = sum(
        parse_decimal(p["parentLower"]) for p in row.get("parentChunks", [])
    )
    row_parent_upper_sum = sum(
        parse_decimal(p["parentUpper"]) for p in row.get("parentChunks", [])
    )

    current_parent_lower_slack = candidate_lower_sum - parent_lower
    current_parent_upper_slack = parent_upper - candidate_upper_sum
    adjusted_parent_lower_slack = adjusted_lower_sum - parent_lower
    adjusted_parent_upper_slack = parent_upper - adjusted_upper_sum
    row_lower_slack_before = row_parent_lower_sum - row_target_lower
    row_upper_slack_before = row_target_upper - row_parent_upper_sum
    parent_lower_delta = adjusted_lower_sum - parent_lower
    parent_upper_delta = adjusted_upper_sum - parent_upper
    row_lower_slack_after_replacing_parent = (
        row_parent_lower_sum - parent_lower + adjusted_lower_sum - row_target_lower
    )
    row_upper_slack_after_replacing_parent = (
        row_target_upper - (row_parent_upper_sum - parent_upper + adjusted_upper_sum)
    )

    status = (
        "derivative_slack_fits_current_parent_and_row_bounds"
        if adjusted_parent_lower_slack >= 0
        and adjusted_parent_upper_slack >= 0
        and row_lower_slack_after_replacing_parent >= 0
        and row_upper_slack_after_replacing_parent >= 0
        else "derivative_slack_exceeds_current_parent_or_row_bounds"
    )

    return {
        "schema": "q3_psdpd_step33_a_refined_subchunk_remainder_slack_audit.v1",
        "status": status,
        "meaning": (
            "Fail-closed accounting for derivative-compatible sampled "
            "remainder slack.  This is not Lean proof data and does not mutate "
            "parent or row bounds."
        ),
        "worklist": str(worklist_path),
        "candidateOverlay": str(candidate_path),
        "derivativeAudit": str(derivative_audit_path),
        "pilot": {
            "family": family_id,
            "row": row_index,
            "parentChunk": parent_chunk,
            "split": int(pilot["split"]),
            "left": pilot.get("left"),
            "right": pilot.get("right"),
        },
        "counts": {
            "subchunks": len(subchunks),
            "derivativeFailuresNeedingSlack": derivative_failures,
            "proofSafeClosedFields": 0,
        },
        "parentAccounting": {
            "parentLower": parent["parentLower"],
            "parentUpper": parent["parentUpper"],
            "candidateLowerSum": decimal_sci(candidate_lower_sum),
            "candidateUpperSum": decimal_sci(candidate_upper_sum),
            "adjustedLowerSum": decimal_sci(adjusted_lower_sum),
            "adjustedUpperSum": decimal_sci(adjusted_upper_sum),
            "currentParentLowerSlack": decimal_sci(current_parent_lower_slack),
            "currentParentUpperSlack": decimal_sci(current_parent_upper_slack),
            "adjustedParentLowerSlack": decimal_sci(adjusted_parent_lower_slack),
            "adjustedParentUpperSlack": decimal_sci(adjusted_parent_upper_slack),
            "parentLowerDeltaIfReplaced": decimal_sci(parent_lower_delta),
            "parentUpperDeltaIfReplaced": decimal_sci(parent_upper_delta),
            "totalExtraRemainderNeeded": decimal_sci(total_extra_remainder),
        },
        "rowAccounting": {
            "rowTargetLower": row["targetLower"],
            "rowTargetUpper": row["targetUpper"],
            "rowParentLowerSumBefore": decimal_sci(row_parent_lower_sum),
            "rowParentUpperSumBefore": decimal_sci(row_parent_upper_sum),
            "rowLowerSlackBefore": decimal_sci(row_lower_slack_before),
            "rowUpperSlackBefore": decimal_sci(row_upper_slack_before),
            "rowLowerSlackAfterReplacingParent": decimal_sci(
                row_lower_slack_after_replacing_parent
            ),
            "rowUpperSlackAfterReplacingParent": decimal_sci(
                row_upper_slack_after_replacing_parent
            ),
        },
        "subchunks": subchunks,
        "routeGuard": [
            "accounting audit only",
            "do not emit Lean from this report",
            "do not mutate parent or row bounds from this report",
            "if current row slack is insufficient, choose an explicit row-target refresh or global slack policy before payload emission",
            "proofSafeClosedFields remains zero",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Refined Subchunk Remainder Slack Audit",
        "",
        "Fail-closed accounting report.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
        f"- family: `{report['pilot']['family']}`",
        f"- row: `{report['pilot']['row']}`",
        f"- parent chunk: `{report['pilot']['parentChunk']}`",
        f"- split: `{report['pilot']['split']}`",
        "",
        "## Counts",
        "",
        "| item | count |",
        "| --- | ---: |",
    ]
    for key, value in report["counts"].items():
        lines.append(f"| `{key}` | `{value}` |")

    lines.extend(["", "## Parent Accounting", "", "| item | value |", "| --- | ---: |"])
    for key, value in report["parentAccounting"].items():
        lines.append(f"| `{key}` | `{value}` |")

    lines.extend(["", "## Row Accounting", "", "| item | value |", "| --- | ---: |"])
    for key, value in report["rowAccounting"].items():
        lines.append(f"| `{key}` | `{value}` |")

    failures = [
        row for row in report["subchunks"]
        if Decimal(row["extraRemainderNeeded"]) > 0
    ]
    if failures:
        lines.extend(
            [
                "",
                "## Slack-Needing Subchunks",
                "",
                "| subchunk | interval | sampled excess | extra remainder |",
                "| ---: | --- | ---: | ---: |",
            ]
        )
        for row in failures:
            lines.append(
                f"| {row['subchunk']} | `({row['left']}, {row['right']}]` | "
                f"`{row['sampledEnvelopeExcess']}` | "
                f"`{row['extraRemainderNeeded']}` |"
            )

    lines.extend(["", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--candidate", type=Path, default=DEFAULT_CANDIDATE)
    parser.add_argument("--derivative-audit", type=Path, default=DEFAULT_DERIVATIVE_AUDIT)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    getcontext().prec = 100
    report = build_report(
        worklist_path=args.worklist,
        candidate_path=args.candidate,
        derivative_audit_path=args.derivative_audit,
    )
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} derivative_failures={failures} "
        "parent_upper_slack={parent_upper} row_upper_slack={row_upper}".format(
            status=report["status"],
            failures=report["counts"]["derivativeFailuresNeedingSlack"],
            parent_upper=report["parentAccounting"]["adjustedParentUpperSlack"],
            row_upper=report["rowAccounting"]["rowUpperSlackAfterReplacingParent"],
        )
    )


if __name__ == "__main__":
    run()
