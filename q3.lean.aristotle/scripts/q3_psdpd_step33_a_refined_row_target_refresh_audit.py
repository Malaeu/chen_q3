#!/usr/bin/env python3
"""Aggregate row-target refresh accounting for refined-subchunk candidates.

This is a fail-closed diagnostic.  It combines existing per-parent remainder
slack audits for one family/row and computes what would happen if the covered
candidate parents replaced the current pointlike parent bounds.  It emits no
Lean and does not mutate parent or row targets.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = ROOT.parent
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

DEFAULT_WORKLIST = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_worklist.json"
DEFAULT_COVERAGE = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_coverage.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_row_target_refresh_audit_primary_finite_row0.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_row_target_refresh_audit_primary_finite_row0.md"
)

WORKLIST_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_worklist.v2"
COVERAGE_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_coverage.v1"
SLACK_AUDIT_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_remainder_slack_audit.v1"


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


def resolve_path(path_text: str) -> Path:
    path = Path(path_text)
    if path.is_absolute():
        return path
    cwd_candidate = Path.cwd() / path
    if cwd_candidate.exists():
        return cwd_candidate
    repo_candidate = REPO_ROOT / path
    if repo_candidate.exists():
        return repo_candidate
    root_candidate = ROOT / path
    if root_candidate.exists():
        return root_candidate
    return cwd_candidate


def parse_decimal(value: Any) -> Decimal:
    return Decimal(str(value))


def decimal_sci(value: Decimal) -> str:
    return format(value, ".18E")


def positive_part(value: Decimal) -> Decimal:
    return value if value > 0 else Decimal(0)


def find_row(worklist: dict[str, Any], *, family_id: str, row_index: int) -> dict[str, Any]:
    for family in worklist.get("families", []):
        if str(family.get("id")) != family_id:
            continue
        for row in family.get("distances", []):
            if int(row.get("row")) == row_index:
                return row
    raise ValueError(f"missing row family={family_id} row={row_index}")


def parent_by_index(row: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {int(parent["parentChunk"]): parent for parent in row.get("parentChunks", [])}


def coverage_candidate_entries(
    coverage: dict[str, Any], *, family_id: str, row_index: int
) -> list[dict[str, Any]]:
    entries = []
    for entry in coverage.get("candidateParents", []):
        if str(entry.get("family")) != family_id:
            continue
        if int(entry.get("row")) != row_index:
            continue
        slack = entry.get("slackAudit")
        if not isinstance(slack, dict) or not slack.get("path"):
            continue
        entries.append(entry)
    entries.sort(key=lambda item: int(item["parentChunk"]))
    return entries


def build_report(
    *,
    worklist_path: Path,
    coverage_path: Path,
    family_id: str,
    row_index: int,
) -> dict[str, Any]:
    worklist = load_json(worklist_path)
    validate_schema(worklist, path=worklist_path, schema=WORKLIST_SCHEMA)
    coverage = load_json(coverage_path)
    validate_schema(coverage, path=coverage_path, schema=COVERAGE_SCHEMA)

    row = find_row(worklist, family_id=family_id, row_index=row_index)
    parents = parent_by_index(row)

    target_lower = parse_decimal(row["targetLower"])
    target_upper = parse_decimal(row["targetUpper"])
    row_lower_before = sum(
        parse_decimal(parent["parentLower"]) for parent in row.get("parentChunks", [])
    )
    row_upper_before = sum(
        parse_decimal(parent["parentUpper"]) for parent in row.get("parentChunks", [])
    )

    row_lower_after = row_lower_before
    row_upper_after = row_upper_before
    parent_reports = []
    total_derivative_failures = 0
    slack_fit_parents = 0

    for entry in coverage_candidate_entries(coverage, family_id=family_id, row_index=row_index):
        parent_index = int(entry["parentChunk"])
        parent = parents.get(parent_index)
        if parent is None:
            raise ValueError(
                f"coverage references missing parent family={family_id} "
                f"row={row_index} parent={parent_index}"
            )

        slack_path = resolve_path(str(entry["slackAudit"]["path"]))
        slack_audit = load_json(slack_path)
        validate_schema(slack_audit, path=slack_path, schema=SLACK_AUDIT_SCHEMA)

        parent_accounting = slack_audit["parentAccounting"]
        current_lower = parse_decimal(parent["parentLower"])
        current_upper = parse_decimal(parent["parentUpper"])
        adjusted_lower = parse_decimal(parent_accounting["adjustedLowerSum"])
        adjusted_upper = parse_decimal(parent_accounting["adjustedUpperSum"])
        lower_delta = adjusted_lower - current_lower
        upper_delta = adjusted_upper - current_upper

        row_lower_after += lower_delta
        row_upper_after += upper_delta
        total_derivative_failures += int(
            slack_audit.get("counts", {}).get("derivativeFailuresNeedingSlack", 0)
        )
        if bool(entry["slackAudit"].get("slackFits")):
            slack_fit_parents += 1

        parent_reports.append(
            {
                "parentChunk": parent_index,
                "left": parent.get("left"),
                "right": parent.get("right"),
                "split": entry.get("split"),
                "subchunks": entry.get("subchunks"),
                "slackAudit": str(slack_path),
                "slackStatus": slack_audit["status"],
                "slackFitsCurrentBounds": bool(entry["slackAudit"].get("slackFits")),
                "derivativeFailuresNeedingSlack": int(
                    slack_audit.get("counts", {}).get(
                        "derivativeFailuresNeedingSlack", 0
                    )
                ),
                "currentParentLower": decimal_sci(current_lower),
                "currentParentUpper": decimal_sci(current_upper),
                "adjustedParentLower": decimal_sci(adjusted_lower),
                "adjustedParentUpper": decimal_sci(adjusted_upper),
                "lowerDeltaIfReplaced": decimal_sci(lower_delta),
                "upperDeltaIfReplaced": decimal_sci(upper_delta),
                "adjustedParentLowerSlack": parent_accounting[
                    "adjustedParentLowerSlack"
                ],
                "adjustedParentUpperSlack": parent_accounting[
                    "adjustedParentUpperSlack"
                ],
                "totalExtraRemainderNeeded": parent_accounting[
                    "totalExtraRemainderNeeded"
                ],
            }
        )

    row_lower_slack_before = row_lower_before - target_lower
    row_upper_slack_before = target_upper - row_upper_before
    row_lower_slack_after = row_lower_after - target_lower
    row_upper_slack_after = target_upper - row_upper_after
    required_lower_target_decrease = positive_part(-row_lower_slack_after)
    required_upper_target_increase = positive_part(-row_upper_slack_after)
    refreshed_target_lower = target_lower - required_lower_target_decrease
    refreshed_target_upper = target_upper + required_upper_target_increase

    status = (
        "covered_candidate_parent_replacements_fit_current_row_targets"
        if required_lower_target_decrease == 0 and required_upper_target_increase == 0
        else "row_target_refresh_required_for_covered_candidate_parents"
    )

    return {
        "schema": "q3_psdpd_step33_a_refined_row_target_refresh_audit.v1",
        "status": status,
        "meaning": (
            "Fail-closed aggregate row accounting for currently slack-audited "
            "candidate parents.  This is not Lean proof data and does not "
            "mutate parent or row targets."
        ),
        "worklist": str(worklist_path),
        "coverage": str(coverage_path),
        "family": family_id,
        "row": row_index,
        "counts": {
            "rowParentChunks": len(row.get("parentChunks", [])),
            "coveredCandidateParents": len(parent_reports),
            "slackFitParents": slack_fit_parents,
            "derivativeFailuresNeedingSlack": total_derivative_failures,
            "proofSafeClosedFields": 0,
        },
        "rowAccounting": {
            "targetLowerBefore": row["targetLower"],
            "targetUpperBefore": row["targetUpper"],
            "rowParentLowerSumBefore": decimal_sci(row_lower_before),
            "rowParentUpperSumBefore": decimal_sci(row_upper_before),
            "rowLowerSlackBefore": decimal_sci(row_lower_slack_before),
            "rowUpperSlackBefore": decimal_sci(row_upper_slack_before),
            "rowParentLowerSumAfterReplacingCoveredParents": decimal_sci(
                row_lower_after
            ),
            "rowParentUpperSumAfterReplacingCoveredParents": decimal_sci(
                row_upper_after
            ),
            "rowLowerSlackAfterReplacingCoveredParents": decimal_sci(
                row_lower_slack_after
            ),
            "rowUpperSlackAfterReplacingCoveredParents": decimal_sci(
                row_upper_slack_after
            ),
            "requiredLowerTargetDecrease": decimal_sci(
                required_lower_target_decrease
            ),
            "requiredUpperTargetIncrease": decimal_sci(
                required_upper_target_increase
            ),
            "minimalRefreshedTargetLower": decimal_sci(refreshed_target_lower),
            "minimalRefreshedTargetUpper": decimal_sci(refreshed_target_upper),
        },
        "parentReplacements": parent_reports,
        "routeGuard": [
            "aggregate accounting audit only",
            "do not emit Lean from this report",
            "do not mutate parent or row bounds from this report",
            "covered parents only; uncovered parents keep current worklist bounds",
            "if refresh is chosen, prove a local row-target/recenter containment theorem before payload emission",
            "proofSafeClosedFields remains zero",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Refined Row Target Refresh Audit",
        "",
        "Fail-closed aggregate row accounting report.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
        f"- family: `{report['family']}`",
        f"- row: `{report['row']}`",
        "",
        "## Counts",
        "",
        "| item | count |",
        "| --- | ---: |",
    ]
    for key, value in report["counts"].items():
        lines.append(f"| `{key}` | `{value}` |")

    lines.extend(["", "## Row Accounting", "", "| item | value |", "| --- | ---: |"])
    for key, value in report["rowAccounting"].items():
        lines.append(f"| `{key}` | `{value}` |")

    lines.extend(
        [
            "",
            "## Covered Parent Replacements",
            "",
            "| parent | interval | current upper | adjusted upper | upper delta | adjusted upper slack | derivative failures |",
            "| ---: | --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for parent in report["parentReplacements"]:
        lines.append(
            f"| {parent['parentChunk']} | `({parent['left']}, {parent['right']}]` | "
            f"`{parent['currentParentUpper']}` | "
            f"`{parent['adjustedParentUpper']}` | "
            f"`{parent['upperDeltaIfReplaced']}` | "
            f"`{parent['adjustedParentUpperSlack']}` | "
            f"`{parent['derivativeFailuresNeedingSlack']}` |"
        )

    lines.extend(["", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--family", default="primary_finite")
    parser.add_argument("--row", type=int, default=0)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    getcontext().prec = 100
    report = build_report(
        worklist_path=args.worklist,
        coverage_path=args.coverage,
        family_id=args.family,
        row_index=args.row,
    )
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} covered_parents={covered} "
        "row_upper_refresh={upper} row_lower_refresh={lower}".format(
            status=report["status"],
            covered=report["counts"]["coveredCandidateParents"],
            upper=report["rowAccounting"]["requiredUpperTargetIncrease"],
            lower=report["rowAccounting"]["requiredLowerTargetDecrease"],
        )
    )


if __name__ == "__main__":
    run()
