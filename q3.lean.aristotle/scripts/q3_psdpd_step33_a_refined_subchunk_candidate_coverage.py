#!/usr/bin/env python3
"""Audit candidate-overlay coverage for the refined raw-Omega subchunk route.

This is a fail-closed coverage report.  It compares the full refined-subchunk
worklist with the currently available candidate overlays and direct-derivative
overlays.  The output is not Lean proof data and must not be imported as a
trusted payload.
"""

from __future__ import annotations

import argparse
import glob
import json
from decimal import Decimal
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

DEFAULT_WORKLIST = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_worklist.json"
DEFAULT_SKELETON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_proof_data_skeleton.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_coverage.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_coverage.md"
)

WORKLIST_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_worklist.v2"
SKELETON_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_proof_data.v17"
CANDIDATE_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"
RESIDUAL_AUDIT_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_rational_residual_audit.v1"
SLACK_AUDIT_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_remainder_slack_audit.v1"
DIRECT_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.v26"


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


def parent_key_from_pilot(pilot: dict[str, Any]) -> tuple[str, int, int]:
    return (
        str(pilot["family"]),
        int(pilot["row"]),
        int(pilot["parentChunk"]),
    )


def collect_parent_totals(worklist: dict[str, Any]) -> dict[tuple[str, int, int], dict[str, Any]]:
    parents: dict[tuple[str, int, int], dict[str, Any]] = {}
    for family in worklist.get("families", []):
        family_id = str(family["id"])
        for row in family.get("distances", []):
            row_index = int(row["row"])
            for parent in row.get("parentChunks", []):
                key = (family_id, row_index, int(parent["parentChunk"]))
                if key in parents:
                    raise ValueError(f"duplicate parent key {key!r}")
                parents[key] = {
                    "family": family_id,
                    "row": row_index,
                    "parentChunk": int(parent["parentChunk"]),
                    "left": parent.get("left"),
                    "right": parent.get("right"),
                    "split": int(parent["split"]),
                    "subchunks": int(parent["subchunkCount"]),
                    "policy": parent.get("policy"),
                }
    return parents


def glob_json(pattern: str) -> list[Path]:
    return [Path(path) for path in sorted(glob.glob(str(REQUEST_DIR / pattern)))]


def path_aliases(path_text: str) -> set[str]:
    path = Path(path_text)
    aliases = {path_text, path.name}
    try:
        aliases.add(str(path.resolve()))
    except OSError:
        pass
    return aliases


def decimal_or_floor(value: Any) -> Decimal:
    if value is None:
        return Decimal("-Infinity")
    return Decimal(str(value))


def load_residual_audits(paths: list[Path]) -> dict[str, dict[str, Any]]:
    audits: dict[str, dict[str, Any]] = {}
    for path in paths:
        payload = load_json(path)
        validate_schema(payload, path=path, schema=RESIDUAL_AUDIT_SCHEMA)
        overlay = str(payload.get("overlay", ""))
        counts = payload.get("counts") or {}
        item = {
            "path": str(path),
            "status": payload.get("status"),
            "passes": int(counts.get("sampledRemainderPasses", 0)),
            "fails": int(counts.get("sampledRemainderFails", 0)),
            "residualAuditPassed": payload.get("status")
            == "sampled_rational_residual_audit_passed_not_proof",
        }
        for alias in path_aliases(overlay):
            audits[alias] = item
    return audits


def load_slack_audits(paths: list[Path]) -> dict[str, dict[str, Any]]:
    audits: dict[str, dict[str, Any]] = {}
    for path in paths:
        payload = load_json(path)
        validate_schema(payload, path=path, schema=SLACK_AUDIT_SCHEMA)
        overlay = str(payload.get("candidateOverlay", ""))
        parent = payload.get("parentAccounting") or {}
        row = payload.get("rowAccounting") or {}
        item = {
            "path": str(path),
            "status": payload.get("status"),
            "slackFits": payload.get("status")
            == "derivative_slack_fits_current_parent_and_row_bounds",
            "adjustedParentUpperSlack": parent.get("adjustedParentUpperSlack"),
            "rowUpperSlackAfterReplacingParent": row.get(
                "rowUpperSlackAfterReplacingParent"
            ),
        }
        for alias in path_aliases(overlay):
            audits[alias] = item
    return audits


def load_candidate_overlays(
    paths: list[Path],
    residual_audits: dict[str, dict[str, Any]],
    slack_audits: dict[str, dict[str, Any]],
) -> dict[tuple[str, int, int], dict[str, Any]]:
    overlays: dict[tuple[str, int, int], dict[str, Any]] = {}
    for path in paths:
        payload = load_json(path)
        validate_schema(payload, path=path, schema=CANDIDATE_SCHEMA)
        pilot = payload.get("pilot") or {}
        key = parent_key_from_pilot(pilot)
        counts = payload.get("counts") or {}
        residual = None
        for alias in path_aliases(str(path)):
            residual = residual_audits.get(alias)
            if residual is not None:
                break
        slack = None
        for alias in path_aliases(str(path)):
            slack = slack_audits.get(alias)
            if slack is not None:
                break
        row_upper_slack = None
        parent_upper_slack = None
        if slack is not None:
            row_upper_slack = slack.get("rowUpperSlackAfterReplacingParent")
            parent_upper_slack = slack.get("adjustedParentUpperSlack")
        item = {
            "path": str(path),
            "status": payload.get("status"),
            "candidateSubchunks": int(counts.get("candidateSubchunks", 0)),
            "seededCandidateFields": int(counts.get("seededCandidateFields", 0)),
            "proofSafeClosedFields": int(counts.get("proofSafeClosedFields", 0)),
            "stillMissingFields": int(counts.get("stillMissingFields", 0)),
            "residualAudit": residual,
            "residualAuditPassed": bool(
                residual and residual.get("residualAuditPassed")
            ),
            "slackAudit": slack,
            "slackFitsCurrentBounds": bool(slack and slack.get("slackFits")),
            "selectionScore": {
                "residualAuditPassed": bool(
                    residual and residual.get("residualAuditPassed")
                ),
                "slackFitsCurrentBounds": bool(slack and slack.get("slackFits")),
                "rowUpperSlackAfterReplacingParent": row_upper_slack,
                "adjustedParentUpperSlack": parent_upper_slack,
            },
        }
        previous = overlays.get(key)
        if previous is None or candidate_is_better(item, previous):
            overlays[key] = item
    return overlays


def candidate_is_better(candidate: dict[str, Any], incumbent: dict[str, Any]) -> bool:
    candidate_score = candidate["selectionScore"]
    incumbent_score = incumbent["selectionScore"]
    return (
        bool(candidate_score["residualAuditPassed"]),
        bool(candidate_score["slackFitsCurrentBounds"]),
        decimal_or_floor(candidate_score["rowUpperSlackAfterReplacingParent"]),
        decimal_or_floor(candidate_score["adjustedParentUpperSlack"]),
        int(candidate["candidateSubchunks"]),
        str(candidate["path"]),
    ) > (
        bool(incumbent_score["residualAuditPassed"]),
        bool(incumbent_score["slackFitsCurrentBounds"]),
        decimal_or_floor(incumbent_score["rowUpperSlackAfterReplacingParent"]),
        decimal_or_floor(incumbent_score["adjustedParentUpperSlack"]),
        int(incumbent["candidateSubchunks"]),
        str(incumbent["path"]),
    )


def load_direct_overlays(
    paths: list[Path],
) -> tuple[dict[tuple[str, int, int], dict[str, Any]], list[dict[str, Any]]]:
    overlays: dict[tuple[str, int, int], dict[str, Any]] = {}
    stale: list[dict[str, Any]] = []
    for path in paths:
        payload = load_json(path)
        schema = payload.get("schema")
        if schema != DIRECT_SCHEMA:
            stale.append({"path": str(path), "schema": schema})
            continue
        pilot = payload.get("pilot") or {}
        key = parent_key_from_pilot(pilot)
        totals = payload.get("totals") or {}
        overlays[key] = {
            "path": str(path),
            "status": payload.get("status"),
            "subchunks": int(totals.get("subchunks", 0)),
            "seededFields": int(totals.get("seededFields", 0)),
            "remainingAnalyticFields": int(totals.get("remainingAnalyticFields", 0)),
            "activeSubchunkProofData": payload.get("activeSubchunkProofData"),
        }
    return overlays, stale


def family_summary(
    parents: dict[tuple[str, int, int], dict[str, Any]],
    candidate_keys: set[tuple[str, int, int]],
    direct_keys: set[tuple[str, int, int]],
) -> list[dict[str, Any]]:
    by_family: dict[str, dict[str, int]] = {}
    for key, parent in parents.items():
        family = parent["family"]
        row = parent["row"]
        item = by_family.setdefault(
            family,
            {
                "rowsSeen": 0,
                "parentChunks": 0,
                "subchunks": 0,
                "candidateParents": 0,
                "candidateSubchunks": 0,
                "directParents": 0,
                "directSubchunks": 0,
            },
        )
        item["parentChunks"] += 1
        item["subchunks"] += parent["subchunks"]
        if key in candidate_keys:
            item["candidateParents"] += 1
            item["candidateSubchunks"] += parent["subchunks"]
        if key in direct_keys:
            item["directParents"] += 1
            item["directSubchunks"] += parent["subchunks"]
        item.setdefault("_rows", set()).add(row)  # type: ignore[attr-defined]

    rows: list[dict[str, Any]] = []
    for family, item in sorted(by_family.items()):
        row_set = item.pop("_rows")  # type: ignore[arg-type]
        item["rowsSeen"] = len(row_set)
        rows.append({"family": family, **item})
    return rows


def first_missing_parents(
    parents: dict[tuple[str, int, int], dict[str, Any]],
    covered: set[tuple[str, int, int]],
    limit: int,
) -> list[dict[str, Any]]:
    missing = []
    for key, parent in parents.items():
        if key in covered:
            continue
        missing.append(parent)
        if len(missing) >= limit:
            break
    return missing


def build_report(
    *,
    worklist_path: Path,
    skeleton_path: Path,
    candidate_paths: list[Path],
    residual_paths: list[Path],
    slack_paths: list[Path],
    direct_paths: list[Path],
    missing_preview: int,
) -> dict[str, Any]:
    worklist = load_json(worklist_path)
    validate_schema(worklist, path=worklist_path, schema=WORKLIST_SCHEMA)
    skeleton = load_json(skeleton_path)
    validate_schema(skeleton, path=skeleton_path, schema=SKELETON_SCHEMA)

    parents = collect_parent_totals(worklist)
    residual_audits = load_residual_audits(residual_paths)
    slack_audits = load_slack_audits(slack_paths)
    candidates = load_candidate_overlays(candidate_paths, residual_audits, slack_audits)
    direct, stale_direct_overlays = load_direct_overlays(direct_paths)
    candidate_keys = set(candidates)
    direct_keys = set(direct)

    candidate_subchunks = sum(item["candidateSubchunks"] for item in candidates.values())
    candidate_residual_files = {
        item["residualAudit"]["path"]
        for item in candidates.values()
        if item.get("residualAudit") is not None
    }
    residual_passed_candidates = sum(
        1 for item in candidates.values() if item["residualAuditPassed"]
    )
    slack_audit_files = {
        item["slackAudit"]["path"]
        for item in candidates.values()
        if item.get("slackAudit") is not None
    }
    slack_fit_candidates = sum(
        1 for item in candidates.values() if item["slackFitsCurrentBounds"]
    )
    direct_subchunks = sum(item["subchunks"] for item in direct.values())
    proof_safe_closed = sum(
        item["proofSafeClosedFields"] for item in candidates.values()
    )
    totals = worklist.get("totals") or {}
    total_parents = int(totals.get("parentChunks", len(parents)))
    total_subchunks = int(totals.get("subchunks", 0))
    missing_groups = skeleton.get("missingGroups") or {}

    return {
        "schema": "q3_psdpd_step33_a_refined_subchunk_candidate_coverage.v1",
        "status": "pilot_only_candidate_coverage_no_lean_emitted",
        "meaning": (
            "Fail-closed coverage audit for refined-subchunk candidate and "
            "direct-derivative overlays.  This is not proof data."
        ),
        "worklist": str(worklist_path),
        "proofDataSkeleton": str(skeleton_path),
        "leanLandingSurface": worklist.get("leanLandingSurface"),
        "activeProofDataSchema": skeleton.get("schema"),
        "activeSubchunkFields": skeleton.get("subchunkAnalyticFields"),
        "missingGroups": missing_groups,
        "totals": {
            "parentChunks": total_parents,
            "refinedSubchunks": total_subchunks,
            "candidateOverlayFiles": len(candidates),
            "residualAuditFiles": len(candidate_residual_files),
            "candidateParents": len(candidate_keys),
            "candidateResidualPassedParents": residual_passed_candidates,
            "slackAuditFiles": len(slack_audit_files),
            "candidateSlackFitParents": slack_fit_candidates,
            "candidateSubchunks": candidate_subchunks,
            "candidateMissingParents": total_parents - len(candidate_keys),
            "candidateMissingSubchunks": total_subchunks - candidate_subchunks,
            "directOverlayFiles": len(direct),
            "staleDirectOverlayFiles": len(stale_direct_overlays),
            "directParents": len(direct_keys),
            "directSubchunks": direct_subchunks,
            "directMissingParents": total_parents - len(direct_keys),
            "directMissingSubchunks": total_subchunks - direct_subchunks,
            "proofSafeClosedFields": proof_safe_closed,
            "missingSubchunkAnalyticFields": int(
                (skeleton.get("totals") or {}).get("missingSubchunkAnalyticFields", 0)
            ),
            "missingRowAnalyticFields": int(
                (skeleton.get("totals") or {}).get("missingRowAnalyticFields", 0)
            ),
        },
        "familySummary": family_summary(parents, candidate_keys, direct_keys),
        "candidateParents": [
            {**parents[key], **candidates[key]} for key in sorted(candidate_keys)
        ],
        "directParents": [
            {**parents[key], **direct[key]} for key in sorted(direct_keys)
        ],
        "staleDirectOverlays": stale_direct_overlays,
        "nextCandidateParents": first_missing_parents(
            parents, candidate_keys, missing_preview
        ),
        "nextDirectParents": first_missing_parents(
            parents, direct_keys, missing_preview
        ),
        "routeGuard": [
            "coverage audit only",
            "do not import this file as Lean proof data",
            "do not write refined generated Lean while missingTotal is nonzero",
            "candidate overlays close zero proof-safe fields",
            "direct overlays still leave hEnvelope and hResidualDerivBoundOnCell open",
            "keep the 26 parent chunks; refined subchunks stay under each parent",
            "no CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3 mutation",
        ],
        "nextGeneratorTarget": [
            "lift candidate-overlay generation from the one pilot parent to shardable parent chunks",
            "for every candidate parent, produce universal hEnvelope and hResidualDerivBoundOnCell proofs",
            "then emit RefinedPayloadFin only after all parent and row comparisons are present",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    totals = report["totals"]
    lines = [
        "# Step33A.1-A Refined Subchunk Candidate Coverage",
        "",
        "Fail-closed coverage audit.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
        f"- Lean landing surface: `{report['leanLandingSurface']}`",
        f"- active proof-data schema: `{report['activeProofDataSchema']}`",
        f"- proof-safe closed fields: `{totals['proofSafeClosedFields']}`",
        "",
        "## Coverage",
        "",
        "| item | count |",
        "| --- | ---: |",
    ]
    for key in [
        "parentChunks",
        "refinedSubchunks",
        "candidateOverlayFiles",
        "residualAuditFiles",
        "candidateParents",
        "candidateResidualPassedParents",
        "slackAuditFiles",
        "candidateSlackFitParents",
        "candidateSubchunks",
        "candidateMissingParents",
        "candidateMissingSubchunks",
        "directOverlayFiles",
        "staleDirectOverlayFiles",
        "directParents",
        "directSubchunks",
        "directMissingParents",
        "directMissingSubchunks",
        "missingSubchunkAnalyticFields",
        "missingRowAnalyticFields",
    ]:
        lines.append(f"| `{key}` | `{totals[key]}` |")

    lines.extend(
        [
            "",
            "## Missing Groups",
            "",
            "| group | missing fields |",
            "| --- | ---: |",
        ]
    )
    for group, count in sorted(report["missingGroups"].items()):
        lines.append(f"| `{group}` | `{count}` |")

    lines.extend(
        [
            "",
            "## Family Summary",
            "",
            "| family | parents | subchunks | candidate parents | direct parents |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for row in report["familySummary"]:
        lines.append(
            f"| `{row['family']}` | `{row['parentChunks']}` | "
            f"`{row['subchunks']}` | `{row['candidateParents']}` | "
            f"`{row['directParents']}` |"
        )

    lines.extend(["", "## Covered Parents", ""])
    if report["candidateParents"]:
        for parent in report["candidateParents"]:
            lines.append(
                "- candidate "
                f"`{parent['family']} row {parent['row']} parent {parent['parentChunk']}`: "
                f"`{parent['candidateSubchunks']}` subchunks, "
                f"`{parent['proofSafeClosedFields']}` proof-safe fields, "
                f"residual audit passed `{parent['residualAuditPassed']}`, "
                f"slack fits current bounds `{parent['slackFitsCurrentBounds']}`"
            )
    else:
        lines.append("- no candidate parents covered")
    if report["directParents"]:
        for parent in report["directParents"]:
            lines.append(
                "- direct "
                f"`{parent['family']} row {parent['row']} parent {parent['parentChunk']}`: "
                f"`{parent['subchunks']}` subchunks, "
                f"`{parent['remainingAnalyticFields']}` analytic fields still open"
            )
    else:
        lines.append("- no direct-derivative parents covered")

    lines.extend(["", "## Next Candidate Parents", ""])
    for parent in report["nextCandidateParents"]:
        lines.append(
            f"- `{parent['family']} row {parent['row']} parent {parent['parentChunk']}` "
            f"split `{parent['split']}` interval `({parent['left']}, {parent['right']}]`"
        )

    lines.extend(["", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Next Generator Target", ""])
    for item in report["nextGeneratorTarget"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--skeleton", type=Path, default=DEFAULT_SKELETON)
    parser.add_argument(
        "--candidate-glob",
        default="a_chunk_taylor_payload_refined_subchunk_candidate_overlay*.json",
    )
    parser.add_argument(
        "--residual-glob",
        default="a_chunk_taylor_payload_refined_subchunk_rational_residual_audit*.json",
    )
    parser.add_argument(
        "--slack-glob",
        default="a_chunk_taylor_payload_refined_subchunk_remainder_slack_audit*.json",
    )
    parser.add_argument(
        "--direct-glob",
        default="a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay*.json",
    )
    parser.add_argument("--missing-preview", type=int, default=8)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(
        worklist_path=args.worklist,
        skeleton_path=args.skeleton,
        candidate_paths=glob_json(args.candidate_glob),
        residual_paths=glob_json(args.residual_glob),
        slack_paths=glob_json(args.slack_glob),
        direct_paths=glob_json(args.direct_glob),
        missing_preview=args.missing_preview,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    totals = report["totals"]
    print(
        "status={status} candidate_subchunks={candidate}/{total} "
        "direct_subchunks={direct}/{total} proof_safe_closed={closed}".format(
            status=report["status"],
            candidate=totals["candidateSubchunks"],
            direct=totals["directSubchunks"],
            total=totals["refinedSubchunks"],
            closed=totals["proofSafeClosedFields"],
        )
    )


if __name__ == "__main__":
    run()
