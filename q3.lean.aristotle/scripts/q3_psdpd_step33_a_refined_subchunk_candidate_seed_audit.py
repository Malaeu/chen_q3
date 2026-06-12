#!/usr/bin/env python3
"""Audit seedable proof-data values from selected refined-subchunk candidates.

This is a fail-closed generator control-plane step.  It consumes the default
candidate coverage report, follows the selected candidate overlays, and records
which active `RefinedPayloadFin` value fields can now be seeded from the
tightened candidate policy.

The output is not Lean proof data.  It deliberately keeps proof-safe closure at
zero while `hEnvelope` and `hResidualDerivBoundOnCell` remain missing.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_COVERAGE = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_coverage.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_seed_audit.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_seed_audit.md"
)

COVERAGE_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_coverage.v1"
CANDIDATE_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"

ACTIVE_SEED_FIELDS = ["coeff", "remainder"]
EXTRA_CANDIDATE_FIELDS = [
    "polyLower",
    "polyUpper",
    "polynomialLowerBound",
    "polynomialUpperBound",
    "integralLower",
    "integralUpper",
    "remainderNonneg",
]


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


def present_fields(entry: dict[str, Any], fields: list[str]) -> list[str]:
    return [field for field in fields if entry.get(field) is not None]


def candidate_seed_row(parent: dict[str, Any]) -> dict[str, Any]:
    path = Path(str(parent["path"]))
    if not path.is_absolute():
        path = (ROOT.parent / path).resolve()
        if not path.exists():
            path = (Path.cwd() / str(parent["path"])).resolve()
    candidate = load_json(path)
    validate_schema(candidate, path=path, schema=CANDIDATE_SCHEMA)

    entries = candidate.get("candidates", [])
    if not isinstance(entries, list):
        raise ValueError(f"{path}: expected candidates list")

    eligible = bool(parent.get("residualAuditPassed"))
    seeded_entries = []
    active_seeded = 0
    extra_seeded = 0
    missing_active = []
    for entry in entries:
        active_present = present_fields(entry, ACTIVE_SEED_FIELDS)
        extra_present = present_fields(entry, EXTRA_CANDIDATE_FIELDS)
        if eligible:
            active_seeded += len(active_present)
            extra_seeded += len(extra_present)
        missing = sorted(set(ACTIVE_SEED_FIELDS) - set(active_present))
        if missing:
            missing_active.append(
                {
                    "subchunk": entry.get("subchunk"),
                    "missing": missing,
                }
            )
        seeded_entries.append(
            {
                "subchunk": entry.get("subchunk"),
                "activeSeedFields": active_present,
                "extraCandidateFields": extra_present,
                "remainder": entry.get("remainder"),
                "remainderRefreshReason": entry.get("remainderRefreshReason"),
            }
        )

    return {
        "family": parent.get("family"),
        "row": parent.get("row"),
        "parentChunk": parent.get("parentChunk"),
        "path": str(path),
        "eligibleForSeedAudit": eligible,
        "residualAuditPassed": bool(parent.get("residualAuditPassed")),
        "parentSlackFitsCurrentBounds": bool(parent.get("slackFitsCurrentBounds")),
        "candidateSubchunks": len(entries),
        "activeValueFieldsSeeded": active_seeded,
        "extraCandidateFieldsRecorded": extra_seeded,
        "missingActiveSeedFields": missing_active,
        "remainderRefresh": candidate.get("remainderRefresh"),
        "seededEntriesPreview": seeded_entries[:3],
    }


def build_report(coverage_path: Path) -> dict[str, Any]:
    coverage = load_json(coverage_path)
    validate_schema(coverage, path=coverage_path, schema=COVERAGE_SCHEMA)
    candidate_parents = coverage.get("candidateParents") or []
    if not isinstance(candidate_parents, list):
        raise ValueError(f"{coverage_path}: expected candidateParents list")

    parent_rows = [candidate_seed_row(parent) for parent in candidate_parents]
    eligible_rows = [row for row in parent_rows if row["eligibleForSeedAudit"]]
    active_seeded = sum(row["activeValueFieldsSeeded"] for row in eligible_rows)
    extra_seeded = sum(row["extraCandidateFieldsRecorded"] for row in eligible_rows)
    seeded_subchunks = sum(row["candidateSubchunks"] for row in eligible_rows)

    totals = coverage.get("totals") or {}
    current_missing_sub = int(totals.get("missingSubchunkAnalyticFields", 0))
    current_missing_row = int(totals.get("missingRowAnalyticFields", 0))
    missing_groups = dict(coverage.get("missingGroups") or {})
    taylor_missing = int(missing_groups.get("taylor_model_data", 0))
    missing_groups_after = dict(missing_groups)
    missing_groups_after["taylor_model_data"] = max(0, taylor_missing - active_seeded)

    missing_sub_after = max(0, current_missing_sub - active_seeded)
    missing_total_after = missing_sub_after + current_missing_row
    status = (
        "candidate_value_fields_seeded_no_lean_emitted"
        if active_seeded
        else "no_candidate_value_fields_seeded_no_lean_emitted"
    )

    return {
        "schema": "q3_psdpd_step33_a_refined_subchunk_candidate_seed_audit.v1",
        "status": status,
        "meaning": (
            "Fail-closed audit of selected tightened candidate overlays.  The "
            "active RefinedPayloadFin value fields `coeff` and `remainder` can "
            "be seeded for residual-passing selected parents, but this still closes zero "
            "proof-safe fields until analytic residual envelope and derivative "
            "cell bounds are generated and Lean-checked."
        ),
        "coverage": str(coverage_path),
        "leanLandingSurface": coverage.get("leanLandingSurface"),
        "activeProofDataSchema": coverage.get("activeProofDataSchema"),
        "activeSeedFields": ACTIVE_SEED_FIELDS,
        "extraCandidateFieldsRecorded": EXTRA_CANDIDATE_FIELDS,
        "proofSafeClosedFields": 0,
        "totals": {
            "candidateParents": len(candidate_parents),
            "eligibleCandidateParents": len(eligible_rows),
            "seededSubchunks": seeded_subchunks,
            "activeValueFieldsSeeded": active_seeded,
            "extraCandidateFieldsRecorded": extra_seeded,
            "missingSubchunkAnalyticFieldsBefore": current_missing_sub,
            "missingSubchunkAnalyticFieldsAfterCandidateSeeds": missing_sub_after,
            "missingRowAnalyticFields": current_missing_row,
            "missingTotalAfterCandidateSeeds": missing_total_after,
        },
        "missingGroupsBefore": missing_groups,
        "missingGroupsAfterCandidateSeeds": missing_groups_after,
        "candidateParents": parent_rows,
        "nextProofProducingTarget": [
            "hEnvelope for the eligible covered candidate subchunks",
            "hResidualDerivBoundOnCell for the eligible covered candidate subchunks",
            "row hLowerSum/hUpperSum comparisons after proof-safe subchunk fields exist",
        ],
        "routeGuard": [
            "candidate seed audit only",
            "not Lean proof data",
            "proofSafeClosedFields remains zero",
            "parent point-bound slack is not required for seeding coeff/remainder values",
            "do not emit RefinedPayloadFin while hEnvelope or hResidualDerivBoundOnCell is missing",
            "do not count sampled residual audits as universal analytic proofs",
            "do not mutate CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    totals = report["totals"]
    lines = [
        "# Step33A.1-A Refined Candidate Seed Audit",
        "",
        "Fail-closed audit.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
        f"- Lean landing surface: `{report['leanLandingSurface']}`",
        f"- proof-safe closed fields: `{report['proofSafeClosedFields']}`",
        "",
        "## Seed Counts",
        "",
        "| item | count |",
        "| --- | ---: |",
    ]
    for key in [
        "candidateParents",
        "eligibleCandidateParents",
        "seededSubchunks",
        "activeValueFieldsSeeded",
        "extraCandidateFieldsRecorded",
        "missingSubchunkAnalyticFieldsBefore",
        "missingSubchunkAnalyticFieldsAfterCandidateSeeds",
        "missingRowAnalyticFields",
        "missingTotalAfterCandidateSeeds",
    ]:
        lines.append(f"| `{key}` | `{totals[key]}` |")

    lines.extend(
        [
            "",
            "## Missing Groups After Candidate Seeds",
            "",
            "| group | missing fields |",
            "| --- | ---: |",
        ]
    )
    for group, count in sorted(report["missingGroupsAfterCandidateSeeds"].items()):
        lines.append(f"| `{group}` | `{count}` |")

    lines.extend(["", "## Eligible Parents", ""])
    for parent in report["candidateParents"]:
        lines.append(
            "- "
            f"`{parent['family']} row {parent['row']} parent {parent['parentChunk']}`: "
            f"eligible `{parent['eligibleForSeedAudit']}`, "
            f"subchunks `{parent['candidateSubchunks']}`, "
            f"active value fields seeded `{parent['activeValueFieldsSeeded']}`"
        )

    lines.extend(["", "## Next Proof-Producing Target", ""])
    for item in report["nextProofProducingTarget"]:
        lines.append(f"- {item}")

    lines.extend(["", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(args.coverage)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    totals = report["totals"]
    print(
        "status={status} eligible_parents={parents} seeded_subchunks={subchunks} "
        "active_fields_seeded={fields} missing_after={missing}".format(
            status=report["status"],
            parents=totals["eligibleCandidateParents"],
            subchunks=totals["seededSubchunks"],
            fields=totals["activeValueFieldsSeeded"],
            missing=totals["missingTotalAfterCandidateSeeds"],
        )
    )


if __name__ == "__main__":
    run()
