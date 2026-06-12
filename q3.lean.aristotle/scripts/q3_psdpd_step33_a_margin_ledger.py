#!/usr/bin/env python3
"""Build the Step33A.1-A margin ledger.

This is an accounting script only.  It reads the current raw-Omega Taylor
payload inventory/worklists and writes a JSON/Markdown dashboard.  It does not
mutate proof data, CSV payloads, radius floors, LDL artifacts, or Lean files.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any


SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[1]
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

DEFAULT_INVENTORY = REQUEST_DIR / "a_chunk_taylor_payload_inventory.json"
DEFAULT_WORKLIST = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_worklist.json"
DEFAULT_DIRECT_WORKLIST = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_direct_proof_input_worklist.json"
)
DEFAULT_ROW_SUM_REFRESH = REQUEST_DIR / "a_chunk_taylor_payload_row_sum_target_refresh.json"
DEFAULT_TAIL_WORKLIST = REQUEST_DIR / "a_tail_remainder_worklist.json"
DEFAULT_COVERAGE = REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_coverage.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_margin_ledger.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_margin_ledger.md"

SCHEMA = "q3_psdpd_step33_a_margin_ledger.v1"
LAW = (
    "certified_error_budget(row/chunk/tail) <= "
    "available_cert_slack(row/chunk/tail)"
)
GUARDS = [
    "no CSV mutation",
    "no ARadius mutation",
    "no radius-floor mutation",
    "no LDL mutation",
    "no Q3.Main",
    "no H1/PO3",
    "no proof route change",
    "no Lean theorem weakening",
]


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text())


def decimal_or_none(value: Any) -> Decimal | None:
    if value is None:
        return None
    try:
        return Decimal(str(value))
    except (InvalidOperation, ValueError):
        return None


def decimal_str(value: Decimal | None) -> str | None:
    if value is None:
        return None
    return f"{value:.18E}"


def min_decimal(values: list[Decimal | None]) -> Decimal | None:
    present = [v for v in values if v is not None]
    if not present:
        return None
    return min(present)


def half_width(lower: Decimal | None, upper: Decimal | None) -> Decimal | None:
    if lower is None or upper is None:
        return None
    return abs(upper - lower) / Decimal(2)


def first_subchunk(parent: dict[str, Any]) -> dict[str, Any] | None:
    subchunks = parent.get("subchunks") or []
    if not subchunks:
        return None
    return subchunks[0]


def subchunk_missing_fields(subchunk: dict[str, Any] | None, required: list[str]) -> list[str]:
    if subchunk is None:
        return required
    status = str(subchunk.get("status", ""))
    if "missing_taylor_model" in status:
        return required
    return [field for field in required if field not in subchunk]


def classify_missing_fields(fields: list[str], finite_or_tail: str) -> str:
    field_set = set(fields)
    if finite_or_tail == "tailRemainderAbs":
        return "missing_tailRemainderAbs"
    if field_set & {"productLower", "productUpper", "productLowerBound", "productUpperBound"}:
        return "missing_product_bounds"
    if field_set & {"degree", "coeff", "remainder", "remainderNonneg"}:
        return "missing_taylor_model"
    if field_set & {"polyLower", "polyUpper", "polynomialLowerBound", "polynomialUpperBound"}:
        return "missing_polynomial_value_bounds"
    if field_set & {"diffLower", "diffUpper", "integralLower", "integralUpper"}:
        return "missing_diff_integral_comparisons"
    return "closed"


def row_refresh_index(data: dict[str, Any]) -> dict[tuple[str, int], dict[str, Any]]:
    index: dict[tuple[str, int], dict[str, Any]] = {}
    for family in data.get("families", []):
        family_id = family.get("family")
        for row in family.get("rows", []):
            row_id = row.get("distance_index", row.get("row", row.get("index")))
            if family_id is not None and row_id is not None:
                index[(str(family_id), int(row_id))] = row
    return index


def tail_records(data: dict[str, Any]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for family in data.get("families", []):
        family_id = str(family.get("family"))
        for row in family.get("rows", []):
            present = bool(row.get("proofPresent"))
            status = "closed" if present else "missing_tailRemainderAbs"
            radius = decimal_or_none(row.get("diagnosticRemainderRadius"))
            records.append(
                {
                    "rowId": row.get("index"),
                    "rowClass": family_id,
                    "parentChunk": None,
                    "subchunk": None,
                    "windowLower": row.get("cutoff"),
                    "windowUpper": row.get("tailEnd"),
                    "finiteOrTail": "tailRemainderAbs",
                    "targetLower": None,
                    "targetUpper": None,
                    "generatedLower": None,
                    "generatedUpper": None,
                    "localSlackLower": None,
                    "localSlackUpper": None,
                    "consumedRadius": decimal_str(radius),
                    "remainingSlackLower": None,
                    "remainingSlackUpper": None,
                    "remainingSlackMin": None,
                    "missingFields": [] if present else ["tailRemainderAbs"],
                    "status": status,
                    "fitsGeneratedTailRadius": row.get("fitsGeneratedTailRadius"),
                    "diagnosticExcess": row.get("diagnosticExcess"),
                    "arithmeticRadiusDef": row.get("arithmeticRadiusDef"),
                }
            )
    return records


def direct_parent_index(data: dict[str, Any]) -> dict[tuple[str, int, int], dict[str, Any]]:
    index: dict[tuple[str, int, int], dict[str, Any]] = {}
    for parent in data.get("parents", []):
        family = parent.get("family")
        row = parent.get("row")
        parent_chunk = parent.get("parentChunk")
        if family is None or row is None or parent_chunk is None:
            continue
        index[(str(family), int(row), int(parent_chunk))] = parent
    return index


def direct_worklist_summary(data: dict[str, Any]) -> dict[str, Any]:
    totals = data.get("totals", {})
    parents = data.get("parents", [])
    parent_status_counts = Counter(str(parent.get("status")) for parent in parents)
    parent_status_counts.pop("None", None)
    return {
        "schema": data.get("schema"),
        "status": data.get("status"),
        "leanLandingSurface": data.get("leanLandingSurface"),
        "downstreamLeanLandingSurface": data.get("downstreamLeanLandingSurface"),
        "sourceLeanLandingSurface": data.get("sourceLeanLandingSurface"),
        "parents": len(parents),
        "subchunks": totals.get("subchunks"),
        "proofSafeClosedFields": totals.get("proofSafeClosedFields"),
        "sampledEnvelopePassingSubchunks": totals.get("sampledEnvelopePassingSubchunks"),
        "hRawCenterCoeffAbsFields": totals.get("hRawCenterCoeffAbsFields"),
        "hResidualDerivBoundOnCellFields": totals.get("hResidualDerivBoundOnCellFields"),
        "openArithmeticObligations": totals.get("openArithmeticObligations"),
        "preferredNormRouteOpenAnalyticObligations": totals.get(
            "preferredNormRouteOpenAnalyticObligations"
        ),
        "parentStatusCounts": dict(sorted(parent_status_counts.items())),
    }


@dataclass
class Worst:
    remaining: Decimal | None = None
    record: dict[str, Any] | None = None

    def consider(self, remaining: Decimal | None, record: dict[str, Any]) -> None:
        if remaining is None:
            return
        if self.remaining is None or remaining < self.remaining:
            self.remaining = remaining
            self.record = record


def build_records(
    worklist: dict[str, Any],
    row_refresh: dict[tuple[str, int], dict[str, Any]],
    direct_parents: dict[tuple[str, int, int], dict[str, Any]],
) -> list[dict[str, Any]]:
    required = list(worklist.get("subchunkRequiredFields", []))
    records: list[dict[str, Any]] = []
    for family in worklist.get("families", []):
        family_id = str(family.get("id"))
        finite_or_tail = str(family.get("familyKind"))
        row_class = f"{family_id}:{family.get('domain')}"
        for row in family.get("distances", []):
            row_id = int(row.get("row"))
            refresh = row_refresh.get((family_id, row_id), {})
            row_slack = decimal_or_none(refresh.get("slack_after_suggested_refresh"))
            target_lower = row.get("targetLower") or refresh.get("target_lower")
            target_upper = row.get("targetUpper") or refresh.get("target_upper")
            for parent in row.get("parentChunks", []):
                parent_chunk = parent.get("parentChunk")
                direct_parent = None
                if parent_chunk is not None:
                    direct_parent = direct_parents.get(
                        (family_id, row_id, int(parent_chunk))
                    )
                sub = first_subchunk(parent)
                missing = subchunk_missing_fields(sub, required)
                status = classify_missing_fields(missing, finite_or_tail)

                generated_lower = decimal_or_none(parent.get("parentLower"))
                generated_upper = decimal_or_none(parent.get("parentUpper"))
                consumed_radius = half_width(generated_lower, generated_upper)

                # Parent chunks are additive row contributions, not independent
                # row targets.  Slack failure is only meaningful once proof data
                # exists and an allocated local target is present.  Until then
                # the row-refresh slack is the safe accounting budget.
                remaining = row_slack
                if status == "closed":
                    lower_slack = decimal_or_none(refresh.get("lower_excess"))
                    upper_slack = decimal_or_none(refresh.get("upper_excess"))
                    if lower_slack is not None and lower_slack < 0:
                        status = "failed_lower_slack"
                    elif upper_slack is not None and upper_slack < 0:
                        status = "failed_upper_slack"
                else:
                    lower_slack = None
                    upper_slack = None

                record = {
                    "rowId": row_id,
                    "rowClass": row_class,
                    "parentChunk": parent_chunk,
                    "subchunk": sub.get("subchunk") if sub else None,
                    "windowLower": parent.get("left"),
                    "windowUpper": parent.get("right"),
                    "finiteOrTail": finite_or_tail,
                    "targetLower": target_lower,
                    "targetUpper": target_upper,
                    "generatedLower": parent.get("parentLower"),
                    "generatedUpper": parent.get("parentUpper"),
                    "localSlackLower": decimal_str(lower_slack),
                    "localSlackUpper": decimal_str(upper_slack),
                    "consumedRadius": decimal_str(consumed_radius),
                    "remainingSlackLower": decimal_str(remaining),
                    "remainingSlackUpper": decimal_str(remaining),
                    "remainingSlackMin": decimal_str(remaining),
                    "missingFields": missing,
                    "status": status,
                    "subchunkCount": parent.get("subchunkCount"),
                    "policy": parent.get("policy"),
                    "rowDistance": row.get("distance"),
                    "rowSlackSource": "row_sum_target_refresh"
                    if refresh
                    else "not_serialized_in_refresh",
                    "fitsAfterLocalTargetRefresh": refresh.get("fits_after_local_target_refresh"),
                    "neededTargetRefreshSlack": refresh.get("needed_target_refresh_slack"),
                    "availableTargetRefreshSlack": refresh.get("available_target_refresh_slack"),
                    "activeProofInputCovered": direct_parent is not None,
                    "activeProofInputStatus": None
                    if direct_parent is None
                    else direct_parent.get("status"),
                    "activeProofInputSplit": None
                    if direct_parent is None
                    else direct_parent.get("split"),
                }
                records.append(record)
    return records


def aggregate(
    inventory: dict[str, Any],
    worklist: dict[str, Any],
    direct_worklist: dict[str, Any],
    coverage: dict[str, Any],
    chunk_records: list[dict[str, Any]],
    tail_remainder_records: list[dict[str, Any]],
) -> dict[str, Any]:
    status_counts = Counter(record["status"] for record in chunk_records)
    tail_status_counts = Counter(record["status"] for record in tail_remainder_records)
    required_tail_row_fields = list(inventory.get("required_tail_row_fields", []))
    tail_remainder_required = "tailRemainderAbs" in required_tail_row_fields

    # `a_tail_remainder_worklist` can exist as a historical/diagnostic artifact
    # after the active PayloadFin contract has stopped requiring tail row fields.
    # Active blockers must follow the current inventory contract.
    blocker_counts = Counter(status_counts)
    if tail_remainder_required:
        blocker_counts += tail_status_counts
    blocker_counts.pop("closed", None)

    totals = inventory.get("totals", {})
    total_cells = int(totals.get("chunk_cells", len(chunk_records)) or 0)
    cells_closed = int(totals.get("complete_cells", 0) or 0)
    readiness = Decimal(0)
    if total_cells:
        readiness = Decimal(cells_closed) * Decimal(100) / Decimal(total_cells)

    worst = Worst()
    for record in chunk_records:
        worst.consider(decimal_or_none(record.get("remainingSlackMin")), record)

    finite_error = Decimal(0)
    tail_error = Decimal(0)
    for record in chunk_records:
        radius = decimal_or_none(record.get("consumedRadius"))
        if radius is None:
            continue
        if record.get("finiteOrTail") == "finite":
            finite_error += radius
        else:
            tail_error += radius

    rows_seen = {(r["rowClass"], r["rowId"]) for r in chunk_records}
    closed_rows = defaultdict(int)
    row_cell_counts = defaultdict(int)
    for record in chunk_records:
        key = (record["rowClass"], record["rowId"])
        row_cell_counts[key] += 1
        if record["status"] == "closed":
            closed_rows[key] += 1
    rows_closed = sum(
        1 for key, count in row_cell_counts.items() if closed_rows.get(key, 0) == count
    )

    tail_closed = sum(1 for r in tail_remainder_records if r["status"] == "closed")

    return {
        "totalRows": len(rows_seen),
        "rowsClosed": rows_closed,
        "rowsOpen": len(rows_seen) - rows_closed,
        "totalCells": total_cells,
        "cellsClosed": cells_closed,
        "PayloadFinReadinessPercent": f"{readiness:.6f}",
        "worstRemainingSlack": decimal_str(worst.remaining),
        "worstRow": None if worst.record is None else worst.record.get("rowId"),
        "worstRowClass": None if worst.record is None else worst.record.get("rowClass"),
        "worstParentChunk": None
        if worst.record is None
        else worst.record.get("parentChunk"),
        "worstSubchunk": None if worst.record is None else worst.record.get("subchunk"),
        "totalFiniteError": decimal_str(finite_error),
        "totalTailError": decimal_str(tail_error),
        "tailRemainderAbsClosed": tail_closed,
        "tailRemainderAbsTotal": len(tail_remainder_records),
        "tailRemainderAbsRequiredByInventory": tail_remainder_required,
        "requiredTailRowFields": required_tail_row_fields,
        "blockersByStatus": dict(sorted(blocker_counts.items())),
        "observedArtifactBlockersByStatus": dict(
            sorted((status_counts + tail_status_counts).items())
        ),
        "chunkStatusCounts": dict(sorted(status_counts.items())),
        "tailRemainderAbsStatusCounts": dict(sorted(tail_status_counts.items())),
        "coverageTotals": coverage.get("totals", {}),
        "coverageMissingGroups": coverage.get("missingGroups", {}),
        "directProofInput": direct_worklist_summary(direct_worklist),
        "worklistTotals": worklist.get("totals", {}),
        "inventoryTotals": totals,
    }


def md_table(rows: list[list[Any]]) -> str:
    if not rows:
        return ""
    header = rows[0]
    out = ["| " + " | ".join(map(str, header)) + " |"]
    out.append("| " + " | ".join(["---"] * len(header)) + " |")
    for row in rows[1:]:
        out.append("| " + " | ".join("" if v is None else str(v) for v in row) + " |")
    return "\n".join(out)


def write_markdown(path: Path, ledger: dict[str, Any]) -> None:
    aggregates = ledger["aggregates"]
    blockers = aggregates["blockersByStatus"]
    rows: list[str] = []
    rows.append("# Step33A.1-A Margin Ledger")
    rows.append("")
    rows.append("Status: monitoring only; no proof route changed.")
    rows.append("")
    rows.append(f"Law: `{LAW}`.")
    rows.append("")
    rows.append("## Five-line readout")
    rows.append("")
    rows.append(f"- worstRemainingSlack: `{aggregates['worstRemainingSlack']}`")
    rows.append(f"- worstRow: `{aggregates['worstRow']}`")
    rows.append(f"- worstParentChunk: `{aggregates['worstParentChunk']}`")
    rows.append(f"- worstSubchunk: `{aggregates['worstSubchunk']}`")
    rows.append(f"- blockersByStatus: `{json.dumps(blockers, sort_keys=True)}`")
    rows.append("")
    rows.append("## Readiness")
    rows.append("")
    rows.append(
        f"- PayloadFin readiness: `{aggregates['PayloadFinReadinessPercent']}%` "
        f"({aggregates['cellsClosed']}/{aggregates['totalCells']})"
    )
    rows.append(
        "- tailRemainderAbs closed / total: "
        f"`{aggregates['tailRemainderAbsClosed']}/{aggregates['tailRemainderAbsTotal']}`"
    )
    rows.append(
        "- tailRemainderAbs required by active inventory: "
        f"`{aggregates['tailRemainderAbsRequiredByInventory']}`"
    )
    rows.append(
        f"- rows closed / total: `{aggregates['rowsClosed']}/{aggregates['totalRows']}`"
    )
    rows.append("")
    rows.append("## Blockers")
    rows.append("")
    rows.append("Active blockers are derived from the current inventory contract.")
    rows.append("")
    rows.append(
        md_table(
            [["status", "count"]]
            + [[status, count] for status, count in sorted(blockers.items())]
        )
    )
    rows.append("")
    rows.append("Observed artifact statuses, including legacy/informational worklists:")
    rows.append("")
    rows.append(
        md_table(
            [["status", "count"]]
            + [
                [status, count]
                for status, count in sorted(
                    aggregates["observedArtifactBlockersByStatus"].items()
                )
            ]
        )
    )
    rows.append("")
    rows.append("## Worst chunk context")
    rows.append("")
    worst = next(
        (
            record
            for record in ledger["records"]
            if record.get("rowId") == aggregates["worstRow"]
            and record.get("rowClass") == aggregates["worstRowClass"]
            and record.get("parentChunk") == aggregates["worstParentChunk"]
        ),
        None,
    )
    if worst:
        rows.append(
            md_table(
                [
                    [
                        "rowClass",
                        "rowId",
                        "parentChunk",
                        "subchunk",
                        "window",
                        "status",
                        "remainingSlackMin",
                        "missingFields",
                    ],
                    [
                        worst.get("rowClass"),
                        worst.get("rowId"),
                        worst.get("parentChunk"),
                        worst.get("subchunk"),
                        f"{worst.get('windowLower')}..{worst.get('windowUpper')}",
                        worst.get("status"),
                        worst.get("remainingSlackMin"),
                        ", ".join(worst.get("missingFields", [])[:6]),
                    ],
                ]
            )
        )
    else:
        rows.append("No numeric row-slack record found.")
    rows.append("")
    rows.append("## Coverage summary")
    rows.append("")
    rows.append("Current active direct proof-input surface:")
    rows.append("")
    rows.append("```json")
    rows.append(
        json.dumps(aggregates["directProofInput"], indent=2, sort_keys=True)
    )
    rows.append("```")
    rows.append("")
    rows.append("Global coverage missing groups:")
    rows.append("")
    rows.append("```json")
    rows.append(json.dumps(aggregates["coverageMissingGroups"], indent=2, sort_keys=True))
    rows.append("```")
    rows.append("")
    rows.append("## Guards")
    rows.append("")
    for guard in GUARDS:
        rows.append(f"- {guard}")
    rows.append("")
    rows.append("Outputs:")
    rows.append(f"- `{DEFAULT_OUT_JSON.relative_to(ROOT)}`")
    rows.append(f"- `{DEFAULT_OUT_MD.relative_to(ROOT)}`")
    rows.append("")
    path.write_text("\n".join(rows) + "\n")


def build(args: argparse.Namespace) -> dict[str, Any]:
    inventory = load_json(args.inventory)
    worklist = load_json(args.worklist)
    direct_worklist = load_json(args.direct_worklist)
    row_refresh_data = load_json(args.row_sum_refresh)
    tail_worklist = load_json(args.tail_worklist)
    coverage = load_json(args.coverage)

    refresh = row_refresh_index(row_refresh_data)
    direct_parents = direct_parent_index(direct_worklist)
    chunk_records = build_records(worklist, refresh, direct_parents)
    tails = tail_records(tail_worklist)
    aggregates = aggregate(
        inventory, worklist, direct_worklist, coverage, chunk_records, tails
    )

    return {
        "schema": SCHEMA,
        "createdAt": datetime.now(timezone.utc).isoformat(),
        "meaning": (
            "Step33A.1-A raw-Omega Taylor payload margin accounting. "
            "This ledger is a dashboard, not a proof-route change."
        ),
        "law": LAW,
        "routeGuard": GUARDS,
        "inputs": {
            "inventory": str(args.inventory.relative_to(ROOT)),
            "worklist": str(args.worklist.relative_to(ROOT)),
            "directProofInputWorklist": str(args.direct_worklist.relative_to(ROOT)),
            "rowSumRefresh": str(args.row_sum_refresh.relative_to(ROOT)),
            "tailWorklist": str(args.tail_worklist.relative_to(ROOT)),
            "coverage": str(args.coverage.relative_to(ROOT)),
        },
        "aggregates": aggregates,
        "records": chunk_records,
        "tailRemainderAbsRecords": tails,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--direct-worklist", type=Path, default=DEFAULT_DIRECT_WORKLIST)
    parser.add_argument("--row-sum-refresh", type=Path, default=DEFAULT_ROW_SUM_REFRESH)
    parser.add_argument("--tail-worklist", type=Path, default=DEFAULT_TAIL_WORKLIST)
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    ledger = build(args)
    args.out_json.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    write_markdown(args.out_md, ledger)
    aggregates = ledger["aggregates"]
    print(json.dumps({
        "schema": SCHEMA,
        "out_json": str(args.out_json),
        "out_md": str(args.out_md),
        "worstRemainingSlack": aggregates["worstRemainingSlack"],
        "worstRow": aggregates["worstRow"],
        "worstParentChunk": aggregates["worstParentChunk"],
        "worstSubchunk": aggregates["worstSubchunk"],
        "blockersByStatus": aggregates["blockersByStatus"],
        "PayloadFinReadinessPercent": aggregates["PayloadFinReadinessPercent"],
        "tailRemainderAbsClosed": aggregates["tailRemainderAbsClosed"],
        "tailRemainderAbsTotal": aggregates["tailRemainderAbsTotal"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
