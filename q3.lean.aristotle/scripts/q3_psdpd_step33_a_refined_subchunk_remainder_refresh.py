#!/usr/bin/env python3
"""Refresh refined-subchunk candidate remainders from a residual audit.

This is a generator-side diagnostic helper.  It consumes a candidate overlay and
a sampled residual audit, then raises each candidate remainder to the sampled
required remainder when needed.  It emits no Lean proof data.
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
DEFAULT_CANDIDATE = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_1_denom1e30.json"
)
DEFAULT_RESIDUAL_AUDIT = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_subchunk_rational_residual_audit_primary_finite_0_1_denom1e30.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_1_denom1e30_residualfit.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_1_denom1e30_residualfit.md"
)

CANDIDATE_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"
RESIDUAL_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_rational_residual_audit.v1"


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


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        numerator, denominator = text.split("/", 1)
        return Fraction(int(numerator), int(denominator))
    return Fraction(Decimal(text))


def decimal_from_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_sci(value: Decimal) -> str:
    return format(value, ".18E")


def residual_by_subchunk(residual: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {int(row["subchunk"]): row for row in residual.get("subchunks", [])}


def refresh_candidate(candidate: dict[str, Any], residual: dict[str, Any]) -> dict[str, Any]:
    validate_schema(candidate, path=Path("<candidate>"), schema=CANDIDATE_SCHEMA)
    validate_schema(residual, path=Path("<residual>"), schema=RESIDUAL_SCHEMA)

    residual_rows = residual_by_subchunk(residual)
    refreshed = json.loads(json.dumps(candidate))
    adjusted = []
    total_extra = Fraction(0)
    max_extra = Fraction(0)

    for entry in refreshed.get("candidates", []):
        subchunk = int(entry["subchunk"])
        row = residual_rows.get(subchunk)
        if row is None:
            raise ValueError(f"residual audit missing subchunk {subchunk}")
        current = parse_fraction(entry["remainder"])
        required = parse_fraction(row["requiredRemainder"])
        new_value = max(current, required)
        extra = new_value - current
        if extra > 0:
            entry["remainderBeforeRefresh"] = fraction_text(current)
            entry["remainder"] = fraction_text(new_value)
            entry["remainderRefreshReason"] = "sampled_residual_required_remainder"
            adjusted.append(
                {
                    "subchunk": subchunk,
                    "currentRemainder": fraction_text(current),
                    "requiredRemainder": fraction_text(required),
                    "newRemainder": fraction_text(new_value),
                    "extraRemainder": fraction_text(extra),
                    "extraRemainderDecimal": decimal_sci(decimal_from_fraction(extra)),
                }
            )
            total_extra += extra
            max_extra = max(max_extra, extra)

    refreshed["status"] = "candidate_overlay_remainder_refreshed_not_proof_data"
    refreshed["sourceCandidateOverlay"] = candidate.get("sourceCandidateOverlay", "")
    refreshed["sourceResidualAudit"] = residual.get("overlay", "")
    refreshed["remainderRefresh"] = {
        "adjustedSubchunks": len(adjusted),
        "totalExtraRemainder": fraction_text(total_extra),
        "totalExtraRemainderDecimal": decimal_sci(decimal_from_fraction(total_extra)),
        "maxExtraRemainder": fraction_text(max_extra),
        "maxExtraRemainderDecimal": decimal_sci(decimal_from_fraction(max_extra)),
        "adjusted": adjusted,
    }
    refreshed["routeGuard"] = refreshed.get("routeGuard", []) + [
        "remainder refresh is diagnostic generator data only",
        "sampled residual audit is not a universal Lean proof",
        "do not emit Lean until analytic residual bounds are checked",
    ]
    return refreshed


def render_md(report: dict[str, Any]) -> str:
    pilot = report["pilot"]
    refresh = report["remainderRefresh"]
    lines = [
        "# Step33A.1-A Refined Subchunk Remainder Refresh",
        "",
        "Diagnostic only: candidate remainders raised to sampled residual requirements.",
        "No Lean proof data is emitted.",
        "",
        "## Summary",
        "",
        f"- status: `{report['status']}`",
        f"- family: `{pilot['family']}`",
        f"- row: `{pilot['row']}`",
        f"- parent chunk: `{pilot['parentChunk']}`",
        f"- split: `{pilot['split']}`",
        f"- adjusted subchunks: `{refresh['adjustedSubchunks']}`",
        f"- total extra remainder: `{refresh['totalExtraRemainderDecimal']}`",
        f"- max extra remainder: `{refresh['maxExtraRemainderDecimal']}`",
        "",
        "## Adjusted Subchunks",
        "",
        "| subchunk | current | required | new | extra |",
        "| ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in refresh["adjusted"]:
        lines.append(
            f"| {row['subchunk']} | `{row['currentRemainder']}` | "
            f"`{row['requiredRemainder']}` | `{row['newRemainder']}` | "
            f"`{row['extraRemainderDecimal']}` |"
        )
    if not refresh["adjusted"]:
        lines.append("| none |  |  |  |  |")
    lines.extend(["", "## Guard", ""])
    for item in report.get("routeGuard", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", type=Path, default=DEFAULT_CANDIDATE)
    parser.add_argument("--residual-audit", type=Path, default=DEFAULT_RESIDUAL_AUDIT)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    getcontext().prec = 120
    candidate = load_json(args.candidate)
    residual = load_json(args.residual_audit)
    report = refresh_candidate(candidate, residual)
    report["sourceCandidateOverlay"] = str(args.candidate)
    report["sourceResidualAudit"] = str(args.residual_audit)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    refresh = report["remainderRefresh"]
    print(
        "status={status} adjusted={adjusted} total_extra={total} max_extra={max_extra}".format(
            status=report["status"],
            adjusted=refresh["adjustedSubchunks"],
            total=refresh["totalExtraRemainderDecimal"],
            max_extra=refresh["maxExtraRemainderDecimal"],
        )
    )


if __name__ == "__main__":
    run()
