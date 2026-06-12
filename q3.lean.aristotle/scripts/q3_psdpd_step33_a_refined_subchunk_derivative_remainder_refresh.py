#!/usr/bin/env python3
"""Refresh refined-subchunk remainders to derivative-envelope requirements.

This is a fail-closed generator helper for Step33A.1-A.  It consumes a
candidate overlay and a derivative-bound audit, then raises each candidate
remainder to the sampled direct-envelope left-hand side when needed:

    sampleRadius + sampledSlope * mesh <= remainder

The output is still diagnostic candidate data, not Lean proof data.  It only
prepares a candidate overlay for the direct derivative overlay generator.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, ROUND_CEILING, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_CANDIDATE = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_1_denom1e30_residualfit.json"
)
DEFAULT_DERIVATIVE_AUDIT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_1_denom1e30_residualfit.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_1_denom1e30_derivfit.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_1_denom1e30_derivfit.md"
)

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


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        numerator, denominator = text.split("/", 1)
        return Fraction(int(numerator), int(denominator))
    return Fraction(Decimal(text))


def decimal_from_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def ceil_decimal_to_denom(value: Decimal, denom: int) -> Fraction:
    scaled = (max(Decimal(0), value) * Decimal(denom)).to_integral_value(
        rounding=ROUND_CEILING
    )
    return Fraction(int(scaled), denom)


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_sci(value: Decimal) -> str:
    return format(value, ".18E")


def derivative_by_subchunk(derivative: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {int(row["subchunk"]): row for row in derivative.get("subchunks", [])}


def denominator_from_derivative(derivative: dict[str, Any], fallback: int) -> int:
    parameters = derivative.get("parameters") or {}
    raw = parameters.get("denominator")
    if raw is None:
        return fallback
    value = int(raw)
    if value <= 0:
        raise ValueError("derivative denominator must be positive")
    return value


def refresh_candidate(
    candidate: dict[str, Any],
    derivative: dict[str, Any],
    *,
    denominator: int,
) -> dict[str, Any]:
    validate_schema(candidate, path=Path("<candidate>"), schema=CANDIDATE_SCHEMA)
    validate_schema(derivative, path=Path("<derivative>"), schema=DERIVATIVE_SCHEMA)

    derivative_rows = derivative_by_subchunk(derivative)
    refreshed = json.loads(json.dumps(candidate))
    adjusted: list[dict[str, Any]] = []
    total_extra = Fraction(0)
    max_extra = Fraction(0)
    sampled_passes_after_refresh = 0

    for entry in refreshed.get("candidates", []):
        subchunk = int(entry["subchunk"])
        row = derivative_rows.get(subchunk)
        if row is None:
            raise ValueError(f"derivative audit missing subchunk {subchunk}")

        current = parse_fraction(entry["remainder"])
        required = ceil_decimal_to_denom(Decimal(str(row["sampledEnvelopeLhs"])), denominator)
        new_value = max(current, required)
        extra = new_value - current
        if extra > 0:
            entry["remainderBeforeDerivativeRefresh"] = fraction_text(current)
            entry["remainder"] = fraction_text(new_value)
            entry["remainderRefreshReason"] = "sampled_derivative_envelope_lhs"
            adjusted.append(
                {
                    "subchunk": subchunk,
                    "currentRemainder": fraction_text(current),
                    "sampledEnvelopeLhs": str(row["sampledEnvelopeLhs"]),
                    "requiredRemainder": fraction_text(required),
                    "newRemainder": fraction_text(new_value),
                    "extraRemainder": fraction_text(extra),
                    "extraRemainderDecimal": decimal_sci(decimal_from_fraction(extra)),
                }
            )
            total_extra += extra
            max_extra = max(max_extra, extra)
        if decimal_from_fraction(new_value) >= Decimal(str(row["sampledEnvelopeLhs"])):
            sampled_passes_after_refresh += 1

    refreshed["status"] = "candidate_overlay_derivative_remainder_refreshed_not_proof_data"
    refreshed["sourceCandidateOverlay"] = candidate.get("sourceCandidateOverlay", "")
    refreshed["sourceDerivativeAudit"] = derivative.get("overlay", "")
    refreshed["derivativeRemainderRefresh"] = {
        "adjustedSubchunks": len(adjusted),
        "totalExtraRemainder": fraction_text(total_extra),
        "totalExtraRemainderDecimal": decimal_sci(decimal_from_fraction(total_extra)),
        "maxExtraRemainder": fraction_text(max_extra),
        "maxExtraRemainderDecimal": decimal_sci(decimal_from_fraction(max_extra)),
        "sampledEnvelopePassesAfterRefresh": sampled_passes_after_refresh,
        "candidateSubchunks": len(refreshed.get("candidates", [])),
        "adjusted": adjusted,
    }
    refreshed["routeGuard"] = refreshed.get("routeGuard", []) + [
        "derivative remainder refresh is diagnostic generator data only",
        "sampled derivative envelope is not a universal Lean proof",
        "do not emit Lean until hEnvelope and hResidualDerivBoundOnCell are checked",
    ]
    return refreshed


def render_md(report: dict[str, Any]) -> str:
    pilot = report["pilot"]
    refresh = report["derivativeRemainderRefresh"]
    lines = [
        "# Step33A.1-A Refined Subchunk Derivative Remainder Refresh",
        "",
        "Diagnostic only: candidate remainders raised to sampled derivative-envelope requirements.",
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
        f"- sampled envelope passes after refresh: `{refresh['sampledEnvelopePassesAfterRefresh']}/{refresh['candidateSubchunks']}`",
        f"- total extra remainder: `{refresh['totalExtraRemainderDecimal']}`",
        f"- max extra remainder: `{refresh['maxExtraRemainderDecimal']}`",
        "",
        "## Adjusted Subchunks",
        "",
        "| subchunk | current | sampled lhs | required | new | extra |",
        "| ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in refresh["adjusted"]:
        lines.append(
            f"| {row['subchunk']} | `{row['currentRemainder']}` | "
            f"`{row['sampledEnvelopeLhs']}` | `{row['requiredRemainder']}` | "
            f"`{row['newRemainder']}` | `{row['extraRemainderDecimal']}` |"
        )
    if not refresh["adjusted"]:
        lines.append("| none |  |  |  |  |  |")
    lines.extend(["", "## Guard", ""])
    for item in report.get("routeGuard", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", type=Path, default=DEFAULT_CANDIDATE)
    parser.add_argument("--derivative-audit", type=Path, default=DEFAULT_DERIVATIVE_AUDIT)
    parser.add_argument("--denominator", type=int, default=0)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    getcontext().prec = 120
    candidate = load_json(args.candidate)
    derivative = load_json(args.derivative_audit)
    denominator = args.denominator or denominator_from_derivative(derivative, 10**30)
    report = refresh_candidate(candidate, derivative, denominator=denominator)
    report["sourceCandidateOverlay"] = str(args.candidate)
    report["sourceDerivativeAudit"] = str(args.derivative_audit)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    refresh = report["derivativeRemainderRefresh"]
    print(
        "status={status} adjusted={adjusted} sampled_passes_after={passes}/{total} total_extra={total_extra}".format(
            status=report["status"],
            adjusted=refresh["adjustedSubchunks"],
            passes=refresh["sampledEnvelopePassesAfterRefresh"],
            total=refresh["candidateSubchunks"],
            total_extra=refresh["totalExtraRemainderDecimal"],
        )
    )


if __name__ == "__main__":
    run()
