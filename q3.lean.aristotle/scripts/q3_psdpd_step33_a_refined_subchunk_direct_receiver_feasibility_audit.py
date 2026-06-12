#!/usr/bin/env python3
"""Audit whether current direct subchunks can feed the preferred receivers.

This is a fail-closed route audit for Step33A.1-A.  It does not emit Lean
proof data.  It checks the concrete scalar candidate data behind the current
direct proof-input worklist and answers one narrow question:

* the scalar direct-envelope inequality is feasible;
* the current one-cell raw/poly derivative receiver loses cancellation and
  cannot prove the tiny residual-derivative bounds from the available
  raw/poly derivative intervals.

The output is meant to become the exact PRO/Louise review payload if this
route fork persists.
"""

from __future__ import annotations

import json
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

getcontext().prec = 100

ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

DEFAULT_AUDITS = [
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30.json",
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_1_denom1e30_derivfit.json",
]
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_receiver_feasibility_audit.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_receiver_feasibility_audit.md"
)

SCHEMA = "q3_psdpd_step33_a_refined_subchunk_direct_receiver_feasibility_audit.v1"
DERIVATIVE_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7"
)


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def decimal_of_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def sci(value: Fraction) -> str:
    return format(decimal_of_fraction(value), ".18E")


def fraction_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def scalar_entry(payload_path: Path, payload: dict[str, Any], row: dict[str, Any]) -> dict[str, Any]:
    raw_lower = parse_fraction(row["sampledRawDerivLower"])
    raw_upper = parse_fraction(row["sampledRawDerivUpper"])
    poly_lower = parse_fraction(row["sampledPolyDerivLower"])
    poly_upper = parse_fraction(row["sampledPolyDerivUpper"])
    deriv_lower = parse_fraction(row["sampledDerivLower"])
    deriv_upper = parse_fraction(row["sampledDerivUpper"])
    slope = parse_fraction(row["sampledSlope"])

    lower_rhs = raw_lower - poly_upper
    upper_lhs = raw_upper - poly_lower
    lower_excess = deriv_lower - lower_rhs
    upper_excess = upper_lhs - deriv_upper

    lower_passes = lower_excess <= 0
    upper_passes = upper_excess <= 0
    raw_poly_passes = lower_passes and upper_passes

    cell = (row.get("derivativeIntervalFiniteCoverCells") or [{}])[0]
    deriv_cell_lower = parse_fraction(cell.get("derivLower", deriv_lower))
    deriv_cell_upper = parse_fraction(cell.get("derivUpper", deriv_upper))
    abs_lower_excess = (-slope) - deriv_cell_lower
    abs_upper_excess = deriv_cell_upper - slope

    return {
        "source": str(payload_path),
        "family": (payload.get("pilot") or {}).get("family"),
        "row": (payload.get("pilot") or {}).get("row"),
        "parentChunk": (payload.get("pilot") or {}).get("parentChunk"),
        "split": (payload.get("pilot") or {}).get("split"),
        "subchunk": row.get("subchunk"),
        "left": row.get("left"),
        "right": row.get("right"),
        "sampledEnvelopePasses": bool(row.get("sampledEnvelopePasses")),
        "sampledEnvelopeExcess": row.get("sampledEnvelopeExcess"),
        "rawPolyOneCellPasses": raw_poly_passes,
        "hDerivLowerFromRawPolyWouldPass": lower_passes,
        "hDerivUpperFromRawPolyWouldPass": upper_passes,
        "hDerivLowerAbsWouldPass": abs_lower_excess <= 0,
        "hDerivUpperAbsWouldPass": abs_upper_excess <= 0,
        "rawLowerMinusPolyUpper": fraction_string(lower_rhs),
        "rawUpperMinusPolyLower": fraction_string(upper_lhs),
        "derivLower": fraction_string(deriv_lower),
        "derivUpper": fraction_string(deriv_upper),
        "derivSlope": fraction_string(slope),
        "lowerExcess": fraction_string(lower_excess),
        "upperExcess": fraction_string(upper_excess),
        "lowerExcessDecimal": sci(lower_excess),
        "upperExcessDecimal": sci(upper_excess),
        "maxRawPolyExcessDecimal": sci(max(lower_excess, upper_excess)),
    }


def build_report(paths: list[Path]) -> dict[str, Any]:
    entries: list[dict[str, Any]] = []
    for path in paths:
        payload = load_json(path)
        schema = payload.get("schema")
        if schema != DERIVATIVE_AUDIT_SCHEMA:
            raise ValueError(f"{path}: expected schema {DERIVATIVE_AUDIT_SCHEMA}, found {schema!r}")
        for row in payload.get("subchunks") or []:
            entries.append(scalar_entry(path, payload, row))

    if not entries:
        raise ValueError("no subchunk entries found")

    raw_poly_failures = [entry for entry in entries if not entry["rawPolyOneCellPasses"]]
    envelope_passes = [entry for entry in entries if entry["sampledEnvelopePasses"]]
    worst_lower = max(entries, key=lambda entry: Decimal(entry["lowerExcessDecimal"]))
    worst_upper = max(entries, key=lambda entry: Decimal(entry["upperExcessDecimal"]))
    worst = max(
        entries,
        key=lambda entry: max(
            Decimal(entry["lowerExcessDecimal"]),
            Decimal(entry["upperExcessDecimal"]),
        ),
    )

    status = (
        "route_fork_one_cell_raw_poly_receiver_loses_cancellation"
        if raw_poly_failures
        else "one_cell_raw_poly_receiver_feasible_for_current_candidates"
    )

    return {
        "schema": SCHEMA,
        "status": status,
        "meaning": (
            "Fail-closed feasibility audit for the current hEnvelope and "
            "hResidualDerivBoundOnCell receiver choices.  This is not Lean "
            "proof data."
        ),
        "totals": {
            "subchunks": len(entries),
            "sampledEnvelopePassingSubchunks": len(envelope_passes),
            "rawPolyOneCellPassingSubchunks": len(entries) - len(raw_poly_failures),
            "rawPolyOneCellFailingSubchunks": len(raw_poly_failures),
        },
        "currentReceiver": (
            "RawOmegaATaylorModelCertificate."
            "residual_deriv_bound_on_single_cell_of_raw_deriv_and_poly_term_expr_bounds"
        ),
        "diagnosis": (
            "The scalar envelope candidate is viable, but the preferred "
            "one-cell raw/poly derivative receiver cannot prove the tiny "
            "residual derivative from the available one-cell raw/poly "
            "intervals.  It loses cancellation across the whole subchunk."
        ),
        "recommendedForkQuestion": (
            "Switch to a cancellation-preserving residual-derivative proof "
            "surface, or generate much finer derivative cells with a receiver "
            "that preserves raw/poly alignment locally; do not mark "
            "hResidualDerivBoundOnCell proof-safe from the sampled direct pass."
        ),
        "worst": worst,
        "worstLower": worst_lower,
        "worstUpper": worst_upper,
        "entries": entries,
    }


def write_markdown(report: dict[str, Any], out: Path) -> None:
    totals = report["totals"]
    worst = report["worst"]
    lines = [
        "# Direct Receiver Feasibility Audit",
        "",
        f"schema: `{report['schema']}`",
        f"status: `{report['status']}`",
        "",
        "## Totals",
        "",
        f"- subchunks: `{totals['subchunks']}`",
        f"- sampled envelope passing subchunks: `{totals['sampledEnvelopePassingSubchunks']}`",
        f"- one-cell raw/poly passing subchunks: `{totals['rawPolyOneCellPassingSubchunks']}`",
        f"- one-cell raw/poly failing subchunks: `{totals['rawPolyOneCellFailingSubchunks']}`",
        "",
        "## Diagnosis",
        "",
        report["diagnosis"],
        "",
        "The scalar `hEnvelope` side is still feasible, but the current",
        "`hResidualDerivBoundOnCell` preferred receiver is not proof-ready from",
        "the available one-cell raw/poly intervals.",
        "",
        "## Worst Raw/Poly Cancellation Loss",
        "",
        f"- family: `{worst['family']}`",
        f"- row: `{worst['row']}`",
        f"- parentChunk: `{worst['parentChunk']}`",
        f"- subchunk: `{worst['subchunk']}`",
        f"- interval: `({worst['left']}, {worst['right']}]`",
        f"- lower excess: `{worst['lowerExcessDecimal']}`",
        f"- upper excess: `{worst['upperExcessDecimal']}`",
        "",
        "## Recommended Fork Question",
        "",
        report["recommendedForkQuestion"],
        "",
        "## Guard",
        "",
        "This artifact is not Lean proof data.  It must not be imported as a",
        "trusted payload and it does not close `A hbox` or Step33A.1-A.",
        "",
    ]
    out.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    report = build_report(DEFAULT_AUDITS)
    DEFAULT_OUT_JSON.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_markdown(report, DEFAULT_OUT_MD)
    totals = report["totals"]
    print(
        "status={status} subchunks={subchunks} raw_poly_failures={failures}".format(
            status=report["status"],
            subchunks=totals["subchunks"],
            failures=totals["rawPolyOneCellFailingSubchunks"],
        )
    )


if __name__ == "__main__":
    main()
