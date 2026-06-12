#!/usr/bin/env python3
"""Sampled residual audit for refined rational polynomial candidates.

This consumes the fail-closed candidate overlay and evaluates the active
raw-Omega integrand against the rational polynomial candidates.  It is still a
diagnostic audit, not Lean proof data: sampled residuals do not prove the
universal `diffLower` / `diffUpper` fields.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, ROUND_CEILING, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

try:
    from flint import acb, arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required. Run with the repo venv, for example:\n"
        "  .venv/bin/python q3.lean.aristotle/scripts/"
        "q3_psdpd_step33_a_refined_subchunk_rational_residual_audit.py"
    ) from exc

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    set_precision,
)
from q3_psdpd_step33_a_chunk_integral_probe import (
    DEFAULT_WORKLIST,
    chunk_integrand,
    decimal_str,
    load_worklist,
    make_builder,
    selected_families,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_rational_residual_audit_primary_finite_0_0.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_rational_residual_audit_primary_finite_0_0.md"
)

OVERLAY_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"


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


def decimal_from_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def ceil_fraction_to_denom(value: Decimal, denom: int) -> Fraction:
    scaled = (max(Decimal(0), value) * Decimal(denom)).to_integral_value(
        rounding=ROUND_CEILING
    )
    return Fraction(int(scaled), denom)


def rational_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def sample_points(left: Decimal, right: Decimal, count: int) -> list[Decimal]:
    if count < 2:
        raise ValueError("sample count must be at least 2")
    step = (right - left) / Decimal(count - 1)
    return [left + Decimal(i) * step for i in range(count)]


def eval_integrand_mid_radius_decimal(f: Any, eta: Decimal) -> tuple[Decimal, Decimal]:
    value = f(acb(arb(str(eta))), True).real
    lower = arb_lower_decimal(value)
    upper = arb_upper_decimal(value)
    mid = (lower + upper) / Decimal(2)
    radius = max(upper - mid, mid - lower)
    return mid, radius


def eval_rational_poly(coeff: list[Fraction], shifted: Decimal) -> Decimal:
    total = Decimal(0)
    power = Decimal(1)
    for coeff_i in coeff:
        total += decimal_from_fraction(coeff_i) * power
        power *= shifted
    return total


def find_family(worklist: dict[str, Any], family_id: str) -> dict[str, Any]:
    matches = selected_families(worklist, family_id)
    if len(matches) != 1:
        raise ValueError(f"expected one family {family_id!r}, found {len(matches)}")
    return matches[0]


def find_row_distance(family: dict[str, Any], row_index: int) -> Decimal:
    rows = family.get("distances", [])
    if row_index < 0 or row_index >= len(rows):
        raise ValueError(f"row {row_index} outside family row count {len(rows)}")
    return Decimal(str(rows[row_index]["distance"]))


def audit_candidate(
    *,
    f: Any,
    candidate: dict[str, Any],
    check_samples: int,
    denominator: int,
    residual_guard: Decimal,
) -> dict[str, Any]:
    coeff = [parse_fraction(value) for value in candidate.get("coeff", [])]
    left = Decimal(str(candidate["left"]))
    right = Decimal(str(candidate["right"]))
    center = Decimal(str(candidate["center"]))
    current_remainder = parse_fraction(candidate["remainder"])
    current_remainder_decimal = decimal_from_fraction(current_remainder)

    max_residual = Decimal(0)
    max_eval_radius = Decimal(0)
    worst_eta = left
    worst_mid = Decimal(0)
    worst_poly = Decimal(0)
    for eta in sample_points(left, right, check_samples):
        mid, radius = eval_integrand_mid_radius_decimal(f, eta)
        poly = eval_rational_poly(coeff, eta - center)
        residual = abs(mid - poly) + radius
        if residual > max_residual:
            max_residual = residual
            worst_eta = eta
            worst_mid = mid
            worst_poly = poly
        max_eval_radius = max(max_eval_radius, radius)

    required = max_residual * (Decimal(1) + residual_guard) + Decimal("1e-90")
    required_rational = ceil_fraction_to_denom(required, denominator)
    required_decimal = decimal_from_fraction(required_rational)
    current_passes = current_remainder_decimal >= required_decimal
    return {
        "subchunk": int(candidate["subchunk"]),
        "left": candidate["left"],
        "right": candidate["right"],
        "center": candidate["center"],
        "coeffLen": len(coeff),
        "currentRemainder": rational_string(current_remainder),
        "sampledMaxResidual": decimal_str(max_residual),
        "sampledMaxEvalRadius": decimal_str(max_eval_radius),
        "requiredRemainder": rational_string(required_rational),
        "requiredRemainderDecimal": decimal_str(required_decimal),
        "currentRemainderPassesSampledAudit": current_passes,
        "worstEta": decimal_str(worst_eta),
        "worstRawMid": decimal_str(worst_mid),
        "worstRationalPoly": decimal_str(worst_poly),
        "sampledDiffLowerCandidate": rational_string(-required_rational),
        "sampledDiffUpperCandidate": rational_string(required_rational),
        "guard": [
            "sampled residual against rational polynomial only",
            "not a universal Lean diff proof",
        ],
    }


def build_report(
    *,
    args: argparse.Namespace,
    overlay: dict[str, Any],
    overlay_path: Path,
    worklist: dict[str, Any],
) -> dict[str, Any]:
    if overlay.get("schema") != OVERLAY_SCHEMA:
        raise ValueError(
            f"{overlay_path}: unexpected schema {overlay.get('schema')!r}"
        )
    pilot = overlay["pilot"]
    family_id = str(pilot["family"])
    row_index = int(pilot["row"])
    family = find_family(worklist, family_id)
    builder = make_builder(args, family=family)
    distance = find_row_distance(family, row_index)
    f = chunk_integrand(args=args, builder=builder, family=family, d=distance)

    residual_guard = Decimal(str(args.residual_guard))
    rows = [
        audit_candidate(
            f=f,
            candidate=candidate,
            check_samples=args.check_samples,
            denominator=args.denominator,
            residual_guard=residual_guard,
        )
        for candidate in overlay.get("candidates", [])
    ]
    pass_count = sum(1 for row in rows if row["currentRemainderPassesSampledAudit"])
    fail_rows = [row for row in rows if not row["currentRemainderPassesSampledAudit"]]
    worst = max(rows, key=lambda row: Decimal(row["sampledMaxResidual"])) if rows else None
    status = (
        "sampled_rational_residual_audit_passed_not_proof"
        if not fail_rows
        else "sampled_rational_residual_audit_failed"
    )
    return {
        "schema": "q3_psdpd_step33_a_refined_subchunk_rational_residual_audit.v1",
        "status": status,
        "meaning": (
            "Sampled diagnostic residual audit against rational polynomial "
            "candidates.  This is not Lean proof data."
        ),
        "overlay": str(overlay_path),
        "sourceWorklist": str(args.worklist),
        "parameters": {
            "source": args.source,
            "ell": args.ell,
            "arbPrec": args.arb_prec,
            "checkSamples": args.check_samples,
            "denominator": args.denominator,
            "residualGuard": args.residual_guard,
        },
        "pilot": pilot,
        "counts": {
            "candidateSubchunks": len(rows),
            "sampledRemainderPasses": pass_count,
            "sampledRemainderFails": len(fail_rows),
            "proofSafeClosedFields": 0,
            "sampledDiffCandidateFields": len(rows) * 2,
        },
        "worst": worst,
        "failures": fail_rows[:20],
        "subchunks": rows,
        "routeGuard": [
            "do not emit Lean from sampled residual audit",
            "sampled diff candidates must be replaced by universal checked bounds",
            "if sampled audit fails, increase or recompute candidate remainder before any proof-data attempt",
            "if sampled audit passes, the next target is a checked analytic enclosure for the same rational polynomial candidates",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    counts = report["counts"]
    pilot = report["pilot"]
    worst = report.get("worst") or {}
    lines = [
        "# Step33A.1-A Refined Subchunk Rational Residual Audit",
        "",
        "Sampled diagnostic audit.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
        f"- family: `{pilot['family']}`",
        f"- row: `{pilot['row']}`",
        f"- parent chunk: `{pilot['parentChunk']}`",
        f"- degree: `{pilot['degree']}`",
        f"- split: `{pilot['split']}`",
        "",
        "## Counts",
        "",
        "| item | count |",
        "| --- | ---: |",
    ]
    for key, value in counts.items():
        lines.append(f"| `{key}` | `{value}` |")
    if worst:
        lines.extend(
            [
                "",
                "## Worst Sample",
                "",
                f"- subchunk: `{worst['subchunk']}`",
                f"- worst eta: `{worst['worstEta']}`",
                f"- sampled max residual: `{worst['sampledMaxResidual']}`",
                f"- current remainder: `{worst['currentRemainder']}`",
                f"- required remainder: `{worst['requiredRemainder']}`",
            ]
        )
    if report.get("failures"):
        lines.extend(["", "## First Failures", "", "| subchunk | current | required | worst eta |", "| ---: | ---: | ---: | ---: |"])
        for failure in report["failures"]:
            lines.append(
                f"| {failure['subchunk']} | `{failure['currentRemainder']}` | "
                f"`{failure['requiredRemainder']}` | `{failure['worstEta']}` |"
            )
    lines.extend(["", "## Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--overlay", type=Path, default=DEFAULT_OVERLAY)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--source", choices=["raw_step22", "centered_receiver"], default="raw_step22")
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--rel-tol", type=str, default="1e-40")
    parser.add_argument("--abs-tol", type=str, default="1e-40")
    parser.add_argument("--deg-limit", type=int, default=64)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=20)
    parser.add_argument("--sinc-terms", type=int, default=90)
    parser.add_argument("--omega-factor", type=str, default="10")
    parser.add_argument("--radius-floor", type=str, default="1e-30")
    parser.add_argument("--arb-prec", type=int, default=224)
    parser.add_argument("--check-samples", type=int, default=61)
    parser.add_argument("--denominator", type=int, default=10**18)
    parser.add_argument("--residual-guard", type=str, default="0.10")
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    overlay = load_json(args.overlay)
    worklist = load_worklist(args.worklist)
    report = build_report(
        args=args,
        overlay=overlay,
        overlay_path=args.overlay,
        worklist=worklist,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} subchunks={subchunks} passes={passes} fails={fails}".format(
            status=report["status"],
            subchunks=report["counts"]["candidateSubchunks"],
            passes=report["counts"]["sampledRemainderPasses"],
            fails=report["counts"]["sampledRemainderFails"],
        )
    )


if __name__ == "__main__":
    run()
