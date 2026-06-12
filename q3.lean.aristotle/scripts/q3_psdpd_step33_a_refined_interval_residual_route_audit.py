#!/usr/bin/env python3
"""Audit direct Arb interval residual enclosure for refined subchunks.

This is a fail-closed route audit, not Lean proof data.  It checks whether the
obvious interval expression

    rawOmegaIntegrand(eta_ball) - rationalPolynomial(eta_ball)

can prove the tiny `diffLower` / `diffUpper` remainders already found by the
sampled rational residual audit.

The expected outcome for the first finite pilot is negative: plain ball
subtraction loses too much dependency information.  Recording that failure is
useful because it rules out a tempting generator swamp and points the next
proof-producing route at a derivative/Cauchy/Taylor-remainder enclosure instead.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

try:
    from flint import acb, arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required. Run with the repo venv, for example:\n"
        "  .venv/bin/python q3.lean.aristotle/scripts/"
        "q3_psdpd_step33_a_refined_interval_residual_route_audit.py"
    ) from exc

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    set_precision,
)
from q3_psdpd_step33_a_chunk_integral_probe import (
    DEFAULT_WORKLIST,
    decimal_str,
    load_worklist,
    make_builder,
    selected_families,
)


getcontext().prec = 100

ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0.json"
)
DEFAULT_RESIDUAL_AUDIT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_rational_residual_audit_primary_finite_0_0.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_interval_residual_route_audit_primary_finite_0_0.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_interval_residual_route_audit_primary_finite_0_0.md"
)

OVERLAY_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"
RESIDUAL_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_rational_residual_audit.v1"
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


def decimal_from_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def decimal_sci(value: Decimal) -> str:
    return format(value, ".18E")


def fraction_arb(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def parse_int_csv(text: str) -> list[int] | None:
    if text == "all":
        return None
    out: list[int] = []
    for part in text.split(","):
        part = part.strip()
        if part:
            out.append(int(part))
    return out


def residual_by_subchunk(residual_audit: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {
        int(row["subchunk"]): row
        for row in residual_audit.get("subchunks", [])
    }


def selected_candidates(
    overlay: dict[str, Any], selection: str
) -> list[dict[str, Any]]:
    candidates = list(overlay.get("candidates", []))
    selected = parse_int_csv(selection)
    if selected is None:
        return candidates
    by_index = {int(candidate["subchunk"]): candidate for candidate in candidates}
    missing = [index for index in selected if index not in by_index]
    if missing:
        raise ValueError(f"missing subchunk(s): {missing}")
    return [by_index[index] for index in selected]


def sinc_series_acb(x: acb, terms: int) -> acb:
    total = acb(0)
    x2 = x * x
    power = acb(1)
    for n in range(terms):
        coeff = arb((-1) ** n) / arb(math.factorial(2 * n + 1))
        total += acb(coeff) * power
        power *= x2
    return total


def raw_step22_series_integrand(builder: Any, d: Decimal, *, sinc_terms: int):
    d_acb = acb(arb(str(d)))
    ell_acb = acb(builder.ell)
    pi_acb = acb(builder.pi)
    norm_acb = acb(builder.norm)
    two = acb(2)
    s_acb = acb(builder.s_k)

    def f(t: acb) -> acb:
        z = acb(arb("0.25")) + builder.i_unit * t / two
        omega = z.digamma().real - builder.log_pi
        x = ell_acb * t / (two * s_acb)
        e2 = norm_acb * (sinc_series_acb(x, sinc_terms) ** builder.sinc_power)
        return (ell_acb / pi_acb) * acb(omega) * e2 * (t * d_acb).cos()

    return f


def polynomial_eval_ball(coeff: list[Fraction], *, eta: arb, center: Decimal) -> arb:
    shifted = eta - arb(str(center))
    total = arb(0)
    power = arb(1)
    for coeff_i in coeff:
        total += fraction_arb(coeff_i) * power
        power *= shifted
    return total


def audit_candidate(
    *,
    f: Any,
    candidate: dict[str, Any],
    residual_info: dict[str, Any] | None,
    split_schedule: list[int],
) -> dict[str, Any]:
    coeff = [parse_fraction(value) for value in candidate.get("coeff", [])]
    left = Decimal(str(candidate["left"]))
    right = Decimal(str(candidate["right"]))
    center = Decimal(str(candidate["center"]))
    remainder = parse_fraction(candidate["remainder"])
    remainder_decimal = decimal_from_fraction(remainder)

    rows = []
    for split_count in split_schedule:
        step = (right - left) / Decimal(split_count)
        lower: Decimal | None = None
        upper: Decimal | None = None
        max_abs = Decimal(0)
        worst_piece = 0
        for piece in range(split_count):
            piece_left = left + Decimal(piece) * step
            piece_right = piece_left + step
            piece_center = (piece_left + piece_right) / Decimal(2)
            piece_radius = (piece_right - piece_left) / Decimal(2)
            eta = arb(str(piece_center), str(piece_radius))
            diff = f(acb(eta)).real - polynomial_eval_ball(
                coeff, eta=eta, center=center
            )
            diff_lower = arb_lower_decimal(diff)
            diff_upper = arb_upper_decimal(diff)
            lower = diff_lower if lower is None else min(lower, diff_lower)
            upper = diff_upper if upper is None else max(upper, diff_upper)
            local_abs = max(abs(diff_lower), abs(diff_upper))
            if local_abs > max_abs:
                max_abs = local_abs
                worst_piece = piece
        assert lower is not None and upper is not None
        passes = lower >= -remainder_decimal and upper <= remainder_decimal
        rows.append(
            {
                "splits": split_count,
                "diffLower": decimal_sci(lower),
                "diffUpper": decimal_sci(upper),
                "maxAbsDiff": decimal_sci(max_abs),
                "passesRemainder": passes,
                "worstPiece": worst_piece,
            }
        )

    last = rows[-1]
    last_abs = Decimal(last["maxAbsDiff"])
    estimated_splits = None
    if last_abs > 0 and remainder_decimal > 0:
        estimated = Decimal(last["splits"]) * last_abs / remainder_decimal
        estimated_splits = decimal_sci(estimated)

    return {
        "subchunk": int(candidate["subchunk"]),
        "left": candidate["left"],
        "right": candidate["right"],
        "center": candidate["center"],
        "remainder": candidate["remainder"],
        "sampledMaxResidual": (
            residual_info or {}
        ).get("sampledMaxResidual"),
        "sampledRemainderPasses": (
            residual_info or {}
        ).get("currentRemainderPassesSampledAudit"),
        "splitRows": rows,
        "passesAtMaxSplit": bool(last["passesRemainder"]),
        "maxSplitMaxAbsDiff": last["maxAbsDiff"],
        "estimatedSplitsForRemainderLinearTrend": estimated_splits,
    }


def build_report(args: argparse.Namespace) -> dict[str, Any]:
    overlay = load_json(args.overlay)
    residual_audit = load_json(args.residual_audit)
    if overlay.get("schema") != OVERLAY_SCHEMA:
        raise ValueError(f"{args.overlay}: unexpected schema {overlay.get('schema')!r}")
    if residual_audit.get("schema") != RESIDUAL_AUDIT_SCHEMA:
        raise ValueError(
            f"{args.residual_audit}: unexpected schema {residual_audit.get('schema')!r}"
        )

    pilot = overlay["pilot"]
    worklist = load_worklist(args.worklist)
    family_id = str(pilot["family"])
    families = selected_families(worklist, family_id)
    if len(families) != 1:
        raise ValueError(f"expected one family {family_id!r}, found {len(families)}")
    family = families[0]
    distance = Decimal(str(family["distances"][int(pilot["row"])]["distance"]))

    set_precision(args.arb_prec)
    builder = make_builder(args, family=family)
    f = raw_step22_series_integrand(
        builder, distance, sinc_terms=args.series_sinc_terms
    )
    split_schedule = [int(part) for part in args.split_schedule.split(",") if part]
    residual_rows = residual_by_subchunk(residual_audit)
    candidates = selected_candidates(overlay, args.subchunks)
    rows = [
        audit_candidate(
            f=f,
            candidate=candidate,
            residual_info=residual_rows.get(int(candidate["subchunk"])),
            split_schedule=split_schedule,
        )
        for candidate in candidates
    ]
    pass_count = sum(1 for row in rows if row["passesAtMaxSplit"])
    worst = max(rows, key=lambda row: Decimal(row["maxSplitMaxAbsDiff"]))
    status = (
        "interval_residual_route_passed_not_proof"
        if pass_count == len(rows)
        else "interval_residual_route_rejected_dependency_overestimate"
    )
    return {
        "schema": "q3_psdpd_step33_a_refined_interval_residual_route_audit.v1",
        "status": status,
        "meaning": (
            "Fail-closed Arb interval route audit for direct residual/diff "
            "bounds.  This does not emit Lean and does not close proof fields."
        ),
        "overlay": str(args.overlay),
        "residualAudit": str(args.residual_audit),
        "worklist": str(args.worklist),
        "pilot": pilot,
        "parameters": {
            "arbPrec": args.arb_prec,
            "seriesSincTerms": args.series_sinc_terms,
            "splitSchedule": split_schedule,
            "subchunks": args.subchunks,
            "ell": args.ell,
            "source": args.source,
        },
        "counts": {
            "auditedSubchunks": len(rows),
            "passesAtMaxSplit": pass_count,
            "failsAtMaxSplit": len(rows) - pass_count,
            "proofSafeClosedFields": 0,
        },
        "worstAtMaxSplit": worst,
        "subchunks": rows,
        "routeVerdict": {
            "rejected": "plain_ball_interval_residual_subtraction",
            "reason": (
                "Ball interval subtraction overestimates the residual by many "
                "orders of magnitude compared with the 1e-18 remainder."
            ),
            "nextRecommended": (
                "derivative_or_cauchy_taylor_remainder_enclosure"
            ),
            "fallback": "much_sharper_symbolic_local_component_bounds",
        },
        "routeGuard": [
            "not Lean proof data",
            "do not import Arb interval residual rows as trusted theorem",
            "do not increase split counts into a microtask swamp",
            "plain interval residual subtraction is rejected unless it passes at practical split counts",
            "next proof-producing generator should use derivative/Cauchy/Taylor-remainder structure",
            "do not mutate CSV, ARadius, radius-floor, LDL, H1/PO3, or Q3.Main",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    counts = report["counts"]
    worst = report["worstAtMaxSplit"]
    route = report["routeVerdict"]
    lines = [
        "# Step33A.1-A Refined Interval Residual Route Audit",
        "",
        "Fail-closed route audit.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- schema: `{report['schema']}`",
        f"- status: `{report['status']}`",
        f"- audited subchunks: `{counts['auditedSubchunks']}`",
        f"- passes at max split: `{counts['passesAtMaxSplit']}`",
        f"- fails at max split: `{counts['failsAtMaxSplit']}`",
        f"- proof-safe closed fields: `{counts['proofSafeClosedFields']}`",
        "",
        "## Worst Max-Split Row",
        "",
        f"- subchunk: `{worst['subchunk']}`",
        f"- interval: `({worst['left']}, {worst['right']}]`",
        f"- max-split max abs diff: `{worst['maxSplitMaxAbsDiff']}`",
        f"- sampled max residual: `{worst['sampledMaxResidual']}`",
        f"- estimated splits for 1e-18 remainder: `{worst['estimatedSplitsForRemainderLinearTrend']}`",
        "",
        "## Route Verdict",
        "",
        f"- rejected: `{route['rejected']}`",
        f"- reason: `{route['reason']}`",
        f"- next recommended: `{route['nextRecommended']}`",
        f"- fallback: `{route['fallback']}`",
        "",
        "## Guard",
        "",
    ]
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--overlay", type=Path, default=DEFAULT_OVERLAY)
    parser.add_argument("--residual-audit", type=Path, default=DEFAULT_RESIDUAL_AUDIT)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--subchunks", default="0,37")
    parser.add_argument("--split-schedule", default="1,16,256,1024")
    parser.add_argument("--arb-prec", type=int, default=224)
    parser.add_argument("--series-sinc-terms", type=int, default=80)
    parser.add_argument("--source", default="raw_step22")
    parser.add_argument("--ell", default="0.30")
    parser.add_argument("--rel-tol", default="1e-40")
    parser.add_argument("--abs-tol", default="1e-40")
    parser.add_argument("--deg-limit", type=int, default=64)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=64)
    parser.add_argument("--sinc-terms", type=int, default=40)
    parser.add_argument("--omega-factor", default="10")
    parser.add_argument("--radius-floor", default="0")
    args = parser.parse_args()

    if args.source != "raw_step22":
        raise ValueError("this audit currently targets the raw_step22 source")
    report = build_report(args)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    counts = report["counts"]
    print(
        "status={status} audited={audited} passes={passes} fails={fails} "
        "worst_subchunk={worst} worst_max_abs={max_abs} next={next_route}".format(
            status=report["status"],
            audited=counts["auditedSubchunks"],
            passes=counts["passesAtMaxSplit"],
            fails=counts["failsAtMaxSplit"],
            worst=report["worstAtMaxSplit"]["subchunk"],
            max_abs=report["worstAtMaxSplit"]["maxSplitMaxAbsDiff"],
            next_route=report["routeVerdict"]["nextRecommended"],
        )
    )


if __name__ == "__main__":
    run()
