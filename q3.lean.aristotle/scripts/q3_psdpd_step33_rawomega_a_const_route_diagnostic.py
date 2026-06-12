#!/usr/bin/env python3
"""Diagnose the raw-Omega Step33 A full-window constant route.

This is not a Lean proof producer.  It checks whether a single constant lower
and upper comparison on the whole finite window `(0,T]` and tail window `(T,U]`
can plausibly fit the generated raw-Omega integral targets.

The check is deliberately optimistic for the constant route: at sampled points
it uses Arb enclosures to derive hard sampled obstructions.  If

    target_lower > window_width * min(sample upper bounds)

then no certified constant lower bound can both stay below the integrand at
those sampled points and reach the target lower integral.  Similarly, if

    window_width * max(sample lower bounds) > target_upper

then no certified constant upper bound can both stay above the integrand at
those sampled points and fit the target upper integral.

A positive sampled excess is therefore a route diagnostic, not a theorem: it
just tells the local worker to stop trying the full-window constant surface and
use the already compiled analytic/window comparison input instead.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path

try:
    from flint import acb, arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required. Run with the repo venv, for example:\n"
        "  .venv/bin/python q3.lean.aristotle/scripts/"
        "q3_psdpd_step33_rawomega_a_const_route_diagnostic.py"
    ) from exc

from q3_psdpd_step19_entry_radii import arb_lower_decimal, arb_upper_decimal, set_precision
from q3_psdpd_step22_arch_interval import ArchIntervalBuilder


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
OUT_JSON = REQUEST_DIR / "rawomega_a_const_route_diagnostic.json"
OUT_MD = REQUEST_DIR / "rawomega_a_const_route_diagnostic.md"

BLOCKS = [
    {
        "label": "primary k=11",
        "k_spline": 11,
        "finite": REQUEST_DIR / "a_finite_tail_components_k11.json",
        "tail": REQUEST_DIR / "a_signed_tail_probe_k11.json",
    },
    {
        "label": "control k=9",
        "k_spline": 9,
        "finite": REQUEST_DIR / "a_finite_tail_components_k9.json",
        "tail": REQUEST_DIR / "a_signed_tail_probe_k9.json",
    },
]


def decimal_str(x: Decimal) -> str:
    if x == 0:
        return "0.000000000000000000E+0"
    return format(x, ".18E")


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def make_builder(block: dict, params: dict) -> ArchIntervalBuilder:
    return ArchIntervalBuilder(
        k_spline=block["k_spline"],
        ell=params["ell"],
        cutoff_t=params["cutoff_t"],
        chunk_size=params["chunk_size"],
        rel_tol=params["rel_tol"],
        abs_tol=params["abs_tol"],
        deg_limit=int(params["deg_limit"]),
        eval_limit=int(params["eval_limit"]),
        depth_limit=int(params["depth_limit"]),
        sinc_terms=int(params["sinc_terms"]),
        omega_factor=params["omega_factor"],
        radius_floor=params["radius_floor"],
    )


def sample_times(left: Decimal, right: Decimal, count: int) -> list[Decimal]:
    if count < 1:
        raise ValueError("--samples-per-window must be positive")
    width = right - left
    if width <= 0:
        raise ValueError("sample window must have positive width")
    return [left + width * Decimal(i) / Decimal(count) for i in range(1, count + 1)]


def eval_bounds(builder: ArchIntervalBuilder, distance: Decimal, eta: Decimal) -> tuple[Decimal, Decimal]:
    val = builder.integrand(distance)(acb(arb(str(eta))), True).real
    return arb_lower_decimal(val), arb_upper_decimal(val)


def window_sample_summary(
    builder: ArchIntervalBuilder,
    distance: Decimal,
    left: Decimal,
    right: Decimal,
    samples_per_window: int,
) -> dict:
    rows = []
    min_sample_upper: Decimal | None = None
    max_sample_lower: Decimal | None = None
    min_upper_eta: Decimal | None = None
    max_lower_eta: Decimal | None = None

    for eta in sample_times(left, right, samples_per_window):
        lo, hi = eval_bounds(builder, distance, eta)
        rows.append({"eta": decimal_str(eta), "lower": decimal_str(lo), "upper": decimal_str(hi)})
        if min_sample_upper is None or hi < min_sample_upper:
            min_sample_upper = hi
            min_upper_eta = eta
        if max_sample_lower is None or lo > max_sample_lower:
            max_sample_lower = lo
            max_lower_eta = eta

    assert min_sample_upper is not None
    assert max_sample_lower is not None
    assert min_upper_eta is not None
    assert max_lower_eta is not None
    return {
        "left": decimal_str(left),
        "right": decimal_str(right),
        "width": decimal_str(right - left),
        "min_sample_upper": decimal_str(min_sample_upper),
        "min_sample_upper_eta": decimal_str(min_upper_eta),
        "max_sample_lower": decimal_str(max_sample_lower),
        "max_sample_lower_eta": decimal_str(max_lower_eta),
        "sample_count": samples_per_window,
        "samples": rows,
    }


def diagnose_window(
    summary: dict,
    target_lower: Decimal,
    target_upper: Decimal,
) -> dict:
    width = Decimal(summary["width"])
    lower_capacity = width * Decimal(summary["min_sample_upper"])
    upper_floor = width * Decimal(summary["max_sample_lower"])
    lower_excess = max(Decimal(0), target_lower - lower_capacity)
    upper_excess = max(Decimal(0), upper_floor - target_upper)
    excess = max(lower_excess, upper_excess)
    return {
        "target_lower": decimal_str(target_lower),
        "target_upper": decimal_str(target_upper),
        "lower_capacity_from_samples": decimal_str(lower_capacity),
        "upper_floor_from_samples": decimal_str(upper_floor),
        "lower_excess": decimal_str(lower_excess),
        "upper_excess": decimal_str(upper_excess),
        "excess": decimal_str(excess),
        "sampled_constant_route_possible": excess == 0,
    }


def diagnose_block(block: dict, args: argparse.Namespace) -> dict:
    finite_payload = load_json(block["finite"])
    tail_payload = load_json(block["tail"])
    if finite_payload.get("schema") != "q3_psdpd_step22_arch_finite_tail_components.v1":
        raise ValueError(f"{block['finite']}: unexpected schema")
    if tail_payload.get("schema") != "q3_psdpd_step33_a_signed_tail_probe.v1":
        raise ValueError(f"{block['tail']}: unexpected schema")

    params = finite_payload["parameters"]
    builder = make_builder(block, params)
    cutoff = Decimal(params["cutoff_t"])
    tail_end = Decimal(tail_payload["parameters"]["tail_window_end"])

    tail_rows = {int(row["index"]): row for row in tail_payload["distances"]}
    rows = []
    worst_finite = None
    worst_tail = None

    for idx, finite_row in enumerate(finite_payload["distances"]):
        tail_row = tail_rows[idx]
        distance = Decimal(finite_row["distance"])
        finite_mid = Decimal(finite_row["finite_mid"])
        finite_radius = Decimal(finite_row["finite_radius"])
        finite_lower = finite_mid - finite_radius
        finite_upper = finite_mid + finite_radius
        tail_lower = Decimal(tail_row["window_lower"])
        tail_upper = Decimal(tail_row["window_upper"])

        finite_summary = window_sample_summary(
            builder, distance, Decimal(0), cutoff, args.samples_per_window
        )
        tail_summary = window_sample_summary(
            builder, distance, cutoff, tail_end, args.samples_per_window
        )
        finite_diag = diagnose_window(finite_summary, finite_lower, finite_upper)
        tail_diag = diagnose_window(tail_summary, tail_lower, tail_upper)
        row = {
            "index": idx,
            "distance": finite_row["distance"],
            "finite": {**finite_summary, **finite_diag},
            "tail": {**tail_summary, **tail_diag},
        }
        rows.append(row)
        if worst_finite is None or Decimal(row["finite"]["excess"]) > Decimal(
            worst_finite["finite"]["excess"]
        ):
            worst_finite = row
        if worst_tail is None or Decimal(row["tail"]["excess"]) > Decimal(
            worst_tail["tail"]["excess"]
        ):
            worst_tail = row

    assert worst_finite is not None
    assert worst_tail is not None
    return {
        "label": block["label"],
        "k_spline": block["k_spline"],
        "distance_count": len(rows),
        "worst_finite": {
            "index": worst_finite["index"],
            "distance": worst_finite["distance"],
            "finite": {k: v for k, v in worst_finite["finite"].items() if k != "samples"},
        },
        "worst_tail": {
            "index": worst_tail["index"],
            "distance": worst_tail["distance"],
            "tail": {k: v for k, v in worst_tail["tail"].items() if k != "samples"},
        },
        "rows": rows,
    }


def render_md(result: dict) -> str:
    lines = [
        "# Raw-Omega A Full-Window Constant Route Diagnostic",
        "",
        "This is a sampled Arb diagnostic, not a Lean proof object.",
        "",
        f"- samples per window: `{result['parameters']['samples_per_window']}`",
        f"- verdict: `{result['verdict']}`",
        "",
        "Positive excess means the full-window constant comparison route is",
        "already too coarse at sampled points and the next target should be",
        "`RawOmegaAAnalyticTailWindowInputs` rather than more constant-route glue.",
        "",
    ]
    for block in result["blocks"]:
        lines.extend(
            [
                f"## {block['label']}",
                "",
                "Worst finite window:",
                "",
                "```json",
                json.dumps(block["worst_finite"], indent=2, sort_keys=True),
                "```",
                "",
                "Worst tail window:",
                "",
                "```json",
                json.dumps(block["worst_tail"], indent=2, sort_keys=True),
                "```",
                "",
            ]
        )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--samples-per-window", type=int, default=257)
    parser.add_argument("--out-json", type=Path, default=OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=OUT_MD)
    args = parser.parse_args()

    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    blocks = [diagnose_block(block, args) for block in BLOCKS]
    any_excess = any(
        Decimal(block["worst_finite"]["finite"]["excess"]) > 0
        or Decimal(block["worst_tail"]["tail"]["excess"]) > 0
        for block in blocks
    )
    verdict = (
        "full_window_constant_route_sampled_too_coarse"
        if any_excess
        else "full_window_constant_route_not_rejected_by_samples"
    )
    result = {
        "schema": "q3_psdpd_step33_rawomega_a_const_route_diagnostic.v1",
        "meaning": (
            "Sampled Arb diagnostic for the raw-Omega full-window constant "
            "comparison route feeding RawOmegaAConstComparisonDirectTailInputs."
        ),
        "parameters": {
            "arb_prec": args.arb_prec,
            "samples_per_window": args.samples_per_window,
        },
        "verdict": verdict,
        "blocks": blocks,
    }

    print(f"verdict={verdict}")
    for block in blocks:
        print(
            f"{block['label']}: worst finite excess="
            f"{block['worst_finite']['finite']['excess']} at d="
            f"{block['worst_finite']['distance']}; worst tail excess="
            f"{block['worst_tail']['tail']['excess']} at d="
            f"{block['worst_tail']['distance']}"
        )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {args.out_json}")
    args.out_md.write_text(render_md(result) + "\n", encoding="utf-8")
    print(f"Wrote {args.out_md}")


if __name__ == "__main__":
    run()
