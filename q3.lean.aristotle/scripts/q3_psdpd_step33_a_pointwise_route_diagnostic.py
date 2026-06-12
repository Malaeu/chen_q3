#!/usr/bin/env python3
"""Diagnostic for the Step33A Arch A pointwise-constant chunk route.

This is not a proof producer.  It checks whether even optimistic sampled
constant pointwise bounds on each 10-wide chunk could fit the current tight
finite/tail window targets.  If the sampled lower/upper chunk sums already
miss the targets, the pointwise-constant route is too coarse and the active
route should use comparison-integral chunks instead.
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
        "q3_psdpd_step33_a_pointwise_route_diagnostic.py"
    ) from exc

from q3_psdpd_step22_arch_interval import ArchIntervalBuilder
from q3_psdpd_step19_entry_radii import set_precision


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_CONTRACT = REQUEST_DIR / "a_signed_chunk_payload_contract.json"


def decimal_str(x: Decimal) -> str:
    return format(x, ".18E")


def eval_point(builder: ArchIntervalBuilder, d: Decimal, t: Decimal) -> Decimal:
    val = builder.integrand(d)(acb(arb(str(t))), True).real
    return Decimal(val.mid().str(80, radius=False))


def sampled_chunk_bounds(
    builder: ArchIntervalBuilder,
    d: Decimal,
    left: Decimal,
    right: Decimal,
    samples_per_chunk: int,
) -> tuple[Decimal, Decimal]:
    if samples_per_chunk < 2:
        raise ValueError("--samples-per-chunk must be at least 2")
    width = right - left
    values = [
        eval_point(
            builder,
            d,
            left + width * Decimal(m) / Decimal(samples_per_chunk - 1),
        )
        for m in range(samples_per_chunk)
    ]
    return min(values), max(values)


def block_builder(k_spline: int, args: argparse.Namespace) -> ArchIntervalBuilder:
    return ArchIntervalBuilder(
        k_spline=k_spline,
        ell=args.ell,
        cutoff_t=args.cutoff_t,
        chunk_size=args.chunk_size,
        rel_tol=args.rel_tol,
        abs_tol=args.abs_tol,
        deg_limit=args.deg_limit,
        eval_limit=args.eval_limit,
        depth_limit=args.depth_limit,
        sinc_terms=args.sinc_terms,
        omega_factor=args.omega_factor,
        radius_floor=args.radius_floor,
    )


def diagnose_block(block: dict, args: argparse.Namespace) -> dict:
    builder = block_builder(int(block["k"]), args)
    chunk = Decimal(args.chunk_size)
    cutoff = Decimal(args.cutoff_t)
    tail_end = Decimal(args.tail_window_end)
    finite_chunks = int(cutoff / chunk)
    tail_chunks = int((tail_end - cutoff) / chunk)
    if finite_chunks * chunk != cutoff:
        raise ValueError("finite cutoff must be divisible by chunk size")
    if tail_chunks * chunk != tail_end - cutoff:
        raise ValueError("tail window must be divisible by chunk size")

    rows = []
    worst_finite = None
    worst_tail = None
    for row in block["distances"]:
        d = Decimal(row["distance"])
        finite_lower_sum = Decimal(0)
        finite_upper_sum = Decimal(0)
        for i in range(finite_chunks):
            left = chunk * Decimal(i)
            right = chunk * Decimal(i + 1)
            lo, hi = sampled_chunk_bounds(builder, d, left, right, args.samples_per_chunk)
            finite_lower_sum += chunk * lo
            finite_upper_sum += chunk * hi

        tail_lower_sum = Decimal(0)
        tail_upper_sum = Decimal(0)
        for i in range(tail_chunks):
            left = cutoff + chunk * Decimal(i)
            right = cutoff + chunk * Decimal(i + 1)
            lo, hi = sampled_chunk_bounds(builder, d, left, right, args.samples_per_chunk)
            tail_lower_sum += chunk * lo
            tail_upper_sum += chunk * hi

        finite_target_lower = Decimal(row["finite_lower"]) / Decimal(2)
        finite_target_upper = Decimal(row["finite_upper"]) / Decimal(2)
        tail_target_lower = Decimal(row["positive_window_lower"])
        tail_target_upper = Decimal(row["positive_window_upper"])

        finite_lower_excess = max(Decimal(0), finite_target_lower - finite_lower_sum)
        finite_upper_excess = max(Decimal(0), finite_upper_sum - finite_target_upper)
        finite_excess = max(finite_lower_excess, finite_upper_excess)
        tail_lower_excess = max(Decimal(0), tail_target_lower - tail_lower_sum)
        tail_upper_excess = max(Decimal(0), tail_upper_sum - tail_target_upper)
        tail_excess = max(tail_lower_excess, tail_upper_excess)

        out = {
            "index": row["index"],
            "distance": row["distance"],
            "finite_sampled_lower_sum": decimal_str(finite_lower_sum),
            "finite_sampled_upper_sum": decimal_str(finite_upper_sum),
            "finite_target_lower": decimal_str(finite_target_lower),
            "finite_target_upper": decimal_str(finite_target_upper),
            "finite_excess": decimal_str(finite_excess),
            "tail_sampled_lower_sum": decimal_str(tail_lower_sum),
            "tail_sampled_upper_sum": decimal_str(tail_upper_sum),
            "tail_target_lower": decimal_str(tail_target_lower),
            "tail_target_upper": decimal_str(tail_target_upper),
            "tail_excess": decimal_str(tail_excess),
        }
        rows.append(out)
        if worst_finite is None or finite_excess > Decimal(worst_finite["finite_excess"]):
            worst_finite = out
        if worst_tail is None or tail_excess > Decimal(worst_tail["tail_excess"]):
            worst_tail = out

    return {
        "block": block["block"],
        "label": block["label"],
        "k": block["k"],
        "distance_count": len(rows),
        "worst_finite": worst_finite,
        "worst_tail": worst_tail,
        "rows": rows,
    }


def render_md(result: dict) -> str:
    lines = [
        "# Step33A.1-A Pointwise Chunk Route Diagnostic",
        "",
        "This is a sampled route diagnostic, not a Lean proof object.",
        "It tests whether optimistic pointwise-constant chunk bounds can fit",
        "the current generated finite/tail window targets.",
        "",
        f"- samples per chunk: `{result['parameters']['samples_per_chunk']}`",
        f"- verdict: `{result['verdict']}`",
        "",
    ]
    for block in result["blocks"]:
        lines.extend(
            [
                f"## {block['label']}",
                "",
                "Worst finite:",
                "",
                "```json",
                json.dumps(block["worst_finite"], indent=2, sort_keys=True),
                "```",
                "",
                "Worst tail:",
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
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--ell", default="0.30")
    parser.add_argument("--cutoff-t", default="260")
    parser.add_argument("--tail-window-end", default="520")
    parser.add_argument("--chunk-size", default="10")
    parser.add_argument("--rel-tol", default="1e-30")
    parser.add_argument("--abs-tol", default="1e-30")
    parser.add_argument("--deg-limit", type=int, default=64)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=20)
    parser.add_argument("--sinc-terms", type=int, default=80)
    parser.add_argument("--omega-factor", default="10")
    parser.add_argument("--radius-floor", default="1e-30")
    parser.add_argument("--arb-prec", type=int, default=192)
    parser.add_argument("--samples-per-chunk", type=int, default=41)
    parser.add_argument("--out-json", type=Path)
    parser.add_argument("--out-md", type=Path)
    args = parser.parse_args()

    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    contract = json.loads(args.contract.read_text(encoding="utf-8"))
    blocks = [diagnose_block(block, args) for block in contract["blocks"]]
    verdict = "pointwise_constant_route_too_coarse"
    result = {
        "schema": "q3_psdpd_step33_a_pointwise_route_diagnostic.v1",
        "meaning": (
            "Sampled optimistic diagnostic for pointwise-constant chunk bounds. "
            "A positive excess means even sampled min/max chunk constants do "
            "not fit the generated target window bounds."
        ),
        "parameters": {
            "arb_prec": args.arb_prec,
            "samples_per_chunk": args.samples_per_chunk,
            "chunk_size": args.chunk_size,
            "cutoff_t": args.cutoff_t,
            "tail_window_end": args.tail_window_end,
        },
        "verdict": verdict,
        "blocks": blocks,
    }

    for block in blocks:
        print(
            f"{block['label']}: worst finite excess="
            f"{block['worst_finite']['finite_excess']} at d="
            f"{block['worst_finite']['distance']}; worst tail excess="
            f"{block['worst_tail']['tail_excess']} at d="
            f"{block['worst_tail']['distance']}"
        )

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Wrote {args.out_json}")
    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_md(result) + "\n", encoding="utf-8")
        print(f"Wrote {args.out_md}")


if __name__ == "__main__":
    run()
