#!/usr/bin/env python3
"""Diagnose the raw-Omega Step33 A quadratic comparison route.

This is a sampled Arb diagnostic, not a Lean proof producer.  It checks whether
one distance-indexed quadratic lower/upper comparison function on each finite
and tail window can plausibly fit the current generated raw-Omega integral
targets.

For a window `[L,U]`, write `s = (eta - L) / (U - L)` and

    q(s) = c0 + c1*s + c2*s^2.

The lower LP maximizes `int q` subject to `q(sample) <= sample_lower`.  The
upper LP minimizes `int q` subject to `q(sample) >= sample_upper`.  If the
optimized sampled capacity still misses the target interval, a full-window
quadratic comparison family is already too coarse at sampled points.
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
        "q3_psdpd_step33_rawomega_a_quadratic_route_diagnostic.py"
    ) from exc

try:
    from scipy.optimize import linprog
except ImportError as exc:
    raise SystemExit("scipy is required for this diagnostic") from exc

from q3_psdpd_step19_entry_radii import arb_lower_decimal, arb_upper_decimal, set_precision
from q3_psdpd_step22_arch_interval import ArchIntervalBuilder


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
OUT_JSON = REQUEST_DIR / "rawomega_a_quadratic_route_diagnostic.json"
OUT_MD = REQUEST_DIR / "rawomega_a_quadratic_route_diagnostic.md"

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


def coeff_str(values: list[float], scale: Decimal) -> list[str]:
    return [format(Decimal(str(v)) * scale, ".18E") for v in values]


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
        radius_floor=params.get("radius_floor", "1e-30"),
    )


def sample_times(left: Decimal, right: Decimal, count: int) -> list[Decimal]:
    if count < 3:
        raise ValueError("--samples-per-window must be at least 3")
    width = right - left
    if width <= 0:
        raise ValueError("sample window must have positive width")
    return [left + width * Decimal(i) / Decimal(count) for i in range(1, count + 1)]


def chunk_grid(left: Decimal, right: Decimal, step: Decimal) -> list[tuple[Decimal, Decimal]]:
    if step <= 0:
        raise ValueError(f"chunk step must be positive, got {step}")
    count = (right - left) / step
    if count != count.to_integral_value():
        raise ValueError(f"chunk step {step} does not divide [{left}, {right}]")
    out = []
    for idx in range(int(count)):
        chunk_left = left + step * idx
        out.append((chunk_left, chunk_left + step))
    return out


def eval_bounds(builder: ArchIntervalBuilder, distance: Decimal, eta: Decimal) -> tuple[Decimal, Decimal]:
    val = builder.integrand(distance)(acb(arb(str(eta))), True).real
    return arb_lower_decimal(val), arb_upper_decimal(val)


def scaled_constraints(
    builder: ArchIntervalBuilder,
    distance: Decimal,
    left: Decimal,
    right: Decimal,
    samples_per_window: int,
) -> tuple[list[list[float]], list[Decimal], list[Decimal]]:
    rows: list[list[float]] = []
    lower: list[Decimal] = []
    upper: list[Decimal] = []
    width = right - left
    for eta in sample_times(left, right, samples_per_window):
        s = float((eta - left) / width)
        rows.append([1.0, s, s * s])
        lo, hi = eval_bounds(builder, distance, eta)
        lower.append(lo)
        upper.append(hi)
    return rows, lower, upper


def solve_window(
    builder: ArchIntervalBuilder,
    distance: Decimal,
    left: Decimal,
    right: Decimal,
    samples_per_window: int,
    target_lower: Decimal,
    target_upper: Decimal,
) -> dict:
    rows, lower, upper = scaled_constraints(builder, distance, left, right, samples_per_window)
    width = right - left
    scale_candidates = [abs(x) for x in lower + upper if x != 0]
    scale = max(scale_candidates) if scale_candidates else Decimal(1)
    if scale == 0:
        scale = Decimal(1)

    b_lower = [float(x / scale) for x in lower]
    b_upper = [float(x / scale) for x in upper]
    objective = [float(width), float(width / Decimal(2)), float(width / Decimal(3))]

    lower_lp = linprog(
        c=[-v for v in objective],
        A_ub=rows,
        b_ub=b_lower,
        bounds=[(None, None), (None, None), (None, None)],
        method="highs",
    )
    upper_lp = linprog(
        c=objective,
        A_ub=[[-a for a in row] for row in rows],
        b_ub=[-v for v in b_upper],
        bounds=[(None, None), (None, None), (None, None)],
        method="highs",
    )

    if not lower_lp.success or not upper_lp.success:
        return {
            "left": decimal_str(left),
            "right": decimal_str(right),
            "samples_per_window": samples_per_window,
            "target_lower": decimal_str(target_lower),
            "target_upper": decimal_str(target_upper),
            "lower_lp_success": bool(lower_lp.success),
            "lower_lp_status": str(lower_lp.message),
            "upper_lp_success": bool(upper_lp.success),
            "upper_lp_status": str(upper_lp.message),
            "quadratic_route_not_rejected_by_samples": False,
        }

    lower_integral = Decimal(str(-lower_lp.fun)) * scale
    upper_integral = Decimal(str(upper_lp.fun)) * scale
    lower_excess = max(Decimal(0), target_lower - lower_integral)
    upper_excess = max(Decimal(0), upper_integral - target_upper)
    excess = max(lower_excess, upper_excess)

    return {
        "left": decimal_str(left),
        "right": decimal_str(right),
        "mode": "full_window_quadratic",
        "samples_per_window": samples_per_window,
        "target_lower": decimal_str(target_lower),
        "target_upper": decimal_str(target_upper),
        "sampled_quadratic_lower_capacity": decimal_str(lower_integral),
        "sampled_quadratic_upper_floor": decimal_str(upper_integral),
        "lower_excess": decimal_str(lower_excess),
        "upper_excess": decimal_str(upper_excess),
        "excess": decimal_str(excess),
        "quadratic_route_not_rejected_by_samples": excess == 0,
        "lower_coefficients_scaled_s": coeff_str(list(lower_lp.x), scale),
        "upper_coefficients_scaled_s": coeff_str(list(upper_lp.x), scale),
    }


def solve_piecewise_window(
    builder: ArchIntervalBuilder,
    distance: Decimal,
    left: Decimal,
    right: Decimal,
    chunk_size: Decimal,
    samples_per_chunk: int,
    target_lower: Decimal,
    target_upper: Decimal,
) -> dict:
    chunks = []
    lower_capacity = Decimal(0)
    upper_floor = Decimal(0)
    for chunk_left, chunk_right in chunk_grid(left, right, chunk_size):
        chunk = solve_window(
            builder,
            distance,
            chunk_left,
            chunk_right,
            samples_per_chunk,
            Decimal(0),
            Decimal(0),
        )
        if not chunk.get("quadratic_route_not_rejected_by_samples", False):
            # The per-chunk target passed to solve_window is dummy.  LP success
            # is all that matters here, so keep chunks with ordinary positive
            # dummy excesses.  Only stop on real LP failure.
            if "sampled_quadratic_lower_capacity" not in chunk:
                return {
                    "left": decimal_str(left),
                    "right": decimal_str(right),
                    "mode": "piecewise_quadratic",
                    "chunk_size": decimal_str(chunk_size),
                    "samples_per_chunk": samples_per_chunk,
                    "target_lower": decimal_str(target_lower),
                    "target_upper": decimal_str(target_upper),
                    "quadratic_route_not_rejected_by_samples": False,
                    "failed_chunk": chunk,
                }
        lower_capacity += Decimal(chunk["sampled_quadratic_lower_capacity"])
        upper_floor += Decimal(chunk["sampled_quadratic_upper_floor"])
        chunks.append(chunk)

    lower_excess = max(Decimal(0), target_lower - lower_capacity)
    upper_excess = max(Decimal(0), upper_floor - target_upper)
    excess = max(lower_excess, upper_excess)
    return {
        "left": decimal_str(left),
        "right": decimal_str(right),
        "mode": "piecewise_quadratic",
        "chunk_size": decimal_str(chunk_size),
        "chunk_count": len(chunks),
        "samples_per_chunk": samples_per_chunk,
        "target_lower": decimal_str(target_lower),
        "target_upper": decimal_str(target_upper),
        "sampled_quadratic_lower_capacity": decimal_str(lower_capacity),
        "sampled_quadratic_upper_floor": decimal_str(upper_floor),
        "lower_excess": decimal_str(lower_excess),
        "upper_excess": decimal_str(upper_excess),
        "excess": decimal_str(excess),
        "quadratic_route_not_rejected_by_samples": excess == 0,
        "worst_lower_chunk": min(chunks, key=lambda chunk: Decimal(chunk["sampled_quadratic_lower_capacity"])),
        "worst_upper_chunk": max(chunks, key=lambda chunk: Decimal(chunk["sampled_quadratic_upper_floor"])),
    }


def selected_indices(text: str | None, row_count: int) -> list[int]:
    if not text:
        return list(range(row_count))
    out = []
    for part in text.split(","):
        idx = int(part.strip())
        if idx < 0 or idx >= row_count:
            raise ValueError(f"index {idx} outside 0..{row_count - 1}")
        out.append(idx)
    return sorted(set(out))


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
    indices = selected_indices(args.indices, len(finite_payload["distances"]))

    rows = []
    worst_finite = None
    worst_tail = None
    for idx in indices:
        finite_row = finite_payload["distances"][idx]
        tail_row = tail_rows[idx]
        distance = Decimal(finite_row["distance"])
        finite_mid = Decimal(finite_row["finite_mid"])
        finite_radius = Decimal(finite_row["finite_radius"])
        finite_lower = finite_mid - finite_radius
        finite_upper = finite_mid + finite_radius

        if args.chunk_size:
            finite_diag = solve_piecewise_window(
                builder,
                distance,
                Decimal(0),
                cutoff,
                Decimal(args.chunk_size),
                args.samples_per_window,
                finite_lower,
                finite_upper,
            )
            tail_diag = solve_piecewise_window(
                builder,
                distance,
                cutoff,
                tail_end,
                Decimal(args.chunk_size),
                args.samples_per_window,
                Decimal(tail_row["window_lower"]),
                Decimal(tail_row["window_upper"]),
            )
        else:
            finite_diag = solve_window(
                builder,
                distance,
                Decimal(0),
                cutoff,
                args.samples_per_window,
                finite_lower,
                finite_upper,
            )
            tail_diag = solve_window(
                builder,
                distance,
                cutoff,
                tail_end,
                args.samples_per_window,
                Decimal(tail_row["window_lower"]),
                Decimal(tail_row["window_upper"]),
            )
        row = {
            "index": idx,
            "distance": finite_row["distance"],
            "finite": finite_diag,
            "tail": tail_diag,
        }
        rows.append(row)
        if worst_finite is None or Decimal(row["finite"].get("excess", "Infinity")) > Decimal(
            worst_finite["finite"].get("excess", "Infinity")
        ):
            worst_finite = row
        if worst_tail is None or Decimal(row["tail"].get("excess", "Infinity")) > Decimal(
            worst_tail["tail"].get("excess", "Infinity")
        ):
            worst_tail = row

    assert worst_finite is not None
    assert worst_tail is not None
    return {
        "label": block["label"],
        "k_spline": block["k_spline"],
        "checked_indices": indices,
        "worst_finite": worst_finite,
        "worst_tail": worst_tail,
        "rows": rows,
    }


def render_md(result: dict) -> str:
    lines = [
        "# Raw-Omega A Quadratic Route Diagnostic",
        "",
        "This is a sampled Arb + linear-programming diagnostic, not a Lean proof object.",
        "",
        f"- samples per window: `{result['parameters']['samples_per_window']}`",
        f"- chunk size: `{result['parameters']['chunk_size'] or 'full-window'}`",
        f"- checked indices: `{result['parameters']['indices'] or 'all'}`",
        f"- verdict: `{result['verdict']}`",
        "",
        "Positive excess means the full-window quadratic comparison route is",
        "already too coarse at sampled points.  Zero excess only means the route",
        "is not rejected by samples; Lean still needs pointwise comparison proofs",
        "and scalar integral containments.",
        "",
    ]
    for block in result["blocks"]:
        wf = block["worst_finite"]
        wt = block["worst_tail"]
        lines.extend(
            [
                f"## {block['label']}",
                "",
                f"- checked indices: `{block['checked_indices']}`",
                f"- worst finite: index `{wf['index']}`, distance `{wf['distance']}`, "
                f"excess `{wf['finite'].get('excess', 'lp_failed')}`",
                f"- worst tail: index `{wt['index']}`, distance `{wt['distance']}`, "
                f"excess `{wt['tail'].get('excess', 'lp_failed')}`",
                "",
            ]
        )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--precision", type=int, default=256)
    parser.add_argument("--samples-per-window", type=int, default=257)
    parser.add_argument(
        "--chunk-size",
        default=None,
        help="optional eta-window chunk size; when set, solve one quadratic LP per chunk",
    )
    parser.add_argument(
        "--indices",
        default="22",
        help="comma-separated distance indices to check; default is the worst finite smoke row",
    )
    parser.add_argument("--out-json", type=Path, default=OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=OUT_MD)
    args = parser.parse_args()

    getcontext().prec = 80
    set_precision(args.precision)
    blocks = [diagnose_block(block, args) for block in BLOCKS]
    all_rows = [row for block in blocks for row in block["rows"]]
    rejected = any(
        not row["finite"].get("quadratic_route_not_rejected_by_samples", False)
        or not row["tail"].get("quadratic_route_not_rejected_by_samples", False)
        for row in all_rows
    )
    result = {
        "schema": "q3_psdpd_step33_rawomega_a_quadratic_route_diagnostic.v1",
        "parameters": {
            "precision": args.precision,
            "samples_per_window": args.samples_per_window,
            "chunk_size": args.chunk_size,
            "indices": args.indices,
        },
        "verdict": (
            ("piecewise_quadratic_route_sampled_too_coarse" if args.chunk_size
             else "full_window_quadratic_route_sampled_too_coarse")
            if rejected
            else ("piecewise_quadratic_route_not_rejected_by_samples" if args.chunk_size
                  else "full_window_quadratic_route_not_rejected_by_samples")
        ),
        "blocks": blocks,
    }
    args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out_md.write_text(render_md(result) + "\n", encoding="utf-8")
    print(f"Wrote {args.out_json}")
    print(f"Wrote {args.out_md}")
    print(result["verdict"])


if __name__ == "__main__":
    main()
