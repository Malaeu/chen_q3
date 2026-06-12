#!/usr/bin/env python3
"""Diagnose the raw-Omega Step33 A nonconstant comparison route.

This is not a Lean proof producer.  It checks whether chunkwise constant
comparison functions are already rejected by sampled Arb point data for the
active direct analytic route:

    RawOmegaAAnalyticTailWindowInputs

For a window split into chunks, any certified chunkwise lower comparison must
stay below the integrand on each chunk.  At sampled points this gives an
optimistic lower integral capacity

    sum(chunk_width * min_sample_upper_on_chunk).

Similarly, any certified chunkwise upper comparison must stay above the
integrand, giving an optimistic upper integral floor

    sum(chunk_width * max_sample_lower_on_chunk).

If the generated target lower exceeds the sampled capacity, or the sampled
floor exceeds the target upper, the chunkwise route is too coarse at the
current chunk grid.  If not, the route is only "not rejected by samples"; Lean
still needs real pointwise comparison proofs and scalar integral containments.
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
        "q3_psdpd_step33_rawomega_a_nonconstant_route_diagnostic.py"
    ) from exc

from q3_psdpd_step19_entry_radii import arb_lower_decimal, arb_upper_decimal, set_precision
from q3_psdpd_step22_arch_interval import ArchIntervalBuilder


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
OUT_JSON = REQUEST_DIR / "rawomega_a_nonconstant_route_diagnostic.json"
OUT_MD = REQUEST_DIR / "rawomega_a_nonconstant_route_diagnostic.md"

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
        radius_floor=params.get("radius_floor", "1e-30"),
    )


def sample_times(left: Decimal, right: Decimal, count: int) -> list[Decimal]:
    if count < 1:
        raise ValueError("--samples-per-chunk must be positive")
    width = right - left
    if width <= 0:
        raise ValueError("sample chunk must have positive width")
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


def summarize_chunk(
    builder: ArchIntervalBuilder,
    distance: Decimal,
    left: Decimal,
    right: Decimal,
    samples_per_chunk: int,
) -> dict:
    min_sample_upper: Decimal | None = None
    max_sample_lower: Decimal | None = None
    min_upper_eta: Decimal | None = None
    max_lower_eta: Decimal | None = None

    for eta in sample_times(left, right, samples_per_chunk):
        lo, hi = eval_bounds(builder, distance, eta)
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
    width = right - left
    return {
        "left": decimal_str(left),
        "right": decimal_str(right),
        "width": decimal_str(width),
        "min_sample_upper": decimal_str(min_sample_upper),
        "min_sample_upper_eta": decimal_str(min_upper_eta),
        "max_sample_lower": decimal_str(max_sample_lower),
        "max_sample_lower_eta": decimal_str(max_lower_eta),
        "lower_capacity": decimal_str(width * min_sample_upper),
        "upper_floor": decimal_str(width * max_sample_lower),
    }


def diagnose_window(
    builder: ArchIntervalBuilder,
    distance: Decimal,
    left: Decimal,
    right: Decimal,
    chunk_size: Decimal,
    samples_per_chunk: int,
    target_lower: Decimal,
    target_upper: Decimal,
) -> dict:
    chunks = [
        summarize_chunk(builder, distance, a, b, samples_per_chunk)
        for a, b in chunk_grid(left, right, chunk_size)
    ]
    lower_capacity = sum((Decimal(chunk["lower_capacity"]) for chunk in chunks), Decimal(0))
    upper_floor = sum((Decimal(chunk["upper_floor"]) for chunk in chunks), Decimal(0))
    lower_excess = max(Decimal(0), target_lower - lower_capacity)
    upper_excess = max(Decimal(0), upper_floor - target_upper)
    excess = max(lower_excess, upper_excess)
    return {
        "left": decimal_str(left),
        "right": decimal_str(right),
        "chunk_size": decimal_str(chunk_size),
        "chunk_count": len(chunks),
        "samples_per_chunk": samples_per_chunk,
        "target_lower": decimal_str(target_lower),
        "target_upper": decimal_str(target_upper),
        "sampled_lower_capacity": decimal_str(lower_capacity),
        "sampled_upper_floor": decimal_str(upper_floor),
        "lower_excess": decimal_str(lower_excess),
        "upper_excess": decimal_str(upper_excess),
        "excess": decimal_str(excess),
        "chunkwise_constant_route_not_rejected_by_samples": excess == 0,
        "worst_capacity_chunk": min(chunks, key=lambda chunk: Decimal(chunk["lower_capacity"])),
        "worst_floor_chunk": max(chunks, key=lambda chunk: Decimal(chunk["upper_floor"])),
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
    chunk_size = Decimal(args.chunk_size_override or params["chunk_size"])
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

        finite_diag = diagnose_window(
            builder,
            distance,
            Decimal(0),
            cutoff,
            chunk_size,
            args.samples_per_chunk,
            finite_lower,
            finite_upper,
        )
        tail_diag = diagnose_window(
            builder,
            distance,
            cutoff,
            tail_end,
            chunk_size,
            args.samples_per_chunk,
            tail_lower,
            tail_upper,
        )
        row = {
            "index": idx,
            "distance": finite_row["distance"],
            "finite": finite_diag,
            "tail": tail_diag,
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
        "chunk_size": decimal_str(chunk_size),
        "worst_finite": {
            "index": worst_finite["index"],
            "distance": worst_finite["distance"],
            "finite": worst_finite["finite"],
        },
        "worst_tail": {
            "index": worst_tail["index"],
            "distance": worst_tail["distance"],
            "tail": worst_tail["tail"],
        },
        "rows": rows,
    }


def render_md(result: dict) -> str:
    lines = [
        "# Raw-Omega A Nonconstant Route Diagnostic",
        "",
        "This is sampled Arb route evidence, not a Lean proof object.",
        "",
        f"- samples per chunk: `{result['parameters']['samples_per_chunk']}`",
        f"- verdict: `{result['verdict']}`",
        "",
        "The diagnostic checks the active target:",
        "",
        "```lean",
        "RawOmegaAAnalyticTailWindowInputs",
        "```",
        "",
        "Positive excess means even chunkwise constants on the current grid are",
        "sampled-too-coarse for the generated finite/tail target.  Zero excess",
        "means only that this route is not rejected by sampled point capacity;",
        "Lean still needs checked pointwise comparisons and scalar integral",
        "containments.",
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
                json.dumps(
                    {
                        "index": block["worst_finite"]["index"],
                        "distance": block["worst_finite"]["distance"],
                        "finite": block["worst_finite"]["finite"],
                    },
                    indent=2,
                    sort_keys=True,
                ),
                "```",
                "",
                "Worst tail window:",
                "",
                "```json",
                json.dumps(
                    {
                        "index": block["worst_tail"]["index"],
                        "distance": block["worst_tail"]["distance"],
                        "tail": block["worst_tail"]["tail"],
                    },
                    indent=2,
                    sort_keys=True,
                ),
                "```",
                "",
            ]
        )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--samples-per-chunk", type=int, default=17)
    parser.add_argument(
        "--chunk-size-override",
        default=None,
        help="Optional diagnostic-only chunk size replacing the source payload grid.",
    )
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
        "chunkwise_constant_route_sampled_too_coarse"
        if any_excess
        else "chunkwise_constant_route_not_rejected_by_samples"
    )
    result = {
        "schema": "q3_psdpd_step33_rawomega_a_nonconstant_route_diagnostic.v1",
        "meaning": (
            "Sampled Arb diagnostic for the active raw-Omega nonconstant "
            "comparison route feeding RawOmegaAAnalyticTailWindowInputs."
        ),
        "parameters": {
            "arb_prec": args.arb_prec,
            "samples_per_chunk": args.samples_per_chunk,
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
    args.out_md.write_text(render_md(result).rstrip() + "\n", encoding="utf-8")
    print(f"Wrote {args.out_md}")


if __name__ == "__main__":
    run()
