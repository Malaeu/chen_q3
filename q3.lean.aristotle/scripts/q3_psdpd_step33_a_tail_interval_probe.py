#!/usr/bin/env python3
"""Probe signed Step33 Arch A tail intervals without mutating payload radii.

This is a diagnostic/generator-shape tool, not a Lean proof producer.  It uses
    the same Step22 acb integrand on a finite positive-tail window [T, U], then
    adds the existing explicit absolute sinc-power remainder bound from U to
    infinity and doubles the result to match Lean's two-sided `TailPart`.
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
        "q3_psdpd_step33_a_tail_interval_probe.py"
    ) from exc

from q3_psdpd_step19_entry_radii import arb_lower_decimal, arb_upper_decimal, set_precision
from q3_psdpd_step22_arch_interval import ArchIntervalBuilder, arch_tail_radius, decimal_range


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"


def load_manifest(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("schema") != "q3_psdpd_step22_arch_finite_tail_components.v1":
        raise ValueError(f"{path}: unexpected schema {payload.get('schema')!r}")
    return payload


def parse_indices(text: str, count: int) -> list[int]:
    if text == "all":
        return list(range(count))
    out: list[int] = []
    for part in text.split(","):
        part = part.strip()
        if not part:
            continue
        value = int(part)
        if value < 0 or value >= count:
            raise ValueError(f"distance index {value} outside [0,{count})")
        out.append(value)
    return out


def integrate_tail_window(builder: ArchIntervalBuilder, d: Decimal, U: Decimal) -> acb:
    total = acb(0)
    points = decimal_range(builder.cutoff_t, U, builder.chunk_size)
    f = builder.integrand(d)
    for left, right in zip(points[:-1], points[1:]):
        total += acb.integral(
            f,
            arb(str(left)),
            arb(str(right)),
            rel_tol=builder.rel_tol,
            abs_tol=builder.abs_tol,
            deg_limit=builder.deg_limit,
            eval_limit=builder.eval_limit,
            depth_limit=builder.depth_limit,
        )
    return total


def decimal_str(x: Decimal) -> str:
    return format(x, ".18E")


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k-spline", type=int, choices=[9, 11], default=11)
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--cutoff-t", type=str, default="260")
    parser.add_argument("--tail-window-end", type=str, default="520")
    parser.add_argument("--chunk-size", type=str, default="10")
    parser.add_argument("--rel-tol", type=str, default="1e-40")
    parser.add_argument("--abs-tol", type=str, default="1e-40")
    parser.add_argument("--deg-limit", type=int, default=64)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=20)
    parser.add_argument("--sinc-terms", type=int, default=90)
    parser.add_argument("--omega-factor", type=str, default="10")
    parser.add_argument("--radius-floor", type=str, default="1e-30")
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--indices", type=str, default="0")
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--out-json", type=Path)
    args = parser.parse_args()

    manifest = args.manifest
    if manifest is None:
        manifest = REQUEST_DIR / f"a_finite_tail_components_k{args.k_spline}.json"
    payload = load_manifest(manifest)
    rows = payload["distances"]
    indices = parse_indices(args.indices, len(rows))

    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    U = Decimal(args.tail_window_end)
    T = Decimal(args.cutoff_t)
    if U <= T:
        raise ValueError("--tail-window-end must be larger than --cutoff-t")

    builder = ArchIntervalBuilder(
        k_spline=args.k_spline,
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
    remainder_radius = Decimal(
        str(
            arch_tail_radius(
                k_spline=args.k_spline,
                ell=Decimal(args.ell),
                cutoff_t=U,
                c_k_lower=builder.c_k_lower,
                omega_factor=Decimal(args.omega_factor),
            )
        )
    )

    out_rows = []
    worst_excess = Decimal("0")
    for idx in indices:
        row = rows[idx]
        d = Decimal(row["distance"])
        generated_tail_radius = Decimal(row["tail_radius"])
        val = integrate_tail_window(builder, d, U).real
        window_lower = arb_lower_decimal(val)
        window_upper = arb_upper_decimal(val)
        positive_tail_lower = window_lower - remainder_radius
        positive_tail_upper = window_upper + remainder_radius
        tail_lower = Decimal(2) * positive_tail_lower
        tail_upper = Decimal(2) * positive_tail_upper
        lower_excess = (-generated_tail_radius) - tail_lower
        upper_excess = tail_upper - generated_tail_radius
        excess = max(Decimal("0"), lower_excess, upper_excess)
        worst_excess = max(worst_excess, excess)
        out_rows.append(
            {
                "index": idx,
                "distance": row["distance"],
                "window_lower": decimal_str(window_lower),
                "window_upper": decimal_str(window_upper),
                "remainder_radius": decimal_str(remainder_radius),
                "positive_tail_lower": decimal_str(positive_tail_lower),
                "positive_tail_upper": decimal_str(positive_tail_upper),
                "tail_lower": decimal_str(tail_lower),
                "tail_upper": decimal_str(tail_upper),
                "generated_tail_radius": decimal_str(generated_tail_radius),
                "fits_generated_tail_radius": excess == 0,
                "excess": decimal_str(excess),
            }
        )
        print(
            f"k={args.k_spline} idx={idx:02d} d={row['distance']} "
            f"tail=[{decimal_str(tail_lower)}, {decimal_str(tail_upper)}] "
            f"R={decimal_str(generated_tail_radius)} excess={decimal_str(excess)}"
        )

    result = {
        "schema": "q3_psdpd_step33_a_signed_tail_probe.v1",
        "meaning": (
            "Diagnostic signed two-sided tail enclosure from acb on the "
            "positive window [T,U] plus the existing explicit absolute "
            "sinc-power remainder from U, doubled to match Lean TailPart. "
            "This is external evidence / generator-shape data, not a Lean "
            "proof."
        ),
        "parameters": {
            "k_spline": args.k_spline,
            "ell": args.ell,
            "cutoff_t": args.cutoff_t,
            "tail_window_end": args.tail_window_end,
            "chunk_size": args.chunk_size,
            "rel_tol": args.rel_tol,
            "abs_tol": args.abs_tol,
            "deg_limit": args.deg_limit,
            "eval_limit": args.eval_limit,
            "depth_limit": args.depth_limit,
            "sinc_terms": args.sinc_terms,
            "omega_factor": args.omega_factor,
            "arb_prec": args.arb_prec,
            "source_manifest": str(manifest),
        },
        "worst_excess": decimal_str(worst_excess),
        "distances": out_rows,
    }
    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Wrote {args.out_json}")


if __name__ == "__main__":
    run()
