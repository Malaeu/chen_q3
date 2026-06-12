#!/usr/bin/env python3
"""
Step33A A-source convention audit.

This diagnostic compares the Step22 Arch source integrand with the active Lean
`centeredBSplineArchKernelProfile` source integrand on the same finite window.
It does not edit CSV/radius payloads and is not a proof object.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal
from pathlib import Path

from flint import acb, arb, ctx

from q3_psdpd_step19_entry_radii import decimal_grid_centers, set_precision, spline_packet_ball
from q3_psdpd_step21_p0_interval import ball_to_mid_rad
from q3_psdpd_step22_arch_interval import ArchIntervalBuilder, sinc_acb


def as_decimal(value) -> Decimal:
    return Decimal(str(value))


def decimal_range(start: Decimal, stop: Decimal, step: Decimal) -> list[Decimal]:
    out: list[Decimal] = []
    x = start
    while x < stop:
        out.append(x)
        x += step
    out.append(stop)
    return out


def integrate_chunks(f, *, cutoff_t: Decimal, chunk_size: Decimal, rel_tol: str, abs_tol: str,
                     deg_limit: int, eval_limit: int, depth_limit: int) -> acb:
    total = acb(0)
    points = decimal_range(Decimal(0), cutoff_t, chunk_size)
    for left, right in zip(points[:-1], points[1:]):
        total += acb.integral(
            f,
            arb(str(left)),
            arb(str(right)),
            rel_tol=arb(rel_tol),
            abs_tol=arb(abs_tol),
            deg_limit=deg_limit,
            eval_limit=eval_limit,
            depth_limit=depth_limit,
        )
    return total


def lean_astar_integrand(*, k_spline: int, ell: str, d: Decimal, sinc_terms: int):
    ell_acb = acb(arb(ell))
    d_acb = acb(arb(str(d)))
    pi_acb = acb(arb.pi())
    two = acb(2)
    i_unit = acb(0, 1)
    s_k, c_k = spline_packet_ball(k_spline)
    s_acb = acb(s_k)
    norm_acb = acb(1) / (acb(s_k) * acb(c_k))
    sinc_power = 2 * k_spline + 2

    def f(t: acb, analytic: bool) -> acb:
        z = acb(arb("0.25")) + i_unit * pi_acb * t
        a_val = arb.pi().log() - z.digamma().real
        a_star = two * pi_acb * acb(a_val)
        x = ell_acb * t / (two * s_acb)
        e2 = norm_acb * (sinc_acb(x, sinc_terms) ** sinc_power)
        return a_star * ell_acb * (t * d_acb).cos() * e2

    return f


def audit_family(*, family: str, k_spline: int, ell: str, L: str, delta: str, args) -> dict:
    builder = ArchIntervalBuilder(
        k_spline=k_spline,
        ell=ell,
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
    centers = decimal_grid_centers(L, ell, delta)
    distances = sorted({abs(centers[j] - centers[i]) for i in range(len(centers)) for j in range(len(centers))})

    rows = []
    for idx, d in enumerate(distances):
        step22_pos = integrate_chunks(
            builder.integrand(d),
            cutoff_t=Decimal(args.cutoff_t),
            chunk_size=Decimal(args.chunk_size),
            rel_tol=args.rel_tol,
            abs_tol=args.abs_tol,
            deg_limit=args.deg_limit,
            eval_limit=args.eval_limit,
            depth_limit=args.depth_limit,
        ).real
        lean_pos = integrate_chunks(
            lean_astar_integrand(k_spline=k_spline, ell=ell, d=d, sinc_terms=args.sinc_terms),
            cutoff_t=Decimal(args.cutoff_t),
            chunk_size=Decimal(args.chunk_size),
            rel_tol=args.rel_tol,
            abs_tol=args.abs_tol,
            deg_limit=args.deg_limit,
            eval_limit=args.eval_limit,
            depth_limit=args.depth_limit,
        ).real

        step22_mid_raw, step22_rad_raw = ball_to_mid_rad(step22_pos)
        lean_mid_raw, lean_rad_raw = ball_to_mid_rad(lean_pos)
        step22_mid = as_decimal(step22_mid_raw)
        step22_rad = as_decimal(step22_rad_raw)
        lean_mid = as_decimal(lean_mid_raw)
        lean_rad = as_decimal(lean_rad_raw)
        step22_full_mid = Decimal(2) * step22_mid
        lean_full_mid = Decimal(2) * lean_mid
        mismatch = abs(lean_full_mid - step22_full_mid)
        rows.append({
            "index": idx,
            "distance": str(d),
            "step22_positive_mid": f"{step22_mid:.30e}",
            "step22_positive_rad": f"{step22_rad:.3e}",
            "step22_full_even_mid": f"{step22_full_mid:.30e}",
            "lean_astar_positive_mid": f"{lean_mid:.30e}",
            "lean_astar_positive_rad": f"{lean_rad:.3e}",
            "lean_astar_full_even_mid": f"{lean_full_mid:.30e}",
            "full_even_mismatch_abs": f"{mismatch:.30e}",
        })

    worst = max(rows, key=lambda row: Decimal(row["full_even_mismatch_abs"]))
    return {
        "family": family,
        "k_spline": k_spline,
        "ell": ell,
        "L": L,
        "delta": delta,
        "rows": rows,
        "worst_full_even_mismatch": worst,
    }


def write_markdown(payload: dict, path: Path) -> None:
    lines = [
        "# Step33A A-source convention audit",
        "",
        "This is a non-mutating diagnostic.  It compares the Step22 `Omega(t)`",
        "finite-window source against the active Lean `Q3.a_star` finite-window",
        "source on the same positive window, then also compares their doubled",
        "even/full-window values.",
        "",
        "It is not a Lean proof object and does not edit `ARadius`, CSV files,",
        "radius-floor data, or global payload radii.",
        "",
        "## Summary",
        "",
    ]
    for family in payload["families"]:
        worst = family["worst_full_even_mismatch"]
        lines.extend([
            f"### {family['family']}",
            "",
            f"- k_spline: `{family['k_spline']}`",
            f"- rows: `{len(family['rows'])}`",
            f"- worst distance index: `{worst['index']}`",
            f"- worst distance: `{worst['distance']}`",
            f"- Step22 full-even midpoint: `{worst['step22_full_even_mid']}`",
            f"- Lean a_star full-even midpoint: `{worst['lean_astar_full_even_mid']}`",
            f"- absolute mismatch: `{worst['full_even_mismatch_abs']}`",
            "",
        ])
    lines.extend([
        "## Interpretation",
        "",
        "A valid local recenter proof cannot identify the current Step22 A payload",
        "with the active Lean `centeredBSplineArchKernelProfile` receiver until the",
        "Arch source convention is chosen and formalized.",
        "",
    ])
    path.write_text("\n".join(lines), encoding="utf-8")


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--cutoff-t", type=str, default="260")
    parser.add_argument("--chunk-size", type=str, default="10")
    parser.add_argument("--rel-tol", type=str, default="1e-40")
    parser.add_argument("--abs-tol", type=str, default="1e-40")
    parser.add_argument("--deg-limit", type=int, default=192)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=128)
    parser.add_argument("--sinc-terms", type=int, default=64)
    parser.add_argument("--omega-factor", type=str, default="10")
    parser.add_argument("--radius-floor", type=str, default="1e-18")
    parser.add_argument("--out-json", type=Path, required=True)
    parser.add_argument("--out-md", type=Path, required=True)
    args = parser.parse_args()

    set_precision(args.arb_prec)
    ctx.dps = max(50, args.arb_prec // 3)

    payload = {
        "schema": "q3_psdpd_step33_a_source_convention_audit.v1",
        "parameters": {
            "arb_prec": args.arb_prec,
            "cutoff_t": args.cutoff_t,
            "chunk_size": args.chunk_size,
            "rel_tol": args.rel_tol,
            "abs_tol": args.abs_tol,
            "deg_limit": args.deg_limit,
            "eval_limit": args.eval_limit,
            "depth_limit": args.depth_limit,
            "sinc_terms": args.sinc_terms,
        },
        "families": [
            audit_family(family="primary", k_spline=11, ell="0.30", L="3.0", delta="0.25", args=args),
            audit_family(family="control", k_spline=9, ell="0.30", L="3.0", delta="0.25", args=args),
        ],
    }

    args.out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(payload, args.out_md)


if __name__ == "__main__":
    run()
