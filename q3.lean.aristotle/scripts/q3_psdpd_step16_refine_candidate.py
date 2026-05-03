#!/usr/bin/env python3
"""
Step 16 PSD-pd candidate refinement.

Refines the best Step 15 candidate:
  k_spline=9, ell=0.30, delta=0.25, kappa≈3.25

Runs three probes:
  1. local basis sweep around the best candidate
  2. fine kappa sweep around viable kappa
  3. quadrature stability check

Uses the best candidate profile as baseline for profile correlations.

This is a numerical pilot, not a proof-grade certificate.
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

import numpy as np

from q3_psdpd_step13_pilot import PilotParams
from q3_psdpd_step15_kappa_stability import (
    compute_case,
    frange,
    profile_correlation,
)


def parse_float_list(text: str) -> list[float]:
    return [float(x.strip()) for x in text.split(",") if x.strip()]


def parse_int_list(text: str) -> list[int]:
    return [int(x.strip()) for x in text.split(",") if x.strip()]


def fmt(x: float | None, nd: int = 8) -> str:
    if x is None:
        return "NA"
    return f"{x:.{nd}e}"


def write_rows_csv(path: Path, rows: list[dict]) -> None:
    if not rows:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def write_kappa_curve_csv(path: Path, tag: str, res) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            lineterminator="\n",
            fieldnames=[
                "tag",
                "kappa",
                "min_R_eucl",
                "min_R_G",
                "rel_max",
                "margin",
                "pass_cert",
            ],
        )
        writer.writeheader()
        for row in res.kappa_rows:
            writer.writerow(
                {
                    "tag": tag,
                    "kappa": row.kappa,
                    "min_R_eucl": row.min_R_eucl,
                    "min_R_G": row.min_R_G,
                    "rel_max": row.rel_max,
                    "margin": row.margin,
                    "pass_cert": row.pass_cert,
                }
            )


def row_from_result(tag: str, res, baseline_profile, profile_grid) -> dict:
    corr_signed = None
    corr_abs = None
    if baseline_profile is not None:
        corr_signed, corr_abs = profile_correlation(profile_grid, res.profile, baseline_profile)

    return {
        "tag": tag,
        "case_id": res.case_id,
        "L": res.params.L,
        "ell": res.params.ell,
        "delta": res.params.delta,
        "k_spline": res.params.k_spline,
        "arch_tmax": res.params.arch_tmax,
        "arch_nt": res.params.arch_nt,
        "p0_na": res.params.p0_na,
        "n_centers": res.n_centers,
        "dim_boundary_null": res.dim_boundary_null,
        "lambda_CG_min": res.lambda_CG_min,
        "lambda_negP0_G_min": res.lambda_negP0_G_min,
        "kappa_pd_min_grid": res.kappa_pd_min_grid,
        "kappa_viable_min_grid": res.kappa_viable_min_grid,
        "viable_rel_max": res.viable_rel_max,
        "viable_margin": res.viable_margin,
        "best_margin_kappa": res.best_margin_kappa,
        "best_rel_max": res.best_rel_max,
        "best_margin": res.best_margin,
        "profile_corr_signed_to_best": corr_signed,
        "profile_corr_abs_to_best": corr_abs,
        "q_resid_fro": res.q_resid_fro,
        "split_err_fro": res.split_err_fro,
    }


def print_compact(rows: list[dict]) -> None:
    print("\nCompact table")
    print(
        "tag                 k   ell    delta  arch_nt   p0_na   "
        "lam_CG_min      k_viable  margin        best_k  best_margin   corr_best"
    )
    for r in rows:
        print(
            f"{r['tag']:<19} "
            f"{int(r['k_spline']):2d}  "
            f"{r['ell']:5.3f}  "
            f"{r['delta']:5.3f}  "
            f"{int(r['arch_nt']):7d}  "
            f"{int(r['p0_na']):6d}  "
            f"{r['lambda_CG_min']: .6e}  "
            f"{str(r['kappa_viable_min_grid']):>8}  "
            f"{fmt(r['viable_margin'], 6):>12}  "
            f"{str(r['best_margin_kappa']):>6}  "
            f"{fmt(r['best_margin'], 6):>12}  "
            f"{fmt(r['profile_corr_abs_to_best'], 6):>10}"
        )


def run() -> None:
    parser = argparse.ArgumentParser()

    parser.add_argument("--L", type=float, default=3.0)

    parser.add_argument("--best-ell", type=float, default=0.30)
    parser.add_argument("--best-delta", type=float, default=0.25)
    parser.add_argument("--best-k-spline", type=int, default=9)

    parser.add_argument("--ells", type=str, default="0.26,0.28,0.30,0.32,0.34")
    parser.add_argument("--deltas", type=str, default="0.20,0.225,0.25,0.275,0.30")
    parser.add_argument("--k-splines", type=str, default="7,9,11")

    parser.add_argument("--kappa-start", type=float, default=2.50)
    parser.add_argument("--kappa-stop", type=float, default=4.25)
    parser.add_argument("--kappa-step", type=float, default=0.025)

    parser.add_argument("--arch-tmax", type=float, default=260.0)
    parser.add_argument("--arch-nt", type=int, default=48001)
    parser.add_argument("--p0-na", type=int, default=24001)

    parser.add_argument(
        "--quad-variants",
        type=str,
        default="220:36001:18001,260:48001:24001,320:64001:32001",
    )

    parser.add_argument("--profile-n", type=int, default=1601)
    parser.add_argument("--r-eps", type=float, default=1e-10)
    parser.add_argument("--pass-tol", type=float, default=1e-9)
    parser.add_argument(
        "--csv",
        type=str,
        default="q3.lean.aristotle/docs/insights/q3_psdpd_step16_refine.csv",
    )
    parser.add_argument(
        "--kappa-csv",
        type=str,
        default="q3.lean.aristotle/docs/insights/q3_psdpd_step16_kappa_curve.csv",
    )

    args = parser.parse_args()

    ells = parse_float_list(args.ells)
    deltas = parse_float_list(args.deltas)
    k_splines = parse_int_list(args.k_splines)
    kappas = frange(args.kappa_start, args.kappa_stop, args.kappa_step)

    profile_grid = np.linspace(-args.L, args.L, args.profile_n)

    print("== Step 16 candidate refinement ==")
    print(f"Best baseline: k={args.best_k_spline}, ell={args.best_ell}, delta={args.best_delta}")
    print(f"kappa grid={args.kappa_start}:{args.kappa_step}:{args.kappa_stop}")
    print("[WARN] Numerical pilot only, not interval-certified.")

    case_id = 0
    rows: list[dict] = []

    case_id += 1
    best_params = PilotParams(
        L=args.L,
        ell=args.best_ell,
        delta=args.best_delta,
        k_spline=args.best_k_spline,
        arch_tmax=args.arch_tmax,
        arch_nt=args.arch_nt,
        p0_na=args.p0_na,
    )

    best_res = compute_case(
        case_id=case_id,
        params=best_params,
        kappas=kappas,
        profile_grid=profile_grid,
        baseline_profile=None,
        r_eps=args.r_eps,
        pass_tol=args.pass_tol,
    )

    baseline_profile = best_res.profile
    best_row = row_from_result("best_baseline", best_res, baseline_profile, profile_grid)
    rows.append(best_row)
    write_kappa_curve_csv(Path(args.kappa_csv), "best_baseline", best_res)

    print("\n== Best baseline ==")
    print_compact([best_row])

    print("\n== Local basis sweep ==")
    local_rows: list[dict] = []

    for k_spline in k_splines:
        for ell in ells:
            for delta in deltas:
                if (
                    k_spline == args.best_k_spline
                    and abs(ell - args.best_ell) < 1e-14
                    and abs(delta - args.best_delta) < 1e-14
                ):
                    continue

                case_id += 1
                params = PilotParams(
                    L=args.L,
                    ell=ell,
                    delta=delta,
                    k_spline=k_spline,
                    arch_tmax=args.arch_tmax,
                    arch_nt=args.arch_nt,
                    p0_na=args.p0_na,
                )

                res = compute_case(
                    case_id=case_id,
                    params=params,
                    kappas=kappas,
                    profile_grid=profile_grid,
                    baseline_profile=baseline_profile,
                    r_eps=args.r_eps,
                    pass_tol=args.pass_tol,
                )

                row = row_from_result("local_basis", res, baseline_profile, profile_grid)
                local_rows.append(row)
                rows.append(row)

    local_rows_sorted = sorted(
        local_rows,
        key=lambda r: -1e99 if r["best_margin"] is None else r["best_margin"],
        reverse=True,
    )
    print_compact(local_rows_sorted[:20])

    print("\n== Quadrature stability on best candidate ==")
    quad_rows: list[dict] = []

    variants = []
    for item in args.quad_variants.split(","):
        item = item.strip()
        if not item:
            continue
        arch_tmax, arch_nt, p0_na = item.split(":")
        variants.append((float(arch_tmax), int(arch_nt), int(p0_na)))

    for arch_tmax, arch_nt, p0_na in variants:
        case_id += 1
        params = PilotParams(
            L=args.L,
            ell=args.best_ell,
            delta=args.best_delta,
            k_spline=args.best_k_spline,
            arch_tmax=arch_tmax,
            arch_nt=arch_nt,
            p0_na=p0_na,
        )

        res = compute_case(
            case_id=case_id,
            params=params,
            kappas=kappas,
            profile_grid=profile_grid,
            baseline_profile=baseline_profile,
            r_eps=args.r_eps,
            pass_tol=args.pass_tol,
        )

        row = row_from_result("quad_check", res, baseline_profile, profile_grid)
        quad_rows.append(row)
        rows.append(row)

    print_compact(quad_rows)

    print("\n== Top candidates by best_margin ==")
    top_rows = sorted(
        rows,
        key=lambda r: -1e99 if r["best_margin"] is None else r["best_margin"],
        reverse=True,
    )[:25]
    print_compact(top_rows)

    out = Path(args.csv)
    write_rows_csv(out, rows)
    print(f"\nWrote CSV: {out}")
    print(f"Wrote kappa curve CSV: {args.kappa_csv}")


if __name__ == "__main__":
    run()
