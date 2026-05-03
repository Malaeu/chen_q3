#!/usr/bin/env python3
"""
Step 15 PSD-pd kappa stability + worst-profile stability.

For a grid of parameters, builds:
  G, A, P, P0, Q, N

Checks:
  direct gap:
    lambda_min(C^circ, G^circ), C=A-P

  Green sanity:
    lambda_min(-P0^circ, G^circ)

  kappa split:
    C = (A - kappa P0) - (P - kappa P0)
      = R_kappa - S_kappa

  viable certificate:
    R_kappa^circ positive definite
    lambda_max(S_kappa^circ, R_kappa^circ) <= 1

Also compares worst-vector spatial profiles against baseline.

Notation:
  k_spline = B-spline degree
  r_pow    = prime-power exponent p^r_pow

This is a reconnaissance script, not a proof-grade certificate.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from scipy import linalg

from q3_psdpd_step13_pilot import (
    PilotParams,
    SplinePacket,
    boundary_null_basis,
    build_A,
    build_G,
    build_P,
    build_P0,
    build_Q,
    build_centers,
    sym,
)
from q3_psdpd_step14_worst_vector import h_profile, normalize_by_G


def parse_float_list(text: str) -> list[float]:
    return [float(x.strip()) for x in text.split(",") if x.strip()]


def parse_int_list(text: str) -> list[int]:
    return [int(x.strip()) for x in text.split(",") if x.strip()]


def frange(start: float, stop: float, step: float) -> list[float]:
    if step <= 0:
        raise ValueError("step must be positive")
    out = []
    x = start
    while x <= stop + 0.5 * step:
        out.append(float(x))
        x += step
    return out


def safe_gen_eigs(A: np.ndarray, B: np.ndarray) -> np.ndarray | None:
    try:
        return linalg.eigh(sym(A), sym(B), eigvals_only=True)
    except Exception:
        return None


def profile_correlation(
    u_grid: np.ndarray,
    f: np.ndarray,
    g: np.ndarray,
) -> tuple[float, float]:
    """Return signed and absolute uniform-grid profile correlations."""
    if len(u_grid) < 2:
        return math.nan, math.nan

    du = float(u_grid[1] - u_grid[0])
    ip = float(np.sum(f * g) * du)
    nf = math.sqrt(max(float(np.sum(f * f) * du), 0.0))
    ng = math.sqrt(max(float(np.sum(g * g) * du), 0.0))

    if nf <= 0 or ng <= 0:
        return math.nan, math.nan

    corr = ip / (nf * ng)
    return corr, abs(corr)


@dataclass(frozen=True)
class KappaRow:
    kappa: float
    min_R_eucl: float
    min_R_G: float
    rel_max: float | None
    margin: float | None
    pass_cert: bool


@dataclass(frozen=True)
class CaseResult:
    case_id: int
    params: PilotParams
    n_centers: int
    dim_boundary_null: int
    lambda_CG_min: float
    lambda_CG_max: float
    lambda_negP0_G_min: float
    lambda_negP0_G_max: float
    kappa_pd_min_grid: float | None
    kappa_viable_min_grid: float | None
    viable_margin: float | None
    viable_rel_max: float | None
    best_margin_kappa: float | None
    best_margin: float | None
    best_rel_max: float | None
    q_resid_fro: float
    split_err_fro: float
    profile_corr_signed: float | None
    profile_corr_abs: float | None
    profile: np.ndarray
    kappa_rows: list[KappaRow]


def compute_case(
    case_id: int,
    params: PilotParams,
    kappas: list[float],
    profile_grid: np.ndarray,
    baseline_profile: np.ndarray | None,
    r_eps: float,
    pass_tol: float,
) -> CaseResult:
    packet = SplinePacket.build(params.k_spline)

    centers = build_centers(params)
    D = centers[:, None] - centers[None, :]

    G = build_G(D, params, packet)
    A = build_A(D, params, packet)
    P, _shifts = build_P(D, params, packet)
    P0 = build_P0(D, params, packet)

    C = sym(A - P)
    Pnu = sym(P - P0)
    R1 = sym(A - P0)
    split_err = float(np.linalg.norm(C - sym(R1 - Pnu), ord="fro"))

    Q = build_Q(centers)
    N = boundary_null_basis(Q)
    if N.shape[1] == 0:
        raise RuntimeError("Boundary-null subspace is empty. Increase grid size.")

    Gc = sym(N.T @ G @ N)
    P0c = sym(N.T @ P0 @ N)
    Cc = sym(N.T @ C @ N)
    q_resid = float(np.linalg.norm(Q @ N, ord="fro"))

    eig_CG = safe_gen_eigs(Cc, Gc)
    if eig_CG is None:
        raise RuntimeError("Failed generalized eig(Cc,Gc).")

    eig_negP0_G = safe_gen_eigs(-P0c, Gc)
    if eig_negP0_G is None:
        raise RuntimeError("Failed generalized eig(-P0c,Gc).")

    evals, evecs = linalg.eigh(Cc, Gc)
    x0 = evecs[:, 0]
    v0 = N @ x0
    v0 = normalize_by_G(v0, G)
    profile = h_profile(profile_grid, centers, v0, params.ell, packet)

    corr_signed = None
    corr_abs = None
    if baseline_profile is not None:
        corr_signed, corr_abs = profile_correlation(profile_grid, profile, baseline_profile)

    kappa_rows: list[KappaRow] = []
    kappa_pd_min_grid = None
    kappa_viable_min_grid = None
    viable_margin = None
    viable_rel_max = None
    best_margin = None
    best_margin_kappa = None
    best_rel_max = None

    for kappa in kappas:
        Rk = sym(N.T @ (A - kappa * P0) @ N)
        Sk = sym(N.T @ (P - kappa * P0) @ N)

        eig_R_eucl = np.linalg.eigvalsh(Rk)
        min_R_eucl = float(eig_R_eucl[0])

        eig_R_G = safe_gen_eigs(Rk, Gc)
        min_R_G = float(eig_R_G[0]) if eig_R_G is not None else math.nan

        rel_max = None
        margin = None
        pass_cert = False

        if min_R_eucl > r_eps:
            try:
                eig_rel = linalg.eigh(Sk, Rk, eigvals_only=True)
                rel_max = float(eig_rel[-1])
                margin = 1.0 - rel_max
                pass_cert = rel_max <= 1.0 + pass_tol
            except Exception:
                rel_max = None
                margin = None
                pass_cert = False

        row = KappaRow(
            kappa=kappa,
            min_R_eucl=min_R_eucl,
            min_R_G=min_R_G,
            rel_max=rel_max,
            margin=margin,
            pass_cert=pass_cert,
        )
        kappa_rows.append(row)

        if kappa_pd_min_grid is None and min_R_eucl > r_eps:
            kappa_pd_min_grid = kappa

        if pass_cert and kappa_viable_min_grid is None:
            kappa_viable_min_grid = kappa
            viable_margin = margin
            viable_rel_max = rel_max

        if margin is not None and (best_margin is None or margin > best_margin):
            best_margin = margin
            best_margin_kappa = kappa
            best_rel_max = rel_max

    return CaseResult(
        case_id=case_id,
        params=params,
        n_centers=len(centers),
        dim_boundary_null=N.shape[1],
        lambda_CG_min=float(eig_CG[0]),
        lambda_CG_max=float(eig_CG[-1]),
        lambda_negP0_G_min=float(eig_negP0_G[0]),
        lambda_negP0_G_max=float(eig_negP0_G[-1]),
        kappa_pd_min_grid=kappa_pd_min_grid,
        kappa_viable_min_grid=kappa_viable_min_grid,
        viable_margin=viable_margin,
        viable_rel_max=viable_rel_max,
        best_margin_kappa=best_margin_kappa,
        best_margin=best_margin,
        best_rel_max=best_rel_max,
        q_resid_fro=q_resid,
        split_err_fro=split_err,
        profile_corr_signed=corr_signed,
        profile_corr_abs=corr_abs,
        profile=profile,
        kappa_rows=kappa_rows,
    )


def fmt_optional(x: float | None, digits: int = 8) -> str:
    if x is None:
        return "NA"
    return f"{x:.{digits}e}"


def print_case_summary(res: CaseResult) -> None:
    p = res.params

    print("\n" + "=" * 88)
    print(
        f"case={res.case_id} "
        f"L={p.L} ell={p.ell} delta={p.delta} k_spline={p.k_spline} "
        f"n={res.n_centers} dim0={res.dim_boundary_null}"
    )
    print("-" * 88)
    print(f"lambda_min(Cc,Gc)       = {res.lambda_CG_min:.16e}")
    print(f"lambda_max(Cc,Gc)       = {res.lambda_CG_max:.16e}")
    print(f"lambda_min(-P0c,Gc)     = {res.lambda_negP0_G_min:.16e}")
    print(f"lambda_max(-P0c,Gc)     = {res.lambda_negP0_G_max:.16e}")
    print(f"||Q N||_F               = {res.q_resid_fro:.3e}")
    print(f"||C-(R-Pnu)||_F         = {res.split_err_fro:.3e}")

    print(f"kappa_pd_min_grid       = {res.kappa_pd_min_grid}")
    print(f"kappa_viable_min_grid   = {res.kappa_viable_min_grid}")
    print(f"viable_rel_max          = {fmt_optional(res.viable_rel_max, 16)}")
    print(f"viable_margin           = {fmt_optional(res.viable_margin, 16)}")

    print(f"best_margin_kappa       = {res.best_margin_kappa}")
    print(f"best_rel_max            = {fmt_optional(res.best_rel_max, 16)}")
    print(f"best_margin             = {fmt_optional(res.best_margin, 16)}")

    if res.profile_corr_abs is not None:
        print(f"profile_corr_signed     = {res.profile_corr_signed:.16e}")
        print(f"profile_corr_abs        = {res.profile_corr_abs:.16e}")

    print("\nKappa scan:")
    print("kappa        min_R_eucl          min_R_G             rel_max              margin              pass")
    for row in res.kappa_rows:
        print(
            f"{row.kappa:8.4f}  "
            f"{row.min_R_eucl: .10e}  "
            f"{row.min_R_G: .10e}  "
            f"{fmt_optional(row.rel_max, 10):>18}  "
            f"{fmt_optional(row.margin, 10):>18}  "
            f"{row.pass_cert}"
        )


def write_csv(path: Path, results: list[CaseResult]) -> None:
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            lineterminator="\n",
            fieldnames=[
                "case_id",
                "L",
                "ell",
                "delta",
                "k_spline",
                "n_centers",
                "dim_boundary_null",
                "lambda_CG_min",
                "lambda_negP0_G_min",
                "kappa_pd_min_grid",
                "kappa_viable_min_grid",
                "viable_rel_max",
                "viable_margin",
                "best_margin_kappa",
                "best_rel_max",
                "best_margin",
                "profile_corr_signed",
                "profile_corr_abs",
                "q_resid_fro",
                "split_err_fro",
            ],
        )
        writer.writeheader()

        for r in results:
            p = r.params
            writer.writerow(
                {
                    "case_id": r.case_id,
                    "L": p.L,
                    "ell": p.ell,
                    "delta": p.delta,
                    "k_spline": p.k_spline,
                    "n_centers": r.n_centers,
                    "dim_boundary_null": r.dim_boundary_null,
                    "lambda_CG_min": r.lambda_CG_min,
                    "lambda_negP0_G_min": r.lambda_negP0_G_min,
                    "kappa_pd_min_grid": r.kappa_pd_min_grid,
                    "kappa_viable_min_grid": r.kappa_viable_min_grid,
                    "viable_rel_max": r.viable_rel_max,
                    "viable_margin": r.viable_margin,
                    "best_margin_kappa": r.best_margin_kappa,
                    "best_rel_max": r.best_rel_max,
                    "best_margin": r.best_margin,
                    "profile_corr_signed": r.profile_corr_signed,
                    "profile_corr_abs": r.profile_corr_abs,
                    "q_resid_fro": r.q_resid_fro,
                    "split_err_fro": r.split_err_fro,
                }
            )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()

    parser.add_argument("--L", type=float, default=3.0)
    parser.add_argument("--ells", type=str, default="0.35")
    parser.add_argument("--deltas", type=str, default="0.25")
    parser.add_argument("--k-splines", type=str, default="5")

    parser.add_argument("--arch-tmax", type=float, default=260.0)
    parser.add_argument("--arch-nt", type=int, default=48001)
    parser.add_argument("--p0-na", type=int, default=24001)

    parser.add_argument("--kappa-start", type=float, default=1.0)
    parser.add_argument("--kappa-stop", type=float, default=14.0)
    parser.add_argument("--kappa-step", type=float, default=0.25)

    parser.add_argument("--r-eps", type=float, default=1e-10)
    parser.add_argument("--pass-tol", type=float, default=1e-9)

    parser.add_argument("--profile-n", type=int, default=1201)
    parser.add_argument("--csv", type=str, default="")

    return parser.parse_args()


def main() -> None:
    args = parse_args()

    ells = parse_float_list(args.ells)
    deltas = parse_float_list(args.deltas)
    k_splines = parse_int_list(args.k_splines)
    kappas = frange(args.kappa_start, args.kappa_stop, args.kappa_step)

    profile_grid = np.linspace(-args.L, args.L, args.profile_n)

    print("== Step 15 kappa stability ==")
    print(f"L={args.L}")
    print(f"ells={ells}")
    print(f"deltas={deltas}")
    print(f"k_splines={k_splines}")
    print(f"kappa grid={args.kappa_start}:{args.kappa_step}:{args.kappa_stop}")
    print(f"arch_tmax={args.arch_tmax}, arch_nt={args.arch_nt}, p0_na={args.p0_na}")
    print("[WARN] This is numerical pilot output, not interval-certified.")

    results: list[CaseResult] = []
    baseline_profile: np.ndarray | None = None

    case_id = 0
    for k_spline in k_splines:
        for ell in ells:
            for delta in deltas:
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

                if baseline_profile is None:
                    baseline_profile = res.profile

                print_case_summary(res)
                results.append(res)

    print("\n" + "=" * 88)
    print("Compact summary")
    print("=" * 88)
    print(
        "case  k  ell    delta  lam_CG_min        kappa_viable  "
        "margin            best_kappa  best_margin       corr_abs"
    )

    for r in results:
        p = r.params
        print(
            f"{r.case_id:4d}  "
            f"{p.k_spline:2d}  "
            f"{p.ell:5.3f}  "
            f"{p.delta:5.3f}  "
            f"{r.lambda_CG_min: .6e}  "
            f"{str(r.kappa_viable_min_grid):>12}  "
            f"{fmt_optional(r.viable_margin, 6):>14}  "
            f"{str(r.best_margin_kappa):>10}  "
            f"{fmt_optional(r.best_margin, 6):>14}  "
            f"{fmt_optional(r.profile_corr_abs, 6):>12}"
        )

    if args.csv:
        out = Path(args.csv)
        write_csv(out, results)
        print(f"\nWrote CSV: {out}")


if __name__ == "__main__":
    main()
