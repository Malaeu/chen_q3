#!/usr/bin/env python3
"""
Step 20 PSD-pd midpoint/radius contract generator.

Purpose:
  Generate both:
    midpoint CSV: matrix,i,j,mid
    radius CSV:   matrix,i,j,rad

Why:
  Step 19 found that for high-degree B-splines, especially k=11,
  Arb evaluation of P disagrees with the current float midpoint evaluator.
  A radius around the wrong midpoint destroys the certificate.

Current method:
  - P and Q: Arb midpoint + Arb radius.
  - A and P0: float midpoint + drift radius for now.
    These remain Step 21/22 proof-grade targets.

Notation:
  k_spline = B-spline degree
  r_pow    = prime-power exponent p^r_pow
"""

from __future__ import annotations

import argparse
import csv
from decimal import Decimal
from pathlib import Path

import numpy as np

try:
    from flint import arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required.\n"
        "Install with:\n"
        "  uv add python-flint\n"
    ) from exc

from q3_psdpd_step13_pilot import (
    PilotParams,
    SplinePacket,
    build_A,
    build_P,
    build_P0,
    build_centers,
    sym,
)
from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    decimal_grid_centers,
    drift_radii_A_P0,
    parse_quad_variants,
    prime_power_shifts_ball,
    r_corr_ball,
    set_precision,
    spline_packet_ball,
)


def ball_to_mid_rad(x: arb) -> tuple[float, float]:
    """
    Convert an Arb ball to a float midpoint and radius that covers the ball.

    The radius is around the chosen float midpoint, not around the exact
    decimal midpoint.
    """
    lo = arb_lower_decimal(x)
    hi = arb_upper_decimal(x)

    mid_dec = (lo + hi) / Decimal(2)
    mid_float = float(mid_dec)
    mid_float_dec = Decimal(str(mid_float))

    rad = max(abs(mid_float_dec - lo), abs(hi - mid_float_dec))
    rad = rad * Decimal("1.0000000001") + Decimal("1e-80")

    return mid_float, float(rad)


def symmetrize_midrad(M: np.ndarray, R: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Symmetrize midpoint matrix and enlarge radii so both directions are covered."""
    n = M.shape[0]
    Ms = M.copy()
    Rs = R.copy()

    for i in range(n):
        for j in range(i + 1, n):
            mid = 0.5 * (M[i, j] + M[j, i])
            rad_ij = R[i, j] + abs(M[i, j] - mid)
            rad_ji = R[j, i] + abs(M[j, i] - mid)
            rad = max(rad_ij, rad_ji)

            Ms[i, j] = mid
            Ms[j, i] = mid
            Rs[i, j] = rad
            Rs[j, i] = rad

    return Ms, Rs


def build_P_midrad_arb(
    centers_dec: list[Decimal],
    L: str,
    ell: str,
    k_spline: int,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Arb midpoint/radius for P.

    P_ij =
      sum_{r log p <= 2L} log(p)/p^(r/2)
      [ r_k((d-a)/ell) + r_k((d+a)/ell) ].
    """
    n = len(centers_dec)
    M = np.zeros((n, n), dtype=float)
    R = np.zeros((n, n), dtype=float)

    ell_ball = arb(ell)
    s_k, c_k = spline_packet_ball(k_spline)
    shifts = prime_power_shifts_ball(L)
    centers_ball = [arb(str(u)) for u in centers_dec]

    for i in range(n):
        for j in range(n):
            d = centers_ball[i] - centers_ball[j]
            val = arb(0)

            for a, weight, _p, _r_pow in shifts:
                val += weight * (
                    r_corr_ball((d - a) / ell_ball, k_spline, s_k, c_k)
                    + r_corr_ball((d + a) / ell_ball, k_spline, s_k, c_k)
                )

            M[i, j], R[i, j] = ball_to_mid_rad(val)

    return symmetrize_midrad(M, R)


def build_Q_midrad_arb(centers_dec: list[Decimal]) -> tuple[np.ndarray, np.ndarray]:
    """
    Arb midpoint/radius for Q.

    Q rows:
      exp(u_j/2)
      exp(-u_j/2)
    """
    n = len(centers_dec)
    M = np.zeros((2, n), dtype=float)
    R = np.zeros((2, n), dtype=float)

    for j, u in enumerate(centers_dec):
        u_ball = arb(str(u))

        q0 = (u_ball / arb(2)).exp()
        q1 = (-u_ball / arb(2)).exp()

        M[0, j], R[0, j] = ball_to_mid_rad(q0)
        M[1, j], R[1, j] = ball_to_mid_rad(q1)

    return M, R


def write_mid_csv(path: Path, mids: dict[str, np.ndarray]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["matrix", "i", "j", "mid"], lineterminator="\n")
        writer.writeheader()

        for name, M in mids.items():
            n, m = M.shape
            for i in range(n):
                for j in range(m):
                    writer.writerow(
                        {
                            "matrix": name,
                            "i": i,
                            "j": j,
                            "mid": f"{float(M[i, j]):.18e}",
                        }
                    )


def write_rad_csv(path: Path, rads: dict[str, np.ndarray]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["matrix", "i", "j", "rad"], lineterminator="\n")
        writer.writeheader()

        for name, M in rads.items():
            n, m = M.shape
            for i in range(n):
                for j in range(m):
                    writer.writerow(
                        {
                            "matrix": name,
                            "i": i,
                            "j": j,
                            "rad": f"{float(M[i, j]):.18e}",
                        }
                    )


def run() -> None:
    parser = argparse.ArgumentParser()

    parser.add_argument("--L", type=str, default="3.0")
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--delta", type=str, default="0.25")
    parser.add_argument("--k-spline", type=int, default=11)

    parser.add_argument("--arch-tmax", type=float, default=260.0)
    parser.add_argument("--arch-nt", type=int, default=48001)
    parser.add_argument("--p0-na", type=int, default=24001)
    parser.add_argument("--arb-prec", type=int, default=256)

    parser.add_argument(
        "--quad-variants",
        type=str,
        default="220:36001:18001,260:48001:24001,320:64001:32001",
    )

    parser.add_argument(
        "--out-mid",
        type=str,
        default="q3.lean.aristotle/docs/insights/q3_psdpd_step20_midpoints.csv",
    )

    parser.add_argument(
        "--out-rad",
        type=str,
        default="q3.lean.aristotle/docs/insights/q3_psdpd_step20_radii.csv",
    )

    args = parser.parse_args()
    set_precision(args.arb_prec)

    params = PilotParams(
        L=float(args.L),
        ell=float(args.ell),
        delta=float(args.delta),
        k_spline=args.k_spline,
        arch_tmax=args.arch_tmax,
        arch_nt=args.arch_nt,
        p0_na=args.p0_na,
    )

    print("== Step 20 midpoint/radius contract ==")
    print(f"L={args.L}, ell={args.ell}, delta={args.delta}, k_spline={args.k_spline}")
    print(f"arb_prec={args.arb_prec}")
    print("[INFO] P/Q midpoint+radii use Arb.")
    print("[WARN] A/P0 midpoint use float midpoint; A/P0 radii use drift for now.")

    centers_float = build_centers(params)
    centers_dec = decimal_grid_centers(args.L, args.ell, args.delta)

    if len(centers_float) != len(centers_dec):
        raise RuntimeError(
            f"Center count mismatch: float={len(centers_float)}, decimal={len(centers_dec)}"
        )

    D = centers_float[:, None] - centers_float[None, :]
    packet = SplinePacket.build(args.k_spline)

    print("Building float midpoint A/P0...")
    mid_A = build_A(D, params, packet)
    mid_P0 = build_P0(D, params, packet)

    print("Building Arb midpoint/radius P...")
    mid_P, rad_P = build_P_midrad_arb(
        centers_dec=centers_dec,
        L=args.L,
        ell=args.ell,
        k_spline=args.k_spline,
    )

    print("Building Arb midpoint/radius Q...")
    mid_Q, rad_Q = build_Q_midrad_arb(centers_dec)

    print("Building drift radii A/P0...")
    variants = parse_quad_variants(args.quad_variants)
    rad_A, rad_P0 = drift_radii_A_P0(
        base_params=params,
        base_A=mid_A,
        base_P0=mid_P0,
        variants=variants,
    )

    mids = {
        "A": sym(mid_A),
        "P": sym(mid_P),
        "P0": sym(mid_P0),
        "Q": mid_Q,
    }

    rads = {
        "A": sym(rad_A),
        "P": sym(rad_P),
        "P0": sym(rad_P0),
        "Q": rad_Q,
    }

    out_mid = Path(args.out_mid)
    out_rad = Path(args.out_rad)

    write_mid_csv(out_mid, mids)
    write_rad_csv(out_rad, rads)

    old_float_P, _ = build_P(D, params, packet)
    diff_P = np.linalg.norm(sym(old_float_P - mid_P), ord=2)

    print("\n== Contract summary ==")
    print(f"n_centers       = {len(centers_float)}")
    print(f"||P_float-P_arb_mid||_2 = {diff_P:.16e}")
    print(f"max rad(A)      = {np.max(rad_A):.16e}  [drift]")
    print(f"max rad(P)      = {np.max(rad_P):.16e}  [Arb]")
    print(f"max rad(P0)     = {np.max(rad_P0):.16e}  [drift]")
    print(f"max rad(Q)      = {np.max(rad_Q):.16e}  [Arb]")
    print(f"Wrote midpoint CSV: {out_mid}")
    print(f"Wrote radius CSV:   {out_rad}")


if __name__ == "__main__":
    run()
