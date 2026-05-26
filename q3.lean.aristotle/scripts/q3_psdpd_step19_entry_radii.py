#!/usr/bin/env python3
"""
Step 19 PSD-pd entry radii generator.

Generates a radius CSV for Step 18 --mode radius.

Current status:
  - P and Q: generated using python-flint Arb ball arithmetic.
  - A and P0: currently generated from quadrature drift variants.
    This is not proof-grade yet, but lets the Step 18 radius pipeline run.
    Step 20/21 should replace A/P0 drift radii by true Arb interval enclosures.

CSV format:
  matrix,i,j,rad

Notation:
  k_spline = B-spline degree
  r_pow    = prime-power exponent p^r_pow
"""

from __future__ import annotations

import argparse
import csv
import math
from decimal import Decimal, getcontext
from pathlib import Path

import numpy as np

try:
    from flint import arb, ctx
except ImportError as exc:
    raise SystemExit(
        "python-flint is required for Step 19.\n"
        "Install with:\n"
        "  uv add python-flint\n"
    ) from exc

from q3_psdpd_step13_pilot import (
    PilotParams,
    SplinePacket,
    build_A,
    build_P,
    build_P0,
    build_Q,
    build_centers,
    sieve_primes,
)


def set_precision(bits: int) -> None:
    ctx.prec = bits
    getcontext().prec = max(80, bits // 3)


def arb_lower_decimal(x: arb) -> Decimal:
    return Decimal(x.lower().str(90, radius=False))


def arb_upper_decimal(x: arb) -> Decimal:
    return Decimal(x.upper().str(90, radius=False))


def arb_interval_from_decimals(lo: Decimal, hi: Decimal) -> arb:
    if hi < lo:
        lo, hi = hi, lo
    mid = (lo + hi) / Decimal(2)
    rad = (hi - lo) / Decimal(2)
    return arb(str(mid), str(rad))


def arb_radius_against_float(x: arb, midpoint_float: float) -> float:
    """
    Return a decimal radius covering the Arb ball x around midpoint_float.

    Step 18 stores only radii around the existing double midpoint, serialized
    as .18e in the CSV.  Measure against that exact decimal, because Lean
    imports the CSV text rather than Decimal(str(float)).
    """
    lo = arb_lower_decimal(x)
    hi = arb_upper_decimal(x)
    mid = Decimal(f"{float(midpoint_float):.18e}")
    rad = max(abs(mid - lo), abs(hi - mid))
    return float(rad * Decimal("1.0000000001") + Decimal("1e-80"))


def positive_part_power_ball(x: arb, deg: int) -> arb:
    """Enclose (max(x, 0))^deg for real ball x."""
    lo = arb_lower_decimal(x)
    hi = arb_upper_decimal(x)

    if hi <= 0:
        return arb(0)
    if lo >= 0:
        return x**deg

    return arb_interval_from_decimals(Decimal(0), hi**deg)


def centered_bspline_ball(deg: int, x: arb) -> arb:
    """
    Interval version of centered cardinal B-spline b_deg.

    b_deg(x) = 1/deg! * sum_j (-1)^j C(deg+1,j)
               (x + (deg+1)/2 - j)_+^deg
    """
    if deg == 0:
        lo = arb_lower_decimal(x)
        hi = arb_upper_decimal(x)
        if hi < Decimal("-0.5") or lo > Decimal("0.5"):
            return arb(0)
        return arb_interval_from_decimals(Decimal(0), Decimal(1))

    y = x + arb(str(Decimal(deg + 1) / Decimal(2)))
    out = arb(0)

    for j in range(deg + 2):
        coeff = arb(((-1) ** j) * math.comb(deg + 1, j))
        out += coeff * positive_part_power_ball(y - arb(j), deg)

    out /= arb(math.factorial(deg))
    return out


def spline_packet_ball(k_spline: int) -> tuple[arb, arb]:
    """
    Return (s_k, c_k) as Arb balls.

    s_k = (k+1)/2
    c_k = b_{2k+1}(0)
    """
    s_k = arb(str(Decimal(k_spline + 1) / Decimal(2)))
    c_k = centered_bspline_ball(2 * k_spline + 1, arb(0))
    return s_k, c_k


def r_corr_ball(x: arb, k_spline: int, s_k: arb, c_k: arb) -> arb:
    """r_k(x) = b_{2k+1}(s_k x) / c_k."""
    return centered_bspline_ball(2 * k_spline + 1, s_k * x) / c_k


def decimal_grid_centers(L: str, ell: str, delta: str) -> list[Decimal]:
    """
    Match Step 13's center rule:
      u_j from -L+ell to L-ell+0.5*delta, step delta.
    """
    Ld = Decimal(L)
    elld = Decimal(ell)
    deltad = Decimal(delta)

    start = -Ld + elld
    stop_guard = Ld - elld + Decimal("0.5") * deltad

    centers: list[Decimal] = []
    u = start
    while u <= stop_guard:
        centers.append(u)
        u += deltad

    return centers


def prime_power_shifts_ball(L: str) -> list[tuple[arb, arb, int, int]]:
    """
    Return (a, weight, p, r_pow), where:
      a = r_pow * log(p)
      weight = log(p) * exp(-a/2)
    """
    Ld = Decimal(L)
    max_n = int(np.floor(np.exp(float(Decimal(2) * Ld)))) + 1
    primes = sieve_primes(max_n)

    cutoff = arb(str(Decimal(2) * Ld))
    shifts: list[tuple[arb, arb, int, int]] = []

    for p in primes:
        logp = arb(p).log()
        r_pow = 1

        while True:
            a = arb(r_pow) * logp
            if arb_lower_decimal(a - cutoff) > 0:
                break

            weight = logp * (-a / arb(2)).exp()
            shifts.append((a, weight, p, r_pow))
            r_pow += 1

    return shifts


def build_P_radius_arb(
    base_P: np.ndarray,
    centers_dec: list[Decimal],
    L: str,
    ell: str,
    k_spline: int,
) -> np.ndarray:
    """Build entry radii for P using Arb intervals."""
    n = len(centers_dec)
    ell_ball = arb(ell)
    s_k, c_k = spline_packet_ball(k_spline)
    shifts = prime_power_shifts_ball(L)

    radii = np.zeros_like(base_P, dtype=float)
    centers_ball = [arb(str(u)) for u in centers_dec]

    for i in range(n):
        for j in range(n):
            d = centers_ball[i] - centers_ball[j]
            val = arb(0)

            for a, weight, _p, _r_pow in shifts:
                arg1 = (d - a) / ell_ball
                arg2 = (d + a) / ell_ball
                val += weight * (
                    r_corr_ball(arg1, k_spline, s_k, c_k)
                    + r_corr_ball(arg2, k_spline, s_k, c_k)
                )

            radii[i, j] = arb_radius_against_float(val, float(base_P[i, j]))

    return np.maximum(radii, radii.T)


def build_Q_radius_arb(base_Q: np.ndarray, centers_dec: list[Decimal]) -> np.ndarray:
    """Build entry radii for Q."""
    radii = np.zeros_like(base_Q, dtype=float)

    for j, u in enumerate(centers_dec):
        u_ball = arb(str(u))
        q0 = (u_ball / arb(2)).exp()
        q1 = (-u_ball / arb(2)).exp()

        radii[0, j] = arb_radius_against_float(q0, float(base_Q[0, j]))
        radii[1, j] = arb_radius_against_float(q1, float(base_Q[1, j]))

    return radii


def parse_quad_variants(text: str) -> list[tuple[float, int, int]]:
    variants = []
    for raw in text.split(","):
        raw = raw.strip()
        if not raw:
            continue
        a, b, c = raw.split(":")
        variants.append((float(a), int(b), int(c)))
    return variants


def drift_radii_A_P0(
    base_params: PilotParams,
    base_A: np.ndarray,
    base_P0: np.ndarray,
    variants: list[tuple[float, int, int]],
) -> tuple[np.ndarray, np.ndarray]:
    """
    Empirical quadrature drift radii for A and P0.

    This is not proof-grade. It keeps Step 18 radius-mode plumbing live while
    Step 20/21 replace these by true intervals.
    """
    centers = build_centers(base_params)
    D = centers[:, None] - centers[None, :]
    packet = SplinePacket.build(base_params.k_spline)

    rad_A = np.zeros_like(base_A, dtype=float)
    rad_P0 = np.zeros_like(base_P0, dtype=float)

    for arch_tmax, arch_nt, p0_na in variants:
        params = PilotParams(
            L=base_params.L,
            ell=base_params.ell,
            delta=base_params.delta,
            k_spline=base_params.k_spline,
            arch_tmax=arch_tmax,
            arch_nt=arch_nt,
            p0_na=p0_na,
        )

        A_v = build_A(D, params, packet)
        P0_v = build_P0(D, params, packet)

        rad_A = np.maximum(rad_A, np.abs(A_v - base_A))
        rad_P0 = np.maximum(rad_P0, np.abs(P0_v - base_P0))

    rad_A *= 2.0
    rad_P0 *= 2.0

    return np.maximum(rad_A, rad_A.T), np.maximum(rad_P0, rad_P0.T)


def write_radius_csv(
    path: Path,
    rad_A: np.ndarray,
    rad_P: np.ndarray,
    rad_P0: np.ndarray,
    rad_Q: np.ndarray,
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    with path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=["matrix", "i", "j", "rad"],
            lineterminator="\n",
        )
        writer.writeheader()

        for name, M in [("A", rad_A), ("P", rad_P), ("P0", rad_P0)]:
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

        n, m = rad_Q.shape
        for i in range(n):
            for j in range(m):
                writer.writerow(
                    {
                        "matrix": "Q",
                        "i": i,
                        "j": j,
                        "rad": f"{float(rad_Q[i, j]):.18e}",
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
        "--out",
        type=str,
        default="q3.lean.aristotle/docs/insights/q3_psdpd_step19_entry_radii.csv",
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

    print("== Step 19 entry radii generator ==")
    print(f"L={args.L}, ell={args.ell}, delta={args.delta}, k_spline={args.k_spline}")
    print(f"arb_prec={args.arb_prec}")
    print("[INFO] P and Q radii use Arb ball arithmetic.")
    print("[WARN] A and P0 radii currently use quadrature drift, not proof-grade intervals.")

    centers_float = build_centers(params)
    centers_dec = decimal_grid_centers(args.L, args.ell, args.delta)

    if len(centers_float) != len(centers_dec):
        raise RuntimeError(
            f"Center count mismatch: Step13={len(centers_float)}, Decimal={len(centers_dec)}"
        )

    D = centers_float[:, None] - centers_float[None, :]
    packet = SplinePacket.build(args.k_spline)

    base_A = build_A(D, params, packet)
    base_P, _shifts = build_P(D, params, packet)
    base_P0 = build_P0(D, params, packet)
    base_Q = build_Q(centers_float)

    print("Building Arb radii for P...")
    rad_P = build_P_radius_arb(
        base_P=base_P,
        centers_dec=centers_dec,
        L=args.L,
        ell=args.ell,
        k_spline=args.k_spline,
    )

    print("Building Arb radii for Q...")
    rad_Q = build_Q_radius_arb(base_Q=base_Q, centers_dec=centers_dec)

    print("Building drift radii for A/P0...")
    variants = parse_quad_variants(args.quad_variants)
    rad_A, rad_P0 = drift_radii_A_P0(
        base_params=params,
        base_A=base_A,
        base_P0=base_P0,
        variants=variants,
    )

    out = Path(args.out)
    write_radius_csv(out, rad_A=rad_A, rad_P=rad_P, rad_P0=rad_P0, rad_Q=rad_Q)

    print("\n== Radius summary ==")
    print(f"max rad(A)  = {np.max(rad_A):.16e}  [drift]")
    print(f"max rad(P)  = {np.max(rad_P):.16e}  [Arb]")
    print(f"max rad(P0) = {np.max(rad_P0):.16e}  [drift]")
    print(f"max rad(Q)  = {np.max(rad_Q):.16e}  [Arb]")
    print(f"Wrote: {out}")


if __name__ == "__main__":
    run()
