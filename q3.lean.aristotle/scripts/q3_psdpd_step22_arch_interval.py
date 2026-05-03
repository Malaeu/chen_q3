#!/usr/bin/env python3
"""
Step 22 PSD-pd Arch interval patcher.

Purpose:
  Replace A rows in existing midpoint/radius CSV files by Arb/acb-backed
  midpoint + radius values for the Arch matrix

    A_ij = ell/pi * int_0^infty Omega(t) |E_{ell,k}(it)|^2 cos(t d_ij) dt.

Input:
  midpoint CSV from Step 21
  radius CSV from Step 21

Output:
  patched midpoint CSV
  patched radius CSV

Status:
  - A becomes interval-backed by acb.integral on [0,T] plus an explicit
    sinc-power tail radius.
  - P, Q, P0 remain whatever the input CSVs contain, normally Arb-backed.
"""

from __future__ import annotations

import argparse
import math
from decimal import Decimal, getcontext
from pathlib import Path

import numpy as np

try:
    from flint import acb, arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required.\n"
        "Install with:\n"
        "  uv add python-flint\n"
    ) from exc

from q3_psdpd_step13_pilot import PilotParams, SplinePacket, build_A, build_centers, sym
from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    decimal_grid_centers,
    set_precision,
    spline_packet_ball,
)
from q3_psdpd_step21_p0_interval import (
    ball_to_mid_rad,
    read_matrix_csv,
    write_matrix_csv,
)


def decimal_range(start: Decimal, stop: Decimal, step: Decimal) -> list[Decimal]:
    if step <= 0:
        raise ValueError("step must be positive")

    out: list[Decimal] = []
    x = start
    while x < stop:
        out.append(x)
        x += step
    out.append(stop)
    return out


def sinc_acb(x: acb, terms: int) -> acb:
    """
    Entire sinc(x)=sin(x)/x.

    The direct quotient is fine away from zero. If an acb ball contains zero,
    use the Taylor series so the callback remains analytic for acb.integral.
    """
    if float(x.abs_lower()) > 0.0:
        return x.sin() / x

    total = acb(0)
    x2 = x * x
    power = acb(1)

    for n in range(terms):
        coeff = arb((-1) ** n) / arb(math.factorial(2 * n + 1))
        total += acb(coeff) * power
        power *= x2

    return total


def arch_tail_radius(
    *,
    k_spline: int,
    ell: Decimal,
    cutoff_t: Decimal,
    c_k_lower: Decimal,
    omega_factor: Decimal,
) -> float:
    """
    Conservative common tail radius for all d.

    For t >= T, use:
      |sinc(ell*t/(2s))| <= 2s/(ell*t)
      |Omega(t)| <= omega_factor * log(2+t)

    The log integral is bounded by log(3t) for t >= 1:
      int_T^inf log(3t) t^(-q) dt
      = T^(1-q) * (log(3T)/(q-1) + 1/(q-1)^2).

    This script records a finite certificate artifact; the corresponding
    analytic omega bound is the reusable theorem statement to formalize later.
    """
    if cutoff_t <= 1:
        raise ValueError("cutoff_t must be > 1 for this tail bound")
    if c_k_lower <= 0:
        raise ValueError("c_k lower bound must be positive")

    q = 2 * k_spline + 2
    s_k = Decimal(k_spline + 1) / Decimal(2)
    T = cutoff_t

    # Decimal has no natural log in older Python versions, so use a float log
    # and then inflate via the deliberately coarse omega_factor.
    log_3T = Decimal(str(math.log(float(Decimal(3) * T))))
    q_minus = Decimal(q - 1)
    integral = (T ** Decimal(1 - q)) * (log_3T / q_minus + Decimal(1) / (q_minus * q_minus))

    prefactor = (
        ell
        / Decimal(str(math.pi))
        * (Decimal(1) / (s_k * c_k_lower))
        * ((Decimal(2) * s_k / ell) ** q)
        * omega_factor
    )

    return float(prefactor * integral)


class ArchIntervalBuilder:
    def __init__(
        self,
        *,
        k_spline: int,
        ell: str,
        cutoff_t: str,
        chunk_size: str,
        rel_tol: str,
        abs_tol: str,
        deg_limit: int,
        eval_limit: int,
        depth_limit: int,
        sinc_terms: int,
        omega_factor: str,
        radius_floor: str,
    ) -> None:
        self.k_spline = k_spline
        self.ell_dec = Decimal(ell)
        self.cutoff_t = Decimal(cutoff_t)
        self.chunk_size = Decimal(chunk_size)
        self.rel_tol = arb(rel_tol)
        self.abs_tol = arb(abs_tol)
        self.deg_limit = deg_limit
        self.eval_limit = eval_limit
        self.depth_limit = depth_limit
        self.sinc_terms = sinc_terms
        self.radius_floor = float(Decimal(radius_floor))

        self.ell = arb(ell)
        self.s_k, self.c_k = spline_packet_ball(k_spline)
        self.c_k_lower = arb_lower_decimal(self.c_k)
        self.pi = arb.pi()
        self.log_pi = self.pi.log()
        self.i_unit = acb(0, 1)
        self.norm = arb(1) / (self.s_k * self.c_k)
        self.sinc_power = 2 * k_spline + 2
        self.tail_radius = arch_tail_radius(
            k_spline=k_spline,
            ell=self.ell_dec,
            cutoff_t=self.cutoff_t,
            c_k_lower=self.c_k_lower,
            omega_factor=Decimal(omega_factor),
        )

    def integrand(self, d: Decimal):
        d_acb = acb(arb(str(d)))
        ell_acb = acb(self.ell)
        pi_acb = acb(self.pi)
        norm_acb = acb(self.norm)
        two = acb(2)
        s_acb = acb(self.s_k)

        def f(t: acb, analytic: bool) -> acb:
            z = acb(arb("0.25")) + self.i_unit * t / two
            omega = z.digamma().real - self.log_pi
            x = ell_acb * t / (two * s_acb)
            e2 = norm_acb * (sinc_acb(x, self.sinc_terms) ** self.sinc_power)
            return (ell_acb / pi_acb) * acb(omega) * e2 * (t * d_acb).cos()

        return f

    def finite_integral(self, d: Decimal) -> acb:
        total = acb(0)
        points = decimal_range(Decimal(0), self.cutoff_t, self.chunk_size)
        f = self.integrand(d)

        for left, right in zip(points[:-1], points[1:]):
            total += acb.integral(
                f,
                arb(str(left)),
                arb(str(right)),
                rel_tol=self.rel_tol,
                abs_tol=self.abs_tol,
                deg_limit=self.deg_limit,
                eval_limit=self.eval_limit,
                depth_limit=self.depth_limit,
            )

        return total

    def entry_mid_rad(self, d_abs: Decimal) -> tuple[float, float]:
        val = self.finite_integral(d_abs)
        mid, rad = ball_to_mid_rad(val.real)
        rad += self.tail_radius + self.radius_floor
        return mid, rad


def build_A_midrad_arch(
    *,
    centers_dec: list[Decimal],
    builder: ArchIntervalBuilder,
) -> tuple[np.ndarray, np.ndarray]:
    n = len(centers_dec)
    mids = np.zeros((n, n), dtype=float)
    rads = np.zeros((n, n), dtype=float)

    unique_d = sorted({abs(centers_dec[j] - centers_dec[i]) for i in range(n) for j in range(n)})
    values: dict[Decimal, tuple[float, float]] = {}

    print(f"Unique Arch distances: {len(unique_d)}")
    print(f"Common tail radius: {builder.tail_radius:.16e}")

    for idx, d in enumerate(unique_d, 1):
        mid, rad = builder.entry_mid_rad(d)
        values[d] = (mid, rad)
        print(f"[{idx:03d}/{len(unique_d):03d}] d={d} mid={mid:.16e} rad={rad:.16e}")

    for i in range(n):
        for j in range(n):
            d_abs = abs(centers_dec[j] - centers_dec[i])
            mids[i, j], rads[i, j] = values[d_abs]

    return sym(mids), sym(rads)


def run() -> None:
    parser = argparse.ArgumentParser()

    parser.add_argument("--L", type=str, default="3.0")
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--delta", type=str, default="0.25")
    parser.add_argument("--k-spline", type=int, default=11)
    parser.add_argument("--arb-prec", type=int, default=256)

    parser.add_argument("--cutoff-t", type=str, default="260")
    parser.add_argument("--chunk-size", type=str, default="10")
    parser.add_argument("--rel-tol", type=str, default="1e-40")
    parser.add_argument("--abs-tol", type=str, default="1e-40")
    parser.add_argument("--deg-limit", type=int, default=64)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=20)
    parser.add_argument("--sinc-terms", type=int, default=90)
    parser.add_argument("--omega-factor", type=str, default="10")
    parser.add_argument("--radius-floor", type=str, default="1e-30")

    parser.add_argument("--in-mid", type=str, required=True)
    parser.add_argument("--in-rad", type=str, required=True)
    parser.add_argument("--out-mid", type=str, required=True)
    parser.add_argument("--out-rad", type=str, required=True)

    args = parser.parse_args()
    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    print("== Step 22 Arch interval patcher ==")
    print(f"L={args.L}, ell={args.ell}, delta={args.delta}, k_spline={args.k_spline}")
    print(f"cutoff_t={args.cutoff_t}, chunk_size={args.chunk_size}, arb_prec={args.arb_prec}")
    print("[INFO] Replacing A midpoint/radius by acb.integral plus sinc-power tail radius.")

    mids = read_matrix_csv(Path(args.in_mid), value_col="mid")
    rads = read_matrix_csv(Path(args.in_rad), value_col="rad")

    if "A" not in mids or "A" not in rads:
        raise RuntimeError("Input CSVs must contain A rows.")

    centers_dec = decimal_grid_centers(args.L, args.ell, args.delta)
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

    mid_A, rad_A = build_A_midrad_arch(centers_dec=centers_dec, builder=builder)

    old_mid_A = mids["A"].copy()
    old_rad_A = rads["A"].copy()

    if old_mid_A.shape != mid_A.shape:
        raise RuntimeError(f"A shape mismatch: input={old_mid_A.shape}, new={mid_A.shape}")

    mids["A"] = mid_A
    rads["A"] = rad_A

    write_matrix_csv(Path(args.out_mid), mids, value_col="mid")
    write_matrix_csv(Path(args.out_rad), rads, value_col="rad")

    # Compare against both input midpoint and the old pilot builder for debugging.
    params = PilotParams(
        L=float(args.L),
        ell=float(args.ell),
        delta=float(args.delta),
        k_spline=args.k_spline,
        arch_tmax=float(args.cutoff_t),
        arch_nt=48001,
        p0_na=24001,
    )
    centers_float = build_centers(params)
    D = centers_float[:, None] - centers_float[None, :]
    pilot_A = build_A(D, params, SplinePacket.build(args.k_spline))

    print("\n== A contract summary ==")
    print(f"n_centers                    = {len(centers_dec)}")
    print(f"||A_old_mid - A_acb_mid||_2  = {np.linalg.norm(old_mid_A - mid_A, ord=2):.16e}")
    print(f"||A_pilot_T - A_acb_mid||_2  = {np.linalg.norm(pilot_A - mid_A, ord=2):.16e}")
    print(f"max old rad(A)               = {np.max(old_rad_A):.16e}")
    print(f"max new rad(A)               = {np.max(rad_A):.16e}")
    print(f"tail radius                  = {builder.tail_radius:.16e}")
    print(f"Wrote midpoint CSV: {args.out_mid}")
    print(f"Wrote radius CSV:   {args.out_rad}")


if __name__ == "__main__":
    run()
