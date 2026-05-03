#!/usr/bin/env python3
"""
Step 21 PSD-pd P0 interval patcher.

Purpose:
  Replace P0 rows in existing Step 20 midpoint/radius CSV files by
  Arb midpoint + Arb radius computed from exact piecewise B-spline
  exponential integrals.

Input:
  midpoint CSV from Step 20
  radius CSV from Step 20

Output:
  patched midpoint CSV
  patched radius CSV

Status:
  - P0 becomes Arb interval-backed.
  - P and Q remain whatever Step 20 gave, normally Arb-backed.
  - A remains whatever Step 20 gave, normally float midpoint + drift radius.
"""

from __future__ import annotations

import argparse
import csv
import math
from decimal import Decimal, getcontext
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

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    decimal_grid_centers,
    set_precision,
    spline_packet_ball,
)


def ball_to_mid_rad(x: arb) -> tuple[float, float]:
    """Convert an Arb ball to float midpoint and radius around that midpoint."""
    lo = arb_lower_decimal(x)
    hi = arb_upper_decimal(x)

    mid_dec = (lo + hi) / Decimal(2)
    mid_float = float(mid_dec)
    mid_float_dec = Decimal(str(mid_float))

    rad = max(abs(mid_float_dec - lo), abs(hi - mid_float_dec))
    rad = rad * Decimal("1.0000000001") + Decimal("1e-80")

    return mid_float, float(rad)


def arb_from_dec(x: Decimal) -> arb:
    return arb(str(x))


def dec_min(a: Decimal, b: Decimal) -> Decimal:
    return a if a <= b else b


def dec_max(a: Decimal, b: Decimal) -> Decimal:
    return a if a >= b else b


def read_matrix_csv(path: Path, value_col: str) -> dict[str, np.ndarray]:
    """
    Read matrix CSV with rows:
      matrix,i,j,value_col
    """
    raw: dict[str, dict[tuple[int, int], float]] = {}
    shapes: dict[str, tuple[int, int]] = {}

    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row["matrix"].strip()
            i = int(row["i"])
            j = int(row["j"])
            val = float(row[value_col])

            raw.setdefault(name, {})[(i, j)] = val
            old = shapes.get(name, (0, 0))
            shapes[name] = (max(old[0], i + 1), max(old[1], j + 1))

    out: dict[str, np.ndarray] = {}

    for name, entries in raw.items():
        n, m = shapes[name]
        M = np.zeros((n, m), dtype=float)
        for (i, j), val in entries.items():
            M[i, j] = val
        out[name] = M

    return out


def write_matrix_csv(path: Path, matrices: dict[str, np.ndarray], value_col: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    with path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=["matrix", "i", "j", value_col],
            lineterminator="\n",
        )
        writer.writeheader()

        for name, M in matrices.items():
            n, m = M.shape
            for i in range(n):
                for j in range(m):
                    writer.writerow(
                        {
                            "matrix": name,
                            "i": i,
                            "j": j,
                            value_col: f"{float(M[i, j]):.18e}",
                        }
                    )


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


def poly_exp_int_monomial(n: int, lam: arb, x: arb) -> arb:
    """
    Antiderivative value for integral x^n exp(lam x) dx.

    Formula:
      exp(lam x) * sum_{r=0}^n (-1)^r n!/(n-r)! x^(n-r) / lam^(r+1)
    """
    total = arb(0)
    nf = math.factorial(n)

    for r in range(n + 1):
        coeff = Decimal(((-1) ** r) * nf) / Decimal(math.factorial(n - r))
        total += arb(str(coeff)) * (x ** (n - r)) / (lam ** (r + 1))

    return (lam * x).exp() * total


def poly_exp_definite(coeffs: list[arb], lam: arb, lo: Decimal, hi: Decimal) -> arb:
    """Definite integral of exp(lam x) * sum_n coeffs[n] x^n dx over [lo, hi]."""
    x0 = arb_from_dec(lo)
    x1 = arb_from_dec(hi)

    total = arb(0)
    for n, c in enumerate(coeffs):
        total += c * (
            poly_exp_int_monomial(n, lam, x1)
            - poly_exp_int_monomial(n, lam, x0)
        )

    return total


def active_bspline_poly_coeffs(
    q: int,
    k_spline: int,
    seg_mid: Decimal,
    s_k: arb,
    c_k: arb,
) -> list[arb]:
    """
    Polynomial coefficients for r_k(x)=b_q(s_k x)/c_k on one segment.

    q = 2*k_spline + 1.
    """
    coeffs = [arb(0) for _ in range(q + 1)]

    s_dec = Decimal(k_spline + 1) / Decimal(2)
    shift_dec = Decimal(q + 1) / Decimal(2)
    y_mid = s_dec * seg_mid + shift_dec

    inv_fact = arb(1) / arb(math.factorial(q))

    for j in range(q + 2):
        if y_mid - Decimal(j) <= 0:
            continue

        sign_comb = ((-1) ** j) * math.comb(q + 1, j)
        base_const_dec = shift_dec - Decimal(j)
        pref = arb(sign_comb) * inv_fact / c_k

        for n in range(q + 1):
            term = (
                pref
                * arb(math.comb(q, n))
                * (s_k ** n)
                * (arb(str(base_const_dec)) ** (q - n))
            )
            coeffs[n] += term

    return coeffs


def spline_breakpoints_dec(k_spline: int) -> list[Decimal]:
    """Breakpoints for r_k(x)=b_{2k+1}(s_k x)/c_k."""
    q = 2 * k_spline + 1
    s_dec = Decimal(k_spline + 1) / Decimal(2)
    shift_dec = Decimal(q + 1) / Decimal(2)

    pts = [(Decimal(j) - shift_dec) / s_dec for j in range(q + 2)]
    pts.append(Decimal("-2"))
    pts.append(Decimal("2"))
    return sorted(set(pts))


def integrate_r_exp(
    lo: Decimal,
    hi: Decimal,
    lam: arb,
    k_spline: int,
    s_k: arb,
    c_k: arb,
) -> arb:
    """Compute integral_lo^hi exp(lam x) r_k(x) dx."""
    support_lo = Decimal("-2")
    support_hi = Decimal("2")

    a = dec_max(lo, support_lo)
    b = dec_min(hi, support_hi)

    if b <= a:
        return arb(0)

    q = 2 * k_spline + 1
    breaks = spline_breakpoints_dec(k_spline)

    pts = [a]
    for bp in breaks:
        if a < bp < b:
            pts.append(bp)
    pts.append(b)
    pts = sorted(set(pts))

    total = arb(0)

    for left, right in zip(pts[:-1], pts[1:]):
        if right <= left:
            continue

        mid = (left + right) / Decimal(2)
        coeffs = active_bspline_poly_coeffs(
            q=q,
            k_spline=k_spline,
            seg_mid=mid,
            s_k=s_k,
            c_k=c_k,
        )
        total += poly_exp_definite(coeffs, lam, left, right)

    return total


def p0_entry_ball(
    d: Decimal,
    L: Decimal,
    ell: Decimal,
    k_spline: int,
    s_k: arb,
    c_k: arb,
) -> arb:
    """
    Arb ball for P0(d).

    P0(d) =
      ell e^{d/2}  int_{(d-2L)/ell}^{d/ell} e^{-ell x/2} r_k(x) dx
    + ell e^{-d/2} int_{d/ell}^{(d+2L)/ell} e^{ ell x/2} r_k(x) dx
    """
    ell_b = arb(str(ell))
    d_b = arb(str(d))

    lam_minus = -ell_b / arb(2)
    lam_plus = ell_b / arb(2)

    lo_plus = (d - Decimal(2) * L) / ell
    hi_plus = d / ell

    lo_minus = d / ell
    hi_minus = (d + Decimal(2) * L) / ell

    I_plus = integrate_r_exp(
        lo=lo_plus,
        hi=hi_plus,
        lam=lam_minus,
        k_spline=k_spline,
        s_k=s_k,
        c_k=c_k,
    )

    I_minus = integrate_r_exp(
        lo=lo_minus,
        hi=hi_minus,
        lam=lam_plus,
        k_spline=k_spline,
        s_k=s_k,
        c_k=c_k,
    )

    return (
        ell_b * (d_b / arb(2)).exp() * I_plus
        + ell_b * (-d_b / arb(2)).exp() * I_minus
    )


def build_P0_midrad_arb(
    centers_dec: list[Decimal],
    L: str,
    ell: str,
    k_spline: int,
) -> tuple[np.ndarray, np.ndarray]:
    n = len(centers_dec)
    M = np.zeros((n, n), dtype=float)
    R = np.zeros((n, n), dtype=float)

    Ld = Decimal(L)
    elld = Decimal(ell)
    s_k, c_k = spline_packet_ball(k_spline)

    for i in range(n):
        for j in range(n):
            d = centers_dec[i] - centers_dec[j]
            val = p0_entry_ball(
                d=d,
                L=Ld,
                ell=elld,
                k_spline=k_spline,
                s_k=s_k,
                c_k=c_k,
            )
            M[i, j], R[i, j] = ball_to_mid_rad(val)

    return symmetrize_midrad(M, R)


def run() -> None:
    parser = argparse.ArgumentParser()

    parser.add_argument("--L", type=str, default="3.0")
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--delta", type=str, default="0.25")
    parser.add_argument("--k-spline", type=int, default=11)
    parser.add_argument("--arb-prec", type=int, default=256)

    parser.add_argument(
        "--in-mid",
        type=str,
        required=True,
        help="Input midpoint CSV from Step 20.",
    )
    parser.add_argument(
        "--in-rad",
        type=str,
        required=True,
        help="Input radius CSV from Step 20.",
    )
    parser.add_argument(
        "--out-mid",
        type=str,
        required=True,
        help="Output midpoint CSV with P0 patched.",
    )
    parser.add_argument(
        "--out-rad",
        type=str,
        required=True,
        help="Output radius CSV with P0 patched.",
    )

    args = parser.parse_args()
    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    print("== Step 21 P0 interval patcher ==")
    print(f"L={args.L}, ell={args.ell}, delta={args.delta}, k_spline={args.k_spline}")
    print(f"arb_prec={args.arb_prec}")
    print("[INFO] Replacing P0 midpoint/radius by Arb piecewise exponential integrals.")

    mids = read_matrix_csv(Path(args.in_mid), value_col="mid")
    rads = read_matrix_csv(Path(args.in_rad), value_col="rad")
    centers_dec = decimal_grid_centers(args.L, args.ell, args.delta)

    print("Building Arb midpoint/radius P0...")
    mid_P0, rad_P0 = build_P0_midrad_arb(
        centers_dec=centers_dec,
        L=args.L,
        ell=args.ell,
        k_spline=args.k_spline,
    )

    if "P0" not in mids or "P0" not in rads:
        raise RuntimeError("Input CSVs must contain P0 rows.")

    old_mid_P0 = mids["P0"].copy()
    old_rad_P0 = rads["P0"].copy()

    if old_mid_P0.shape != mid_P0.shape:
        raise RuntimeError(f"P0 shape mismatch: input={old_mid_P0.shape}, new={mid_P0.shape}")

    diff_mid = np.linalg.norm(old_mid_P0 - mid_P0, ord=2)
    diff_rad = np.linalg.norm(old_rad_P0 - rad_P0, ord=2)

    mids["P0"] = mid_P0
    rads["P0"] = rad_P0

    write_matrix_csv(Path(args.out_mid), mids, value_col="mid")
    write_matrix_csv(Path(args.out_rad), rads, value_col="rad")

    print("\n== P0 contract summary ==")
    print(f"||P0_old_mid - P0_arb_mid||_2 = {diff_mid:.16e}")
    print(f"||P0_old_rad - P0_arb_rad||_2 = {diff_rad:.16e}")
    print(f"max old rad(P0)               = {np.max(old_rad_P0):.16e}")
    print(f"max new rad(P0)               = {np.max(rad_P0):.16e}")
    print(f"Wrote midpoint CSV: {args.out_mid}")
    print(f"Wrote radius CSV:   {args.out_rad}")


if __name__ == "__main__":
    run()
