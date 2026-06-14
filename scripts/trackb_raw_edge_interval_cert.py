#!/usr/bin/env python3
"""
Track B / E5p raw-edge interval penalty certificate generator.

This script builds Arb interval matrices for the finite raw-edge target

  mu * G - (P_edge - P0_edge) + tau * Q^T Q >= 0

on the full packet coefficient space.  If the interval eigenvalue lower bound
is positive, this gives a proof-grade finite PSD certificate for the supplied
`mu` and `tau`; it does not prove that `mu` is the analytic E5p budget.

All coordinates are raw-log coordinates: a = r * log(p), edge=[2K,4K].
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from dataclasses import dataclass
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

try:
    from flint import arb, arb_mat, ctx
except ImportError as exc:  # pragma: no cover - environment guard
    raise SystemExit(
        "python-flint is required for interval certificates. "
        "Use the repo venv or install python-flint."
    ) from exc


REPO_ROOT = Path(__file__).resolve().parents[1]
STEP13_PATH = REPO_ROOT / "q3.lean.aristotle" / "scripts" / "q3_psdpd_step13_pilot.py"


def load_step13() -> Any:
    spec = importlib.util.spec_from_file_location("q3_psdpd_step13_pilot", STEP13_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load Step13 pilot from {STEP13_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_frac(raw: str | float | int) -> Fraction:
    return Fraction(str(raw))


def arb_from_frac(x: Fraction) -> arb:
    return arb(x.numerator) / arb(x.denominator)


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


def arb_record(x: arb) -> dict[str, str]:
    lo = arb_lower_decimal(x)
    hi = arb_upper_decimal(x)
    mid = (lo + hi) / Decimal(2)
    rad = (hi - lo) / Decimal(2)
    return {
        "lo": str(lo),
        "hi": str(hi),
        "mid": str(mid),
        "rad": str(rad),
    }


def positive_part_power_ball(x: arb, deg: int) -> arb:
    """Enclose (max(x,0))^deg for a real Arb ball."""
    lo = arb_lower_decimal(x)
    hi = arb_upper_decimal(x)
    if hi <= 0:
        return arb(0)
    if lo >= 0:
        return x**deg
    return arb_interval_from_decimals(Decimal(0), hi**deg)


def centered_bspline_arb(deg: int, x: arb) -> arb:
    support = arb(Fraction(deg + 1, 2).numerator) / arb(Fraction(deg + 1, 2).denominator)
    if (x - support) > 0 or (x + support) < 0:
        return arb(0)

    y = x + support
    total = arb(0)
    inv_fact = arb(1) / arb(math.factorial(deg))
    for j in range(deg + 2):
        coeff = ((-1) ** j) * math.comb(deg + 1, j)
        total += arb(coeff) * positive_part_power_ball(y - arb(j), deg)
    return total * inv_fact


@dataclass(frozen=True)
class PacketArb:
    k_spline: int
    s_k: Fraction
    c_k: arb

    @staticmethod
    def build(k_spline: int) -> "PacketArb":
        if k_spline < 1:
            raise ValueError("k_spline must be >= 1")
        q = 2 * k_spline + 1
        s_k = Fraction(k_spline + 1, 2)
        c_k = centered_bspline_arb(q, arb(0))
        if not c_k > 0:
            raise ValueError(f"bad spline normalization: c_k={c_k}")
        return PacketArb(k_spline=k_spline, s_k=s_k, c_k=c_k)

    @property
    def q(self) -> int:
        return 2 * self.k_spline + 1

    def r_corr(self, x: arb) -> arb:
        return centered_bspline_arb(self.q, arb_from_frac(self.s_k) * x) / self.c_k


def build_centers_frac(K: Fraction, ell: Fraction, delta: Fraction) -> list[Fraction]:
    L = 2 * K
    x = -L + ell
    stop = L - ell + delta / 2
    out: list[Fraction] = []
    while x < stop:
        out.append(x)
        x += delta
    return out


def build_D(u: list[Fraction]) -> list[list[Fraction]]:
    return [[ui - uj for uj in u] for ui in u]


def shifted_packet_entry(packet: PacketArb, d: Fraction, ell: Fraction, a: arb) -> arb:
    d_ball = arb_from_frac(d)
    ell_ball = arb_from_frac(ell)
    return packet.r_corr((d_ball - a) / ell_ball) + packet.r_corr((d_ball + a) / ell_ball)


@dataclass(frozen=True)
class PrimeShiftInterval:
    p: int
    r_pow: int
    a: arb
    weight: arb


def compare_leq_cert(x: arb, y: arb, *, label: str) -> bool:
    if x <= y:
        return True
    if x > y:
        return False
    raise RuntimeError(f"uncertain Arb comparison for {label}: {x} <= {y}")


def prime_power_shifts_interval(pilot: Any, L: Fraction) -> list[PrimeShiftInterval]:
    max_n = int(math.floor(math.exp(float(2 * L)))) + 1
    primes = pilot.sieve_primes(max_n)
    cutoff = arb_from_frac(2 * L)
    shifts: list[PrimeShiftInterval] = []
    for p in primes:
        logp = arb(p).log()
        r_pow = 1
        while True:
            a = arb(r_pow) * logp
            if compare_leq_cert(a, cutoff, label=f"{r_pow}*log({p}) <= 2L"):
                weight = logp * ((-a / arb(2)).exp())
                shifts.append(PrimeShiftInterval(p=p, r_pow=r_pow, a=a, weight=weight))
                r_pow += 1
                continue
            break
    shifts.sort(key=lambda sh: float(sh.a))
    return shifts


def zero_matrix(n: int) -> list[list[arb]]:
    return [[arb(0) for _ in range(n)] for __ in range(n)]


def symmetrize(M: list[list[arb]]) -> list[list[arb]]:
    n = len(M)
    out = zero_matrix(n)
    for i in range(n):
        for j in range(n):
            out[i][j] = (M[i][j] + M[j][i]) / arb(2)
    return out


def build_G(packet: PacketArb, D: list[list[Fraction]], ell: Fraction) -> list[list[arb]]:
    n = len(D)
    G = zero_matrix(n)
    cache: dict[Fraction, arb] = {}
    for i in range(n):
        for j in range(n):
            d = D[i][j]
            if d not in cache:
                cache[d] = packet.r_corr(arb_from_frac(d / ell))
            G[i][j] = cache[d]
    return symmetrize(G)


def build_Q(u: list[Fraction]) -> list[list[arb]]:
    row_plus = [(arb_from_frac(ui) / arb(2)).exp() for ui in u]
    row_minus = [(-arb_from_frac(ui) / arb(2)).exp() for ui in u]
    return [row_plus, row_minus]


def build_QTQ(Q: list[list[arb]]) -> list[list[arb]]:
    n = len(Q[0])
    out = zero_matrix(n)
    for i in range(n):
        for j in range(n):
            out[i][j] = Q[0][i] * Q[0][j] + Q[1][i] * Q[1][j]
    return symmetrize(out)


def build_P_edge(
    packet: PacketArb,
    D: list[list[Fraction]],
    ell: Fraction,
    shifts: list[PrimeShiftInterval],
    lo: Fraction,
    hi: Fraction,
) -> tuple[list[list[arb]], int]:
    n = len(D)
    P = zero_matrix(n)
    lo_ball = arb_from_frac(lo)
    hi_ball = arb_from_frac(hi)
    ell_ball = arb_from_frac(ell)
    support = arb(2)
    count = 0
    for sh in shifts:
        in_left = compare_leq_cert(lo_ball, sh.a, label=f"{lo} <= shift")
        in_right = compare_leq_cert(sh.a, hi_ball, label=f"shift <= {hi}")
        if not (in_left and in_right):
            continue
        count += 1
        entry_cache: dict[Fraction, arb] = {}
        for i in range(n):
            for j in range(n):
                d = D[i][j]
                if d not in entry_cache:
                    d_ball = arb_from_frac(d)
                    x_minus = (d_ball - sh.a) / ell_ball
                    x_plus = (d_ball + sh.a) / ell_ball
                    minus_outside = (x_minus - support) > 0 or (x_minus + support) < 0
                    plus_outside = (x_plus - support) > 0 or (x_plus + support) < 0
                    if minus_outside and plus_outside:
                        entry_cache[d] = arb(0)
                    else:
                        entry_cache[d] = shifted_packet_entry(packet, d, ell, sh.a)
                P[i][j] += sh.weight * entry_cache[d]
    return symmetrize(P), count


def poly_exp_int_monomial(n: int, lam: arb, x: arb) -> arb:
    total = arb(0)
    nf = math.factorial(n)
    for r in range(n + 1):
        coeff = Fraction(((-1) ** r) * nf, math.factorial(n - r))
        total += arb_from_frac(coeff) * (x ** (n - r)) / (lam ** (r + 1))
    return (lam * x).exp() * total


def poly_exp_definite(coeffs: list[arb], lo: Fraction, hi: Fraction) -> arb:
    lam = arb(1) / arb(2)
    x0 = arb_from_frac(lo)
    x1 = arb_from_frac(hi)
    total = arb(0)
    for n, c in enumerate(coeffs):
        total += c * (poly_exp_int_monomial(n, lam, x1) - poly_exp_int_monomial(n, lam, x0))
    return total


def active_poly_coeffs(
    packet: PacketArb,
    d: Fraction,
    ell: Fraction,
    seg_mid: Fraction,
) -> list[arb]:
    """Polynomial coefficients in a for r((d-a)/ell)+r((d+a)/ell)."""
    q = packet.q
    shift = Fraction(q + 1, 2)
    s_over_ell = packet.s_k / ell
    coeffs = [arb(0) for _ in range(q + 1)]
    inv_fact_over_c = (arb(1) / arb(math.factorial(q))) / packet.c_k

    for slope in (-s_over_ell, s_over_ell):
        base0 = s_over_ell * d + shift
        for j in range(q + 2):
            base = base0 - j
            if base + slope * seg_mid <= 0:
                continue
            pref = arb(((-1) ** j) * math.comb(q + 1, j)) * inv_fact_over_c
            base_ball = arb_from_frac(base)
            slope_ball = arb_from_frac(slope)
            for n in range(q + 1):
                coeffs[n] += (
                    pref
                    * arb(math.comb(q, n))
                    * (base_ball ** (q - n))
                    * (slope_ball ** n)
                )
    return coeffs


def raw_edge_breakpoints(packet: PacketArb, d: Fraction, ell: Fraction, lo: Fraction, hi: Fraction) -> list[Fraction]:
    q = packet.q
    shift = Fraction(q + 1, 2)
    s_over_ell = packet.s_k / ell
    points = {lo, hi}
    for slope in (-s_over_ell, s_over_ell):
        base0 = s_over_ell * d + shift
        for j in range(q + 2):
            base = base0 - j
            if slope == 0:
                continue
            a0 = -base / slope
            if lo < a0 < hi:
                points.add(a0)
    return sorted(points)


def P0_entry(packet: PacketArb, d: Fraction, ell: Fraction, lo: Fraction, hi: Fraction) -> arb:
    points = raw_edge_breakpoints(packet, d, ell, lo, hi)
    total = arb(0)
    for left, right in zip(points[:-1], points[1:]):
        if left == right:
            continue
        mid = (left + right) / 2
        coeffs = active_poly_coeffs(packet, d, ell, mid)
        total += poly_exp_definite(coeffs, left, right)
    return total


def build_P0_edge(packet: PacketArb, D: list[list[Fraction]], ell: Fraction, lo: Fraction, hi: Fraction) -> list[list[arb]]:
    n = len(D)
    P0 = zero_matrix(n)
    cache: dict[Fraction, arb] = {}
    for i in range(n):
        for j in range(i, n):
            d = D[i][j]
            if d not in cache:
                cache[d] = P0_entry(packet, d, ell, lo, hi)
            value = cache[d]
            P0[i][j] = value
            P0[j][i] = value
    return symmetrize(P0)


def build_penalty_matrix(
    *,
    mu: Fraction,
    tau: Fraction,
    G: list[list[arb]],
    P_edge: list[list[arb]],
    P0_edge: list[list[arb]],
    QTQ: list[list[arb]],
) -> list[list[arb]]:
    n = len(G)
    mu_ball = arb_from_frac(mu)
    tau_ball = arb_from_frac(tau)
    M = zero_matrix(n)
    for i in range(n):
        for j in range(n):
            M[i][j] = mu_ball * G[i][j] - (P_edge[i][j] - P0_edge[i][j]) + tau_ball * QTQ[i][j]
    return symmetrize(M)


def min_real_eigen_lower(M: list[list[arb]]) -> tuple[arb, list[dict[str, str]]]:
    A = arb_mat(M)
    eigs = A.eig()
    records: list[dict[str, str]] = []
    best: arb | None = None
    for z in eigs:
        real_part = z.real
        imag_part = z.imag
        records.append(
            {
                "real_lo": str(arb_lower_decimal(real_part)),
                "real_hi": str(arb_upper_decimal(real_part)),
                "imag_abs_upper": str(imag_part.abs_upper()),
            }
        )
        if best is None or arb_lower_decimal(real_part) < arb_lower_decimal(best):
            best = real_part
    if best is None:
        raise RuntimeError("empty eigenvalue list")
    return best, records


def run_one(args: argparse.Namespace, K_raw: str, mu_raw: str, tau_raw: str) -> dict[str, Any]:
    pilot = load_step13()
    K = parse_frac(K_raw)
    ell = parse_frac(args.ell)
    delta = parse_frac(args.grid_delta)
    k_spline = int(args.k_spline)
    mu = parse_frac(mu_raw)
    tau = parse_frac(tau_raw)
    lo = 2 * K
    hi = 4 * K

    packet = PacketArb.build(k_spline)
    u = build_centers_frac(K, ell, delta)
    D = build_D(u)
    G = build_G(packet, D, ell)
    Q = build_Q(u)
    QTQ = build_QTQ(Q)
    shifts = prime_power_shifts_interval(pilot, 2 * K)
    P_edge, edge_count = build_P_edge(packet, D, ell, shifts, lo, hi)
    P0_edge = build_P0_edge(packet, D, ell, lo, hi)
    M = build_penalty_matrix(mu=mu, tau=tau, G=G, P_edge=P_edge, P0_edge=P0_edge, QTQ=QTQ)
    min_eig, eig_records = min_real_eigen_lower(M)
    min_lower = arb_lower_decimal(min_eig)
    cert_pass = min_lower > 0

    return {
        "mode": "trackb_raw_edge_interval_penalty_cert",
        "K": str(K),
        "raw_edge": [str(lo), str(hi)],
        "ell": str(ell),
        "grid_delta": str(delta),
        "k_spline": k_spline,
        "n_centers": len(u),
        "full_space_dim": len(u),
        "boundary_rows": 2,
        "kerQ_dim_if_rank2": len(u) - 2,
        "prime_power_shifts_total": len(shifts),
        "edge_prime_power_shifts": edge_count,
        "mu": str(mu),
        "tau": str(tau),
        "arb_prec_bits": int(args.arb_prec),
        "matrix_entry_sources": {
            "G": "exact centered B-spline rational inputs evaluated in Arb",
            "Q": "Arb exp(+-u/2)",
            "P_edge": "Arb log(p) and exp(-r log(p)/2) with B-spline interval evaluation",
            "P0_edge": "piecewise-polynomial B-spline integral of exp(a/2) in Arb",
        },
        "penalty_matrix": "mu*G - (P_edge-P0_edge) + tau*Q^TQ",
        "min_eigenvalue_interval": arb_record(min_eig),
        "min_eigenvalue_lower": str(min_lower),
        "finite_interval_psd_cert": "PASS" if cert_pass else "FAIL",
        "proof_scope": "finite raw-edge penalty PSD for supplied mu and tau only",
        "not_e5_closure_reason": (
            "same-unit analytic mu_K source/bridge is not supplied by this certificate"
        ),
        "analytic_mu_bridge_status": "GAP",
        "eigenvalue_records": eig_records if args.emit_eigs else None,
    }


def expand_values(values: list[str], count: int, *, name: str) -> list[str]:
    if len(values) == count:
        return values
    if len(values) == 1:
        return values * count
    raise SystemExit(f"--{name} must have length 1 or match --K length")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--K", nargs="+", required=True, help="active K values, e.g. 2 3 3.5")
    parser.add_argument("--mu", nargs="+", required=True, help="supplied finite mu value(s)")
    parser.add_argument("--tau", nargs="+", required=True, help="penalty tau value(s)")
    parser.add_argument("--ell", default="0.35")
    parser.add_argument("--grid-delta", default="0.5")
    parser.add_argument("--k-spline", type=int, default=5)
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--emit-eigs", action="store_true")
    parser.add_argument("--out", help="optional JSON output path")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    ctx.prec = int(args.arb_prec)
    getcontext().prec = max(100, int(args.arb_prec) // 2)
    mus = expand_values(args.mu, len(args.K), name="mu")
    taus = expand_values(args.tau, len(args.K), name="tau")
    rows = [run_one(args, K_raw, mu_raw, tau_raw) for K_raw, mu_raw, tau_raw in zip(args.K, mus, taus)]
    text = json.dumps(rows, indent=2, sort_keys=True)
    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
