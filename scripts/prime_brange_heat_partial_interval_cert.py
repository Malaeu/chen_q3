#!/usr/bin/env python3
"""
Interval certificate for the prime-heat partial sum at t_critical (tau = 0).

Computes an interval upper bound for:
  sum_{n<=N} w_Q(n) * exp(-4*pi^2*t*xi_n^2) * |xi_n|
and checks it against the existing heat cert constants.

This is a numeric certificate helper (not a formal proof).
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from decimal import ROUND_CEILING, Decimal, getcontext
from pathlib import Path

import mpmath as mp
from mpmath import iv

N = 1_000_000
B_MIN = Decimal("3.0")
T_CRITICAL = iv.mpf(3) / iv.mpf(20)  # 0.15
B_MAX = iv.mpf("4.9")
DIGITS = 12

HEAT_CERT_SOURCE = Path("output/prime_cert_brange_heat_L_2026-01-28_0115.txt")


@dataclass
class HeatCert:
    tail_bound: Decimal
    prime_heat_raw: Decimal
    arch_heat_raw: Decimal
    b_min: Decimal
    b_max: Decimal
    t_critical: Decimal


def parse_heat_cert(text: str) -> HeatCert:
    tail = None
    lprime = None
    larch = None
    bmin = None
    bmax = None
    tcrit = None
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("B_min"):
            bmin = Decimal(line.split("=", 1)[1].strip())
        elif line.startswith("B_max"):
            bmax = Decimal(line.split("=", 1)[1].strip())
        elif line.startswith("t_critical"):
            tcrit = Decimal(line.split("=", 1)[1].strip())
        elif line.startswith("tail_bound_heat"):
            tail = Decimal(line.split("=", 1)[1].strip())
        elif line.startswith("L_prime_heat"):
            lprime = Decimal(line.split("=", 1)[1].strip())
        elif line.startswith("L_arch_heat"):
            larch = Decimal(line.split("=", 1)[1].strip())
    if None in (tail, lprime, larch, bmin, bmax, tcrit):
        raise SystemExit("Failed to parse heat cert fields from source file")
    return HeatCert(
        tail_bound=tail,
        prime_heat_raw=lprime,
        arch_heat_raw=larch,
        b_min=bmin,
        b_max=bmax,
        t_critical=tcrit,
    )


def sieve_primes(limit: int) -> list[int]:
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if is_prime[p]:
            start = p * p
            step = p
            is_prime[start : limit + 1 : step] = b"\x00" * (((limit - start) // step) + 1)
    return [i for i in range(2, limit + 1) if is_prime[i]]


def precompute_entries(limit: int):
    primes = sieve_primes(limit)
    entries = []
    two_pi = iv.mpf(2) * iv.pi
    four_pi_sq = iv.mpf(4) * iv.pi * iv.pi
    for p in primes:
        logp = iv.log(iv.mpf(p))
        pk = p
        while pk <= limit:
            n_iv = iv.mpf(pk)
            xi = iv.log(n_iv) / two_pi
            # indicator |xi| <= B_max (always true for n<=1e6, but keep guard)
            if xi.b > B_MAX:
                pk *= p
                continue
            w_q = (iv.mpf(2) * logp) / iv.sqrt(n_iv)
            heat = iv.exp(-four_pi_sq * T_CRITICAL * xi * xi)
            entries.append((xi, w_q, heat))
            pk *= p
    return entries, len(primes)


def main() -> int:
    if not HEAT_CERT_SOURCE.exists():
        raise SystemExit(f"Missing source file: {HEAT_CERT_SOURCE}")

    mp.mp.dps = 80
    getcontext().prec = max(50, DIGITS + 10)
    quant = Decimal(f"1e-{DIGITS}")

    cert = parse_heat_cert(HEAT_CERT_SOURCE.read_text(encoding="utf-8"))

    entries, nprimes = precompute_entries(N)
    total = iv.mpf(0)
    for xi, w_q, heat in entries:
        total += w_q * heat * xi

    sum_ub = Decimal(mp.nstr(mp.mpf(total.b), 50)).quantize(quant, rounding=ROUND_CEILING)

    partial_bound = (cert.prime_heat_raw - cert.tail_bound).quantize(quant, rounding=ROUND_CEILING)

    ok = sum_ub <= partial_bound
    prime_heat_raw_ub = (sum_ub + cert.tail_bound).quantize(quant, rounding=ROUND_CEILING)
    l_total = ((prime_heat_raw_ub + cert.arch_heat_raw) / (cert.b_min * cert.b_min)).quantize(
        quant, rounding=ROUND_CEILING
    )

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out_path = Path(f"output/prime_cert_brange_heat_prime_partial_interval_{ts}.txt")
    heat_out_path = Path(f"output/prime_cert_brange_heat_L_interval_{ts}.txt")

    lines = [
        "Prime-heat partial-sum interval certificate (t_critical, tau=0)",
        "===============================================================",
        "",
        f"Source heat cert: {HEAT_CERT_SOURCE}",
        f"N = {N}",
        f"t_critical = {mp.nstr(mp.mpf(T_CRITICAL.b), 20)}",
        f"B_max = {B_MAX}",
        f"primes <= N: {nprimes}",
        "",
        f"tail_bound_heat = {cert.tail_bound}",
        f"L_prime_heat = {cert.prime_heat_raw}",
        f"L_prime_heat_partial = {partial_bound}",
        f"prime_heat_sum_up_to_ub = {sum_ub}",
        f"check sum_ub <= L_prime_heat_partial: {ok}",
        "",
    ]
    out_path.write_text("\n".join(lines), encoding="utf-8")
    print(out_path)

    heat_lines = [
        "Heat-weighted Lipschitz certificate scaffold (t_critical, tau=0)",
        "============================================================",
        "",
        f"B_min = {cert.b_min}",
        f"B_max = {cert.b_max}",
        f"t_critical = {cert.t_critical}",
        f"N = {N}",
        "",
        f"primes <= N: {nprimes}",
        f"tail_bound_heat = {cert.tail_bound}",
        f"prime_heat_sum_up_to_ub = {sum_ub}",
        f"L_prime_heat = {prime_heat_raw_ub}",
        f"L_arch_heat = {cert.arch_heat_raw}",
        f"L_total = {l_total}",
        "note: L_prime_heat uses interval sum_ub + tail_bound_heat",
        "",
    ]
    heat_out_path.write_text("\n".join(heat_lines), encoding="utf-8")
    print(heat_out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
