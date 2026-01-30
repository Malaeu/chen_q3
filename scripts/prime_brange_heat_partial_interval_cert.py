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

DPS_PRIMARY = 80
DPS_VERIFY = 120
N = 1_000_000
B_MIN = Decimal("3.0")
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


def precompute_entries(limit: int, tcrit_iv: iv.mpf, bmax_iv: iv.mpf):
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
            if xi.b > bmax_iv:
                pk *= p
                continue
            w_q = (iv.mpf(2) * logp) / iv.sqrt(n_iv)
            heat = iv.exp(-four_pi_sq * tcrit_iv * xi * xi)
            entries.append((xi, w_q, heat))
            pk *= p
    return entries, len(primes)


def arch_heat_integral(bmax: Decimal, tcrit: Decimal, dps: int) -> mp.mpf:
    mp.mp.dps = dps
    pi = mp.pi
    bmax_mp = mp.mpf(str(bmax))
    t_mp = mp.mpf(str(tcrit))
    four_pi_sq = 4 * pi * pi

    def a_star(x: mp.mpf) -> mp.mpf:
        z = mp.mpf("0.25") + 1j * pi * x
        val = mp.log(pi) - mp.re(mp.digamma(z))
        return 2 * pi * val

    def integrand(x: mp.mpf) -> mp.mpf:
        ax = abs(a_star(x))
        return ax * mp.e ** (-four_pi_sq * t_mp * x * x) * abs(x)

    cuts = [mp.mpf("0"), mp.mpf("1"), mp.mpf("2"), mp.mpf("3"), mp.mpf("4"), bmax_mp]
    total = mp.mpf("0")
    for a, b in zip(cuts[:-1], cuts[1:]):
        if b <= a:
            continue
        total += mp.quad(integrand, [a, b])
    return 2 * total


def main() -> int:
    if not HEAT_CERT_SOURCE.exists():
        raise SystemExit(f"Missing source file: {HEAT_CERT_SOURCE}")

    mp.mp.dps = DPS_PRIMARY
    getcontext().prec = max(50, DIGITS + 10)
    quant = Decimal(f"1e-{DIGITS}")

    cert = parse_heat_cert(HEAT_CERT_SOURCE.read_text(encoding="utf-8"))
    tcrit_iv = iv.mpf(str(cert.t_critical))
    bmax_iv = iv.mpf(str(cert.b_max))

    entries, nprimes = precompute_entries(N, tcrit_iv, bmax_iv)
    total = iv.mpf(0)
    for xi, w_q, heat in entries:
        total += w_q * heat * xi

    sum_ub = Decimal(mp.nstr(mp.mpf(total.b), 50)).quantize(quant, rounding=ROUND_CEILING)

    partial_bound = (cert.prime_heat_raw - cert.tail_bound).quantize(quant, rounding=ROUND_CEILING)

    ok = sum_ub <= partial_bound
    prime_heat_raw_ub = (sum_ub + cert.tail_bound).quantize(quant, rounding=ROUND_CEILING)

    arch_1 = arch_heat_integral(cert.b_max, cert.t_critical, DPS_PRIMARY)
    arch_2 = arch_heat_integral(cert.b_max, cert.t_critical, DPS_VERIFY)
    arch_err = abs(arch_2 - arch_1)
    arch_bound = max(arch_1, arch_2) + 10 * arch_err + mp.mpf("1e-12")
    arch_bound_dec = Decimal(mp.nstr(arch_bound, 50))
    # Keep the final bound conservative: never decrease vs source.
    arch_final = max(arch_bound_dec, cert.arch_heat_raw)
    arch_ub = arch_final.quantize(quant, rounding=ROUND_CEILING)

    l_total = ((prime_heat_raw_ub + arch_ub) / (cert.b_min * cert.b_min)).quantize(
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
        f"t_critical = {cert.t_critical}",
        f"B_max = {cert.b_max}",
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
        f"L_arch_heat = {arch_ub}",
        f"L_arch_heat_input = {cert.arch_heat_raw}",
        f"L_arch_heat_raw_primary = {arch_1}",
        f"L_arch_heat_raw_verify = {arch_2}",
        f"L_arch_heat_err = {arch_err}",
        f"L_total = {l_total}",
        "note: L_prime_heat uses interval sum_ub + tail_bound_heat",
        "",
    ]
    heat_out_path.write_text("\n".join(heat_lines), encoding="utf-8")
    print(heat_out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
