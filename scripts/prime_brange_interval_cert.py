#!/usr/bin/env python3
"""
Interval certificate for prime-term partial sums on the full B-grid.

Reads the existing B-range certificate file for arch_term values and tail bound,
computes interval upper bounds for the prime partial sums, then writes a new
certificate file with conservative rounding:
- prime_sum: rounded UP (upper bound)
- prime_ub:  rounded UP (sum_ub + tail)
- arch_term: taken from source (as-is)
- margin:    rounded DOWN (arch_term - prime_ub)
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from decimal import ROUND_CEILING, ROUND_FLOOR, Decimal, getcontext
from pathlib import Path

import mpmath as mp
from mpmath import iv

SOURCE = Path("output/prime_cert_brange_tcritical_2026-01-26_0050.txt")
DIGITS = 12
N = 1_000_000
B_MIN = 3.0
B_MAX = 4.9
B_H = 0.1


@dataclass
class Row:
    B: float
    arch_term: Decimal


def parse_source(text: str) -> tuple[list[Row], Decimal]:
    rows: list[Row] = []
    tail = None
    for line in text.splitlines():
        line = line.strip()
        if "tail_bound" in line:
            parts = line.split("=", 1)
            if len(parts) == 2:
                tail = Decimal(parts[1].strip())
        if not line or not line[0].isdigit():
            continue
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 5:
            continue
        B = float(parts[0])
        arch = Decimal(parts[3])
        rows.append(Row(B=B, arch_term=arch))
    if tail is None:
        raise SystemExit("tail_bound not found in source file")
    return rows, tail


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
    pi = iv.pi
    two_pi = iv.mpf(2) * pi
    four_pi_sq = iv.mpf(4) * pi * pi
    t_critical = iv.mpf(3) / iv.mpf(20)

    for p in primes:
        logp = iv.log(iv.mpf(p))
        pk = p
        while pk <= limit:
            n_iv = iv.mpf(pk)
            xi = iv.log(n_iv) / two_pi
            w_q = (iv.mpf(2) * logp) / iv.sqrt(n_iv)
            heat = iv.exp(-four_pi_sq * t_critical * xi * xi)
            entries.append((xi, w_q, heat))
            pk *= p
    return entries


def main() -> int:
    if not SOURCE.exists():
        raise SystemExit(f"Missing source file: {SOURCE}")

    # interval precision
    mp.mp.dps = 80

    rows, tail = parse_source(SOURCE.read_text(encoding="utf-8"))

    # sanity: xi_n(N) < B_min
    xi_max = iv.log(iv.mpf(N)) / (iv.mpf(2) * iv.pi)
    if mp.mpf(xi_max.b) >= B_MIN:
        raise SystemExit("xi_n(N) not below B_min; interval max check failed")

    entries = precompute_entries(N)

    getcontext().prec = max(50, DIGITS + 10)
    quant = Decimal(f"1e-{DIGITS}")

    # build grid dict for quick lookup
    rows_by_B = {row.B: row for row in rows}
    B_values = []
    steps = int(round((B_MAX - B_MIN) / B_H))
    for i in range(steps + 1):
        B_values.append(round(B_MIN + i * B_H, 10))

    out_lines = []
    out_lines.append("Prime-term B-range interval certificate at t_critical (tau=0)")
    out_lines.append("===========================================================")
    out_lines.append("")
    out_lines.append(f"B_min = {B_MIN}")
    out_lines.append(f"B_max = {B_MAX}")
    out_lines.append(f"B_h = {B_H}")
    out_lines.append(f"t_critical = {Decimal('0.15')}")
    out_lines.append(f"tau = 0")
    out_lines.append(f"N = {N}")
    out_lines.append("")
    out_lines.append(f"tail_bound (n>N) = {tail}")
    out_lines.append("")
    out_lines.append("B, prime_sum, prime_ub, arch_term, margin")

    for B in B_values:
        if B not in rows_by_B:
            raise SystemExit(f"Missing row for B={B} in {SOURCE}")
        B_iv = iv.mpf(B)
        total = iv.mpf(0)
        for xi, w_q, heat in entries:
            fejer = iv.mpf(1) - (xi / B_iv)
            total += w_q * fejer * heat
        # round up for prime_sum upper bound
        upper = mp.mpf(total.b)
        sum_ub = Decimal(mp.nstr(upper, 50)).quantize(quant, rounding=ROUND_CEILING)
        prime_ub = (sum_ub + tail).quantize(quant, rounding=ROUND_CEILING)
        arch = rows_by_B[B].arch_term.quantize(quant, rounding=ROUND_FLOOR)
        margin = (arch - prime_ub).quantize(quant, rounding=ROUND_FLOOR)
        out_lines.append(f"{B:.4f}, {sum_ub}, {prime_ub}, {arch}, {margin}")

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out_path = Path(f"output/prime_cert_brange_tcritical_interval_{ts}.txt")
    out_path.write_text("\n".join(out_lines) + "\n", encoding="utf-8")
    print(out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
