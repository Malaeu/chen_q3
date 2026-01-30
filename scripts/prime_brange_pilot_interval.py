#!/usr/bin/env python3
"""
Interval certificate for the prime-term partial sums at two pilot B values.

Computes rigorous interval bounds for:
  sum_{n<=N} w_Q(n) * phi_shift(B, t_critical, 0, xi_n n)
using mpmath interval arithmetic, and checks the result against the
pilot table values.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

import mpmath as mp
from mpmath import iv

# Parameters
B_VALUES = [3.0, 4.9]
T_CRITICAL = iv.mpf(3) / iv.mpf(20)  # 0.15
N = 1_000_000

SOURCE_PILOT = Path("output/prime_cert_brange_tcritical_pilot_2026-01-30_2208.txt")


@dataclass
class PilotRow:
    B: float
    prime_sum_str: str


def parse_pilot_rows(text: str) -> dict[float, PilotRow]:
    rows: dict[float, PilotRow] = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or not line[0].isdigit():
            continue
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 5:
            continue
        B = float(parts[0])
        rows[B] = PilotRow(B=B, prime_sum_str=parts[1])
    return rows


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

    for p in primes:
        logp = iv.log(iv.mpf(p))
        pk = p
        while pk <= limit:
            n_iv = iv.mpf(pk)
            xi = iv.log(n_iv) / two_pi
            w_q = (iv.mpf(2) * logp) / iv.sqrt(n_iv)
            heat = iv.exp(-four_pi_sq * T_CRITICAL * xi * xi)
            entries.append((xi, w_q, heat))
            pk *= p
    return entries


def main() -> int:
    if not SOURCE_PILOT.exists():
        raise SystemExit(f"Missing source file: {SOURCE_PILOT}")

    # precision for interval arithmetic
    mp.mp.dps = 80

    pilot_rows = parse_pilot_rows(SOURCE_PILOT.read_text(encoding="utf-8"))
    for B in B_VALUES:
        if B not in pilot_rows:
            raise SystemExit(f"Missing pilot row for B={B} in {SOURCE_PILOT}")

    # sanity: xi_n(N) < B_min
    xi_max = iv.log(iv.mpf(N)) / (iv.mpf(2) * iv.pi)
    if xi_max.b >= min(B_VALUES):
        raise SystemExit("xi_n(N) not below B_min; interval max check failed")

    entries = precompute_entries(N)

    lines = []
    lines.append("Prime-term pilot interval certificate")
    lines.append("===================================")
    lines.append("")
    lines.append(f"N = {N}")
    lines.append(f"t_critical = {T_CRITICAL}")
    lines.append(f"xi_max_upper = {xi_max.b}")
    lines.append("")

    for B in B_VALUES:
        B_iv = iv.mpf(B)
        total = iv.mpf(0)
        for xi, w_q, heat in entries:
            fejer = iv.mpf(1) - (xi / B_iv)
            total += w_q * fejer * heat
        row = pilot_rows[B]
        lines.append(f"B = {B:.4f}")
        lines.append(f"interval_sum = [{total.a}, {total.b}]")
        lines.append(f"pilot_prime_sum = {row.prime_sum_str}")
        # check inequality
        ok = total.b <= iv.mpf(row.prime_sum_str)
        lines.append(f"upper <= pilot_prime_sum : {ok}")
        lines.append("")

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out_path = Path(f"output/prime_cert_brange_tcritical_pilot_interval_{ts}.txt")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
