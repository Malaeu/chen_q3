#!/usr/bin/env python3
"""
Generate bucketed interval sums for the prime-heat partial sum (t_critical, tau=0).

This produces a Lean file with per-bucket upper bounds for
prime_heat_prime_sum_up_to prime_cert_heat_N.
"""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import dataclass
from decimal import ROUND_CEILING, Decimal, getcontext
from pathlib import Path

import mpmath as mp
from mpmath import iv


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--input", required=True)
    p.add_argument("--output", required=True)
    p.add_argument("--digits", type=int, default=14)
    p.add_argument("--bucket", type=int, default=10_000)
    return p.parse_args()


def sha256_hex(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def source_label(path: Path) -> str:
    parts = path.resolve().parts
    if "q3.lean.aristotle" in parts:
        idx = parts.index("q3.lean.aristotle")
        rel = Path(*parts[idx + 1 :])
        return str(rel)
    return str(path)


def parse_value(text: str, key: str) -> str:
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith(key):
            continue
        _, rhs = line.split("=", 1)
        return rhs.strip()
    raise SystemExit(f"Missing '{key}' in input file")


def sieve_primes(limit: int) -> list[int]:
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if is_prime[p]:
            start = p * p
            step = p
            is_prime[start : limit + 1 : step] = b"\x00" * (((limit - start) // step) + 1)
    return [i for i in range(2, limit + 1) if is_prime[i]]


@dataclass
class Entry:
    n: int
    xi: iv.mpf
    w_q: iv.mpf
    heat: iv.mpf


def precompute_entries(limit: int) -> list[Entry]:
    primes = sieve_primes(limit)
    entries: list[Entry] = []
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
            entries.append(Entry(n=pk, xi=xi, w_q=w_q, heat=heat))
            pk *= p
    entries.sort(key=lambda e: e.n)
    return entries


def main() -> None:
    args = parse_args()
    inp = Path(args.input)
    outp = Path(args.output)

    if not inp.exists():
        raise SystemExit(f"Missing input file: {inp}")

    text = inp.read_text(encoding="utf-8")
    sum_ub_raw = parse_value(text, "prime_heat_sum_up_to_ub")
    B_max_raw = parse_value(text, "B_max")

    # interval precision
    mp.mp.dps = 80

    N = 1_000_000
    bucket_size = args.bucket
    B_max = mp.mpf(B_max_raw)

    entries = precompute_entries(N)

    bucket_ranges: list[tuple[int, int]] = []
    for start in range(1, N + 1, bucket_size):
        end = min(N, start + bucket_size - 1)
        bucket_ranges.append((start, end))

    # accumulate interval sums by bucket
    bucket_sums: list[iv.mpf] = []
    idx = 0
    for start, end in bucket_ranges:
        total = iv.mpf(0)
        while idx < len(entries) and entries[idx].n < start:
            idx += 1
        j = idx
        while j < len(entries) and entries[j].n <= end:
            e = entries[j]
            xi_abs = abs(e.xi)
            if xi_abs.b <= B_max:
                term = e.w_q * e.heat * xi_abs
            elif xi_abs.a > B_max:
                term = iv.mpf(0)
            else:
                # straddling bound; keep upper bound by allowing the indicator to be 1
                term = e.w_q * e.heat * xi_abs
            total += term
            j += 1
        idx = j
        bucket_sums.append(total)

    getcontext().prec = max(50, args.digits + 10)
    quant = Decimal(f"1e-{args.digits}")

    def round_up(x: iv.mpf) -> str:
        upper = mp.mpf(x.b)
        return format(Decimal(mp.nstr(upper, 50)).quantize(quant, rounding=ROUND_CEILING), "f")

    bucket_ub = [round_up(s) for s in bucket_sums]

    # sanity check against the partial-sum upper bound
    total = sum(Decimal(v) for v in bucket_ub)
    sum_ub = Decimal(sum_ub_raw)
    if total > sum_ub:
        raise SystemExit(f"Bucket total {total} exceeds prime_heat_sum_up_to_ub {sum_ub}")

    digest = sha256_hex(inp)
    src = source_label(inp)

    def render_bucket_table(name: str, values: list[str]) -> str:
        lines = [f"def {name} : Fin prime_heat_bucket_count -> ℚ"]
        for idx, val in enumerate(values):
            lines.append(f"| ⟨{idx}, _⟩ => {val}")
        lines.append(f"| _ => {values[-1]}")
        return "\n".join(lines)

    bucket_count = len(bucket_ranges)

    def render_bucket_bounds(name: str, idx: int) -> str:
        lines = [f"def {name} : Fin prime_heat_bucket_count -> ℕ"]
        for k, (a, b) in enumerate(bucket_ranges):
            val = a if idx == 0 else b
            lines.append(f"| ⟨{k}, _⟩ => {val}")
        lines.append(f"| _ => {bucket_ranges[-1][idx]}")
        return "\n".join(lines)

    lo_table = render_bucket_bounds("prime_heat_bucket_lo", 0)
    hi_table = render_bucket_bounds("prime_heat_bucket_hi", 1)
    table = render_bucket_table("prime_heat_bucket_ub_q_get", bucket_ub)

    lean = f"""import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Data

/-!
Bucketed prime-heat partial sums (t_critical, tau = 0).

Source: {src}
Generated by: scripts/prime_brange_heat_interval_checker.py
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Source file (prime-heat partial interval certificate). -/
def prime_cert_heat_bucket_source : String :=
  "{src}"

/-- SHA256 of the source file. -/
def prime_cert_heat_bucket_sha256 : String :=
  "{digest}"

/-- Number of prime-heat buckets. -/
def prime_heat_bucket_count : Nat := {bucket_count}

/-- Bucket lower bounds (inclusive). -/
{lo_table}

/-- Bucket upper bounds (inclusive). -/
{hi_table}

/-- Bucket upper bounds (prime-heat partial sum). -/
{table}

/-- Bucket upper bounds (real). -/
def prime_heat_bucket_ub (k : Fin prime_heat_bucket_count) : ℝ :=
  (prime_heat_bucket_ub_q_get k : ℝ)

end Q3.Proofs.PrimeCert
"""

    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(lean + "\n", encoding="utf-8")
    print(f"Wrote {outp}")


if __name__ == "__main__":
    main()
