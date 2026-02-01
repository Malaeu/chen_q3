#!/usr/bin/env python3
"""
Generate bucketed interval sums for the full B-grid (20 points).

This produces a Lean file with per-bucket upper bounds for every grid point,
which can be consumed by a future formal interval checker.
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
    p.add_argument("--digits", type=int, default=12)
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


def parse_prime_sums(text: str) -> dict[float, str]:
    rows: dict[float, str] = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or not line[0].isdigit():
            continue
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 2:
            continue
        try:
            B = float(parts[0])
        except ValueError:
            continue
        rows[B] = parts[1]
    if not rows:
        raise SystemExit("No B-grid rows found in input file.")
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

    # interval precision
    mp.mp.dps = 80

    N = 1_000_000
    bucket_size = args.bucket

    prime_rows = parse_prime_sums(inp.read_text(encoding="utf-8"))
    B_values = sorted(prime_rows.keys())

    entries = precompute_entries(N)

    bucket_ranges: list[tuple[int, int]] = []
    for start in range(1, N + 1, bucket_size):
        end = min(N, start + bucket_size - 1)
        bucket_ranges.append((start, end))

    B_iv = [iv.mpf(B) for B in B_values]

    # accumulate interval sums by bucket
    bucket_sums = {B: [] for B in B_values}
    idx = 0
    for start, end in bucket_ranges:
        sums = [iv.mpf(0) for _ in B_values]
        while idx < len(entries) and entries[idx].n < start:
            idx += 1
        j = idx
        while j < len(entries) and entries[j].n <= end:
            e = entries[j]
            for b_idx, B in enumerate(B_iv):
                fejer = iv.mpf(1) - (e.xi / B)
                if fejer.b <= 0:
                    term = iv.mpf(0)
                else:
                    term = e.w_q * fejer * e.heat
                sums[b_idx] += term
            j += 1
        idx = j
        for b_idx, B in enumerate(B_values):
            bucket_sums[B].append(sums[b_idx])

    getcontext().prec = max(50, args.digits + 10)
    quant = Decimal(f"1e-{args.digits}")

    def round_up(x: iv.mpf) -> str:
        upper = mp.mpf(x.b)
        return format(Decimal(mp.nstr(upper, 50)).quantize(quant, rounding=ROUND_CEILING), "f")

    bucket_ub = {B: [round_up(s) for s in bucket_sums[B]] for B in B_values}

    # check total upper bound
    for B in B_values:
        total = sum(Decimal(v) for v in bucket_ub[B])
        prime_sum = Decimal(prime_rows[B])
        if total > prime_sum:
            raise SystemExit(f"Bucket total {total} exceeds prime_sum {prime_sum} for B={B}")

    digest = sha256_hex(inp)
    src = source_label(inp)

    def render_bucket_table(name: str, values: list[str]) -> str:
        lines = [f"def {name} : Fin prime_b_grid_bucket_count -> ℚ"]
        for idx, val in enumerate(values):
            lines.append(f"| ⟨{idx}, _⟩ => {val}")
        lines.append(f"| _ => {values[-1]}")
        return "\n".join(lines)

    bucket_count = len(bucket_ranges)

    def render_bucket_bounds(name: str, idx: int) -> str:
        lines = [f"def {name} : Fin prime_b_grid_bucket_count -> ℕ"]
        for k, (a, b) in enumerate(bucket_ranges):
            val = a if idx == 0 else b
            lines.append(f"| ⟨{k}, _⟩ => {val}")
        lines.append(f"| _ => {bucket_ranges[-1][idx]}")
        return "\n".join(lines)

    lo_table = render_bucket_bounds("prime_b_grid_bucket_lo", 0)
    hi_table = render_bucket_bounds("prime_b_grid_bucket_hi", 1)

    bucket_tables: list[str] = []
    for idx, B in enumerate(B_values):
        bucket_tables.append(
            render_bucket_table(f"prime_b_grid_bucket_ub_q_get_{idx}", bucket_ub[B])
        )
    bucket_sum = [sum(Decimal(v) for v in bucket_ub[B]) for B in B_values]

    table_cases = []
    for idx in range(len(B_values)):
        table_cases.append(f"| ⟨{idx}, _⟩, k => prime_b_grid_bucket_ub_q_get_{idx} k")
    table_cases.append(f"| _, k => prime_b_grid_bucket_ub_q_get_{len(B_values) - 1} k")

    lean = f"""import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_UB
import Q3.Proofs.PrimeCert.BrangeGrid_2046

/-!
Bucketed interval sums for the full B-grid (t_critical, tau = 0).

Source: {src}
Generated by: scripts/prime_brange_interval_checker_grid.py
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Source file (full interval certificate). -/
def prime_cert_brange_bucket_source : String :=
  "{src}"

/-- SHA256 of the source file. -/
def prime_cert_brange_bucket_sha256 : String :=
  "{digest}"

/-- Number of buckets for the full grid certificate. -/
def prime_b_grid_bucket_count : Nat := {bucket_count}

/-- Bucket lower bounds (inclusive). -/
{lo_table}

/-- Bucket upper bounds (inclusive). -/
{hi_table}

"""

    for table in bucket_tables:
        lean += f"/-- Bucket upper bounds for grid index {bucket_tables.index(table)}. -/\n"
        lean += table + "\n\n"

    lean += """/-- Bucket upper bounds (by grid index). -/
def prime_b_grid_bucket_ub_q_get :
    Fin prime_b_grid_size -> Fin prime_b_grid_bucket_count -> ℚ
"""
    lean += "\n".join(table_cases)
    lean += "\n\n/-- Bucket upper bounds (real). -/\ndef prime_b_grid_bucket_ub (i : Fin prime_b_grid_size) (k : Fin prime_b_grid_bucket_count) : ℝ :=\n  (prime_b_grid_bucket_ub_q_get i k : ℝ)\n\n"

    lean += "/-- Sum of bucket upper bounds (by grid index). -/\n"
    lean += "def prime_b_grid_bucket_ub_sum_q_get : Fin prime_b_grid_size -> ℚ\n"
    for idx, total in enumerate(bucket_sum):
        lean += f"| ⟨{idx}, _⟩ => {total}\n"
    lean += f"| _ => {bucket_sum[-1]}\n\n"

    lean += """/-- Sum of bucket upper bounds (real). -/
def prime_b_grid_bucket_ub_sum (i : Fin prime_b_grid_size) : ℝ :=
  (prime_b_grid_bucket_ub_sum_q_get i : ℝ)

lemma prime_b_grid_bucket_ub_sum_le :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_bucket_ub_sum i ≤ prime_b_grid_prime_sum_ub i := by
  intro i
  fin_cases i <;>
    norm_num [prime_b_grid_bucket_ub_sum, prime_b_grid_bucket_ub_sum_q_get,
      prime_b_grid_prime_sum_ub, prime_b_grid_prime_sum_ub_q_get]

end Q3.Proofs.PrimeCert
"""

    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(lean + "\n", encoding="utf-8")
    print(f"Wrote {outp}")


if __name__ == "__main__":
    main()
