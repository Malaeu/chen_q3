#!/usr/bin/env python3
"""
Generate bucketed interval sums for the pilot B values (B=3.0, 4.9).

This produces a Lean file with per-bucket upper bounds that can be used by a
future formal interval checker.
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


def parse_pilot_sums(text: str) -> dict[float, str]:
    rows: dict[float, str] = {}
    current_B: float | None = None
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("B ="):
            try:
                current_B = float(line.split("=", 1)[1].strip())
            except ValueError:
                current_B = None
            continue
        if line.startswith("pilot_prime_sum ="):
            if current_B is None:
                raise SystemExit("pilot_prime_sum without preceding B")
            rows[current_B] = line.split("=", 1)[1].strip()
    if not rows:
        raise SystemExit("No pilot_prime_sum entries found.")
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

    B_VALUES = [3.0, 4.9]
    N = 1_000_000
    bucket_size = args.bucket

    pilot_rows = parse_pilot_sums(inp.read_text(encoding="utf-8"))
    for B in B_VALUES:
        if B not in pilot_rows:
            raise SystemExit(f"Missing pilot row for B={B} in {inp}")

    entries = precompute_entries(N)

    bucket_ranges: list[tuple[int, int]] = []
    for start in range(1, N + 1, bucket_size):
        end = min(N, start + bucket_size - 1)
        bucket_ranges.append((start, end))

    # accumulate interval sums by bucket
    bucket_sums = {B: [] for B in B_VALUES}
    idx = 0
    for start, end in bucket_ranges:
        sums = {B: iv.mpf(0) for B in B_VALUES}
        while idx < len(entries) and entries[idx].n < start:
            idx += 1
        j = idx
        while j < len(entries) and entries[j].n <= end:
            e = entries[j]
            for B in B_VALUES:
                B_iv = iv.mpf(B)
                fejer = iv.mpf(1) - (e.xi / B_iv)
                if fejer.b <= 0:
                    term = iv.mpf(0)
                else:
                    term = e.w_q * fejer * e.heat
                sums[B] += term
            j += 1
        idx = j
        for B in B_VALUES:
            bucket_sums[B].append(sums[B])

    getcontext().prec = max(50, args.digits + 10)
    quant = Decimal(f"1e-{args.digits}")

    def round_up(x: iv.mpf) -> str:
        upper = mp.mpf(x.b)
        return format(Decimal(mp.nstr(upper, 50)).quantize(quant, rounding=ROUND_CEILING), "f")

    bucket_ub = {B: [round_up(s) for s in bucket_sums[B]] for B in B_VALUES}

    # check total upper bound
    for B in B_VALUES:
        total = sum(Decimal(v) for v in bucket_ub[B])
        pilot_sum = Decimal(pilot_rows[B])
        if total > pilot_sum:
            raise SystemExit(f"Bucket total {total} exceeds pilot sum {pilot_sum} for B={B}")

    digest = sha256_hex(inp)
    src = source_label(inp)

    def render_bucket_table(name: str, values: list[str]) -> str:
        lines = [f"def {name} : Fin pilot_bucket_count -> ℚ"]
        for idx, val in enumerate(values):
            lines.append(f"| ⟨{idx}, _⟩ => {val}")
        lines.append(f"| _ => {values[-1]}")
        return "\n".join(lines)

    bucket_count = len(bucket_ranges)

    def render_bucket_bounds(name: str, idx: int) -> str:
        lines = [f"def {name} : Fin pilot_bucket_count -> ℕ"]
        for k, (a, b) in enumerate(bucket_ranges):
            val = a if idx == 0 else b
            lines.append(f"| ⟨{k}, _⟩ => {val}")
        lines.append(f"| _ => {bucket_ranges[-1][idx]}")
        return "\n".join(lines)

    table0 = render_bucket_table("prime_b_grid_pilot_bucket_ub_q_get_0", bucket_ub[B_VALUES[0]])
    table19 = render_bucket_table("prime_b_grid_pilot_bucket_ub_q_get_19", bucket_ub[B_VALUES[1]])

    lo_table = render_bucket_bounds("prime_b_grid_pilot_bucket_lo", 0)
    hi_table = render_bucket_bounds("prime_b_grid_pilot_bucket_hi", 1)

    sum0 = sum(Decimal(v) for v in bucket_ub[B_VALUES[0]])
    sum19 = sum(Decimal(v) for v in bucket_ub[B_VALUES[1]])

    lean = f"""import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_Pilot_2026_01_30_UB
import Q3.Proofs.PrimeCert.BrangeGrid_Pilot_2026_01_30

/-!
Bucketed pilot interval sums (t_critical, tau = 0).

Source: {src}
Generated by: scripts/prime_brange_interval_checker_pilot.py
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Source file (pilot interval certificate). -/
def prime_cert_brange_pilot_bucket_source : String :=
  "{src}"

/-- SHA256 of the pilot source file. -/
def prime_cert_brange_pilot_bucket_sha256 : String :=
  "{digest}"

/-- Number of pilot buckets. -/
def pilot_bucket_count : Nat := {bucket_count}

/-- Bucket lower bounds (inclusive). -/
{lo_table}

/-- Bucket upper bounds (inclusive). -/
{hi_table}

/-- Bucket upper bounds for pilot i0. -/
{table0}

/-- Bucket upper bounds for pilot i19. -/
{table19}

/-- Bucket upper bounds (by pilot index). -/
def prime_b_grid_pilot_bucket_ub_q_get :
    Fin prime_b_grid_size -> Fin pilot_bucket_count -> ℚ
| ⟨0, _⟩, k => prime_b_grid_pilot_bucket_ub_q_get_0 k
| ⟨19, _⟩, k => prime_b_grid_pilot_bucket_ub_q_get_19 k
| _, k => prime_b_grid_pilot_bucket_ub_q_get_19 k

/-- Bucket upper bounds (real). -/
def prime_b_grid_pilot_bucket_ub (i : Fin prime_b_grid_size) (k : Fin pilot_bucket_count) : ℝ :=
  (prime_b_grid_pilot_bucket_ub_q_get i k : ℝ)

/-- Sum of bucket upper bounds (pilot i0). -/
def prime_b_grid_pilot_bucket_ub_sum_0 : ℝ :=
  {sum0}

/-- Sum of bucket upper bounds (pilot i19). -/
def prime_b_grid_pilot_bucket_ub_sum_19 : ℝ :=
  {sum19}

lemma prime_b_grid_pilot_bucket_ub_sum_le_0 :
    prime_b_grid_pilot_bucket_ub_sum_0 ≤ prime_b_grid_pilot_sum_ub pilot_i0 := by
  norm_num [prime_b_grid_pilot_bucket_ub_sum_0,
    prime_b_grid_pilot_sum_ub, prime_b_grid_pilot_sum_ub_q_get]

lemma prime_b_grid_pilot_bucket_ub_sum_le_19 :
    prime_b_grid_pilot_bucket_ub_sum_19 ≤ prime_b_grid_pilot_sum_ub pilot_i19 := by
  norm_num [prime_b_grid_pilot_bucket_ub_sum_19,
    prime_b_grid_pilot_sum_ub, prime_b_grid_pilot_sum_ub_q_get]

end Q3.Proofs.PrimeCert
"""

    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(lean + "\n", encoding="utf-8")
    print(f"Wrote {outp}")


if __name__ == "__main__":
    main()
