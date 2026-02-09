#!/usr/bin/env python3
"""
Generate prime-power upper bounds for the B-grid prime-term buckets.

This is a grid analogue of the heat prime-power table generator:
- choose one grid index i (B = B_min + i * h)
- compute upper bounds for prime-power terms n <= N
- emit Lean lookup tables bucketed by n-ranges

The output is data-only (no theorem proofs yet), intended for checker wiring.
"""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import dataclass
from decimal import ROUND_CEILING, Decimal, getcontext
from pathlib import Path
import re

import mpmath as mp
from mpmath import iv


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--input", required=True, help="Certificate CSV-like source file")
    p.add_argument("--output", required=True, help="Output Lean file")
    p.add_argument("--grid-index", type=int, required=True, help="B-grid index in [0, 19]")
    p.add_argument("--digits", type=int, default=30, help="Decimal digits for rounding-up")
    p.add_argument("--bucket-size", type=int, default=10_000)
    p.add_argument(
        "--buckets",
        default="",
        help="Comma-separated bucket indices to keep; other buckets are emitted empty",
    )
    p.add_argument(
        "--name-prefix",
        default="prime_b_grid_pp",
        help="Lean identifier prefix (sanitized to [A-Za-z0-9_])",
    )
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


def sanitize_ident(s: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_]", "_", s)
    if not out:
        return "prime_b_grid_pp"
    if out[0].isdigit():
        out = "_" + out
    return out


def parse_prime_sums(text: str) -> dict[float, str]:
    rows: dict[float, str] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line or not line[0].isdigit():
            continue
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 2:
            continue
        try:
            b = float(parts[0])
        except ValueError:
            continue
        rows[b] = parts[1]
    if not rows:
        raise SystemExit("No B-grid rows found in input.")
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
    p: int
    xi: iv.mpf
    w_q: iv.mpf
    heat: iv.mpf


def precompute_entries(limit: int) -> list[Entry]:
    primes = sieve_primes(limit)
    out: list[Entry] = []
    two_pi = iv.mpf(2) * iv.pi
    four_pi_sq = iv.mpf(4) * iv.pi * iv.pi
    t_critical = iv.mpf(3) / iv.mpf(20)
    for p in primes:
        logp = iv.log(iv.mpf(p))
        pk = p
        while pk <= limit:
            n_iv = iv.mpf(pk)
            xi = iv.log(n_iv) / two_pi
            w_q = (iv.mpf(2) * logp) / iv.sqrt(n_iv)
            heat = iv.exp(-four_pi_sq * t_critical * xi * xi)
            out.append(Entry(n=pk, p=p, xi=xi, w_q=w_q, heat=heat))
            pk *= p
    out.sort(key=lambda e: e.n)
    return out


def parse_bucket_filter(raw: str) -> set[int] | None:
    if not raw.strip():
        return None
    out: set[int] = set()
    for part in raw.split(","):
        part = part.strip()
        if not part:
            continue
        out.add(int(part))
    return out


def main() -> None:
    args = parse_args()
    inp = Path(args.input)
    outp = Path(args.output)
    if not inp.exists():
        raise SystemExit(f"Missing input: {inp}")
    if not (0 <= args.grid_index < 20):
        raise SystemExit("--grid-index must be in [0, 19]")

    mp.mp.dps = 120
    text = inp.read_text(encoding="utf-8")
    prime_rows = parse_prime_sums(text)
    b_values = sorted(prime_rows.keys())
    if args.grid_index >= len(b_values):
        raise SystemExit(f"grid-index {args.grid_index} out of range for parsed B rows")
    b = iv.mpf(b_values[args.grid_index])

    n_max = 1_000_000
    bucket_size = args.bucket_size
    bucket_count = (n_max + bucket_size - 1) // bucket_size
    bucket_filter = parse_bucket_filter(args.buckets)
    prefix = sanitize_ident(args.name_prefix)

    entries = precompute_entries(n_max)
    bucket_sums = [iv.mpf(0) for _ in range(bucket_count)]
    ub_by_bucket: list[list[tuple[int, str]]] = [[] for _ in range(bucket_count)]

    getcontext().prec = max(90, args.digits + 40)
    quant = Decimal(f"1e-{args.digits}")

    def round_up(x: iv.mpf) -> str:
        upper = mp.mpf(x.b)
        return format(Decimal(mp.nstr(upper, 120)).quantize(quant, rounding=ROUND_CEILING), "f")

    for e in entries:
        k = (e.n - 1) // bucket_size
        if bucket_filter is not None and k not in bucket_filter:
            continue
        fejer = iv.mpf(1) - (abs(e.xi) / b)
        if fejer.b <= 0:
            term = iv.mpf(0)
        else:
            term = e.w_q * fejer * e.heat
        bucket_sums[k] += term
        ub_by_bucket[k].append((e.n, round_up(term)))

    total = sum(Decimal(round_up(s)) for s in bucket_sums)
    prime_sum_ref = Decimal(prime_rows[b_values[args.grid_index]])
    if total > prime_sum_ref:
        raise SystemExit(
            f"Rounded bucket total {total} exceeds source prime_sum {prime_sum_ref} for B={b_values[args.grid_index]}"
        )

    digest = sha256_hex(inp)
    src = source_label(inp)
    den = 10**args.digits

    lines: list[str] = []
    lines.append("import Mathlib")
    lines.append("import Q3.Proofs.PrimeCert.ArrayLookup")
    lines.append("")
    lines.append("/-!")
    lines.append("Prime-power bucket upper bounds for one B-grid index.")
    lines.append(f"Source: {src}")
    lines.append("Generated by: scripts/prime_brange_grid_pp_interval_checker.py")
    lines.append("-/")
    lines.append("")
    lines.append("noncomputable section")
    lines.append("")
    lines.append("namespace Q3.Proofs.PrimeCert")
    lines.append("")
    lines.append(f"def {prefix}_source : String :=")
    lines.append(f'  "{src}"')
    lines.append("")
    lines.append(f"def {prefix}_sha256 : String :=")
    lines.append(f'  "{digest}"')
    lines.append("")
    lines.append(f"def {prefix}_grid_index : Nat := {args.grid_index}")
    lines.append(f"def {prefix}_B : ℝ := {b_values[args.grid_index]}")
    lines.append(f"def {prefix}_bucket_count : Nat := {bucket_count}")
    lines.append(f"def {prefix}_bucket_width : Nat := {bucket_size}")
    lines.append(f"def {prefix}_den : ℚ := {den}")
    lines.append("")

    for k in range(bucket_count):
        lines.append(f"def {prefix}_bucket_{k} : Array (Nat × Nat) := #[")
        for n, ub in ub_by_bucket[k]:
            num = int(Decimal(ub) * den)
            lines.append(f"  ({n}, {num}),")
        lines.append("]")
        lines.append("")

    lines.append(f"def {prefix}_buckets : Array (Array (Nat × Nat)) := #[")
    for k in range(bucket_count):
        lines.append(f"  {prefix}_bucket_{k},")
    lines.append("]")
    lines.append("")

    lines.append(f"def {prefix}_bucket_index (n : ℕ) : ℕ :=")
    lines.append(f"  (n - 1) / {prefix}_bucket_width")
    lines.append("")
    lines.append(f"def {prefix}_ub_q_get_bucket (arr : Array (Nat × Nat)) (n : ℕ) : ℚ :=")
    lines.append("  match natArrayLookup arr n with")
    lines.append(f"  | some num => (num : ℚ) / {prefix}_den")
    lines.append("  | none => 0")
    lines.append("")
    lines.append(f"def {prefix}_ub_q_get (n : ℕ) : ℚ :=")
    lines.append(f"  match {prefix}_buckets[{prefix}_bucket_index n]? with")
    lines.append(f"  | some arr => {prefix}_ub_q_get_bucket arr n")
    lines.append("  | none => 0")
    lines.append("")
    lines.append(f"def {prefix}_ub (n : ℕ) : ℝ :=")
    lines.append(f"  ({prefix}_ub_q_get n : ℝ)")
    lines.append("")

    for k in range(bucket_count):
        if bucket_filter is not None and k not in bucket_filter:
            continue
        total_k = sum(int(Decimal(ub) * den) for _, ub in ub_by_bucket[k])
        lines.append(f"def {prefix}_ub_q_sum_bucket_{k} : ℚ :=")
        lines.append(f"  ({total_k} : ℚ) / {prefix}_den")
        lines.append("")

    if bucket_filter is None:
        lines.append(f"def {prefix}_ub_q_sum_get : Fin {prefix}_bucket_count -> ℚ")
        for k in range(bucket_count):
            lines.append(f"| ⟨{k}, _⟩ => {prefix}_ub_q_sum_bucket_{k}")
        lines.append(f"| _ => {prefix}_ub_q_sum_bucket_{bucket_count - 1}")
        lines.append("")

    lines.append("end Q3.Proofs.PrimeCert")

    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {outp}")


if __name__ == "__main__":
    main()
