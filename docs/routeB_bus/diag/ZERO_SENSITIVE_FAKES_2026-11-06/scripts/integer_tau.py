#!/usr/bin/env python3
"""Generate exact Ramanujan tau prime weights for the T2 Euler inverse.

This uses the already installed python-flint runtime; it adds no dependencies.
The exact fmpz series is temporary. The binary output is a dense, native
little-endian array of doubles indexed by n, with only prime entries nonzero.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import resource
import struct
import sys
import time


def primes_up_to(limit: int) -> bytearray:
    is_prime = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        is_prime[0] = 0
    if limit >= 1:
        is_prime[1] = 0
    for p in range(2, math.isqrt(limit) + 1):
        if is_prime[p]:
            start = p * p
            count = (limit - start) // p + 1
            is_prime[start : limit + 1 : p] = b"\x00" * count
    return is_prime


def euler_series(limit: int):
    try:
        from flint import ctx, fmpz_series
    except ImportError as exc:
        raise RuntimeError(
            "python-flint is unavailable; run with the repository .venv interpreter"
        ) from exc

    ctx.cap = limit + 1
    pentagonal = [0] * (limit + 1)
    pentagonal[0] = 1
    k = 1
    while True:
        g1 = k * (3 * k - 1) // 2
        g2 = k * (3 * k + 1) // 2
        if g1 > limit:
            break
        sign = -1 if k & 1 else 1
        pentagonal[g1] = sign
        if g2 <= limit:
            pentagonal[g2] = sign
        k += 1
    euler = fmpz_series(pentagonal, prec=limit + 1)
    del pentagonal
    eta24 = euler**24
    del euler
    q = fmpz_series([0, 1], prec=limit + 1)
    tau = eta24 * q
    del eta24
    return tau


def max_rss() -> int:
    """Return getrusage's platform-defined ru_maxrss value without unit guessing."""
    return int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=10_000_000)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    if args.limit < 2:
        parser.error("--limit must be at least 2")
    if sys.byteorder != "little":
        raise RuntimeError("the T2 C++ reader expects native little-endian doubles")

    started = time.monotonic()
    rss_before = max_rss()
    print(
        f"PHASE tau_exact start limit={args.limit} method=fmpz_series_euler_pentagonal_power24 "
        f"series_cap={args.limit + 1} expected_weight_bytes={(args.limit + 1) * 8}",
        flush=True,
    )
    tau = euler_series(args.limit)
    is_prime = primes_up_to(args.limit)
    raw = bytearray((args.limit + 1) * 8)
    prime_count = 0
    scan_started = time.monotonic()
    next_progress = 1_000_000
    for p in range(2, args.limit + 1):
        if not is_prime[p]:
            continue
        # tau(q) = q * product_{n>=1}(1-q^n)^24. Only prime coefficients
        # are needed by the inverse Euler factors.
        coefficient = int(tau[p])
        normalized = -float(coefficient) / math.pow(float(p), 5.5)
        struct.pack_into("<d", raw, p * 8, normalized)
        prime_count += 1
        if p >= next_progress:
            elapsed = time.monotonic() - scan_started
            fraction = p / args.limit
            eta = elapsed * (1.0 / fraction - 1.0)
            print(
                f"PROGRESS tau_prime_index p={p}/{args.limit} pct={100.0 * fraction:.1f} "
                f"elapsed_s={elapsed:.1f} eta_s={eta:.1f}",
                flush=True,
            )
            next_progress += 1_000_000

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(raw)
    digest = hashlib.sha256(raw).hexdigest()
    receipt = {
        "status": "PASS",
        "classification": "EXACT_TAU_SERIES_WITH_BINARY64_NORMALIZED_PRIME_WEIGHTS",
        "limit": args.limit,
        "series": "fmpz_series Euler pentagonal product raised exactly to 24, then multiplied by q",
        "series_cap": args.limit + 1,
        "coefficient_indices_used": "prime p only; exact tau(p) converted to binary64 before division by p^5.5",
        "prime_count": prime_count,
        "output_bytes": len(raw),
        "output_sha256": digest,
        "output_path": str(args.output),
        "output_lifecycle": "temporary binary consumed by the integer C++ run and removed with its temporary directory",
        "ru_maxrss_platform_units_before": rss_before,
        "ru_maxrss_platform_units_after": max_rss(),
        "elapsed_seconds": time.monotonic() - started,
        "normalization": "b(p)=-tau(p)/p^(11/2), b(p^2)=1, b(p^e)=0 for e>=3",
    }
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"TAU_GENERATION_RECEIPT {json.dumps(receipt, sort_keys=True)}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
