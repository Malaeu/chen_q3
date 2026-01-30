#!/usr/bin/env python3
"""
Extract pilot points (B=3.0 and B=4.9) from the existing B-range certificate.

This is a lightweight helper to keep the pilot data traceable in this worktree.
It does NOT recompute any numeric bounds; it only reprints the selected rows
and the tail bound from the certificate file.
"""

from __future__ import annotations

import re
from datetime import datetime
from pathlib import Path

SOURCE = Path("output/prime_cert_brange_tcritical_interval_2026-01-30_2206.txt")
PILOT_BS = [3.0, 4.9]


def parse_rows(text: str):
    rows: dict[float, tuple[str, str, str, str]] = {}
    tail = None
    for line in text.splitlines():
        if "tail_bound" in line:
            # example: tail_bound (n>N) = 2.7839976842107422016355450099369e-09
            parts = line.split("=", 1)
            if len(parts) == 2:
                tail = parts[1].strip()
        line = line.strip()
        if not line or not line[0].isdigit():
            continue
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 5:
            continue
        try:
            B = float(parts[0])
        except ValueError:
            continue
        rows[B] = (parts[1], parts[2], parts[3], parts[4])
    return rows, tail


def main() -> int:
    if not SOURCE.exists():
        raise SystemExit(f"Missing source file: {SOURCE}")

    rows, tail = parse_rows(SOURCE.read_text(encoding="utf-8"))

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out_path = Path(f"output/prime_cert_brange_tcritical_pilot_{ts}.txt")

    lines = []
    lines.append("Prime-term B-range pilot points (t_critical, tau=0)")
    lines.append("==================================================")
    lines.append("")
    lines.append(f"Source: {SOURCE}")
    if tail is not None:
        lines.append(f"tail_bound (n>N) = {tail}")
    lines.append("")
    lines.append("B, prime_sum, prime_ub, arch_term, margin")

    for B in PILOT_BS:
        if B not in rows:
            raise SystemExit(f"Missing row for B={B} in {SOURCE}")
        ps, pub, arch, marg = rows[B]
        lines.append(f"{B:.4f}, {ps}, {pub}, {arch}, {marg}")

    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
