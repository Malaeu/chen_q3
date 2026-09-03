#!/usr/bin/env python3
"""S7 table generator (Goal 058, 2026-09-04): source-only D_n versus the W02 pole diagonal.

Strange thing S7 (energy preflight, docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT.md §10):
the arch/prime diagonal defect
    D_n := -W_R(n,n) - Prime(n,n) - a_n            (mu = (K y)_0 ~ lambda_1 dropped: it is < 1e-25 on every cell)
    a_n := b_n - p_n,  b_n := tau(n,0),  p_n := A_L / d_n,  A_L := 32 L sinh^2(L/4),  d_n := L^2 + 16 pi^2 n^2
and the pole diagonal
    P_n := 32 pi^2 A_L n^2 / d_n^2
are built from DISJOINT parts of the CCM source, yet D_n / P_n = 0.9982 .. 1.0000 at n = 1 on m = 13..163.
Their difference delta_n = D_n - P_n is the odd-sector diagonal of D - lambda_1 (>= 0 by interlacing).

This script needs NO eigen-solve: every quantity is a builder entry. It produces a table over many
windows m and modes n for (a) the live metric "does the ratio tend to 1 as m grows" and (b) a later
symbolic-regression pass (PySR) on delta_n(n, L).

Reading A of S7: delta_n is the shadow of a source identity (b_n nearly constant at low modes).
Reading B: coincidence on five cells. This table is the distinguishing measurement over hundreds of cells.
DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.

Usage: .venv/bin/python docs/routeB_bus/phase5_codex/s7_table.py [--m-max 600] [--n-max 12] [--dps 60]
Output: docs/routeB_bus/phase5_codex/out/s7_table.csv and s7_table.md; one progress line per window (ETA).
"""
from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
PHASE5_SCRIPTS = HERE.parent / "phase5_scripts"
sys.path.insert(0, str(PHASE5_SCRIPTS))
from edge_ledger_build import CCMArbBuilder  # noqa: E402

OUT_DIR = HERE / "out"


def f(x: arb) -> float:
    return float(x.mid())


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--m-max", type=int, default=600)
    ap.add_argument("--m-min", type=int, default=13)
    ap.add_argument("--m-step", type=int, default=1)
    ap.add_argument("--n-max", type=int, default=12)
    ap.add_argument("--dps", type=int, default=60)
    args = ap.parse_args()

    ctx.dps = args.dps
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    csv_path = OUT_DIR / "s7_table.csv"
    md_path = OUT_DIR / "s7_table.md"

    ms = list(range(args.m_min, args.m_max + 1, args.m_step))
    total = len(ms)
    t0 = time.monotonic()
    rows: list[dict[str, float | int]] = []
    summary: list[tuple[int, float, float, float, float, float]] = []

    with csv_path.open("w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["m", "L", "n", "D_n", "P_n", "ratio", "delta_n", "delta_n_L2", "b_n", "a_n", "p_n"])
        for i, m in enumerate(ms):
            N = args.n_max  # entries only depend on (m, L, n); N only sizes the builder's caches
            b = CCMArbBuilder(m, N)
            L = b.L
            pi = b.pi
            A_L = 32 * L * (L / 4).sinh() ** 2
            per_n = []
            for n in range(1, args.n_max + 1):
                d_n = L * L + 16 * pi**2 * n * n
                b_n = b.tau_entry(n, 0)
                p_n = A_L / d_n
                a_n = b_n - p_n
                D_n = -b.wr(n, n) - b.prime(n, n) - a_n
                P_n = 32 * pi**2 * A_L * n * n / (d_n * d_n)
                delta = D_n - P_n
                ratio = D_n / P_n
                w.writerow([m, f(L), n, f(D_n), f(P_n), f(ratio), f(delta), f(delta * L * L), f(b_n), f(a_n), f(p_n)])
                per_n.append((n, f(ratio), f(delta), f(delta * L * L), f(b_n)))
            fh.flush()
            r1, r2, r3 = per_n[0][1], per_n[1][1], per_n[2][1]
            d1L2 = per_n[0][3]
            bvar = max(abs(x[4] - per_n[0][4]) for x in per_n[:8]) / abs(per_n[0][4])
            neg = sum(1 for x in per_n if x[2] < 0)
            summary.append((m, r1, r2, r3, d1L2, bvar))
            elapsed = time.monotonic() - t0
            rate = (i + 1) / elapsed if elapsed > 0 else 0
            eta = (total - i - 1) / rate if rate > 0 else float("nan")
            # live metric: ratio at n=1..3 (reading A predicts -> 1), delta_1*L^2 (floor scale), b_n variation, #negative delta
            print(
                f"[s7 {i+1}/{total} {100*(i+1)/total:5.1f}% eta {eta/60:5.1f}m] m={m:4d} L={f(L):6.3f} "
                f"ratio(n=1..3)={r1:.6f} {r2:.6f} {r3:.6f}  delta_1*L^2={d1L2:.3e}  b_var(n<=8)={bvar:.2e}  neg_delta={neg}",
                flush=True,
            )

    with md_path.open("w") as fh:
        fh.write("# S7 table — source-only D_n vs pole diagonal P_n (DIAGNOSTIC_NEVER_A_PROOF)\n\n")
        fh.write(f"m = {ms[0]}..{ms[-1]} step {args.m_step}, n = 1..{args.n_max}, dps {args.dps}. CSV: `out/s7_table.csv`.\n\n")
        fh.write("| m | ratio n=1 | ratio n=2 | ratio n=3 | delta_1·L² | b_n variation (n≤8) |\n|---:|---:|---:|---:|---:|---:|\n")
        for m, r1, r2, r3, d1L2, bvar in summary:
            if m in (ms[0], ms[-1]) or m % 25 == 0 or m in (13, 23, 43, 83, 163):
                fh.write(f"| {m} | {r1:.6f} | {r2:.6f} | {r3:.6f} | {d1L2:.3e} | {bvar:.2e} |\n")
        rs = [s[1] for s in summary]
        fh.write(f"\nratio(n=1): min {min(rs):.6f}, max {max(rs):.6f}, last {rs[-1]:.6f}.\n")
    print(f"[s7] wrote {csv_path} and {md_path} in {time.monotonic()-t0:.1f}s", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
