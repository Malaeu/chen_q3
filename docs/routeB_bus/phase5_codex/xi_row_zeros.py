#!/usr/bin/env python3
"""Probe 12 (precommit ADDENDUM 13, 2026-09-04): zeros of the P59 numerator for the ground row and the Xi-sample row.

Written and run by the orchestrator (rule 13: decisive number by hand). For m = N in --cells, dps per cell:
  ground row x_n = xi_n/xi_0 (raw mode ratio, even eigenvector of CCMArbBuilder.even_block()),
  Xi row y_n = (-1)^n centeredXi(2 pi n/L)/centeredXi(0) (raw ratio; same convention, no sqrt2),
  numerator P(z) = sum_{|k|<=N} c_k prod_{j!=k}(z - x_j), x_j = 2 pi j/L; zeros of P = off-lattice zeros of the transform.
Prints: number of non-real roots (midpoint test |Im| > 1e-6 max(1,|z|)), first positive zeros vs the Riemann zeros
(mpmath.zetazero at 25 digits), sign-flip sets. Lesson 2026-09-04: never test a ball with a strict threshold
(undecidable comparison reads as False); use midpoints. DIAGNOSTIC_NEVER_A_PROOF.
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
from flint import arb, acb, acb_mat, acb_poly, ctx
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "phase5_scripts")); sys.path.insert(0, str(HERE))
from edge_ledger_build import CCMArbBuilder  # noqa: E402
from lattice_error import centered_xi  # noqa: E402

def f(x): return float(x.mid())

def ground_raw(ev, N):
    E, R = acb_mat(ev).eig(right=True); idx = min(range(N + 1), key=lambda i: f(E[i].real))
    v = [R[i, idx].real for i in range(N + 1)]
    return [arb(1)] + [(v[n] / v[0]) / arb(2).sqrt() for n in range(1, N + 1)]

def numerator_roots(c, N, L):
    pi = arb.pi(); x = {k: 2 * pi * k / L for k in range(-N, N + 1)}; P = acb_poly([0])
    for k in range(-N, N + 1):
        t = acb_poly([acb(c[abs(k)])])
        for j in range(-N, N + 1):
            if j != k: t = t * acb_poly([acb(-x[j]), acb(1)])
        P = P + t
    return [(f(r.real), f(r.imag)) for r in P.roots()]

def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--cells", default="13:200,23:300,43:420"); ap.add_argument("--nzeros", type=int, default=8)
    a = ap.parse_args()
    import mpmath
    mpmath.mp.dps = 30
    gamma = [float(mpmath.zetazero(k).imag) for k in range(1, a.nzeros + 1)]
    for cell in a.cells.split(","):
        m, dps = (int(t) for t in cell.split(":")); ctx.dps = dps
        b = CCMArbBuilder(m, m); N = m; L = b.L; pi = b.pi
        x = ground_raw(b.even_block(), N); Xi0 = centered_xi(acb(0)).real
        y = [arb(1)] + [((-1) ** n) * centered_xi(acb(2 * pi * n / L)).real / Xi0 for n in range(1, N + 1)]
        for name, c in (("ground", x), ("xi_row", y)):
            rr = numerator_roots(c, N, L)
            nonreal = [(p, q) for p, q in rr if abs(q) > 1e-6 * max(1.0, abs(p))]
            pos = sorted(p for p, q in rr if abs(q) <= 1e-6 * max(1.0, abs(p)) and p > 0)
            cmp = " ".join(f"{p:.6f}({p - g:+.1e})" for p, g in zip(pos[: a.nzeros], gamma))
            print(f"m={m} dps={dps} {name:7s}: roots={len(rr)} NONREAL={len(nonreal)} | zeros vs gamma_j: {cmp}", flush=True)
        sx = [n for n in range(1, N + 1) if f(((-1) ** n) * x[n]) < 0]; sy = [n for n in range(1, N + 1) if f(((-1) ** n) * y[n]) < 0]
        print(f"      sign flips: ground {sx[:8]} ({len(sx)}) | xi_row {sy[:8]} ({len(sy)}) | same={sx == sy}", flush=True)

if __name__ == "__main__":
    raise SystemExit(main())
