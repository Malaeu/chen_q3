#!/usr/bin/env python3
"""Probe 19 (Goal 058, 2026-09-04): judge's R2 — second jet of ground vs CCM prolate trial vs Xi.

kappa(v) = -F_v''(0)/(2F_v(0)) = (L^2/2)[1/12 + (1/(pi^2 c_0)) sum_{k>=1} c_k/k^2] for ANY even mode vector c
(full coefficients c_k, c_{-k} = c_k); exact from the P59 transform's Taylor expansion at 0.
Cells: trial caches (13,13),(23,23),(43,43),(83,83; MAX_DEGREE=600 regenerated 2026-09-04) + bonus (13,120). DIAGNOSTIC_NEVER_A_PROOF.
Usage: .venv/bin/python docs/routeB_bus/phase5_codex/r2_second_jet.py
"""
from __future__ import annotations
import sys, math
from pathlib import Path
from fractions import Fraction
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "phase5_scripts"))
from flint import arb, acb_mat, ctx  # noqa: E402
from edge_ledger_build import CCMArbBuilder, inverse_iteration_ground  # noqa: E402
from edge_ledger_relritz import q_projected_exact_even  # noqa: E402

KAPPA_X = 0.0231049931154  # = (1/2)(log xi)''(1/2), verified 2026-09-04 (mpmath) against S_X(1e-4)

def f(x): return float(x.mid())

def kappa_full(c: dict[int, float], L: float) -> float:
    return (L * L / 2) * (1 / 12 + (1 / (math.pi ** 2 * c[0])) * sum(c[k] / (k * k) for k in range(1, max(c) + 1)))

def ground_full(m: int, N: int, dps: int) -> tuple[dict[int, float], float]:
    ctx.dps = dps
    b = CCMArbBuilder(m, N); ev = b.even_block()
    if N <= 43:
        E, R = acb_mat(ev).eig(right=True)
        i1 = min(range(N + 1), key=lambda i: f(E[i].real)); u = [R[r, i1].real for r in range(N + 1)]
    else:
        lam1, u, res = inverse_iteration_ground(ev, N + 1, 6)
    s2 = math.sqrt(2)
    c = {0: f(u[0])}
    for n in range(1, N + 1): c[n] = f(u[n]) / s2
    if c[0] < 0: c = {k: -v for k, v in c.items()}
    return c, f(b.L)

def main() -> int:
    print("| cell | L | T_m | kappa(G) | kappa(q) | alpha_G=kG-kX | alpha_q=kq-kX | delta=kG-kq | alpha_q/T | delta/T | p=1-<xi,q>^2 | sup|dr_n| | sum|dr_n|/n^2 |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for m, N, dps in ((13, 13, 220), (23, 23, 320), (43, 43, 460), (83, 83, 700), (13, 120, 240)):
        c, L = ground_full(m, N, dps)
        proj, meta = q_projected_exact_even(m, N)
        norm = math.sqrt(float(sum(x * x for x in proj)))
        q = {n: float(proj[n + N]) / norm for n in range(0, N + 1)}
        if q[0] < 0: q = {k: -v for k, v in q.items()}
        gnorm = math.sqrt(c[0] ** 2 + 2 * sum(c[n] ** 2 for n in range(1, N + 1)))
        inner = (c[0] * q[0] + 2 * sum(c[n] * q[n] for n in range(1, N + 1))) / gnorm
        p = 1 - inner * inner
        T = (L * L / (4 * math.pi ** 2)) * sum(1 / (k * k) for k in range(N + 1, 400000))
        kG, kq = kappa_full(c, L), kappa_full(q, L)
        dr = {n: c[n] / c[0] - q[n] / q[0] for n in range(1, N + 1)}
        sup = max(abs(v) for v in dr.values()); wsum = sum(abs(v) / (n * n) for n, v in dr.items())
        print(f"| ({m},{N}) | {L:.4f} | {T:.3e} | {kG:.10f} | {kq:.10f} | {kG-KAPPA_X:+.3e} | {kq-KAPPA_X:+.3e} | {kG-kq:+.3e} | {(kq-KAPPA_X)/T:+.3f} | {(kG-kq)/T:+.3f} | {p:.2e} | {sup:.2e} | {wsum:.2e} |", flush=True)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
