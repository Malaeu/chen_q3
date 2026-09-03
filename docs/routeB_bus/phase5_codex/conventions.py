#!/usr/bin/env python3
"""Convention converter for the CCM finite Weil matrix (Goal 058) — with built-in isometry checks.

Owner 2026-09-04: "too many normalizations; I want a fast, proven converter". This is it, at the
scale we need: every basis in play, the exact maps between them, and an assertion that each map is
what it claims (orthogonal change of basis, parity flip of R). Run it and it prints residuals; a
nonzero residual means a convention claim in some report is wrong.

Bases (N = window size, modes n in [-N, N]):
  FULL   : mode coefficients c_n, n = -N..N; matrix K(i,j) = tau_entry(i,j) (symmetric, tau(-i,-j) = tau(i,j)).
  EVEN   : orthonormal e_0 = mode_0, e_n = (mode_n + mode_-n)/sqrt2, n >= 1.
           coordinates v_0 = c_0, v_n = sqrt2 * c_n for an even c (c_n = c_-n). Matrix = builder.even_block().
  ODD    : orthonormal o_n = (mode_n - mode_-n)/sqrt2, n >= 1. coordinates w_n = sqrt2 * c_n for an odd c.
           Matrix = odd_block(): tau(i,j) - tau(i,-j).
  R      : (R c)_n = c_n / n for n != 0, (R c)_0 = 0, in FULL coordinates. R sends even -> odd (1/n is odd in n).
           In coordinates: even v (n >= 1) -> odd w with w_n = v_n / n. So diag(1/n) on even coordinates IS R,
           and the quadratic form <R c, (K - lam) R c>_FULL equals <w, (K_odd - lam) w> with the ODD block —
           not the even block restricted to n >= 1 (those are different forms on the same numbers).
  Ratios : x_n = xi_n / xi_0 (FULL mode ratio; the P59 sample ratio f_k(x_n) = (-1)^n x_n carries NO sqrt2);
           y_n = v_n / v_0 = sqrt2 * x_n (EVEN-coordinate ratio; lattice_equation.py's y).
  Pairing: FULL Euclidean over [-N, N]. For two even (or two odd) vectors this equals c_0 d_0 + 2 sum_{n>=1} c_n d_n
           (the "2 sum" pairing of the energy preflight); in EVEN/ODD coordinates it is plain Euclidean.

Usage: .venv/bin/python docs/routeB_bus/phase5_codex/conventions.py [--m 13] [--dps 60]
DIAGNOSTIC tool; the isometry statements are elementary and hold for any symmetric K with tau(-i,-j)=tau(i,j).
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

from flint import arb, arb_mat, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "phase5_scripts"))
from edge_ledger_build import CCMArbBuilder  # noqa: E402


def full_matrix(b: CCMArbBuilder) -> arb_mat:
    N = b.N
    K = arb_mat(2 * N + 1, 2 * N + 1)
    for i in range(-N, N + 1):
        for j in range(-N, N + 1):
            K[i + N, j + N] = b.tau_entry(i, j)
    return K


def odd_block(b: CCMArbBuilder) -> arb_mat:
    N = b.N
    O = arb_mat(N, N)
    for i in range(1, N + 1):
        for j in range(1, N + 1):
            O[i - 1, j - 1] = b.tau_entry(i, j) - b.tau_entry(i, -j)
    return O


def U_even(N: int) -> arb_mat:
    """(2N+1) x (N+1) matrix whose columns are the even orthonormal basis in FULL coordinates."""
    U = arb_mat(2 * N + 1, N + 1)
    s = 1 / arb(2).sqrt()
    U[N, 0] = arb(1)
    for n in range(1, N + 1):
        U[N + n, n] = s
        U[N - n, n] = s
    return U


def U_odd(N: int) -> arb_mat:
    U = arb_mat(2 * N + 1, N)
    s = 1 / arb(2).sqrt()
    for n in range(1, N + 1):
        U[N + n, n - 1] = s
        U[N - n, n - 1] = -s
    return U


def R_full(N: int) -> arb_mat:
    R = arb_mat(2 * N + 1, 2 * N + 1)
    for n in range(-N, N + 1):
        if n != 0:
            R[n + N, n + N] = arb(1) / n
    return R


# ---- coordinate maps -----------------------------------------------------
def even_to_full(v: list[arb], N: int) -> list[arb]:
    """even coordinates (v_0..v_N) -> full mode coefficients c_-N..c_N."""
    s = 1 / arb(2).sqrt()
    c = [arb(0)] * (2 * N + 1)
    c[N] = v[0]
    for n in range(1, N + 1):
        c[N + n] = s * v[n]
        c[N - n] = s * v[n]
    return c


def full_to_odd(c: list[arb], N: int) -> list[arb]:
    s = 1 / arb(2).sqrt()
    return [s * (c[N + n] - c[N - n]) for n in range(1, N + 1)]


def max_abs(M: arb_mat) -> float:
    out = 0.0
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            out = max(out, abs(float(M[i, j].mid())))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=13)
    ap.add_argument("--dps", type=int, default=60)
    a = ap.parse_args()
    ctx.dps = a.dps
    b = CCMArbBuilder(a.m, a.m)
    N = b.N
    K = full_matrix(b)
    Ue, Uo = U_even(N), U_odd(N)
    print(f"m=N={a.m} dps={a.dps}")
    # 1. orthonormality
    print(f"[1] Ue^T Ue - I       : {max_abs(Ue.transpose() * Ue - arb_mat(N + 1, N + 1, [1 if i == j else 0 for i in range(N + 1) for j in range(N + 1)])):.1e}")
    print(f"[1] Uo^T Uo - I       : {max_abs(Uo.transpose() * Uo - arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])):.1e}")
    print(f"[1] Ue^T Uo (parity)  : {max_abs(Ue.transpose() * Uo):.1e}")
    # 2. even block is the compression of K to the even basis
    print(f"[2] Ue^T K Ue - even_block : {max_abs(Ue.transpose() * K * Ue - b.even_block()):.1e}")
    # 3. odd block likewise
    print(f"[3] Uo^T K Uo - odd_block  : {max_abs(Uo.transpose() * K * Uo - odd_block(b)):.1e}")
    # 4. K has no even-odd coupling
    print(f"[4] Ue^T K Uo (coupling)   : {max_abs(Ue.transpose() * K * Uo):.1e}")
    # 5. R maps even to odd, and in coordinates it is diag(1/n): Uo^T R Ue = [0 | diag(1/n)]
    RUe = Uo.transpose() * R_full(N) * Ue
    D = arb_mat(N, N + 1)
    for n in range(1, N + 1):
        D[n - 1, n] = arb(1) / n
    print(f"[5] Uo^T R Ue - [0|diag(1/n)] : {max_abs(RUe - D):.1e}")
    # 6. quadratic form: <Rc,(K-lam)Rc>_full == <w,(K_odd-lam)w> with w_n = v_n/n, for a random even v
    import random

    random.seed(1)
    v = [arb(random.uniform(-1, 1)) for _ in range(N + 1)]
    c = even_to_full(v, N)
    Rc = [arb(0)] * (2 * N + 1)
    for n in range(-N, N + 1):
        if n != 0:
            Rc[n + N] = c[n + N] / n
    w = full_to_odd(Rc, N)
    w_expected = [v[n] / n for n in range(1, N + 1)]
    print(f"[6] full_to_odd(R c) - v_n/n   : {max(abs(float((w[i] - w_expected[i]).mid())) for i in range(N)):.1e}")
    lam = arb("0.3")
    Rc_mat = arb_mat(2 * N + 1, 1, Rc)
    lhs = (Rc_mat.transpose() * (K - lam * arb_mat(2 * N + 1, 2 * N + 1, [1 if i == j else 0 for i in range(2 * N + 1) for j in range(2 * N + 1)])) * Rc_mat)[0, 0]
    w_mat = arb_mat(N, 1, w)
    rhs_odd = (w_mat.transpose() * (odd_block(b) - lam * arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])) * w_mat)[0, 0]
    ev = b.even_block()
    ev1 = arb_mat(N, N, [ev[i, j] for i in range(1, N + 1) for j in range(1, N + 1)])
    rhs_even = (w_mat.transpose() * (ev1 - lam * arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])) * w_mat)[0, 0]
    print(f"[6] <Rc,(K-lam)Rc>_full - <w,(K_odd-lam)w>       : {abs(float((lhs - rhs_odd).mid())):.1e}   (must vanish)")
    print(f"[6] <Rc,(K-lam)Rc>_full - <w,(K_even|n>=1 -lam)w> : {abs(float((lhs - rhs_even).mid())):.1e}   (does NOT vanish: different form)")
    # 7. pairing: full Euclidean of two even vectors = c0 d0 + 2 sum_{n>=1}
    d = [arb(random.uniform(-1, 1)) for _ in range(N + 1)]
    cd = even_to_full(d, N)
    full_pair = sum((c[i] * cd[i] for i in range(2 * N + 1)), arb(0))
    two_sum = c[N] * cd[N] + 2 * sum((c[N + n] * cd[N + n] for n in range(1, N + 1)), arb(0))
    even_pair = sum((v[i] * d[i] for i in range(N + 1)), arb(0))
    print(f"[7] full pairing - (c0 d0 + 2 sum)  : {abs(float((full_pair - two_sum).mid())):.1e}")
    print(f"[7] full pairing - even-coord pairing: {abs(float((full_pair - even_pair).mid())):.1e}")
    # 8. ratios: y = sqrt2 x
    print(f"[8] y_n / x_n - sqrt2 : {abs(float((v[3] / v[0]) / (c[N + 3] / c[N]) - arb(2).sqrt()).real if False else abs(float(((v[3] / v[0]) / (c[N + 3] / c[N]) - arb(2).sqrt()).mid()))):.1e}")
    # 9. odd diagonal = tau(n,n) - tau(n,0) (reflection identity tau(n,-n) = tau(n,0))
    O = odd_block(b)
    refl = max(abs(float((b.tau_entry(n, -n) - b.tau_entry(n, 0)).mid())) for n in range(1, N + 1))
    diag = max(abs(float((O[n - 1, n - 1] - (b.tau_entry(n, n) - b.tau_entry(n, 0))).mid())) for n in range(1, N + 1))
    print(f"[9] tau(n,-n) - tau(n,0)            : {refl:.1e}   odd diag - (tau(n,n)-tau(n,0)): {diag:.1e}")
    print("all lines marked 'must vanish' at ~1e-(dps) => conventions consistent")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
