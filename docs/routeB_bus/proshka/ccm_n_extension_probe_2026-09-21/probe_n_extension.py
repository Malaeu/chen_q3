#!/usr/bin/env python3
"""Cheap VOI probe: does ||B^{-1} r|| fall as Fourier N grows, at fixed m?

Analytic packet: even spheroidal 0/4 Ferrers jets of the angular ODE at c^2=m,
mapped by the Mellin generator of exact_generator.py (no quadrature in q).
Weil matrix: literal W02 - WR - Prime, mpmath, DIAGNOSTIC_NEVER_A_PROOF.

    python3 probe_n_extension.py
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
GEN = ROOT.parent / "ccm_exact_source_generator_2026-09-20"
sys.path.insert(0, str(GEN))
import exact_generator as gen  # noqa: E402

M_FIXED = 2
N_LIST = (1, 2, 3)
J_FERRERS = 12
DPS = 40


def even_chi(c2, n_even_index: int, terms: int):
    """Characteristic values of the even angular ODE; index 0,1,2 -> n=0,2,4."""

    def u_last(chi):
        u_prev = mp.mpf(0)
        u = mp.mpf(1)
        for j in range(terms - 1):
            nxt = ((2 * j * (2 * j + 1) - chi) * u + c2 * u_prev) / (
                (2 * j + 2) * (2 * j + 1)
            )
            u_prev, u = u, nxt
        return u

    # Even spheroidal chi starts near n(n+1) + c^2/2.
    seeds = [n * (n + 1) + c2 / 2 for n in range(0, 12, 2)]
    found = []
    for seed in seeds:
        try:
            chi = mp.findroot(u_last, seed)
        except Exception:
            continue
        if all(abs(chi - x) > mp.mpf("1e-8") for x in found):
            found.append(chi)
        if len(found) > n_even_index:
            break
    found.sort()
    if len(found) <= n_even_index:
        raise RuntimeError(f"not enough even chi: {found}")
    return found[n_even_index]


def taylor_to_ferrers(u, terms: int):
    """f=sum u_j t^{2j} -> A_k of sum A_k P_{2k}, then a_k = (-1)^k A_k."""
    A = []
    for k in range(terms):
        # A_k = (4k+1) int_0^1 f(t) P_{2k}(t) dt  (even function, full-line factor)
        def integrand(t, kk=k):
            f = mp.fsum(u[j] * t ** (2 * j) for j in range(terms))
            return f * mp.legendre(2 * kk, t)

        integ = mp.quad(integrand, [0, 1])
        A.append((4 * k + 1) * integ)
    return [((-1) ** k) * A[k] for k in range(terms)]


def ferrers_packet(c2, terms: int):
    chi0 = even_chi(c2, 0, terms + 2)
    chi4 = even_chi(c2, 2, terms + 2)
    u0, u4 = [mp.mpf(1)], [mp.mpf(1)]
    # reuse recurrence
    def jet(chi):
        out = [mp.mpf(1)]
        u_prev = mp.mpf(0)
        u = mp.mpf(1)
        for j in range(terms - 1):
            nxt = ((2 * j * (2 * j + 1) - chi) * u + c2 * u_prev) / (
                (2 * j + 2) * (2 * j + 1)
            )
            u_prev, u = u, nxt
            out.append(u)
        return out

    a0 = taylor_to_ferrers(jet(chi0), terms)
    a4 = taylor_to_ferrers(jet(chi4), terms)
    return chi0, chi4, a0, a4


def q_source_row(m: int, N: int, a0, a4):
    """Normalized Mellin row n=-N..N of the 0/4 packet. Exact generator, mp."""
    J = len(a0)
    b = [a4[0] * a0[j] - a0[0] * a4[j] for j in range(J)]
    row = []
    for n in range(-N, N + 1):
        s = mp.fsum(
            b[j] * ((-1) ** j) * _poly_kernel(m, n, 2 * j) for j in range(J) if b[j] != 0
        )
        row.append(s)
    # Euclidean C^{2N+1} norm
    nrm = mp.sqrt(mp.fsum(z.conjugate() * z for z in row).real)
    if nrm == 0:
        raise RuntimeError("zero packet")
    return [z / nrm for z in row]


def _poly_kernel(m, n, degree):
    """Mellin of t^degree via monomial_kernel identity, mp."""
    return gen._mp_kernel(m, n, degree)


def _legendre_poly_kernel(m, n, k):
    """Mellin of P_{2k}(t) by expanding in monomials."""
    # P_n(x) = 2^{-n} sum_{j=0}^{floor n/2} (-1)^j C(n,j) C(2n-2j,n) x^{n-2j}
    nP = 2 * k
    total = mp.mpc(0)
    for j in range(k + 1):
        power = nP - 2 * j
        c = (
            mp.binomial(nP, j)
            * mp.binomial(2 * nP - 2 * j, nP)
            * ((-1) ** j)
            / mp.power(2, nP)
        )
        total += c * gen._mp_kernel(m, n, power)
    return total


def q_source_row_legendre(m, N, a0, a4):
    J = len(a0)
    b = [a4[0] * a0[j] - a0[0] * a4[j] for j in range(J)]
    row = []
    for n in range(-N, N + 1):
        s = mp.fsum(b[j] * ((-1) ** j) * _legendre_poly_kernel(m, n, j) for j in range(J) if abs(b[j]) > mp.mpf("1e-30"))
        row.append(s)
    nrm = mp.sqrt(mp.fsum((z.conjugate() * z).real for z in row))
    return [z / nrm for z in row]


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))


def von_mangoldt_support(limit: int):
    out = []
    for k in range(2, limit + 1):
        for p in range(2, k + 1):
            if not is_prime(p):
                continue
            power = p
            while power < k:
                power *= p
            if power == k:
                out.append((k, p))
                break
    return out


def q_kernel(x, L, n, m):
    if n == m:
        return 2 * (L - x) / L * mp.cos(2 * mp.pi * n * x / L)
    return (mp.sin(2 * mp.pi * m * x / L) - mp.sin(2 * mp.pi * n * x / L)) / (
        mp.pi * (n - m)
    )


def w02_entry(L, n, m):
    return (
        32
        * L
        * mp.sinh(L / 4) ** 2
        * (L ** 2 - 16 * mp.pi ** 2 * m * n)
        / ((L ** 2 + 16 * mp.pi ** 2 * m ** 2) * (L ** 2 + 16 * mp.pi ** 2 * n ** 2))
    )


def wr_entry(L, n, m):
    q0 = mp.mpf(2 if n == m else 0)
    eL = mp.exp(L)
    constant = mp.euler + mp.log(4 * mp.pi * ((eL - 1) / (eL + 1)))
    # integrand in t=x/L, x=L t

    def integrand(t):
        x = L * t
        if t == 0:
            # removable: (e^{x/2} q'(0) + q0/2) / 2  at 0, handled by series
            return L * _wr_at_zero(L, n, m)
        qx = q_kernel(x, L, n, m)
        return L * (mp.exp(x / 2) * qx - q0) / (mp.exp(x) - mp.exp(-x))

    integ = mp.quad(integrand, [0, 1])
    return q0 / 2 * constant + integ


def _wr_at_zero(L, n, m):
    # limit x->0 of (e^{x/2} q(x) - q(0)) / (e^x - e^{-x})
    # = (q'(0) + q(0)/2) / 4
    # q'(0): n=m => 2/L * ( -1 * 1 + 0) wait
    if n == m:
        qp0 = -2 / L  # d/dx [2(L-x)/L cos(omega x)] at 0 = -2/L
        q0 = 2
    else:
        qp0 = (2 * m - 2 * n) / L / (n - m)  # d sin(a x)/dx at 0 = a, (2pi m/L - 2pi n/L)/(pi(n-m))
        qp0 = (2 * m / L - 2 * n / L) / (n - m)  # 2/L
        q0 = 0
        qp0 = mp.mpf(2) / L
    return (qp0 + q0 / 2) / 4


def prime_entry(L, n, m, m_project):
    total = mp.mpf(0)
    for k, p in von_mangoldt_support(m_project):
        x = L if k == m_project else mp.log(k)
        qv = q_kernel(x, L, n, m)
        total += mp.log(p) / mp.sqrt(k) * qv.real
    return total


def weil_entry(L, n, mm, m_project):
    return w02_entry(L, n, mm) - wr_entry(L, n, mm) - prime_entry(L, n, mm, m_project)


def build_K(m_project, N):
    L = mp.log(m_project)
    modes = list(range(-N, N + 1))
    s = 2 * N + 1
    K = mp.matrix(s)
    for i, ni in enumerate(modes):
        for j in range(i, s):
            nj = modes[j]
            val = weil_entry(L, ni, nj, m_project)
            K[i, j] = val
            K[j, i] = val
    return K


def measures(K, q):
    dim = K.rows
    qv = mp.matrix(dim, 1)
    for i, z in enumerate(q):
        qv[i] = z
    # real-ify if imaginary noise
    Kn = mp.matrix(dim)
    for i in range(dim):
        for j in range(dim):
            Kn[i, j] = mp.re(K[i, j])
    qn = mp.matrix(dim, 1)
    for i in range(dim):
        qn[i] = mp.re(qv[i])
    nrm = mp.sqrt(mp.fsum(qn[i] ** 2 for i in range(dim)))
    qn = qn / nrm
    a = (qn.T * Kn * qn)[0]
    r = Kn * qn - a * qn
    rnorm = mp.sqrt(mp.fsum(r[i] ** 2 for i in range(dim)))
    # complement basis via QR on [q | e_i]
    M = mp.matrix(dim)
    for i in range(dim):
        M[i, 0] = qn[i]
        for j in range(1, dim):
            M[i, j] = mp.mpf(1 if i == j - 1 else 0)
    Qmat, _R = mp.qr(M)
    U = Qmat[:, 1:]  # dim x (dim-1)
    B = U.T * Kn * U - a * mp.eye(dim - 1)
    rred = U.T * r
    # beta = min eig of B
    ev = mp.eigsy(B, eigvals_only=True)
    beta = min(ev)
    try:
        u = mp.lu_solve(B, rred)
        eta = mp.sqrt(mp.fsum(u[i] ** 2 for i in range(dim - 1)))
    except Exception as exc:
        eta = None
        uerr = str(exc)
    else:
        uerr = None
    evK = mp.eigsy(Kn, eigvals_only=True)
    lam0, lam1 = evK[0], evK[1]
    gap = lam1 - lam0
    excess = a - lam0
    return dict(
        a=a,
        rnorm=rnorm,
        eta=eta,
        eta_error=uerr,
        beta=beta,
        lam0=lam0,
        lam1=lam1,
        gap=gap,
        excess=excess,
        sufficient=gap - 2 * excess,
        dim=dim,
    )


def plant_K21():
    """Reproduce Proshka sign of b and y-energy, not the q_source numbers."""
    K = build_K(2, 1)
    b = K[1, 2]  # modes (-1,0,1): index 0=-1,1=0,2=1; b is K_{0,1} in 0-1 numbering of (0,1) modes
    # modes: 0 -> n=-1, 1 -> n=0, 2 -> n=1. Off-diag between 0 and 1 is K[1,2]
    b01 = K[1, 2]
    q = mp.matrix([mp.mpf("0.5"), 1 / mp.sqrt(2), mp.mpf("0.5")])
    y = mp.matrix([mp.mpf("-0.5"), 1 / mp.sqrt(2), mp.mpf("-0.5")])
    a = (q.T * K * q)[0]
    ye = (y.T * (K - a * mp.eye(3)) * y)[0]
    return dict(b01=b01, a_sym=a, y_energy=ye, identity=ye + 2 * mp.sqrt(2) * b01)


def main():
    mp.mp.dps = DPS
    m = M_FIXED
    c2 = mp.mpf(m)
    print(f"DPS={DPS} m={m} J={J_FERRERS} DIAGNOSTIC_NEVER_A_PROOF")
    plant = plant_K21()
    print("PLANT K(2,1) b01=", plant["b01"])
    print("PLANT a_sym=", plant["a_sym"], "yE=", plant["y_energy"], "id=", plant["identity"])
    chi0, chi4, a0, a4 = ferrers_packet(c2, J_FERRERS)
    print("chi0=", chi0, "chi4=", chi4)
    print("a0[0:3]=", a0[:3])
    print("a4[0:3]=", a4[:3])
    rows = []
    for N in N_LIST:
        q = q_source_row_legendre(m, N, a0, a4)
        K = build_K(m, N)
        meas = measures(K, q)
        meas["N"] = N
        rows.append(meas)
        def ns(x):
            if x is None:
                return "None"
            return mp.nstr(x, 8)
        print(
            f"N={N} dim={meas['dim']} a={ns(meas['a'])} ||r||={ns(meas['rnorm'])} "
            f"eta={ns(meas['eta'])} beta={ns(meas['beta'])} "
            f"gap={ns(meas['gap'])} e={ns(meas['excess'])} Delta-2e={ns(meas['sufficient'])}"
        )
    etas = [float(r["eta"]) if r["eta"] is not None else None for r in rows]
    falling = None
    if None not in etas:
        falling = all(etas[i + 1] < etas[i] for i in range(len(etas) - 1))
    print("ETA_SEQUENCE", etas, "STRICTLY_FALLING", falling)
    out = {
        "diagnostic": True,
        "never_a_proof": True,
        "m": m,
        "N_list": list(N_LIST),
        "J_ferrers": J_FERRERS,
        "dps": DPS,
        "plant": {k: mp.nstr(v, 12) for k, v in plant.items()},
        "chi0": mp.nstr(chi0, 12),
        "chi4": mp.nstr(chi4, 12),
        "rows": [
            {
                **{k: (mp.nstr(v, 12) if isinstance(v, (mp.mpf, mp.mpc)) else v) for k, v in r.items()},
            }
            for r in rows
        ],
        "eta_strictly_falling": falling,
        "verdict": (
            "FALLS_ENTER_FINITE_GROUND_TRANSFORM"
            if falling
            else "DOES_NOT_FALL_KILL_FORCING_ANALOGY"
        ),
        "rh_claim": False,
    }
    (ROOT / "result.json").write_text(json.dumps(out, indent=2) + "\n")
    print("VERDICT", out["verdict"])
    print("wrote", ROOT / "result.json")


if __name__ == "__main__":
    main()
