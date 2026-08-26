"""DIAGNOSTIC NUMERICS ONLY — NEVER A PROOF, NEVER A LEAN INPUT.

Edge-slope probe (Goal 058, W5_DEFECT_EDGE_TOP_LATTICE_BUDGET,
verdict c47b75a8 aftermath).

Builds the ACTUAL committed even prolate Ferrers mode (mode-0 branch) from
the committed three-term Legendre recurrence
(D0Mode4PSWFLegendreRecurrenceCrosswalk.lean):

  sub(q)*a_{q-1} + (diag(q) - theta)*a_q + sup(q)*a_{q+1} = 0,
  N = 2q, G = (2*pi*m)^2,
  sub  = -G (N-1) N / ((2N-3)(2N-1)),
  diag =  N(N+1) + G (2N(N+1)-1) / ((2N-1)(2N+3)),
  sup  = -G (N+1)(N+2) / ((2N+3)(2N+5)),

takes the lowest eigenpair (chi_0 ~ c = 2*pi*m), anchors the physical mode
c0*S(y/lam) to the cylinder target D_0(sqrt(4pi)y) = exp(-pi y^2) at the
center, and measures

  (a) the defect edge slope |delta'(y)| for y in (lam - 1/lam, lam),
  (b) the averaged top-lattice functional
      T = int_0^L sqrt(u) * y_top * |delta'(y_top)| dx,  u = e^x/lam,
      y_top = floor(lam/u)*u,
  (c) the exponent fits |delta'(edge)| ~ lam^p and T ~ lam^p.

Readings: A = slope O(lam^{-1/2}) or better (judge's P_WC_TOP_1);
B = slope O(lam) (the G-amplification through r(lam)/(2 lam)).
"""
import numpy as np


def legendre_and_deriv(nmax, s):
    """P_n(s), P'_n(s) for n = 0..nmax at scalar/array s, stable upward."""
    P = np.zeros((nmax + 1,) + np.shape(s))
    D = np.zeros_like(P)
    P[0] = 1.0
    if nmax >= 1:
        P[1] = s
        D[1] = 1.0
    for n in range(1, nmax):
        P[n + 1] = ((2 * n + 1) * s * P[n] - n * P[n - 1]) / (n + 1)
        D[n + 1] = D[n - 1] + (2 * n + 1) * P[n]
    return P, D


def build_mode(m, Q):
    G = (2 * np.pi * m) ** 2
    q = np.arange(Q)
    N = 2.0 * q
    sub = -G * (N - 1) * N / ((2 * N - 3) * (2 * N - 1))
    diag = N * (N + 1) + G * (2 * N * (N + 1) - 1) / ((2 * N - 1) * (2 * N + 3))
    sup = -G * (N + 1) * (N + 2) / ((2 * N + 3) * (2 * N + 5))
    M = np.zeros((Q, Q))
    for i in range(Q):
        M[i, i] = diag[i]
        if i > 0:
            M[i, i - 1] = sub[i]
        if i < Q - 1:
            M[i, i + 1] = sup[i]
    w, V = np.linalg.eig(M)
    w = np.real(w)
    V = np.real(V)
    idx = np.argmin(w)
    theta = w[idx]
    a = V[:, idx]
    # committed normalization: sum a_q^2/(4q+1) = 1, a_0 > 0
    a = a / np.sqrt(np.sum(a ** 2 / (4 * q + 1)))
    if a[0] < 0:
        a = -a
    return theta, a


def probe(m, Q=None):
    lam = np.sqrt(m)
    c_band = 2 * np.pi * m
    if Q is None:
        Q = int(2.2 * c_band / 2) + 60   # q-range beyond the classical turning index
    theta, a = build_mode(m, Q)
    q = np.arange(Q)
    nmax = 2 * (Q - 1)

    sgn = (-1.0) ** q   # committed series: mode4FerrersTerm = (-1)^q a_q P_{2q}
    def S_and_Sp(s):
        P, D = legendre_and_deriv(nmax, s)
        S = np.tensordot(sgn * a, P[2 * q], axes=(0, 0))
        Sp = np.tensordot(sgn * a, D[2 * q], axes=(0, 0))
        return S, Sp

    S0, _ = S_and_Sp(np.array(0.0))
    c0 = 1.0 / S0   # center anchor: c0*S(0) = D_0(0) = 1

    # (a) edge slope: y in (lam - 1/lam, lam)
    tgrid = np.linspace(0.02, 1.0, 25)
    ys = lam - tgrid / lam
    ss = ys / lam
    _, Sp = S_and_Sp(ss)
    dprime = c0 * Sp / lam + 2 * np.pi * ys * np.exp(-np.pi * ys ** 2)
    edge_sup = np.max(np.abs(dprime))
    # (b) averaged top functional
    L = np.log(m)
    xs = np.linspace(1e-4, L - 1e-9, 4000)
    us = np.exp(xs) / lam
    ntop = np.floor(lam / us)
    ytop = ntop * us
    stop = np.clip(ytop / lam, -1.0, 1.0)
    _, Sp_top = S_and_Sp(stop)
    dprime_top = c0 * Sp_top / lam + 2 * np.pi * ytop * np.exp(-np.pi * ytop ** 2)
    T = np.trapz(np.sqrt(us) * ytop * np.abs(dprime_top), xs)
    # eigenvalue sanity: mu = theta/m should approach 2*pi
    return dict(m=m, lam=lam, theta=theta, mu=theta / m,
                edge_sup=edge_sup, T=T, c0=c0, Q=Q)


def main():
    ms = [16, 32, 64, 128, 256]
    rows = [probe(m) for m in ms]
    print(f"{'m':>5} {'lam':>7} {'mu=theta/m':>11} {'sup|d(edge)|':>13} "
          f"{'T_avg':>10} {'c0':>9}")
    for r in rows:
        print(f"{r['m']:>5} {r['lam']:>7.3f} {r['mu']:>11.6f} "
              f"{r['edge_sup']:>13.4e} {r['T']:>10.4e} {r['c0']:>9.4f}")
    lams = np.array([r['lam'] for r in rows])
    for key in ('edge_sup', 'T'):
        vals = np.array([r[key] for r in rows])
        p = np.polyfit(np.log(lams), np.log(vals), 1)[0]
        print(f"power fit: {key} ~ lam^{p:.3f}")


if __name__ == "__main__":
    main()
