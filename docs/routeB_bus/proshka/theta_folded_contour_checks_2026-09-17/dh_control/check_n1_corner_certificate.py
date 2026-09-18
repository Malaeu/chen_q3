"""Finite-certificate enclosure of the n=1 (and n=1,2) head at the compact corner.

Coercive tail + Gauss–Legendre panels with a Cauchy remainder from an explicit
strip majorant of the integrand (2.5).  DIAGNOSTIC until the majorant maximum
on each disk is replaced by a fully rational comparison; the Gauss nodes are
mpmath values at the working dps.

    python check_n1_corner_certificate.py
"""
from __future__ import annotations
import sys
from pathlib import Path
import mpmath as mp
from mpmath import mpf, mpc, pi, exp, cos, factorial

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import check_contour as cc
import check_head_masses as hm

# ---- parameters of the certificate ----
DPS = 40
T_VAL = mp.sqrt(20)
SIGMA = mpf("1/2")
A = mpf(3)          # tail starts here
R = mpf("1/10")     # Cauchy radius; 2*theta + 2R < pi/2
N_GL = 6            # Gauss–Legendre nodes per panel
N_PANELS = 40
NMAX = 2            # enclose n=1 and n=1+2


def gl_nodes_weights(n, dps):
    """Gauss–Legendre nodes/weights on [-1,1] at working dps."""
    old = mp.mp.dps
    mp.mp.dps = dps
    xs, ws = mp.gauss_quadrature(n, qtype="legendre")
    mp.mp.dps = old
    return [xs[i] for i in range(n)], [ws[i] for i in range(n)]


def phi(z, a):
    return (4 * a * a * exp(mpf(9) * z / 2) - 6 * a * exp(mpf(5) * z / 2)) * exp(-a * exp(2 * z))


def f_plus(t, a, p, theta):
    z = t + 1j * theta
    return phi(z, a) * exp(p * z)


def f_minus(t, a, p, theta):
    z = t - 1j * theta
    return phi(z, a) * exp(-p * z)


def M_plus_disk(c, r, a, sigma, T, theta):
    """Explicit upper bound of |f_+| on the disk |zeta - c| <= r, Re zeta >= 0."""
    x_hi = c + r
    x_lo = mp.fabs(c - r)  # if c>r this is c-r; keep nonnegative for the decaying exp
    if c > r:
        x_lo = c - r
    else:
        x_lo = mpf(0)
    c2 = cos(2 * theta + 2 * r)
    if c2 <= 0:
        raise RuntimeError("strip hits a vanishing cosine; shrink R")
    pref = 4 * a * a * exp(mpf(9) * x_hi / 2) + 6 * a * exp(mpf(5) * x_hi / 2)
    return pref * exp(-a * exp(2 * x_lo) * c2) * exp(sigma * x_hi - T * (theta - r))


def M_minus_disk(c, r, a, sigma, T, theta):
    x_hi = c + r
    x_lo = c - r if c > r else mpf(0)
    c2 = cos(2 * theta + 2 * r)
    if c2 <= 0:
        raise RuntimeError("strip hits a vanishing cosine; shrink R")
    pref = 4 * a * a * exp(mpf(9) * x_hi / 2) + 6 * a * exp(mpf(5) * x_hi / 2)
    # Re(-p z) <= -sigma x_lo + T (r - theta)
    return pref * exp(-a * exp(2 * x_lo) * c2) * exp(-sigma * x_lo + T * (r - theta))


def gl_remainder(width, n, Mder):
    """|R| for Gauss–Legendre n nodes on an interval of length `width`.

    R = width^{2n+1} (n!)^4 / ((2n+1) [(2n)!]^3) * f^{(2n)}(xi)
    """
    nf = factorial(n)
    n2f = factorial(2 * n)
    return (width ** (2 * n + 1) * nf ** 4 / ((2 * n + 1) * n2f ** 3)) * Mder


def strip_radius(theta):
    """R so that 2*theta + 2R < pi/2, i.e. R < 1/(T+1)."""
    room = pi / 4 - theta
    if room <= 0:
        raise RuntimeError("theta >= pi/4")
    return min(R, room / 2)


def enclose_ray(sign, n, p, theta, T, sigma, xs, ws, r=None, n_panels=None):
    a = pi * n * n
    r = strip_radius(theta) if r is None else r
    n_panels = N_PANELS if n_panels is None else n_panels
    # keep width/r roughly as in the corner tuning
    n_panels = max(n_panels, int(mp.ceil(4 / r)))
    width = A / n_panels
    I = mpc(0)
    V = mpc(0)  # ∫ (t ± i theta) f  or the chain-rule image
    remI = mpf(0)
    remV = mpf(0)
    for j in range(n_panels):
        t0 = j * width
        t1 = t0 + width
        c = (t0 + t1) / 2
        # map [-1,1] -> [t0,t1]
        sI = mpc(0)
        sV = mpc(0)
        for x, w in zip(xs, ws):
            t = c + x * width / 2
            if sign > 0:
                ft = f_plus(t, a, p, theta)
                sI += w * ft
                sV += w * (t + 1j * theta) * ft
            else:
                ft = f_minus(t, a, p, theta)
                sI += w * ft
                # d/dp I(-p,-theta) = ∫ -(t - i theta) f_minus
                sV += w * (-(t - 1j * theta)) * ft
        I += sI * width / 2
        V += sV * width / 2
        M = M_plus_disk(c, r, a, sigma, T, theta) if sign > 0 else M_minus_disk(c, r, a, sigma, T, theta)
        Mder = factorial(2 * N_GL) * M / r ** (2 * N_GL)
        rem = gl_remainder(width, N_GL, Mder)
        remI += rem
        Mg = (c + width / 2 + r + theta) * M
        Mder_g = factorial(2 * N_GL) * Mg / r ** (2 * N_GL)
        remV += gl_remainder(width, N_GL, Mder_g)
    # elementary tail: u = e^{2t} >= e^{2A}
    umin = exp(2 * A)
    k = a * cos(2 * theta)
    # ∫_U^∞ u^alpha e^{-k u} du < U^alpha e^{-kU}/k / (1 - alpha/(kU))
    def tail_pow(alpha):
        if k * umin <= alpha + 1:
            raise RuntimeError("tail not coercive enough")
        return (umin ** alpha) * exp(-k * umin) / k / (1 - alpha / (k * umin))

    eT = exp(-T * theta)
    if sign > 0:
        integ = 4 * a * a * tail_pow(sigma / 2 + mpf("5/4")) + 6 * a * tail_pow(sigma / 2 + mpf("1/4"))
        tail = eT / 2 * integ
        # moment tail: t = log(u)/2 <= A/2 + u/(2 e^{2A}) crude? use t <= log(u)/2 <= u^{1/8} for U large
        # (A + |theta|) * same integrand is enough: t <= A + (u/umin - 1)/2 * (umin/u wait)
        # t - A = log(u/U)/2 <= (u/U - 1)/2
        extra = (A + theta + mpf("1/2")) * tail + eT / 2 * (
            4 * a * a * tail_pow(sigma / 2 + mpf("5/4") + 1) / (2 * umin)
            + 6 * a * tail_pow(sigma / 2 + mpf("1/4") + 1) / (2 * umin)
        )
    else:
        integ = 4 * a * a * tail_pow(-sigma / 2 + mpf("5/4")) + 6 * a * tail_pow(-sigma / 2 + mpf("1/4"))
        tail = eT / 2 * integ
        extra = (A + theta + mpf("1/2")) * tail + eT / 2 * (
            4 * a * a * tail_pow(-sigma / 2 + mpf("5/4") + 1) / (2 * umin)
            + 6 * a * tail_pow(-sigma / 2 + mpf("1/4") + 1) / (2 * umin)
        )
    remI += tail
    remV += extra
    return I, V, remI, remV, tail


def masses_balls(u, v, ru, rv):
    """First-order enclosure of h and M+ from disks around u,v (one pair or two)."""
    J = sum(u)
    D = sum(v)
    dJ = sum(ru)
    dD = sum(rv)
    h0 = 4 * (D * J.conjugate()).real
    dh = 4 * (abs(D) * dJ + abs(J) * dD + dJ * dD)
    s0 = sum(ui.conjugate() * vi for ui, vi in zip(u, v))
    ds = sum(abs(ui) * rvi + abs(vi) * rui + rui * rvi for ui, vi, rui, rvi in zip(u, v, ru, rv))
    U2 = sum(abs(ui) ** 2 for ui in u)
    V2 = sum(abs(vi) ** 2 for vi in v)
    # |ΔU2| <= 2 |u| r + r^2 per component
    dU2 = sum(2 * abs(ui) * rui + rui ** 2 for ui, rui in zip(u, ru))
    dV2 = sum(2 * abs(vi) * rvi + rvi ** 2 for vi, rvi in zip(v, rv))
    disc0 = U2 * V2 - s0.imag ** 2
    # disc perturbation (very crude)
    ddisc = (abs(U2) + dU2) * dV2 + (abs(V2) + dV2) * dU2 + 2 * abs(s0.imag) * ds + ds ** 2
    absD2 = abs(D) ** 2
    absJ2 = abs(J) ** 2
    dabsD2 = 2 * abs(D) * dD + dD ** 2
    dabsJ2 = 2 * abs(J) * dJ + dJ ** 2
    ImDCJ = (D * J.conjugate()).imag
    dImDCJ = abs(D) * dJ + abs(J) * dD + dD * dJ
    Q0 = U2 * absD2 + V2 * absJ2 - 2 * ImDCJ * s0.imag
    dQ = (
        (U2 + dU2) * dabsD2 + (absD2 + dabsD2) * dU2
        + (V2 + dV2) * dabsJ2 + (absJ2 + dabsJ2) * dV2
        + 2 * (abs(ImDCJ) + dImDCJ) * ds
        + 2 * (abs(s0.imag) + ds) * dImDCJ
    )
    root0 = mp.sqrt(disc0)
    # sqrt(disc0 ± ddisc) enclosure
    if disc0 <= ddisc:
        return dict(ok=False, reason="disc ball hits 0", h0=h0, dh=dh, disc0=disc0, ddisc=ddisc)
    root_lo = mp.sqrt(disc0 - ddisc)
    root_hi = mp.sqrt(disc0 + ddisc)
    Mp0 = h0 / 2 + Q0 / root0
    # M+ = h/2 + Q/sqrt(disc)
    Mp_hi = (h0 + dh) / 2 + (Q0 + dQ) / root_lo
    Mp_lo = (h0 - dh) / 2 + (Q0 - dQ) / root_hi
    h_lo = h0 - dh
    G_lo = h_lo / (SIGMA * Mp_hi)
    G_hi = (h0 + dh) / (SIGMA * Mp_lo) if Mp_lo > 0 else mp.inf
    return dict(
        ok=True, h0=h0, dh=dh, Mp0=Mp0, Mp_lo=Mp_lo, Mp_hi=Mp_hi,
        G0=h0 / (SIGMA * Mp0), G_lo=G_lo, G_hi=G_hi,
        disc0=disc0, ddisc=ddisc, Q0=Q0, dQ=dQ,
        rem_rel_I=None,
    )


def main():
    mp.mp.dps = DPS
    T = T_VAL
    sigma = SIGMA
    theta = pi / 4 - 1 / (T + 1)
    p = sigma + 1j * T
    r0 = strip_radius(theta)
    print(f"T={T} sigma={sigma} theta={theta} R={r0}")
    print(f"2theta+2R={2 * theta + 2 * r0} pi/2={pi / 2}")
    assert 2 * theta + 2 * r0 < pi / 2
    xs, ws = gl_nodes_weights(N_GL, DPS + 20)
    rays = []
    for n in range(1, NMAX + 1):
        for sign in (+1, -1):
            I, V, rI, rV, tail = enclose_ray(sign, n, p, theta, T, sigma, xs, ws)
            rays.append((n, sign, I, V, rI, rV, tail))
            print(f"n={n} sign={sign:+d}  |I|={abs(I)} remI={rI} tail={tail}  |V|={abs(V)} remV={rV}")

    cc.ADAPTIVE_R = 0.0
    # compare n=1 against diffs
    u_ex, v_ex = hm.rays_mp("zeta", p, theta, 1)
    print("diffs I+", u_ex[0], "encl", rays[0][2], "err", abs(u_ex[0] - rays[0][2]))
    print("diffs v+", v_ex[0], "encl", rays[0][3], "err", abs(v_ex[0] - rays[0][3]))

    for label, take in (("n=1", 2), ("n=1,2", 4)):
        u = [rays[i][2] for i in range(take)]
        v = [rays[i][3] for i in range(take)]
        ru = [rays[i][4] for i in range(take)]
        rv = [rays[i][5] for i in range(take)]
        box = masses_balls(u, v, ru, rv)
        print(f"\n=== {label} ===")
        if not box["ok"]:
            print("FAILED", box)
            continue
        print(f"G0={box['G0']}")
        print(f"G in [{box['G_lo']}, {box['G_hi']}]")
        print(f"h0={box['h0']} dh={box['dh']}")
        print(f"M+ in [{box['Mp_lo']}, {box['Mp_hi']}]")
        print(f"clears 1/4? {box['G_lo'] > mpf('1/4')}")
        mm = hm.masses_from(u, v)
        print(f"center masses_from G={mm['h_direct'] / (sigma * mm['M_plus'])}")


if __name__ == "__main__":
    main()
