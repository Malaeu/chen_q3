"""Rigorous interval certificate for the scalar floor F(h4)  [SCALARFLOOR (38)].

  F(h) = -int_R W_h ell_2 dxi
       = [-int_{|xi|<=X} W_h ell_2^{[J0]}]  +  R_euler  +  R_freq
  |R_euler| <= 4 pi eps_{J0}          (SCALARFLOOR (32)-(33), C = 256)
  |R_freq|  <= 2 Tstar mu_X           (Tstar: uniform |t_2| bound, mu_X: omitted W-mass)

Compact part: composite Clenshaw-Curtis on panels of width WID, degree NCC,
error by the Bernstein-ellipse interpolation bound
  |I - I_n| <= 2 ||f - p_n||_inf <= 8 M rho^{-n}/(rho-1)     (Trefethen, ATAP Thm 8.2)
with M an enclosure-based upper bound for |f| on the ellipse E_rho.

Usage: cert.py X WID NCC RHO NPROC [outfile]
"""
import sys, time, math
from multiprocessing import Pool
from flint import arb, acb, ctx
import h4arb, evalf

PREC = 400
NODE_PREC = 12000      # xi-node balls must be far finer than the e^beta cancellation


# ---------------------------------------------------------------- CC rule
def cc_rule(n, prec):
    ctx.prec = prec
    xs, ws = [], []
    for k in range(n + 1):
        xs.append((arb(k) / n).cos_pi())
        ck = 1 if (k == 0 or k == n) else 2
        ssum = arb(0)
        for j in range(1, n // 2 + 1):
            bj = 1 if (2 * j == n) else 2
            ssum += arb(bj) / (4 * j * j - 1) * (arb(2 * j * k) / n).cos_pi()
        ws.append(arb(ck) * (1 - ssum) / n)
    return xs, ws


# ------------------------------------------------- exact-enough ball transport
def pack(b):
    """arb ball -> (float mid, float rad) with the radius inflated so that the
    reconstructed double ball provably contains the original one."""
    m = float(b.mid().str(25, radius=False))
    r = float(b.rad().str(25, radius=False))
    return m, r * 1.000001 + abs(m) * 2.0 ** -50 + 1e-300


def unpack(mr):
    m, r = mr
    return arb(m, r)


# ---------------------------------------------------------------- globals
_G = {}


def _init(X, WID, NCC, RHO):
    _G['C'] = evalf.Ctx(PREC)
    _G['xs'], _G['ws'] = cc_rule(NCC, NODE_PREC)
    _G['WID'] = WID
    ctx.prec = PREC
    _G['R'] = arb(WID) / 4 * (arb(RHO) + 1 / arb(RHO))
    _G['RHO'] = RHO
    _G['NCC'] = NCC
    C = _G['C']
    R = _G['R']
    # constant part of the ellipse bound on |f|
    L1 = (2 * C.d * C.H).sqrt()                       # ||h||_1 <= sqrt(2 delta H)  (Cauchy-Schwarz)
    _G['pref'] = L1 * L1 * (2 * C.d * R).exp() / C.H  # bound on |hhat|^2/H
    _G['Tb'] = arb(evalf.J0 + 2) / ((arb(1) / 2 - R) ** 2) / (2 * arb.pi())   # bound on |t_2^{[J0]}|


def panel(idx):
    C, xs, ws = _G['C'], _G['xs'], _G['ws']
    WID, R = _G['WID'], _G['R']
    ctx.prec = NODE_PREC
    m = arb(WID) * idx + arb(WID) / 2
    half = arb(WID) / 2
    acc = arb(0)
    ns = 0
    for x, w in zip(xs, ws):
        ctx.prec = NODE_PREC
        xi = m + half * x
        ctx.prec = PREC
        v, k = evalf.integrand(xi, C)
        ns += k
        ctx.prec = PREC
        acc += w * v
    ctx.prec = PREC
    I = half * acc
    # ---- ellipse bound M on this panel
    Rub = R.abs_upper()
    ball = acb(arb(m.mid(), Rub), arb(0, Rub))
    g1 = h4arb.gamma2_abs_ub(ball, Rub, PREC)
    g2 = h4arb.gamma2_abs_ub(-ball, Rub, PREC)
    gm = g1 if g1 > g2 else g2
    wfac = (1 - (acb(C.a) * ball).cos()).abs_upper()
    M = wfac * _G['pref'] * 2 * gm * _G['Tb']
    if I.rad() > arb(1e-12):
        raise ValueError(f"panel {idx} wide: I={I.str(8)}")
    try:
        return pack(I), pack(M), ns
    except ValueError:
        raise ValueError(f"panel {idx}: I={I.str(8)} M={M.str(8)} gm={gm.str(8)} wfac={wfac.str(8)}")


def main():
    X = float(sys.argv[1]); WID = float(sys.argv[2]); NCC = int(sys.argv[3])
    RHO = float(sys.argv[4]); NP = int(sys.argv[5])
    out = sys.argv[6] if len(sys.argv) > 6 else None
    npan = int(round(X / WID))
    t0 = time.time()
    with Pool(NP, initializer=_init, initargs=(X, WID, NCC, RHO)) as P:
        res = []
        for i, r in enumerate(P.imap(panel, range(npan), chunksize=4)):
            res.append(r)
            if i % 50 == 0:
                el = time.time() - t0
                print(f"\r  panels {i+1}/{npan}  {el:7.1f}s  ETA {el/(i+1)*(npan-i-1):7.1f}s", end='', flush=True)
    print()
    _init(X, WID, NCC, RHO)
    ctx.prec = PREC
    half = arb(0)
    Msum = arb(0)
    nser = 0
    for I, M, ns in res:
        half += unpack(I)
        Msum += unpack(M)
        nser += ns
    Icompact = 2 * half                                  # both halves of the real line
    rho = arb(RHO)
    Equad = 2 * (arb(WID) / 2) * 8 * Msum * rho ** (-NCC) / (rho - 1)
    print("PANELS", npan, "NODES", npan * (NCC + 1), "SERIES_CALLS", nser,
          "WALL", f"{time.time()-t0:.1f}s")
    print("I_compact_over_pm =", Icompact.str(20))
    print("E_quadrature      =", Equad.str(10))
    if out:
        with open(out, 'w') as f:
            f.write(f"X={X} WID={WID} NCC={NCC} RHO={RHO} npanels={npan}\n")
            f.write("I_compact = " + Icompact.str(25) + "\n")
            f.write("E_quad    = " + Equad.str(15) + "\n")
            f.write("Msum      = " + Msum.str(10) + "\n")
            f.write("wall_s    = %.1f\n" % (time.time() - t0))


if __name__ == '__main__':
    main()
