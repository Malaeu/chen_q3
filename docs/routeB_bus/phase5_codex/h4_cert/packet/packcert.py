"""Rigorous compact part of the packet floor matrix F_ij (v1 (8), v2 Cor. 1 (6)).

  F_ij = -int_R w_a hhat_i hhat_j ell_2 dxi,   w_a = 1 - cos(a xi)
       = [-int_{|xi|<=X} w_a hhat_i hhat_j ell_2^{[J0]}] + R_euler^{ij} + R_freq^{ij}

This script computes the bracket (composite Clenshaw-Curtis, panels of width WID, degree NCC,
doubled by evenness), the Bernstein-ellipse quadrature BASE (Trefethen ATAP Thm 8.2), and, free
of charge on the same nodes, the mass integrals int_{|xi|<=X} w_a |hhat_i|^2 (verification V1).

COST NOTE: ell_2^{[J0]}(xi) is evaluated ONCE per node and reused for all 15 pairs; the hhat_i
share one cos-moment cache.  ell_2 is ~99% of the node cost.

Usage: packcert.py X WID NCC RHO NPROC [outfile]
"""
import sys, os, time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx
import h4arb, evalf, cert
import packarb

PREC = cert.PREC              # 400
NODE_PREC = cert.NODE_PREC    # 12000
NAMES = packarb.NAMES
ND = len(NAMES)
PAIRS = [(i, j) for i in range(ND) for j in range(i, ND)]

_G = {}


def _init(WID, NCC, RHO):
    _G['C'] = evalf.Ctx(PREC)                       # betas, a, r (h4 profile unused here)
    _G['xs'], _G['ws'] = cert.cc_rule(NCC, NODE_PREC)
    ctx.prec = PREC
    d, A = packarb.profiles(PREC)
    _G['d'], _G['A'] = d, A
    _G['WID'] = arb(WID)
    _G['R'] = arb(WID) / 4 * (arb(RHO) + 1 / arb(RHO))
    R = _G['R']
    _G['ell_pref'] = (2 * d * R).exp()                                    # e^{2 delta R}
    _G['Tb'] = arb(evalf.J0 + 2) / ((arb(1) / 2 - R) ** 2) / (2 * arb.pi())


def panel(idx):
    C, xs, ws = _G['C'], _G['xs'], _G['ws']
    WID, R, d, A = _G['WID'], _G['R'], _G['d'], _G['A']
    accF = [arb(0)] * len(PAIRS)
    accM = [arb(0)] * ND
    ns = 0
    ctx.prec = NODE_PREC
    m = WID * idx + WID / 2
    half = WID / 2
    for x, w in zip(xs, ws):
        ctx.prec = NODE_PREC
        xi = m + half * x
        ctx.prec = PREC
        t2, g2, k = evalf.t2_and_gamma(xi, C, PREC)
        ns += k
        ctx.prec = PREC
        ell = 2 * (g2 * t2).real
        hv = [v.real for v in packarb.hhat_vec(acb(xi), d, A, PREC, NAMES)]
        wa = 1 - (C.a * xi).cos()
        wl = w * wa
        wle = -wl * ell
        for p, (i, j) in enumerate(PAIRS):
            accF[p] += wle * hv[i] * hv[j]
        for i in range(ND):
            accM[i] += wl * hv[i] * hv[i]
    ctx.prec = PREC
    IF = [half * v for v in accF]
    IM = [half * v for v in accM]
    # ---- Bernstein-ellipse base bound (common to all entries; M_ij = L1_i L1_j * base)
    Rub = R.abs_upper()
    ball = acb(arb(m.mid(), Rub), arb(0, Rub))
    g1 = h4arb.gamma2_abs_ub(ball, Rub, PREC)
    g2b = h4arb.gamma2_abs_ub(-ball, Rub, PREC)
    gm = g1 if g1 > g2b else g2b
    wfac = (1 - (acb(C.a) * ball).cos()).abs_upper()
    base = wfac * _G['ell_pref'] * 2 * gm * _G['Tb']      # for the ell_2-weighted integrand
    basem = wfac * _G['ell_pref']                          # for the mass integrand (no ell_2)
    rmax = max([v.rad() for v in IF] + [v.rad() for v in IM])
    if rmax > arb(1e-8):
        raise ValueError(f"panel {idx} wide: rad={rmax.str(8)}")
    return ([cert.pack(v) for v in IF], [cert.pack(v) for v in IM],
            cert.pack(base), cert.pack(basem), ns, float(rmax.str(8, radius=False)))


def main():
    X = float(sys.argv[1]); WID = float(sys.argv[2]); NCC = int(sys.argv[3])
    RHO = float(sys.argv[4]); NP = int(sys.argv[5])
    out = sys.argv[6] if len(sys.argv) > 6 else None
    npan = int(round(X / WID))
    t0 = time.time()
    res = []
    with Pool(NP, initializer=_init, initargs=(WID, NCC, RHO)) as P:
        for i, r in enumerate(P.imap(panel, range(npan), chunksize=4)):
            res.append(r)
            if i % 50 == 0:
                el = time.time() - t0
                print(f"\r  panels {i+1}/{npan}  {el:8.1f}s  ETA {el/(i+1)*(npan-i-1):8.1f}s",
                      end='', flush=True)
    print()
    _init(WID, NCC, RHO)
    ctx.prec = PREC
    Fh = [arb(0)] * len(PAIRS)
    Mh = [arb(0)] * ND
    base = arb(0); basem = arb(0); nser = 0; rmax = 0.0
    BAND = 1000.0                       # band [0,BAND] emitted separately for the cross-check
    nband = int(round(BAND / WID))
    Fb = [arb(0)] * len(PAIRS)
    for pi, (IF, IM, b, bm, ns, rm) in enumerate(res):
        if pi < nband:
            for p_ in range(len(PAIRS)):
                Fb[p_] += cert.unpack(IF[p_])
        for p in range(len(PAIRS)):
            Fh[p] += cert.unpack(IF[p])
        for i in range(ND):
            Mh[i] += cert.unpack(IM[i])
        base += cert.unpack(b); basem += cert.unpack(bm)
        nser += ns; rmax = max(rmax, rm)
    F = [2 * v for v in Fh]            # both halves of the real line (integrand even)
    M = [2 * v for v in Mh]
    rho = arb(RHO)
    kq = 2 * (arb(WID) / 2) * 8 * rho ** (-NCC) / (rho - 1)
    Ebase = kq * base                  # E_quad^{ij} = L1_i L1_j * Ebase
    Ebasem = kq * basem                # E_mass^{i}  = L1_i^2   * Ebasem
    wall = time.time() - t0
    print(f"PANELS {npan} NODES {npan*(NCC+1)} SERIES_CALLS {nser} "
          f"MAXPANELRAD {rmax:.2e} WALL {wall:.1f}s")
    lines = [f"X={X} WID={WID} NCC={NCC} RHO={RHO} J0={evalf.J0} npanels={npan} "
             f"nodes={npan*(NCC+1)} wall_s={wall:.1f}",
             "NAMES = " + " ".join(NAMES)]
    for p, (i, j) in enumerate(PAIRS):
        lines.append(f"I_compact[{NAMES[i]},{NAMES[j]}] = " + F[p].str(25))
    for i in range(ND):
        lines.append(f"MASS[{NAMES[i]}] = " + M[i].str(25))
    for p, (i, j) in enumerate(PAIRS):
        lines.append(f"I_band{int(BAND)}[{NAMES[i]},{NAMES[j]}] = " + (2 * Fb[p]).str(25))
    lines.append("Ebase  = " + Ebase.str(15))
    lines.append("Ebasem = " + Ebasem.str(15))
    txt = "\n".join(lines)
    print(txt)
    if out:
        open(out, 'w').write(txt + "\n")


if __name__ == '__main__':
    main()
