"""Rigorous compact part of the Legendre packet floor matrices F_even, F_odd.

  F_ij = -int_R w_a conj(hhat_i) hhat_j ell_2 dxi,   w_a = 1 - cos(a xi)
       = [-int_{|xi|<=X} w_a g_i g_j ell_2^{[J0]}] + R_euler^{ij} + R_freq^{ij}

with g_i the real profile of legarb.hprofiles (g = hhat for even tests, g = i*hhat for
odd tests; conj(hhat_i)hhat_j = g_i g_j inside a parity block).  The integrand is even in
xi for every same-parity pair, so the band [0,X] is computed and doubled.  Cross-parity
entries are odd and vanish exactly; they are NOT computed (checked separately).

Also computed free of charge on the same nodes: the masses int_{|xi|<=X} w_a |hhat_i|^2,
which drive the sharp mass-deficit frequency tail (verdict (6)).

COST: ell_2^{[J0]}(xi) is evaluated ONCE per node and reused for all 20 pairs; the eight
profiles share one moment cache E_0..E_15.

Every emitted number is a FULL arb ball (NOTES.md item 2): no radius-free decimal is
exported from this script.

Usage: legcert.py XLO XHI WID NCC RHO NPROC [outfile]
"""
import sys, os, time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx
import h4arb, evalf, cert
import legarb

PREC = cert.PREC              # 400
NODE_PREC = cert.NODE_PREC    # 12000
NAMES = legarb.NAMES
EVEN, ODD = legarb.EVEN, legarb.ODD
EPAIRS = [(EVEN[i], EVEN[j]) for i in range(4) for j in range(i, 4)]
OPAIRS = [(ODD[i], ODD[j]) for i in range(4) for j in range(i, 4)]
PAIRS = EPAIRS + OPAIRS

_G = {}


def _init(XLO, WID, NCC, RHO):
    _G['C'] = evalf.Ctx(PREC)                       # betas, a, r
    _G['xs'], _G['ws'] = cert.cc_rule(NCC, NODE_PREC)
    ctx.prec = PREC
    d, A = legarb.profiles(PREC)
    _G['d'], _G['A'] = d, A
    _G['WID'] = arb(WID)
    _G['XLO'] = arb(XLO)
    R = arb(WID) / 4 * (arb(RHO) + 1 / arb(RHO))
    _G['R'] = R
    _G['ell_pref'] = (2 * d * R).exp()                                    # e^{2 delta R}
    _G['Tb'] = arb(evalf.J0 + 2) / ((arb(1) / 2 - R) ** 2) / (2 * arb.pi())


def panel(idx):
    C, xs, ws = _G['C'], _G['xs'], _G['ws']
    WID, R, d, A = _G['WID'], _G['R'], _G['d'], _G['A']
    accF = [arb(0)] * len(PAIRS)
    accM = [arb(0)] * 8
    ns = 0
    ctx.prec = NODE_PREC
    m = _G['XLO'] + WID * idx + WID / 2
    half = WID / 2
    for x, w in zip(xs, ws):
        ctx.prec = NODE_PREC
        xi = m + half * x
        ctx.prec = PREC
        t2, g2, k = evalf.t2_and_gamma(xi, C, PREC)
        ns += k
        ctx.prec = PREC
        ell = 2 * (g2 * t2).real
        gv = legarb.hprofiles(acb(xi), d, A, PREC)
        wa = 1 - (C.a * xi).cos()
        wl = w * wa
        wle = -wl * ell
        for p, (i, j) in enumerate(PAIRS):
            accF[p] += wle * gv[i] * gv[j]
        for i in range(8):
            accM[i] += wl * gv[i] * gv[i]
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
    base = wfac * _G['ell_pref'] * 2 * gm * _G['Tb']      # ell_2-weighted integrand
    basem = wfac * _G['ell_pref']                          # mass integrand (no ell_2)
    rmax = max([v.rad() for v in IF] + [v.rad() for v in IM])
    if rmax > arb(1e-8):
        raise ValueError(f"panel {idx} wide: rad={rmax.str(8)}")
    return ([cert.pack(v) for v in IF], [cert.pack(v) for v in IM],
            cert.pack(base), cert.pack(basem), ns, float(rmax.str(8, radius=False)))


def main():
    XLO = float(sys.argv[1]); XHI = float(sys.argv[2]); WID = float(sys.argv[3])
    NCC = int(sys.argv[4]); RHO = float(sys.argv[5]); NP = int(sys.argv[6])
    out = sys.argv[7] if len(sys.argv) > 7 else None
    npan = int(round((XHI - XLO) / WID))
    t0 = time.time()
    res = []
    with Pool(NP, initializer=_init, initargs=(XLO, WID, NCC, RHO)) as P:
        for i, r in enumerate(P.imap(panel, range(npan), chunksize=4)):
            res.append(r)
            if i % 25 == 0:
                el = time.time() - t0
                print(f"  panels {i+1}/{npan}  {el:8.1f}s  ETA {el/(i+1)*(npan-i-1):8.1f}s",
                      flush=True)
    _init(XLO, WID, NCC, RHO)
    ctx.prec = PREC
    Fh = [arb(0)] * len(PAIRS)
    Mh = [arb(0)] * 8
    base = arb(0); basem = arb(0); nser = 0; rmax = 0.0
    BAND = 1000.0                       # sub-band emitted separately for the cross-check
    nband = int(round(BAND / WID)) if XLO == 0.0 else 0
    Fb = [arb(0)] * len(PAIRS)
    for pi, (IF, IM, b, bm, ns, rm) in enumerate(res):
        if pi < nband:
            for p_ in range(len(PAIRS)):
                Fb[p_] += cert.unpack(IF[p_])
        for p in range(len(PAIRS)):
            Fh[p] += cert.unpack(IF[p])
        for i in range(8):
            Mh[i] += cert.unpack(IM[i])
        base += cert.unpack(b); basem += cert.unpack(bm)
        nser += ns; rmax = max(rmax, rm)
    F = [2 * v for v in Fh]            # both halves of the real line (integrand even)
    M = [2 * v for v in Mh]
    rho = arb(RHO)
    kq = 2 * (arb(WID) / 2) * 8 * rho ** (-NCC) / (rho - 1)
    Ebase = kq * base                  # in-run (rho as given); legequad.py optimizes it
    Ebasem = kq * basem
    wall = time.time() - t0
    print(f"PANELS {npan} NODES {npan*(NCC+1)} SERIES_CALLS {nser} "
          f"MAXPANELRAD {rmax:.2e} WALL {wall:.1f}s", flush=True)
    lines = [f"XLO={XLO} XHI={XHI} WID={WID} NCC={NCC} RHO={RHO} J0={evalf.J0} "
             f"npanels={npan} nodes={npan*(NCC+1)} wall_s={wall:.1f}",
             "NAMES = " + " ".join(NAMES)]
    for p, (i, j) in enumerate(PAIRS):
        lines.append(f"I_compact[{NAMES[i]},{NAMES[j]}] = " + F[p].str(25))
    for i in range(8):
        lines.append(f"MASS[{NAMES[i]}] = " + M[i].str(25))
    if nband:
        for p, (i, j) in enumerate(PAIRS):
            lines.append(f"I_band{int(BAND)}[{NAMES[i]},{NAMES[j]}] = " + (2 * Fb[p]).str(25))
    lines.append("Ebase_inrun  = " + Ebase.str(20))
    lines.append("Ebasem_inrun = " + Ebasem.str(20))
    txt = "\n".join(lines)
    print(txt)
    if out:
        open(out, 'w').write(txt + "\n")


if __name__ == '__main__':
    main()
