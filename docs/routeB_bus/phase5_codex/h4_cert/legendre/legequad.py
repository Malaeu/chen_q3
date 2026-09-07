"""Post-hoc Bernstein-ellipse quadrature bound for the Legendre packet, optimized over rho.

The composite Clenshaw-Curtis RULE (nodes, weights, panel width, degree) does not depend on
rho; rho enters only the error estimate (Trefethen ATAP Thm 8.2, re-derived in CLASSFLOOR 2.2)

    |I - I_n| <= 8 M(rho) rho^{-n}/(rho - 1),

valid for every rho for which the integrand is analytic and bounded by M(rho) inside the
Bernstein ellipse of the panel.  Re-deriving the bound from the finished run with a better
rho is legal (CLASSFLOOR 2.2: "the quadrature rule is unchanged").

  * the ellipse over a panel of width w has semi-major R_maj = (w/4)(rho + 1/rho) and
    semi-MINOR R_min = (w/4)(rho - 1/rho); the strip constraint is R_min < 1/2, and every
    factor measuring distance to the singularities at Im xi = +-1/2 uses R_min;
  * gamma_2 is enclosed over the RECTANGLE |Re xi - m| <= R_maj, |Im xi| <= R_min;
  * |1 - cos(a z)| <= 1 + cosh(a R_min);
  * the continued transform factors: hhat_j(z) and conj(hhat_j(zbar)) are BOTH entire with
    |.| <= ||h_j||_1 e^{delta R_min} on the rectangle (CLASSFLOOR 2.2), for either parity;
  * |t_2^{[J0]}| <= (J0 + 2)/(2 pi (1/2 - R_min)^2).

Then M_ij(panel) = (1 + cosh(a R_min)) ||h_i||_1 ||h_j||_1 e^{2 delta R_min}
                   * 2 max(|gamma_2(z)|,|gamma_2(-z)|) * T_b, so M_ij = L1_i L1_j * base and

    E_quad^{ij} = L1_i L1_j * Ebase,   Ebase = 2 (w/2) 8 rho^{-n}/(rho-1) * sum_panels base,
    E_mass^{i}  = L1_i^2         * Ebasem,  Ebasem the same without 2 gm T_b.

Both constants are exported as FULL BALLS and as certified upward-rounded decimals
(NOTES.md item 2 -- no radius-free decimal is relied upon).

Usage: legequad.py XLO XHI WID NCC NPROC [rho1 rho2 ...]
"""
import sys, os, time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx
import h4arb, evalf
import legarb, legser

PREC = 400
_G = {}


def _init(XLO, WID, RHO):
    ctx.prec = PREC
    d, _A = legarb.profiles(PREC)
    a = arb(2).log()
    w = arb(WID)
    rho = arb(RHO)
    Rmaj = w / 4 * (rho + 1 / rho)
    Rmin = w / 4 * (rho - 1 / rho)
    if not (Rmin < arb(1) / 2):
        raise ValueError(f"rho={RHO}: R_min={Rmin.str(6)} not < 1/2 (ellipse leaves the strip)")
    _G.update(d=d, a=a, w=w, XLO=arb(XLO), Rmaj=Rmaj.abs_upper(), Rmin=Rmin.abs_upper(),
              wfac=1 + (a * Rmin.abs_upper()).cosh(),
              hpref=(2 * d * Rmin.abs_upper()).exp(),
              Tb=arb(evalf.J0 + 2) / ((arb(1) / 2 - Rmin.abs_upper()) ** 2) / (2 * arb.pi()))


def _panel(idx):
    ctx.prec = PREC
    w, Rmaj, Rmin = _G['w'], _G['Rmaj'], _G['Rmin']
    m = _G['XLO'] + w * idx + w / 2
    ball = acb(arb(m.mid(), Rmaj), arb(0, Rmin))
    g1 = h4arb.gamma2_abs_ub(ball, Rmin, PREC)
    g2 = h4arb.gamma2_abs_ub(-ball, Rmin, PREC)
    gm = g1 if g1 > g2 else g2
    base = _G['wfac'] * _G['hpref'] * 2 * gm * _G['Tb']
    basem = _G['wfac'] * _G['hpref']
    return (float(base.abs_upper().str(20, radius=False)),
            float(basem.abs_upper().str(20, radius=False)))


def sweep(XLO, XHI, WID, NCC, NP, rhos):
    npan = int(round((XHI - XLO) / WID))
    out = {}
    for RHO in rhos:
        t0 = time.time()
        try:
            _init(XLO, WID, RHO)
        except ValueError as e:
            print(f"  rho={RHO}: {e}")
            continue
        with Pool(NP, initializer=_init, initargs=(XLO, WID, RHO)) as P:
            res = P.map(_panel, range(npan), chunksize=64)
        ctx.prec = PREC
        S = arb(0); Sm = arb(0)
        for b, bm in res:
            S += arb(b) * (1 + arb(2) ** -50)
            Sm += arb(bm) * (1 + arb(2) ** -50)
        rho = arb(RHO)
        kq = 2 * (arb(WID) / 2) * 8 * rho ** (-NCC) / (rho - 1)
        Eb = (kq * S).abs_upper()
        Ebm = (kq * Sm).abs_upper()
        out[RHO] = (Eb, Ebm)
        print(f"  rho={RHO:5.2f}  R_min={_G['Rmin'].str(6)}  R_maj={_G['Rmaj'].str(6)}  "
              f"Ebase={Eb.str(8)}  Ebasem={Ebm.str(8)}  ({time.time()-t0:.0f}s)", flush=True)
    return out


if __name__ == '__main__':
    XLO = float(sys.argv[1]); XHI = float(sys.argv[2])
    WID = float(sys.argv[3]); NCC = int(sys.argv[4]); NP = int(sys.argv[5])
    rhos = [float(x) for x in sys.argv[6:]] or [3.0, 3.4, 3.6, 3.8, 3.9, 4.0]
    print(f"post-hoc E_quad sweep: band [{XLO},{XHI}] WID={WID} NCC={NCC} J0={evalf.J0}")
    out = sweep(XLO, XHI, WID, NCC, NP, rhos)
    best = min(out, key=lambda r: float(out[r][0].str(10, radius=False)))
    Eb, Ebm = out[best]
    print(f"\nBEST rho = {best}")
    print(f"  Ebase  full ball      = {Eb.str(20)}")
    print(f"  Ebase  directed upper = {legser.dec_upper(Eb)}")
    print(f"  Ebasem full ball      = {Ebm.str(20)}")
    print(f"  Ebasem directed upper = {legser.dec_upper(Ebm)}")
