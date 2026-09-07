"""Post-hoc Bernstein-ellipse quadrature bound, optimized over rho.

The composite Clenshaw-Curtis RULE (nodes, weights, panel width, degree) does not depend on
rho; rho enters only the error estimate (Trefethen, ATAP Thm 8.2)

    |I - I_n| <= 8 M(rho) rho^{-n} / (rho - 1),

valid for every rho for which the integrand is analytic and bounded by M(rho) inside the
Bernstein ellipse E_rho of the panel.  So the bound may be re-derived from the already
computed run with a better rho, and with a sharper enclosure of M.

Sharpenings over the value emitted by packcert.py (which reused the h4 script's conservative
choice rho = 3 and used the semi-MAJOR axis as the |Im xi| bound):

  * the ellipse over a panel of width w has semi-major R_maj = (w/4)(rho + 1/rho) and
    semi-MINOR R_min = (w/4)(rho - 1/rho); the strip constraint is R_min < 1/2, and every
    factor that measures the distance to the singularities at Im xi = +-1/2 (the pole of
    Gamma(1/4 + i xi/2), the zero of b, and the J-bound) must use R_min, not R_maj;
  * gamma_2 is enclosed over the RECTANGLE |Re xi - m| <= R_maj, |Im xi| <= R_min;
  * |1 - cos(a xi)| <= 1 + cosh(a R_min);
  * |hhat_i(xi)| <= ||h_i||_1 e^{delta R_min};
  * |t_2^{[J0]}| <= (J0 + 2) / (2 pi (1/2 - R_min)^2)   (elementary |J| <= (1/2-R)^{-2}).

Then  M_ij(panel) = (1 + cosh(a R_min)) * ||h_i||_1 ||h_j||_1 e^{2 delta R_min}
                    * 2 max(|gamma_2(xi)|, |gamma_2(-xi)|) * T_b,
so M_ij = ||h_i||_1 ||h_j||_1 * base(panel), and

    E_quad^{ij} = ||h_i||_1 ||h_j||_1 * Ebase,   Ebase = 2 (w/2) 8 rho^{-n}/(rho-1) * sum base,
    E_mass^{i}  = ||h_i||_1^2         * Ebasem,  Ebasem the same without 2 gm T_b.

Usage: packequad.py X WID NCC NPROC [rho1 rho2 ...]
"""
import sys, os, time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx
import h4arb, evalf
import packarb

PREC = 400
_G = {}


def _init(WID, RHO):
    ctx.prec = PREC
    d, A = packarb.profiles(PREC)
    a = arb(2).log()
    w = arb(WID)
    rho = arb(RHO)
    Rmaj = w / 4 * (rho + 1 / rho)
    Rmin = w / 4 * (rho - 1 / rho)
    if not (Rmin < arb(1) / 2):
        raise ValueError(f"rho={RHO}: R_min={Rmin.str(6)} not < 1/2 (ellipse leaves the strip)")
    _G.update(d=d, a=a, w=w, Rmaj=Rmaj.abs_upper(), Rmin=Rmin.abs_upper(),
              wfac=1 + (a * Rmin.abs_upper()).cosh(),
              hpref=(2 * d * Rmin.abs_upper()).exp(),
              Tb=arb(evalf.J0 + 2) / ((arb(1) / 2 - Rmin.abs_upper()) ** 2) / (2 * arb.pi()))


def _panel(idx):
    ctx.prec = PREC
    w, Rmaj, Rmin = _G['w'], _G['Rmaj'], _G['Rmin']
    m = w * idx + w / 2
    ball = acb(arb(m.mid(), Rmaj), arb(0, Rmin))
    g1 = h4arb.gamma2_abs_ub(ball, Rmin, PREC)
    g2 = h4arb.gamma2_abs_ub(-ball, Rmin, PREC)
    gm = g1 if g1 > g2 else g2
    base = _G['wfac'] * _G['hpref'] * 2 * gm * _G['Tb']
    basem = _G['wfac'] * _G['hpref']
    # RECEIPT REPAIR (CLASSFLOOR v2 §1.6): return the outward upper endpoints as 40-digit decimal strings
    # (rounding error <= 1e-39 relative, covered by the (1 + 2^-50) pad applied by the caller), never floats.
    return (base.abs_upper().str(40, radius=False),
            basem.abs_upper().str(40, radius=False))


def sweep(X, WID, NCC, NP, rhos):
    npan = int(round(X / WID))
    out = {}
    for RHO in rhos:
        t0 = time.time()
        try:
            _init(WID, RHO)
        except ValueError as e:
            print(f"  rho={RHO}: {e}")
            continue
        with Pool(NP, initializer=_init, initargs=(WID, RHO)) as P:
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
              f"sum_base={S.str(6)}  Ebase={Eb.str(6)}  Ebasem={Ebm.str(6)}  "
              f"({time.time()-t0:.0f}s)")
    return out


if __name__ == '__main__':
    X = float(sys.argv[1]); WID = float(sys.argv[2]); NCC = int(sys.argv[3]); NP = int(sys.argv[4])
    rhos = [float(x) for x in sys.argv[5:]] or [3.0, 3.2, 3.4, 3.5, 3.6, 3.7, 3.8, 3.9]
    print(f"post-hoc E_quad sweep: X={X} WID={WID} NCC={NCC} J0={evalf.J0}")
    out = sweep(X, WID, NCC, NP, rhos)
    best = min(out, key=lambda r: float(out[r][0].str(10, radius=False)))   # selection only; values stay balls
    print(f"\nBEST rho = {best}   Ebase = {out[best][0].str(12)}   Ebasem = {out[best][1].str(12)}")
    # RECEIPT: full balls and 60-digit outward upper endpoints (the assembly must import THESE, not printed midpoints)
    import os
    os.makedirs('out', exist_ok=True)
    with open('out/equad_receipt.txt', 'w') as f:
        f.write(f"rho {best}\n")
        f.write(f"Ebase_ball {out[best][0].str(60)}\n")
        f.write(f"Ebasem_ball {out[best][1].str(60)}\n")
        f.write(f"Ebase_upper60 {out[best][0].abs_upper().str(60, radius=False)}\n")
        f.write(f"Ebasem_upper60 {out[best][1].abs_upper().str(60, radius=False)}\n")
    print("receipt written: out/equad_receipt.txt")
