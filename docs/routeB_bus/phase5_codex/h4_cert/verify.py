"""Independent checks (different channels), all in arb unless stated.

 V1  int_{|xi|<=X} W_h dxi  vs  2pi - mu_X          (checks hhat, H, quadrature)
 V2  J_series vs J_asym on the overlap band          (two unrelated representations)
 V3  ell_2 at sample xi: arb chain vs the mpmath incomplete-gamma evaluator of
     mellin_d2/core.py + dens.py  (a different code path, float output)
 V4  moments int h e^{+-x/2} dx = 0 (algebraic identity + numeric check)
"""
import sys, math
from multiprocessing import Pool
from flint import arb, acb, ctx
import h4arb, evalf, budget, cert

PREC = 400


def V1(X=2000.0, WID=0.5, NCC=32):
    ctx.prec = cert.NODE_PREC
    xs, ws = cert.cc_rule(NCC, cert.NODE_PREC)
    d, A, H = h4arb.profile(PREC)
    a = arb(2).log()
    npan = int(round(X / WID))
    tot = arb(0)
    for idx in range(npan):
        ctx.prec = cert.NODE_PREC
        m = arb(WID) * idx + arb(WID) / 2
        half = arb(WID) / 2
        acc = arb(0)
        for x, w in zip(xs, ws):
            ctx.prec = cert.NODE_PREC
            xi = m + half * x
            ctx.prec = PREC
            hh = h4arb.hhat(acb(xi), d, A, PREC).real
            acc += w * (1 - (a * xi).cos()) * hh * hh / H
        ctx.prec = PREC
        tot += half * acc
    ctx.prec = PREC
    return 2 * tot


def V2():
    rows = []
    for xi in (0.0, 50.0, 250.0, 900.0, 1999.0):
        for j in (9, 10, 11, 12):
            ps = int(1.4427 * (2 * math.pi * 2 ** j)) + 500
            B = evalf.Ctx.beta_at(j + 1, ps)
            ctx.prec = ps
            s = acb(arb(1) / 2) - acb(0, 1) * acb(xi)
            Js = h4arb.J_series(B, s, ps)
            ctx.prec = PREC
            B2 = evalf.Ctx.beta_at(j + 1, PREC)
            s2 = acb(arb(1) / 2) - acb(0, 1) * acb(xi)
            G, K = h4arb.gk_pieces(s2, PREC)
            P, Q = h4arb.PQ(s2, 160, PREC)
            best = None
            for k in evalf.KLIST:
                v, E = h4arb.J_asym(B2, s2, G, K, P, Q, k, PREC)
                Ef = float(E.str(10, radius=False))
                if best is None or Ef < best[1]:
                    best = (v, Ef)
            rows.append((xi, j, Js.overlaps(best[0]), Js.abs_upper().str(6), best[1]))
    return rows


def V3():
    sys.path.insert(0, '/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/mellin_d2')
    import dens
    C = evalf.Ctx(PREC)
    out = []
    for xi in (1.0, 17.5, 60.0, 123.25, 400.0, 600.0):
        t2, g2, _ = evalf.t2_and_gamma(arb(xi), C, PREC)
        ctx.prec = PREC
        ell = 2 * (g2 * t2).real
        t2m = dens.t_S(xi, (2,), Ju=55)
        g2m = complex(dens.gamma_S(xi, (2,))[0])
        ellm = 2 * (g2m * t2m).real
        out.append((xi, ell.str(12), ellm, float((ell - arb(ellm)).abs_upper().str(6, radius=False))))
    return out


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if what in ('all', 'V2'):
        print("== V2: J_series vs J_asym (overlap band) ==")
        for xi, j, ok, mag, E in V2():
            print(f"   xi={xi:7.1f} beta=2pi*2^{j:<3d} overlap={ok}  |J|<={mag}  E_asym={E:.2e}")
    if what in ('all', 'V3'):
        print("== V3: ell_2 arb chain vs mpmath incomplete-gamma evaluator ==")
        for xi, e_arb, e_mp, diff in V3():
            print(f"   xi={xi:8.2f}  arb={e_arb}   mpmath={e_mp:+.12f}   |diff|<={diff:.2e}")
    if what in ('all', 'V4'):
        ctx.prec = PREC
        d, A, H = h4arb.profile(PREC)
        for sg in (1, -1):
            # int_{-d}^{d} sum A_j (x/d)^{2j} e^{sg x/2} dx by the entire series of e^{sg x/2}
            tot = arb(0)
            for j in range(5):
                s = arb(0); t = arb(1); n = 0
                while True:
                    if n % 2 == 0:
                        s += t / (2 * j + n + 1)
                    n += 1
                    t = t * (arb(sg) * d / 2) / n
                    if t.abs_upper() < arb(2) ** (-PREC + 20) and n > 20:
                        break
                tot += A[j] * 2 * d * s
            print(f"== V4: moment sign {sg:+d}:  int h e^(x/2) dx = {tot.str(10)}")
    if what in ('all', 'V1'):
        print("== V1: mass check ==")
        X = 2000.0
        m = V1(X)
        ctx.prec = PREC
        mu = budget.mu_X(X)
        print("   int_{|xi|<=X} W_h  =", m.str(20))
        print("   2 pi               =", (2 * arb.pi()).str(20))
        print("   2pi - computed     =", (2 * arb.pi() - m).str(10), "   must lie in [0, mu_X =",
              mu.str(8), "]")
