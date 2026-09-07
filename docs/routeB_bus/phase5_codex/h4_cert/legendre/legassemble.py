"""Assemble F_even / F_odd, certify positivity, certify the pencil floor, and -- when a
block is not PSD-certifiable -- emit the SIGNED upper enclosure of the declared direction.

LEDGER per entry (i,j) inside one parity block:

  F_ij  in  I_compact_ij +/- [E_quad + E_euler + E_freq]

  E_quad_ij  = ||h_i||_1 ||h_j||_1 * Ebase        Bernstein ellipse, ATAP Thm 8.2 / CLASSFLOOR
                                                  2.2; rho optimized post hoc (legequad.py),
                                                  the RULE unchanged.
  E_euler_ij = 4 pi eps_{J0} sqrt(H_ii H_jj)      |ell_2 - ell_2^{[J0]}| <= 2 eps_{J0} with the
                                                  constant C = 256 KEPT (the newly proved 120
                                                  of CLASSFLOOR Thm 1 is not used here),
                                                  Cauchy-Schwarz, int w_a|hhat|^2 = 2 pi H.
  E_freq_ij  = 2 Tstar min( nu_X^{ij}, sqrt(D_i D_j) ),  D_i = 2 pi H_ii - mass_i(X),
                                                  the mass computed on the same nodes with its
                                                  own Bernstein enclosure E_mass_i.

POSITIVITY (same method as the ratified packet, CLASSFLOOR 2.4).  Split F = F0 + Delta,
F0 the thin midpoint matrix, |Delta| <= R entrywise; then

  lambda_min(F) >= lambda_min(F0) - ||Delta||_2,  ||Delta||_2 <= ||R||_2 <= min(||R||_F,||R||_inf),

and lambda_min(F0) > s is certified by an interval Cholesky of F0 - sI.  Success proves every
symmetric matrix in the hull positive definite, the exact F included, hence -- the block being
real symmetric -- also for all COMPLEX coefficient vectors.

PENCIL FLOOR.  lambda_min(F,H) >= lam  <=>  F - lam H >= 0, certified by the same split with
radius R_F + lam R_H, bisected in lam.  The lower endpoint is exported as a certified rational
and a certified rounded-down decimal; the upper endpoint is the interval Rayleigh quotient of
the (exactly rounded) float minimizing vector.

SIGNED WITNESS.  If a block fails, the float minimizing vector is rounded to exact binary
rationals and c*Fc is enclosed in ball arithmetic; the SIGNED upper endpoint is the judge's
discriminator.  `abs_lower` is never used as a signed lower endpoint (NOTES.md item 3): all
directed endpoints go through legser.

Usage: legassemble.py X J0 raw1 [raw2 ...] [--ebase S --ebasem S]
"""
import sys, os, re

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, ctx
import legarb, legbudget, legser

PREC = 400
ctx.prec = PREC
NAMES = legarb.NAMES
EVEN, ODD = legarb.EVEN, legarb.ODD

# post-hoc optimized Bernstein bounds over [0,6000], w=0.5, n=36, best rho (legequad.py),
# stored as CERTIFIED UPWARD-ROUNDED decimals (legser.dec_upper of the full ball).
EBASE_DEF = "9.00663030119015950e-09"
EBASEM_DEF = "1.87229186662733177e-17"


# --------------------------------------------------------------- directed endpoints
def ub(x):
    """thin arb >= sup(x), sign-agnostic and certified (legser)."""
    return arb(legser.dec_upper(x, 20))


def lb(x):
    """thin arb <= inf(x), sign-agnostic and certified (legser)."""
    return arb(legser.dec_lower(x, 20))


def read_mr(txt, key):
    """(mid, rad_upper) as thin arb.  The float transport is radius-padded (NOTES.md item 1)."""
    m = re.search(re.escape(key) + r"\s*=\s*\[?([-+0-9.eE]+)\s*\+/-\s*([0-9.eE+-]+)\]?", txt)
    if m is None:
        m = re.search(re.escape(key) + r"\s*=\s*([-+0-9.eE]+)", txt)
        if m is None:
            raise KeyError(key)
        mid, rad = m.group(1), "0"
    else:
        mid, rad = m.group(1), m.group(2)
    ctx.prec = PREC
    a = arb(mid)
    r = arb(rad) * arb("1.0001") + a.abs_upper() * arb(2) ** -48 + arb("1e-300")
    return a, r.abs_upper()


def read_sum(texts, key):
    """band-additive read: sum of the same key over all raw files."""
    mid = arb(0); rad = arb(0)
    for t in texts:
        a, r = read_mr(t, key)
        mid = mid + a
        rad = rad + r
    return mid.mid(), (rad + mid.rad()).abs_upper()


# --------------------------------------------------------------- interval Cholesky
def interval_cholesky(A):
    n = len(A)
    L = [[arb(0)] * n for _ in range(n)]
    piv = []
    for k in range(n):
        s = A[k][k]
        for t in range(k):
            s = s - L[k][t] * L[k][t]
        piv.append(s)
        if not (s > arb(0)):
            return False, piv
        L[k][k] = s.sqrt()
        for i in range(k + 1, n):
            u = A[i][k]
            for t in range(k):
                u = u - L[i][t] * L[k][t]
            L[i][k] = u / L[k][k]
    return True, piv


def rnorm_bound(R):
    """rigorous upper bound for ||R||_2 of the nonnegative symmetric radius matrix R."""
    ctx.prec = PREC
    n = len(R)
    fro = arb(0)
    for i in range(n):
        for j in range(n):
            fro += R[i][j] * R[i][j]
    fro = fro.sqrt().abs_upper()
    inf = arb(0)
    for i in range(n):
        s = arb(0)
        for j in range(n):
            s += R[i][j]
        s = s.abs_upper()
        if s > inf:
            inf = s
    return fro if fro < inf else inf


def spd_certify(A0, R):
    ctx.prec = PREC
    s = rnorm_bound(R)
    n = len(A0)
    B = [[A0[i][j] - (s if i == j else arb(0)) for j in range(n)] for i in range(n)]
    ok, piv = interval_cholesky(B)
    return ok, s, piv


def certify_lam(F0, RF, H0, RH, hi=0.02, iters=60):
    ctx.prec = PREC
    n = len(F0)

    def ok(lam):
        A = [[F0[i][j] - lam * H0[i][j] for j in range(n)] for i in range(n)]
        R = [[(RF[i][j] + lam * RH[i][j]).abs_upper() for j in range(n)] for i in range(n)]
        return spd_certify(A, R)[0]

    if not ok(arb(0)):
        return None
    a, b = arb(0), arb(hi)
    if ok(b):
        return b
    for _ in range(iters):
        mid = (a + b) / 2
        if ok(mid):
            a = mid
        else:
            b = mid
    return a


def quad(M, c):
    ctx.prec = PREC
    n = len(M)
    s = arb(0)
    for i in range(n):
        for j in range(n):
            s += c[i] * M[i][j] * c[j]
    return s


def fmid(M):
    import numpy as np
    n = len(M)
    return np.array([[float(M[i][j].mid().str(20, radius=False)) for j in range(n)]
                     for i in range(n)])


def build(X, J0, texts, ebase, ebasem):
    ctx.prec = PREC
    d, A = legarb.profiles(PREC)
    Hfull = legarb.gram(d, A, PREC)
    L1 = legarb.l1_bounds(d, Hfull, PREC)
    T = legbudget.Tstar()
    eps = legbudget.eps_J(J0)
    nu = legbudget.nu_matrix(X, T, PREC)
    Ebase = arb(ebase)
    Ebasem = arb(ebasem)

    # ---- mass deficits D_i (signed enclosure, then a certified nonnegative upper bound)
    D = []
    MASSROW = []
    for i in range(8):
        Mi, Mr = read_sum(texts, f"MASS[{NAMES[i]}]")
        em = (L1[i] * L1[i] * Ebasem).abs_upper()
        tgt = 2 * arb.pi() * Hfull[i][i]
        Dball = tgt - arb(Mi, (Mr + em).abs_upper())
        dup = ub(Dball)
        dlo = lb(Dball)
        D.append(dup if dup > arb(0) else arb(0))
        MASSROW.append((tgt, arb(Mi, Mr), em, dlo, dup))

    Ic = {}; Icr = {}; Eq = {}; Ee = {}; Ef = {}; Efnu = {}
    for i in range(8):
        for j in range(i, 8):
            if (i + j) % 2:
                continue
            v, vr = read_sum(texts, f"I_compact[{NAMES[i]},{NAMES[j]}]")
            eq = (L1[i] * L1[j] * Ebase).abs_upper()
            ee = (4 * arb.pi() * eps * (Hfull[i][i] * Hfull[j][j]).sqrt()).abs_upper()
            efnu = (2 * T * nu[i][j]).abs_upper()
            efD = (2 * T * (D[i] * D[j]).sqrt()).abs_upper()
            ef = efD if efD < efnu else efnu
            for k in ((i, j), (j, i)):
                Ic[k] = v; Icr[k] = vr; Eq[k] = eq; Ee[k] = ee; Ef[k] = ef; Efnu[k] = efnu
    return dict(d=d, A=A, H=Hfull, L1=L1, T=T, eps=eps, nu=nu, Ebase=Ebase, Ebasem=Ebasem,
                D=D, MASSROW=MASSROW, Ic=Ic, Icr=Icr, Eq=Eq, Ee=Ee, Ef=Ef, Efnu=Efnu)


def block(S, idx):
    """(F0, RF, H, H0, RH) restricted to the index list idx."""
    n = len(idx)
    F0 = [[S['Ic'][(idx[i], idx[j])] for j in range(n)] for i in range(n)]
    RF = [[(S['Icr'][(idx[i], idx[j])] + S['Eq'][(idx[i], idx[j])]
            + S['Ee'][(idx[i], idx[j])] + S['Ef'][(idx[i], idx[j])]).abs_upper()
           for j in range(n)] for i in range(n)]
    H = [[S['H'][idx[i]][idx[j]] for j in range(n)] for i in range(n)]
    H0 = [[H[i][j].mid() for j in range(n)] for i in range(n)]
    RH = [[H[i][j].rad().abs_upper() for j in range(n)] for i in range(n)]
    return F0, RF, H, H0, RH


def main(X, J0, paths, ebase=EBASE_DEF, ebasem=EBASEM_DEF):
    import numpy as np
    import scipy.linalg as sla
    texts = [open(p).read() for p in paths]
    S = build(X, J0, texts, ebase, ebasem)
    Hfull = S['H']

    print("=" * 108)
    print(f"LEGENDRE PACKET FLOOR MATRICES   X={X}  J0={J0}  tests: "
          + ", ".join(f"{NAMES[j]}(P_{j})" for j in range(8)))
    print(f"Tstar = {S['T'].str(12)}   eps_J0 = {S['eps'].str(8)} (C = 256)"
          f"   Ebase = {ebase}   Ebasem = {ebasem}")
    print(f"raw bands: " + ", ".join(os.path.basename(p) for p in paths))
    print("=" * 108)

    OUT = {}
    for tag, idx in (("EVEN {L0,L2,L4,L6}", EVEN), ("ODD  {L1,L3,L5,L7}", ODD)):
        F0, RF, H, H0, RH = block(S, idx)
        nm = [NAMES[i] for i in idx]
        print(f"\n{'='*108}\nBLOCK {tag}\n")
        print("-- H (Gram, exact rational in delta) --")
        for i in range(4):
            print("   " + nm[i].rjust(3) + " " + " ".join(H[i][j].str(16).rjust(26)
                                                          for j in range(4)))
        print("\n-- F (interval) --")
        for i in range(4):
            print("   " + nm[i].rjust(3) + " " +
                  " ".join(arb(F0[i][j].mid(), RF[i][j]).str(14).rjust(28) for j in range(4)))
        print("\n-- ledger per entry --")
        print(f"   {'entry':10s} {'I_compact (rule value)':>30s} {'E_quad':>11s} {'E_euler':>11s}"
              f" {'E_freq':>11s} {'(nu branch)':>12s}")
        for a in range(4):
            for b in range(a, 4):
                i, j = idx[a], idx[b]
                print(f"   {NAMES[i]+','+NAMES[j]:10s} "
                      f"{arb(S['Ic'][(i,j)].mid(), S['Icr'][(i,j)]).str(20):>30s} "
                      f"{S['Eq'][(i,j)].str(4):>11s} {S['Ee'][(i,j)].str(4):>11s} "
                      f"{S['Ef'][(i,j)].str(4):>11s} {S['Efnu'][(i,j)].str(4):>12s}")
        print("\n-- diagonal normalized floors F_ii/H_ii (certified directed endpoints) --")
        for a in range(4):
            i = idx[a]
            q = arb(F0[a][a].mid(), RF[a][a]) / H[a][a]
            print(f"   {NAMES[i]:4s} [{legser.dec_lower(q, 14)}, {legser.dec_upper(q, 14)}]"
                  f"   >= 1/500: {bool(lb(q) > arb(1)/500)}"
                  f"   >= 1/1000: {bool(lb(q) > arb(1)/1000)}")

        print("\n-- positivity certificate (midpoint split + Weyl + interval Cholesky) --")
        okH, sH, pH = spd_certify(H0, RH)
        okF, sF, pF = spd_certify(F0, RF)
        print(f"   H : ok={okH}  ||R||_2 <= {sH.str(6)}  shifted pivots = "
              + ", ".join(p.str(8) for p in pH))
        print(f"   F : ok={okF}  ||R||_2 <= {sF.str(6)}  shifted pivots = "
              + ", ".join(p.str(8) for p in pF))
        plain = interval_cholesky([[arb(F0[i][j].mid(), RF[i][j]) for j in range(4)]
                                   for i in range(4)])
        print(f"   (plain interval Cholesky without the split: ok={plain[0]}, pivots = "
              + ", ".join(p.str(4) for p in plain[1]) + ")")

        print("\n-- certified pencil floor lambda_min(H^-1/2 F H^-1/2) --")
        lam = certify_lam(F0, RF, H0, RH)
        Ff = fmid(F0); Hf = fmid(H0)
        ev, V = sla.eigh(Ff, Hf)
        v = V[:, 0] / np.max(np.abs(V[:, 0]))
        from fractions import Fraction
        cex = [arb(Fraction(float(t)).numerator) / Fraction(float(t)).denominator for t in v]
        Fb = [[arb(F0[i][j].mid(), RF[i][j]) for j in range(4)] for i in range(4)]
        num = quad(Fb, cex); den = quad(H, cex)
        ray = num / den
        if lam is None:
            print("   lower: NOT CERTIFIED (F itself not certifiably PD at this error budget)")
        else:
            p, q_, rs = legser.rat_lower(lam)
            print(f"   lower: {legser.dec_lower(lam, 14)}   (rational {rs} = "
                  f"{float(p)/q_:.12g})   >= 1/1000: {bool(lb(lam) > arb(1)/1000)}"
                  f"   >= 1/2000: {bool(lb(lam) > arb(1)/2000)}"
                  f"   >= 1/5000: {bool(lb(lam) > arb(1)/5000)}")
        print(f"   upper (Rayleigh of the exactly rounded float minimizer): "
              f"{legser.dec_upper(ray, 14)}")
        print(f"   SIGNED enclosure of c*Fc on that vector: "
              f"[{legser.dec_lower(num, 14)}, {legser.dec_upper(num, 14)}]"
              f"   c*Hc = {den.str(12)}")
        neg = bool(ub(num) < arb(0))
        strad = bool(num.overlaps(arb(0)))
        print(f"   strictly negative upper endpoint: {neg}      zero-straddle: {strad}")

        print("\n-- weakest direction and modes (float, DIAGNOSTIC_NEVER_A_PROOF) --")
        print(f"   pencil eigenvalues = {np.array2string(ev, precision=8)}")
        print(f"   eig(F0) = {np.array2string(np.linalg.eigvalsh(Ff), precision=6)}")
        print(f"   eig(H0) = {np.array2string(np.linalg.eigvalsh(Hf), precision=6)}")
        for k in range(4):
            vv = V[:, k] / np.max(np.abs(V[:, k]))
            lab = "weakest" if k == 0 else f"mode {k} "
            print(f"   {lab}: " + "  ".join(f"{n}:{c:+.5f}" for n, c in zip(nm, vv)))

        print("\n-- nested growth of the floor (first k tests of the block) --")
        for k in range(1, 5):
            sub = idx[:k]
            f0, rf, h, h0, rh = block(S, sub)
            lk = certify_lam(f0, rf, h0, rh)
            evk = sla.eigh(fmid(f0), fmid(h0))[0]
            ls = "NOT CERTIFIED" if lk is None else legser.dec_lower(lk, 12)
            print(f"   k={k} ({','.join(NAMES[t] for t in sub):20s})  certified lower = {ls:>18s}"
                  f"   float lambda_min = {evk[0]:.10g}")
        OUT[tag.split()[0]] = dict(F0=F0, RF=RF, H=H, H0=H0, RH=RH, lam=lam, ok=okF,
                                   s=sF, ev=ev, V=V, num=num, den=den, idx=idx)

    print("\n" + "=" * 108)
    print("MASS CHECK (V1) -- load-bearing: it supplies the sharp frequency tail")
    for i in range(8):
        tgt, Mi, em, dlo, dup = S['MASSROW'][i]
        print(f"   {NAMES[i]:4s} 2piH = {tgt.str(18):>24s}  computed = {Mi.str(18):>24s}"
              f"  D_i in [{legser.dec_lower(dlo,6)}, {legser.dec_upper(dup,6)}]"
              f"  nu_ii = {S['nu'][i][i].abs_upper().str(6):>11s}"
              f"  D<=nu: {bool(dup < S['nu'][i][i].abs_upper())}")
    return S, OUT


if __name__ == '__main__':
    a = sys.argv[1:]
    eb, ebm = EBASE_DEF, EBASEM_DEF
    if '--ebase' in a:
        k = a.index('--ebase'); eb = a[k + 1]; del a[k:k + 2]
    if '--ebasem' in a:
        k = a.index('--ebasem'); ebm = a[k + 1]; del a[k:k + 2]
    main(float(a[0]), int(a[1]), a[2:], eb, ebm)
