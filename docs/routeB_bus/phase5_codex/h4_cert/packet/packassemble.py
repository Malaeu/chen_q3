"""Assemble the packet floor matrix F, certify F >= 0, and certify lambda_min of (F, H).

LEDGER per entry (i,j):   F_ij  in  I_compact_ij +/- [E_quad + E_euler + E_freq]

  E_quad_ij  = ||h_i||_1 ||h_j||_1 * Ebase        Bernstein ellipse, ATAP Thm 8.2, rho optimized
                                                  post hoc (packequad.py); the RULE is unchanged.
  E_euler_ij = 4 pi eps_{J0} sqrt(H_ii H_jj)      |ell_2 - ell_2^{[J0]}| <= 2 eps_{J0}, Cauchy-
                                                  Schwarz, and int w_a |hhat|^2 = 2 pi H exactly.
  E_freq_ij  = 2 Tstar min( nu_X^{ij}, sqrt(D_i D_j) )
        D_i := int_{|xi|>X} w_a |hhat_i|^2 = 2 pi H_i - int_{|xi|<=X} w_a |hhat_i|^2,
        the second term computed on the same nodes with its own Bernstein error E_mass_i.
        Both branches are rigorous; the D branch is the sharper one (the analytic transform-tail
        nu is 5-12x pessimistic here), and it turns the mass check from a diagnostic into a
        load-bearing row.

POSITIVITY.  Plain interval Cholesky is too lossy for this packet: F is nearly singular in
absolute units (lambda_min(F_3) = 0.50 against entries ~1.5e3), and the Schur complements
amplify the entry radii by ~20x.  Instead split F = F0 + Delta with F0 the (thin) midpoint
matrix and |Delta| <= R entrywise, and use

  lambda_min(F) >= lambda_min(F0) - ||Delta||_2,  ||Delta||_2 <= ||R||_2 <= min(||R||_F,||R||_inf)

(Weyl; for |B| <= R entrywise the spectral radius of |B| is dominated by that of R, so
||B||_2 <= ||R||_2, and ||R||_2 <= ||R||_inf for symmetric R).  lambda_min(F0) > s is certified
by an interval Cholesky of F0 - s I, which loses nothing here because F0 is thin (400 bits).
Success proves that EVERY symmetric matrix in the hull is positive definite, the exact F included.

PENCIL FLOOR.  lambda_min(F,H) >= lam  <=>  F - lam H >= 0; midpoint F0 - lam H0, radius
R_F + lam R_H.  Bisect lam with the same certificate.  A rigorous UPPER bound comes free from
any ball vector c: lambda_min <= (c*Fc)/(c*Hc).

Usage: packassemble.py rawfile X J0 [Ebase Ebasem]
"""
import sys, os, re

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, ctx
import packarb, packbudget

PREC = 400
ctx.prec = PREC
NAMES = packarb.NAMES
ND = len(NAMES)
REQ_IDX = [NAMES.index(n) for n in packarb.REQ]
SPAN3 = [NAMES.index(n) for n in ("h4", "h5", "h6")]
SPAN4 = [NAMES.index(n) for n in ("h4", "h5", "h6", "h7")]

# post-hoc optimized Bernstein bound (packequad.py 4000 0.5 36, best rho = 3.9)
EBASE_DEF = "5.02304551867e-9"
EBASEM_DEF = "1.24819457775e-17"


def read_mr(txt, key):
    """(mid, rad_upper) as arb, mid thin."""
    m = re.search(re.escape(key) + r"\s*=\s*\[?([-+0-9.eE]+)\s*\+/-\s*([0-9.eE+-]+)\]?", txt)
    if m is None:
        m = re.search(re.escape(key) + r"\s*=\s*([-+0-9.eE]+)", txt)
        mid, rad = m.group(1), "0"
    else:
        mid, rad = m.group(1), m.group(2)
    ctx.prec = PREC
    a = arb(mid)
    r = arb(rad) * arb("1.0001") + a.abs_upper() * arb(2) ** -48 + arb("1e-300")
    return a, r.abs_upper()


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
    """True if every symmetric A with |A - A0| <= R entrywise is positive definite."""
    ctx.prec = PREC
    s = rnorm_bound(R)
    n = len(A0)
    B = [[A0[i][j] - (s if i == j else arb(0)) for j in range(n)] for i in range(n)]
    ok, piv = interval_cholesky(B)
    return ok, s, piv


def sub(M, idx):
    return [[M[i][j] for j in idx] for i in idx]


def certify_lam(F0, RF, H0, RH, hi=0.02, iters=50):
    """largest lam with F - lam H certified positive definite over the hull."""
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


def rayleigh(F, H, c):
    ctx.prec = PREC
    n = len(F)
    num = arb(0); den = arb(0)
    for i in range(n):
        for j in range(n):
            num += c[i] * F[i][j] * c[j]
            den += c[i] * H[i][j] * c[j]
    return num / den


def _receipt():
    """RECEIPT REPAIR (CLASSFLOOR v2 §1.6): import the 60-digit outward upper endpoints written by packequad.py.
    The (1 + 2^-40) pad then covers the 60-digit decimal rounding by ~1e47 ulps. Falls back to the old 12-digit
    literals ONLY if no receipt exists (and says so)."""
    import os
    fn = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'equad_receipt.txt')
    if not os.path.exists(fn):
        print("WARNING: no out/equad_receipt.txt — using 12-digit literals (NOT an outward receipt)")
        return EBASE_DEF, EBASEM_DEF
    kv = dict(line.split(None, 1) for line in open(fn) if line.strip())
    print(f"receipt: rho={kv['rho'].strip()}  Ebase_upper60={kv['Ebase_upper60'].strip()}  Ebasem_upper60={kv['Ebasem_upper60'].strip()}")
    return kv['Ebase_upper60'].strip(), kv['Ebasem_upper60'].strip()

def main(path, X, J0, ebase=None, ebasem=None):
    if ebase is None or ebasem is None:
        ebase, ebasem = _receipt()
    txt = open(path).read()
    ctx.prec = PREC
    d, A = packarb.profiles(PREC)
    Hm = packarb.gram(d, A, PREC, NAMES)
    L1 = packarb.l1_bounds(d, Hm, PREC)
    T = packbudget.Tstar()
    eps = packbudget.eps_J(J0)
    nu = packbudget.nu_matrix(X, T, PREC, NAMES)
    Ebase = arb(ebase) * (1 + arb(2) ** -40)
    Ebasem = arb(ebasem) * (1 + arb(2) ** -40)

    # ---- mass deficits D_i (rigorous upper bounds): the sharp tail row
    D = []
    MASSROW = []
    for i in range(ND):
        Mi, Mr = read_mr(txt, f"MASS[{NAMES[i]}]")
        em = (L1[i] * L1[i] * Ebasem).abs_upper()
        tgt = 2 * arb.pi() * Hm[i][i]
        dup = (tgt.abs_upper() - (Mi.abs_lower() - Mr - em)).abs_upper()
        dlo = tgt.abs_lower() - (Mi.abs_upper() + Mr + em)
        D.append(dup if dup > arb(0) else arb(0))
        MASSROW.append((tgt, Mi, Mr, em, dlo, dup))

    Ic = [[None] * ND for _ in range(ND)]
    Icr = [[None] * ND for _ in range(ND)]
    Eq = [[None] * ND for _ in range(ND)]
    Ee = [[None] * ND for _ in range(ND)]
    Ef = [[None] * ND for _ in range(ND)]
    Efnu = [[None] * ND for _ in range(ND)]
    F0 = [[None] * ND for _ in range(ND)]
    RF = [[None] * ND for _ in range(ND)]
    for i in range(ND):
        for j in range(i, ND):
            v, vr = read_mr(txt, f"I_compact[{NAMES[i]},{NAMES[j]}]")
            eq = (L1[i] * L1[j] * Ebase).abs_upper()
            ee = (4 * arb.pi() * eps * (Hm[i][i] * Hm[j][j]).sqrt()).abs_upper()
            efnu = (2 * T * nu[i][j]).abs_upper()
            efD = (2 * T * (D[i] * D[j]).sqrt()).abs_upper()
            ef = efD if efD < efnu else efnu
            Ic[i][j] = Ic[j][i] = v
            Icr[i][j] = Icr[j][i] = vr
            Eq[i][j] = Eq[j][i] = eq
            Ee[i][j] = Ee[j][i] = ee
            Ef[i][j] = Ef[j][i] = ef
            Efnu[i][j] = Efnu[j][i] = efnu
            F0[i][j] = F0[j][i] = v
            RF[i][j] = RF[j][i] = (vr + eq + ee + ef).abs_upper()
    H0 = [[Hm[i][j].mid() for j in range(ND)] for i in range(ND)]
    RH = [[Hm[i][j].rad().abs_upper() for j in range(ND)] for i in range(ND)]

    print("=" * 104)
    print(f"PACKET FLOOR MATRIX   X={X}  J0={J0}  tests: {', '.join(NAMES)}")
    print(f"Tstar = {T.str(12)}   eps_J0 = {eps.str(8)}   Ebase = {Ebase.str(8)}"
          f"   Ebasem = {Ebasem.str(8)}")
    print("=" * 104)

    print("\n-- H  (Gram, exact rational in delta) --")
    for i in range(ND):
        print("  " + NAMES[i].rjust(4) + " " +
              " ".join(Hm[i][j].str(16).rjust(26) for j in range(ND)))

    print("\n-- F  (interval) --")
    for i in range(ND):
        print("  " + NAMES[i].rjust(4) + " " +
              " ".join(arb(F0[i][j].mid(), RF[i][j]).str(14).rjust(28) for j in range(ND)))

    print("\n-- ledger per entry --")
    print(f"  {'entry':12s} {'I_compact (rule value)':>30s} {'E_quad':>11s} {'E_euler':>11s}"
          f" {'E_freq':>11s} {'(nu branch)':>12s}")
    for i in range(ND):
        for j in range(i, ND):
            print(f"  {NAMES[i]+','+NAMES[j]:12s} {arb(Ic[i][j].mid(), Icr[i][j]).str(20):>30s} "
                  f"{Eq[i][j].str(4):>11s} {Ee[i][j].str(4):>11s} {Ef[i][j].str(4):>11s}"
                  f" {Efnu[i][j].str(4):>12s}")

    print("\n-- diagonal normalized floors F_ii/H_ii --")
    for i in range(ND):
        q = arb(F0[i][i].mid(), RF[i][i]) / Hm[i][i]
        lo = q.mid() - q.rad(); lo = lo.mid() - lo.rad(); hi_ = q.mid() + q.rad(); hi_ = hi_.mid() + hi_.rad()   # signed directed endpoints (not abs_lower: CLASSFLOOR §2.5)
        print(f"  {NAMES[i]:5s} [{lo.str(14, radius=False)}, {hi_.str(14, radius=False)}]"
              f"   >= 1/500: {bool(lo > arb(1)/500)}   >= 1/1000: {bool(lo > arb(1)/1000)}")

    print("\n-- V1 mass check / tail source:  int_{|xi|<=X} w_a |hhat_i|^2 = 2 pi H_i - D_i,"
          "  D_i in [0, nu_ii] --")
    for i in range(ND):
        tgt, Mi, Mr, em, dlo, dup = MASSROW[i]
        print(f"  {NAMES[i]:5s} 2piH={tgt.str(18):>24s} computed={arb(Mi.mid(),Mr).str(18):>24s}"
              f"  D_i<={dup.str(6):>11s}  nu_ii={nu[i][i].abs_upper().str(6):>11s}"
              f"  0<=D: {bool(dup >= arb(0))}  D<=nu: {bool(dup < nu[i][i].abs_upper())}")

    print("\n-- exact rank identity h4z = h4 - h5 (entrywise, inside the computed balls) --")
    i4, i5, i4z = NAMES.index("h4"), NAMES.index("h5"), NAMES.index("h4z")
    okall = True
    for j in range(ND):
        lhs = arb(Ic[i4z][j].mid(), Icr[i4z][j])
        rhs = arb(Ic[i4][j].mid(), Icr[i4][j]) - arb(Ic[i5][j].mid(), Icr[i5][j])
        ok = lhs.overlaps(rhs)
        okall &= ok
        print(f"  j={NAMES[j]:5s} I[h4z,j]={lhs.str(14):>24s}  I[h4,j]-I[h5,j]={rhs.str(14):>24s}"
              f"   overlap={ok}")
    print(f"  ALL OVERLAP: {okall}")
    for j in range(ND):
        assert Hm[i4z][j].overlaps(Hm[i4][j] - Hm[i5][j])
    print("  Gram H satisfies the same identity exactly: True")

    print("\n" + "=" * 104)
    print("POSITIVITY CERTIFICATES")
    print("  method: lambda_min(F) >= lambda_min(F0) - ||R||_2,  ||R||_2 <= min(||R||_F,||R||_inf);"
          "\n          lambda_min(F0) > ||R||_2 certified by interval Cholesky of F0 - ||R||_2 I")
    for tag, idx, Mx, Rx in (("H  span3 (h4,h5,h6)", SPAN3, H0, RH),
                             ("H  span4 (h4,h5,h6,h7)", SPAN4, H0, RH),
                             ("F  span3 (h4,h5,h6)", SPAN3, F0, RF),
                             ("F  span4 (h4,h5,h6,h7)", SPAN4, F0, RF)):
        ok, s, piv = spd_certify(sub(Mx, idx), sub(Rx, idx))
        print(f"  {tag:24s} ok={str(ok):5s}  ||R||_2 <= {s.str(6):>11s}  shifted pivots = "
              + ", ".join(p.str(6) for p in piv))
    okr, sr, pr = spd_certify(sub(F0, REQ_IDX), sub(RF, REQ_IDX))
    print(f"  F  requested 4x4 (rank 3)  ok={okr}  (must be False: exactly singular,"
          f" kernel c=(1,-1,0,-1))")
    c = [arb(1), arb(-1), arb(0), arb(-1)]
    Fr = [[arb(F0[i][j].mid(), RF[i][j]) for j in REQ_IDX] for i in REQ_IDX]
    Hr = sub(Hm, REQ_IDX)
    n1 = arb(0); n2 = arb(0)
    for i in range(4):
        for j in range(4):
            n1 += c[i] * Fr[i][j] * c[j]
            n2 += c[i] * Hr[i][j] * c[j]
    print(f"  kernel check: c*Fc = {n1.str(6)}   c*Hc = {n2.str(6)}   both contain 0: "
          f"{bool(n1.overlaps(arb(0))) and bool(n2.overlaps(arb(0)))}")
    plain = interval_cholesky([[arb(F0[i][j].mid(), RF[i][j]) for j in SPAN3] for i in SPAN3])
    print(f"  plain interval Cholesky of F on span3 (no midpoint split), for comparison: "
          f"ok={plain[0]}, pivots = " + ", ".join(p.str(4) for p in plain[1]))

    print("\n" + "=" * 104)
    print("CERTIFIED PENCIL FLOOR   lambda_min(H^{-1/2} F H^{-1/2})")
    out = {}
    for tag, idx in (("span3", SPAN3), ("span4", SPAN4)):
        lam = certify_lam(sub(F0, idx), sub(RF, idx), sub(H0, idx), sub(RH, idx))
        out[tag] = lam
        if lam is None:
            print(f"  {tag}: NOT CERTIFIED (F itself not certifiably PD at this error budget)")
        else:
            print(f"  {tag}: lambda_min >= {(lam.mid() - lam.rad()).str(12)}"
                  f"    >= 1/1000: {bool(lam > arb(1)/1000)}"
                  f"    >= 1/2000: {bool(lam > arb(1)/2000)}")
    return (F0, RF, Hm, H0, RH, out)


if __name__ == '__main__':
    a = sys.argv
    main(a[1], float(a[2]), int(a[3]),
         a[4] if len(a) > 4 else EBASE_DEF, a[5] if len(a) > 5 else EBASEM_DEF)
