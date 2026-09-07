"""Parity-complete Legendre packet for the CLASSFLOOR floor matrix (verdict 5.6).

PREDECLARED PACKET (fixed before any spectrum was looked at):

    h_j = (d^2/dx^2 - 1/4)[ eta_4(x) P_j(x/delta) ],   j = 0..7,
    eta_4 = (1 - z^2)^4,   z = x/delta,   delta = (log 3 - log 2)/8,
    N = 1, zero extension, support [-delta, delta].

P_j is the Legendre polynomial.  P_j is even for even j and odd for odd j, so

    even block  j in {0,2,4,6}      odd block  j in {1,3,5,7}.

Since b(xi) = (1 - cos(a xi)) ell_2(xi) is real and EVEN, the cross-parity entries of
F vanish exactly (the integrand is odd), and the two blocks decouple.

RANK.  eta -> eta'' - eta/4 is injective on polynomials (its kernel is spanned by
exponentials), and p -> (1-z^2)^4 p is injective, so dim span{h_0..h_7} = 8: rank 4 in
each parity block.  Checked symbolically over Q(u), u = delta^{-2} (rank_report()).

COEFFICIENTS.  With eta_j(z) = sum_n e_n z^n (exact rationals),

    h_j(x) = p_j(z) = sum_n a_n z^n,   a_n = u (n+2)(n+1) e_{n+2} - e_n/4,  u = delta^{-2}.

VANISHING ORDER.  eta_j has a zero of order exactly 4 at z = +-1 (P_j(+-1) = +-1 != 0),
so eta_j'' has one of order 2 and h_j one of order exactly m = 2 for EVERY j.  Hence
h_j and h_j' vanish at +-delta, the analytic transform tail is the xi^{-3} one, and

    |hhat_j(xi)| <= C_a/|xi|^3 + C_b/|xi|^4,
    C_a = 2|p^{(2)}(1)| delta^{-2},
    C_b = [2|p^{(3)}(1)| + int_{-1}^1 |p^{(4)}|] delta^{-3},
    int_{-1}^1 |p^{(t)}| <= sum_n |a_n| n!/(n-t)! * 2/(n-t+1).

Note eta_j^{(4)}(+-1) = 4! (1+-z)^4 P_j |_{z=+-1} = 384 (+-1)^j in modulus 384 for every j,
so C_a is the SAME for all eight tests while H_jj grows with j.

TRANSFORM.  hhat_j(xi) = delta int_{-1}^1 p_j(z) e^{-i delta xi z} dz.  With c = delta xi
and E_n(c) = int_0^1 z^n e^{icz} dz = C_n(c) + i S_n(c),

    even j:  hhat_j = 2 delta sum_{n even} a_n C_n(c)          (real, even in xi)
    odd  j:  hhat_j = -i v_j,  v_j = 2 delta sum_{n odd} a_n S_n(c)  (v_j real, odd in xi)

and for a same-parity pair conj(hhat_i) hhat_j = g_i g_j with g = the real profile above
(for the odd block: (+i v_i)(-i v_j) = v_i v_j).  The holomorphic continuation used for the
Bernstein bound is conj(hhat_i(zbar)) hhat_j(z), which for these real-coefficient profiles
equals G_i(z) G_j(z) with G entire and |G_i(z)| <= ||h_i||_1 e^{delta |Im z|}: exactly the
same M-bound as the even packet (verdict 2.2).

NOTHING here becomes a Python float on the certificate path (except the protected
pack/read transports documented in NOTES.md item 1).
"""
import sys, os
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from flint import arb, acb, ctx

NAMES = tuple(f"L{j}" for j in range(8))
EVEN = [0, 2, 4, 6]
ODD = [1, 3, 5, 7]
NMAX = 15                      # deg_z p_7 = 8 + 7 = 15
MORD = 2                       # order of the zero of h at +-delta, every test
PORD = 3                       # = m + 1


# ------------------------------------------------------------------ exact coefficients
def legendre_coeffs(J):
    """[ [c_0..c_j] Fractions ] for P_0..P_J via (n+1)P_{n+1} = (2n+1) z P_n - n P_{n-1}."""
    P = [[Fraction(1)], [Fraction(0), Fraction(1)]]
    for n in range(1, J):
        a = [Fraction(0)] * (n + 2)
        for k, c in enumerate(P[n]):
            a[k + 1] += Fraction(2 * n + 1, n + 1) * c
        for k, c in enumerate(P[n - 1]):
            a[k] -= Fraction(n, n + 1) * c
        P.append(a)
    return P[:J + 1]


def _poly_mul(p, q):
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def eta_coeffs():
    """{j: [e_0..e_{8+j}] Fractions} for eta_j = (1-z^2)^4 P_j."""
    w = [Fraction(0)] * 9
    c = 1
    for m in range(5):
        w[2 * m] = Fraction(c if m % 2 == 0 else -c)
        c = c * (4 - m) // (m + 1)
    L = legendre_coeffs(7)
    return {j: _poly_mul(w, L[j]) for j in range(8)}


def p_coeffs():
    """{j: [(cu_n, cc_n)]}: a_n = cu_n * u + cc_n exactly, u = delta^{-2}."""
    out = {}
    for j, e in eta_coeffs().items():
        deg = len(e) - 1
        a = []
        for n in range(deg + 1):
            cu = Fraction((n + 2) * (n + 1)) * e[n + 2] if n + 2 <= deg else Fraction(0)
            a.append((cu, -e[n] / 4))
        while len(a) > 1 and a[-1] == (Fraction(0), Fraction(0)):
            a.pop()
        out[j] = a
    return out


# ------------------------------------------------------------------ arb profiles
def profiles(prec):
    """(delta, {j: [A_0..A_deg] arb}) -- the polynomial p_j in z."""
    ctx.prec = prec
    d = (arb(3).log() - arb(2).log()) / 8
    u = 1 / (d * d)
    out = {}
    for j, a in p_coeffs().items():
        out[j] = [u * arb(cu.numerator) / cu.denominator
                  + arb(cc.numerator) / cc.denominator for cu, cc in a]
    return d, out


def gram(d, A, prec, idx=range(8)):
    """H_ij = <h_i,h_j> = delta * int_{-1}^1 p_i p_j dz, exact rational in delta."""
    ctx.prec = prec
    idx = list(idx)
    n = len(idx)
    Hm = [[arb(0)] * n for _ in range(n)]
    for ii, i in enumerate(idx):
        for jj, j in enumerate(idx):
            s = arb(0)
            for k, ak in enumerate(A[i]):
                for l, al in enumerate(A[j]):
                    if (k + l) % 2 == 0:
                        s += ak * al * 2 / arb(k + l + 1)
            Hm[ii][jj] = d * s
    return Hm


def _fall(n, t):
    if n < t:
        return 0
    r = 1
    for i in range(t):
        r *= (n - i)
    return r


def tails(d, A, prec, idx=range(8)):
    """{j: (m, P, C_a, C_b)}, |hhat_j| <= C_a/|xi|^3 + C_b/|xi|^4."""
    ctx.prec = prec
    out = {}
    for j in idx:
        a = A[j]
        pm = arb(0); pm1 = arb(0); l1 = arb(0)
        for n, an in enumerate(a):
            pm += an * _fall(n, MORD)
            pm1 += an * _fall(n, MORD + 1)
            f = _fall(n, MORD + 2)
            if f:
                l1 += an.abs_upper() * f * 2 / arb(n - (MORD + 2) + 1)
        Ca = 2 * pm.abs_upper() / d ** MORD
        Cb = (2 * pm1.abs_upper() + l1) / d ** (MORD + 1)
        out[j] = (MORD, PORD, Ca, Cb)
    return out


def l1_bounds(d, Hm, prec):
    """||h_i||_1 <= sqrt(2 delta H_ii)."""
    ctx.prec = prec
    return [(2 * d * Hm[i][i]).sqrt() for i in range(len(Hm))]


# ------------------------------------------------------------------ moments E_n(c)
CSWITCH = 48


def emoments(c, N, prec):
    """[E_0..E_N], E_n = int_0^1 z^n e^{i c z} dz, as acb balls.  c an acb (real here).

    |c| <= CSWITCH: entire power series E_n = sum_k (ic)^k/(k!(n+k+1)).  The loop stops
    only when k > 2|c| + 4 (so the ratio |c|/(k+1) < 1/2) AND |t_k| < 2^{-prec-10};
    the remainder is then bounded by 2|t_k|/(n+k+1) (geometric, ratio < 1/2).

    |c| > CSWITCH: the exact integration-by-parts recursion
        E_0 = (e^{ic}-1)/(ic),   E_n = e^{ic}/(ic) - (n/(ic)) E_{n-1},
    whose error amplification factor n/|c| <= 15/48 < 1 is contracting, so no
    cancellation occurs (|E_n| ~ 1/|c| and the second term is ~ n/|c|^2).
    """
    ctx.prec = prec
    cu = c.abs_upper()
    if cu <= arb(CSWITCH):
        tot = [acb(0)] * (N + 1)
        t = acb(1)
        k = 0
        thresh = arb(2) ** (-prec - 10)
        while True:
            for n in range(N + 1):
                tot[n] += t / (n + k + 1)
            k += 1
            t = t * acb(0, 1) * c / k
            if k > 2 * cu + 4 and t.abs_upper() < thresh:
                break
            if k > 100000:
                raise RuntimeError("emoments series did not terminate")
        assert bool(c.abs_upper() / (k + 1) < arb(1) / 2)
        e = 2 * t.abs_upper()
        return [tot[n] + acb(arb(0, (e / (n + k + 1)).abs_upper()),
                             arb(0, (e / (n + k + 1)).abs_upper())) for n in range(N + 1)]
    ic = acb(0, 1) * c
    eic = ic.exp()
    E = [(eic - 1) / ic]
    for n in range(1, N + 1):
        E.append(eic / ic - (acb(n) / ic) * E[n - 1])
    return E


def hprofiles(xi, d, A, prec, idx=range(8), N=NMAX):
    """[g_i(xi)] real arb: g = hhat for even tests, g = i*hhat (real) for odd tests.
    conj(hhat_i) hhat_j = g_i g_j and |hhat_i|^2 = g_i^2 for same-parity pairs."""
    ctx.prec = prec
    c = acb(d) * xi
    E = emoments(c, N, prec)
    out = []
    for j in idx:
        s = arb(0)
        for n, an in enumerate(A[j]):
            if j % 2 == 0:
                if n % 2 == 0:
                    s += an * E[n].real
            else:
                if n % 2 == 1:
                    s += an * E[n].imag
        out.append(2 * d * s)
    return out


# ------------------------------------------------------------------ exact structure checks
def rank_report():
    """Symbolic rank over Q(u) of the eight profiles, and of each parity block."""
    import sympy as sp
    u = sp.symbols('u')
    P = p_coeffs()
    rows = []
    for j in range(8):
        r = [sp.Integer(0)] * (NMAX + 1)
        for n, (cu, cc) in enumerate(P[j]):
            r[n] = sp.Rational(cu.numerator, cu.denominator) * u + sp.Rational(cc.numerator,
                                                                              cc.denominator)
        rows.append(r)
    M = sp.Matrix(rows)
    res = {"all": M.rank(),
           "even": sp.Matrix([rows[j] for j in EVEN]).rank(),
           "odd": sp.Matrix([rows[j] for j in ODD]).rank()}
    return res


def vanishing_report():
    """p_j^{(t)}(+-1) = 0 for t < 2 and != 0 for t = 2, EXACTLY in u = delta^{-2}."""
    P = p_coeffs()
    out = {}
    for j in range(8):
        rows = []
        for t in range(0, 4):
            for sgn in (1, -1):
                su = sum(cu * _fall(n, t) * (sgn ** (n - t) if n >= t else 0)
                         for n, (cu, cc) in enumerate(P[j]))
                sc = sum(cc * _fall(n, t) * (sgn ** (n - t) if n >= t else 0)
                         for n, (cu, cc) in enumerate(P[j]))
                rows.append((t, sgn, su, sc))
        out[j] = rows
    return out


def pole_moments(d, A, prec, idx=range(8)):
    """int h e^{+-x/2} dx, must be 0 for every test (algebraic identity)."""
    ctx.prec = prec
    out = {}
    for j in idx:
        for sg in (1, -1):
            tot = arb(0)
            for n, an in enumerate(A[j]):
                # int_{-1}^1 z^n e^{sg*d*z/2} dz = sum_k (sg d/2)^k/k! * (1+(-1)^{n+k})/(n+k+1)
                s = arb(0); t = arb(1); k = 0
                while True:
                    if (n + k) % 2 == 0:
                        s += t * 2 / arb(n + k + 1)
                    k += 1
                    t = t * (arb(sg) * d / 2) / k
                    if t.abs_upper() < arb(2) ** (-prec + 20) and k > 20:
                        break
                tot += an * d * s
            out[(j, sg)] = tot
    return out


if __name__ == '__main__':
    PR = 400
    ctx.prec = PR
    d, A = profiles(PR)
    Hm = gram(d, A, PR)
    T = tails(d, A, PR)
    L1 = l1_bounds(d, Hm, PR)
    print("delta =", d.str(20), "   2 delta =", (2 * d).str(20), "   a = log2 =",
          arb(2).log().str(20))
    print("\nprofiles p_j(z) = sum a_n z^n  (deg, parity, C_a, C_b, H_jj):")
    for j in range(8):
        m, P_, Ca, Cb = T[j]
        print(f"  {NAMES[j]}  deg={len(A[j])-1:2d}  parity={'even' if j%2==0 else 'odd '}"
              f"  m={m}  C_a={Ca.str(12)}  C_b={Cb.str(12)}  H={Hm[j][j].str(16)}")
    print("\nGram H (exact rational in delta), 8x8:")
    for i in range(8):
        print("  " + NAMES[i].rjust(3) + " " + " ".join(Hm[i][j].str(12).rjust(22)
                                                        for j in range(8)))
    print("\ncross-parity Gram entries (must be exactly 0):")
    bad = [(i, j, Hm[i][j].str(6)) for i in range(8) for j in range(8)
           if (i + j) % 2 == 1 and not Hm[i][j].is_zero()]
    print("   nonzero cross-parity entries:", bad if bad else "NONE (all exactly 0)")
    print("\n||h_i||_1 <= sqrt(2 delta H_ii):", [x.str(10) for x in L1])

    print("\nEXACT vanishing p^{(t)}(+-1), rational in u = delta^-2"
          " (t=0,1 must be 0; t=2 must be nonzero):")
    V = vanishing_report()
    for j in range(8):
        z01 = all(su == 0 and sc == 0 for t, s, su, sc in V[j] if t < 2)
        t2 = [(s, str(su), str(sc)) for t, s, su, sc in V[j] if t == 2]
        print(f"  {NAMES[j]}  t<2 all zero: {z01}   p''(+-1) = {t2}")

    print("\nSYMBOLIC RANK over Q(u):", rank_report())

    print("\npole moments int h e^{+-x/2} dx (arb, must contain 0):")
    PM = pole_moments(d, A, PR)
    mxp = max(v.abs_upper() for v in PM.values())
    print("   max |.| =", mxp.str(6), "   below 1e-100 (algebraic identity, evaluation"
          " width only):", bool(mxp < arb(10) ** -100))

    print("\nh_0 vs the h4 profile of the earlier certificate (must be identical):")
    import h4arb
    d4, A4, H4 = h4arb.profile(PR)
    diff = max((A[0][2 * k] - A4[k]).abs_upper() for k in range(5))
    odd0 = max(A[0][2 * k + 1].abs_upper() for k in range(4)) if len(A[0]) > 1 else arb(0)
    print(f"   max |A0_even - A4| = {diff.str(6)}   max |A0_odd| = {odd0.str(6)}"
          f"   H_00 - H_4 = {(Hm[0][0]-H4).abs_upper().str(6)}")

    print("\nmoment evaluator cross-check (series vs recursion) at c near the switch:")
    for cv in ("12.5", "47.9", "48.1", "202.7", "304.1"):
        c = acb(arb(cv))
        Es = emoments(c, NMAX, 4000) if arb(cv) > arb(CSWITCH) else emoments(c, NMAX, 400)
        # force the other branch by a high-precision series
        ctx.prec = 4000
        tot = [acb(0)] * (NMAX + 1); t = acb(1); k = 0
        while k < 8000:
            for n in range(NMAX + 1):
                tot[n] += t / (n + k + 1)
            k += 1
            t = t * acb(0, 1) * acb(arb(cv)) / k
            if k > 2 * float(cv) + 4 and t.abs_upper() < arb(2) ** -3000:
                break
        ctx.prec = 400
        mx = max((Es[n] - tot[n]).abs_upper() for n in range(NMAX + 1))
        print(f"   c={cv:>7s}  max |recursion/series - reference series| = {mx.str(6)}")
