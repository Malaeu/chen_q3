"""Packet profiles for the SCALARFLOOR floor matrix (v1 (8) / v2 Cor. 1 (6)).

Tests: h = eta'' - eta/4 with eta = eta(z), z = x/delta, supported on |x| <= delta.
   eta4  = (1-z^2)^4          zero of order k = 4 at z = +-1
   eta5  = (1-z^2)^5          k = 5
   eta6  = (1-z^2)^6          k = 6
   eta4z = z^2 (1-z^2)^4      k = 4
   eta7  = (1-z^2)^7          k = 7   [ADDED: the four requested tests span only 3 dims]

RANK.  (1-z^2)^5 = (1-z^2)^4 - z^2(1-z^2)^4, so eta5 = eta4 - eta4z and hence, the map
eta -> eta'' - eta/4 being linear, h5 = h4 - h4z EXACTLY.  More generally all four
requested tests lie in (1-z^2)^4 * span{1, 1-z^2, (1-z^2)^2, z^2} = (1-z^2)^4 * span{1,z^2,z^4},
which is 3-dimensional.  eta7 adds (1-z^2)^4 * (1-z^2)^3, i.e. z^6, giving a genuine 4-dim span.
The map eta -> eta''-eta/4 is injective on polynomials (its kernel consists of exponentials),
so dim span{h} = dim span{eta}.

All eta are EVEN polynomials in z, so every h is real and even, hhat is real and even,
and M, F, H are real symmetric.  N = 1 for every test (v1 7.2: the normalized functional
is scale invariant); H_ij carries the whole normalization.

If eta(z) = sum_m e_m z^{2m}, then with d^2/dx^2 = delta^{-2} d^2/dz^2

    h(x) = p(z) = sum_j A_j z^{2j},   A_j = delta^{-2} e_{j+1}(2j+2)(2j+1) - e_j/4.

POLE-NULLITY  int h e^{+-x/2} dx = 0 is an algebraic identity whenever eta and eta' vanish
at z = +-1 (two integrations by parts; (e^{+-x/2})'' = e^{+-x/2}/4): true for all (k >= 2).

TRANSFORM TAIL.  eta has a zero of order k at z = +-1, so eta'' has one of order k-2, and
h = eta'' - eta/4 has one of order exactly m := k-2 (no cancellation: the eta/4 term has
order k > m).  Hence h, h', ..., h^{(m-1)} vanish at +-delta and m integrations by parts give
    hhat(xi) = (i xi)^{-m} int h^{(m)} e^{-i xi x} dx,
    |int h^{(m)} e^{-i xi x}| <= 2|h^{(m)}(delta)|/|xi| + (2|h^{(m+1)}(delta)| + ||h^{(m+2)}||_1)/xi^2,
so with  P := m+1,
    |hhat(xi)| <= C_a/|xi|^P + C_b/|xi|^{P+1},
    C_a = 2|p^{(m)}(1)| delta^{-m},
    C_b = 2|p^{(m+1)}(1)| delta^{-(m+1)} + delta^{-(m+1)} int_{-1}^1 |p^{(m+2)}(z)| dz,
    int_{-1}^1 |p^{(t)}| <= sum_{2j>=t} |A_j| (2j)!/(2j-t)! * 2/(2j-t+1)   (sharp monomial bound).
For m = 2 this is exactly (B3, B4) of the h4 report 3(f).  m = 2,3,4,2,5 for the five tests.

NOTHING here becomes a Python float on the certificate path.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from flint import arb, acb, ctx
import h4arb

REQ = ("h4", "h5", "h6", "h4z")            # the requested packet (rank 3)
NAMES = ("h4", "h5", "h6", "h4z", "h7")    # extended: genuine 4-dim span
JMAX = 7                                   # eta7 has degree 14 -> j = 0..7
ORDER = {"h4": 4, "h5": 5, "h6": 6, "h4z": 4, "h7": 7}   # order k of the zero at z = +-1


def _binom_eta(k):
    """integer coefficients e_m of (1-z^2)^k in z^{2m}."""
    e, c = [], 1
    for m in range(k + 1):
        e.append(c if m % 2 == 0 else -c)
        c = c * (k - m) // (m + 1)
    return e


def _etas():
    return {"h4": _binom_eta(4), "h5": _binom_eta(5), "h6": _binom_eta(6),
            "h4z": [0] + _binom_eta(4), "h7": _binom_eta(7)}


def profiles(prec):
    """(delta, {name: [A_0..A_m] arb})."""
    ctx.prec = prec
    d = (arb(3).log() - arb(2).log()) / 8
    di2 = 1 / (d * d)
    out = {}
    for name, e in _etas().items():
        m = len(e) - 1
        A = []
        for j in range(m + 1):
            t = arb(0)
            if j + 1 <= m:
                t += di2 * e[j + 1] * (2 * j + 2) * (2 * j + 1)
            t -= arb(e[j]) / 4
            A.append(t)
        while len(A) > 1 and A[-1].is_zero():
            A.pop()
        out[name] = A
    return d, out


def gram(d, A, prec, names=NAMES):
    """H_ij = <h_i,h_j> = 2 delta sum_{k,l} A_k^i A_l^j/(2(k+l)+1). Exact rational in delta."""
    ctx.prec = prec
    n = len(names)
    Hm = [[arb(0)] * n for _ in range(n)]
    for i, ni in enumerate(names):
        for j, nj in enumerate(names):
            s = arb(0)
            for k, ak in enumerate(A[ni]):
                for l, al in enumerate(A[nj]):
                    s += ak * al / (2 * (k + l) + 1)
            Hm[i][j] = 2 * d * s
    return Hm


def hhat_vec(xi, d, A, prec, names=NAMES):
    """[hhat_i(xi)] as acb, sharing one cos-moment cache. hhat = 2 delta sum_j A_j C_j."""
    ctx.prec = prec
    c = acb(d) * xi
    C = [h4arb.C_pow_cos(2 * j, c, prec) for j in range(JMAX + 1)]
    out = []
    for name in names:
        s = acb(0)
        for j, aj in enumerate(A[name]):
            s += acb(aj) * C[j]
        out.append(2 * acb(d) * s)
    return out


def _fall(n, t):
    """n!/(n-t)! for n >= t, else 0."""
    if n < t:
        return 0
    r = 1
    for i in range(t):
        r *= (n - i)
    return r


def tails(d, A, prec, names=NAMES):
    """{name: (m, P, C_a, C_b)} with |hhat| <= C_a/|xi|^P + C_b/|xi|^{P+1}, P = m+1."""
    ctx.prec = prec
    out = {}
    for name in names:
        a = A[name]
        m = ORDER[name] - 2
        pm = arb(0); pm1 = arb(0); l1 = arb(0)
        for j, aj in enumerate(a):
            n = 2 * j
            pm += aj * _fall(n, m)
            pm1 += aj * _fall(n, m + 1)
            f = _fall(n, m + 2)
            if f:
                l1 += aj.abs_upper() * f * 2 / arb(n - (m + 2) + 1)
        Ca = 2 * pm.abs_upper() / d ** m
        Cb = (2 * pm1.abs_upper() + l1) / d ** (m + 1)
        out[name] = (m, m + 1, Ca, Cb)
    return out


def l1_bounds(d, Hm, prec):
    """||h_i||_1 <= sqrt(2 delta H_ii) (Cauchy-Schwarz on the support)."""
    ctx.prec = prec
    return [(2 * d * Hm[i][i]).sqrt() for i in range(len(Hm))]


def exact_vanishing_check():
    """p^{(t)}(1) = 0 for t < m as EXACT integer/rational identities in u = delta^{-2}.
    Returns {name: (m, [max |numerator| over t < m])}; all must be 0."""
    from fractions import Fraction
    res = {}
    for name, e in _etas().items():
        mdeg = len(e) - 1
        # A_j = u * e_{j+1}(2j+2)(2j+1) - e_j/4  ->  (coef of u, constant), exact rationals
        A = []
        for j in range(mdeg + 1):
            cu = Fraction(e[j + 1] * (2 * j + 2) * (2 * j + 1)) if j + 1 <= mdeg else Fraction(0)
            A.append((cu, -Fraction(e[j], 4)))
        m = ORDER[name] - 2
        bad = []
        for t in range(m):
            su = sum(A[j][0] * _fall(2 * j, t) for j in range(len(A)))
            sc = sum(A[j][1] * _fall(2 * j, t) for j in range(len(A)))
            bad.append((t, su, sc))
        res[name] = (m, bad)
    return res


if __name__ == '__main__':
    P = 400
    ctx.prec = P
    d, A = profiles(P)
    Hm = gram(d, A, P)
    T = tails(d, A, P)
    L1 = l1_bounds(d, Hm, P)
    print("delta =", d.str(20))
    for n in NAMES:
        m, PP, Ca, Cb = T[n]
        print(f"\n[{n}] deg_z={2*(len(A[n])-1)}  k={ORDER[n]}  m={m}  "
              f"|hhat| <= Ca/|xi|^{PP} + Cb/|xi|^{PP+1}")
        print("   A =", [a.str(15) for a in A[n]])
        print(f"   C_a = {Ca.str(12)}   C_b = {Cb.str(12)}")
    print("\nGram H (exact rational in delta):")
    for i, ni in enumerate(NAMES):
        print("   " + ni.rjust(4) + " " + "  ".join(Hm[i][j].str(15) for j in range(len(NAMES))))
    print("\n||h||_1 <= sqrt(2 delta H_ii):", [x.str(10) for x in L1])
    print("\nEXACT vanishing p^{(t)}(1) = 0 for t < m (rational in u = delta^-2):")
    for n, (m, bad) in exact_vanishing_check().items():
        ok = all(su == 0 and sc == 0 for _, su, sc in bad)
        print(f"   {n:4s} m={m}  all t<m give 0 : {ok}   {[(t,str(su),str(sc)) for t,su,sc in bad]}")
    print("\nEXACT rank identity h5 = h4 - h4z (coefficientwise, rational in u):")
    from fractions import Fraction
    E = _etas()
    def coefs(name):
        e = E[name]; mdeg = len(e) - 1
        return [((Fraction(e[j+1]*(2*j+2)*(2*j+1)) if j+1 <= mdeg else Fraction(0)),
                 -Fraction(e[j], 4)) for j in range(mdeg + 1)]
    c4, c5, c4z = coefs("h4"), coefs("h5"), coefs("h4z")
    L = max(len(c4), len(c5), len(c4z))
    def get(c, j): return c[j] if j < len(c) else (Fraction(0), Fraction(0))
    diff = [(get(c5,j)[0] - get(c4,j)[0] + get(c4z,j)[0],
             get(c5,j)[1] - get(c4,j)[1] + get(c4z,j)[1]) for j in range(L)]
    print("   h5 - h4 + h4z  =", diff, " -> zero:", all(a == 0 and b == 0 for a, b in diff))
    print("\npole moments int h e^{+-x/2} dx (arb):")
    for n in NAMES:
        for sg in (1, -1):
            tot = arb(0)
            for j, aj in enumerate(A[n]):
                s = arb(0); t = arb(1); k = 0
                while True:
                    if k % 2 == 0:
                        s += t / (2 * j + k + 1)
                    k += 1
                    t = t * (arb(sg) * d / 2) / k
                    if t.abs_upper() < arb(2) ** (-P + 20) and k > 20:
                        break
                tot += aj * 2 * d * s
            print(f"   {n:4s} sign {sg:+d}: {tot.str(8)}")
