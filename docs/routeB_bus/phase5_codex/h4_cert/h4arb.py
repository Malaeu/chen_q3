"""Rigorous (arb/acb ball) evaluator for the SCALARFLOOR h4 certificate.

Conventions (all pinned to the verdicts, see the report):
  a = log 2, r = 2^{-1/2}, delta = (log3-log2)/8.
  hhat(xi)   = int h(x) e^{-i xi x} dx            [SCALARFLOOR (1)]
  H          = ||h||_2^2
  W_h(xi)    = (1 - cos(a xi)) |hhat|^2 / H       [SCALARFLOOR (1)]
  gamma_2    = pi^{-i xi} G(1/4+i xi/2)/G(1/4-i xi/2) * b(-xi)/b(xi),  b(xi)=1-r e^{-i a xi}
                                                   [RESONANCE (2)]
  J(beta,eta)= int_0^1 (-log v) v^{-1/2+i eta} cos(beta v) dv   [RESONANCE 2.2]
  t_2(xi)    = (1/2pi)[ sum_{j>=0} J(2pi 2^j, -xi) - J(pi, -xi) ] [RESONANCE (10), p=2]
  ell_2      = 2 Re(gamma_2 t_2)                   [SCALARFLOOR (3)]
  F(h)       = - int W_h ell_2 dxi                 [SCALARFLOOR (3)]

NOTHING here is converted to a Python float on the certificate path.
"""
from flint import arb, acb, ctx


# ------------------------------------------------------------------ profile h4
def profile(prec):
    """(delta, A[0..4], H4) as arb balls at the given precision."""
    ctx.prec = prec
    d = (arb(3).log() - arb(2).log()) / 8
    di2 = 1 / (d * d)
    A = [-8 * di2 - arb(1) / 4,
         72 * di2 + 1,
         -120 * di2 - arb(3) / 2,
         56 * di2 + 1,
         -arb(1) / 4]
    H = arb(0)
    for i in range(5):
        for j in range(5):
            H += A[i] * A[j] / (2 * (i + j) + 1)
    H *= 2 * d
    return d, A, H


def C_pow_cos(m, c, prec):
    """int_0^1 z^m cos(c z) dz, entire power series in c (acb c)."""
    ctx.prec = prec
    tot = acb(0)
    t = acb(1)
    n = 0
    c2 = c * c
    thresh = arb(2) ** (-prec - 10)
    while True:
        tot += t / (m + 2 * n + 1)
        n += 1
        t = -t * c2 / ((2 * n) * (2 * n - 1))
        if n > 4 and t.abs_upper() < thresh and 2 * n > c.abs_upper() + 4:
            break
        if n > 20000:
            raise RuntimeError("C_pow_cos did not terminate")
    e = 2 * t.abs_upper() / (m + 2 * n + 1)      # |tail| <= 2|first omitted|, q < 1/2
    return tot + acb(arb(0, e), arb(0, e))


def hhat(xi, d, A, prec):
    """hhat(xi) = 2 delta sum_j A_j * int_0^1 z^{2j} cos(delta xi z) dz.  acb, entire."""
    ctx.prec = prec
    c = acb(d) * xi
    s = acb(0)
    for j in range(5):
        s += acb(A[j]) * C_pow_cos(2 * j, c, prec)
    return 2 * acb(d) * s


# ------------------------------------------------------------------ gamma_2
def gamma2(xi, prec):
    """RESONANCE (2) for S = {inf, 2}. acb; |gamma_2| = 1 for real xi."""
    ctx.prec = prec
    a = arb(2).log()
    r = 1 / arb(2).sqrt()
    i = acb(0, 1)
    lg = (acb(arb(1) / 4) + i * xi / 2).lgamma() - (acb(arb(1) / 4) - i * xi / 2).lgamma()
    g = (-i * xi * acb.pi().log() + lg).exp()
    b_m = 1 - acb(r) * (i * acb(a) * xi).exp()      # b(-xi) = 1 - r e^{+i a xi}
    b_p = 1 - acb(r) * (-i * acb(a) * xi).exp()     # b(xi)  = 1 - r e^{-i a xi}
    return g * b_m / b_p


# ------------------------------------------------------------------ J: series
def J_series(beta, s, prec):
    """J = sum_n (-1)^n beta^{2n} / ((2n)! (s+2n)^2), s = 1/2 - i xi (acb).
    beta an exact arb/int. Rigorous: alternating tail once 2n > beta."""
    ctx.prec = prec
    b2 = arb(beta) ** 2
    bub = arb(beta).abs_upper()
    term = arb(1)
    tot = acb(0)
    n = 0
    thresh = arb(2) ** (-prec + 10)
    while True:
        d = s + 2 * n
        tot += acb(term) / (d * d)
        n += 1
        term = -term * b2 / ((2 * n) * (2 * n - 1))
        if 2 * n > bub + 4 and term.abs_upper() < thresh:
            break
        if n > 2000000:
            raise RuntimeError("J_series did not terminate")
    # alternating-with-decreasing-terms remainder: |tail| <= |first omitted term|
    d = s + 2 * n
    rem = 2 * (acb(term) / (d * d)).abs_upper()   # geometric with ratio < 1/2 at this n
    return tot + acb(arb(0, rem), arb(0, rem))


# ------------------------------------------------------------------ J: large beta
def PQ(s, k, prec):
    """P_m = prod_{i<m}(s-1-i), Q_{m+1} = (s-1-m) Q_m + P_m, Q_0 = 0. Lists 0..k."""
    ctx.prec = prec
    P = [acb(1)]
    Q = [acb(0)]
    for m in range(k):
        f = s - 1 - m
        P.append(P[m] * f)
        Q.append(f * Q[m] + P[m])
    return P, Q


def gk_pieces(s, prec):
    """G = Gamma(s) cos(pi s/2),  K = Gamma(s)[-psi(s) cos(pi s/2) + (pi/2) sin(pi s/2)].
    J_main(beta) = beta^{-s} (G log beta + K)."""
    ctx.prec = prec
    g = s.gamma()
    cs = (s / 2).cos_pi()
    sn = (s / 2).sin_pi()
    G = g * cs
    K = g * (-s.digamma() * cs + acb.pi() / 2 * sn)
    return G, K


def J_asym(beta, s, G, K, P, Q, k, prec):
    """J(beta, .) = beta^{-s}(G log beta + K) + R,
       R = - sum_{m=2..k} (-1)^{m-1} Q_{m-1} beta^{-m} T_m + E_k,
       T_m = sin(beta - (m-1) pi/2),
       |E_k| <= beta^{-k} [ |P_k|/(k-1/2)^2 + |Q_k|/(k-1/2) ].
    Returns (value, err_upper) or (None, None) if the remainder is not small."""
    ctx.prec = prec
    B = arb(beta)
    lb = B.log()
    val = (-s * lb).exp() * (G * lb + K)
    ib = 1 / B
    bm = ib                                   # beta^{-m}, m = 1
    sb = B.sin()
    cb = B.cos()
    T = [None, sb, -cb, -sb, cb]              # T_m, period 4
    acc = acb(0)
    for m in range(1, k + 1):
        if m >= 2:
            sgn = -1 if (m - 1) % 2 == 0 else 1     # -(-1)^{m-1}
            acc += sgn * Q[m - 1] * bm * T[(m - 1) % 4 + 1]
        bm = bm * ib
    kk = arb(k) - arb(1) / 2
    Ek = (B ** (-k)) * (P[k].abs_upper() / (kk * kk) + Q[k].abs_upper() / kk)
    return val + acc + acb(arb(0, Ek), arb(0, Ek)), Ek


def gamma2_abs_ub(ball, R, prec):
    """Rigorous upper bound for |gamma_2(xi)| over the acb ball `ball`
    (|Im xi| <= R). Uses the entire reciprocal gamma, so no branch/zero issue."""
    ctx.prec = prec
    a = arb(2).log()
    r = 1 / arb(2).sqrt()
    i = acb(0, 1)
    z1 = acb(arb(1) / 4) + i * ball / 2
    z2 = acb(arb(1) / 4) - i * ball / 2
    # shift by 3 so that acb_gamma/acb_rgamma are evaluated well inside Re > 0
    num = z1.gamma()
    den = z2.rgamma()
    if not (num.is_finite() and den.is_finite()):
        num = (z1 + 3).gamma()
        for t in range(3):
            num = num / (z1 + t).abs_lower()
        den = (z2 + 3).rgamma()
        for t in range(3):
            den = den * (z2 + t).abs_upper()
    g = (arb.pi() ** R) * num.abs_upper() * den.abs_upper()
    q = r * (a * R).exp()
    return g * (1 + q) / (1 - q)
