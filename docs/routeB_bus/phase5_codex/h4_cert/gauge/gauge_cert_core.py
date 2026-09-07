"""Ball-arithmetic core for the pole-gauged positive-extension certificate (20).

R(t) = K_T(t) - c S(t)  on |t| <= d0, via the exact regrouping (7) of
PROSHKA_VERDICT_GOAL058_SIGNED_SCHUR_COMPLEMENT_2026-09-07:

    R(t) = (c/2) Q(t) - (sqrt2/4) G(t) - 2 pi Ntilde(t)
    Q(t) = sum_{j>=0} [ q_{b_j}(t) + q_{b_j}(-t) ],  q_b(t) = e^{t/2} L(b(e^t-1)) - L(b t)
    G(t) = e^{t/2} L(2pi(1-e^t)) + e^{-t/2} L(2pi(1-e^{-t}))
    Ntilde(t) = N_0(t) - (1/2) N_+(t) - (1/2) N_-(t)

with N_s the double series (5) at argument u = t+s, s in {0,+a,-a}, with the exactly
resonant difference terms (i,j>=0, i-j = +-s/a) removed.

Every quantity is an arb ball.  Truncation tails are added as explicit radii.
No float ever touches the certificate path.
"""
from flint import arb, ctx

# ---------------------------------------------------------------- constants
def setup(prec=300):
    ctx.prec = prec

def K():
    a  = arb(2).log()
    d0 = a/4
    dl = (arb(3).log() - a)/8
    c  = (a/2).cosh() - 1
    pi = arb.pi()
    r2 = arb(2).sqrt()
    kap= ((-d0).exp() - arb(1)/2)/2          # (e^{-d0}-1/2)/2 = e^{-a-d0}(1-e^{d0}/2)
    E  = ((a+d0)/2).exp()
    Bx = (a+d0).exp()
    return dict(a=a, d0=d0, delta=dl, c=c, pi=pi, r2=r2, kappa=kap, E=E, Bx=Bx,
                cstar=2*pi*c*a)

# --------------------------------------------------------- L(z)=Si(z)/z, L'
_NSER = 70
def _Lseries(z):
    """L and L' by the entire series; used only for |z| <= 4 (wider balls lose to dependency)."""
    z2 = z*z
    L  = arb(0); Lp = arb(0); term = arb(1)          # term = (-1)^n z^{2n}/((2n)! (2n+1)^2) * ((2n)!(2n+1)^2)
    num = arb(1)
    for n in range(_NSER):
        den = arb(1)
        # coefficient 1/((2n)! (2n+1)^2)
        f = arb(1)
        for k in range(1, 2*n+1):
            f = f*k
        coef = arb(1)/(f*arb(2*n+1)**2)
        t = coef*(z2**n)
        if n % 2: t = -t
        L = L + t
        if n >= 1:
            tp = coef*arb(2*n)*(z**(2*n-1))
            if n % 2: tp = -tp
            Lp = Lp + tp
    # tail: |term_n| decreasing geometrically once (2n+1)(2n+2) > |z|^2 ; with N=70, |z|<=12 it is < 2^-1000
    e = arb(0, arb(2)**-900)
    return L+e, Lp+e

_ZBIG = arb(10)**8
def Lpair(z):
    """(L(z), L'(z)) enclosures for an arb ball z."""
    lo = z.abs_lower(); hi = z.abs_upper()
    if hi <= 4:
        return _Lseries(z)
    if lo >= _ZBIG:
        return arb(0, (arb(4)/lo).upper()), arb(0, (arb(5)/(lo*lo)).upper())
    if lo >= arb(2)/5:
        s = z.si()
        return s/z, (z.sin()-s)/(z*z)
    # never expected with a graded grid; valid but crude
    Lpair.fallback += 1
    return arb(0, 1), arb(0, arb('0.396'))
Lpair.fallback = 0

# ------------------------------------------------------------- Q, G, Ntilde
def _qpair(beta, t):
    """(q_beta(t), q'_beta(t)) for an arb ball t."""
    et = t.exp()
    A  = beta*(et-1)
    LA, LpA = Lpair(A)
    Bt = beta*t
    LB, LpB = Lpair(Bt)
    e2 = (t/2).exp()
    q  = e2*LA - LB
    qp = e2*LA/2 + e2*LpA*beta*et - beta*LpB
    return q, qp

def QQ(t, Jq, tlo, KK):
    """(Q(t), Q'(t)) with rigorous truncation tail.  tlo>0 = lower bound of |t| on the cell."""
    pi = KK['pi']
    S = arb(0); Sp = arb(0)
    for j in range(Jq+1):
        b = 2*pi*arb(2)**j
        qp_, qpp_ = _qpair(b, t)
        qm_, qmp_ = _qpair(b, -t)
        S  = S  + qp_ + qm_
        Sp = Sp + qpp_ - qmp_
    # tails:  |q_b| <= 6/b ;  |q'_b(t)-q'_b(-t)| <= 4.76/(b|t|) + 25.4/(b t^2)
    g = arb(2)**(-Jq)/(2*pi)                      # sum_{j>Jq} 1/beta_j
    S  = S  + arb(0, (12*g).upper())
    Sp = Sp + arb(0, (g*(arb('4.76')/tlo + arb('25.4')/(tlo*tlo))).upper())
    return S, Sp

def GG(t, KK):
    pi = KK['pi']
    e  = (t/2).exp(); em = (-t/2).exp()
    A  = 2*pi*(1-t.exp());  C = 2*pi*(1-(-t).exp())
    LA, LpA = Lpair(A); LC, LpC = Lpair(C)
    G  = e*LA + em*LC
    Gp = e*LA/2 + e*LpA*(-2*pi*t.exp()) - em*LC/2 + em*LpC*(2*pi*(-t).exp())
    return G, Gp

def NT(t, JN, KK):
    """(Ntilde(t), Ntilde'(t)) with rigorous nonresonant tail."""
    pi = KK['pi']; a = KK['a']
    bet = [2*pi*arb(2)**m for m in range(-1, JN+1)]
    cs  = [arb(-1)/2] + [arb(1)/2]*(JN+1)
    tot = arb(0); totp = arb(0)
    for s, w, k1 in ((arb(0), arb(1), 0), (a, arb(-1)/2, 1), (-a, arb(-1)/2, -1)):
        u  = t + s
        eu = u.exp(); em = (-u).exp()
        e2 = (u/2).exp(); e2m = (-u/2).exp()
        acc = arb(0); accp = arb(0)
        for ii in range(-1, JN+1):
            bi = bet[ii+1]; ci = cs[ii+1]
            for jj in range(-1, JN+1):
                bj = bet[jj+1]; cij = ci*cs[jj+1]
                res1 = (ii >= 0 and jj >= 0 and ii-jj == k1)
                res2 = (ii >= 0 and jj >= 0 and ii-jj == -k1)
                A = bi - bj*eu;  B = bi + bj*eu
                C = bi - bj*em;  D = bi + bj*em
                if res1: LA = arb(0); LpA = arb(0)
                else:    LA, LpA = Lpair(A)
                LB, LpB = Lpair(B)
                if res2: LC = arb(0); LpC = arb(0)
                else:    LC, LpC = Lpair(C)
                LD, LpD = Lpair(D)
                v  = e2*(LA+LB) + e2m*(LC+LD)
                vp = (e2*(LA+LB)/2 + e2*(LpA*(-bj*eu) + LpB*(bj*eu))
                      - e2m*(LC+LD)/2 + e2m*(LpC*(bj*em) + LpD*(-bj*em)))
                acc  = acc  + cij*v
                accp = accp + cij*vp
        tot  = tot  + w*acc/pi
        totp = totp + w*accp/pi
    # nonresonant tail over max index n > JN:  (2n+3) pairs, per-pair bounds
    tl  = arb('1.834')*(2*JN+7)*arb(2)**(-JN)     # value
    tlp = arb('32.90')*(2*JN+7)*arb(2)**(-JN)     # derivative
    tot  = tot  + arb(0, (2*tl).upper())
    totp = totp + arb(0, (2*tlp).upper())
    return tot, totp

def R_and_Rp(t, tlo, Jq, JN, KK):
    c = KK['c']; r2 = KK['r2']; pi = KK['pi']
    Q, Qp = QQ(t, Jq, tlo, KK)
    G, Gp = GG(t, KK)
    N, Np = NT(t, JN, KK)
    R  = c/2*Q  - r2/4*G  - 2*pi*N
    Rp = c/2*Qp - r2/4*Gp - 2*pi*Np
    return R, Rp
