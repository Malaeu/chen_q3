"""Rigorous budget terms of (38): Euler-tail eps_J, uniform |t_2| bound, frequency tail mu_X."""
import sys
from flint import arb, acb, ctx
import h4arb

PREC = 400


def eps_J(J, prec=PREC):
    """SCALARFLOOR (32) with the proved uniform constant C = 256 of Theorem 4 (31):
       |t_2 - t_2^{[J]}| <= eps_J,  uniformly in real xi."""
    ctx.prec = prec
    r = 1 / arb(2).sqrt()
    a = arb(2).log()
    bJ1 = 2 * arb.pi() * arb(2) ** (J + 1)
    return (128 / (arb.pi() * (2 * arb.pi()).sqrt())) * r ** (J + 1) * (
        (1 + bJ1.log()) / (1 - r) + a * r / (1 - r) ** 2)


def Tstar(N=40, prec=PREC):
    """Uniform bound |t_2(xi)| <= Tstar for all real xi, from
         |J(beta,.)| <= min( 4 , 256 beta^{-1/2}(1+log beta) ),
       the first factor elementary (int_0^1 (-log v) v^{-1/2} dv = 4),
       the second SCALARFLOOR Theorem 4 (31).  Terms j = -1 (beta=pi) and j = 0..inf."""
    ctx.prec = prec
    r = 1 / arb(2).sqrt()
    a = arb(2).log()
    tot = arb(4)                                   # j = -1, beta = pi
    for j in range(N + 1):
        b = 2 * arb.pi() * arb(2) ** j
        cand = 256 * b.rsqrt() * (1 + b.log())
        tot += cand if cand < arb(4) else arb(4)
    bN1 = 2 * arb.pi() * arb(2) ** (N + 1)
    tail = (256 / (2 * arb.pi()).sqrt()) * r ** (N + 1) * (
        (1 + bN1.log()) / (1 - r) + a * r / (1 - r) ** 2)
    return (tot + tail) / (2 * arb.pi())


def transform_tail(prec=PREC):
    """B3 = 2|h''(delta)|, B4 = 2|h'''(delta)| + ||h''''||_{L1(-d,d)}, so that
         |hhat(xi)| <= B3/|xi|^3 + B4/xi^4     (two/three integrations by parts)."""
    ctx.prec = prec
    d, A, H = h4arb.profile(prec)
    p2 = sum(A[j] * (2 * j) * (2 * j - 1) for j in range(1, 5))            # p''(1)
    p3 = sum(A[j] * (2 * j) * (2 * j - 1) * (2 * j - 2) for j in range(2, 5))   # p'''(1)
    B3 = 2 * (p2 / (d * d)).abs_upper()
    B4a = 2 * (p3 / d ** 3).abs_upper()
    # ||h''''||_1 <= (2/delta^3) * sum_{j>=2} |A_j| (2j)(2j-1)(2j-2)
    s4 = arb(0)
    for j in range(2, 5):
        s4 += A[j].abs_upper() * (2 * j) * (2 * j - 1) * (2 * j - 2)
    B4 = B4a + 2 * s4 / d ** 3
    return d, H, B3, B4


def mu_X(X, prec=PREC):
    """mu_X = int_{|xi|>X} W_h <= (4/H)[B3^2/(5X^5) + 2 B3 B4/(6 X^6) + B4^2/(7 X^7)]."""
    ctx.prec = prec
    d, H, B3, B4 = transform_tail(prec)
    Xa = arb(X)
    return (4 / H) * (B3 ** 2 / (5 * Xa ** 5) + 2 * B3 * B4 / (6 * Xa ** 6)
                      + B4 ** 2 / (7 * Xa ** 7))


if __name__ == '__main__':
    ctx.prec = PREC
    d, H, B3, B4 = transform_tail()
    print("delta        =", d.str(20))
    print("H_4          =", H.str(20))
    print("B3           =", B3.str(12))
    print("B4           =", B4.str(12))
    T = Tstar()
    print("Tstar (|t_2|)=", T.str(12), "   -> |ell_2| <= 2 Tstar =", (2 * T).str(12))
    for J in (55, 70, 90):
        e = eps_J(J)
        print(f"eps_J(J={J:3d}) = {e.str(8)}   4 pi eps = {(4*arb.pi()*e).str(8)}")
    for X in (600, 1000, 1500, 2000, 2500, 3000):
        m = mu_X(X)
        print(f"X={X:5d}  mu_X <= {m.str(8)}   2 Tstar mu_X <= {(2*T*m).str(8)}")
