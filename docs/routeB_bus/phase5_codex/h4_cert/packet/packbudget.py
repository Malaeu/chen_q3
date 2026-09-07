"""Rigorous per-entry budget rows for the packet floor matrix.

Per entry (i,j) of the UNNORMALIZED F_ij = -int w_a hhat_i hhat_j ell_2 (w_a = 1 - cos a xi):

 (1) Euler-sum truncation.  |ell_2 - ell_2^{[J0]}| <= 2|t_2 - t_2^{[J0]}| <= 2 eps_{J0}
     (|gamma_2| = 1 on R), so by Cauchy-Schwarz
        |R_euler^{ij}| <= 2 eps_{J0} int w_a |hhat_i||hhat_j|
                       <= 2 eps_{J0} (int w_a|hhat_i|^2)^{1/2}(int w_a|hhat_j|^2)^{1/2}
                        = 2 eps_{J0} * 2 pi sqrt(H_i H_j) = 4 pi eps_{J0} sqrt(H_i H_j).
     Here int w_a |hhat|^2 = 2 pi H exactly: Parseval gives int|hhat|^2 = 2 pi H, and
     int cos(a xi)|hhat|^2 = 2 pi (h*h~)(a) = 0 because the autocorrelation of h is supported
     in [-2delta, 2delta] and 2 delta < a = log 2.  For i = j this is the h4 report's 4 pi eps_J.

 (2) Frequency tail.  |ell_2| <= 2T (T = Tstar, uniform) and w_a <= 2, so with
     |hhat_i| <= Ca_i/|xi|^{P_i} + Cb_i/|xi|^{P_i+1} (packarb.tails),
        |R_freq^{ij}| <= 2T * 2 * 2 int_X^inf (Ca_i/xi^{P_i}+Cb_i/xi^{P_i+1})
                                             (Ca_j/xi^{P_j}+Cb_j/xi^{P_j+1}) dxi
                       =: 2T nu_X^{ij},
     nu_X^{ij} = 4 sum over the four products c*c'/((P+P'-1) X^{P+P'-1}).
     For i = j = h4 this is exactly H_4 * mu_X of the h4 report.

 (3) Quadrature.  Bernstein-ellipse (Trefethen ATAP Thm 8.2), the panel-sum base is computed
     in packcert.py; E_quad^{ij} = L1_i L1_j * BASE, L1_i = ||h_i||_1 <= sqrt(2 delta H_ii).

eps_J and Tstar are imported unchanged from the h4 certificate (budget.py).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from flint import arb, ctx
import budget                       # eps_J (v1 (32), C = 256), Tstar (uniform |t_2|)
import packarb

PREC = 400
eps_J = budget.eps_J
Tstar = budget.Tstar


def nu_matrix(X, T, prec=PREC, names=packarb.NAMES):
    """nu_X^{ij} (arb upper bounds), the UNNORMALIZED frequency-tail integral bound."""
    ctx.prec = prec
    d, A = packarb.profiles(prec)
    TL = packarb.tails(d, A, prec, names)
    Xa = arb(X)
    n = len(names)
    nu = [[arb(0)] * n for _ in range(n)]
    for i, ni in enumerate(names):
        mi, Pi, Cai, Cbi = TL[ni]
        for j, nj in enumerate(names):
            mj, Pj, Caj, Cbj = TL[nj]
            s = arb(0)
            for (ci, pi_) in ((Cai, Pi), (Cbi, Pi + 1)):
                for (cj, pj_) in ((Caj, Pj), (Cbj, Pj + 1)):
                    r = pi_ + pj_
                    s += ci * cj / ((r - 1) * Xa ** (r - 1))
            nu[i][j] = 4 * s
    return nu


if __name__ == '__main__':
    ctx.prec = PREC
    names = packarb.NAMES
    d, A = packarb.profiles(PREC)
    Hm = packarb.gram(d, A, PREC, names)
    T = Tstar()
    print("Tstar =", T.str(12), "   |ell_2| <= 2 Tstar =", (2 * T).str(12))
    for J in (70, 90, 110):
        e = eps_J(J)
        print(f"eps_J({J}) = {e.str(8)}   4 pi eps = {(4*arb.pi()*e).str(8)}"
              f"   (normalized Euler row, all entries)")
    print("\nnormalized frequency-tail rows  2 T nu^{ij} / sqrt(H_ii H_jj):")
    for X in (2000, 3000, 4000, 5000, 6000):
        nu = nu_matrix(X, T)
        worst = arb(0); wij = None
        for i in range(len(names)):
            for j in range(len(names)):
                v = 2 * T * nu[i][j] / (Hm[i][i] * Hm[j][j]).sqrt()
                if v > worst:
                    worst = v; wij = (names[i], names[j])
        print(f"  X={X:5d}  worst = {worst.str(6)}  at {wij}")
    X = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    nu = nu_matrix(X, T)
    print(f"\nfull normalized tail matrix at X={X}:")
    print("        " + "".join(n.rjust(12) for n in names))
    for i, ni in enumerate(names):
        row = "".join((2 * T * nu[i][j] / (Hm[i][i] * Hm[j][j]).sqrt()).abs_upper().str(4).rjust(12)
                      for j in range(len(names)))
        print(f"  {ni:5s}" + row)
