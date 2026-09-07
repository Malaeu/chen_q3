"""Rigorous per-entry budget rows for the Legendre packet floor matrix.

Per entry (i,j) of the UNNORMALIZED F_ij = -int w_a conj(hhat_i) hhat_j ell_2,
w_a = 1 - cos(a xi):

 (1) Euler-sum truncation.  |ell_2 - ell_2^{[J0]}| <= 2 eps_{J0} uniformly on R
     (|gamma_2| = 1 there; CLASSFLOOR (12) with the constant C = 256 KEPT -- the
     newly proved 120 is not used, see the report), so by Cauchy-Schwarz
        |R_euler^{ij}| <= 2 eps_{J0} int w_a |hhat_i||hhat_j|
                       <= 4 pi eps_{J0} sqrt(H_ii H_jj),
     using int w_a |hhat|^2 = 2 pi H exactly (Parseval, plus the autocorrelation of h
     living in [-2delta,2delta] with 2delta = 0.1014 < a = log 2, so the cos term drops).
     This holds for every test, either parity.

 (2) Frequency tail, analytic branch.  |ell_2| <= 2 T0 and w_a <= 2, so with
     |hhat_i| <= Ca_i/|xi|^3 + Cb_i/|xi|^4 (legarb.tails, m = 2 for every test),
        |R_freq^{ij}| <= 2 T0 nu_X^{ij},
        nu_X^{ij} = 4 sum_{(c,p),(c',p')} c c' / ((p+p'-1) X^{p+p'-1}).

 (3) Frequency tail, mass-deficit branch (verdict (6)).
        |R_freq^{ij}| <= 2 T0 sqrt(D_i D_j),
        D_i = 2 pi H_ii - int_{|xi|<=X} w_a |hhat_i|^2,
     the compact mass computed on the same nodes with its own Bernstein enclosure.
     The ledger takes the minimum of (2) and (3) per entry.

 (4) Quadrature.  Bernstein ellipse (ATAP Thm 8.2), E_quad^{ij} = L1_i L1_j * Ebase,
     L1_i = ||h_i||_1 <= sqrt(2 delta H_ii); Ebase from legequad.py.

eps_J and Tstar are imported unchanged from the ratified h4 certificate (budget.py).
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, ctx
import budget                       # eps_J (C = 256), Tstar (uniform |t_2|)
import legarb

PREC = 400
eps_J = budget.eps_J
Tstar = budget.Tstar


def nu_matrix(X, T, prec=PREC, idx=range(8)):
    """nu_X^{ij} (arb upper bounds), UNNORMALIZED frequency-tail integral bound."""
    ctx.prec = prec
    idx = list(idx)
    d, A = legarb.profiles(prec)
    TL = legarb.tails(d, A, prec, idx)
    Xa = arb(X)
    n = len(idx)
    nu = [[arb(0)] * n for _ in range(n)]
    for ii, i in enumerate(idx):
        mi, Pi, Cai, Cbi = TL[i]
        for jj, j in enumerate(idx):
            mj, Pj, Caj, Cbj = TL[j]
            s = arb(0)
            for (ci, pi_) in ((Cai, Pi), (Cbi, Pi + 1)):
                for (cj, pj_) in ((Caj, Pj), (Cbj, Pj + 1)):
                    r = pi_ + pj_
                    s += ci * cj / ((r - 1) * Xa ** (r - 1))
            nu[ii][jj] = 4 * s
    return nu


if __name__ == '__main__':
    ctx.prec = PREC
    d, A = legarb.profiles(PREC)
    Hm = legarb.gram(d, A, PREC)
    T = Tstar()
    print("Tstar =", T.str(12), "   |ell_2| <= 2 Tstar =", (2 * T).str(12))
    for J in (70, 90, 110):
        e = eps_J(J)
        print(f"eps_J({J}) = {e.str(8)}   4 pi eps = {(4*arb.pi()*e).str(8)}"
              f"   (normalized Euler row, every entry)")
    print("\nnormalized analytic frequency-tail rows  2 T nu^{ij} / sqrt(H_ii H_jj):")
    for X in (2000, 3000, 4000, 5000, 6000, 8000):
        nu = nu_matrix(X, T)
        worst = arb(0); wij = None
        for i in range(8):
            for j in range(8):
                v = 2 * T * nu[i][j] / (Hm[i][i] * Hm[j][j]).sqrt()
                if v > worst:
                    worst = v; wij = (legarb.NAMES[i], legarb.NAMES[j])
        print(f"  X={X:5d}  worst = {worst.str(6)}  at {wij}")
    X = float(sys.argv[1]) if len(sys.argv) > 1 else 4000.0
    nu = nu_matrix(X, T)
    print(f"\nUNNORMALIZED 2 T nu^{{ij}} at X={X} (the analytic E_freq branch):")
    print("       " + "".join(n.rjust(12) for n in legarb.NAMES))
    for i in range(8):
        print(f"  {legarb.NAMES[i]:4s}" + "".join(
            (2 * T * nu[i][j]).abs_upper().str(4).rjust(12) for j in range(8)))
