"""Node evaluator: rigorous acb enclosure of the floor integrand.

  f(xi) = - (1 - cos(a xi)) hhat(xi)^2 / H * ell_2^{[J0]}(xi)
  F(h)  = int_R f  = 2 int_0^inf f      (f even)
"""
import math
from flint import arb, acb, ctx
import h4arb

J0 = 90                  # Euler cutoff: t_2^{[J0]} keeps j = -1, 0..J0
KLIST = (16, 32, 64, 96, 128, 160)
ASYM_TOL = 1e-28


class Ctx:
    """Precomputed profile constants at a fixed high precision."""
    def __init__(self, prec=400):
        self.prec = prec
        ctx.prec = prec
        self.d, self.A, self.H = h4arb.profile(prec)
        self.a = arb(2).log()
        self.r = 1 / arb(2).sqrt()
        self.pi = arb.pi()
        self.betas = [self.pi] + [2 * self.pi * arb(2) ** j for j in range(J0 + 1)]
        self.bfloat = [float(b.str(20, radius=False)) for b in self.betas]

    @staticmethod
    def beta_at(idx, prec):
        """beta_{idx-1} recomputed at `prec` bits (needed: beta^{2n} amplifies its radius by 2n)."""
        ctx.prec = prec
        return arb.pi() if idx == 0 else 2 * arb.pi() * arb(2) ** (idx - 1)


def t2_and_gamma(xi, C, prec):
    """t_2^{[J0]}(xi) and gamma_2(xi) as acb, xi a thin arb."""
    ctx.prec = prec
    s = acb(arb(1) / 2) - acb(0, 1) * acb(xi)
    smod = float(s.abs_upper().str(20, radius=False))
    G, K = h4arb.gk_pieces(s, prec)
    P, Q = h4arb.PQ(s, max(KLIST), prec)
    tot = acb(0)
    n_series = 0
    for idx, B in enumerate(C.betas):
        bf = C.bfloat[idx]
        val = None
        if bf > 1.7 * smod:
            best = None
            for k in KLIST:
                v, E = h4arb.J_asym(B, s, G, K, P, Q, k, prec)
                Ef = float(E.str(10, radius=False))
                if best is None or Ef < best[1]:
                    best = (v, Ef)
            if best[1] <= ASYM_TOL:
                val = best[0]
        if val is None:
            ps = int(1.4427 * bf) + prec + 60 + 4 * int(bf).bit_length()
            Bhi = Ctx.beta_at(idx, ps)
            ctx.prec = ps
            shi = acb(arb(1) / 2) - acb(0, 1) * acb(xi)
            val = h4arb.J_series(Bhi, shi, ps)
            ctx.prec = prec
            n_series += 1
        # c_{-1} = -1/2 (idx 0), c_j = +1/2
        tot += (-val if idx == 0 else val)
    ctx.prec = prec
    t2 = tot / (2 * acb.pi())
    g2 = h4arb.gamma2(acb(xi), prec)
    return t2, g2, n_series


def integrand(xi, C, prec=400):
    """acb enclosure of f(xi); its .real is the (real) integrand."""
    t2, g2, ns = t2_and_gamma(xi, C, prec)
    ctx.prec = prec
    ell = 2 * (g2 * t2).real
    hh = h4arb.hhat(acb(xi), C.d, C.A, prec).real
    w = 1 - (C.a * xi).cos()
    return -(w * hh * hh / C.H) * ell, ns
