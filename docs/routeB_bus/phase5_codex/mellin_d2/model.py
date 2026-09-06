"""d_S(xi) from the Galerkin model + exact Mellin scalars."""
import numpy as np, mpmath as mp
import galerkin as gk, dens, core

class Model:
    def __init__(self, M, p=None, J1=14, ppw=6.0, verbose=False):
        self.M, self.p, self.J1 = M, p, J1
        self.A = gk.A_galerkin(M, p, J1, ppw, verbose)
        self.lam, self.V = np.linalg.eigh(self.A)
        o = np.argsort(-np.abs(self.lam))
        self.lam, self.V = self.lam[o], self.V[:, o]
        self.alpha = np.abs(self.lam).max()
        self.primes = () if p is None else (p,)

    def coeffs(self, xi):
        return self.V.T @ gk.mellin_moments(xi, self.M)

    def d(self, xi, t_exact=None, nmax=None):
        c = self.coeffs(xi)
        L = self.lam; 
        if nmax: c, L = c[:nmax], L[:nmax]
        den = 1.0 - L**2
        t_gal = np.sum(L*np.conj(c)**2)
        mixed = np.sum(L*np.conj(c)**2/den)          # <v, A Z vbar>
        quad = float(np.sum(L**2*np.abs(c)**2/den).real)   # <u, Z u>
        unorm2 = float(np.sum(L**2*np.abs(c)**2).real)
        g = dens.gamma_S(np.array([xi]), self.primes)[0]
        out = dict(d_gal=2*np.real(g*mixed)-2*quad, t_gal=t_gal, quad=quad,
                   unorm2=unorm2, gamma=g, alpha=self.alpha)
        if t_exact is not None:
            corr = np.sum(L**3*np.conj(c)**2/den)
            out['d_hyb'] = 2*np.real(g*(t_exact+corr)) - 2*quad
            out['t_exact'] = t_exact
        return out
