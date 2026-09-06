"""Assemble d_S(xi) from operator data + Mellin scalars."""
import numpy as np, mpmath as mp
from core import gl_nodes, kernel_coeffs, kernel_vals, build_A
import dens

class Evaluator:
    def __init__(self, N, primes=(), J=8, ximax=130.0, dens_q=0.35, M=60, base=16, Ju=55):
        self.primes, self.J, self.Ju = primes, J, Ju
        p = primes[0] if primes else None
        self.betas, self.cs = kernel_coeffs(p, J)
        self.u, self.w, A = build_A(N, self.betas, self.cs)
        self.lam, self.V = np.linalg.eigh(A)          # A = V diag(lam) V^T
        self.alpha = np.abs(self.lam).max()
        self.vq, self.wq = dens.fine_grid(ximax, self.betas.max(), M=M, dens=dens_q, base=base)
        self.G = dens.build_G(self.u, self.betas, self.cs, self.vq, self.wq)
        self.sw = np.sqrt(self.w)
        self.logv = np.log(self.vq); self.vm = self.vq**-0.5

    def uvec(self, xi):
        """u_S(xi) in the sqrt(w)-scaled Nystrom representation."""
        f = (self.vm*np.exp(1j*xi*self.logv))/np.sqrt(2*np.pi)
        return self.sw*(self.G @ f)

    def parts(self, xi, t_val=None):
        ut = self.uvec(xi)
        c = self.V.T @ ut                     # coefficients <phi_n, u> (phi real)
        den = 1.0 - self.lam**2
        quad = np.sum(np.abs(c)**2/den).real                     # <u, Z u>
        mixed = np.sum(self.lam*np.conj(c)**2/den)               # <u, A Z conj(u)>
        t = dens.t_S(xi, self.primes, self.Ju) if t_val is None else t_val
        g = dens.gamma_S(np.array([xi]), self.primes)[0]
        d = 2*np.real(g*(t + mixed)) - 2*quad
        return dict(d=d, t=t, mixed=mixed, quad=quad, gamma=g,
                    unorm2=float(np.sum(np.abs(ut)**2)))
