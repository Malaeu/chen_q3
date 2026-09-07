"""Off-diagonal archimedean Sonin projector kernel  K(xi,eta) = <w_eta, w_xi>.

S_inf = P' - T* Z T,  P = physical cutoff (0,1), P'=I-P, F = F_inf (kernel 2cos(2 pi u v)),
A = P F P on L^2(0,1), T = P F P', Z = (I-A^2)^{-1};  TT* = I - A^2 gives the formula.
With  f_xi(u) = (2pi)^{-1/2} u^{-1/2+i xi},  g_xi = P f_{-xi},  u_xi = A P f_xi,
F f_xi = gamma(xi) f_{-xi},  gamma = e^{2 i theta_RS}:

  K(xi,eta) = C(xi,eta) - gam_xi conj(gam_eta) conj(Q) - Q
              + conj(gam_eta) R + gam_xi conj(R)
  C(xi,eta) = e^{i D} sin D / (pi (xi-eta)),  D = theta_RS(xi) - theta_RS(eta)   [-> q_inf/2pi]
  Q(xi,eta) = <u_eta, Z u_xi>          (Hermitian: Q(eta,xi) = conj(Q(xi,eta)))
  R(xi,eta) = Tt(xi,eta) + M(xi,eta),  both symmetric
  Tt = (1/pi) [I(xi)-I(eta)] / (i (eta-xi)),   I(xi) = int_0^1 v^{-1/2+i xi} cos(2 pi v) dv
  M  = <conj(u_eta), Z A u_xi> = sum_n lam_n c_n(xi) c_n(eta)/(1-lam_n^2)
Diagonal K(xi,xi) = k_inf(xi) = q_inf/2pi + d_inf(xi), reproducing mellin_d2's d_inf.
"""
import numpy as np, os, sys
from scipy.special import loggamma, digamma

def theta_RS(x):
    x = np.asarray(x, float)
    return np.imag(loggamma(0.25 + 0.5j*x)) - 0.5*x*np.log(np.pi)

def q_inf(x):
    return np.real(digamma(0.25 + 0.5j*np.asarray(x, float))) - np.log(np.pi)

class ArchSonin:
    """Nystrom realisation of A_inf on (0,1) + the fine Mellin v-grid."""
    def __init__(self, N=800, ximax=700.0, densq=0.45, Mpan=100, base=20):
        x, w = np.polynomial.legendre.leggauss(N)
        u = 0.5*(x+1.0); w = 0.5*w
        self.u, self.w = u, w
        sw = np.sqrt(w); self.sw = sw
        A = (2.0*np.cos(2*np.pi*np.outer(u, u)))*sw[:, None]*sw[None, :]
        A = 0.5*(A+A.T)
        self.lam, self.V = np.linalg.eigh(A)
        self.alpha = float(np.abs(self.lam).max())
        self.Zd = 1.0/(1.0 - self.lam**2)          # diag of Z in the eigenbasis
        vs, ws = [], []
        for m in range(Mpan):
            lo, hi = 2.0**(-m-1), 2.0**(-m)
            n = base + int(np.ceil(densq*(0.7*ximax + 2*np.pi*hi)))
            xx, ww = np.polynomial.legendre.leggauss(n)
            vs.append(0.5*(hi-lo)*xx + 0.5*(hi+lo)); ws.append(0.5*(hi-lo)*ww)
        self.vq = np.concatenate(vs); self.wq = np.concatenate(ws)
        self.logv = np.log(self.vq)
        self.Gm = (2.0*np.cos(2*np.pi*np.outer(u, self.vq)))*self.wq
        self.wIb = self.wq*self.vq**-0.5*np.cos(2*np.pi*self.vq)

    def data(self, xi, block=48, verbose=False):
        """c (N x nxi) = eigen-coefficients of u_xi;  I(xi), J(xi), gamma(xi)."""
        xi = np.atleast_1d(np.asarray(xi, float))
        nx = xi.size
        c = np.empty((self.lam.size, nx), complex)
        Iv = np.empty(nx, complex); Jv = np.empty(nx, complex)
        pref = self.vq**-0.5/np.sqrt(2*np.pi)
        for s in range(0, nx, block):
            e = min(s+block, nx)
            ph = np.exp(1j*np.outer(self.logv, xi[s:e]))
            c[:, s:e] = self.V.T @ (self.sw[:, None]*(self.Gm @ (pref[:, None]*ph)))
            b = self.wIb[:, None]*ph
            Iv[s:e] = b.sum(axis=0)
            Jv[s:e] = (-self.logv[:, None]*b).sum(axis=0)
            if verbose and (s//block) % 10 == 0:
                print(f"   data {e}/{nx}", flush=True)
        return c, Iv, Jv, np.exp(2j*theta_RS(xi))

    def Jmid(self, m, dl):
        """J(2pi, m) with the sinc regularisation: exact divided difference of I."""
        out = np.empty(np.size(m), complex)
        m = np.ravel(m); dl = np.ravel(dl)
        base = self.wIb*(-self.logv)
        for k in range(m.size):
            out[k] = np.sum(base*np.exp(1j*m[k]*self.logv)*np.sinc(0.5*dl[k]*self.logv/np.pi))
        return out

class Kern:
    """K(xi_i, xi_j) on a fixed xi grid."""
    def __init__(self, son, xi, block=48, verbose=False):
        self.son = son
        self.xi = np.atleast_1d(np.asarray(xi, float))
        self.c, self.I, self.J, self.gam = son.data(self.xi, block, verbose)
        self.th = theta_RS(self.xi)
        self.Zd = son.Zd; self.lam = son.lam
        self._diag = None

    def diag(self):
        if self._diag is None:
            c = self.c
            q = np.einsum('nk,nk,n->k', c.conj(), c, self.Zd).real
            M = np.einsum('nk,nk,n->k', c, c, self.lam*self.Zd)
            t = self.J/np.pi
            self._diag = q_inf(self.xi)/(2*np.pi) - 2*q + 2*np.real(np.conj(self.gam)*(t+M))
        return self._diag

    def block(self, isl, jsl, tol=1e-2):
        i0 = isl.start or 0; j0 = jsl.start or 0
        xi = self.xi[isl][:, None]; eta = self.xi[jsl][None, :]
        ci = self.c[:, isl]; cj = self.c[:, jsl]
        gi = self.gam[isl][:, None]; gj = self.gam[jsl][None, :]
        d = xi - eta
        Dl = self.th[isl][:, None] - self.th[jsl][None, :]
        zero = np.abs(d) < 1e-13
        dd = np.where(zero, 1.0, d)
        C = np.exp(1j*Dl)*np.sin(Dl)/(np.pi*dd)
        Q = ((cj*self.Zd[:, None]).conj().T @ ci).T          # [i,j] = <u_eta_j, Z u_xi_i>
        M = ((cj*(self.lam*self.Zd)[:, None]).T @ ci).T      # [i,j] symmetric
        Ii = self.I[isl][:, None]; Ij = self.I[jsl][None, :]
        near = np.abs(d) < tol
        Tt = (Ii-Ij)/(1j*np.where(near, 1.0, eta-xi))/np.pi
        if near.any():
            ii, jj = np.where(near)
            m = 0.5*(self.xi[isl][ii] + self.xi[jsl][jj]); dl = self.xi[isl][ii] - self.xi[jsl][jj]
            Tt[ii, jj] = self.son.Jmid(m, dl)/np.pi
        R = Tt + M
        K = C - gi*np.conj(gj)*np.conj(Q) - Q + np.conj(gj)*R + gi*np.conj(R)
        if zero.any():
            dg = self.diag()
            ii, jj = np.where(zero)
            K[ii, jj] = dg[isl][ii]
        return K

    def full(self):
        n = self.xi.size
        return self.block(slice(0, n), slice(0, n))
