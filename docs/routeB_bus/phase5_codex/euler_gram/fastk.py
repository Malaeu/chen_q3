"""Fast archimedean Sonin projector kernel K(xi,eta) = <w_eta,w_xi>, spectral form.

u_xi = A P f_xi  =>  c_n(xi) = <phi_n, u_xi> = lam_n m_n(xi),  m_n(xi) = <phi_n, P f_xi>.
Hence, with w_n = lam_n^2/(1-lam_n^2),  v_n = lam_n^3/(1-lam_n^2)  (lam_n^2 decays
super-geometrically for the prolate operator A_inf, so 8-12 modes suffice):

  Q(eta,xi) = <u_eta, Z u_xi>      = sum_n w_n conj(m_n(eta)) m_n(xi)
  M(eta,xi) = <conj u_eta, Z A u_xi> = sum_n v_n m_n(eta) m_n(xi)
  Tt(xi,eta) = (1/pi)[I(xi)-I(eta)]/(i(eta-xi)),  I(xi)=int_0^1 v^{-1/2+i xi} cos 2 pi v dv
  C(xi,eta) = e^{iD} sin D/(pi (xi-eta)),   D = theta_RS(xi)-theta_RS(eta)
  K(xi,eta) = C - gam_xi conj(gam_eta) conj(Q(eta,xi)) - Q(eta,xi)
              + conj(gam_eta) R(xi,eta) + gam_xi conj(R(xi,eta)),  R = Tt + M.

phi_n and I are expanded in the orthonormal shifted-Legendre basis, whose Mellin
moments mu_k(xi) = <phi^Leg_k, f_xi> have the exact product recursion (mellin_d2).
"""
import numpy as np, os, sys
from scipy.special import loggamma, digamma
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mellin_d2'))

def theta_RS(x):
    x = np.asarray(x, float)
    return np.imag(loggamma(0.25 + 0.5j*x)) - 0.5*x*np.log(np.pi)

def q_inf(x):
    return np.real(digamma(0.25 + 0.5j*np.asarray(x, float))) - np.log(np.pi)

def mellin_moments(xi, M):
    """mu_k(xi) = <phi_k, f_xi>, phi_k = sqrt(2k+1) P_k(2u-1), f_xi=(2pi)^{-1/2}u^{-1/2+i xi}.
    Returns (M, nxi).  Also returns d mu/ds."""
    xi = np.atleast_1d(np.asarray(xi, float))
    s = 0.5 + 1j*xi
    out = np.empty((M, xi.size), complex)
    dl = np.empty((M, xi.size), complex)          # d log mu / ds
    cur = 1.0/s
    lg = -1.0/s
    out[0] = cur; dl[0] = lg
    for m in range(1, M):
        cur = cur*(s-m)/(s+m)
        lg = lg + 1.0/(s-m) - 1.0/(s+m)
        out[m] = cur; dl[m] = lg
    nrm = (np.sqrt(2*np.arange(M)+1.0)/np.sqrt(2*np.pi))[:, None]
    return out*nrm, dl

class FastKern:
    def __init__(self, M=120, nmode=12, Mleg_cos=40):
        from galerkin import Smat
        A = Smat(2*np.pi, M)
        A = 0.5*(A+A.T)
        lam, V = np.linalg.eigh(A)
        o = np.argsort(-np.abs(lam))
        self.lam = lam[o][:nmode]; self.a = V[:, o][:, :nmode]     # (M, nmode)
        self.M = M
        self.w = self.lam**2/(1-self.lam**2)
        self.v = self.lam**3/(1-self.lam**2)
        # Legendre coefficients of cos(2 pi v) on (0,1)
        x, wq = np.polynomial.legendre.leggauss(400)
        u = 0.5*(x+1); wq = 0.5*wq
        P = np.polynomial.legendre.legvander(2*u-1.0, M-1).T*np.sqrt(2*np.arange(M)+1.0)[:, None]
        self.bcos = P @ (wq*np.cos(2*np.pi*u))

    def data(self, xi):
        xi = np.atleast_1d(np.asarray(xi, float))
        mu, dl = mellin_moments(xi, self.M)
        m = self.a.T @ mu                                  # (nmode, nxi)
        I = np.sqrt(2*np.pi)*(self.bcos @ mu)              # I(2pi, xi)
        J = -np.sqrt(2*np.pi)*(self.bcos @ (mu*dl))        # J = -dI/ds
        gam = np.exp(2j*theta_RS(xi))
        return dict(xi=xi, m=m, I=I, J=J, gam=gam, th=theta_RS(xi))

    def diag(self, D):
        m = D['m']
        Q = np.einsum('nk,nk,n->k', m.conj(), m, self.w).real
        Mx = np.einsum('nk,nk,n->k', m, m, self.v)
        t = D['J']/np.pi
        return q_inf(D['xi'])/(2*np.pi) - 2*Q + 2*np.real(np.conj(D['gam'])*(t+Mx))

    def block(self, Di, Dj, tol=0.02, jfun=None):
        """K(xi_i, eta_j) matrix."""
        xi = Di['xi'][:, None]; eta = Dj['xi'][None, :]
        d = xi - eta
        Dl = Di['th'][:, None] - Dj['th'][None, :]
        zero = np.abs(d) < 1e-13
        C = np.exp(1j*Dl)*np.sin(Dl)/(np.pi*np.where(zero, 1.0, d))
        Q = (Dj['m'].conj()*self.w[:, None]).T @ Di['m']       # [j,i] = Q(eta_j, xi_i)
        Q = Q.T
        Mx = ((Dj['m']*self.v[:, None]).T @ Di['m']).T
        Ii = Di['I'][:, None]; Ij = Dj['I'][None, :]
        near = np.abs(d) < tol
        Tt = (Ii-Ij)/(1j*np.where(near, 1.0, eta-xi))/np.pi
        if near.any():
            ii, jj = np.where(near)
            if jfun is None:
                # 2nd-order divided difference from J and its s-derivative is avoided:
                # use J at the midpoint (error O(delta^2 I'''/24))
                Jm = 0.5*(Di['J'][ii] + Dj['J'][jj])
            else:
                Jm = jfun(0.5*(Di['xi'][ii]+Dj['xi'][jj]), Di['xi'][ii]-Dj['xi'][jj])
            Tt[ii, jj] = Jm/np.pi
        R = Tt + Mx
        gi = Di['gam'][:, None]; gj = Dj['gam'][None, :]
        K = C - gi*np.conj(gj)*np.conj(Q) - Q + np.conj(gj)*R + gi*np.conj(R)
        if zero.any():
            dg = self.diag(Di)
            ii, jj = np.where(zero)
            K[ii, jj] = dg[ii]
        return K
