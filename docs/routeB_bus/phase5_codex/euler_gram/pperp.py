"""Exact |P_0 v|^2 through the orthogonal complement, and the physical Sonin
reproducing vectors w_xi(s) on s in (1,2).

H_0 = ker P cap ker Q_inf = (ran P + ran Q_inf)^perp.  With g = (E e_k) u (F E e_k)
(E = zero extension from (0,1)) the Gram is [[I,A],[A,I]], A = P F P, and
[[I,A],[A,I]]^{-1} = [[Z,-ZA],[-AZ,Z]], Z = (I-A^2)^{-1}.  Hence for any v,

   |P_0 v|^2 = |v|^2 - ( <m_a,Z m_a> + <m_b,Z m_b> - 2 Re <m_a, Z A m_b> ),
   m_a = P v,  m_b = P F v.                                        EXACT

For psi = (U_a + U_{-a}) y with y in H_0 (supported in (1,infty)):
   U_a y lives on (2,infty)  =>  contributes nothing to m_a, m_b,
   m_a(u) = sqrt2 y(2u),  m_b(u) = sqrt2 (F y)(2u) = sqrt2 sum_j c_j gam_j conj(w_j(2u)),
both supported on (1/2,1)  (F H_0 = H_0 and F w_xi = gamma(xi) conj(w_xi)).

Physical reproducing vector, for s > 1:
   w_xi(s) = (2pi)^{-1/2} s^{-1/2+i xi} - 2 gamma(xi) sum_k b_k(2 pi s) conj(mu_k(xi))
             - 2 sum_n (a^T b(2 pi s))_n h_n(xi),
   h_n(xi) = gamma(xi) lam_n^2/(1-lam_n^2) conj(m_n(xi)) - lam_n/(1-lam_n^2) m_n(xi),
   b_k(beta) = int_0^1 cos(beta v) phi_k^Leg(v) dv = sqrt(2k+1) Re[e^{i beta/2} i^k j_k(beta/2)].
"""
import numpy as np
from scipy.special import spherical_jn
import fastk

def bvec(beta, M):
    """b_k(beta), k<M, for an array of beta -> (nbeta, M)."""
    beta = np.atleast_1d(np.asarray(beta, float))
    z = beta/2.0
    out = np.empty((beta.size, M))
    e = np.exp(1j*z)
    for k in range(M):
        out[:, k] = np.sqrt(2*k+1.0)*np.real((1j**k)*e*spherical_jn(k, z))
    return out

def wphys(fk, xi, s):
    """W[si, j] = w_{xi_j}(s_i)  for s>1."""
    xi = np.atleast_1d(np.asarray(xi, float)); s = np.atleast_1d(np.asarray(s, float))
    mu, _ = fastk.mellin_moments(xi, fk.M)              # (M, nxi)
    m = fk.a.T @ mu                                     # (nmode, nxi)
    gam = np.exp(2j*fastk.theta_RS(xi))
    B = bvec(2*np.pi*s, fk.M)                           # (ns, M)
    lam = fk.lam
    hn = gam[None, :]*(lam**2/(1-lam**2))[:, None]*m.conj() - (lam/(1-lam**2))[:, None]*m
    W = (s[:, None]**(-0.5+1j*xi[None, :]))/np.sqrt(2*np.pi)
    W = W - 2*gam[None, :]*(B @ mu.conj())
    W = W - 2*((B @ fk.a) @ hn)
    return W

class Complement:
    """Nystrom realisation of A on (0,1) with a panel break at 1/2."""
    def __init__(self, npan=500):
        x, w = np.polynomial.legendre.leggauss(npan)
        u1 = 0.25*(x+1.0); w1 = 0.25*w
        u2 = 0.25*(x+1.0)+0.5; w2 = 0.25*w
        self.u = np.concatenate([u1, u2]); self.w = np.concatenate([w1, w2])
        self.sw = np.sqrt(self.w)
        A = (2.0*np.cos(2*np.pi*np.outer(self.u, self.u)))*self.sw[:, None]*self.sw[None, :]
        A = 0.5*(A+A.T)
        self.lam, self.V = np.linalg.eigh(A)
        self.den = 1.0 - self.lam**2
        self.n2 = self.u.size//2                          # index where u>1/2 starts

    def proj_sq(self, ma, mb):
        """|P_0 v|^2 correction term <v,P_R v>;  ma, mb are function values on self.u
        (columns = different v).  Returns the correction (real, >=0)."""
        Aa = self.V.T @ (self.sw[:, None]*ma)
        Ab = self.V.T @ (self.sw[:, None]*mb)
        t1 = np.einsum('nm,nm,n->m', Aa.conj(), Aa, 1.0/self.den).real
        t2 = np.einsum('nm,nm,n->m', Ab.conj(), Ab, 1.0/self.den).real
        t3 = np.einsum('nm,nm,n->m', Aa.conj(), Ab, self.lam/self.den)
        return t1 + t2 - 2*np.real(t3)
