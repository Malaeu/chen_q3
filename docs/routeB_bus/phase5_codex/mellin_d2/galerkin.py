"""Galerkin compression of A_S on L^2(0,1) in the orthonormal shifted-Legendre basis.

phi_m(u) = sqrt(2m+1) P_m(2u-1).
S_mn(beta) = int_0^1 int_0^1 phi_m(u) 2cos(beta u t) phi_n(t) du dt
           = 2 sqrt((2m+1)(2n+1)) Re[ i^n int_0^1 P_m(2u-1) e^{i beta u/2} j_n(beta u/2) du ]
A_S = sum_{j>=-1} c_j S(beta_j);  tail j>J1 handled analytically  S_mn(beta) ~ phi_m(0)phi_n(0) pi/beta.
Galerkin compression P_M A P_M is a compression of a self-adjoint contraction => ||.|| <= ||A_S|| < 1.
"""
import numpy as np
from scipy.special import spherical_jn


_GL = {}
def _gl(k):
    if k not in _GL:
        _GL[k] = np.polynomial.legendre.leggauss(k)
    return _GL[k]

def _quad(beta, ppw=6.0, k=20, M=1):
    """Composite Gauss-Legendre on (0,1): panels short enough for frequency beta/2."""
    npan = max(1, int(np.ceil(ppw*beta/(2*np.pi*k))), int(np.ceil(4.0*M/k)))
    edges = np.linspace(0.0, 1.0, npan+1)
    x, w = _gl(k)
    h = edges[1]-edges[0]
    u = (0.5*h*(x[None, :]+1.0) + edges[:-1, None]).ravel()
    ww = np.tile(0.5*h*w, npan)
    return u, ww


def Smat(beta, M, ppw=6.0):
    if beta == 0:
        v = np.zeros(M); v[0] = 1.0
        return 2*np.outer(v, v)
    u, w = _quad(beta, ppw, M=M)
    z = beta*u/2.0
    P = np.polynomial.legendre.legvander(2*u-1.0, M-1).T          # (M,Nq)
    X = P*w
    e = np.exp(1j*z)
    Y = np.empty((M, u.size), complex)
    for n in range(M):
        Y[n] = (1j**n)*e*spherical_jn(n, z)
    S = 2.0*np.real(X @ Y.T)
    nrm = np.sqrt(2*np.arange(M)+1.0)
    return nrm[:, None]*S*nrm[None, :]


def A_galerkin(M, p=None, J1=12, ppw=6.0, verbose=False):
    if p is None:
        return Smat(2*np.pi, M, ppw)
    A = -(1.0/p)*Smat(2*np.pi/p, M, ppw)
    c = 1.0 - 1.0/p
    for j in range(J1+1):
        A += c*Smat(2*np.pi*float(p)**j, M, ppw)
        if verbose:
            print(f"   j={j} beta={2*np.pi*p**j:.3e} done", flush=True)
    phi0 = np.sqrt(2*np.arange(M)+1.0)*(-1.0)**np.arange(M)        # phi_m(0)
    A += np.outer(phi0, phi0)*float(p)**(-J1-1)/2.0                # analytic tail j>J1
    return 0.5*(A+A.T)


def mellin_moments(xi, M):
    """<phi_m, f_xi> = (2pi)^{-1/2} sqrt(2m+1) prod_{k=1}^m (s-k) / prod_{k=0}^m (s+k), s=1/2+i xi."""
    s = 0.5 + 1j*xi
    out = np.empty(M, complex)
    num = 1.0+0j
    den = s
    out[0] = num/den
    for m in range(1, M):
        num *= (s-m)
        den *= (s+m)
        out[m] = num/den
    return out*np.sqrt(2*np.arange(M)+1.0)/np.sqrt(2*np.pi)
