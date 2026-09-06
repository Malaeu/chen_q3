"""Analytic Fourier transforms of the frozen test h = (d^2 - 1/4) eta and of the
pole-null family eta_k = (1-(x/d0)^2)^k.  hhat(xi) = -(xi^2+1/4) etahat(xi)."""
import numpy as np
D0 = (np.log(3.0)-np.log(2.0))/8.0

# ---- C^infty bump ----------------------------------------------------------
def _bump_grid(n=60001):
    t = np.linspace(-1.0, 1.0, n)
    y = np.zeros_like(t)
    m = np.abs(t) < 1.0
    y[m] = np.exp(-1.0/(1.0-t[m]**2))
    return t, y

_TB, _YB = _bump_grid()
_NB = 1.0/(np.trapz(_YB, _TB)*D0)          # so that int eta dx = 1

def etahat_bump(xi):
    """Fourier transform of the normalized C^inf bump (real, even)."""
    xi = np.atleast_1d(np.asarray(xi, float))
    x = _TB*D0
    w = np.gradient(x)                      # uniform
    f = _NB*_YB
    out = np.empty(xi.size)
    blk = max(1, int(4e7//x.size))
    for s in range(0, xi.size, blk):
        e = min(s+blk, xi.size)
        out[s:e] = np.trapz(f*np.cos(np.outer(xi[s:e], x)), x, axis=1)
    return out

# ---- polynomial pole-null family (closed form) -----------------------------
from scipy.special import jv, gammaln
def etahat_poly(xi, k):
    """eta_k = N_k (1-(x/d0)^2)^k on |x|<d0, int eta_k = 1.
    int_{-1}^{1}(1-t^2)^k e^{-i w t} dt = sqrt(pi) Gamma(k+1) (2/w)^{k+1/2} J_{k+1/2}(w)."""
    xi = np.atleast_1d(np.asarray(xi, float))
    c = np.exp(gammaln(2*k+2) - (2*k+1)*np.log(2.0) - 2*gammaln(k+1))   # (2k+1)!/(2^{2k+1}(k!)^2)
    Nk = c/D0
    w = np.abs(xi)*D0
    out = np.empty_like(w)
    small = w < 1e-8
    base = np.sqrt(np.pi)*np.exp(gammaln(k+1))
    out[~small] = base*(2.0/w[~small])**(k+0.5)*jv(k+0.5, w[~small])
    out[small] = 2.0**(2*k+1)*np.exp(2*gammaln(k+1)-gammaln(2*k+2))     # value at w=0
    return Nk*D0*out

def hhat2(xi, kind, k=None):
    eh = etahat_bump(xi) if kind == 'bump' else etahat_poly(xi, k)
    return ((np.asarray(xi, float)**2 + 0.25)*eh)**2

# ---- exact L^2 norms of h_k = (d^2-1/4) eta_k ------------------------------
def Hnorm_poly(k, n=4000):
    """||h_k||^2 = int_{-d0}^{d0} (eta_k'' - eta_k/4)^2 dx, exact by Gauss-Legendre
    (the integrand is a polynomial in t of degree 4k-4)."""
    from scipy.special import gammaln
    c = np.exp(gammaln(2*k+2) - (2*k+1)*np.log(2.0) - 2*gammaln(k+1))
    Nk = c/D0
    x, w = np.polynomial.legendre.leggauss(n)     # t in (-1,1)
    t = x
    e   = Nk*(1-t**2)**k
    e2  = Nk/D0**2*(-2*k*(1-t**2)**(k-1) + 4*k*(k-1)*t**2*(1-t**2)**(k-2))
    h   = e2 - e/4.0
    return float(np.sum(w*h*h)*D0)

def Wpoly(xi, k, H=None):
    if H is None: H = Hnorm_poly(k)
    return (1-np.cos(np.log(2.0)*np.asarray(xi,float)))*hhat2(xi,'poly',k)/H
