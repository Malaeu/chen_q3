"""Angle density d_S(xi) evaluator (verdict eq (2),(3),(5),(6),(10))."""
import numpy as np, mpmath as mp
from core import gl_nodes, kernel_coeffs, kernel_vals, build_A, I_closed, J_closed

# ------------------------------------------------------------------ gamma_S,q_S
def gamma_S(xi, primes=()):
    xi = np.atleast_1d(np.asarray(xi, float))
    from scipy.special import loggamma
    g = np.exp(-1j*xi*np.log(np.pi) + loggamma(0.25+0.5j*xi) - loggamma(0.25-0.5j*xi))
    for p in primes:
        a, r = np.log(p), p**-0.5
        g *= (1-r*np.exp(1j*a*xi))/(1-r*np.exp(-1j*a*xi))
    return g

def q_S(xi, primes=(), jmax=200):
    from scipy.special import digamma
    xi = np.atleast_1d(np.asarray(xi, float))
    q = np.real(digamma(0.25+0.5j*xi)) - np.log(np.pi)
    for p in primes:
        a, r = np.log(p), p**-0.5
        j = np.arange(1, jmax+1)
        q -= 2*a*np.sum(r**j[:, None]*np.cos(np.outer(j, a*xi)), axis=0)
    return q

# ------------------------------------------------------------------ v-quadrature
def fine_grid(ximax, betamax, M=60, dens=0.35, base=16):
    """Composite GL on dyadic panels [2^{-m-1},2^{-m}], resolving v^{i xi} and cos(beta v)."""
    vs, ws = [], []
    for m in range(M):
        lo, hi = 2.0**(-m-1), 2.0**(-m)
        n = base + int(np.ceil(dens*(0.7*ximax + betamax*hi)))
        x, w = np.polynomial.legendre.leggauss(n)
        vs.append(0.5*(hi-lo)*x + 0.5*(hi+lo)); ws.append(0.5*(hi-lo)*w)
    return np.concatenate(vs), np.concatenate(ws)

def build_G(u, betas, cs, vq, wq):
    """G_{ik} = K(u_i v_k) w_k  with K(w)=2 sum c_j cos(beta_j w)."""
    G = np.empty((u.size, vq.size))
    blk = max(1, int(4e7//vq.size))
    for s in range(0, u.size, blk):
        e = min(s+blk, u.size)
        G[s:e] = kernel_vals(np.outer(u[s:e], vq), betas, cs)*wq
    return G

# ------------------------------------------------------------------ t_S closed form
def t_S(xi, primes=(), Ju=55, dps=40):
    """t_S(xi) = (1/pi) sum_j c_j J(beta_j, -xi)   (one prime; archimedean: single term)."""
    if not primes:
        return complex(J_closed(2*mp.pi, -xi, dps)/mp.pi)
    p = primes[0]
    tot = mp.mpc(0)
    tot += mp.mpf(-1)/p*J_closed(2*mp.pi/p, -xi, dps)
    for j in range(Ju+1):
        tot += (1-mp.mpf(1)/p)*J_closed(2*mp.pi*mp.mpf(p)**j, -xi, dps)
    return complex(tot/mp.pi)
