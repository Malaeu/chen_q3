"""Source-exact evaluator of the angle density d_S(xi), verdict eq (1)-(18).
Cutoff lambda = 1, physical half-line u in (0,1).
"""
import numpy as np
import mpmath as mp

# ---------------------------------------------------------------- scalars I, J
def I_closed(beta, xi, dps=40):
    """I(beta,xi) = int_0^1 v^{-1/2+i xi} cos(beta v) dv, closed form."""
    with mp.workdps(dps):
        s = mp.mpf(1)/2 + 1j*mp.mpmathify(xi)
        b = mp.mpmathify(beta)
        if b == 0:
            return mp.mpc(1)/s
        out = 0
        for sgn in (-1, 1):
            z = sgn*1j*b          # z = -i beta  and  +i beta
            out += z**(-s)*mp.gammainc(s, 0, z)
        return out/2

def _I_series_s(beta, s, deriv=0):
    """I (deriv=0) or J = -dI/ds (deriv=1) from the exact power series."""
    b2 = mp.mpmathify(beta)**2
    term = mp.mpf(1); tot = mp.mpc(0); m = 0
    while True:
        d = (2*m + s)
        c = term/(d if deriv == 0 else d*d)
        tot += c
        if m > 4 and abs(c) < abs(tot)*mp.mpf(10)**(-mp.mp.dps-5) and abs(term) < mp.mpf(10)**(-mp.mp.dps-5):
            break
        m += 1
        term *= -b2/((2*m)*(2*m-1))
        if m > 200000:
            raise RuntimeError('series did not terminate')
    return tot

def I_series(beta, xi, dps=None):
    if dps is None:
        dps = int(0.435*float(beta)) + 60
    with mp.workdps(dps):
        s = mp.mpf(1)/2 + 1j*mp.mpmathify(xi)
        return +_I_series_s(beta, s, 0)

def J_series(beta, xi, dps=None):
    """J(beta,xi) = int_0^1 (-log v) v^{-1/2+i xi} cos(beta v) dv = -dI/ds."""
    if dps is None:
        dps = int(0.435*float(beta)) + 60
    with mp.workdps(dps):
        s = mp.mpf(1)/2 + 1j*mp.mpmathify(xi)
        return +_I_series_s(beta, s, 1)

def J_closed(beta, xi, dps=40):
    with mp.workdps(dps):
        s0 = mp.mpf(1)/2 + 1j*mp.mpmathify(xi)
        b = mp.mpmathify(beta)
        def f(s):
            if b == 0:
                return mp.mpc(1)/s
            out = 0
            for sgn in (-1, 1):
                z = sgn*1j*b
                out += z**(-s)*mp.gammainc(s, 0, z)
            return out/2
        return -mp.diff(f, s0)

# ---------------------------------------------------------------- operator A_S
def gl_nodes(N):
    """Gauss-Legendre nodes/weights on (0,1)."""
    x, w = np.polynomial.legendre.leggauss(N)
    return 0.5*(x+1.0), 0.5*w

def kernel_coeffs(p=None, J=8):
    """(betas, cs) for the compressed kernel K(w) = 2 sum_j c_j cos(beta_j w).
    p=None -> archimedean only."""
    betas = [2*np.pi]; cs = [1.0]
    if p is not None:
        betas = [2*np.pi/p] + [2*np.pi*float(p)**j for j in range(J+1)]
        cs = [-1.0/p] + [1.0-1.0/p]*(J+1)
    return np.array(betas), np.array(cs)

def kernel_vals(w, betas, cs):
    out = np.zeros_like(w)
    for b, c in zip(betas, cs):
        out += c*np.cos(b*w)
    return 2.0*out

def build_A(N, betas, cs):
    u, w = gl_nodes(N)
    sw = np.sqrt(w)
    A = kernel_vals(np.outer(u, u), betas, cs)
    A *= sw[:, None]; A *= sw[None, :]
    return u, w, A
