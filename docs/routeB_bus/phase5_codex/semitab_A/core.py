"""Core objects: tests v, the archimedean/semilocal quantities, prolate angle data."""
import numpy as np
from numpy.polynomial.legendre import leggauss

GAMMA_E = 0.57721566490153286060651209008240243104215933593992
C_A     = GAMMA_E + np.log(8*np.pi) + np.pi/2          # = 5.3721834192...
LOG2    = np.log(2.0)
LOG3    = np.log(3.0)

# ---------------------------------------------------------------- tests
class Test:
    """A test v on [-Lh,Lh] given as a callable; all functionals by Gauss-Legendre."""
    def __init__(self, fun, half, name, ngl=800, complex_=False):
        self.fun, self.half, self.name = fun, half, name
        x, w = leggauss(ngl)
        self.x = half*x; self.w = half*w
        self.v = np.asarray(fun(self.x), dtype=complex if complex_ else float)
        self.nrm2 = float(np.real(np.sum(self.w*np.abs(self.v)**2)))
        self.Ap = complex(np.sum(self.w*self.v*np.exp( self.x/2)))
        self.Am = complex(np.sum(self.w*self.v*np.exp(-self.x/2)))
        self.P02 = 2*np.real(self.Ap*np.conj(self.Am))
    def _build_ftab(self, ns=40001):
        S = np.linspace(-2*self.half, 2*self.half, ns)
        vals = np.zeros(ns, dtype=complex)
        chunk = 2000
        cw = self.w*np.conj(self.v)
        for a in range(0, ns, chunk):
            b = min(ns, a+chunk)
            Z = self.x[None, :] + S[a:b, None]
            V = np.zeros(Z.shape, dtype=self.v.dtype)
            m = np.abs(Z) < self.half
            V[m] = self.fun(Z[m])
            vals[a:b] = V @ cw
        self._S = S; self._ftab = vals

    def f(self, s):
        """f(s) = int conj(v(x)) v(x+s) dx  (=0 for |s| > 2*half). Cubic-interpolated table."""
        if not hasattr(self, "_ftab"):
            self._build_ftab()
        s = np.asarray(s, dtype=float)
        out = np.zeros(s.shape, dtype=complex)
        m = np.abs(s) < 2*self.half
        if m.any():
            from scipy.interpolate import CubicSpline
            if not hasattr(self, "_csr"):
                self._csr = CubicSpline(self._S, np.real(self._ftab))
                self._csi = CubicSpline(self._S, np.imag(self._ftab))
            out[m] = self._csr(s[m]) + 1j*self._csi(s[m])
        return out
    def veval(self, z):
        z = np.asarray(z, dtype=float)
        out = np.zeros(z.shape, dtype=self.v.dtype)
        m = np.abs(z) < self.half
        if m.any():
            out[m] = self.fun(z[m])
        return out
    def Cv(self, t):
        return np.real(self.f(np.atleast_1d(np.asarray(t, float))))

    def fexact(self, si):
        return complex(np.sum(self.w*np.conj(self.v)*self.veval(self.x+si)))
    # --- vhat on a tau grid
    def vhat(self, tau):
        tau = np.asarray(tau, float)
        return (self.w*self.v)[None, :] @ np.exp(-1j*np.outer(tau, self.x)).T.conj().T.T if False else \
               np.exp(-1j*np.outer(tau, self.x)) @ (self.w*self.v)

def digamma_re(z):
    from scipy.special import digamma
    return np.real(digamma(z))

def D_minus_cA(T, ntau=200000, taumax=None):
    """(D(v) - c_A ||v||^2) via the Fourier multiplier Re psi(1/4+i tau/2) - log pi."""
    if taumax is None:
        taumax = max(400.0, 60.0/max(T.half, 1e-3))
    tau = np.linspace(-taumax, taumax, ntau+1)
    vh = T.vhat(tau)
    mult = digamma_re(0.25+0.5j*tau) - np.log(np.pi)
    integ = np.abs(vh)**2*mult
    return float(np.trapz(integ, tau)/(2*np.pi))

def D_direct(T, nt=4000, tmax=80.0):
    """D(v) = int_0^inf a(t) ||v(.+t)-v||^2 dt, direct (independent code path)."""
    # substitute t = e^y to handle the 1/(2t) singularity: dt = e^y dy
    y = np.linspace(np.log(1e-12), np.log(tmax), nt)
    t = np.exp(y)
    a = np.exp(-t/2)/(1-np.exp(-2*t))
    g = 2*T.nrm2 - 2*T.Cv(t)
    return float(np.trapz(a*g*t, y))

def prime_sum(T, primes, jmax=200):
    """2 * sum_{p in primes, j>=1} (log p) p^{-j/2} C_v(j log p)."""
    tot = 0.0
    for p in primes:
        lp = np.log(p)
        j = 1
        while j*lp < 2*T.half + 1e-12 and j <= jmax:
            tot += lp*p**(-j/2.0)*T.Cv(np.array([j*lp]))[0]
            j += 1
    return 2*tot

def primes_upto(n):
    s = np.ones(n+1, bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0].tolist()

def L_S(T, Sf=(2,)):
    return D_minus_cA(T) - prime_sum(T, Sf)

def Q_form(T, Sf=(2,)):
    """Full Weil form Q(v) = D - c_A||v||^2 + P02 - 2 sum_{all n>=2} w_n C_v(log n)."""
    allp = primes_upto(int(np.exp(2*T.half))+2)
    return D_minus_cA(T) + T.P02 - prime_sum(T, allp)

# ---------------------------------------------------------------- prolate angle data
class Angles:
    """alpha_n, xi_n, zeta_n for the pair (P_lambda, Q_lambda) with F = F_inf or F_S."""
    def __init__(self, lam, npan=8, nq=60, Jsum=None):
        self.lam = lam
        # composite Gauss-Legendre on [0,lam]
        edges = np.linspace(0, lam, npan+1)
        xs, ws = [], []
        gx, gw = leggauss(nq)
        for a, b in zip(edges[:-1], edges[1:]):
            xs.append(0.5*(b-a)*gx+0.5*(a+b)); ws.append(0.5*(b-a)*gw)
        self.t = np.concatenate(xs); self.w = np.concatenate(ws)
        K = 2*np.cos(2*np.pi*np.outer(self.t, self.t))
        if Jsum is not None:                        # semilocal: F_S = J F J^{-1}
            K = Jsum(K, self.t, self.w)
        M = np.sqrt(self.w)[:, None]*K*np.sqrt(self.w)[None, :]
        M = 0.5*(M+M.T)
        ev, U = np.linalg.eigh(M)
        idx = np.argsort(-np.abs(ev))
        self.alpha = ev[idx]; self.U = U[:, idx]    # unitary coords
    def xi(self, n):
        """values of xi_n at the quadrature nodes t (function values, not unitary coords)"""
        return self.U[:, n]/np.sqrt(self.w)
    def Fxi(self, n, u):
        """(F_inf xi_n)(u) = 2 int_0^lam xi_n(t) cos(2 pi u t) dt, spectrally exact"""
        xi = self.xi(n)
        u = np.atleast_1d(np.asarray(u, float))
        return 2.0*(np.cos(2*np.pi*np.outer(u, self.t))@(self.w*xi))
