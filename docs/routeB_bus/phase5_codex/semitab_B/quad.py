"""Independent quadrature path: ||v||^2, C_v(t), D(v), L_S, P_02, Q(v).
No operators are used here (the S4 identity check needs L_S from an independent path)."""
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.interpolate import CubicSpline
import mpmath as mp

mp.mp.dps = 30
C_A = float(mp.euler + mp.log(8 * mp.pi) + mp.pi / 2)
LOG2 = float(np.log(2.0))


def von_mangoldt(nmax):
    lam = np.zeros(nmax + 1)
    sieve = np.ones(nmax + 1, dtype=bool); sieve[:2] = False
    for p in range(2, int(nmax ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= nmax:
            lam[q] = np.log(p); q *= int(p)
    return lam


class Quad:
    """v: callable on a numpy array (may be complex); supp v subset [-a, a]."""
    def __init__(self, v, a, dx=1e-4, pad=0.3):
        self.v = v; self.a = a; self.L = 2 * a; self.dx = dx
        X0 = a + pad
        n = int(np.ceil(2 * X0 / dx)) + 1
        self.xg = np.linspace(-X0, X0, n)
        self.h = self.xg[1] - self.xg[0]
        vg = np.asarray(v(self.xg), dtype=complex)
        self.vg = vg
        self.norm2 = float(self.h * np.sum(np.abs(vg) ** 2))
        self.Ap = complex(self.h * np.sum(vg * np.exp(self.xg / 2)))
        self.Am = complex(self.h * np.sum(vg * np.exp(-self.xg / 2)))
        self.P02 = 2 * float(np.real(self.Ap * np.conj(self.Am)))
        Cc = complex(self.h * np.sum(vg * np.cosh(self.xg / 2)))
        Ss = complex(self.h * np.sum(vg * np.sinh(self.xg / 2)))
        self.P02_alt = 2 * (abs(Cc) ** 2 - abs(Ss) ** 2)
        # autocorrelation by FFT (linear, zero padded): r(k h) = h sum_i conj(v_i) v_{i+k}
        m = 1
        while m < 2 * n:
            m *= 2
        V = np.fft.fft(vg, m)
        R = np.fft.ifft(np.conj(V) * V)
        lags = np.arange(-(n - 1), n)
        r = np.concatenate([R[m - (n - 1):], R[:n]]) * self.h
        self.ct = lags * self.h
        self.cs = CubicSpline(self.ct, np.real(r))

    def C(self, t):
        t = np.atleast_1d(np.asarray(t, dtype=float))
        out = np.where(np.abs(t) <= self.ct[-1], self.cs(np.clip(t, self.ct[0], self.ct[-1])), 0.0)
        return out

    def D(self, ngl=300, nseg=10):
        L = self.L
        edges = np.linspace(0.0, L, nseg + 1)
        xs, ws = leggauss(ngl)
        tot = 0.0
        for s in range(nseg):
            lo, hi = edges[s], edges[s + 1]
            tt = 0.5 * (hi - lo) * xs + 0.5 * (hi + lo)
            wq = 0.5 * (hi - lo) * ws
            at = np.exp(-tt / 2) / (1 - np.exp(-2 * tt))
            tot += float(np.sum(wq * 2 * at * (self.norm2 - self.C(tt))))
        k = np.arange(0, 600)
        tail = 2 * self.norm2 * float(np.sum(np.exp(-(2 * k + 0.5) * L) / (2 * k + 0.5)))
        return tot + tail

    def prime_sum(self, primes=None, nmax=None):
        """returns -2 * sum_{n} Lambda(n)/sqrt(n) * C_v(log n) restricted to n with log n <= L.
           primes=None -> all n (full Q); primes=(2,) -> only powers of 2 (L_S with S_f={2})."""
        if nmax is None:
            nmax = int(np.exp(self.L)) + 2
        nmax = max(nmax, 4)
        lam = von_mangoldt(nmax)
        s = 0.0
        for n in range(2, nmax + 1):
            if lam[n] == 0.0:
                continue
            if primes is not None:
                pm = int(round(np.exp(lam[n])))
                if pm not in primes:
                    continue
            t = np.log(n)
            if t > self.L:
                continue
            s += lam[n] / np.sqrt(n) * float(self.C(np.array([t]))[0])
        return -2.0 * s

    def all(self, Sf=(2,)):
        D = self.D()
        base = D - C_A * self.norm2
        pS = self.prime_sum(primes=Sf)
        pall = self.prime_sum(primes=None)
        return dict(norm2=self.norm2, D=D, base=base, P02=self.P02, P02_alt=self.P02_alt,
                    prime_S=pS, prime_all=pall, L_S=base + pS, Q=base + self.P02 + pall,
                    Ap=self.Ap, Am=self.Am)
