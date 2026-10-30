"""Numerical check of the MARKOV verdict identity (6.8). DIAGNOSTIC_NEVER_A_PROOF (float64 quadrature).
k[hF] = E_h[F] - 8 (Var_mu F + (int tau F dmu)^2),  h = theta function (4.3), dmu = cosh(x/2) h dx / 2, tau = tanh(x/2).
Left side: Weil form of f = hF via the Fourier multiplier a(xi) = Re psi(1/4 + i xi/2) - log pi, minus prime correlations,
plus pole |<p,f>|^2 - |<q,f>|^2 (verdict (1.2)-(1.4)). Normalization cross-check: the same left-side code on the smooth
window mode psi_0 - (psi_1 + psi_-1)/2 must reproduce c^T K c of full_center_probe.matrix_K (the discontinuous psi_0 alone
gives unstable quadrature, 0.1222 / 0.1224 vs 0.1223).
Right side: jump energy (6.4) by 2D quadrature, all prime powers with log n <= 5, exterior jumps kept.
"""
import math, sys
from pathlib import Path
import numpy as np
import mpmath as mp
from scipy import integrate
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))

def h(x):
    x = abs(x); s = 0.0
    for n in range(1, 40):
        e2 = math.exp(2 * x) * n * n
        if math.pi * e2 > 700: break
        s += (16 * math.pi**2 * e2**2 - 24 * math.pi * e2) * math.exp(-math.pi * e2)
    return math.exp(x / 2) * s

def vonmangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            k = n
            while k % p == 0: k //= p
            return math.log(p) if k == 1 else 0.0
    return 0.0

def a_mult(xi):
    return float(mp.re(mp.digamma(mp.mpf(1) / 4 + 0.5j * xi))) - math.log(math.pi)

def weil_form(f, lo, hi, nmax, ximax=200.0):  # scipy quad breaks on [0, 3000] (oscillation noise); 200 is converged for smooth f
    """Weil form of a real function f supported in [lo, hi]; primes n <= nmax."""
    def fhat2(xi):
        re = integrate.quad(lambda x: f(x) * math.cos(xi * x), lo, hi, limit=200)[0]
        im = integrate.quad(lambda x: f(x) * math.sin(xi * x), lo, hi, limit=200)[0]
        return re * re + im * im
    arch = 2 * integrate.quad(lambda xi: a_mult(xi) * fhat2(xi), 0, ximax, limit=400)[0] / (2 * math.pi)
    prime = 0.0
    for n in range(2, nmax + 1):
        c = vonmangoldt(n) / math.sqrt(n); s = math.log(n)
        if c and s < hi - lo:
            prime += c * 2 * integrate.quad(lambda x: f(x) * f(x + s), lo, hi - s, limit=200)[0]
    P = integrate.quad(lambda x: math.sqrt(2) * math.cosh(x / 2) * f(x), lo, hi)[0]
    Q = integrate.quad(lambda x: math.sqrt(2) * math.sinh(x / 2) * f(x), lo, hi)[0]
    return arch - prime + P * P - Q * Q, arch

if __name__ == "__main__":
    import parity_gap_table as t
    mp.mp.dps = 30
    for m in (3, 5):
        K = t.fc.matrix_K(m); L = math.log(m)
        c = mp.matrix([0] * (2 * m + 1)); c[m] = 1; c[m + 1] = c[m - 1] = mp.mpf(-1) / 2
        q = float((c.T * K * c)[0])
        w, _ = weil_form(lambda x: (1 - math.cos(2 * math.pi * (x + L / 2) / L)) / math.sqrt(L), -L / 2, L / 2, m)
        print(f"normalization m={m}: Weil form = {w:.12g}  c^T K c = {q:.12g}  diff = {w - q:.2e}")
    # 2) identity (6.8) on a smooth F supported in (-r, r), with an odd part
    for r, wodd in ((0.4, 0.7), (0.9, -0.5)):
        def F(x, r=r, wodd=wodd):
            if abs(x) >= r: return 0.0
            return math.exp(-1 / (1 - (x / r)**2)) * (1 + wodd * x / r)
        f = lambda x: h(x) * F(x)
        lhs, _ = weil_form(f, -r, r, 60)
        j = lambda s: math.exp(-s / 2) / (1 - math.exp(-2 * s)) if s > 1e-12 else 0.0
        B = 2.2
        def integrand(y, x):
            d = F(x) - F(y)
            return 0.0 if d == 0.0 else j(abs(x - y)) * h(x) * h(y) * d * d
        # F(x) != F(y) needs x or y in (-r, r): split the square to keep quadrature honest
        E_arch = 0.5 * (2 * integrate.dblquad(integrand, -r, r, lambda x: -B, lambda x: -r, epsabs=1e-11)[0]
                        + 2 * integrate.dblquad(integrand, -r, r, lambda x: r, lambda x: B, epsabs=1e-11)[0]
                        + integrate.dblquad(integrand, -r, r, lambda x: -r, lambda x: r, epsabs=1e-11)[0])
        E_prime = 0.0
        for n in range(2, int(math.exp(5)) + 1):
            c = vonmangoldt(n) / math.sqrt(n)
            if c:
                s = math.log(n)
                E_prime += c * integrate.quad(lambda x: h(x) * h(x + s) * (F(x + s) - F(x))**2, -r - s, r, limit=200)[0]
        mu = lambda g: integrate.quad(lambda x: 0.5 * math.cosh(x / 2) * h(x) * g(x), -r, r, limit=200)[0]
        mass = integrate.quad(lambda x: 0.5 * math.cosh(x / 2) * h(x), -4, 4, limit=200)[0]
        var = mu(lambda x: F(x)**2) - mu(F)**2
        odd = mu(lambda x: math.tanh(x / 2) * F(x))
        rhs = E_arch + E_prime - 8 * (var + odd * odd)
        print("mu mass =", mass)
        print("E_arch =", E_arch, " E_prime =", E_prime, " Var =", var, " odd =", odd)
        print(f"r={r}: LHS k[hF] =", lhs, "  RHS E_h - 8(Var+odd^2) =", rhs, "  diff =", lhs - rhs)
