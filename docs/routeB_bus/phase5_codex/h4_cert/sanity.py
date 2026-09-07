"""STEP 0 (DIAGNOSTIC, float/mpmath): reproduce the scalar floor F(h4) ~ 0.0035.

h4(x) = sum_{j=0..4} A_j (x/delta)^{2j} on |x|<delta, zero-extended; N_4 = 1.
Conventions: SCALARFLOOR verdict (1)-(3), (35); RESONANCE (2), (10).
"""
import numpy as np, mpmath as mp

a = np.log(2.0); r = 2.0**-0.5
d0 = (np.log(3.0) - np.log(2.0)) / 8.0
di2 = 1.0 / d0**2
A = np.array([-8*di2 - 0.25, 72*di2 + 1.0, -120*di2 - 1.5, 56*di2 + 1.0, -0.25])

# ---- H_4 by (35)
H4 = 2*d0*sum(A[i]*A[j]/(2*(i+j)+1) for i in range(5) for j in range(5))
print(f"delta      = {d0!r}")
print(f"A          = {A}")
print(f"H_4 (35)   = {H4:.6f}   (target 301750.44686)")

# ---- moments  int h e^{+-x/2} dx  (must vanish)
for sg in (+1, -1):
    f = lambda x: sum(A[j]*(x/d0)**(2*j) for j in range(5))*mp.e**(sg*x/2)
    print(f"  moment sign {sg:+d}: {mp.quad(f, [-d0, 0, d0])}")

# ---- exact Fourier transform:  hhat(xi) = 2 delta sum_j A_j C_{2j}(delta xi)
def C_m(m, c):
    """int_0^1 z^m cos(c z) dz by its entire power series."""
    tot = 0.0; t = 1.0; n = 0
    while True:
        tot += t/(m + 2*n + 1)
        n += 1
        t *= -c*c/((2*n)*(2*n-1))
        if abs(t) < 1e-18*max(abs(tot), 1e-300) and n > abs(c):
            break
        if n > 4000: raise RuntimeError
    return tot

def hhat(xi):
    c = d0*xi
    return 2*d0*sum(A[j]*C_m(2*j, c) for j in range(5))

# Parseval check: H = (1/2pi) int |hhat|^2
xg = np.arange(0.0, 20000.0, 0.05)
hh = np.array([hhat(x) for x in xg])
print(f"Parseval   = {2*np.trapz(hh**2, xg)/(2*np.pi):.6f}  vs H_4 = {H4:.6f}")

# ---- gamma_2
def gamma2(xi):
    from scipy.special import loggamma
    g = np.exp(-1j*xi*np.log(np.pi) + loggamma(0.25+0.5j*xi) - loggamma(0.25-0.5j*xi))
    return g*(1-r*np.exp(1j*a*xi))/(1-r*np.exp(-1j*a*xi))

# ---- t_2 from the mellin_d2 closed form (mpmath), J_U = 55
import sys
sys.path.insert(0, '/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/mellin_d2')
import core

def t2(xi, JU=55):
    tot = mp.mpf(-1)/2*core.J_closed(mp.pi, -xi, 40)
    for j in range(JU+1):
        tot += mp.mpf(1)/2*core.J_closed(2*mp.pi*mp.mpf(2)**j, -xi, 40)
    return complex(tot/mp.pi)

if __name__ == '__main__':
    from multiprocessing import Pool
    XI = np.round(np.arange(0.0, 600.0001, 0.25), 4)
    with Pool(22) as P:
        T2 = np.array(P.map(t2, XI, chunksize=8))
    hq = np.array([hhat(x) for x in XI])
    W = (1-np.cos(a*XI))*hq**2/H4
    print(f"int W over |xi|<=600  = {2*np.trapz(W, XI):.6f}  (target 2pi = {2*np.pi:.6f})")
    ell = 2*np.real(gamma2(XI)*T2)
    F = -2*np.trapz(W*ell, XI)
    print(f"F(h4) = -int W ell_2  = {F:+.6f}   (target ~ +0.003509)")
    np.savez('/home/chirurgie/.claude/jobs/4b35770d/tmp/h4_cert/sanity.npz', xi=XI, t2=T2, hhat=hq, ell=ell)
