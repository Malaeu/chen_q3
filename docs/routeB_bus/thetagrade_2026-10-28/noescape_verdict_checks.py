"""Observer checks of the NOESCAPE verdict (2026-10-30). DIAGNOSTIC_NEVER_A_PROOF.
1. L14 counterexample (5.6): exact rationals, count, Delta^2 < mu^2, overlap t^2.
2. Normalisation (1.2): hat h(t) = int h e^{-itx} dx equals 4 Xi(t).
3. Exterior size: h(b), ||h_out||, hat h_out(omega_{m+1}) vs H(omega_{m+1}) at m = 16, 20.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from radical_rayleigh import h  # noqa: E402

# 1. L14
for m in range(2, 7):
    eps = Fr(1, 2 ** (m * m))
    coeff = [Fr(1, 2 ** j) for j in range(m + 1)]
    nrm2 = sum(c * c for c in coeff)
    t2 = coeff[m] ** 2 / nrm2
    lam = [eps] * m + [eps * eps]
    count = sum(1 for x in lam if x < eps)
    Delta2 = sum(l * l * c * c for l, c in zip(lam, coeff)) / nrm2
    print(f"L14 m={m}: count={count}  Delta2<mu2={Delta2 < eps*eps}  Delta/mu={float((Delta2/(eps*eps))**0.5):.6f}  t2={float(t2):.3e}")

mp.mp.dps = 30
def Xi(t):
    s = mp.mpf(1) / 2 + 1j * t
    return mp.re(s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s))

# 2. normalisation at t = 0, 3
for t in [0, 3]:
    hh = mp.quad(lambda x: h(x) * mp.cos(t * x), [-mp.inf, -2, -1, 0, 1, 2, mp.inf])
    print(f"hat h({t}) = {mp.nstr(hh, 15)}   4 Xi({t}) = {mp.nstr(4 * Xi(t), 15)}")

# 3. exterior sizes
for m in [16, 20]:
    L = mp.log(m); b = L / 2; om = 2 * mp.pi * (m + 1) / L
    hb = h(b)
    out_norm = mp.sqrt(2 * mp.quad(lambda x: h(x) ** 2, [b, b + 1, mp.inf]))
    hout_hat = 2 * mp.quad(lambda x: h(x) * mp.cos(om * x), [b, b + mp.mpf(1) / 4, b + 1, mp.inf])
    print(f"m={m}: h(b)={mp.nstr(hb, 4)}  ||h_out||={mp.nstr(out_norm, 4)}  e^(-pi m)={mp.nstr(mp.exp(-mp.pi*m), 4)}  "
          f"hat h_out(om_{m+1})={mp.nstr(hout_hat, 4)}  H(om_{m+1})={mp.nstr(4*Xi(om), 4)}")
