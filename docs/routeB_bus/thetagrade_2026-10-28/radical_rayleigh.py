"""Does a crude structured trial vector give lam0(K_E) within a factor ~m? DIAGNOSTIC_NEVER_A_PROOF.
Trials: pure h, and the plateau radical vector F = h + s h'' + c2 h'''' (raw ratios from heatsmooth_check, m = 24),
projected on the window modes psi_n = L^{-1/2} e^{2 pi i n (x + L/2)/L}. Rayleigh quotient R(F) vs lam0(K_E), and the
even ladder shares w_i lam_i / lam0(K_E).
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
def hder(x, k):
    """Exact k-th derivative of h: each summand is a sum of c u^a e^{-pi n^2 u}, u = e^{2x}, and d/dx = 2u d/du."""
    x = abs(x) if k % 2 == 0 else x
    sgn = 1
    if k % 2 == 1 and x < 0: x, sgn = -x, -1   # odd derivative of an even function is odd
    u = mp.e**(2 * x); tot = mp.mpf(0); n = 1
    while True:
        a = mp.pi * n * n
        if a * u > 2.4 * mp.mp.prec: break
        terms = {mp.mpf(9) / 4: 16 * mp.pi**2 * n**4, mp.mpf(5) / 4: -24 * mp.pi * n**2}
        for _ in range(k):
            nt = {}
            for al, c in terms.items():
                nt[al] = nt.get(al, 0) + 2 * al * c
                nt[al + 1] = nt.get(al + 1, 0) - 2 * a * c
            terms = nt
        tot += sum(c * u**al for al, c in terms.items()) * mp.e**(-a * u); n += 1
    return sgn * tot
def h(x): return hder(x, 0)

mp.mp.dps = int(sys.argv[1]); S1, S2 = mp.mpf("0.0030819"), mp.mpf("3.82498e-6")
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m)
    evE, VE = mp.eigsy(E.T * K * E); lamE = evE[0]
    out = {"m": m, "lam0_E": mp.nstr(lamE, 4)}
    for name, F in (("h", lambda x: h(x)), ("F_plateau", lambda x: hder(x, 0) + S1 * hder(x, 2) + S2 * hder(x, 4))):
        # cosine coefficients (even): c_n = L^{-1/2} int F(x) cos(2 pi n (x + L/2)/L) dx  (real part of <psi_n, F>)
        with mp.workdps(60):
            cl = [mp.quad(lambda x: F(x) * mp.cos(2 * mp.pi * n * (x + L / 2) / L), [-L / 2, -L / 4, 0, L / 4, L / 2]) / mp.sqrt(L) for n in range(-m, m + 1)]
        c = mp.matrix(cl)
        R = (c.T * K * c)[0] / (c.T * c)[0]
        a = (E * VE).T * c; cc = (c.T * c)[0]
        shares = [a[i]**2 / cc * evE[i] / lamE for i in range(len(evE))]
        out[name] = {"R_over_lam0E": mp.nstr(R / lamE, 5), "shares": [mp.nstr(x, 3) for x in shares[:8]]}
    print(json.dumps(out), flush=True)
