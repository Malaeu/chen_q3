"""CONFINE verdict (3.9) control: ||K_m coeff(P_m h)|| / ||coeff|| must fall faster than every power of m.
P_m h = window projection of the theta radical vector h (the cutoff chi is numerically irrelevant: h(L/2) ~ m^2.25 e^{-pi m}).
DIAGNOSTIC_NEVER_A_PROOF.
"""
import sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
from radical_rayleigh import h  # noqa: E402  (module body guarded by argv slice: runs no m)

mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m)
    c = mp.matrix([mp.quad(lambda x: h(x) * mp.cos(2 * mp.pi * n * (x + L / 2) / L), [-L / 2, -L / 4, 0, L / 4, L / 2]) / mp.sqrt(L)
                   for n in range(-m, m + 1)])
    nc = mp.norm(c); Kc = mp.norm(K * c) / nc; R = (c.T * K * c)[0] / nc**2
    print(f"m={m}: ||K u||/||u|| = {mp.nstr(Kc,5)}  Rayleigh = {mp.nstr(R,5)}  ||u|| = {mp.nstr(nc,8)}", flush=True)
