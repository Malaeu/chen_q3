"""Does the geometry of the bottom survive when the sign breaks? DIAGNOSTIC_NEVER_A_PROOF.
Shift log 2 (and its powers, Beurling-style) by eps at m = 12; compare the new even bottom with the old one:
eigenvalue (sign) and 1 - |cos| of the eigenvectors (shape).
"""
import sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
from shake_probe import q, prime_powers  # noqa: E402
mp.mp.dps = 80
m = 12; K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m); modes = list(range(-m, m + 1))
ev0, V0 = mp.eigsy(E.T * K * E); v0 = V0[:, 0]
for eps in ("-1e-26", "-1e-20", "-1e-12", "-1e-6"):
    e = mp.mpf(eps); dK = mp.matrix(K.rows)
    for a, n in enumerate(modes):
        for b, v in enumerate(modes):
            dK[a, b] = -sum(mp.mangoldt(k) / mp.sqrt(k) * (q(mp.log(k) + j * e, n, v, L) - q(mp.log(k), n, v, L)) for j, k in prime_powers(2, m))
    ev, V = mp.eigsy(E.T * (K + dK) * E); c = abs((V[:, 0].T * v0)[0])
    print(f"eps={eps}: lam0_E old {mp.nstr(ev0[0], 4)} -> new {mp.nstr(ev[0], 4)}   shape change 1-|cos| = {mp.nstr(1 - c, 3)}")

