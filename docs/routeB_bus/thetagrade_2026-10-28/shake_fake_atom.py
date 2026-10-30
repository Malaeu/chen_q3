"""SHAKE control: is the two-sided pin arithmetic or a shape property of the bottom vectors? DIAGNOSTIC_NEVER_A_PROOF.
A prime atom at position a with weight w enters K as -w q(a, n, v). For a FAKE atom at any a in (0, L):
  pos_E(a) = -f_E^T dq(a) f_E  (speed of lam0(K_E) when the atom moves right), pos_O(a) likewise for f_O.
Two-sided pin at a <=> pos_E(a) > 0 and pos_O(a) < 0. If this holds for (almost) all a, the pin is generic geometry.
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
from shake_probe import q, dq  # noqa: E402

mp.mp.dps = int(sys.argv[1]); G = 60
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m); modes = list(range(-m, m + 1))
    vecs = {}
    for name, B in (("E", E), ("O", O)):
        ev, V = mp.eigsy(B.T * K * B); vecs[name] = B * V[:, 0]
    def qf(f, fn, a):
        return sum(f[i] * f[j] * fn(a, n, v, L) for i, n in enumerate(modes) for j, v in enumerate(modes))
    grid = [L * k / G for k in range(1, G)]
    pin, rows = 0, []
    for a in grid:
        pe = -qf(vecs["E"], dq, a); po = -qf(vecs["O"], dq, a)
        two = pe > 0 and po < 0; pin += two
        rows.append((float(a / L), two, mp.nstr(pe, 3), mp.nstr(po, 3)))
    logs = {n: float(mp.log(n) / L) for n in range(2, m) if mp.mangoldt(n) > 0}
    print(json.dumps({"m": m, "two_sided_fraction": f"{pin}/{G - 1}",
                      "not_pinned_at_a_over_L": [r[0] for r in rows if not r[1]],
                      "prime_power_positions_a_over_L": logs}), flush=True)
