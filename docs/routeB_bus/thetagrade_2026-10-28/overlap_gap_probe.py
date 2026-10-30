"""Can the quasimode u_m = P_m h force overlap with the even bottom? DIAGNOSTIC_NEVER_A_PROOF.
Bound: mass of u on levels |lam_i| >= mu is <= delta^2/mu^2, delta = ||K u||/||u||. Reports the even spectrum, delta,
how many levels lie below delta, weights w_i of u on each level, and the bound 1 - delta^2/lam_1^2.
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
from radical_rayleigh import h  # noqa: E402

mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, _ = t.parity_bases(m)
    with mp.workdps(50):
        c = mp.matrix([mp.quad(lambda x: h(x) * mp.cos(2 * mp.pi * n * (x + L / 2) / L), [-L / 2, -L / 4, 0, L / 4, L / 2]) / mp.sqrt(L)
                       for n in range(-m, m + 1)])
    c = c / mp.norm(c)
    delta = mp.norm(K * c)
    ev, V = mp.eigsy(E.T * K * E)
    a = (E * V).T * c
    w = [a[i]**2 for i in range(len(ev))]
    below = sum(1 for x in ev if abs(x) < delta)
    print(json.dumps({"m": m, "delta": mp.nstr(delta, 4), "levels_below_delta": below, "dim_E": len(ev),
                      "lam": [mp.nstr(x, 3) for x in ev[:8]], "w": [mp.nstr(x, 3) for x in w[:8]],
                      "mass_below_delta": mp.nstr(sum(w[i] for i in range(len(ev)) if abs(ev[i]) < delta), 6),
                      "bound_1_minus_d2_over_lam1sq": mp.nstr(1 - delta**2 / ev[1]**2, 4)}), flush=True)
