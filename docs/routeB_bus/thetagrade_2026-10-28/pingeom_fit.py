"""PINGEOM fit: do the window bottoms drift inside the xi-radical family? DIAGNOSTIC_NEVER_A_PROOF.
Even bottom fitted in span{h, h'', h''''}, odd bottom in span{h', h''', h^(5)} (all exact null vectors of the global Weil form:
transforms (iz)^k 4 xi(1/2 - iz)). Least squares on a 240-point window grid; reports normalised weights, residual, and the
pin threshold a*(m) (sign change of the odd speed) on a 300-point grid in a.
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
from shake_probe import dq  # noqa: E402

def h(x):
    x = abs(x); s = mp.mpf(0); n = 1
    while True:
        e2 = mp.e**(2 * x) * n * n
        if mp.pi * e2 > 3 * mp.mp.dps: break
        s += (16 * mp.pi**2 * e2**2 - 24 * mp.pi * e2) * mp.e**(-mp.pi * e2); n += 1
    return mp.e**(x / 2) * s

mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m); modes = list(range(-m, m + 1))
    xs = [-L / 2 + L * (k + 0.5) / 240 for k in range(240)]
    with mp.workdps(30):
        D = {k: [mp.diff(h, x, k) for x in xs] for k in range(6)}
    out = {"m": m}
    for name, B, ks in (("E", E, (0, 2, 4)), ("O", O, (1, 3, 5))):
        ev, V = mp.eigsy(B.T * K * B); f = B * V[:, 0]
        fc = [sum(f[j] * mp.exp(2j * mp.pi * (j - m) * (x + L / 2) / L) for j in range(2 * m + 1)) for x in xs]
        kk = max(range(240), key=lambda i: abs(fc[i])); ph = fc[kk] / abs(fc[kk]); y = mp.matrix([mp.re(v / ph) for v in fc])
        A = mp.matrix([[D[k][i] for k in ks] for i in range(240)])
        c = mp.lu_solve(A.T * A, A.T * y); r = y - A * c
        w = [c[i] * mp.sqrt(sum(D[ks[i]][j]**2 for j in range(240))) for i in range(3)]; s = mp.sqrt(sum(v * v for v in w))
        out[name] = {"weights_normalised": [mp.nstr(v / s, 5) for v in w], "rel_residual": mp.nstr(mp.norm(r) / mp.norm(y), 4)}
        if name == "O":
            G = 300; sp = [-sum(f[i] * f[j] * dq(L * k / G, n, v, L) for i, n in enumerate(modes) for j, v in enumerate(modes)) for k in range(1, G)]
            out["a_star"] = [round(float(L * (k + 1.5) / G), 4) for k in range(len(sp) - 1) if sp[k] * sp[k + 1] < 0]
    print(json.dumps(out), flush=True)
