"""PINGEOM: where exactly does the two-sided pin start, and what fixes the threshold a*? DIAGNOSTIC_NEVER_A_PROOF.
speed_S(a) = -f_S^T dq(a) f_S for the sector bottom f_S of K (S = E, O); a fake atom at shift a is pinned two-sidedly
iff speed_E(a) > 0 and speed_O(a) < 0. Fine grid in a; sign changes reported per sector.
Shape test: bottom vectors synthesized on the window (-L/2, L/2) and compared (L2 cosine) with h (MARKOV (4.3), the theta
radical vector) and odd candidates h', x h, tanh(x/2) h, sinh(x/2) h.
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
from shake_probe import q, dq  # noqa: E402

def h(x):
    x = abs(x); s = mp.mpf(0); n = 1
    while True:
        e2 = mp.e**(2 * x) * n * n
        if mp.pi * e2 > 3 * mp.mp.dps: break
        s += (16 * mp.pi**2 * e2**2 - 24 * mp.pi * e2) * mp.e**(-mp.pi * e2); n += 1
    return mp.e**(x / 2) * s
def hp(x): return mp.diff(h, x)

mp.mp.dps = int(sys.argv[1]); G = int(sys.argv[2])
for m in [int(a) for a in sys.argv[3:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m); modes = list(range(-m, m + 1))
    out = {"m": m}
    for name, B in (("E", E), ("O", O)):
        ev, V = mp.eigsy(B.T * K * B); f = B * V[:, 0]
        sp = []
        for k in range(1, G):
            a = L * k / G
            sp.append(-sum(f[i] * f[j] * dq(a, n, v, L) for i, n in enumerate(modes) for j, v in enumerate(modes)))
        ch = [float(L * (k + 1.5) / G) for k in range(len(sp) - 1) if sp[k] * sp[k + 1] < 0]
        # synthesize on (-L/2, L/2), common phase
        xs = [-L / 2 + L * (k + 0.5) / 200 for k in range(200)]
        fc = [sum(f[j] * mp.exp(2j * mp.pi * (j - m) * (x + L / 2) / L) for j in range(2 * m + 1)) for x in xs]
        kk = max(range(200), key=lambda i: abs(fc[i])); ph = fc[kk] / abs(fc[kk]); fx = [mp.re(y / ph) for y in fc]
        def cos_with(g):
            gx = [g(x) for x in xs]; num = sum(a * b for a, b in zip(fx, gx))
            return mp.nstr(abs(num) / mp.sqrt(sum(a * a for a in fx) * sum(b * b for b in gx)), 8)
        cands = {"h": h} if name == "E" else {"h'": hp, "x h": lambda x: x * h(x), "tanh h": lambda x: mp.tanh(x / 2) * h(x), "sinh h": lambda x: mp.sinh(x / 2) * h(x)}
        out[name] = {"lam0": mp.nstr(ev[0], 4), "speed_sign_changes_at_a": [round(c, 4) for c in ch],
                     "speed_at_log2": mp.nstr(-sum(f[i] * f[j] * dq(mp.log(2), n, v, L) for i, n in enumerate(modes) for j, v in enumerate(modes)), 4),
                     "cosine": {k: cos_with(g) for k, g in cands.items()}}
    print(json.dumps(out), flush=True)
