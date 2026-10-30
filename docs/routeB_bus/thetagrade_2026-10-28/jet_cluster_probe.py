"""Subspace version of fixed-jet geometry. DIAGNOSTIC_NEVER_A_PROOF.
J_k = span{P_m h, P_m h'', ..., P_m h^(2k)} (even). For k = 0..3: cosines of principal angles between J_k and the span
of the lowest k+1 even eigenvectors, the residual delta_k = max_{u in J_k, |u|=1} ||K u||, and lam_{k+1}(K_E).
RH-implying shape: cosines -> 1 and delta_k << lam_{k+1} cofinally.
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
from radical_rayleigh import hder  # noqa: E402

def orth(cols):
    Q = []
    for c in cols:
        w = c.copy()
        for q in Q:
            w = w - (q.T * w)[0] * q
        for q in Q:
            w = w - (q.T * w)[0] * q
        Q.append(w / mp.norm(w))
    M = mp.matrix(cols[0].rows, len(Q))
    for j, q in enumerate(Q):
        for i in range(q.rows):
            M[i, j] = q[i]
    return M

mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, _ = t.parity_bases(m)
    cols = []
    for k in range(4):
        with mp.workdps(60):
            c = mp.matrix([mp.quad(lambda x: hder(x, 2 * k) * mp.cos(2 * mp.pi * n * (x + L / 2) / L), [-L / 2, -L / 4, 0, L / 4, L / 2]) / mp.sqrt(L)
                           for n in range(-m, m + 1)])
        cols.append(c)
    ev, V = mp.eigsy(E.T * K * E); EV = E * V
    out = {"m": m, "lam": [mp.nstr(x, 3) for x in ev[:6]]}
    for k in range(4):
        Q = orth(cols[:k + 1])
        Vl = mp.matrix(EV.rows, k + 1)
        for i in range(EV.rows):
            for j in range(k + 1):
                Vl[i, j] = EV[i, j]
        cos = sorted(mp.svd_r(Vl.T * Q, compute_uv=False), reverse=True)
        dk = max(mp.svd_r(K * Q, compute_uv=False))
        out[f"k{k}"] = {"cos_min": mp.nstr(min(cos), 8), "delta_k": mp.nstr(dk, 3), "lam_k+1": mp.nstr(ev[k + 1], 3),
                        "delta_over_lam_next": mp.nstr(dk / ev[k + 1], 3)}
    print(json.dumps(out), flush=True)
