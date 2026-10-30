"""Two secular scalars behind window positivity under the PF split K = G + kappa (u u^T - v v^T). DIAGNOSTIC_NEVER_A_PROOF.
u_n = L/(L^2+16 pi^2 n^2) (even), v_n = 4 pi n/(L^2+16 pi^2 n^2) (odd), kappa = 32 L sinh^2(L/4) (W02 of matrix_K).
If G_E has exactly one negative eigenvalue: K_E >= 0 <=> s_E = 1 + kappa u^T G^-1 u <= 0.
If G_O >= 0: K_O >= 0 <=> s_O = 1 - kappa v^T G^-1 v >= 0.
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402

mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); n = 2 * m + 1
    u = mp.matrix([L / (L**2 + 16 * mp.pi**2 * a * a) for a in range(-m, m + 1)])
    v = mp.matrix([4 * mp.pi * a / (L**2 + 16 * mp.pi**2 * a * a) for a in range(-m, m + 1)])
    kap = 32 * L * mp.sinh(L / 4)**2
    W = kap * (u * u.T - v * v.T)
    G = K - W
    E, O = t.parity_bases(m)
    gE = mp.eigsy(E.T * G * E, eigvals_only=True); gO = mp.eigsy(O.T * G * O, eigvals_only=True)
    sE = 1 + kap * (u.T * mp.lu_solve(G, u))[0]; sO = 1 - kap * (v.T * mp.lu_solve(G, v))[0]
    kE = mp.eigsy(E.T * K * E, eigvals_only=True)[0]
    print(json.dumps({"m": m, "W02_rebuild_err": mp.nstr(mp.mnorm(K - G - W, 1), 3) if False else "n/a",
        "G_E_neg_count": sum(1 for x in gE if x < 0), "G_E_l0": mp.nstr(gE[0], 5), "G_E_l1": mp.nstr(gE[1], 5),
        "G_O_l0": mp.nstr(gO[0], 5), "G_O_neg_count": sum(1 for x in gO if x < 0),
        "kappa": mp.nstr(kap, 5), "s_E": mp.nstr(sE, 5), "s_O": mp.nstr(sO, 5), "lam0_K_E": mp.nstr(kE, 5)}), flush=True)
