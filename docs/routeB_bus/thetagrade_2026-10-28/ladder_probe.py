"""Ladder of the translation mode (CONFINE Q2 follow-up). DIAGNOSTIC_NEVER_A_PROOF.
g = diag(2 pi n/L) f_E. For every odd level i: share_i = w_i lam_i / lam0(K_O), w_i = |<g, v_i>|^2 / ||g||^2.
C_m = R(g) / lam0(K_O) = sum_i share_i. Also R(g)/lam0(K_E) (the G1a slack) and lam0(K_O)/lam0(K_E).
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m)
    evE, VE = mp.eigsy(E.T * K * E); f = E * VE[:, 0]; lamE = evE[0]
    evO, VO = mp.eigsy(O.T * K * O); lamO = evO[0]
    g = mp.diag([2 * mp.pi * k / L for k in range(-m, m + 1)]) * f; gg = (g.T * g)[0]
    a = (O * VO).T * g
    share = [a[i]**2 / gg * evO[i] / lamO for i in range(len(evO))]
    C = sum(share); R = C * lamO
    print(json.dumps({"m": m, "lam0_E": mp.nstr(lamE, 4), "lam0_O": mp.nstr(lamO, 4), "C_m": mp.nstr(C, 5),
                      "slack_R_over_lamE": mp.nstr(R / lamE, 5), "gap_ratio_O_over_E": mp.nstr(lamO / lamE, 5),
                      "shares": [mp.nstr(s, 3) for s in share], "levels": [mp.nstr(x, 3) for x in evO]}), flush=True)
