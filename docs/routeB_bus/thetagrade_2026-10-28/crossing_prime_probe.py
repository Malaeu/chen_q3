"""Literature-agent candidate check (Barta / positive supersolution via A_abs in the odd sector). DIAGNOSTIC_NEVER_A_PROOF.
Folded odd sector: archimedean and pole couplings are Markov-type (negative off-diagonal); the only positive couplings come
from prime jumps a_n = log n that cross the window centre (y < 0 < y + a_n). For the odd bottom f of K_O (positive on the
right half-window), A_abs(|f|) = k[f] - 2T with T = sum_n c_n 2 int_cross f(|y|) f(y + a_n) dy. If 2T >> lam0(K_O), then
lam_min(A_abs) < 0 and the comparison certificate cannot reach the Weil sign.
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
    ev, V = mp.eigsy(O.T * K * O); c = O * V[:, 0]
    def fc(y): return sum(c[j] * mp.exp(2j * mp.pi * (j - m) * (y + L / 2) / L) for j in range(2 * m + 1)) / mp.sqrt(L)
    ph = fc(L / 4); ph = ph / abs(ph)
    f = lambda y: mp.re(fc(y) / ph)
    right = [f(L / 2 * k / 40) for k in range(1, 40)]
    sign_changes = sum(1 for a, b in zip(right, right[1:]) if a * b < 0)
    T = mp.mpf(0)
    for n in range(2, m):
        cn = mp.mangoldt(n) / mp.sqrt(n)
        if cn == 0: continue
        a = mp.log(n); lo, hi = max(-L / 2, -a), min(mp.mpf(0), L / 2 - a)
        if lo < hi: T += cn * 2 * mp.quad(lambda y: f(-y) * f(y + a), [lo, hi])
    print(json.dumps({"m": m, "lam0_K_O": mp.nstr(ev[0], 5), "T_crossing": mp.nstr(T, 5), "ratio_2T_over_lam0": mp.nstr(2 * T / ev[0], 5),
                      "sign_changes_right_half": sign_changes, "A_abs_value_at_abs_f": mp.nstr(ev[0] - 2 * T, 5)}), flush=True)
