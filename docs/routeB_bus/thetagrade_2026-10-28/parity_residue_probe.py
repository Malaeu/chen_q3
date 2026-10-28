"""PARITYSPLIT checks on the literal CCM matrix. DIAGNOSTIC_NEVER_A_PROOF.

Verifies Proshka's displacement identity (4.1) and determinant identity (4.8), and evaluates
the lowest-odd-pole residue R_m (4.13) and the secular function f_m (4.7) on finite cells.
Source: PROSHKA_VERDICT_PARITYSPLIT_2026-10-28.md; matrix from full_center_probe.matrix_K.
"""
import argparse
import json
import sys
from pathlib import Path

import mpmath as mp

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402


def cell(m, dps):
    mp.mp.dps = dps
    K = t.fc.matrix_K(m)
    idx = lambda n: m + n  # noqa: E731
    b = {n: n * K[idx(n), idx(0)] for n in range(-m, m + 1)}
    disp = max(abs((n - k) * K[idx(n), idx(k)] - (b[n] - b[k]))
               for n in range(-m, m + 1) for k in range(-m, m + 1) if n != k)
    E, O = t.parity_bases(m)
    Eb, Ob = E.T * K * E, O.T * K * O
    ev_e = mp.eigsy(Eb, eigvals_only=True)
    ev_o, vec_o = mp.eigsy(Ob)
    lam_e, mu, mu2 = ev_e[0], ev_o[0], ev_o[1]
    A0 = K[idx(0), idx(0)]
    beta_o = mp.matrix([mp.sqrt(2) * b[n] for n in range(1, m + 1)])
    d = mp.matrix([mp.sqrt(2) / n for n in range(1, m + 1)])
    B2inv_beta = mp.matrix([beta_o[n - 1] / n**2 for n in range(1, m + 1)])

    def f(tt):
        v = (A0 - tt) * d - B2inv_beta
        return A0 - tt + (v.T * mp.lu_solve(Ob - tt * mp.eye(m), beta_o))[0]

    tmid = (lam_e + mu) / 2
    det_ratio = mp.det(Eb - tmid * mp.eye(m + 1)) / mp.det(Ob - tmid * mp.eye(m))
    det_err = abs(det_ratio - f(tmid)) / max(abs(det_ratio), mp.mpf(10) ** (-dps + 10))
    y = vec_o[:, 0]
    v0 = (A0 - mu) * d - B2inv_beta
    R = (v0.T * y)[0] * (y.T * beta_o)[0]
    out = {"m": m, "dps": dps, "displacement_max_err": disp, "det_identity_rel_err": det_err,
           "lam_even": lam_e, "mu_odd": mu, "odd_gap_g_o": mu2 - mu,
           "f_at_midpoint": f(tmid), "R_m": R, "R_over_mu": R / mu}
    return {k: (mp.nstr(v, 12) if isinstance(v, mp.mpf) else v) for k, v in out.items()}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, nargs="+", required=True)
    ap.add_argument("--dps", type=int, default=90)
    a = ap.parse_args()
    for m in a.m:
        print(json.dumps({"status": "DIAGNOSTIC_NEVER_A_PROOF", **cell(m, a.dps)}), flush=True)
