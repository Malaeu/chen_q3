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
    # Closed form from (4.8) at a simple odd bottom: R = prod_i (lam_i^E - mu) / prod_{j>=2} (mu_j - mu).
    # So sign R = (-1)^(number of even eigenvalues below mu).
    num = mp.fprod([ev - mu for ev in ev_e])
    den = mp.fprod([ev - mu for ev in ev_o[1:]])
    R_closed_err = abs(num / den - R) / abs(R)
    n_even_below = sum(1 for ev in ev_e if ev < mu)
    # Parity pattern of the full spectrum, left to right: does it alternate E,O,E,O,...?
    merged = sorted([(ev, "E") for ev in ev_e] + [(ev, "O") for ev in ev_o])
    pattern = "".join(p for _, p in merged)
    alternates = all(pattern[i] != pattern[i + 1] for i in range(len(pattern) - 1))
    # Proshka (4.15)-(4.16) bracket on this cell.
    Pi_beta = y * (y.T * beta_o)[0]
    rest = beta_o - Pi_beta
    C = abs(A0 - mu) + 1 + mp.norm(d) * mp.norm(Pi_beta) + (mp.norm(v0) + mp.norm(d)) * mp.norm(rest) / (mu2 - mu)
    eps = min(mp.mpf(1), -R / (2 * C)) if R < 0 else mp.mpf(0)
    # Observer identity: f(t) = 1/g(t), g(t) = <eta,(K-t)^-1 e0> = h^T (E-t)^-1 e0 = det(O-t)/det(E-t),
    # so g(t) = sum_i w_i/(lam_i - t) with w_i = (h.xi_i)(xi_i)_0 over even eigenvectors, sum_i w_i = 1.
    h = mp.matrix([1] + [mp.sqrt(2)] * m)
    e0 = mp.matrix([1] + [0] * m)
    g_mid = (h.T * mp.lu_solve(Eb - tmid * mp.eye(m + 1), e0))[0]
    ev_e2, VE = mp.eigsy(Eb)
    w = [(h.T * VE[:, i])[0] * VE[0, i] for i in range(m + 1)]
    W = [mp.fsum(w[:k + 1]) for k in range(m + 1)]
    out = {"m": m, "dps": dps, "displacement_max_err": disp, "det_identity_rel_err": det_err,
           "lam_even": lam_e, "mu_odd": mu, "odd_gap_g_o": mu2 - mu,
           "f_at_midpoint": f(tmid), "R_m": R, "R_over_mu": R / mu,
           "R_closed_form_rel_err": R_closed_err, "n_even_below_mu": n_even_below,
           "spectrum_parity_pattern": pattern, "parity_alternates": alternates,
           "v0_dot_y": (v0.T * y)[0], "y_dot_beta_o": (y.T * beta_o)[0],
           "C_m": C, "eps_m": eps, "eps_over_parity_gap": eps / (mu - lam_e),
           "f_at_mu_minus_eps": f(mu - eps) if eps > 0 else None,
           "fg_minus_1": abs(f(tmid) * g_mid - 1), "sum_w": mp.fsum(w), "w0": w[0],
           "w_signs": "".join("+" if x > 0 else "-" for x in w), "min_cum_W": min(W),
           "argmin_cum_W": W.index(min(W)), "neg_w_total": mp.fsum(x for x in w if x < 0)}
    return {k: (mp.nstr(v, 12) if isinstance(v, mp.mpf) else v) for k, v in out.items()}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, nargs="+", required=True)
    ap.add_argument("--dps", type=int, default=90)
    a = ap.parse_args()
    for m in a.m:
        print(json.dumps({"status": "DIAGNOSTIC_NEVER_A_PROOF", **cell(m, a.dps)}), flush=True)
