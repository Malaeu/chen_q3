"""Upper bound for lambda_min(E) from explicit even trial vectors. DIAGNOSTIC_NEVER_A_PROOF.

Trial vectors from full_center_probe.gaussian_plane (theta-Gaussian Fourier coefficients bs and its
companion ds, both even). U1 = Rayleigh(bs), U2 = Ritz bottom on span{bs, ds}; both >= lambda_min(E)
because the vectors are even. Question: U/lambda and U vs mu = lambda_min(O) on m = 2..16.
"""
import argparse
import json
import sys
from pathlib import Path

import mpmath as mp

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--m", type=int, nargs="+", required=True)
    ap.add_argument("--dps", type=int, default=80); a = ap.parse_args()
    for m in a.m:
        mp.mp.dps = a.dps
        K = t.fc.matrix_K(m); Eb_, Ob_ = (lambda E, O: (E.T * K * E, O.T * K * O))(*t.parity_bases(m))
        lam = mp.eigsy(Eb_, eigvals_only=True)[0]; mu = mp.eigsy(Ob_, eigvals_only=True)[0]
        Pi, _, _ = t.fc.gaussian_plane(m)
        # recover bs, ds: rebuild them the same way gaussian_plane does (it returns only Pi), so use Pi's range
        ev, V = mp.eigsy(Pi)
        cols = [V[:, i] for i in range(Pi.rows) if ev[i] > mp.mpf('0.5')]
        Q = mp.matrix(Pi.rows, len(cols))
        for j, c in enumerate(cols):
            for i in range(Pi.rows): Q[i, j] = c[i]
        Kp = Q.T * K * Q
        U2 = mp.eigsy(Kp, eigvals_only=True)[0]
        odd_leak = max(abs(Q[i, j] - Q[2 * m - i, j]) for i in range(Pi.rows) for j in range(Q.cols))
        out = {"m": m, "dps": a.dps, "lam": lam, "mu": mu, "U_plane": U2, "U_over_lam": U2 / lam,
               "U_below_mu": bool(U2 < mu), "mu_over_U": mu / U2, "plane_dim": Q.cols, "plane_odd_leak": odd_leak}
        print(json.dumps({k: (mp.nstr(v, 8) if isinstance(v, mp.mpf) else v) for k, v in out.items()}), flush=True)
