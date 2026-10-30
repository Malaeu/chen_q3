"""THETAGRADE Q2 first fact: signed parity gap D_m on the literal CCM matrix.

DIAGNOSTIC_NEVER_A_PROOF. Finite cells test a claim; they never supply a cofinal quantifier.
Sources: matrix_K and the selected reference row are reused unchanged from
../fokas_k_sign_2026-09-25/full_center_probe.py and rectangle_probe.py.
Reflection R: mode n -> -n (CCMFiniteWeilParity.lean:24). eta = all-ones (CCMFiniteWeilSourceMatrix.lean:51).
"""
import argparse
import json
import sys
import time
from functools import lru_cache
from pathlib import Path

import mpmath as mp

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fokas_k_sign_2026-09-25"))
import full_center_probe as fc  # noqa: E402
import rectangle_probe as rp  # noqa: E402

rp._mp_kernel = lru_cache(maxsize=None)(rp._mp_kernel)


def selected_row(m):
    intervals = rp.bracket(m)
    c0 = sum(intervals[0]) / 2
    c4 = sum(intervals[4]) / 2
    p0 = rp.recurrence(m, c0)[0]
    p4 = rp.recurrence(m, c4)[0]
    F = rp.F_matrix(m)
    return F * mp.matrix([(-1) ** k * (p0[k] - p4[k]) for k in range(1, 6 * m)])


def parity_bases(m):
    size = 2 * m + 1
    E = mp.zeros(size, m + 1)
    O = mp.zeros(size, m)
    E[m, 0] = 1
    for n in range(1, m + 1):
        E[m + n, n] = 1 / mp.sqrt(2)
        E[m - n, n] = 1 / mp.sqrt(2)
        O[m + n, n - 1] = 1 / mp.sqrt(2)
        O[m - n, n - 1] = -1 / mp.sqrt(2)
    return E, O


def reflect(v, m):
    return mp.matrix([v[2 * m - i] for i in range(2 * m + 1)])


def complement_basis(q):
    """Orthonormal basis of q-perp via one Householder reflection sending q to e_k."""
    size = q.rows
    k = max(range(size), key=lambda i: abs(q[i]))
    e = mp.zeros(size, 1)
    e[k] = 1 if q[k] >= 0 else -1
    w = q - e
    H = mp.eye(size) - 2 * (w * w.T) / (w.T * w)[0]
    cols = [j for j in range(size) if j != k]
    B = mp.zeros(size, size - 1)
    for c, j in enumerate(cols):
        for i in range(size):
            B[i, c] = H[i, j]
    return B


def cell(m, dps):
    mp.mp.dps = dps
    t = time.time()
    K = fc.matrix_K(m)
    E, O = parity_bases(m)
    lam_even = mp.eigsy(E.T * K * E, eigvals_only=True)[0]
    lam_odd = mp.eigsy(O.T * K * O, eigvals_only=True)[0]
    vals, vecs = mp.eigsy(K)
    xi = vecs[:, 0]
    lam1, lam2 = vals[0], vals[1]
    size = 2 * m + 1
    eta_cos = abs(mp.fsum(xi)) / (mp.norm(xi) * mp.sqrt(size))
    xi_parity = mp.norm(xi - reflect(xi, m)) / mp.norm(xi)

    z = selected_row(m)
    k = max(range(z.rows), key=lambda i: abs(z[i]))
    phase = mp.conj(z[k]) / abs(z[k])
    zp = z * phase
    imag_residue = mp.norm(mp.matrix([mp.im(x) for x in zp])) / mp.norm(zp)
    q = mp.matrix([mp.re(x) for x in zp])
    q = q / mp.norm(q)
    q_parity = mp.norm(q - reflect(q, m))
    a = (q.T * K * q)[0]
    r = K * q - a * q
    rnorm = mp.norm(r)
    B = complement_basis(q)
    delta = mp.eigsy(B.T * K * B, eigvals_only=True)[0] - a
    overlap = abs((xi.T * q)[0]) / mp.norm(xi)
    alpha = mp.sqrt(max(mp.mpf(0), 1 - overlap ** 2))

    D = lam_odd - lam_even
    out = {
        "m": m, "dps": dps, "seconds": round(time.time() - t, 1),
        "lam_even": lam_even, "lam_odd": lam_odd, "D_m": D,
        "lam1": lam1, "lam2": lam2, "simple_gap": lam2 - lam1,
        "eta_cos_ground": eta_cos, "ground_parity_defect": xi_parity,
        "q_parity_defect": q_parity, "q_phase_imag_residue": imag_residue, "a_m": a, "r_norm": rnorm,
        "delta_m": delta, "alpha_m": alpha,
        "D_over_r": D / rnorm if rnorm else mp.inf,
        "delta_over_r": delta / rnorm if rnorm else mp.inf,
        "a_minus_lam_even": a - lam_even,
    }
    return {k: (mp.nstr(v, 20) if isinstance(v, mp.mpf) else v) for k, v in out.items()}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, nargs="+", required=True)
    ap.add_argument("--dps", type=int, default=60)
    args = ap.parse_args()
    for m in args.m:
        print(json.dumps({"status": "DIAGNOSTIC_NEVER_A_PROOF", **cell(m, args.dps)}), flush=True)
