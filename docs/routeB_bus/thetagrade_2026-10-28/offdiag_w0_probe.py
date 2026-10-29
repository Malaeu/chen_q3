"""Off-diagonal w0 probe: literal CCM matrix with N (modes -N..N) and lambda^2 (prime cutoff,
L = log lambda^2) independent. DIAGNOSTIC_NEVER_A_PROOF.

Question: does the STIELTJES lead weight w0 > 0 (and all Abel sums W_k > 0, and G1a
lambda_min(E) < lambda_min(O)) hold off our diagonal N = lambda^2 = m?
Matrix: copy of full_center_probe.matrix_K with m split into (N, lam2); check_diagonal()
asserts equality with the original on N = lam2 = m. Weights as in parity_residue_probe.cell.
"""
import argparse
import json
import sys
from pathlib import Path

import mpmath as mp

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402


def matrix_K2(N, lam2):
    L = mp.log(lam2); modes = list(range(-N, N + 1)); K = mp.zeros(len(modes))

    def q(x, n, j):
        if n == j: return 2 * (L - x) / L * mp.cos(2 * mp.pi * n * x / L)
        return (mp.sin(2 * mp.pi * j * x / L) - mp.sin(2 * mp.pi * n * x / L)) / (mp.pi * (n - j))

    def mang(k):
        for p in range(2, k + 1):
            if any(p % d == 0 for d in range(2, int(p**.5) + 1)): continue
            a = p
            while a < k: a *= p
            if a == k: return mp.log(p)
        return mp.mpf(0)
    grid = [L * k / 8 for k in range(9)]
    moments = {0: mp.mpf(0)}; diagonals = {}
    for n in range(N + 1):
        omega = 2 * mp.pi * n / L
        if n:
            sn = mp.quad(lambda x: omega / 2 if not x else mp.exp(x / 2) * mp.sin(omega * x) / (2 * mp.sinh(x)), grid)
            moments[n] = sn; moments[-n] = -sn
        diagonals[n] = mp.quad(lambda x: mp.mpf('0.5') - 1 / L if not x else (mp.exp(x / 2) * q(x, n, n) - 2) / (2 * mp.sinh(x)), grid)
    constant = mp.euler + mp.log(4 * mp.pi * mp.tanh(L / 2))
    kmax = int(mp.floor(lam2))
    for i, n in enumerate(modes):
        for j in range(i, len(modes)):
            v = modes[j]
            w02 = 32 * L * mp.sinh(L / 4)**2 * (L**2 - 16 * mp.pi**2 * v * n) / ((L**2 + 16 * mp.pi**2 * v * v) * (L**2 + 16 * mp.pi**2 * n * n))
            wr = constant + diagonals[abs(n)] if n == v else (moments[v] - moments[n]) / (mp.pi * (n - v))
            prime = mp.fsum(mang(k) / mp.sqrt(k) * q(mp.log(k), n, v) for k in range(2, kmax + 1))
            K[i, j] = K[j, i] = w02 - wr - prime
    return K


def check_diagonal(m):
    A, B = matrix_K2(m, m), t.fc.matrix_K(m)
    return max(abs(A[i, j] - B[i, j]) for i in range(A.rows) for j in range(A.cols))


def cell(N, lam2, dps):
    mp.mp.dps = dps
    K = matrix_K2(N, mp.mpf(lam2))
    E, O = t.parity_bases(N)
    Eb, Ob = E.T * K * E, O.T * K * O
    ev_e, VE = mp.eigsy(Eb)
    ev_o = mp.eigsy(Ob, eigvals_only=True)
    h = mp.matrix([1] + [mp.sqrt(2)] * N)
    w = [(h.T * VE[:, i])[0] * VE[0, i] for i in range(N + 1)]
    W = [mp.fsum(w[:k + 1]) for k in range(N + 1)]
    out = {"N": N, "lam2": lam2, "dps": dps, "lam_even": ev_e[0], "mu_odd": ev_o[0],
           "G1a": bool(ev_e[0] < ev_o[0]), "even_gap": ev_e[1] - ev_e[0], "w0": w[0],
           "min_cum_W": min(W), "argmin_cum_W": W.index(min(W)), "sum_w": mp.fsum(w),
           "w_signs": "".join("+" if x > 0 else "-" for x in w)}
    return {k: (mp.nstr(v, 10) if isinstance(v, mp.mpf) else v) for k, v in out.items()}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="+", required=True)
    ap.add_argument("--lam2", type=float, nargs="+", required=True)
    ap.add_argument("--dps", type=int, default=50)
    ap.add_argument("--check", type=int, nargs="*", default=[])
    a = ap.parse_args()
    for m in a.check:
        mp.mp.dps = a.dps
        print(json.dumps({"check_diagonal_m": m, "max_abs_diff": mp.nstr(check_diagonal(m), 5)}), flush=True)
    for N in a.N:
        for l2 in a.lam2:
            print(json.dumps({"status": "DIAGNOSTIC_NEVER_A_PROOF", **cell(N, l2, a.dps)}), flush=True)
