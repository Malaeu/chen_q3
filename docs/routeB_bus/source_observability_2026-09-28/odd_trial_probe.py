"""Exploratory CCM odd-sector diagnostic; never an interval certificate.

Uses the exact trial prescription of REQ-2026-10-06-ODD-SECULAR-SOURCE-SIGN,
approximating its full theta sum by full_center_probe's documented cutoff.
No eventual conclusion follows from these finite samples.
"""
import argparse
import json
from pathlib import Path
import sys

import mpmath as mp

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fokas_k_sign_2026-09-25"))
import full_center_probe as fc


def sample(m, dps):
    mp.mp.dps = dps
    K = fc.matrix_K(m)
    plane, parity_error, cutoff = fc.gaussian_plane(m)
    _, vectors = mp.eigsy(plane)
    Q = vectors[:, vectors.cols - 2:vectors.cols]
    U = mp.eigsy(Q.T * K * Q, eigvals_only=True)[0]
    O = mp.zeros(2 * m + 1, m)
    for n in range(1, m + 1):
        O[m + n, n - 1] = 1 / mp.sqrt(2)
        O[m - n, n - 1] = -1 / mp.sqrt(2)
    B = O.T * K * O
    L = mp.log(m)
    s = mp.matrix([16 * mp.sqrt(2) * mp.pi * n * mp.sqrt(L) * mp.sinh(L / 4)
                   / (L**2 + 16 * mp.pi**2 * n*n) for n in range(1, m + 1)])
    M = B + 2 * s * s.T - U * mp.eye(m)
    odd = mp.eigsy(B, eigvals_only=True)[0]
    minimum_M = mp.eigsy(M, eigvals_only=True)[0]
    psi = 1 - 2 * (s.T * mp.lu_solve(M, s))[0]
    values = dict(U=U, odd_minimum=odd, odd_minus_U=odd-U,
                  minimum_M=minimum_M, Psi=psi,
                  projector_residual=mp.norm(plane*plane-plane),
                  theta_endpoint_parity_residual=parity_error)
    return {"m": m, "dps": dps, "theta_cutoff": cutoff,
            "status": "EXPLORATORY_NOT_CERTIFIED_NOT_COFINAL",
            **{key: mp.nstr(value, 35) for key, value in values.items()}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, default=8)
    parser.add_argument("--dps", type=int, default=90)
    args = parser.parse_args()
    if args.m < 2 or args.dps < 60:
        parser.error("require m >= 2 and dps >= 60")
    print(json.dumps(sample(args.m, args.dps), indent=2))
