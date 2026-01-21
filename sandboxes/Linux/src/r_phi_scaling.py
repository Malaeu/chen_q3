#!/usr/bin/env python3
"""
Compute and plot the scaling of R(Phi_X) = E_comm / E_lat for the twin vector.

Method:
  * Build twin primes up to each X in a user-specified list.
  * Weights: lambda_p = Lambda(p) Lambda(p+2) = (log p)(log(p+2)).
  * Kernel: Gaussian G(delta) = sqrt(2π t) exp(-delta^2/(8 t)).
  * Commutator matrix: A_pq = 0.5 (xi_q - xi_p) (G^2)_pq.
  * Energies: E_comm = (A λ)^T G (A λ), E_lat = (G λ)^T (G λ).
  * R = E_comm / E_lat.

Outputs:
  * Table to stdout.
  * Optional CSV file.
  * Optional log–log plot saved to output/r_phi_scaling.png (unless --no-plot).

This is a lightweight, dependency-free (beyond numpy / matplotlib) script for
replication of the observed scaling R ~ X^β.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Iterable, List, Optional

import numpy as np


# ---------- Primes and twins ----------

def sieve_primes(limit: int) -> List[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            step = ((limit - p * p) // p) + 1
            sieve[p * p : limit + 1 : p] = b"\x00" * step
    return [i for i, b in enumerate(sieve) if b]


def twin_primes(limit: int) -> List[int]:
    primes = set(sieve_primes(limit + 2))
    return [p for p in primes if p + 2 in primes and p <= limit]


# ---------- Core computation ----------

def compute_R(
    X: int,
    t: float = 1.0,
    mode: str = "default",
) -> Optional[dict]:
    """
    mode:
      - "default": legacy variant
          G = sqrt(2π t) exp(-Δ²/8t)
          A = 0.5 (xi_q - xi_p) (G^2)
          E_lat = ||G λ||^2
          E_comm = (Aλ)^T G (Aλ)
      - "paper": manuscript definitions
          G = sqrt(2π t) exp(-Δ²/8t)
          A = (xi_q - xi_p) (G^2)
          E_lat = λ^T G λ
          E_comm = ||A λ||^2
      - "paper-norm": same as paper + diagnostics (||G||, diag/offdiag split)
    """
    twins = twin_primes(X)
    N = len(twins)
    if N < 2:
        return None

    pos = np.log(np.array(twins, dtype=np.float64)) / (2 * math.pi)  # xi_p
    lam = np.log(np.array(twins, dtype=np.float64)) * np.log(
        np.array(twins, dtype=np.float64) + 2.0
    )  # Lambda(p) Lambda(p+2)

    diff = pos[:, None] - pos[None, :]
    G = math.sqrt(2 * math.pi * t) * np.exp(-diff * diff / (8.0 * t))
    G2 = G @ G

    if mode.startswith("paper"):
        A = (pos[None, :] - pos[:, None]) * G2
        E_lat = float(lam @ (G @ lam))
        A_lam = A @ lam
        E_comm = float(A_lam @ A_lam)
    else:
        A = 0.5 * (pos[None, :] - pos[:, None]) * G2
        G_lam = G @ lam
        E_lat = float(G_lam @ G_lam)
        c = A @ lam
        E_comm = float(c @ (G @ c))

    R = E_comm / E_lat if E_lat > 0 else math.nan

    out = {"X": X, "N": N, "R": R, "E_comm": E_comm, "E_lat": E_lat}

    if mode.startswith("paper"):
        w, _ = np.linalg.eigh(G)
        out["G_norm"] = float(np.max(np.abs(w)))
        diag = float(np.sum((A.diagonal() * lam) ** 2))
        off = E_comm - diag
        out["diag_frac"] = diag / E_comm if E_comm > 0 else math.nan
        out["off_frac"] = off / E_comm if E_comm > 0 else math.nan
        # mean of B = A^T A (unweighted by λ)
        B = A.T @ A
        out["B_mean"] = float(B.mean())
    return out


def loglog_fit(xs: Iterable[float], ys: Iterable[float]) -> tuple[float, float]:
    xs_arr = np.array(list(xs), dtype=np.float64)
    ys_arr = np.array(list(ys), dtype=np.float64)
    mask = (xs_arr > 0) & (ys_arr > 0)
    xs_arr, ys_arr = xs_arr[mask], ys_arr[mask]
    coeffs = np.polyfit(np.log(xs_arr), np.log(ys_arr), 1)
    slope, intercept = coeffs[0], coeffs[1]
    return float(slope), float(intercept)


# ---------- CLI ----------

def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Scaling of R(Phi_X) for twins")
    parser.add_argument(
        "--X",
        nargs="*",
        type=int,
        default=[10**3, 10**4, 10**5, 200_000, 300_000],
        help="Values of X to test (default: 1e3, 1e4, 1e5, 2e5, 3e5)",
    )
    parser.add_argument("--t", type=float, default=1.0, help="Gaussian kernel width t")
    parser.add_argument("--csv", type=Path, help="Optional CSV output path")
    parser.add_argument(
        "--plot",
        type=Path,
        default=Path("output/r_phi_scaling.png"),
        help="PNG plot output path (default: output/r_phi_scaling.png)",
    )
    parser.add_argument("--no-plot", action="store_true", help="Skip plotting")
    parser.add_argument(
        "--mode",
        choices=["default", "paper", "paper-norm"],
        default="default",
        help="Energy definitions: default (legacy) or paper (manuscript).",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    results = []
    for X in args.X:
        res = compute_R(X, t=args.t, mode=args.mode)
        if res is None:
            print(f"X={X}: not enough twins to compute R.")
            continue
        results.append(res)
        line = (
            f"X={res['X']:>8}, N={res['N']:>6}, "
            f"R={res['R']:.4e}, R/X^2={res['R']/ (res['X']**2):.3e}"
        )
        if args.mode.startswith("paper"):
            line += (
                f", ||G||={res['G_norm']:.3e}, diag%={res['diag_frac']*100:.2f}, "
                f"off%={res['off_frac']*100:.2f}"
            )
        print(line)

    if not results:
        return

    slope, intercept = loglog_fit([r["X"] for r in results], [r["R"] for r in results])
    print(f"log–log fit: R ~ X^{slope:.3f} (intercept {intercept:.3f})")

    # CSV output
    if args.csv:
        args.csv.parent.mkdir(parents=True, exist_ok=True)
        with args.csv.open("w") as f:
            f.write("X,N,R,E_comm,E_lat\n")
            for r in results:
                f.write(f"{r['X']},{r['N']},{r['R']},{r['E_comm']},{r['E_lat']}\n")

    # Plot
    if not args.no_plot:
        try:
            import matplotlib.pyplot as plt

            xs = [r["X"] for r in results]
            Rs = [r["R"] for r in results]
            plt.figure()
            plt.loglog(xs, Rs, "o-", label="R(Phi_X)")
            # fitted line
            xs_fit = np.array(xs, dtype=np.float64)
            plt.loglog(
                xs_fit,
                np.exp(intercept) * xs_fit**slope,
                "--",
                label=f"fit: X^{slope:.2f}",
            )
            plt.xlabel("X")
            plt.ylabel("R(Phi_X)")
            plt.legend()
            plt.tight_layout()
            args.plot.parent.mkdir(parents=True, exist_ok=True)
            plt.savefig(args.plot, dpi=200)
            print(f"Plot saved to {args.plot}")
        except Exception as exc:  # pragma: no cover - plotting optional
            print(f"Plotting skipped: {exc}")


if __name__ == "__main__":
    main()
