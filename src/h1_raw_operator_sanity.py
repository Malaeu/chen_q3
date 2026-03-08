#!/usr/bin/env python3
r"""
Sanity check for the raw H1 operator package.

This script verifies the normalization brick extracted from the A3 files:

    Pi_M = (2M+1) T_P^Ray(t,M)
    Q_M^raw = T_M[P_A] - Pi_M

and the raw entry formula

    q_rs = A_{r-s} - sum_{|\xi_n| <= B} lambda_n exp(2 pi i (s-r) xi_n),
    lambda_n = (2 Lambda(n) / sqrt(n)) Phi_{B,t}(xi_n).

The nontrivial part is the prime normalization.  The Toeplitz part is included
so that the script checks the full raw matrix in the exact notation we now hand
to Proshka.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from scipy.special import digamma


@dataclass(frozen=True)
class PrimeNode:
    n: int
    xi: float
    lam: float


def a_scalar(xi: np.ndarray) -> np.ndarray:
    z = 0.25 + 1j * np.pi * xi
    return np.log(np.pi) - np.real(digamma(z))


def phi_fejer_heat(xi: np.ndarray, B: float, t: float) -> np.ndarray:
    xi = np.asarray(xi, dtype=float)
    out = np.zeros_like(xi)
    mask = np.abs(xi) <= B
    if np.any(mask):
        out[mask] = (1.0 - np.abs(xi[mask]) / B) * np.exp(-4.0 * np.pi**2 * t * xi[mask] ** 2)
    return out


def smallest_prime_factors(n_max: int) -> list[int]:
    spf = list(range(n_max + 1))
    if n_max >= 1:
        spf[1] = 1
    for p in range(2, int(n_max**0.5) + 1):
        if spf[p] == p:
            for m in range(p * p, n_max + 1, p):
                if spf[m] == m:
                    spf[m] = p
    return spf


def prime_power_base(n: int, spf: list[int]) -> int | None:
    p = spf[n]
    m = n
    while m % p == 0:
        m //= p
    return p if m == 1 else None


def active_prime_nodes(B: float, t: float) -> list[PrimeNode]:
    n_max = int(math.floor(math.exp(2.0 * np.pi * B) + 1e-12))
    spf = smallest_prime_factors(n_max)
    nodes: list[PrimeNode] = []
    for n in range(2, n_max + 1):
        p = prime_power_base(n, spf)
        if p is None:
            continue
        xi = math.log(n) / (2.0 * np.pi)
        phi = float(phi_fejer_heat(np.array([xi]), B, t)[0])
        if phi == 0.0:
            continue
        lam = 2.0 * math.log(p) / math.sqrt(n) * phi
        nodes.append(PrimeNode(n=n, xi=xi, lam=lam))
    return nodes


def arch_coefficients(B: float, t: float, max_k: int, grid_size: int) -> dict[int, complex]:
    xi = np.linspace(-B, B, grid_size)
    integrand_base = 2.0 * np.pi * a_scalar(xi) * phi_fejer_heat(xi, B, t)
    coeffs: dict[int, complex] = {}
    for k in range(-max_k, max_k + 1):
        phase = np.exp(-2j * np.pi * k * xi)
        coeffs[k] = np.trapezoid(integrand_base * phase, xi)
    return coeffs


def basis_indices(M: int) -> list[int]:
    return list(range(-M, M + 1))


def toeplitz_matrix(M: int, A: dict[int, complex]) -> np.ndarray:
    idx = basis_indices(M)
    size = len(idx)
    out = np.zeros((size, size), dtype=complex)
    for i, r in enumerate(idx):
        for j, s in enumerate(idx):
            out[i, j] = A[r - s]
    return out


def normalized_prime_matrix(M: int, nodes: list[PrimeNode]) -> np.ndarray:
    idx = np.array(basis_indices(M), dtype=float)
    size = idx.size
    out = np.zeros((size, size), dtype=complex)
    norm = math.sqrt(2 * M + 1)
    for node in nodes:
        coeffs = np.exp(-2j * np.pi * idx * node.xi) / norm
        out += node.lam * np.outer(coeffs, np.conjugate(coeffs))
    return out


def raw_prime_formula_matrix(M: int, nodes: list[PrimeNode]) -> np.ndarray:
    idx = basis_indices(M)
    size = len(idx)
    out = np.zeros((size, size), dtype=complex)
    for i, r in enumerate(idx):
        for j, s in enumerate(idx):
            out[i, j] = sum(node.lam * np.exp(2j * np.pi * (s - r) * node.xi) for node in nodes)
    return out


def raw_formula_matrix(M: int, A: dict[int, complex], nodes: list[PrimeNode]) -> np.ndarray:
    return toeplitz_matrix(M, A) - raw_prime_formula_matrix(M, nodes)


def max_abs_entry(mat: np.ndarray) -> float:
    return float(np.max(np.abs(mat))) if mat.size else 0.0


def overlap_block(mat_large: np.ndarray, M_large: int, M_small: int) -> np.ndarray:
    idx_large = basis_indices(M_large)
    idx_small = basis_indices(M_small)
    pos = {r: i for i, r in enumerate(idx_large)}
    rows = [pos[r] for r in idx_small]
    return mat_large[np.ix_(rows, rows)]


def run_check(M: int, M_big: int, B: float, t: float, grid_size: int) -> dict[str, float | int]:
    nodes = active_prime_nodes(B, t)
    max_k = 2 * M_big
    A = arch_coefficients(B, t, max_k=max_k, grid_size=grid_size)

    tp_norm_M = normalized_prime_matrix(M, nodes)
    tp_norm_big = normalized_prime_matrix(M_big, nodes)

    pi_from_norm_M = (2 * M + 1) * tp_norm_M
    pi_from_norm_big = (2 * M_big + 1) * tp_norm_big

    pi_formula_M = raw_prime_formula_matrix(M, nodes)
    pi_formula_big = raw_prime_formula_matrix(M_big, nodes)

    q_matrix_M = toeplitz_matrix(M, A) - pi_from_norm_M
    q_formula_M = raw_formula_matrix(M, A, nodes)

    q_matrix_big = toeplitz_matrix(M_big, A) - pi_from_norm_big
    q_matrix_big_overlap = overlap_block(q_matrix_big, M_large=M_big, M_small=M)

    return {
        "M": M,
        "M_big": M_big,
        "B": B,
        "t": t,
        "n_active_nodes": len(nodes),
        "prime_scaling_error_M": max_abs_entry(pi_from_norm_M - pi_formula_M),
        "prime_scaling_error_M_big": max_abs_entry(pi_from_norm_big - pi_formula_big),
        "raw_entry_error_M": max_abs_entry(q_matrix_M - q_formula_M),
        "stability_error_overlap": max_abs_entry(q_matrix_M - q_matrix_big_overlap),
        "max_abs_q_entry": max_abs_entry(q_matrix_M),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Sanity-check the raw H1 operator normalization.")
    parser.add_argument("--M", type=int, default=4, help="Base finite section size M.")
    parser.add_argument("--M-big", type=int, default=7, help="Larger finite section size for overlap stability.")
    parser.add_argument("--B", type=float, default=0.2, help="Compact support parameter B.")
    parser.add_argument("--t", type=float, default=0.15, help="Heat scale t.")
    parser.add_argument("--grid-size", type=int, default=20001, help="Integration grid size for A_k.")
    parser.add_argument("--tol", type=float, default=1e-9, help="Numerical tolerance for pass/fail.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.M < 0 or args.M_big <= args.M:
        raise SystemExit("Need M >= 0 and M_big > M.")
    if args.B <= 0 or args.t <= 0:
        raise SystemExit("Need B > 0 and t > 0.")

    results = run_check(
        M=args.M,
        M_big=args.M_big,
        B=args.B,
        t=args.t,
        grid_size=args.grid_size,
    )

    print("H1 raw-operator sanity check")
    print("============================")
    print(f"M={results['M']}  M_big={results['M_big']}  B={results['B']}  t={results['t']}")
    print(f"active nodes: {results['n_active_nodes']}")
    print(f"prime scaling error (M):      {results['prime_scaling_error_M']:.3e}")
    print(f"prime scaling error (M_big):  {results['prime_scaling_error_M_big']:.3e}")
    print(f"raw entry error (M):          {results['raw_entry_error_M']:.3e}")
    print(f"overlap stability error:      {results['stability_error_overlap']:.3e}")
    print(f"max |q_rs| on M block:        {results['max_abs_q_entry']:.3e}")

    max_error = max(
        float(results["prime_scaling_error_M"]),
        float(results["prime_scaling_error_M_big"]),
        float(results["raw_entry_error_M"]),
        float(results["stability_error_overlap"]),
    )
    if max_error <= args.tol:
        print(f"PASS: all sanity checks are within tolerance {args.tol:.1e}")
        return 0

    print(f"FAIL: max error {max_error:.3e} exceeds tolerance {args.tol:.1e}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
