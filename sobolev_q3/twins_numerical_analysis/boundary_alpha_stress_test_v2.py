#!/usr/bin/env python3
"""
boundary_alpha_stress_test_v2.py

We test the Q3-2 contraction metric on boundary minor-arc α.

Correct metric (generalized Rayleigh quotient):
  rho(α)^2 := sup_{y≠0}  ( y* (W U_α G U_α* W) y ) / ( y* G^{-1} y )

This rho(α) is the minimal constant such that:
  y* (W U_α G U_α* W) y ≤ rho(α)^2 · y* G^{-1} y   for all y.

Numerical method:
  Use Cholesky G = L L^T, rewrite the generalized eigenproblem as a standard
  Hermitian PSD eigenproblem:
    rho(α)^2 = λ_max( H_α ),   H_α := L^T (W U_α G U_α* W) L.
  Then estimate λ_max(H_α) via power iteration.

Micro-block decomposition:
  Split primes into dyadic blocks [2^j, 2^{j+1}) and compute rho_j(α) per block.
  Define rho_total(α) := max_j rho_j(α).

Boundary α (just outside major arcs):
  For each q<=Q and each (a,q)=1:
    α = a/q ± ( Q/(q^radius_power * N) + 1/N^2 )

Major arcs radius_power:
  radius_power=1  -> Q/(q N)   (older)
  radius_power=2  -> Q/(q^2 N) (corrected classical form, matches your v2.4 fix)

Output:
  For each N we report:
    - rho_worst_boundary: max rho_total(α) over boundary-α points
    - rho_random_max/mean/p95 over random minor-arc α samples
    - worst q and worst dyadic block j (where max is attained)

Author: GPT 5.2 PRO (Прошка 2) for Q3 Twin Prime Project

Usage examples:
  python boundary_alpha_stress_test_v2.py --N-list 5000,10000,20000 --Q 10 --t 0.03 --radius-power 2
  python boundary_alpha_stress_test_v2.py --N-list 50000 --Q 20 --t 0.03 --n-iter 50 --n-restarts 3
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional

import numpy as np


# ----------------------------
# Basic utilities
# ----------------------------

def primes_upto(n: int) -> np.ndarray:
    """Fast sieve; returns array of primes <= n."""
    if n < 2:
        return np.array([], dtype=np.int64)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    m = int(n ** 0.5)
    for p in range(2, m + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = False
    return np.nonzero(sieve)[0].astype(np.int64)


def dist_mod1(x: float, y: float) -> float:
    """Distance on R/Z."""
    d = abs(x - y)
    return min(d, 1.0 - d)


def is_major_arc(alpha: float, N: int, Q: int, radius_power: int = 2) -> bool:
    """
    alpha in major arcs if exists reduced a/q, 1<=q<=Q, s.t.
      dist(alpha, a/q) <= Q/(q^radius_power * N).
    """
    for q in range(1, Q + 1):
        rad = Q / ((q ** radius_power) * N)
        aq = alpha * q
        a0 = int(round(aq))
        # check near candidates for safety
        for a in (a0 - 1, a0, a0 + 1):
            a_mod = a % q
            if a_mod == 0:
                continue
            if math.gcd(a_mod, q) != 1:
                continue
            cand = a_mod / q
            if dist_mod1(alpha, cand) <= rad:
                return True
    return False


def sample_minor_alphas(
    N: int, Q: int, n_samples: int, radius_power: int, seed: int
) -> np.ndarray:
    rng = np.random.default_rng(seed)
    out: List[float] = []
    tries = 0
    while len(out) < n_samples:
        tries += 1
        if tries > 300000:
            raise RuntimeError("Too many rejection samples; Q might be too large.")
        a = float(rng.random())
        if not is_major_arc(a, N=N, Q=Q, radius_power=radius_power):
            out.append(a)
    return np.array(out, dtype=np.float64)


def boundary_alphas(
    N: int,
    Q: int,
    radius_power: int,
    eps: Optional[float] = None,
) -> Tuple[np.ndarray, List[Tuple[int, int, int]]]:
    """
    Boundary α points just outside each major arc a/q:
        α = a/q ± ( Q/(q^radius_power N) + eps )
    with eps default 1/N^2.

    Returns:
      alphas: array of α in [0,1)
      meta:   list of (q,a,sign) for each alpha
    """
    if eps is None:
        eps = 1.0 / (N * N)
    alphas: List[float] = []
    meta: List[Tuple[int, int, int]] = []
    for q in range(1, Q + 1):
        rad = Q / ((q ** radius_power) * N)
        delta = rad + eps
        for a in range(1, q + 1):
            if math.gcd(a, q) != 1:
                continue
            base = a / q
            for sgn in (-1, +1):
                alpha = (base + sgn * delta) % 1.0
                alphas.append(alpha)
                meta.append((q, a, sgn))
    return np.array(alphas, dtype=np.float64), meta


# ----------------------------
# Dyadic blocks + RKHS Gram
# ----------------------------

@dataclass
class BlockData:
    j: int                  # dyadic exponent
    primes: np.ndarray      # (n,) int64
    w: np.ndarray           # (n,) float64 weights = log p / sqrt p
    L: np.ndarray           # (n,n) float64 Cholesky factor of Gram G = L L^T
    t: float                # heat parameter
    jitter: float           # diagonal jitter used


def safe_cholesky(G: np.ndarray, jitter0: float, max_tries: int = 8) -> Tuple[np.ndarray, float]:
    """
    Cholesky with adaptive jitter. Returns (L, jitter_used).
    """
    jitter = jitter0
    n = G.shape[0]
    for _ in range(max_tries):
        try:
            G_sym = (G + G.T) * 0.5
            G_sym[np.diag_indices(n)] += jitter
            L = np.linalg.cholesky(G_sym)
            return L, jitter
        except np.linalg.LinAlgError:
            jitter *= 10.0
    raise np.linalg.LinAlgError(f"Cholesky failed even with jitter ~ {jitter:g}")


def build_block(j: int, primes_block: np.ndarray, t: float, jitter: float) -> BlockData:
    p = primes_block.astype(np.float64)
    # log-scale nodes xi_p = log p / (2π)
    xi = np.log(p) / (2.0 * np.pi)
    diff = xi[:, None] - xi[None, :]
    G = np.exp(-(diff * diff) / (4.0 * t))
    L, jitter_used = safe_cholesky(G, jitter0=jitter)
    w = np.log(p) / np.sqrt(p)  # Λ(p)/sqrt(p) for primes
    return BlockData(j=j, primes=primes_block, w=w, L=L, t=t, jitter=jitter_used)


def dyadic_blocks(primes: np.ndarray, N: int, min_block_size: int) -> List[Tuple[int, np.ndarray]]:
    """
    Return list of (j, primes_in_[2^j,2^{j+1})) for j with enough primes.
    """
    blocks: List[Tuple[int, np.ndarray]] = []
    j = 0
    while (1 << j) <= N:
        lo = 1 << j
        hi = min((1 << (j + 1)) - 1, N)
        mask = (primes >= lo) & (primes <= hi)
        ps = primes[mask]
        if ps.size >= min_block_size:
            blocks.append((j, ps))
        j += 1
    return blocks


# ----------------------------
# The metric: generalized Rayleigh quotient via power iteration
# ----------------------------

def _matvec_H(x: np.ndarray, block: BlockData, phase: np.ndarray) -> np.ndarray:
    """
    H_α = L^T (W U_α G U_α* W) L, with G = L L^T.

    Matvec uses only L and L^T (no explicit G^{-1} needed, but it's equivalent):
      y = L x
      y = W y
      y = U* y
      y = L^T y
      y = L y
      y = U y
      y = W y
      out = L^T y
    """
    L = block.L
    w = block.w
    y = L @ x
    y = w * y
    y = np.conj(phase) * y
    y = L.T @ y
    y = L @ y
    y = phase * y
    y = w * y
    y = L.T @ y
    return y


def estimate_rho_block(
    block: BlockData,
    alpha: float,
    n_iter: int,
    n_restarts: int,
    seed: int,
) -> float:
    """
    Estimate rho_block(alpha) by power method on Hermitian PSD H_α.
    rho(α)^2 = λ_max(H_α), so rho(α) = sqrt(λ_max).
    """
    p = block.primes.astype(np.float64)
    phase = np.exp(2j * np.pi * alpha * p).astype(np.complex128)
    n = p.shape[0]
    rng = np.random.default_rng(seed)

    best_lam = 0.0
    for r in range(n_restarts):
        x = rng.standard_normal(n) + 1j * rng.standard_normal(n)
        x = x.astype(np.complex128)
        x /= np.linalg.norm(x)

        for _ in range(n_iter):
            y = _matvec_H(x, block, phase)
            norm = np.linalg.norm(y)
            if norm == 0.0:
                break
            x = y / norm

        # Rayleigh quotient (should be real >=0)
        y = _matvec_H(x, block, phase)
        lam = float(np.real(np.vdot(x, y)))
        if lam > best_lam:
            best_lam = lam

    return math.sqrt(max(best_lam, 0.0))


def estimate_rho_all_blocks(
    blocks: List[BlockData],
    alpha: float,
    n_iter: int,
    n_restarts: int,
    seed: int,
) -> Tuple[float, int]:
    """
    rho_total(alpha) := max_j rho_j(alpha).
    Returns (rho_total, argmax_block_j).
    """
    best_rho = -1.0
    best_j = -1
    for idx, block in enumerate(blocks):
        rho = estimate_rho_block(
            block, alpha,
            n_iter=n_iter,
            n_restarts=n_restarts,
            seed=seed + 1000 * idx
        )
        if rho > best_rho:
            best_rho = rho
            best_j = block.j
    return best_rho, best_j


# ----------------------------
# Main experiment
# ----------------------------

def run_one_N(
    N: int,
    Q: int,
    t: float,
    radius_power: int,
    n_random: int,
    n_iter: int,
    n_restarts: int,
    min_block_size: int,
    jitter: float,
    seed: int,
) -> Dict[str, object]:
    primes = primes_upto(N)
    if primes.size == 0:
        raise ValueError("No primes found. N too small.")

    blocks_spec = dyadic_blocks(primes, N=N, min_block_size=min_block_size)
    if len(blocks_spec) == 0:
        raise ValueError("All dyadic blocks are too small; lower --min-block-size.")

    # Precompute blocks: Gram -> Cholesky, and weights
    blocks: List[BlockData] = []
    for j, ps in blocks_spec:
        blocks.append(build_block(j=j, primes_block=ps, t=t, jitter=jitter))

    # boundary alphas just outside major arcs
    alphas_b, meta_b = boundary_alphas(N=N, Q=Q, radius_power=radius_power, eps=1.0 / (N * N))

    # Keep only those that are actually minor arcs under the same major-arc definition
    keep_a: List[float] = []
    keep_m: List[Tuple[int, int, int]] = []
    for a, m in zip(alphas_b, meta_b):
        if not is_major_arc(float(a), N=N, Q=Q, radius_power=radius_power):
            keep_a.append(float(a))
            keep_m.append(m)
    alphas_b = np.array(keep_a, dtype=np.float64)
    meta_b = keep_m

    # random minor alphas
    alphas_r = sample_minor_alphas(N=N, Q=Q, n_samples=n_random, radius_power=radius_power, seed=seed + 999)

    # Evaluate boundary worst-case
    worst_rho = -1.0
    worst_q = None
    worst_alpha = None
    worst_block_j = None
    for alpha, (q, a, sgn) in zip(alphas_b, meta_b):
        rho, bj = estimate_rho_all_blocks(blocks, float(alpha), n_iter=n_iter, n_restarts=n_restarts, seed=seed)
        if rho > worst_rho:
            worst_rho = rho
            worst_q = q
            worst_alpha = float(alpha)
            worst_block_j = bj

    # Evaluate random sample
    rhos_random: List[float] = []
    worst_rho_random = -1.0
    worst_alpha_random = None
    worst_block_j_random = None
    for alpha in alphas_r:
        rho, bj = estimate_rho_all_blocks(blocks, float(alpha), n_iter=n_iter, n_restarts=n_restarts, seed=seed)
        rhos_random.append(rho)
        if rho > worst_rho_random:
            worst_rho_random = rho
            worst_alpha_random = float(alpha)
            worst_block_j_random = bj

    rhos_random = np.array(rhos_random, dtype=np.float64)

    return {
        "N": N,
        "n_primes": int(primes.size),
        "n_blocks": int(len(blocks)),
        "Q": Q,
        "t": t,
        "radius_power": radius_power,
        "rho_worst_boundary": float(worst_rho),
        "delta_boundary": float(1.0 - worst_rho),
        "worst_q_boundary": worst_q,
        "worst_alpha_boundary": worst_alpha,
        "worst_block_j_boundary": worst_block_j,
        "rho_random_max": float(worst_rho_random),
        "delta_random_max": float(1.0 - worst_rho_random),
        "rho_random_mean": float(rhos_random.mean()),
        "rho_random_p95": float(np.quantile(rhos_random, 0.95)),
        "worst_alpha_random": worst_alpha_random,
        "worst_block_j_random": worst_block_j_random,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N-list", type=str, default="5000,10000,20000",
                    help="Comma-separated list of N values.")
    ap.add_argument("--Q", type=int, default=10,
                    help="Major arc denominator cutoff Q (test q=1..Q).")
    ap.add_argument("--t", type=float, default=0.03,
                    help="Heat kernel parameter t>0.")
    ap.add_argument("--radius-power", type=int, default=2, choices=[1, 2],
                    help="Major arc radius is Q/(q^radius_power N). Use 2 for corrected.")
    ap.add_argument("--n-random", type=int, default=30,
                    help="How many random minor-arc α to sample.")
    ap.add_argument("--n-iter", type=int, default=30,
                    help="Power iterations for rho estimation (per block, per alpha).")
    ap.add_argument("--n-restarts", type=int, default=2,
                    help="Random restarts for rho estimation.")
    ap.add_argument("--min-block-size", type=int, default=80,
                    help="Skip dyadic blocks with fewer primes than this.")
    ap.add_argument("--jitter", type=float, default=1e-10,
                    help="Diagonal jitter for Gram matrix before Cholesky.")
    ap.add_argument("--seed", type=int, default=123,
                    help="Random seed.")
    args = ap.parse_args()

    Ns = [int(x.strip()) for x in args.N_list.split(",") if x.strip()]
    rows: List[Dict[str, object]] = []

    for N in Ns:
        row = run_one_N(
            N=N,
            Q=args.Q,
            t=args.t,
            radius_power=args.radius_power,
            n_random=args.n_random,
            n_iter=args.n_iter,
            n_restarts=args.n_restarts,
            min_block_size=args.min_block_size,
            jitter=args.jitter,
            seed=args.seed + N,
        )
        rows.append(row)

    header = (
        f"{'N':>8} {'primes':>7} {'blocks':>6} "
        f"{'rho_bdry':>9} {'delta_b':>7} {'worst_q':>7} {'worst_j':>7} "
        f"{'rho_rmax':>9} {'delta_r':>7} {'rho_rmean':>9} {'rho_rp95':>9}"
    )
    print(header)
    print("-" * len(header))

    for r in rows:
        print(
            f"{r['N']:8d} {r['n_primes']:7d} {r['n_blocks']:6d} "
            f"{r['rho_worst_boundary']:9.4f} {r['delta_boundary']:7.4f} {str(r['worst_q_boundary']):>7} {str(r['worst_block_j_boundary']):>7} "
            f"{r['rho_random_max']:9.4f} {r['delta_random_max']:7.4f} {r['rho_random_mean']:9.4f} {r['rho_random_p95']:9.4f}"
        )


if __name__ == "__main__":
    main()
