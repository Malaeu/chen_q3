#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Boundary-α stress test (v2.3 patch)

What it computes
----------------
For dyadic micro-blocks j (by default: last 3 blocks near N),
and for α points just OUTSIDE major arcs boundaries:
  α = a/q ± (Q/(qN) + 1/N^radius_power),

we estimate the generalized Rayleigh quotient (stable, no explicit G^{-1}):

  rho_abs(α)^2  ≈  sup_{y≠0}  [ y* (W U_α G U_α* W) y ] / [ y* G^{-1} y ].

We compute y*G^{-1}y stably via Cholesky:
  G = L L*, so  y*G^{-1}y = ||L^{-1} y||^2.

We also report:
  rho_rel(α) := rho_abs(α) / rho_abs(0)  (per same micro-block).

CLI highlights
--------------
--mu-weights : use μ_p ≈ log(p)/(2π p) instead of log(p)/sqrt(p)
--n-blocks   : how many top dyadic blocks to analyze (default 3)
--print-blocks : print per-block diagnostics
"""

import argparse
import math
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict

import numpy as np

try:
    from scipy.linalg import solve_triangular
except Exception:
    solve_triangular = None


# ----------------------------
# Utilities: primes, blocks
# ----------------------------

def primes_upto(n: int) -> np.ndarray:
    """Simple sieve, returns primes <= n as int64 array."""
    if n < 2:
        return np.array([], dtype=np.int64)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    r = int(n ** 0.5)
    for p in range(2, r + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = False
    return np.nonzero(sieve)[0].astype(np.int64)


def top_dyadic_blocks(primes: np.ndarray, N: int, n_blocks: int) -> List[Tuple[int, np.ndarray, int, int]]:
    """
    Returns last n_blocks dyadic blocks near N:
      j in [j_max-n_blocks+1, ..., j_max], where 2^j <= p < 2^{j+1} (clipped by N).
    Each entry: (j, primes_in_block, lo, hi_exclusive)
    """
    if N < 2:
        return []
    j_max = int(math.log2(N))
    j_min = max(0, j_max - n_blocks + 1)
    out: List[Tuple[int, np.ndarray, int, int]] = []
    for j in range(j_min, j_max + 1):
        lo = 2 ** j
        hi = min(2 ** (j + 1), N + 1)  # exclusive
        mask = (primes >= lo) & (primes < hi)
        pj = primes[mask]
        if pj.size > 0:
            out.append((j, pj, lo, hi))
    return out


# ----------------------------
# Major/minor arcs + sampling
# ----------------------------

def mod1_dist(a: float, b: float) -> float:
    """Distance on R/Z, with a,b in [0,1)."""
    d = a - b
    d -= round(d)  # now in [-0.5,0.5]
    return abs(d)


def in_major_arcs(alpha: float, N: int, Q: int) -> bool:
    """Check if alpha lies in major arcs defined by q<=Q, radius Q/(qN)."""
    for q in range(1, Q + 1):
        rad = Q / (q * N)
        for a in range(1, q + 1):
            if math.gcd(a, q) != 1:
                continue
            if mod1_dist(alpha, a / q) <= rad:
                return True
    return False


def boundary_alphas(N: int, Q: int, radius_power: int) -> List[Tuple[float, int, int, int]]:
    """
    Boundary points just outside major arcs:
      alpha = a/q ± (Q/(qN) + 1/N^radius_power)
    Returns list of tuples: (alpha, q, a, sign) where sign ∈ {+1,-1}.
    """
    out: List[Tuple[float, int, int, int]] = []
    fudge_base = 1.0 / (N ** radius_power)
    for q in range(1, Q + 1):
        rad = Q / (q * N) + fudge_base
        for a in range(1, q + 1):
            if math.gcd(a, q) != 1:
                continue
            base = a / q
            out.append(((base + rad) % 1.0, q, a, +1))
            out.append(((base - rad) % 1.0, q, a, -1))
    return out


def sample_random_minor_alphas(N: int, Q: int, n: int, rng: np.random.Generator) -> List[float]:
    """Rejection-sample alphas in minor arcs."""
    out: List[float] = []
    while len(out) < n:
        a = float(rng.random())
        if not in_major_arcs(a, N, Q):
            out.append(a)
    return out


# ----------------------------
# Gram matrix + stable solve
# ----------------------------

def build_gram(primes: np.ndarray, t: float) -> np.ndarray:
    """
    Heat-kernel Gram:
      G_{pq} = exp( - (xi_p - xi_q)^2 / (4t) ),
      xi_p = log p / (2π)
    => G_{pq} = exp( - log(p/q)^2 / (16 π^2 t) )
    """
    logs = np.log(primes.astype(np.float64))
    diff = logs[:, None] - logs[None, :]
    denom = 16.0 * (math.pi ** 2) * t
    return np.exp(-(diff * diff) / denom)


def chol_psd(G: np.ndarray, jitter: float = 1e-12, max_tries: int = 8) -> Tuple[np.ndarray, float]:
    """
    Robust Cholesky for nearly-PSD matrices.
    Returns (L, eps) where L is lower-triangular such that G+eps I = L L*.
    """
    n = G.shape[0]
    scale = float(np.trace(G)) / max(n, 1)
    if not np.isfinite(scale) or scale <= 0:
        scale = 1.0

    for k in range(max_tries):
        eps = (jitter * (10.0 ** k)) * scale
        try:
            L = np.linalg.cholesky(G + eps * np.eye(n))
            return L, eps
        except np.linalg.LinAlgError:
            continue

    # fallback: eigen clamp (not triangular, but still a valid factor-ish)
    evals, evecs = np.linalg.eigh(G)
    eps = (jitter * (10.0 ** max_tries)) * scale
    evals = np.clip(evals, eps, None)
    L = evecs @ np.diag(np.sqrt(evals))
    return L, eps


def solve_L(L: np.ndarray, Y: np.ndarray) -> np.ndarray:
    """
    Compute Z = L^{-1} Y stably.
    If L is triangular, use solve_triangular; otherwise fallback to np.linalg.solve.
    """
    if solve_triangular is not None and np.allclose(L, np.tril(L)):
        return solve_triangular(L, Y, lower=True, check_finite=False)
    return np.linalg.solve(L, Y)


# ----------------------------
# Weights
# ----------------------------

def compute_weights(primes: np.ndarray, mu_weights: bool) -> np.ndarray:
    """
    Default weights: w(p)=log(p)/sqrt(p).
    If --mu-weights: μ_p ≈ log(p)/(2π p).
    """
    p = primes.astype(np.float64)
    lp = np.log(p)
    if mu_weights:
        return lp / (2.0 * math.pi * p)
    return lp / np.sqrt(p)


# ----------------------------
# Rayleigh estimator (vectorized)
# ----------------------------

def estimate_rhosq_for_alphas(
    G: np.ndarray,
    L: np.ndarray,
    primes: np.ndarray,
    weights: np.ndarray,
    alphas: List[float],
    n_samples: int,
    rng: np.random.Generator,
) -> np.ndarray:
    """
    Estimate rho(α)^2 for each α by random Rayleigh sampling:

      rho(α)^2 ≈ max_k  num_k(α)/den_k,
      num_k(α) = z_k(α)^* G z_k(α),
      z_k(α) = U_α^* W y_k,
      den_k   = y_k^* G^{-1} y_k = ||L^{-1} y_k||^2.

    Uses one shared random batch Y across all α (faster + consistent).
    """
    n = primes.size
    if n == 0:
        return np.array([], dtype=np.float64)

    # random complex vectors Y: n x n_samples
    Y = rng.standard_normal((n, n_samples)) + 1j * rng.standard_normal((n, n_samples))

    # denominators: ||L^{-1} Y||^2 columnwise (stable, no explicit G^{-1})
    Zden = solve_L(L, Y)
    denom = np.sum(np.abs(Zden) ** 2, axis=0)
    denom = np.maximum(denom, 1e-300)  # avoid division by 0

    # precompute W*Y once
    WY = weights[:, None] * Y

    # evaluate each alpha
    p_float = primes.astype(np.float64)
    out = np.empty(len(alphas), dtype=np.float64)

    for i, alpha in enumerate(alphas):
        # z = U_α^* (W y) : multiply by exp(-2π i α p)
        phase = np.exp(-2j * math.pi * alpha * p_float)[:, None]
        Z = WY * phase

        # num = diag(Z^* (G Z)) columnwise
        GZ = G @ Z
        num = np.sum(np.conj(Z) * GZ, axis=0).real
        num = np.maximum(num, 0.0)  # numerical guard

        ratios = num / denom
        out[i] = float(np.max(ratios))

    return out


# ----------------------------
# Reporting
# ----------------------------

@dataclass
class BlockStats:
    j: int
    lo: int
    hi: int
    n_primes: int
    rho0_abs: float

    bdry_abs: float
    bdry_rel: float
    bdry_q: int
    bdry_a: int
    bdry_sign: int
    bdry_alpha: float

    rnd_abs_max: float
    rnd_rel_max: float
    rnd_abs_mean: float
    rnd_rel_mean: float
    rnd_abs_p95: float
    rnd_rel_p95: float


def compute_block_stats(
    N: int,
    Q: int,
    t: float,
    radius_power: int,
    primes_block: np.ndarray,
    j: int,
    lo: int,
    hi: int,
    n_samples: int,
    n_random: int,
    mu_weights: bool,
    seed: int,
) -> Optional[BlockStats]:
    if primes_block.size < 2:
        return None

    # Build Gram + factor
    G = build_gram(primes_block, t=t)
    L, eps = chol_psd(G)

    # weights
    w = compute_weights(primes_block, mu_weights=mu_weights)

    rng = np.random.default_rng(seed + 10_000 * j + N)

    # baseline α=0
    r0_sq = estimate_rhosq_for_alphas(G, L, primes_block, w, [0.0], n_samples, rng)[0]
    rho0_abs = math.sqrt(max(r0_sq, 0.0))

    # boundary alphas
    bdry = boundary_alphas(N=N, Q=Q, radius_power=radius_power)
    bdry_alphas = [x[0] for x in bdry]
    r_bdry_sq = estimate_rhosq_for_alphas(G, L, primes_block, w, bdry_alphas, n_samples, rng)
    r_bdry_abs = np.sqrt(np.maximum(r_bdry_sq, 0.0))

    i_worst = int(np.argmax(r_bdry_abs))
    bdry_abs = float(r_bdry_abs[i_worst])
    bdry_rel = float(bdry_abs / rho0_abs) if rho0_abs > 0 else float("nan")
    bdry_alpha, bdry_q, bdry_a, bdry_sign = bdry[i_worst]

    # random minor alphas
    rnd_alphas = sample_random_minor_alphas(N=N, Q=Q, n=n_random, rng=rng)
    r_rnd_sq = estimate_rhosq_for_alphas(G, L, primes_block, w, rnd_alphas, n_samples, rng)
    r_rnd_abs = np.sqrt(np.maximum(r_rnd_sq, 0.0))

    rnd_abs_max = float(np.max(r_rnd_abs)) if r_rnd_abs.size else float("nan")
    rnd_rel_max = float(rnd_abs_max / rho0_abs) if rho0_abs > 0 else float("nan")
    rnd_abs_mean = float(np.mean(r_rnd_abs)) if r_rnd_abs.size else float("nan")
    rnd_rel_mean = float(rnd_abs_mean / rho0_abs) if rho0_abs > 0 else float("nan")
    rnd_abs_p95 = float(np.percentile(r_rnd_abs, 95)) if r_rnd_abs.size else float("nan")
    rnd_rel_p95 = float(rnd_abs_p95 / rho0_abs) if rho0_abs > 0 else float("nan")

    return BlockStats(
        j=j, lo=lo, hi=hi, n_primes=int(primes_block.size), rho0_abs=rho0_abs,
        bdry_abs=bdry_abs, bdry_rel=bdry_rel,
        bdry_q=int(bdry_q), bdry_a=int(bdry_a), bdry_sign=int(bdry_sign), bdry_alpha=float(bdry_alpha),
        rnd_abs_max=rnd_abs_max, rnd_rel_max=rnd_rel_max,
        rnd_abs_mean=rnd_abs_mean, rnd_rel_mean=rnd_rel_mean,
        rnd_abs_p95=rnd_abs_p95, rnd_rel_p95=rnd_rel_p95,
    )


def parse_N_list(s: str) -> List[int]:
    out: List[int] = []
    for part in s.split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N-list", type=str, default="5000,10000,20000",
                    help="Comma-separated list of N values.")
    ap.add_argument("--Q", type=int, default=10, help="Major arcs denominator cutoff Q.")
    ap.add_argument("--t", type=float, default=0.1, help="Heat kernel parameter t>0.")
    ap.add_argument("--radius-power", type=int, default=2,
                    help="Boundary offset uses 1/N^radius_power as extra fudge.")
    ap.add_argument("--n-random", type=int, default=30, help="Number of random minor-arc α samples.")
    ap.add_argument("--n-samples", type=int, default=20,
                    help="Number of random vectors for Rayleigh sampling.")
    ap.add_argument("--n-blocks", type=int, default=3,
                    help="How many top dyadic blocks to analyze (default: 3).")
    ap.add_argument("--seed", type=int, default=0, help="RNG seed.")
    ap.add_argument("--mu-weights", action="store_true",
                    help="Use μ_p ≈ log(p)/(2π p) instead of log(p)/sqrt(p).")
    ap.add_argument("--print-blocks", action="store_true",
                    help="Print per-block breakdown.")
    args = ap.parse_args()

    Ns = parse_N_list(args.N_list)

    # Header
    header = (
        "N   primes  blocks | "
        "bdry_abs  bdry_rel  worst_q  worst_j | "
        "rnd_abs_max  rnd_rel_max  rnd_abs_mean  rnd_rel_mean  rnd_abs_p95  rnd_rel_p95"
    )
    print(header)
    print("-" * len(header))

    for N in Ns:
        primes = primes_upto(N)
        blocks = top_dyadic_blocks(primes, N, n_blocks=args.n_blocks)

        block_stats: List[BlockStats] = []
        for (j, pj, lo, hi) in blocks:
            st = compute_block_stats(
                N=N,
                Q=args.Q,
                t=args.t,
                radius_power=args.radius_power,
                primes_block=pj,
                j=j,
                lo=lo,
                hi=hi,
                n_samples=args.n_samples,
                n_random=args.n_random,
                mu_weights=args.mu_weights,
                seed=args.seed,
            )
            if st is not None:
                block_stats.append(st)

        if not block_stats:
            print(f"{N:5d} {primes.size:7d} {0:7d} | (no blocks)")
            continue

        # Aggregate: "worst" boundary across blocks by ABS rho
        worst = max(block_stats, key=lambda s: s.bdry_abs)

        # Aggregate random stats across blocks: pool all blocks' random stats approximately.
        # Here we combine by using max over blocks for max columns, and mean of means for mean columns.
        rnd_abs_max = max(s.rnd_abs_max for s in block_stats)
        rnd_rel_max = max(s.rnd_rel_max for s in block_stats)
        rnd_abs_mean = float(np.mean([s.rnd_abs_mean for s in block_stats]))
        rnd_rel_mean = float(np.mean([s.rnd_rel_mean for s in block_stats]))
        rnd_abs_p95 = float(np.mean([s.rnd_abs_p95 for s in block_stats]))
        rnd_rel_p95 = float(np.mean([s.rnd_rel_p95 for s in block_stats]))

        print(
            f"{N:5d} {primes.size:7d} {len(block_stats):7d} | "
            f"{worst.bdry_abs:8.4f} {worst.bdry_rel:8.4f} {worst.bdry_q:7d} {worst.j:7d} | "
            f"{rnd_abs_max:11.4f} {rnd_rel_max:11.4f} "
            f"{rnd_abs_mean:12.4f} {rnd_rel_mean:12.4f} "
            f"{rnd_abs_p95:11.4f} {rnd_rel_p95:11.4f}"
        )

        if args.print_blocks:
            print("  micro-block breakdown:")
            for s in sorted(block_stats, key=lambda x: x.j):
                sign = "+" if s.bdry_sign > 0 else "-"
                print(
                    f"    j={s.j:2d} [{s.lo},{s.hi}) primes={s.n_primes:4d} "
                    f"rho0_abs={s.rho0_abs:8.4f} | "
                    f"bdry_abs={s.bdry_abs:8.4f} bdry_rel={s.bdry_rel:8.4f} "
                    f"(a/q={s.bdry_a}/{s.bdry_q} {sign} , alpha={s.bdry_alpha:.8f}) | "
                    f"rnd_abs_max={s.rnd_abs_max:8.4f} rnd_rel_max={s.rnd_rel_max:8.4f}"
                )
            print()

if __name__ == "__main__":
    main()
