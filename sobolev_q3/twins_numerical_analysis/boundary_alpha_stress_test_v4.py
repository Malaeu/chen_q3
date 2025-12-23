#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Boundary-α stress test v4 (Power Iteration, no G^{-1})

Key insight from Gemini Flash 3:
- G^{-1} explodes when G ≈ 1_{n×n} (upper dyadic blocks)
- Power Iteration finds spectral radius without inversion
- Metric: ‖B_α‖ / ‖B_0‖ (v1-style, stable)

We compute:
  B_α = G^{1/2} W U_α G^{1/2}  (balanced operator)

But to avoid sqrt(G), we work with B_α* B_α directly:
  M_α = G W U_α* G U_α W  (Hermitian, for power iteration)

Then: ‖B_α‖² = λ_max(M_α)

Power Iteration: v_{k+1} = M_α v_k / ‖M_α v_k‖
After convergence: λ_max ≈ ‖M_α v‖ / ‖v‖

CLI:
--N-list, --Q, --t, --n-blocks, --print-blocks (same as v3)
--power-steps : number of power iteration steps (default 30)
"""

import argparse
import math
from dataclasses import dataclass
from typing import List, Tuple, Optional

import numpy as np


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
    """Returns last n_blocks dyadic blocks near N."""
    if N < 2:
        return []
    j_max = int(math.log2(N))
    j_min = max(0, j_max - n_blocks + 1)
    out: List[Tuple[int, np.ndarray, int, int]] = []
    for j in range(j_min, j_max + 1):
        lo = 2 ** j
        hi = min(2 ** (j + 1), N + 1)
        mask = (primes >= lo) & (primes < hi)
        pj = primes[mask]
        if pj.size > 0:
            out.append((j, pj, lo, hi))
    return out


# ----------------------------
# Major/minor arcs + sampling
# ----------------------------

def mod1_dist(a: float, b: float) -> float:
    d = a - b
    d -= round(d)
    return abs(d)


def in_major_arcs(alpha: float, N: int, Q: int) -> bool:
    for q in range(1, Q + 1):
        rad = Q / (q * N)
        for a in range(1, q + 1):
            if math.gcd(a, q) != 1:
                continue
            if mod1_dist(alpha, a / q) <= rad:
                return True
    return False


def boundary_alphas(N: int, Q: int, radius_power: int) -> List[Tuple[float, int, int, int]]:
    """Boundary points just outside major arcs."""
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
    out: List[float] = []
    while len(out) < n:
        a = float(rng.random())
        if not in_major_arcs(a, N, Q):
            out.append(a)
    return out


# ----------------------------
# Gram matrix
# ----------------------------

def build_gram(primes: np.ndarray, t: float) -> np.ndarray:
    """Heat-kernel Gram: G_{pq} = exp(-(log(p/q))^2 / (16π²t))"""
    logs = np.log(primes.astype(np.float64))
    diff = logs[:, None] - logs[None, :]
    denom = 16.0 * (math.pi ** 2) * t
    return np.exp(-(diff * diff) / denom)


def compute_weights(primes: np.ndarray, mu_weights: bool) -> np.ndarray:
    """Default: w(p)=log(p)/sqrt(p). With mu_weights: log(p)/(2πp)."""
    p = primes.astype(np.float64)
    lp = np.log(p)
    if mu_weights:
        return lp / (2.0 * math.pi * p)
    return lp / np.sqrt(p)


# ----------------------------
# Power Iteration (NO G^{-1}!)
# ----------------------------

def spectral_radius_power_iter(
    G: np.ndarray,
    W: np.ndarray,
    alpha: float,
    primes: np.ndarray,
    steps: int = 30,
    rng: Optional[np.random.Generator] = None
) -> float:
    """
    Compute ‖B_α‖ via power iteration on M_α = B_α* B_α.

    B_α = G^{1/2} W U_α G^{1/2}
    M_α = B_α* B_α = G^{1/2} U_α* W G W U_α G^{1/2}

    To avoid sqrt(G), we work with the similar operator:
    M'_α = G W* U_α* G U_α W  (conjugated by G^{1/2})

    Power iteration: v_{k+1} = M'_α v_k normalized
    λ_max(M'_α) = ‖B_α‖²
    """
    n = G.shape[0]
    if n == 0:
        return 0.0

    if rng is None:
        rng = np.random.default_rng()

    # Initialize with random complex vector
    v = rng.standard_normal(n) + 1j * rng.standard_normal(n)
    v = v / np.linalg.norm(v)

    # Phase diagonal: U_α = diag(e^{2πi α p})
    p_float = primes.astype(np.float64)
    phase = np.exp(2j * math.pi * alpha * p_float)  # U_α diagonal
    phase_conj = np.conj(phase)  # U_α*

    # Power iteration on M'_α = G W* U_α* G U_α W
    # Actually for real weights W, W* = W
    # M'_α v = G @ (W * (phase_conj * (G @ (phase * (W * v)))))

    eigenvalue = 0.0
    for _ in range(steps):
        # Apply M'_α = G W U_α* G U_α W
        z = W * v                      # W v
        z = phase * z                  # U_α W v
        z = G @ z                      # G U_α W v
        z = phase_conj * z             # U_α* G U_α W v
        z = W * z                      # W U_α* G U_α W v
        z = G @ z                      # G W U_α* G U_α W v = M'_α v

        # Rayleigh quotient estimate
        eigenvalue = float(np.real(np.vdot(v, z)))

        # Normalize
        norm_z = np.linalg.norm(z)
        if norm_z < 1e-300:
            break
        v = z / norm_z

    # ‖B_α‖ = sqrt(λ_max(M'_α))
    return math.sqrt(max(eigenvalue, 0.0))


# ----------------------------
# Block statistics
# ----------------------------

@dataclass
class BlockStats:
    j: int
    lo: int
    hi: int
    n_primes: int

    norm_0: float      # ‖B_0‖ (baseline)
    norm_bdry: float   # ‖B_α‖ worst boundary
    r_bdry: float      # ‖B_α‖ / ‖B_0‖
    bdry_q: int
    bdry_a: int
    bdry_sign: int
    bdry_alpha: float

    norm_rnd_max: float
    r_rnd_max: float
    norm_rnd_mean: float
    r_rnd_mean: float


def compute_block_stats(
    N: int,
    Q: int,
    t: float,
    radius_power: int,
    primes_block: np.ndarray,
    j: int,
    lo: int,
    hi: int,
    power_steps: int,
    n_random: int,
    mu_weights: bool,
    seed: int,
) -> Optional[BlockStats]:
    if primes_block.size < 2:
        return None

    G = build_gram(primes_block, t=t)
    W = compute_weights(primes_block, mu_weights=mu_weights)
    rng = np.random.default_rng(seed + 10_000 * j + N)

    # Baseline α=0
    norm_0 = spectral_radius_power_iter(G, W, 0.0, primes_block, power_steps, rng)

    # Boundary alphas
    bdry = boundary_alphas(N=N, Q=Q, radius_power=radius_power)
    bdry_norms = []
    for (alpha, q, a, sign) in bdry:
        norm_alpha = spectral_radius_power_iter(G, W, alpha, primes_block, power_steps, rng)
        bdry_norms.append((norm_alpha, alpha, q, a, sign))

    # Worst boundary
    worst = max(bdry_norms, key=lambda x: x[0])
    norm_bdry, bdry_alpha, bdry_q, bdry_a, bdry_sign = worst
    r_bdry = norm_bdry / norm_0 if norm_0 > 0 else float('nan')

    # Random minor alphas
    rnd_alphas = sample_random_minor_alphas(N=N, Q=Q, n=n_random, rng=rng)
    rnd_norms = [spectral_radius_power_iter(G, W, a, primes_block, power_steps, rng) for a in rnd_alphas]

    norm_rnd_max = max(rnd_norms) if rnd_norms else 0.0
    r_rnd_max = norm_rnd_max / norm_0 if norm_0 > 0 else float('nan')
    norm_rnd_mean = float(np.mean(rnd_norms)) if rnd_norms else 0.0
    r_rnd_mean = norm_rnd_mean / norm_0 if norm_0 > 0 else float('nan')

    return BlockStats(
        j=j, lo=lo, hi=hi, n_primes=int(primes_block.size),
        norm_0=norm_0,
        norm_bdry=norm_bdry, r_bdry=r_bdry,
        bdry_q=int(bdry_q), bdry_a=int(bdry_a), bdry_sign=int(bdry_sign), bdry_alpha=float(bdry_alpha),
        norm_rnd_max=norm_rnd_max, r_rnd_max=r_rnd_max,
        norm_rnd_mean=norm_rnd_mean, r_rnd_mean=r_rnd_mean,
    )


def parse_N_list(s: str) -> List[int]:
    return [int(x.strip()) for x in s.split(",") if x.strip()]


def main() -> None:
    ap = argparse.ArgumentParser(description="Boundary-α stress test v4 (Power Iteration)")
    ap.add_argument("--N-list", type=str, default="5000,10000,20000")
    ap.add_argument("--Q", type=int, default=10)
    ap.add_argument("--t", type=float, default=0.1)
    ap.add_argument("--radius-power", type=int, default=2)
    ap.add_argument("--n-random", type=int, default=30)
    ap.add_argument("--power-steps", type=int, default=30)
    ap.add_argument("--n-blocks", type=int, default=3)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--mu-weights", action="store_true")
    ap.add_argument("--print-blocks", action="store_true")
    args = ap.parse_args()

    Ns = parse_N_list(args.N_list)

    print("=" * 100)
    print("BOUNDARY-α STRESS TEST v4 (Power Iteration, NO G^{-1})")
    print(f"Parameters: Q={args.Q}, t={args.t}, power_steps={args.power_steps}, mu_weights={args.mu_weights}")
    print("=" * 100)
    print()

    header = "    N  primes  blocks | ‖B_0‖    ‖B_α‖_bdry  r_bdry   worst_q  worst_j | ‖B_α‖_rnd_max  r_rnd_max  r_rnd_mean"
    print(header)
    print("-" * len(header))

    for N in Ns:
        primes = primes_upto(N)
        blocks = top_dyadic_blocks(primes, N, n_blocks=args.n_blocks)

        block_stats: List[BlockStats] = []
        for (j, pj, lo, hi) in blocks:
            st = compute_block_stats(
                N=N, Q=args.Q, t=args.t, radius_power=args.radius_power,
                primes_block=pj, j=j, lo=lo, hi=hi,
                power_steps=args.power_steps, n_random=args.n_random,
                mu_weights=args.mu_weights, seed=args.seed,
            )
            if st:
                block_stats.append(st)

        if not block_stats:
            print(f"{N:5d} {primes.size:7d} {0:7d} | (no blocks)")
            continue

        # Aggregate: worst boundary across blocks
        worst = max(block_stats, key=lambda s: s.r_bdry if not math.isnan(s.r_bdry) else -1)

        # Aggregate random stats
        r_rnd_max = max(s.r_rnd_max for s in block_stats if not math.isnan(s.r_rnd_max))
        r_rnd_mean = float(np.mean([s.r_rnd_mean for s in block_stats if not math.isnan(s.r_rnd_mean)]))
        norm_rnd_max = max(s.norm_rnd_max for s in block_stats)

        status = "✅ PASS" if worst.r_bdry < 1.0 else "❌ FAIL"

        print(
            f"{N:5d} {primes.size:7d} {len(block_stats):7d} | "
            f"{worst.norm_0:7.4f}  {worst.norm_bdry:10.4f}  {worst.r_bdry:7.4f}  "
            f"{worst.bdry_q:7d}  {worst.j:7d} | "
            f"{norm_rnd_max:13.4f}  {r_rnd_max:9.4f}  {r_rnd_mean:10.4f}  {status}"
        )

        if args.print_blocks:
            print("  Micro-block breakdown:")
            for s in sorted(block_stats, key=lambda x: x.j):
                sign = "+" if s.bdry_sign > 0 else "-"
                status_j = "✅" if s.r_bdry < 1.0 else "❌"
                print(
                    f"    j={s.j:2d} [{s.lo},{s.hi}) n={s.n_primes:4d} | "
                    f"‖B_0‖={s.norm_0:8.4f} | "
                    f"‖B_α‖={s.norm_bdry:8.4f} r={s.r_bdry:6.4f} "
                    f"(a/q={s.bdry_a}/{s.bdry_q} {sign}) | "
                    f"rnd_max={s.r_rnd_max:6.4f} {status_j}"
                )
            print()

    print()
    print("=" * 100)
    print("INTERPRETATION:")
    print("  r_bdry = ‖B_α‖ / ‖B_0‖  (relative contraction)")
    print("  r_bdry < 1 means phases SUPPRESS the operator (GOOD)")
    print("  r_bdry > 1 means phases AMPLIFY the operator (BAD)")
    print("=" * 100)


if __name__ == "__main__":
    main()
