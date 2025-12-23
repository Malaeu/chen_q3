#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Boundary-α stress test v5 (Power Iteration + P2 Debug)

Combines:
- v4 Power Iteration approach (Gemini Flash 3)
- P2 debug functions (stable_factor_psd, exact comparison)
- P1 Q3-2_rel formulation

Key insight (P2):
- α = 1/2 → U = -I for odd primes, so phases don't affect (normal!)
- At α ≈ 1/6 ± Q/(qN) should get rho_rel ≈ 0.4-0.5 < 1

Debug features:
--debug : compare power iteration vs exact eigvalsh for small blocks
--scientific : use scientific notation in output
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


def phase_vec(alpha: float, primes: np.ndarray) -> np.ndarray:
    """Phase vector: exp(2πi α p) for each prime p."""
    return np.exp(2j * math.pi * alpha * primes.astype(np.float64))


# ----------------------------
# P2: Stable PSD factorization
# ----------------------------

def stable_factor_psd(G: np.ndarray,
                      jitter0: float = 1e-12,
                      max_tries: int = 8,
                      mult: float = 10.0) -> Tuple[np.ndarray, float, str]:
    """
    Return L such that G_reg ≈ L L*, with G_reg = sym(G) + jitter*I.
    Tries Cholesky; if it fails, falls back to eigen-factorization.
    """
    G = 0.5 * (G + G.conj().T)
    n = G.shape[0]
    I = np.eye(n, dtype=G.dtype)

    jitter = jitter0
    for _ in range(max_tries):
        try:
            L = np.linalg.cholesky(G + jitter * I)
            return L, jitter, "chol"
        except np.linalg.LinAlgError:
            jitter *= mult

    # Fallback: eigen-factor
    evals, evecs = np.linalg.eigh(G)
    evals = np.maximum(evals, 0.0) + jitter
    L = evecs @ np.diag(np.sqrt(evals))
    return L, jitter, "eigh"


# ----------------------------
# P2: Power Iteration (improved)
# ----------------------------

def power_iteration_hermitian(mv, n: int,
                              n_iter: int = 250,
                              tol: float = 1e-9,
                              seed: int = 0) -> Tuple[float, np.ndarray, int]:
    """
    Power iteration for largest eigenvalue of Hermitian PSD operator.
    Returns (lambda_max, eigenvector, iterations_used).
    """
    rng = np.random.default_rng(seed)
    v = rng.standard_normal(n) + 1j * rng.standard_normal(n)
    v = v.astype(np.complex128)
    v /= np.linalg.norm(v)

    lam_old = 0.0
    for it in range(1, n_iter + 1):
        w = mv(v)
        lam = float(np.vdot(v, w).real)  # Rayleigh quotient

        nw = np.linalg.norm(w)
        if nw == 0.0:
            return 0.0, v, it

        v = w / nw

        if it > 2 and abs(lam - lam_old) <= tol * max(1.0, abs(lam_old)):
            return lam, v, it
        lam_old = lam

    return lam_old, v, n_iter


def rho_abs_power(G: np.ndarray,
                  w: np.ndarray,
                  phase: np.ndarray,
                  jitter0: float = 1e-12,
                  n_iter: int = 250,
                  tol: float = 1e-9,
                  seed: int = 0) -> Tuple[float, dict]:
    """
    Compute rho_abs = ||B_alpha|| via power iteration.

    ||B_alpha||^2 = lambda_max(L^* (W U G U^* W) L)
    with G ≈ L L* from stable_factor_psd.
    """
    G = 0.5 * (G + G.conj().T)
    n = G.shape[0]

    L, jitter_used, factor_kind = stable_factor_psd(G, jitter0=jitter0)

    w = w.astype(np.complex128)
    phase = phase.astype(np.complex128)
    conj_phase = phase.conj()

    # A_alpha x = W U (G (U^* (W x)))
    def apply_A(x: np.ndarray) -> np.ndarray:
        x = w * x
        x = conj_phase * x
        x = G @ x
        x = phase * x
        x = w * x
        return x

    # M_alpha u = L^* A_alpha (L u)
    def mv(u: np.ndarray) -> np.ndarray:
        x = L @ u
        x = apply_A(x)
        return L.conj().T @ x

    lam, v, it = power_iteration_hermitian(mv, n, n_iter=n_iter, tol=tol, seed=seed)
    lam = max(lam, 0.0)
    return math.sqrt(lam), {"iters": it, "jitter": jitter_used, "factor": factor_kind}


# ----------------------------
# P2: Exact computation (for debug)
# ----------------------------

def rho_abs_exact(G: np.ndarray,
                  w: np.ndarray,
                  phase: np.ndarray,
                  jitter: float = 1e-12) -> float:
    """
    Exact computation via eigvalsh for small blocks (n <= 200).
    For debugging: compare with power iteration.
    """
    G = 0.5 * (G + G.conj().T)
    n = G.shape[0]
    G = G + jitter * np.eye(n)

    try:
        L = np.linalg.cholesky(G)
    except np.linalg.LinAlgError:
        evals, evecs = np.linalg.eigh(G)
        evals = np.maximum(evals, jitter)
        L = evecs @ np.diag(np.sqrt(evals))

    W = np.diag(w.astype(np.complex128))
    U = np.diag(phase.astype(np.complex128))
    A = W @ U @ G @ U.conj().T @ W
    M = L.conj().T @ A @ L
    M = 0.5 * (M + M.conj().T)  # ensure Hermitian
    lam = np.linalg.eigvalsh(M)[-1].real
    return math.sqrt(max(lam, 0.0))


# ----------------------------
# Block statistics
# ----------------------------

@dataclass
class BlockStats:
    j: int
    lo: int
    hi: int
    n_primes: int

    norm_0: float
    norm_bdry: float
    r_bdry: float
    bdry_q: int
    bdry_a: int
    bdry_sign: int
    bdry_alpha: float

    norm_rnd_max: float
    r_rnd_max: float
    norm_rnd_mean: float
    r_rnd_mean: float

    # Debug info
    factor_kind: str
    jitter_used: float
    iters_used: int


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
    power_tol: float,
    jitter: float,
    n_random: int,
    mu_weights: bool,
    seed: int,
    debug: bool = False,
) -> Optional[BlockStats]:
    if primes_block.size < 2:
        return None

    G = build_gram(primes_block, t=t)
    W = compute_weights(primes_block, mu_weights=mu_weights)
    rng = np.random.default_rng(seed + 10_000 * j + N)

    # Baseline α=0
    phase0 = np.ones(primes_block.size, dtype=np.complex128)
    norm_0, info0 = rho_abs_power(G, W, phase0, jitter0=jitter, n_iter=power_steps, tol=power_tol, seed=seed)

    # Debug: compare with exact for small blocks
    if debug and primes_block.size <= 200:
        exact_0 = rho_abs_exact(G, W, phase0, jitter=jitter)
        rel_err = abs(norm_0 - exact_0) / max(exact_0, 1e-12)
        print(f"    [DEBUG j={j}] α=0: power={norm_0:.6e} exact={exact_0:.6e} rel_err={rel_err:.2e}")

    # Boundary alphas
    bdry = boundary_alphas(N=N, Q=Q, radius_power=radius_power)
    best_norm = -1.0
    best_info = (0.0, 0, 0, 0)

    for (alpha, q, a, sign) in bdry:
        ph = phase_vec(alpha, primes_block)
        norm_alpha, info = rho_abs_power(G, W, ph, jitter0=jitter, n_iter=power_steps, tol=power_tol, seed=seed+q*100+a)

        if norm_alpha > best_norm:
            best_norm = norm_alpha
            best_info = (alpha, q, a, sign)
            best_iters = info["iters"]

    norm_bdry = best_norm
    bdry_alpha, bdry_q, bdry_a, bdry_sign = best_info
    r_bdry = norm_bdry / norm_0 if norm_0 > 0 else float('nan')

    # Debug: compare worst boundary with exact
    if debug and primes_block.size <= 200:
        ph = phase_vec(bdry_alpha, primes_block)
        exact_bdry = rho_abs_exact(G, W, ph, jitter=jitter)
        rel_err = abs(norm_bdry - exact_bdry) / max(exact_bdry, 1e-12)
        print(f"    [DEBUG j={j}] α={bdry_alpha:.6f}: power={norm_bdry:.6e} exact={exact_bdry:.6e} rel_err={rel_err:.2e}")

    # Random minor alphas
    rnd_alphas = sample_random_minor_alphas(N=N, Q=Q, n=n_random, rng=rng)
    rnd_norms = []
    for a in rnd_alphas:
        ph = phase_vec(a, primes_block)
        norm_a, _ = rho_abs_power(G, W, ph, jitter0=jitter, n_iter=power_steps, tol=power_tol, seed=seed+int(a*1000))
        rnd_norms.append(norm_a)

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
        factor_kind=info0["factor"],
        jitter_used=info0["jitter"],
        iters_used=info0["iters"],
    )


def parse_N_list(s: str) -> List[int]:
    return [int(x.strip()) for x in s.split(",") if x.strip()]


def main() -> None:
    ap = argparse.ArgumentParser(description="Boundary-α stress test v5 (Power Iteration + P2 Debug)")
    ap.add_argument("--N-list", type=str, default="5000,10000,20000")
    ap.add_argument("--Q", type=int, default=10)
    ap.add_argument("--t", type=float, default=0.1)
    ap.add_argument("--radius-power", type=int, default=2)
    ap.add_argument("--n-random", type=int, default=30)
    ap.add_argument("--power-steps", type=int, default=250, help="Power iteration steps")
    ap.add_argument("--power-tol", type=float, default=1e-9, help="Power iteration tolerance")
    ap.add_argument("--jitter", type=float, default=1e-12, help="Regularization jitter")
    ap.add_argument("--n-blocks", type=int, default=3)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--mu-weights", action="store_true")
    ap.add_argument("--print-blocks", action="store_true")
    ap.add_argument("--debug", action="store_true", help="Compare power vs exact for small blocks")
    ap.add_argument("--scientific", action="store_true", help="Use scientific notation")
    args = ap.parse_args()

    Ns = parse_N_list(args.N_list)

    print("=" * 110)
    print("BOUNDARY-α STRESS TEST v5 (Power Iteration + P2 Debug)")
    print(f"Parameters: Q={args.Q}, t={args.t}, power_steps={args.power_steps}, mu_weights={args.mu_weights}")
    print(f"Debug: {args.debug}, Scientific: {args.scientific}")
    print("=" * 110)
    print()

    # Format strings
    if args.scientific:
        fmt_norm = ".3e"
        fmt_r = ".4f"
    else:
        fmt_norm = ".4f"
        fmt_r = ".4f"

    header = f"{'N':>6} {'primes':>7} {'blk':>3} | {'‖B_0‖':>10} {'‖B_α‖_bdry':>12} {'r_bdry':>8} {'q':>3} {'j':>3} | {'r_rnd_max':>10} {'r_rnd_mean':>11} | Status"
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
                power_steps=args.power_steps, power_tol=args.power_tol,
                jitter=args.jitter, n_random=args.n_random,
                mu_weights=args.mu_weights, seed=args.seed,
                debug=args.debug,
            )
            if st:
                block_stats.append(st)

        if not block_stats:
            print(f"{N:6d} {primes.size:7d} {0:3d} | (no blocks)")
            continue

        # Aggregate: worst boundary across blocks
        worst = max(block_stats, key=lambda s: s.r_bdry if not math.isnan(s.r_bdry) else -1)

        # Aggregate random stats
        r_rnd_max = max(s.r_rnd_max for s in block_stats if not math.isnan(s.r_rnd_max))
        r_rnd_mean = float(np.mean([s.r_rnd_mean for s in block_stats if not math.isnan(s.r_rnd_mean)]))

        status = "✅ PASS" if worst.r_bdry < 1.0 else "❌ FAIL"

        print(
            f"{N:6d} {primes.size:7d} {len(block_stats):3d} | "
            f"{worst.norm_0:{fmt_norm}} {worst.norm_bdry:{fmt_norm}} {worst.r_bdry:{fmt_r}} "
            f"{worst.bdry_q:3d} {worst.j:3d} | "
            f"{r_rnd_max:{fmt_r}} {r_rnd_mean:{fmt_r}} | {status}"
        )

        if args.print_blocks:
            print("  Micro-block breakdown:")
            for s in sorted(block_stats, key=lambda x: x.j):
                sign = "+" if s.bdry_sign > 0 else "-"
                status_j = "✅" if s.r_bdry < 1.0 else "❌"
                print(
                    f"    j={s.j:2d} [{s.lo},{s.hi}) n={s.n_primes:4d} | "
                    f"‖B_0‖={s.norm_0:{fmt_norm}} | "
                    f"‖B_α‖={s.norm_bdry:{fmt_norm}} r={s.r_bdry:{fmt_r}} "
                    f"(a/q={s.bdry_a}/{s.bdry_q} {sign}) | "
                    f"rnd_max={s.r_rnd_max:{fmt_r}} | "
                    f"fact={s.factor_kind} jit={s.jitter_used:.0e} it={s.iters_used} {status_j}"
                )
            print()

    print()
    print("=" * 110)
    print("INTERPRETATION:")
    print("  r_bdry = ‖B_α‖ / ‖B_0‖  (relative contraction, Q3-2_rel)")
    print("  r_bdry < 1 means phases SUPPRESS the operator (GOOD)")
    print("  r_bdry > 1 means phases AMPLIFY the operator (BAD)")
    print()
    print("P2 INSIGHT: α ≈ 1/6 (q=6) should give r ≈ 0.4-0.5 < 1")
    print("           α = 1/2 gives U = -I for odd primes (no cancellation, normal!)")
    print("=" * 110)


if __name__ == "__main__":
    main()
