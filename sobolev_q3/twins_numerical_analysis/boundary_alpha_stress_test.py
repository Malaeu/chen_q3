#!/usr/bin/env python3
"""
Boundary-α stress test for Q3-2 (Circle Edition)

What it does:
  1) Enumerates "just outside major arcs" boundary points:
        α = a/q ± ( Q/(q^q_power * N) + 1/N^2 )
     for 1 <= q <= Q and gcd(a,q)=1.
  2) Computes ||B_α||_2 (via power iteration on B_α B_α*).
  3) Computes baseline ||B_0||_2 and ratio r(α) = ||B_α||/||B_0||.
  4) Compares boundary worst-case vs random minor-arc α sample.
  5) Prints table: N vs rho_worst vs rho_random (plus ratios).

Matrix model (matches Q3_2_BRIDGE_v2.x):
  primes p <= N, nodes ξ_p = log p / (2π)
  Gram: G_{pq} = exp( - (ξ_p - ξ_q)^2 / (4t) )
  weights: w(p) = log p / sqrt(p)
  twist: U_α = diag( exp(2π i α p) )

Balanced operator:
  B_α = G^{1/2} W U_α G^{1/2}
We estimate ||B_α|| by power iteration on A_α = B_α B_α* (PSD).

Notes:
  - This is expensive for large N because G is dense.
  - Use --max-primes and/or a modest Q to keep it practical.

Author: GPT 5.2 PRO (Прошка 2) for Q3 Twin Prime Project
"""

from __future__ import annotations
from dataclasses import dataclass
import argparse
import math
import time
import numpy as np


# ------------------------
# Prime utilities
# ------------------------

def primes_up_to(n: int) -> np.ndarray:
    """Return primes <= n as int64 numpy array (simple sieve)."""
    if n < 2:
        return np.array([], dtype=np.int64)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    lim = int(math.isqrt(n))
    for p in range(2, lim + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = False
    return np.nonzero(sieve)[0].astype(np.int64)


def select_primes(primes: np.ndarray, max_primes: int | None, mode: str = "all") -> np.ndarray:
    """
    Optionally downselect primes to control memory/compute.

    mode:
      - "all": keep all (default)
      - "head": keep smallest max_primes
      - "tail": keep largest max_primes
      - "stratified": roughly uniform in log-scale
    """
    if max_primes is None or primes.size <= max_primes:
        return primes
    if max_primes <= 0:
        raise ValueError("max_primes must be positive.")

    if mode == "head":
        return primes[:max_primes]
    if mode == "tail":
        return primes[-max_primes:]
    if mode == "stratified":
        # simplest stratified: uniform indices (good enough as a quick knob)
        idx = np.linspace(0, primes.size - 1, max_primes)
        idx = np.round(idx).astype(int)
        return primes[idx]

    raise ValueError(f"Unknown prime selection mode: {mode}")


# ------------------------
# Circle major/minor arcs
# ------------------------

def major_arc_radius(N: int, Q: int, q: int, q_power: int) -> float:
    # radius = Q / (q^q_power * N)
    return Q / ((q ** q_power) * N)


def dist_mod1(x: float, y: float) -> float:
    d = abs(x - y)
    return min(d, 1.0 - d)


def is_major_arc(alpha: float, N: int, Q: int, q_power: int) -> bool:
    """
    Membership test for major arcs:
      α is major if ∃ q<=Q, ∃ a (mod q), gcd(a,q)=1:
         dist_mod1(α, a/q) <= Q/(q^q_power N)
    """
    a0 = alpha % 1.0
    for q in range(1, Q + 1):
        # nearest integer to a0*q
        a = int(a0 * q + 0.5) % q
        if math.gcd(a, q) != 1:
            continue
        center = a / q
        if dist_mod1(a0, center) <= major_arc_radius(N, Q, q, q_power):
            return True
    return False


def sample_random_minor_alphas(N: int, Q: int, q_power: int, count: int, seed: int) -> list[float]:
    rng = np.random.default_rng(seed)
    out: list[float] = []
    while len(out) < count:
        a = float(rng.random())
        if not is_major_arc(a, N, Q, q_power=q_power):
            out.append(a)
    return out


def boundary_alpha_points(N: int, Q: int, q_power: int) -> list[tuple[float, int, int, int]]:
    """
    Boundary points:
      α = a/q ± ( radius + 1/N^2 ), radius = Q/(q^q_power N)
    Returns list of (alpha, q, a, sign) with sign in {+1,-1}.
    """
    eps = 1.0 / (N * N)
    pts: list[tuple[float, int, int, int]] = []
    for q in range(1, Q + 1):
        delta = major_arc_radius(N, Q, q, q_power) + eps
        for a in range(q):
            if math.gcd(a, q) == 1:
                center = a / q
                pts.append(((center + delta) % 1.0, q, a, +1))
                pts.append(((center - delta) % 1.0, q, a, -1))
    return pts


# ------------------------
# RKHS / Gram model
# ------------------------

@dataclass
class KernelContext:
    N: int
    t: float
    primes: np.ndarray          # shape (n,)
    xi: np.ndarray              # log primes / (2π), shape (n,)
    G: np.ndarray               # Gram matrix, shape (n,n)
    L: np.ndarray               # Cholesky factor (lower), G+jI = L L^T
    w: np.ndarray               # weights log p / sqrt p, shape (n,)
    jitter: float               # actual jitter used


def build_context(N: int, t: float, max_primes: int | None, prime_mode: str,
                  jitter0: float = 1e-12, max_tries: int = 12) -> KernelContext:
    primes = primes_up_to(N)
    primes = select_primes(primes, max_primes=max_primes, mode=prime_mode)
    if primes.size == 0:
        raise ValueError(f"No primes <= {N}")

    xi = np.log(primes.astype(np.float64)) / (2.0 * math.pi)
    dif = xi[:, None] - xi[None, :]
    G = np.exp(-(dif * dif) / (4.0 * t)).astype(np.float64, copy=False)

    # weights: log p / sqrt p
    w = np.log(primes.astype(np.float64)) / np.sqrt(primes.astype(np.float64))

    # Cholesky with jitter escalation
    n = primes.size
    I = np.eye(n, dtype=np.float64)
    jitter = jitter0
    L = None
    for _ in range(max_tries):
        try:
            L = np.linalg.cholesky(G + jitter * I)
            break
        except np.linalg.LinAlgError:
            jitter *= 10.0
    if L is None:
        raise np.linalg.LinAlgError("Cholesky failed even after jitter escalation.")

    return KernelContext(N=N, t=t, primes=primes, xi=xi, G=G, L=L, w=w, jitter=jitter)


def apply_A(v: np.ndarray, phase: np.ndarray, ctx: KernelContext) -> np.ndarray:
    """
    Apply A_α = B_α B_α* using Cholesky sqrt:

      B_α = G^{1/2} W U_α G^{1/2}
      A_α = B_α B_α* = G^{1/2} W U_α G U_α* W G^{1/2}

    If G = L L^T (Cholesky), then A_α is unitarily similar to:
      A'_α = L^T W U_α G U_α* W L
    and has the same eigenvalues.

    We use the action of A'_α for power iteration.
    """
    x = ctx.L @ v
    x = ctx.w * x
    x = np.conj(phase) * x     # U_α*
    x = ctx.G @ x
    x = phase * x              # U_α
    x = ctx.w * x
    x = ctx.L.T @ x
    return x


def power_iteration_norm_B(alpha: float, ctx: KernelContext,
                           n_iter: int = 20,
                           tol: float = 1e-6,
                           v0: np.ndarray | None = None,
                           seed: int = 0) -> tuple[float, np.ndarray]:
    """
    Approximate ||B_α||_2 via power iteration on A_α = B_α B_α* (PSD).

    Returns:
      (norm_B, v_last)
    """
    n = ctx.primes.size
    if v0 is None:
        rng = np.random.default_rng(seed)
        v = (rng.normal(size=n) + 1j * rng.normal(size=n)).astype(np.complex128)
    else:
        v = v0.astype(np.complex128, copy=True)
    v /= np.linalg.norm(v)

    phase = np.exp(2j * math.pi * (alpha % 1.0) * ctx.primes.astype(np.float64))

    lam_prev = 0.0
    lam = 0.0
    for _ in range(n_iter):
        Av = apply_A(v, phase, ctx)
        lam = float(np.vdot(v, Av).real)  # PSD => real >=0 (up to tiny imag noise)
        normAv = float(np.linalg.norm(Av))
        if normAv == 0.0:
            return 0.0, v
        v = Av / normAv
        if lam_prev > 0 and abs(lam - lam_prev) / lam_prev < tol:
            break
        lam_prev = lam

    return math.sqrt(max(lam, 0.0)), v


def estimate_max_over_alphas(alphas: list[tuple[float, int, int, int]],
                             ctx: KernelContext,
                             baseline_v0: np.ndarray,
                             n_iter_fast: int,
                             n_iter_refine: int,
                             refine_top_k: int,
                             seed: int) -> tuple[float, tuple[float, int, int, int]]:
    """
    Two-stage max search:
      1) fast screen for all α (few iters),
      2) refine top-K candidates with more iterations.

    Returns (max_norm, argmax_record).
    """
    scored: list[tuple[float, tuple[float, int, int, int]]] = []
    for rec in alphas:
        alpha = rec[0]
        est, _ = power_iteration_norm_B(alpha, ctx, n_iter=n_iter_fast, v0=baseline_v0, seed=seed)
        scored.append((est, rec))

    scored.sort(key=lambda x: x[0], reverse=True)
    candidates = scored[: max(1, refine_top_k)]

    best_val = -1.0
    best_rec = candidates[0][1]
    for _, rec in candidates:
        alpha = rec[0]
        val, _ = power_iteration_norm_B(alpha, ctx, n_iter=n_iter_refine, v0=baseline_v0, seed=seed)
        if val > best_val:
            best_val = val
            best_rec = rec

    return best_val, best_rec


def run_for_N(N: int, Q: int, t: float, q_power: int,
              n_alpha_random: int, seed: int,
              max_primes: int | None, prime_mode: str,
              n_iter_fast: int, n_iter_refine: int, refine_top_k: int,
              max_boundary_points: int | None) -> dict:
    t0 = time.time()
    ctx = build_context(N=N, t=t, max_primes=max_primes, prime_mode=prime_mode)

    # Baseline ||B_0||
    rho0, v0 = power_iteration_norm_B(0.0, ctx, n_iter=n_iter_refine, seed=seed)

    # Boundary α list (just outside major arcs)
    boundary = boundary_alpha_points(N, Q, q_power=q_power)
    if max_boundary_points is not None and len(boundary) > max_boundary_points:
        rng = np.random.default_rng(seed + 12345)
        idx = rng.choice(len(boundary), size=max_boundary_points, replace=False)
        boundary = [boundary[int(i)] for i in idx]

    rho_worst, worst_rec = estimate_max_over_alphas(
        boundary, ctx, baseline_v0=v0,
        n_iter_fast=n_iter_fast, n_iter_refine=n_iter_refine, refine_top_k=refine_top_k, seed=seed
    )

    # Random α in minor arcs
    rand_alphas = sample_random_minor_alphas(N, Q, q_power=q_power, count=n_alpha_random, seed=seed + 777)
    rand_recs = [(a, -1, -1, 0) for a in rand_alphas]
    rho_random, rand_rec = estimate_max_over_alphas(
        rand_recs, ctx, baseline_v0=v0,
        n_iter_fast=n_iter_fast, n_iter_refine=n_iter_refine, refine_top_k=min(refine_top_k, len(rand_recs)),
        seed=seed + 999
    )

    elapsed = time.time() - t0

    out = {
        "N": N,
        "Q": Q,
        "q_power": q_power,
        "t": t,
        "n_primes": int(ctx.primes.size),
        "jitter": float(ctx.jitter),
        "rho0": float(rho0),
        "rho_worst": float(rho_worst),
        "rho_random": float(rho_random),
        "r_worst": float(rho_worst / rho0) if rho0 != 0 else float("nan"),
        "r_random": float(rho_random / rho0) if rho0 != 0 else float("nan"),
        "worst_alpha": float(worst_rec[0]),
        "worst_q": int(worst_rec[1]),
        "worst_a": int(worst_rec[2]),
        "worst_sign": int(worst_rec[3]),
        "rand_alpha": float(rand_rec[0]),
        "elapsed_sec": float(elapsed),
    }
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", nargs="+", type=int, required=True,
                    help="List of N values (e.g. --N 5000 10000 50000)")
    ap.add_argument("--Q", type=int, required=True,
                    help="Major arc denominator cutoff Q (scan q=1..Q)")
    ap.add_argument("--q-power", type=int, default=2, choices=[1, 2],
                    help="Major arc radius uses q^q_power (default 2 to match v2.4 formalization).")
    ap.add_argument("--t", type=float, default=0.1, help="Heat kernel parameter t>0 (default 0.1)")
    ap.add_argument("--n-alpha-random", type=int, default=50, help="Number of random minor-arc α samples")
    ap.add_argument("--seed", type=int, default=0, help="RNG seed")
    ap.add_argument("--max-primes", type=int, default=None, help="Cap number of primes to control memory")
    ap.add_argument("--prime-mode", type=str, default="all",
                    choices=["all", "head", "tail", "stratified"],
                    help="How to downselect primes if --max-primes is set")
    ap.add_argument("--n-iter-fast", type=int, default=6, help="Power-iteration steps for screening")
    ap.add_argument("--n-iter-refine", type=int, default=20, help="Power-iteration steps for refinement")
    ap.add_argument("--refine-top-k", type=int, default=25, help="How many α to refine after screening")
    ap.add_argument("--max-boundary-points", type=int, default=None,
                    help="Optional cap: randomly subsample boundary α points (useful if Q is large).")
    ap.add_argument("--csv", type=str, default=None, help="Optional path to write CSV summary")

    args = ap.parse_args()

    rows = []
    for N in args.N:
        print("=" * 72)
        print(f"N={N}  Q={args.Q}  q_power={args.q_power}  t={args.t}")
        row = run_for_N(
            N=N, Q=args.Q, t=args.t, q_power=args.q_power,
            n_alpha_random=args.n_alpha_random, seed=args.seed,
            max_primes=args.max_primes, prime_mode=args.prime_mode,
            n_iter_fast=args.n_iter_fast, n_iter_refine=args.n_iter_refine,
            refine_top_k=args.refine_top_k,
            max_boundary_points=args.max_boundary_points,
        )
        rows.append(row)

        print(f"primes={row['n_primes']}  jitter={row['jitter']:.1e}  elapsed={row['elapsed_sec']:.1f}s")
        print(f"||B_0||      = {row['rho0']:.6g}")
        print(f"||B||_worst  = {row['rho_worst']:.6g}   at α={row['worst_alpha']:.6g}  (q={row['worst_q']}, a={row['worst_a']}, sign={row['worst_sign']:+d})")
        print(f"||B||_random = {row['rho_random']:.6g}  at α={row['rand_alpha']:.6g}")
        print(f"r_worst  = ||B||_worst/||B_0||  = {row['r_worst']:.6g}")
        print(f"r_random = ||B||_random/||B_0|| = {row['r_random']:.6g}")

    print("\n" + "=" * 72)
    print("SUMMARY (N vs rho_worst vs rho_random)")
    header = f"{'N':>10}  {'primes':>8}  {'rho_worst':>12}  {'rho_random':>12}  {'r_worst':>10}  {'r_random':>10}"
    print(header)
    print("-" * len(header))
    for row in rows:
        print(f"{row['N']:>10d}  {row['n_primes']:>8d}  {row['rho_worst']:>12.6g}  {row['rho_random']:>12.6g}  {row['r_worst']:>10.6g}  {row['r_random']:>10.6g}")

    if args.csv:
        import csv
        with open(args.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            for row in rows:
                w.writerow(row)
        print(f"\nWrote CSV → {args.csv}")


if __name__ == "__main__":
    main()
