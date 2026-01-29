#!/usr/bin/env python3
"""
Stronger numerical verification of Q(Φ) with explicit tail control.

- Uses the same definitions as Lean (xi_n, w_Q, fejer_heat_window, Q).
- Sums the prime term over prime powers up to N_max.
- Bounds the tail using Λ(n) ≤ log n and Φ(ξ_n) ≤ exp(-t (log n)^2).

This gives rigorous sign brackets:
  Q_lower = arch_term - (prime_partial + tail_bound)
  Q_upper = arch_term - prime_partial
So if Q_lower > 0 => Q > 0, and if Q_upper < 0 => Q < 0.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import List, Tuple

import numpy as np
from scipy import integrate
from scipy.special import digamma

PI = math.pi


# === Lean-aligned definitions ===

def xi_n(n: int) -> float:
    return math.log(n) / (2 * PI)


def w_Q_prime_power(p: int, k: int) -> float:
    """w_Q(p^k) = 2 * log(p) / sqrt(p^k)."""
    return 2.0 * math.log(p) / math.sqrt(p ** k)


def a(xi: float) -> float:
    z = 0.25 + 1j * PI * xi
    return math.log(PI) - float(np.real(digamma(z)))


def a_star(xi: float) -> float:
    return 2 * PI * a(xi)


def fejer_heat_window(B: float, t: float, xi: float) -> float:
    fejer = max(0.0, 1.0 - abs(xi) / B)
    if fejer == 0.0:
        return 0.0
    return fejer * math.exp(-4.0 * PI * PI * t * xi * xi)


# === Prime power enumeration ===

def primes_upto(n: int) -> np.ndarray:
    """Simple sieve of Eratosthenes returning primes <= n."""
    if n < 2:
        return np.array([], dtype=np.int64)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    lim = int(math.isqrt(n))
    for p in range(2, lim + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start : n + 1 : step] = False
    return np.nonzero(sieve)[0]


def prime_powers_data(n_max: int) -> Tuple[np.ndarray, np.ndarray]:
    """
    Return arrays (xi_arr, w_arr) for all prime powers p^k <= n_max.
    w_arr already includes the factor 2*log(p)/sqrt(p^k).
    """
    primes = primes_upto(n_max)
    xi_list: List[float] = []
    w_list: List[float] = []
    for p in primes:
        logp = math.log(int(p))
        pk = int(p)
        k = 1
        while pk <= n_max:
            logn = math.log(pk)
            xi_list.append(logn / (2 * PI))
            w_list.append(2.0 * logp / math.sqrt(pk))
            # avoid overflow in pk *= p
            if pk > n_max // p:
                break
            pk *= p
            k += 1
    xi_arr = np.array(xi_list, dtype=np.float64)
    w_arr = np.array(w_list, dtype=np.float64)
    return xi_arr, w_arr


# === Tail bound ===

def tail_bound(N: int, t: float) -> float:
    """
    Upper bound for sum_{n>N} 2 log n / sqrt(n) * exp(-t (log n)^2).

    Uses integral test after change of variables u = log n:
    ∫_{log N}^∞ 2u * exp(-t u^2 + u/2) du.
    """
    if N < 3:
        N = 3
    u0 = math.log(N)

    def integrand(u: float) -> float:
        return 2.0 * u * math.exp(-t * u * u + 0.5 * u)

    val, err = integrate.quad(integrand, u0, np.inf, limit=200)
    return float(val)


@dataclass
class QBounds:
    B: float
    t: float
    N: int
    arch: float
    prime_partial: float
    tail: float
    Q_lower: float
    Q_upper: float


def arch_term(B: float, t: float) -> float:
    integrand = lambda xi: a_star(xi) * fejer_heat_window(B, t, xi)
    val, _ = integrate.quad(integrand, -B, B, limit=500)
    return float(val)


def prime_term_partial(xi_arr: np.ndarray, w_arr: np.ndarray, B: float, t: float) -> float:
    # Phi(ξ) = max(0, 1 - |ξ|/B) * exp(-4π² t ξ²)
    abs_xi = np.abs(xi_arr)
    fejer = 1.0 - abs_xi / B
    fejer = np.where(fejer > 0.0, fejer, 0.0)
    phi = fejer * np.exp(-4.0 * (PI ** 2) * t * xi_arr * xi_arr)
    return float(np.sum(w_arr * phi))


def compute_Q_bounds(xi_arr: np.ndarray, w_arr: np.ndarray, B: float, t: float, N: int) -> QBounds:
    arch = arch_term(B, t)
    prime_partial = prime_term_partial(xi_arr, w_arr, B, t)
    tail = tail_bound(N, t)
    Q_upper = arch - prime_partial
    Q_lower = arch - (prime_partial + tail)
    return QBounds(B, t, N, arch, prime_partial, tail, Q_lower, Q_upper)


def format_bounds(qb: QBounds) -> str:
    return (
        f"B={qb.B:.3f}, t={qb.t:.5f}, N={qb.N}\n"
        f"  arch_term      = {qb.arch:.8f}\n"
        f"  prime_partial  = {qb.prime_partial:.8f}\n"
        f"  tail_bound     = {qb.tail:.8e}\n"
        f"  Q_lower        = {qb.Q_lower:.8f}\n"
        f"  Q_upper        = {qb.Q_upper:.8f}\n"
    )


def main():
    # Config
    N = 10_000_000  # 1e7 prime power cutoff
    B_values = [3.0, 4.9]

    # t values
    t_sym = 3 / 50  # 0.06
    t_critical = 3 / 20  # 0.15

    print("Generating prime powers up to N =", N)
    xi_arr, w_arr = prime_powers_data(N)
    print(f"Prime power terms: {len(xi_arr)}")

    print("\n=== Q bounds at t_sym = 0.06 (expected NEGATIVE) ===")
    qb = compute_Q_bounds(xi_arr, w_arr, B=3.0, t=t_sym, N=N)
    print(format_bounds(qb))

    print("\n=== Q bounds at t_critical = 0.15 (expected POSITIVE) ===")
    for B in B_values:
        qb = compute_Q_bounds(xi_arr, w_arr, B=B, t=t_critical, N=N)
        print(format_bounds(qb))


if __name__ == "__main__":
    main()
