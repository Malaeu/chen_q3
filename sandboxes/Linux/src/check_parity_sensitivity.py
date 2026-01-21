"""
Parity-sensitivity experiment for the Rayleigh quotient R = E_comm / E_lat.

Compares three ensembles for a given X:
  1. True twin primes: p, p+2 both prime.
  2. Twin semiprimes: n, n+2 both semiprime (product of two primes).
  3. Random pairs: random n with n+2 (same sample size as true twins).

Uses manuscript definitions (paper mode):
  G_ij   = sqrt(2π t) * exp(-(Δξ)^2 / (8 t))
  K_ij   = G_ij^2 = 2π t * exp(-(Δξ)^2 / (4 t))
  A_ij   = (ξ_j - ξ_i) * K_ij
  E_lat  = λ^T G λ
  E_comm = ||A λ||^2
  R      = E_comm / E_lat

Run:
  python3 -m src.check_parity_sensitivity --X 50000 --t 1.0
"""

from __future__ import annotations

import argparse
import math
import random
from dataclasses import dataclass
from typing import List, Tuple

import numpy as np


# ------------------ prime utilities ------------------
def sieve(n: int) -> List[int]:
    """Simple sieve returning primes <= n."""
    if n < 2:
        return []
    is_prime = bytearray(b"\x01") * (n + 1)
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if is_prime[p]:
            step = p
            start = p * p
            is_prime[start : n + 1 : step] = b"\x00" * ((n - start) // step + 1)
    return [i for i, f in enumerate(is_prime) if f]


def spf_sieve(n: int) -> List[int]:
    """Smallest prime factor for 0..n."""
    spf = list(range(n + 1))
    for i in range(2, int(n**0.5) + 1):
        if spf[i] == i:  # prime
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def is_semiprime(x: int, spf: List[int]) -> bool:
    """Return True if x = p*q with primes p<=q (squarefree or square allowed)."""
    if x < 4:
        return False
    p = spf[x]
    q = x // p
    return p * q == x and spf[q] == q


# ------------------ datasets ------------------
def twin_primes(X: int, primes: List[int]) -> List[int]:
    pset = set(primes)
    return [p for p in primes if p + 2 <= X and (p + 2) in pset]


def twin_semiprimes(X: int, spf: List[int]) -> List[int]:
    out = []
    for n in range(4, X - 1):
        if is_semiprime(n, spf) and is_semiprime(n + 2, spf):
            out.append(n)
    return out


def twin_random(X: int, count: int) -> List[int]:
    rng = random.Random(42)
    out = set()
    while len(out) < count and len(out) < max(1, count):
        n = rng.randint(5, X - 2)
        out.add(n)
    return sorted(out)


# ------------------ energies ------------------
def xi(arr: np.ndarray) -> np.ndarray:
    return np.log(arr) / (2 * math.pi)


def compute_R(n_array: np.ndarray, t: float = 1.0) -> Tuple[float, float, float]:
    """Given 1D array of n values, compute (R, E_comm, E_lat)."""
    if n_array.size == 0:
        return float("nan"), float("nan"), float("nan")
    lam = np.log(n_array) ** 2
    x = xi(n_array)
    dx = x[:, None] - x[None, :]
    G = math.sqrt(2 * math.pi * t) * np.exp(-(dx**2) / (8 * t))
    K = (2 * math.pi * t) * np.exp(-(dx**2) / (4 * t))
    A = dx * K
    E_lat = lam @ (G @ lam)
    v = A @ lam
    E_comm = float(np.dot(v, v))
    R = E_comm / E_lat if E_lat != 0 else float("inf")
    return R, E_comm, E_lat


# ------------------ main ------------------
@dataclass
class Result:
    name: str
    count: int
    R: float
    E_comm: float
    E_lat: float


def run(X: int, t: float) -> List[Result]:
    primes = sieve(X)
    spf = spf_sieve(X + 2)

    twins = twin_primes(X, primes)
    semis = twin_semiprimes(X, spf)
    n_twins = len(twins)

    # Normalize sample sizes: subsample semiprimes to twin count, random match twin count
    if len(semis) > n_twins:
        rng = random.Random(42)
        semis_sub = sorted(rng.sample(semis, n_twins))
    else:
        semis_sub = semis
    randoms = twin_random(X, n_twins)

    datasets = [
        ("twins (true)", np.array(twins, dtype=float)),
        ("semiprime (sub)", np.array(semis_sub, dtype=float)),
        ("random (ref)", np.array(randoms, dtype=float)),
    ]
    out: List[Result] = []
    for name, arr in datasets:
        R, Ec, El = compute_R(arr, t=t)
        out.append(Result(name, len(arr), R, Ec, El))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Parity-sensitivity test for R(Φ).")
    parser.add_argument("--X", type=int, default=50000, help="cutoff for n")
    parser.add_argument("--t", type=float, default=1.0, help="Gaussian scale t")
    args = parser.parse_args()

    results = run(args.X, args.t)
    print(f"X={args.X}, t={args.t}")
    print("type\tcount\tR\tE_comm\tE_lat")
    for r in results:
        print(f"{r.name}\t{r.count}\t{r.R:.3e}\t{r.E_comm:.3e}\t{r.E_lat:.3e}")


if __name__ == "__main__":
    main()
