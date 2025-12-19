"""Twin-sector state construction for commutator resonance experiments."""

from __future__ import annotations

import numpy as np
from math import log, pi

from .hamiltonian import fejer_heat_kernel


def chi4(n: int) -> int:
    if n % 2 == 0:
        return 0
    return 1 if n % 4 == 1 else -1


def sieve_primes(limit: int):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(limit ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (((limit - p * p) // p) + 1)
    return [i for i, b in enumerate(sieve) if b]


def build_twins_vector(X_max: int, xi_grid: np.ndarray, t: float = 1.0,
                       kernel: str = "gauss", use_chi4: bool = False,
                       twin_only: bool = True, normalize: bool = True) -> np.ndarray:
    """Construct twin-sector vector on xi_grid.

    Args:
        X_max: upper bound for primes considered
        xi_grid: frequency grid (same as H)
        t: kernel width
        kernel: currently only 'gauss' (heat) supported
        use_chi4: if True, weight by chi4(p)chi4(p+2)
        twin_only: if True, include only pairs with p,p+2 prime; otherwise include all primes with chi4 weights
    Returns:
        psi (complex ndarray, normalized to L2=1)
    """

    primes = sieve_primes(X_max + 2)
    primes_set = set(primes)
    weights = []
    nodes = []
    for p in primes:
        is_twin = (p + 2) in primes_set
        if twin_only and not is_twin:
            continue
        w = log(p) * log(p + 2) if is_twin else log(p) * log(p)
        if use_chi4:
            w *= chi4(p) * chi4(p + 2)
        weights.append(w)
        nodes.append(log(p) / (2 * pi))

    weights = np.array(weights, dtype=np.float64)
    nodes = np.array(nodes, dtype=np.float64)
    if len(weights) == 0:
        return np.zeros_like(xi_grid, dtype=np.complex128)

    psi = np.zeros_like(xi_grid, dtype=np.complex128)
    for w, xi_p in zip(weights, nodes):
        kvec = fejer_heat_kernel(xi_grid - xi_p, t)
        psi += w * kvec

    if normalize:
        norm = np.sqrt(np.vdot(psi, psi).real)
        if norm > 0:
            psi /= norm
    return psi


__all__ = ["build_twins_vector", "chi4", "sieve_primes"]
