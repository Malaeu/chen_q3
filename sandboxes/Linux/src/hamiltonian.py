"""Minimal builder for the Q3 Hamiltonian H = T_A - T_P.

This is a lightweight, self-contained implementation intended for the
commutator-resonance experiments. It does **not** aim to reproduce every
constant from the main proof, but keeps the structure:

  * Toeplitz-like archimedean part T_A on an xi-grid of size M over [-K, K]
  * Prime part T_P as a sum of rank-one bumps centred at xi_p = log p / 2π

Public API:
    build_hamiltonian(K, M, X_max, t_sym=1.0, kernel='gauss') -> (H, xi_grid)

Dependencies: numpy only.
"""

from __future__ import annotations

import numpy as np
from math import log, pi


def arch_symbol(xi: np.ndarray) -> np.ndarray:
    """Archimedean symbol a(ξ).

    We use a simple smooth, positive profile that decays like log |ξ| to
    mimic log π - Re ψ(1/4 + iπξ). This is sufficient for resonance testing
    (precise constants are irrelevant here).
    """

    # avoid log(0)
    eps = 1e-12
    return np.log(1.0 + 1.0 / (eps + xi**2)) + 1.0


def fejer_heat_kernel(x: np.ndarray, t: float) -> np.ndarray:
    """Gaussian/heat kernel exp(-x^2 / (4 t))."""

    return np.exp(-x * x / (4.0 * t))


def build_hamiltonian(K: float, M: int, X_max: int, t_sym: float = 1.0,
                      kernel: str = "gauss", return_prime_vectors: bool = False):
    """Assemble H = T_A - T_P on an xi-grid.

    Args:
        K: spectral window half-width (grid over [-K, K])
        M: grid size
        X_max: largest prime included in T_P
        t_sym: kernel scale for prime bumps
        kernel: currently only 'gauss' is supported

    Returns:
        H (M x M Hermitian ndarray), xi_grid (length M ndarray)
    """

    xi_grid = np.linspace(-K, K, M)

    # --- Archimedean part: diagonal with symbol values (Toeplitz surrogate) ---
    a_vals = arch_symbol(xi_grid)
    T_A = np.diag(a_vals)

    # --- Prime part: sum of rank-one kernels ---
    T_P = np.zeros((M, M), dtype=np.complex128)
    prime_vectors = []
    # simple sieve for primes up to X_max
    sieve = bytearray(b"\x01") * (X_max + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(X_max ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p : X_max + 1 : p] = b"\x00" * (((X_max - p * p) // p) + 1)
    primes = [i for i, b in enumerate(sieve) if b]

    for p in primes:
        w = 2.0 * log(p) / (p ** 0.5)
        xi_p = log(p) / (2 * pi)
        kvec = fejer_heat_kernel(xi_grid - xi_p, t_sym)
        T_P += w * np.outer(kvec, kvec.conj())
        if return_prime_vectors:
            prime_vectors.append((w, kvec))

    H = T_A - T_P
    # symmetrize numerically
    H = 0.5 * (H + H.conj().T)
    if return_prime_vectors:
        return H, xi_grid, prime_vectors
    return H, xi_grid


__all__ = ["build_hamiltonian", "arch_symbol", "fejer_heat_kernel"]
