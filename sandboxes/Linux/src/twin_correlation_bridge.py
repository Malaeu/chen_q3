"""Compute classical twin correlations alongside commutator metrics."""

from __future__ import annotations

import numpy as np
from math import log

from .twins_state import sieve_primes
from .commutator_resonance import commutator_metrics


def twin_correlation(X: int) -> int:
    """Unsmooth sum T(X)=sum_{n<=X} Λ(n)Λ(n+2) using only primes (simplified)."""

    primes = sieve_primes(X + 2)
    pset = set(primes)
    s = 0
    for p in primes:
        if p + 2 in pset:
            s += int(log(p) * log(p + 2))
    return s


def twin_correlation_smoothed(X: int, sigma: float = 0.05) -> float:
    """Smoothed sum with Gaussian weight w(n/X) = exp(- ((n/X)-1)^2 / (2 sigma^2))."""

    primes = sieve_primes(X + 2)
    pset = set(primes)
    s = 0.0
    for p in primes:
        if p + 2 in pset:
            w = np.exp(-((p / X - 1.0) ** 2) / (2 * sigma * sigma))
            s += log(p) * log(p + 2) * w
    return s


def bridge_row(H, S, psi, X: int, sigma: float = 0.05):
    C, D2, R = commutator_metrics(H, S, psi)
    T = twin_correlation(X)
    Tsm = twin_correlation_smoothed(X, sigma=sigma)
    return {
        "X": X,
        "C": C,
        "D2": D2,
        "R": R,
        "T": T,
        "T_smooth": Tsm,
    }


__all__ = ["twin_correlation", "twin_correlation_smoothed", "bridge_row"]

