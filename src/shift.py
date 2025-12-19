"""Shift operators S_delta for commutator resonance experiments."""

from __future__ import annotations

import numpy as np
from math import pi


def delta_from_X(X: float) -> float:
    """Heuristic twin-gap shift: delta ≈ 2 / (2π log X).

    For p ~ X, log(p+2)-log(p) ≈ 2/p; dividing by 2π converts to xi-units.
    """

    return 2.0 / (2.0 * pi * np.log(max(X, 3.0)))


def phase_shift(xi_grid: np.ndarray, delta: float) -> np.ndarray:
    """Diagonal unitary phase shift S_delta on the xi grid.

    (S_delta f)(xi_k) = e^{i delta xi_k} f(xi_k).
    Returns the full matrix (diagonal) for convenience.
    """

    phases = np.exp(1j * delta * xi_grid)
    return np.diag(phases)


def apply_phase_shift(vec: np.ndarray, xi_grid: np.ndarray, delta: float) -> np.ndarray:
    """Apply S_delta to a vector sampled on xi_grid."""

    return np.exp(1j * delta * xi_grid) * vec


__all__ = ["delta_from_X", "phase_shift", "apply_phase_shift"]
