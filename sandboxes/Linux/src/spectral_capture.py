"""Spectral capture: decompose psi in eigenbasis of H and measure phase dispersion under S."""

from __future__ import annotations

import numpy as np


def spectral_capture(H: np.ndarray, S: np.ndarray, psi: np.ndarray, thresh: float = 0.01):
    """Return eigenvalues, significant coefficients, and phase variance.

    Args:
        H: Hermitian matrix
        S: unitary matrix (same size)
        psi: vector to analyse
        thresh: keep modes with |a_j| >= thresh * max|a_j|

    Returns:
        dict with keys: lam (eigenvalues), a (coeffs), phi (phases), var_phi
    """

    lam, V = np.linalg.eigh(H)
    a = V.conj().T @ psi
    mask = np.abs(a) >= thresh * np.max(np.abs(a))
    lam = lam[mask]
    a = a[mask]
    Vsig = V[:, mask]

    # phases induced by S on the captured subspace
    Sv = S @ Vsig
    # project Sv onto Vsig to get approximate phases
    phases = []
    for j in range(Vsig.shape[1]):
        vj = Vsig[:, j]
        sj = Sv[:, j]
        phase = np.vdot(vj, sj)
        phase /= np.vdot(vj, vj) + 1e-30
        phases.append(np.angle(phase))
    phases = np.array(phases)

    phi_bar = np.sum(np.abs(a) ** 2 * phases) / (np.sum(np.abs(a) ** 2) + 1e-30)
    var_phi = np.sum(np.abs(a) ** 2 * (phases - phi_bar) ** 2) / (np.sum(np.abs(a) ** 2) + 1e-30)

    return {
        "lam": lam,
        "a": a,
        "phi": phases,
        "var_phi": var_phi,
    }


if __name__ == "__main__":
    # smoke test
    import numpy as np
    H = np.diag(np.linspace(0, 1, 5))
    S = np.diag(np.exp(1j * np.linspace(0, 0.5, 5)))
    psi = np.ones(5) / np.sqrt(5)
    out = spectral_capture(H, S, psi)
    print(out["var_phi"])

