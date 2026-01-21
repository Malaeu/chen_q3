"""Compute commutator resonance metrics for the twin sector.

Usage (example):

    from hamiltonian import build_hamiltonian
    from shift import delta_from_X, phase_shift
    from twins_state import build_twins_vector
    import numpy as np

    H, xi = build_hamiltonian(K=2.0, M=256, X_max=1_000_000, t_sym=1.0)
    delta = delta_from_X(1_000_000)
    S = phase_shift(xi, delta)
    psi = build_twins_vector(1_000_000, xi, t=1.0, twin_only=True)
    C, D2, R = commutator_metrics(H, S, psi)

"""

from __future__ import annotations

import numpy as np


def commutator_metrics(H: np.ndarray, S: np.ndarray, psi: np.ndarray,
                       return_components: bool = False,
                       diag_vectors: list | None = None):
    """Return (C, D2, R) and, optionally, components.

    If return_components is True and diag_vectors is a list of
    (weight w_p, vector u_p) such that T_P = sum_p w_p |u_p><u_p|
    and H = T_A - T_P, we also return a dict with:

      D2_A    = ||[T_A, S] psi||^2
      D2_diag = sum_p ||[w_p |u_p><u_p|, S] psi||^2
      D2_twin = D2 - D2_A - D2_diag  (cross-terms / twin correlations)

    Key identity: [T_A, S] = [H, S] + [T_P, S], so v_A = v + v_P.
    """

    # full commutator [H, S] psi
    comm = H @ S - S @ H
    v = comm @ psi
    C = np.vdot(psi, v)
    D2 = np.vdot(v, v).real
    Hpsi_norm = np.sqrt(np.vdot(H @ psi, H @ psi).real) + 1e-30
    R = np.sqrt(D2) / Hpsi_norm

    if not return_components:
        return C, D2, R

    comps: dict[str, float] = {}

    if diag_vectors is not None and len(diag_vectors) > 0:
        # Build [T_P, S] psi and the diagonal background
        v_P = np.zeros_like(psi, dtype=np.complex128)  # accumulate [T_P, S] psi
        D2_diag = 0.0

        for w, up in diag_vectors:
            # rank-one projector P_p = |u_p><u_p|
            P = np.outer(up, up.conj())
            comm_p = w * (P @ S - S @ P)  # [w_p P_p, S]
            vp = comm_p @ psi             # [w_p P_p, S] psi
            v_P += vp
            D2_diag += np.vdot(vp, vp).real

        comps["D2_diag"] = D2_diag

        # [T_A, S] psi = [H, S] psi + [T_P, S] psi = v + v_P
        v_A = v + v_P
        D2_A = np.vdot(v_A, v_A).real
        comps["D2_A"] = D2_A

        # twin/off-diagonal remainder (cross-terms)
        comps["D2_twin"] = D2 - D2_A - D2_diag

    else:
        # no decomposition: everything attributed to "A"
        comps["D2_diag"] = 0.0
        comps["D2_A"] = D2
        comps["D2_twin"] = 0.0

    return C, D2, R, comps


def sweep(K=2.0, M=256, X_list=(10_000,), t_sym=1.0, twin_t=1.0,
          delta_mode: str = "fromX", delta0: float = 0.01, delta_alpha: float = 1.0,
          build_H=None, build_psi=None, normalize_psi: bool = True,
          return_components: bool = False):
    """Sweep over X_list, returning list of dicts with metrics.

    delta_mode: "fromX" uses delta_from_X(X), "fixed" uses delta0.
    """

    if build_H is None:
        from .hamiltonian import build_hamiltonian as build_H
    from .shift import delta_from_X, phase_shift
    if build_psi is None:
        from .twins_state import build_twins_vector
        build_psi = lambda X, xi: build_twins_vector(X, xi, t=twin_t,
                                                     twin_only=True, normalize=normalize_psi)

    rows = []
    for X in X_list:
        H_full = build_H(K, M, X, t_sym=t_sym, return_prime_vectors=return_components)
        if return_components:
            H, xi, prime_vectors = H_full
            diag_vectors = prime_vectors
        else:
            H, xi = H_full
            diag_vectors = None
        if delta_mode == "fixed":
            delta = delta0
        elif delta_mode == "power":
            delta = delta0 / (X ** delta_alpha)
        else:
            delta = delta_from_X(X)
        S = phase_shift(xi, delta)
        psi = build_psi(X, xi)
        if return_components:
            C, D2, R, comps = commutator_metrics(H, S, psi, return_components=True,
                                                 diag_vectors=diag_vectors)
        else:
            C, D2, R = commutator_metrics(H, S, psi)
            comps = {}
        rows.append({"X": X, "delta": delta, "C": C, "D2": D2, "R": R, **comps})
    return rows


def loglog_fit(xs, ys):
    """Simple log-log slope fit (returns slope, intercept)."""
    xs = np.array(xs, dtype=float)
    ys = np.array(ys, dtype=float)
    mask = (xs > 0) & (ys > 0)
    xs = xs[mask]
    ys = ys[mask]
    if len(xs) < 2:
        return None, None
    lx = np.log(xs)
    ly = np.log(ys)
    A = np.vstack([lx, np.ones_like(lx)]).T
    slope, intercept = np.linalg.lstsq(A, ly, rcond=None)[0]
    return slope, intercept


if __name__ == "__main__":
    # Small smoke test
    from .hamiltonian import build_hamiltonian
    from .shift import delta_from_X, phase_shift
    from .twins_state import build_twins_vector

    H, xi = build_hamiltonian(2.0, 128, 100_000, t_sym=1.0)
    delta = delta_from_X(100_000)
    S = phase_shift(xi, delta)
    psi = build_twins_vector(100_000, xi, t=1.0, twin_only=True)
    C, D2, R = commutator_metrics(H, S, psi)
    print(f"X=1e5: |C|={abs(C):.3e}, D={np.sqrt(D2):.3e}, R={R:.3e}")
