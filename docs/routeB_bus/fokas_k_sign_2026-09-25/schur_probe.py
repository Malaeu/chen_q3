#!/usr/bin/env python3
"""High-precision finite-cell Schur/complement diagnostic; never a proof."""
from __future__ import annotations

import argparse
import json
import time
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import rectangle_probe as rp
import full_center_probe as fc

PACKET = Path(__file__).resolve().parent


def norm(v):
    return mp.sqrt(max(mp.mpf(0), mp.re((v.H * v)[0])))


def complement_basis(q):
    """Stable complex Householder U with U*U=I and U*q=0."""
    n = q.rows
    q = q / norm(q)
    q0 = q[0, 0]
    phase = q0 / abs(q0) if q0 else mp.mpc(1)
    target = -phase
    v = mp.matrix(q)
    v[0, 0] -= target
    v2 = mp.re((v.H * v)[0])
    if not v2:
        raise ArithmeticError("Householder vector vanished unexpectedly")
    H = mp.eye(n) - (mp.mpf(2) / v2) * v * v.H
    U = mp.matrix([[H[i, j] for j in range(1, n)] for i in range(n)])
    return U


def trace_projection(Pi, K):
    PKP = Pi * K * Pi
    return mp.fsum(PKP[i, i] for i in range(PKP.rows))


def plane_companion(Pi, p):
    """Unit vector in range(Pi), orthogonal to the projected source p."""
    u = p / norm(p)
    for j in range(Pi.cols):
        candidate = mp.matrix([Pi[i, j] for i in range(Pi.rows)])
        candidate -= u * (u.H * candidate)[0]
        candidate_norm = norm(candidate)
        if candidate_norm > mp.mpf("1e-30"):
            return candidate / candidate_norm
    raise ArithmeticError("could not construct rank-two plane companion")


def complex_pair(z, digits=40):
    return [mp.nstr(mp.re(z), digits), mp.nstr(mp.im(z), digits)]


def real_matrix(A, digits=40):
    return [[mp.nstr(mp.re(A[i, j]), digits) for j in range(A.cols)]
            for i in range(A.rows)]


def complex_matrix(A, digits=40):
    return [[complex_pair(A[i, j], digits) for j in range(A.cols)]
            for i in range(A.rows)]


def vector_pairs(v, digits=40):
    return [complex_pair(v[i, 0], digits) for i in range(v.rows)]


def run(m, dps):
    mp.mp.dps = dps
    # Kernel terms repeat heavily across the Mellin matrix at fixed precision.
    rp._mp_kernel = lru_cache(maxsize=None)(rp._mp_kernel)
    started = time.time()

    intervals = rp.bracket(m)
    E0 = sum(intervals[0]) / 2
    E4 = sum(intervals[4]) / 2
    P0 = rp.recurrence(m, E0)[0]
    P4 = rp.recurrence(m, E4)[0]
    F = rp.F_matrix(m)
    coeff = mp.matrix([(-1)**k * (P0[k] - P4[k]) for k in range(1, 6*m)])
    z = F * coeff
    X = norm(z)
    q = z / X

    K = fc.matrix_K(m)
    Pi, gaussian_parity_error, gaussian_cutoff = fc.gaussian_plane(m)
    p = Pi * z
    Y = norm(p)
    theta = mp.re(trace_projection(Pi, K))
    a_complex = (q.H * K * q)[0]
    a = mp.re(a_complex)
    competitor = theta - mp.re((p.H * K * p)[0]) / (Y**2)
    tau = competitor - a
    v = plane_companion(Pi, p)

    # Full q-perpendicular compression for ground diagnostics.
    A = K - a * mp.eye(K.rows)
    U = complement_basis(q)
    B = U.H * A * U
    eta_B = U.H * (A * q)
    residual = A * q
    rnorm, etanorm = norm(residual), norm(eta_B)
    B_eigs, B_evecs = mp.eighe(B)
    dmin, dmax = B_eigs[0, 0], B_eigs[B_eigs.rows - 1, 0]
    B_lowest_coordinates = mp.matrix([B_evecs[i, 0] for i in range(B_evecs.rows)])
    B_lowest_witness = U * B_lowest_coordinates
    B_witness_energy = (B_lowest_witness.H * A * B_lowest_witness)[0]
    B_witness_norm = norm(B_lowest_witness)
    B_witness_q_overlap = abs((q.H * B_lowest_witness)[0])
    B_witness_reflected = mp.matrix([B_lowest_witness[K.rows - 1 - i, 0]
                                     for i in range(K.rows)])
    B_witness_even = (B_lowest_witness + B_witness_reflected) / 2
    B_witness_odd = (B_lowest_witness - B_witness_reflected) / 2
    B_witness_even_mass = norm(B_witness_even) ** 2
    B_witness_odd_mass = norm(B_witness_odd) ** 2
    B_hermitian_error = mp.norm(B - B.H)
    U_orthogonality_error = mp.norm(U.H * U - mp.eye(U.cols))
    U_q_error = norm(U.H * q)
    q_residual_error = abs((q.H * residual)[0])

    residual_energy_B = None
    preconditioned_residual_B = None
    coarse_ratio_B = None
    B_invertible = min(abs(B_eigs[i, 0]) for i in range(B_eigs.rows)) > 0
    if B_invertible:
        B_inv_eta = mp.lu_solve(B, eta_B)
        residual_energy_B = mp.re((eta_B.H * B_inv_eta)[0])
        preconditioned_residual_B = norm(B_inv_eta)
    if dmin > 0:
        coarse_ratio_B = rnorm / dmin

    # Source-specific dual Schur block: q and its rank-two-plane companion v
    # are orthonormal; W spans X={q,v}^perp. This is the D,eta used with tau.
    v_coordinates = U.H * v
    W_coordinates = complement_basis(v_coordinates)
    W = U * W_coordinates
    D_X = W.H * A * W
    eta_X = W.H * (A * v)
    D_X_eigs = mp.eighe(D_X, eigvals_only=True)
    dX_min, dX_max = D_X_eigs[0, 0], D_X_eigs[D_X_eigs.rows - 1, 0]
    D_X_hermitian_error = mp.norm(D_X - D_X.H)
    schur_correction_X = None
    schur_s_X = None
    rho_X = None
    preconditioned_eta_X = None
    if dX_min > 0:
        D_X_inv_eta = mp.lu_solve(D_X, eta_X)
        schur_correction_X = mp.re((eta_X.H * D_X_inv_eta)[0])
        schur_s_X = tau - schur_correction_X
        rho_X = schur_correction_X / tau if tau else mp.nan
        preconditioned_eta_X = norm(D_X_inv_eta)

    # Lowest eigenvector of the full literal K, distinct from the compressed gap.
    K_eigs, K_vecs = mp.eigsy(K)
    lambda0 = K_eigs[0, 0]
    lambda1 = K_eigs[1, 0]
    K_eigenvalues = [K_eigs[i, 0] for i in range(K_eigs.rows)]
    K_eigenvalues_below_a = [x for x in K_eigenvalues if x < a]
    lowest = mp.matrix([K_vecs[i, 0] for i in range(K.rows)])
    overlap = abs((q.H * lowest)[0])
    overlap_sq = min(mp.mpf(1), max(mp.mpf(0), overlap**2))
    sin_angle = mp.sqrt(max(mp.mpf(0), 1 - overlap_sq))
    angle_bound = (preconditioned_residual_B / mp.sqrt(1 + preconditioned_residual_B**2)
                   if preconditioned_residual_B is not None else None)

    modes = list(range(-m, m + 1))
    z_by_mode = {str(n): complex_pair(z[i, 0]) for i, n in enumerate(modes)}
    # Preserve the complete compressed block and coupling vector for auditability.
    fmt = lambda x: mp.nstr(x, 40)
    b_eigvals_json = [fmt(B_eigs[i, 0]) for i in range(B_eigs.rows)]
    dx_eigvals_json = [fmt(D_X_eigs[i, 0]) for i in range(D_X_eigs.rows)]
    result = {
        "status": "FINITE_CELL_CENTRAL_TRIAL_DIAGNOSTIC_ONLY_NOT_A_PROOF",
        "m": m,
        "dps": dps,
        "input_scope": "rectangle-midpoint source z and central Gaussian plane; not the literal exact-energy selected Ferrers trial",
        "source": {
            "central_energy_E0": fmt(E0),
            "central_energy_E4": fmt(E4),
            "source_norm_X": fmt(X),
            "projected_norm_Y": fmt(Y),
            "z_by_mode_real_imag": z_by_mode,
            "gaussian_plane_cutoff": gaussian_cutoff,
            "gaussian_evenness_error": fmt(gaussian_parity_error),
            "projection_idempotence_error": fmt(mp.norm(Pi*Pi-Pi)),
        },
        "trial_and_scalar": {
            "a_qKq": fmt(a),
            "a_imaginary_residual": fmt(mp.im(a_complex)),
            "companion_rayleigh": fmt(competitor),
            "central_tau": fmt(tau),
            "theta_trace_PiKPi": fmt(theta),
            "qstar_v_orthogonality_residual": fmt(abs((q.H * v)[0])),
            "v_norm_minus_1": fmt(abs(norm(v)-1)),
            "Pi_v_minus_v_norm": fmt(norm(Pi*v-v)),
            "vKv_minus_companion_rayleigh_residual": fmt(abs((v.H*K*v)[0]-competitor)),
        },
        "complement": {
            "definition": "B=U*(K-aI)U is the full q-perpendicular compression; r=(K-aI)q. Separately, source D_X=W*(K-aI)W on X={q,v}^perp and eta_X=W*(K-aI)v, so s=tau-eta_X*D_X^-1 eta_X.",
            "basis": "complex Householder complements",
            "B_eigenvalues_ascending": b_eigvals_json,
            "d_min": fmt(dmin),
            "d_max": fmt(dmax),
            "B_matrix_real_imag": complex_matrix(B),
            "eta_qperp_coordinates_real_imag": vector_pairs(eta_B),
            "residual_coordinates_mode_real_imag": vector_pairs(residual),
            "minimum_eigenvector_qperp_witness_by_mode_real_imag": vector_pairs(B_lowest_witness),
            "minimum_witness_norm": fmt(B_witness_norm),
            "minimum_witness_q_overlap": fmt(B_witness_q_overlap),
            "minimum_witness_quadratic_form_y_star_K_minus_aI_y": complex_pair(B_witness_energy),
            "minimum_witness_energy_minus_d_min": fmt(abs(B_witness_energy-dmin)),
            "minimum_witness_even_reflection_mass": fmt(B_witness_even_mass),
            "minimum_witness_odd_reflection_mass": fmt(B_witness_odd_mass),
            "negative_eigenvalue_count": sum(1 for i in range(B_eigs.rows) if B_eigs[i, 0] < 0),
            "residual_norm": fmt(rnorm),
            "eta_norm": fmt(etanorm),
            "residual_norm_over_d_if_B_positive": fmt(coarse_ratio_B) if coarse_ratio_B is not None else None,
            "residual_energy_etaBstar_Binv_etaB_algebraic_if_B_invertible": fmt(residual_energy_B) if residual_energy_B is not None else None,
            "preconditioned_residual_R_norm_Binv_etaB_algebraic_if_B_invertible": fmt(preconditioned_residual_B) if preconditioned_residual_B is not None else None,
            "sin_angle_bound_R_over_sqrt1plusR2_only_if_B_positive": fmt(angle_bound) if angle_bound is not None else None,
            "B_hermitian_residual": fmt(B_hermitian_error),
            "U_orthonormality_residual": fmt(U_orthogonality_error),
            "Ustar_q_residual": fmt(U_q_error),
            "qstar_residual_residual": fmt(q_residual_error),
            "source_dual_schur_block": {
                "X_definition": "X={q,v}^perp; v is unit companion in the Q5 plane orthogonal to Pi*z",
                "D_X_eigenvalues_ascending": dx_eigvals_json,
                "d_X_min": fmt(dX_min),
                "d_X_max": fmt(dX_max),
                "D_X_matrix_real_imag": complex_matrix(D_X),
                "eta_X_coordinates_real_imag": vector_pairs(eta_X),
                "eta_X_norm": fmt(norm(eta_X)),
                "eta_X_D_Xinv_eta_X_if_D_X_positive": fmt(schur_correction_X) if schur_correction_X is not None else None,
                "s_tau_minus_eta_X_D_Xinv_eta_X_if_D_X_positive": fmt(schur_s_X) if schur_s_X is not None else None,
                "rho_eta_X_D_Xinv_eta_X_over_tau_if_D_X_positive": fmt(rho_X) if rho_X is not None else None,
                "norm_D_Xinv_eta_X_if_D_X_positive": fmt(preconditioned_eta_X) if preconditioned_eta_X is not None else None,
                "D_X_hermitian_residual": fmt(D_X_hermitian_error),
            },
        },
        "actual_lowest_full_K_eigenpair": {
            "lambda0": fmt(lambda0),
            "lambda1": fmt(lambda1),
            "gap_lambda1_minus_lambda0": fmt(lambda1-lambda0),
            "number_of_full_K_eigenvalues_below_a": len(K_eigenvalues_below_a),
            "full_K_eigenvalues_below_a": [fmt(x) for x in K_eigenvalues_below_a],
            "absolute_overlap_q_with_lowest_eigenvector": fmt(overlap),
            "overlap_squared": fmt(overlap_sq),
            "sin_angle_q_to_lowest_eigenvector": fmt(sin_angle),
        },
        "timing_seconds": time.time() - started,
    }
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, choices=(4, 8, 13), required=True)
    ap.add_argument("--dps", type=int, default=100)
    args = ap.parse_args()
    result = run(args.m, args.dps)
    output = PACKET / f"schur_probe_m{args.m}_dps{args.dps}.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print(f"WROTE {output}")


if __name__ == "__main__":
    main()
