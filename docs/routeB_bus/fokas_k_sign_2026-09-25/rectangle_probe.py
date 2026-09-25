#!/usr/bin/env python3
"""High-precision diagnostic for the Goal058 scalar-sign source rectangle.

This is scratch-only numerical work. It is not an interval certificate.
The source recurrence coefficients are transcribed from
PROSHKA_VERDICT_GOAL058_ADJOINT_GREEN_MIX_2026-09-25.md, section 1; the
Robin brackets and R5-R8 screen follow section 5 of
PROSHKA_VERDICT_GOAL058_FULL_SCALAR_SIGN_CHAIN_2026-09-25.md.

The finite Mellin kernel is copied algebraically from
ccm_exact_source_generator_2026-09-20/exact_generator.py::_mp_kernel.
The even-Legendre monomial expansion follows
ccm_n_extension_probe_2026-09-21/probe_n_extension.py::_legendre_poly_kernel.
No files in the canonical checkout are modified.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import mpmath as mp

OUT = Path(__file__).resolve().parent


def _G(m: int):
    return 4 * mp.pi**2 * m**2


def _ell(m: int, k: int):
    if k < 1:
        return mp.mpf(0)
    G = _G(m)
    return -G * (2*k - 1) * (2*k) / ((4*k - 3) * (4*k - 1))


def _diag(m: int, k: int):
    G = _G(m)
    return 2*k*(2*k + 1) + G * (4*k*(2*k + 1) - 1) / ((4*k - 1)*(4*k + 3))


def _u(m: int, k: int):
    G = _G(m)
    return -G * (2*k + 1)*(2*k + 2) / ((4*k + 3)*(4*k + 5))


def jacobi(m: int, t, extra: int = 0):
    """Return the symmetric source Jacobi matrix on k=0..6m-1+extra.

    The last diagonal receives the R1 perturbation u_N*t. Setting extra=1
    repeats the endpoint eigenvalues with one additional Jacobi cell.
    """
    if m < 2 or extra < 0:
        raise ValueError("m >= 2 and extra >= 0 required")
    N = 6*m - 1 + extra
    A = mp.matrix(N + 1)
    for k in range(N + 1):
        A[k, k] = _diag(m, k)
    for k in range(N):
        # Similarity weights mu_k=(4k+1)^(-1) give this negative edge.
        edge = -mp.sqrt(_u(m, k) * _ell(m, k + 1))
        A[k, k + 1] = edge
        A[k + 1, k] = edge
    A[N, N] += _u(m, N) * mp.mpf(t)
    return A


def _endpoint_eigenvalues(m: int, t, extra: int = 0):
    vals, _vecs = mp.eigsy(jacobi(m, t, extra=extra))
    return vals[0], vals[2]


def bracket(m: int, extra: int = 0):
    """Return {0:(lo,hi), 4:(lo,hi)} with lo=lambda_p(1/2), hi=lambda_p(0)."""
    low0, low2 = _endpoint_eigenvalues(m, mp.mpf("0.5"), extra=extra)
    high0, high2 = _endpoint_eigenvalues(m, mp.mpf(0), extra=extra)
    return {0: (low0, high0), 4: (low2, high2)}


def recurrence(m: int, e):
    """Return source P_k(e), P'_k(e), P''_k(e), each list indexed by k."""
    if m < 2:
        raise ValueError("m >= 2 required")
    N = 6*m - 1
    e = mp.mpf(e)
    P = [mp.mpf(1)]
    P1 = [mp.mpf(0)]
    P2 = [mp.mpf(0)]
    for k in range(N):
        ell = _ell(m, k)
        prev = P[k - 1] if k else mp.mpf(0)
        prev1 = P1[k - 1] if k else mp.mpf(0)
        prev2 = P2[k - 1] if k else mp.mpf(0)
        d, u = _diag(m, k), _u(m, k)
        P.append(((e - d)*P[k] - ell*prev) / u)
        P1.append((P[k] + (e - d)*P1[k] - ell*prev1) / u)
        P2.append((2*P1[k] + (e - d)*P2[k] - ell*prev2) / u)
    return P, P1, P2


def _mp_kernel(m: int, n: int, degree: int):
    """Finite monomial Mellin kernel from exact_generator.py::_mp_kernel."""
    L = mp.log(m)
    s = mp.mpf("0.5") - 2j*mp.pi*n/L
    return mp.mpf(m)**(-mp.mpf("0.25"))/mp.sqrt(L) * mp.fsum(
        (mp.sqrt(m)*mp.mpf(k)**(-s) - (mp.mpf(k)/m)**degree) / (s + degree)
        for k in range(1, m + 1)
    )


def _legendre_poly_kernel(m: int, n: int, k: int):
    """Mellin kernel of P_(2k), expanded in monomials as prior probe did."""
    degree = 2*k
    total = mp.mpc(0)
    for j in range(k + 1):
        power = degree - 2*j
        coeff = (mp.binomial(degree, j) * mp.binomial(2*degree - 2*j, degree)
                 * (-1)**j / mp.power(2, degree))
        total += coeff * _mp_kernel(m, n, power)
    return total


def F_matrix(m: int):
    """Return the full F matrix: rows n=-m..m, columns k=1..6m-1."""
    if m < 2:
        raise ValueError("m >= 2 required")
    N = 6*m - 1
    F = mp.matrix(2*m + 1, N)
    for row, n in enumerate(range(-m, m + 1)):
        for col, k in enumerate(range(1, N + 1)):
            F[row, col] = _legendre_poly_kernel(m, n, k)
    return F


def r6_bounds(m: int, interval):
    """Return R6 majorants R^(0), R^(1), R^(2), indexed by k."""
    lo, hi = interval
    N = 6*m - 1
    R0, R1, R2 = [mp.mpf(1)], [mp.mpf(0)], [mp.mpf(0)]
    for k in range(N):
        D = max(abs(lo - _diag(m, k)), abs(hi - _diag(m, k)))
        ell, u = abs(_ell(m, k)), abs(_u(m, k))
        prev0 = R0[k - 1] if k else mp.mpf(0)
        prev1 = R1[k - 1] if k else mp.mpf(0)
        prev2 = R2[k - 1] if k else mp.mpf(0)
        R0.append((D*R0[k] + ell*prev0) / u)
        R1.append((R0[k] + D*R1[k] + ell*prev1) / u)
        R2.append((2*R1[k] + D*R2[k] + ell*prev2) / u)
    return {0: R0, 1: R1, 2: R2}


def _norm(v):
    return mp.sqrt(mp.fsum(abs(x)**2 for x in v))


def _frob_norm(F):
    return mp.sqrt(mp.fsum(abs(F[i, j])**2 for i in range(F.rows) for j in range(F.cols)))


def analyze(m: int, dps: int = 90):
    with mp.workdps(dps):
        I = bracket(m)
        Ihigher = bracket(m, extra=1)
        F = F_matrix(m)
        fnorm = _frob_norm(F)
        centers = {i: (I[i][0] + I[i][1]) / 2 for i in (0, 4)}
        p0, p4 = recurrence(m, centers[0])[0], recurrence(m, centers[4])[0]
        coeffs = [(-1)**k * (p0[k] - p4[k]) for k in range(1, 6*m)]
        zc = [mp.fsum(F[row, col] * coeffs[col] for col in range(F.cols)) for row in range(F.rows)]
        znorm = _norm(zc)
        sens = {}
        a_sum = mp.mpf(0)
        for i in (0, 4):
            a = (I[i][1] - I[i][0]) / 2
            bounds = r6_bounds(m, I[i])
            d1 = _norm(bounds[1][1:])
            d2 = _norm(bounds[2][1:])
            V, J = fnorm*d1, fnorm*d2
            contribution = a*V
            a_sum += contribution
            sens[i] = {
                "half_width": mp.nstr(a, 48),
                "R6_l2_P1": mp.nstr(d1, 48),
                "R6_l2_P2": mp.nstr(d2, 48),
                "V_i_frobenius_bound": mp.nstr(V, 48),
                "J_i_frobenius_bound": mp.nstr(J, 48),
                "a_i_times_V_i": mp.nstr(contribution, 48),
                "a_i_V_i_over_norm_zc": mp.nstr(contribution / znorm, 48) if znorm else "undefined",
                "max_R6_P1": mp.nstr(max(bounds[1][1:]), 24),
                "max_R6_P2": mp.nstr(max(bounds[2][1:]), 24),
            }
        G = _G(m)
        coarse = G * mp.power(4, -m) / 8
        widths = {i: I[i][1] - I[i][0] for i in (0, 4)}
        widths_higher = {i: Ihigher[i][1] - Ihigher[i][0] for i in (0, 4)}
        candidate = G * ((16*m - 3) / (24*m - 3)) * mp.power(4, -2*m) / 8
        extended_diffs = {
            i: max(abs(I[i][0] - Ihigher[i][0]), abs(I[i][1] - Ihigher[i][1]))
            for i in (0, 4)
        }
        return {
            "m": m,
            "N": 6*m - 1,
            "precision_dps": dps,
            "coarse_G_4^-m_over_8": mp.nstr(coarse, 48),
            "unverified_q_ge_4m_candidate_bound": mp.nstr(candidate, 48),
            "candidate_bound_status": "unverified proposal from parent; not used as an established R2 bound",
            "intervals": {
                i: {
                    "lambda_p_half": mp.nstr(I[i][0], 48),
                    "lambda_p_zero": mp.nstr(I[i][1], 48),
                    "width": mp.nstr(widths[i], 48),
                    "width_over_coarse": mp.nstr(widths[i] / coarse, 24),
                    "width_over_unverified_candidate_bound": mp.nstr(widths[i] / candidate, 24),
                    "one_cell_higher_width": mp.nstr(widths_higher[i], 48),
                    "midpoint": mp.nstr(centers[i], 48),
                    "one_cell_higher_endpoint_max_difference": mp.nstr(extended_diffs[i], 24),
                } for i in (0, 4)
            },
            "F_shape_rows_n_minus_m_to_m_cols_k_1_to_N": [F.rows, F.cols],
            "F_frobenius_bound": mp.nstr(fnorm, 48),
            "z_center_norm": mp.nstr(znorm, 48),
            "sum_a_i_V_i": mp.nstr(a_sum, 48),
            "necessary_y_minus_screen": {
                "a0V0_plus_a4V4_ge_norm_zc": bool(a_sum >= znorm),
                "conclusion_if_true": "y_minus cannot be positive even using ||Pi zc||<=||zc||",
                "relative_sensitivity_sum": mp.nstr(a_sum / znorm, 24) if znorm else "undefined",
            },
            "source_majorant_sensitivity": sens,
            "diagnostic_scope": "high_precision numerical screen; not an interval certificate or sign proof",
        }


def _main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, default=2)
    parser.add_argument("--dps", type=int, default=90)
    args = parser.parse_args()
    result = analyze(args.m, args.dps)
    path = OUT / f"rectangle_probe_m{args.m}.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print(f"WROTE {path}")


if __name__ == "__main__":
    _main()
