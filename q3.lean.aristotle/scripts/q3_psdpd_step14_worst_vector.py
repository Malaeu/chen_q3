#!/usr/bin/env python3
"""
Step 14 PSD-pd worst-vector autopsy.

Imports Step 13 matrix builders, extracts the worst generalized eigenvector
for C^circ = N^T(A-P)N against G^circ = N^TGN, then decomposes energy into:

  A, P, P0, Pnu, R=A-P0, C=A-P

Also prints:
  - boundary residual Qv
  - largest coordinates of the lifted vector v
  - top prime-shift contributions
  - optional kappa split:
        C = (A - kappa P0) - (P - kappa P0)

Notation:
  k_spline = B-spline degree
  r_pow    = prime-power exponent p^r_pow

This is a reconnaissance script, not a proof-grade certificate.
"""

from __future__ import annotations

import argparse

import numpy as np
from scipy import linalg

from q3_psdpd_step13_pilot import (
    PilotParams,
    SplinePacket,
    boundary_null_basis,
    build_A,
    build_G,
    build_P,
    build_P0,
    build_Q,
    build_centers,
    centered_bspline,
    sym,
)


def qform(M: np.ndarray, v: np.ndarray) -> float:
    return float(np.real(v.T @ M @ v))


def normalize_by_G(v: np.ndarray, G: np.ndarray) -> np.ndarray:
    nrm2 = qform(G, v)
    if nrm2 <= 0:
        raise ValueError(f"Bad G norm: {nrm2}")
    return v / np.sqrt(nrm2)


def eta_values(packet: SplinePacket, x: np.ndarray) -> np.ndarray:
    """eta_k(x) = sqrt(s_k/c_k) * b_k(s_k*x), support [-1,1]."""
    return np.sqrt(packet.s_k / packet.c_k) * centered_bspline(
        packet.k_spline, packet.s_k * x
    )


def h_profile(
    u_grid: np.ndarray,
    centers: np.ndarray,
    v: np.ndarray,
    ell: float,
    packet: SplinePacket,
) -> np.ndarray:
    """h_v(u)=sum_j v_j ell^{-1/2} eta((u-u_j)/ell)."""
    out = np.zeros_like(u_grid, dtype=float)
    for coeff, uj in zip(v, centers):
        out += coeff * ell ** (-0.5) * eta_values(packet, (u_grid - uj) / ell)
    return out


def ascii_bar(value: float, scale: float, width: int = 42) -> str:
    if scale <= 0:
        scale = 1.0
    n = int(min(width, abs(value) / scale * width))
    sign = "+" if value >= 0 else "-"
    return sign + "#" * n


def print_top_coordinates(centers: np.ndarray, v: np.ndarray, top: int) -> None:
    idx = np.argsort(np.abs(v))[::-1][:top]
    max_abs = float(np.max(np.abs(v[idx]))) if len(idx) else 1.0

    print("\n== Top lifted coefficients v_j ==")
    print("rank        u_j              v_j                 |v_j|      bar")
    for rank, j in enumerate(idx, 1):
        print(
            f"{rank:4d}  {centers[j]: .10e}  {v[j]: .16e}  "
            f"{abs(v[j]): .8e}  {ascii_bar(v[j], max_abs)}"
        )


def print_profile_summary(
    params: PilotParams,
    packet: SplinePacket,
    centers: np.ndarray,
    v: np.ndarray,
    n_grid: int = 401,
) -> None:
    u_grid = np.linspace(-params.L, params.L, n_grid)
    hv = h_profile(u_grid, centers, v, params.ell, packet)
    idx = np.argsort(np.abs(hv))[::-1][:12]
    max_abs = float(np.max(np.abs(hv))) if len(hv) else 1.0

    print("\n== Spatial profile h_v(u), top samples ==")
    print("rank        u              h(u)               |h(u)|     bar")
    for rank, j in enumerate(idx, 1):
        print(
            f"{rank:4d}  {u_grid[j]: .10e}  {hv[j]: .16e}  "
            f"{abs(hv[j]): .8e}  {ascii_bar(hv[j], max_abs)}"
        )


def print_prime_shift_contributions(
    D: np.ndarray,
    params: PilotParams,
    packet: SplinePacket,
    shifts,
    v: np.ndarray,
    top: int,
) -> None:
    rows = []

    for sh in shifts:
        M = sh.weight * (
            packet.r_corr((D - sh.a) / params.ell)
            + packet.r_corr((D + sh.a) / params.ell)
        )
        e = qform(sym(M), v)
        rows.append((abs(e), e, sh.a, sh.weight, sh.p, sh.r_pow))

    rows.sort(reverse=True, key=lambda x: x[0])

    print("\n== Top prime-shift energy contributions to P ==")
    print("rank      energy              |energy|            a=r log p        weight          p   r_pow")
    for rank, (abs_e, e, a, w, p, r_pow) in enumerate(rows[:top], 1):
        print(
            f"{rank:4d}  {e: .16e}  {abs_e: .16e}  "
            f"{a: .10e}  {w: .10e}  {p:5d}  {r_pow:5d}"
        )


def print_kappa_sweep(
    A: np.ndarray,
    P: np.ndarray,
    P0: np.ndarray,
    N: np.ndarray,
    kappas: list[float],
) -> None:
    print("\n== Kappa split sweep ==")
    print("C = (A - kappa P0) - (P - kappa P0)")
    print("kappa        min eig(R_k)        max eig(S_k,R_k)       cert max<=1?")

    for kappa in kappas:
        Rk = sym(N.T @ (A - kappa * P0) @ N)
        Sk = sym(N.T @ (P - kappa * P0) @ N)
        eig_Rk = np.linalg.eigvalsh(Rk)
        min_R = eig_Rk[0]

        if min_R > 1e-10:
            eig_rel = linalg.eigh(Sk, Rk, eigvals_only=True)
            max_rel = eig_rel[-1]
            ok = max_rel <= 1.0
            print(f"{kappa: .6f}  {min_R: .16e}  {max_rel: .16e}  {ok}")
        else:
            print(f"{kappa: .6f}  {min_R: .16e}  {'indefinite':>20}  False")


def run_autopsy(params: PilotParams, top: int, kappas: list[float]) -> None:
    packet = SplinePacket.build(params.k_spline)

    centers = build_centers(params)
    D = centers[:, None] - centers[None, :]

    print("== Step 14 worst-vector autopsy ==")
    print(f"L={params.L}, ell={params.ell}, delta={params.delta}, k_spline={params.k_spline}")
    print(f"n_centers={len(centers)}")
    print(f"arch_tmax={params.arch_tmax}, arch_nt={params.arch_nt}, p0_na={params.p0_na}")

    G = build_G(D, params, packet)
    A = build_A(D, params, packet)
    P, shifts = build_P(D, params, packet)
    P0 = build_P0(D, params, packet)

    Pnu = sym(P - P0)
    R = sym(A - P0)
    C = sym(A - P)

    Q = build_Q(centers)
    N = boundary_null_basis(Q)

    Gc = sym(N.T @ G @ N)
    Cc = sym(N.T @ C @ N)

    evals, evecs = linalg.eigh(Cc, Gc)
    lam_min = float(evals[0])
    x = evecs[:, 0]

    v = N @ x
    v = normalize_by_G(v, G)

    boundary_resid = Q @ v

    E_G = qform(G, v)
    E_A = qform(A, v)
    E_P = qform(P, v)
    E_P0 = qform(P0, v)
    E_Pnu = qform(Pnu, v)
    E_R = qform(R, v)
    E_C = qform(C, v)

    print("\n== Generalized near-kernel ==")
    print(f"lambda_min(Cc,Gc) = {lam_min:.16e}")
    print(f"v^T G v            = {E_G:.16e}")
    print(f"||Qv||_2           = {np.linalg.norm(boundary_resid):.16e}")
    print(f"Qv                 = [{boundary_resid[0]: .6e}, {boundary_resid[1]: .6e}]")

    print("\n== Energy decomposition on worst vector, normalized v^T G v = 1 ==")
    print(f"E_A      = v^T A    v      = {E_A: .16e}")
    print(f"E_P      = v^T P    v      = {E_P: .16e}")
    print(f"E_P0     = v^T P0   v      = {E_P0: .16e}")
    print(f"E_Pnu    = v^T Pnu  v      = {E_Pnu: .16e}")
    print(f"E_R      = v^T R    v      = {E_R: .16e}   where R=A-P0")
    print(f"E_C      = v^T C    v      = {E_C: .16e}   where C=A-P")
    print(f"A-P      check             = {(E_A - E_P): .16e}")
    print(f"R-Pnu    check             = {(E_R - E_Pnu): .16e}")
    print(f"split residual             = {(E_C - (E_R - E_Pnu)): .3e}")

    print("\n== Ratios ==")
    if abs(E_A) > 1e-30:
        print(f"E_P / E_A      = {E_P / E_A: .16e}")
    if abs(E_R) > 1e-30:
        print(f"E_Pnu / E_R    = {E_Pnu / E_R: .16e}")
    if abs(E_P0) > 1e-30:
        print(f"(-E_P0)        = {-E_P0: .16e}")

    print_top_coordinates(centers, v, top)
    print_profile_summary(params, packet, centers, v)
    print_prime_shift_contributions(D, params, packet, shifts, v, top)

    if kappas:
        print_kappa_sweep(A, P, P0, N, kappas)


def parse_args() -> tuple[PilotParams, int, list[float]]:
    parser = argparse.ArgumentParser()
    parser.add_argument("--L", type=float, default=3.0)
    parser.add_argument("--ell", type=float, default=0.35)
    parser.add_argument("--delta", type=float, default=0.25)
    parser.add_argument("--k-spline", type=int, default=5)
    parser.add_argument("--arch-tmax", type=float, default=180.0)
    parser.add_argument("--arch-nt", type=int, default=24001)
    parser.add_argument("--p0-na", type=int, default=12001)
    parser.add_argument("--top", type=int, default=12)
    parser.add_argument(
        "--kappas",
        type=str,
        default="0.5,1,1.5,2,3,4,6,8,10",
        help="Comma-separated kappa values for C=(A-kP0)-(P-kP0). Empty string disables.",
    )
    args = parser.parse_args()

    params = PilotParams(
        L=args.L,
        ell=args.ell,
        delta=args.delta,
        k_spline=args.k_spline,
        arch_tmax=args.arch_tmax,
        arch_nt=args.arch_nt,
        p0_na=args.p0_na,
    )

    kappas = []
    if args.kappas.strip():
        kappas = [float(x) for x in args.kappas.split(",") if x.strip()]

    return params, args.top, kappas


if __name__ == "__main__":
    params_, top_, kappas_ = parse_args()
    run_autopsy(params_, top_, kappas_)
