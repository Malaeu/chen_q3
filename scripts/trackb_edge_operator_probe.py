#!/usr/bin/env python3
"""
Track B / E5' edge-operator probes.

This is reconnaissance code, not a proof certificate.  It reuses the Step13
B-spline packet pilot to make the current B2 obstruction checks reproducible:

  edge      projected edge-defect proxy on ker(Q)
  lowband   mass captured by the Selberg-positive ultra-low band
  gaussian  finite-packet failure of the naive PSD Gaussian majorant
  finiteop  direct projected finite-operator certificate diagnostics
  finitesweep compact finiteop spectrum sweep over packet scales
  finiteschedule stability-filtered best packet-scale schedule
  spacing   D2 log-spacing barrier for generic Hilbert/large-sieve bounds
  clvrecv   Selberg-CLV smoothed receiver operator diagnostics
  clvprimary
            receiver-primary CLV schedule and B3 fit diagnostics
  clvblend receiver affine-tradeoff no-free-lunch diagnostics
  clvbreakdown
            endpoint/bulk anatomy of the Selberg receiver correction
  clvstructure
            operator-level rank/cancellation diagnostics for that correction
  clvquad  partial-summation / Chebyshev-psi variation diagnostics for the
            smooth Selberg correction quadrature route
  clvfourier
            sampled Fourier-sign diagnostics for E_delta(a)*F_v(a)
  clvledger
            finite psi-staircase ledger diagnostics for the smooth correction
  clvmesh  mesh-stability audit for the finite psi-staircase ledger
  clvsigncert
            smooth/jump split prototype for a future V_J sign certificate
            with analytic B-spline derivatives for the packet profile
  liftsearch finite operator-majorant search for positive-definite lifts
             (two-point or signed/multi-packet autocorrelation dictionaries)

All coordinates below are raw-log coordinates: a = r * log(p).
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from pathlib import Path
from typing import Any

import numpy as np
from scipy import special
from scipy import linalg
from scipy.optimize import linprog


REPO_ROOT = Path(__file__).resolve().parents[1]
STEP13_PATH = REPO_ROOT / "q3.lean.aristotle" / "scripts" / "q3_psdpd_step13_pilot.py"


def load_step13() -> Any:
    spec = importlib.util.spec_from_file_location("q3_psdpd_step13_pilot", STEP13_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load Step13 pilot from {STEP13_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def finite_float(x: float) -> float:
    return float(x)


def finite_float_or_none(x: float) -> float | None:
    value = float(x)
    return value if math.isfinite(value) else None


def build_packet_context(
    pilot: Any,
    *,
    K: float,
    ell: float,
    grid_delta: float,
    k_spline: int,
    p0_na: int,
) -> dict[str, Any]:
    params = pilot.PilotParams(
        L=2.0 * K,
        ell=ell,
        delta=grid_delta,
        k_spline=k_spline,
        p0_na=p0_na,
    )
    packet = pilot.SplinePacket.build(k_spline)
    u = pilot.build_centers(params)
    D = u[:, None] - u[None, :]
    G = pilot.build_G(D, params, packet)
    Q = pilot.build_Q(u)
    N = pilot.boundary_null_basis(Q)
    if N.shape[1] == 0:
        raise RuntimeError("boundary-null subspace is empty; decrease grid delta")
    Gc = pilot.sym(N.T @ G @ N)
    return {
        "params": params,
        "packet": packet,
        "u": u,
        "D": D,
        "G": G,
        "Q": Q,
        "N": N,
        "Gc": Gc,
    }


def shifted_packet_matrix(pilot: Any, packet: Any, D: np.ndarray, ell: float, a: float) -> np.ndarray:
    return (
        packet.r_corr((D - a) / ell)
        + packet.r_corr((D + a) / ell)
    )


def projected_generalized_eigs(pilot: Any, M: np.ndarray, N: np.ndarray, Gc: np.ndarray) -> np.ndarray:
    Mc = pilot.sym(N.T @ M @ N)
    return linalg.eigh(Mc, Gc, eigvals_only=True)


def project_matrix(pilot: Any, M: np.ndarray, N: np.ndarray) -> np.ndarray:
    return pilot.sym(N.T @ M @ N)


def generalized_to_standard(pilot: Any, Mc: np.ndarray, Gc: np.ndarray) -> np.ndarray:
    chol = linalg.cholesky(Gc, lower=True)
    left = linalg.solve_triangular(chol, Mc, lower=True, check_finite=False)
    standard = linalg.solve_triangular(chol, left.T, lower=True, check_finite=False).T
    return pilot.sym(standard)


def build_P0_edge(pilot: Any, packet: Any, D: np.ndarray, ell: float, lo: float, hi: float, p0_na: int) -> np.ndarray:
    a_grid = np.linspace(lo, hi, p0_na)
    wa = pilot.trap_weights_uniform(a_grid)
    P0 = np.zeros_like(D, dtype=float)
    for a, w in zip(a_grid, wa):
        P0 += w * math.exp(0.5 * float(a)) * shifted_packet_matrix(pilot, packet, D, ell, float(a))
    return pilot.sym(P0)


def build_prime_matrix_for_weight(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    shifts: list[Any],
    weight_fn: Any,
) -> np.ndarray:
    P = np.zeros_like(D, dtype=float)
    for sh in shifts:
        P += sh.weight * float(weight_fn(sh.a)) * shifted_packet_matrix(pilot, packet, D, ell, sh.a)
    return pilot.sym(P)


def build_continuum_matrix_for_weight(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    *,
    max_a: float,
    p0_na: int,
    weight_fn: Any,
) -> np.ndarray:
    a_grid = np.linspace(0.0, max_a, p0_na)
    wa = pilot.trap_weights_uniform(a_grid)
    P0 = np.zeros_like(D, dtype=float)
    for a, w in zip(a_grid, wa):
        coeff = math.exp(0.5 * float(a)) * float(weight_fn(float(a)))
        P0 += w * coeff * shifted_packet_matrix(pilot, packet, D, ell, float(a))
    return pilot.sym(P0)


def effective_shift_cutoff(D: np.ndarray, ell: float, *, packet_support_radius: float = 2.0) -> float:
    """Largest positive shift that can interact with the compact packet support."""
    return float(np.max(np.abs(D)) + packet_support_radius * ell + 1e-12)


def run_edge(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        lo, hi = 2.0 * K, 4.0 * K
        ctx = build_packet_context(
            pilot,
            K=K,
            ell=args.ell,
            grid_delta=args.grid_delta,
            k_spline=args.k_spline,
            p0_na=args.p0_na,
        )
        params = ctx["params"]
        packet = ctx["packet"]
        D = ctx["D"]
        N = ctx["N"]
        Gc = ctx["Gc"]

        shifts = pilot.prime_power_shifts(params.L)
        edge_shifts = [sh for sh in shifts if lo <= sh.a <= hi]
        P_edge = np.zeros_like(D, dtype=float)
        for sh in edge_shifts:
            P_edge += sh.weight * shifted_packet_matrix(pilot, packet, D, params.ell, sh.a)

        P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, args.p0_na)
        Pnu_edge = pilot.sym(P_edge - P0_edge)
        eigs = projected_generalized_eigs(pilot, Pnu_edge, N, Gc)
        eig_G = np.linalg.eigvalsh(Gc)

        rows.append(
            {
                "mode": "edge",
                "K": finite_float(K),
                "raw_edge": [finite_float(lo), finite_float(hi)],
                "ell": finite_float(params.ell),
                "grid_delta": finite_float(params.delta),
                "k_spline": int(params.k_spline),
                "n_centers": int(len(ctx["u"])),
                "kerQ_dim": int(N.shape[1]),
                "q_resid_fro": finite_float(np.linalg.norm(ctx["Q"] @ N, ord="fro")),
                "prime_power_shifts_total": int(len(shifts)),
                "edge_prime_power_shifts": int(len(edge_shifts)),
                "edge_weight_sum": finite_float(sum(sh.weight for sh in edge_shifts)),
                "P0_edge_mass_model_integral": finite_float(2.0 * (math.exp(0.5 * hi) - math.exp(0.5 * lo))),
                "eig_Gc_min": finite_float(eig_G[0]),
                "eig_Gc_max": finite_float(eig_G[-1]),
                "eig_Pnu_edge_G_min": finite_float(eigs[0]),
                "eig_Pnu_edge_G_max": finite_float(eigs[-1]),
                "opnorm_G_Pnu_edge": finite_float(max(abs(eigs[0]), abs(eigs[-1]))),
                "fro_Pnu_edge": finite_float(np.linalg.norm(Pnu_edge, ord="fro")),
                "D2": "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi)",
            }
        )
    return rows


def rayleigh_shift_breakdown(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    N: np.ndarray,
    Gc: np.ndarray,
    ell: float,
    shifts: list[Any],
    y: np.ndarray,
    *,
    top: int,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    by_power: dict[int, dict[str, Any]] = {}
    prime_rayleigh = 0.0
    total_abs = 0.0

    for sh in shifts:
        M = sh.weight * shifted_packet_matrix(pilot, packet, D, ell, sh.a)
        A = generalized_to_standard(pilot, project_matrix(pilot, M, N), Gc)
        contribution = float(y @ A @ y)
        prime_rayleigh += contribution
        total_abs += abs(contribution)

        power_row = by_power.setdefault(
            int(sh.r_pow),
            {"count": 0, "sum": 0.0, "abs_sum": 0.0},
        )
        power_row["count"] += 1
        power_row["sum"] += contribution
        power_row["abs_sum"] += abs(contribution)

        rows.append(
            {
                "a": finite_float(sh.a),
                "xi": finite_float(sh.a / (2.0 * math.pi)),
                "p": int(sh.p),
                "r_pow": int(sh.r_pow),
                "weight": finite_float(sh.weight),
                "contribution": finite_float(contribution),
            }
        )

    rows.sort(key=lambda row: -abs(float(row["contribution"])))
    top_rows = rows[:top]
    top_abs = sum(abs(float(row["contribution"])) for row in top_rows)
    for row in top_rows:
        row["abs_fraction"] = 0.0 if total_abs == 0.0 else abs(float(row["contribution"])) / total_abs

    by_power_rows = [
        {
            "r_pow": int(r_pow),
            "count": int(data["count"]),
            "sum": finite_float(float(data["sum"])),
            "abs_sum": finite_float(float(data["abs_sum"])),
            "abs_fraction": 0.0
            if total_abs == 0.0
            else finite_float(float(data["abs_sum"]) / total_abs),
        }
        for r_pow, data in sorted(by_power.items())
    ]

    return {
        "prime_rayleigh": finite_float(prime_rayleigh),
        "prime_abs_contribution_sum": finite_float(total_abs),
        "top_abs_contribution_sum": finite_float(top_abs),
        "top_abs_fraction": 0.0 if total_abs == 0.0 else finite_float(top_abs / total_abs),
        "by_r_pow": by_power_rows,
        "top_shifts_by_abs_contribution": top_rows,
    }


def edge_region(a: float, *, lo: float, hi: float, halo: float) -> str:
    if a < lo - halo:
        return "below_far"
    if a < lo:
        return "left_outside_halo"
    if a <= lo + halo:
        return "left_inside_halo"
    if a < hi - halo:
        return "interior_bulk"
    if a <= hi:
        return "right_inside_halo"
    if a <= hi + halo:
        return "right_outside_halo"
    return "above_far"


def add_bucket(
    buckets: dict[str, dict[str, Any]],
    key: str,
    contribution: float,
    *,
    count_weight: float = 1.0,
) -> None:
    bucket = buckets.setdefault(key, {"count": 0.0, "sum": 0.0, "abs_sum": 0.0})
    bucket["count"] += count_weight
    bucket["sum"] += contribution
    bucket["abs_sum"] += abs(contribution)


def bucket_rows(buckets: dict[str, dict[str, Any]], total_abs: float) -> list[dict[str, Any]]:
    return [
        {
            "label": key,
            "count": finite_float(float(data["count"])),
            "sum": finite_float(float(data["sum"])),
            "abs_sum": finite_float(float(data["abs_sum"])),
            "abs_fraction": 0.0
            if total_abs == 0.0
            else finite_float(float(data["abs_sum"]) / total_abs),
        }
        for key, data in sorted(buckets.items())
    ]


def rayleigh_weighted_shift_breakdown(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    N: np.ndarray,
    Gc: np.ndarray,
    ell: float,
    shifts: list[Any],
    y: np.ndarray,
    *,
    weight_fn: Any,
    lo: float,
    hi: float,
    halo: float,
    top: int,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    by_region: dict[str, dict[str, Any]] = {}
    by_power: dict[str, dict[str, Any]] = {}
    rayleigh = 0.0
    total_abs = 0.0

    for sh in shifts:
        scalar = float(weight_fn(float(sh.a)))
        if scalar == 0.0:
            continue
        M = sh.weight * scalar * shifted_packet_matrix(pilot, packet, D, ell, sh.a)
        A = generalized_to_standard(pilot, project_matrix(pilot, M, N), Gc)
        contribution = float(y @ A @ y)
        rayleigh += contribution
        total_abs += abs(contribution)
        region = edge_region(float(sh.a), lo=lo, hi=hi, halo=halo)
        add_bucket(by_region, region, contribution)
        add_bucket(by_power, f"r={int(sh.r_pow)}", contribution)
        rows.append(
            {
                "a": finite_float(float(sh.a)),
                "xi": finite_float(float(sh.a) / (2.0 * math.pi)),
                "p": int(sh.p),
                "r_pow": int(sh.r_pow),
                "weight": finite_float(float(sh.weight)),
                "receiver_minus_edge_weight": finite_float(scalar),
                "region": region,
                "contribution": finite_float(contribution),
            }
        )

    rows.sort(key=lambda row: -abs(float(row["contribution"])))
    top_rows = rows[:top]
    top_abs = sum(abs(float(row["contribution"])) for row in top_rows)
    for row in top_rows:
        row["abs_fraction"] = 0.0 if total_abs == 0.0 else abs(float(row["contribution"])) / total_abs

    return {
        "prime_rayleigh": finite_float(rayleigh),
        "prime_abs_contribution_sum": finite_float(total_abs),
        "prime_top_abs_contribution_sum": finite_float(top_abs),
        "prime_top_abs_fraction": 0.0 if total_abs == 0.0 else finite_float(top_abs / total_abs),
        "prime_by_region": bucket_rows(by_region, total_abs),
        "prime_by_r_pow": bucket_rows(by_power, total_abs),
        "prime_top_shifts_by_abs_contribution": top_rows,
    }


def rayleigh_weighted_continuum_breakdown(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    N: np.ndarray,
    Gc: np.ndarray,
    ell: float,
    y: np.ndarray,
    *,
    weight_fn: Any,
    lo: float,
    hi: float,
    halo: float,
    max_a: float,
    p0_na: int,
) -> dict[str, Any]:
    a_grid = np.linspace(0.0, max_a, p0_na)
    wa = pilot.trap_weights_uniform(a_grid)
    by_region: dict[str, dict[str, Any]] = {}
    rayleigh = 0.0
    total_abs = 0.0

    for a, w in zip(a_grid, wa):
        scalar = float(weight_fn(float(a)))
        coeff = float(w) * math.exp(0.5 * float(a)) * scalar
        if coeff == 0.0:
            continue
        M = coeff * shifted_packet_matrix(pilot, packet, D, ell, float(a))
        A = generalized_to_standard(pilot, project_matrix(pilot, M, N), Gc)
        contribution = float(y @ A @ y)
        rayleigh += contribution
        total_abs += abs(contribution)
        region = edge_region(float(a), lo=lo, hi=hi, halo=halo)
        add_bucket(by_region, region, contribution)

    return {
        "continuum_rayleigh": finite_float(rayleigh),
        "continuum_abs_contribution_sum": finite_float(total_abs),
        "continuum_by_region": bucket_rows(by_region, total_abs),
    }


def rayleigh_correction_continuum_breakdown(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    N: np.ndarray,
    Gc: np.ndarray,
    ell: float,
    y: np.ndarray,
    *,
    plus_weight_fn: Any,
    lo: float,
    hi: float,
    halo: float,
    max_a: float,
    p0_na: int,
) -> dict[str, Any]:
    """Break down the exact continuum operator P0(M+) - P0(edge).

    `build_P0_edge` uses a dedicated interval grid, while `P0(M+)` uses a
    full `[0,max_a]` grid.  This helper mirrors that exact convention so the
    Rayleigh check matches the matrix used by `clvrecv`.
    """
    by_region: dict[str, dict[str, Any]] = {}
    rayleigh = 0.0
    total_abs = 0.0

    def add_continuum_grid(a_grid: np.ndarray, weights: np.ndarray, sign: float, weight_fn: Any) -> None:
        nonlocal rayleigh, total_abs
        for a, w in zip(a_grid, weights):
            coeff = sign * float(w) * math.exp(0.5 * float(a)) * float(weight_fn(float(a)))
            if coeff == 0.0:
                continue
            M = coeff * shifted_packet_matrix(pilot, packet, D, ell, float(a))
            A = generalized_to_standard(pilot, project_matrix(pilot, M, N), Gc)
            contribution = float(y @ A @ y)
            rayleigh += contribution
            total_abs += abs(contribution)
            region = edge_region(float(a), lo=lo, hi=hi, halo=halo)
            add_bucket(by_region, region, contribution)

    plus_grid = np.linspace(0.0, max_a, p0_na)
    add_continuum_grid(plus_grid, pilot.trap_weights_uniform(plus_grid), 1.0, plus_weight_fn)

    edge_grid = np.linspace(lo, hi, p0_na)
    add_continuum_grid(edge_grid, pilot.trap_weights_uniform(edge_grid), -1.0, lambda _a: 1.0)

    return {
        "continuum_rayleigh": finite_float(rayleigh),
        "continuum_abs_contribution_sum": finite_float(total_abs),
        "continuum_by_region": bucket_rows(by_region, total_abs),
    }


def opnorm_sym(A: np.ndarray) -> float:
    if A.size == 0:
        return 0.0
    eigs = np.linalg.eigvalsh(A)
    return float(max(abs(float(eigs[0])), abs(float(eigs[-1]))))


def spectral_summary(A: np.ndarray, *, top: int = 8) -> dict[str, Any]:
    A = 0.5 * (A + A.T)
    eigs = np.linalg.eigvalsh(A)
    abs_eigs = np.abs(eigs)
    fro = float(np.linalg.norm(A, ord="fro"))
    nuclear = float(np.sum(abs_eigs))
    opnorm = 0.0 if len(abs_eigs) == 0 else float(np.max(abs_eigs))
    sq_total = float(np.sum(abs_eigs**2))
    abs_total = float(np.sum(abs_eigs))
    order = np.argsort(-abs_eigs)
    top_rows = []
    for idx in order[:top]:
        top_rows.append(
            {
                "index": int(idx),
                "eigenvalue": finite_float(float(eigs[idx])),
                "abs_fraction": 0.0
                if abs_total == 0.0
                else finite_float(float(abs_eigs[idx]) / abs_total),
                "fro_fraction": 0.0
                if sq_total == 0.0
                else finite_float(float(abs_eigs[idx] ** 2) / sq_total),
            }
        )
    return {
        "opnorm": finite_float(opnorm),
        "lambda_min": finite_float(float(eigs[0])) if len(eigs) else 0.0,
        "lambda_max": finite_float(float(eigs[-1])) if len(eigs) else 0.0,
        "fro_norm": finite_float(fro),
        "nuclear_norm": finite_float(nuclear),
        "effective_rank_fro": finite_float(0.0 if fro == 0.0 else nuclear**2 / fro**2),
        "top_abs_eigenvalues": top_rows,
    }


def row_column_concentration(
    A: np.ndarray,
    *,
    top_counts: list[int],
    top: int,
) -> dict[str, Any]:
    A2 = np.asarray(A, dtype=float) ** 2
    total = float(np.sum(A2))
    row_energy = np.sum(A2, axis=1)
    order = np.argsort(-row_energy)
    top_rows = [
        {
            "index": int(idx),
            "row_fro_fraction": 0.0
            if total == 0.0
            else finite_float(float(row_energy[idx]) / total),
        }
        for idx in order[:top]
    ]
    captures = []
    n = A.shape[0]
    for count in top_counts:
        k = min(int(count), n)
        idxs = order[:k]
        mask = np.zeros_like(A2, dtype=bool)
        mask[idxs, :] = True
        mask[:, idxs] = True
        block = np.zeros_like(A2, dtype=bool)
        block[np.ix_(idxs, idxs)] = True
        captures.append(
            {
                "rows": int(k),
                "union_rows_cols_fro_fraction": 0.0
                if total == 0.0
                else finite_float(float(np.sum(A2[mask])) / total),
                "principal_block_fro_fraction": 0.0
                if total == 0.0
                else finite_float(float(np.sum(A2[block])) / total),
            }
        )
    return {
        "basis": "standardized projected kerQ basis",
        "top_rows_by_fro_energy": top_rows,
        "captures": captures,
    }


def add_matrix_bucket(mats: dict[str, np.ndarray], key: str, M: np.ndarray) -> None:
    if key not in mats:
        mats[key] = np.zeros_like(M, dtype=float)
    mats[key] += M


def build_prime_region_matrices(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    shifts: list[Any],
    *,
    weight_fn: Any,
    lo: float,
    hi: float,
    halo: float,
) -> dict[str, np.ndarray]:
    mats: dict[str, np.ndarray] = {}
    for sh in shifts:
        scalar = float(weight_fn(float(sh.a)))
        if scalar == 0.0:
            continue
        M = sh.weight * scalar * shifted_packet_matrix(pilot, packet, D, ell, sh.a)
        add_matrix_bucket(mats, edge_region(float(sh.a), lo=lo, hi=hi, halo=halo), M)
    return {key: pilot.sym(M) for key, M in mats.items()}


def build_correction_continuum_region_matrices(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    *,
    plus_weight_fn: Any,
    lo: float,
    hi: float,
    halo: float,
    max_a: float,
    p0_na: int,
) -> dict[str, np.ndarray]:
    """Region matrices for P0(M+) - P0(edge), matching `build_P0_edge`."""
    mats: dict[str, np.ndarray] = {}

    def add_grid(a_grid: np.ndarray, weights: np.ndarray, sign: float, weight_fn: Any) -> None:
        for a, w in zip(a_grid, weights):
            coeff = sign * float(w) * math.exp(0.5 * float(a)) * float(weight_fn(float(a)))
            if coeff == 0.0:
                continue
            M = coeff * shifted_packet_matrix(pilot, packet, D, ell, float(a))
            add_matrix_bucket(mats, edge_region(float(a), lo=lo, hi=hi, halo=halo), M)

    plus_grid = np.linspace(0.0, max_a, p0_na)
    add_grid(plus_grid, pilot.trap_weights_uniform(plus_grid), 1.0, plus_weight_fn)

    edge_grid = np.linspace(lo, hi, p0_na)
    add_grid(edge_grid, pilot.trap_weights_uniform(edge_grid), -1.0, lambda _a: 1.0)
    return {key: pilot.sym(M) for key, M in mats.items()}


def sum_region_matrices(mats: dict[str, np.ndarray], regions: set[str], template: np.ndarray) -> np.ndarray:
    out = np.zeros_like(template, dtype=float)
    for region in regions:
        if region in mats:
            out += mats[region]
    return out


def standard_summary_for_matrix(
    pilot: Any,
    M: np.ndarray,
    N: np.ndarray,
    Gc: np.ndarray,
    *,
    top: int,
) -> dict[str, Any]:
    A = generalized_to_standard(pilot, project_matrix(pilot, M, N), Gc)
    return spectral_summary(A, top=top)


def standardized_eigenvector_to_full_coeffs(
    Gc: np.ndarray,
    N: np.ndarray,
    y: np.ndarray,
) -> np.ndarray:
    chol = linalg.cholesky(Gc, lower=True)
    z = linalg.solve_triangular(chol.T, y, lower=False, check_finite=False)
    return N @ z


def packet_profile_value(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    coeffs: np.ndarray,
    a: float,
) -> float:
    M = shifted_packet_matrix(pilot, packet, D, ell, float(a))
    return float(coeffs @ M @ coeffs)


def packet_profile_grid(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    coeffs: np.ndarray,
    a_grid: np.ndarray,
) -> np.ndarray:
    return np.array(
        [packet_profile_value(pilot, packet, D, ell, coeffs, float(a)) for a in a_grid],
        dtype=float,
    )


def centered_bspline_derivative(pilot: Any, deg: int, x: np.ndarray | float) -> np.ndarray:
    x_arr = np.asarray(x, dtype=float)
    if deg <= 0:
        return np.zeros_like(x_arr, dtype=float)
    return pilot.centered_bspline(deg - 1, x_arr + 0.5) - pilot.centered_bspline(
        deg - 1, x_arr - 0.5
    )


def centered_bspline_second_derivative(pilot: Any, deg: int, x: np.ndarray | float) -> np.ndarray:
    x_arr = np.asarray(x, dtype=float)
    if deg <= 1:
        return np.zeros_like(x_arr, dtype=float)
    return (
        pilot.centered_bspline(deg - 2, x_arr + 1.0)
        - 2.0 * pilot.centered_bspline(deg - 2, x_arr)
        + pilot.centered_bspline(deg - 2, x_arr - 1.0)
    )


def r_corr_derivative(pilot: Any, packet: Any, x: np.ndarray | float) -> np.ndarray:
    deg = 2 * int(packet.k_spline) + 1
    y = packet.s_k * np.asarray(x, dtype=float)
    return (packet.s_k / packet.c_k) * centered_bspline_derivative(pilot, deg, y)


def r_corr_second_derivative(pilot: Any, packet: Any, x: np.ndarray | float) -> np.ndarray:
    deg = 2 * int(packet.k_spline) + 1
    y = packet.s_k * np.asarray(x, dtype=float)
    return (packet.s_k**2 / packet.c_k) * centered_bspline_second_derivative(pilot, deg, y)


def shifted_packet_matrix_derivative(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    a: float,
) -> np.ndarray:
    return (
        -r_corr_derivative(pilot, packet, (D - a) / ell)
        + r_corr_derivative(pilot, packet, (D + a) / ell)
    ) / ell


def shifted_packet_matrix_second_derivative(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    a: float,
) -> np.ndarray:
    return (
        r_corr_second_derivative(pilot, packet, (D - a) / ell)
        + r_corr_second_derivative(pilot, packet, (D + a) / ell)
    ) / (ell**2)


def packet_profile_derivative_value(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    coeffs: np.ndarray,
    a: float,
) -> float:
    M = shifted_packet_matrix_derivative(pilot, packet, D, ell, float(a))
    return float(coeffs @ M @ coeffs)


def packet_profile_second_derivative_value(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    coeffs: np.ndarray,
    a: float,
) -> float:
    M = shifted_packet_matrix_second_derivative(pilot, packet, D, ell, float(a))
    return float(coeffs @ M @ coeffs)


def packet_profile_derivative_grid(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    coeffs: np.ndarray,
    a_grid: np.ndarray,
) -> np.ndarray:
    return np.array(
        [
            packet_profile_derivative_value(pilot, packet, D, ell, coeffs, float(a))
            for a in a_grid
        ],
        dtype=float,
    )


def packet_profile_second_derivative_grid(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    coeffs: np.ndarray,
    a_grid: np.ndarray,
) -> np.ndarray:
    return np.array(
        [
            packet_profile_second_derivative_value(pilot, packet, D, ell, coeffs, float(a))
            for a in a_grid
        ],
        dtype=float,
    )


def psi_error_on_grid(a_grid: np.ndarray, shifts: list[Any]) -> np.ndarray:
    sorted_shifts = sorted(shifts, key=lambda sh: float(sh.a))
    shift_a = np.array([float(sh.a) for sh in sorted_shifts], dtype=float)
    lambda_weights = np.array(
        [float(sh.weight) * math.exp(0.5 * float(sh.a)) for sh in sorted_shifts],
        dtype=float,
    )
    cumulative = np.cumsum(lambda_weights)
    idx = np.searchsorted(shift_a, a_grid, side="right") - 1
    psi = np.zeros_like(a_grid, dtype=float)
    valid = idx >= 0
    psi[valid] = cumulative[idx[valid]]
    return psi - np.exp(a_grid)


def chebyshev_staircase_arrays(shifts: list[Any]) -> tuple[np.ndarray, np.ndarray]:
    sorted_shifts = sorted(shifts, key=lambda sh: float(sh.a))
    shift_a = np.array([float(sh.a) for sh in sorted_shifts], dtype=float)
    lambda_weights = np.array(
        [float(sh.weight) * math.exp(0.5 * float(sh.a)) for sh in sorted_shifts],
        dtype=float,
    )
    cumulative = np.cumsum(lambda_weights)
    return shift_a, cumulative


def chebyshev_psi_error_at(
    a: float,
    shift_a: np.ndarray,
    cumulative: np.ndarray,
    *,
    side: str,
) -> float:
    if side == "right":
        idx = int(np.searchsorted(shift_a, float(a), side="right") - 1)
    elif side == "left":
        idx = int(np.searchsorted(shift_a, float(a), side="left") - 1)
    else:
        raise ValueError("side must be 'left' or 'right'")
    psi = 0.0 if idx < 0 else float(cumulative[idx])
    return psi - math.exp(float(a))


def finite_chebyshev_error_sup_on_cell(
    cell_lo: float,
    cell_hi: float,
    shift_a: np.ndarray,
    cumulative: np.ndarray,
) -> dict[str, Any]:
    """Finite supremum candidates for |psi(e^a)-e^a| on a raw-a cell.

    Between prime-power jumps, psi(e^a)-e^a is strictly decreasing.  Therefore
    the supremum of its absolute value is attained at a cell endpoint or at a
    left/right limit of a jump point.  This is still a diagnostic floating-point
    extraction of the finite candidate list, not a Lean certificate.
    """
    candidates: list[tuple[float, str, float]] = [
        (float(cell_lo), "left_endpoint_left", chebyshev_psi_error_at(cell_lo, shift_a, cumulative, side="left")),
        (float(cell_lo), "left_endpoint_right", chebyshev_psi_error_at(cell_lo, shift_a, cumulative, side="right")),
        (float(cell_hi), "right_endpoint_left", chebyshev_psi_error_at(cell_hi, shift_a, cumulative, side="left")),
        (float(cell_hi), "right_endpoint_right", chebyshev_psi_error_at(cell_hi, shift_a, cumulative, side="right")),
    ]
    lo_idx = int(np.searchsorted(shift_a, float(cell_lo), side="left"))
    hi_idx = int(np.searchsorted(shift_a, float(cell_hi), side="right"))
    for idx in range(lo_idx, hi_idx):
        a0 = float(shift_a[idx])
        candidates.append(
            (a0, "jump_left", chebyshev_psi_error_at(a0, shift_a, cumulative, side="left"))
        )
        candidates.append(
            (a0, "jump_right", chebyshev_psi_error_at(a0, shift_a, cumulative, side="right"))
        )
    best_a, best_label, best_value = max(candidates, key=lambda item: abs(float(item[2])))
    return {
        "finite_sup_abs_psi_minus_x": finite_float(abs(float(best_value))),
        "finite_sup_location": finite_float(float(best_a)),
        "finite_sup_side": best_label,
        "finite_sup_signed_value": finite_float(float(best_value)),
        "finite_sup_candidate_count": int(len(candidates)),
        "finite_jump_count": int(hi_idx - lo_idx),
    }


def explicit_psi_error_bound(a_grid: np.ndarray) -> np.ndarray:
    """Unconditional explicit proxy for |psi(x)-x| in x=e^a coordinates.

    For x>2 this uses the Fiori--Kadiri--Swidinsky shape recorded in the
    Track B docs.  For very small x we fall back to a trivial positive bound.
    The minimum with x*(log x+1) is a diagnostic tightening, not a new theorem
    claim in the docs.
    """
    a = np.asarray(a_grid, dtype=float)
    x = np.exp(a)
    trivial = x * (np.maximum(a, 0.0) + 1.0)
    out = trivial.copy()
    mask = x > 2.0
    if np.any(mask):
        am = np.maximum(a[mask], 1e-15)
        fks = 9.22106 * x[mask] * am ** 1.5 * np.exp(-0.8476836 * np.sqrt(am))
        out[mask] = np.minimum(trivial[mask], fks)
    return out


def stieltjes_variation_bounds(
    a_grid: np.ndarray,
    H: np.ndarray,
    shifts: list[Any],
) -> dict[str, Any]:
    dH = np.gradient(H, a_grid, edge_order=2 if len(a_grid) >= 3 else 1)
    phi = np.exp(-0.5 * a_grid) * H
    variation_density = np.exp(-0.5 * a_grid) * np.abs(dH - 0.5 * H)
    endpoint_weight = abs(float(phi[0])) + abs(float(phi[-1]))
    variation_x = float(np.trapezoid(variation_density, a_grid))
    psi_err = psi_error_on_grid(a_grid, shifts)
    exact_U = np.abs(psi_err)
    pnt_U = explicit_psi_error_bound(a_grid)

    exact_weighted = (
        float(exact_U[0]) * abs(float(phi[0]))
        + float(exact_U[-1]) * abs(float(phi[-1]))
        + float(np.trapezoid(exact_U * variation_density, a_grid))
    )
    pnt_weighted = (
        float(pnt_U[0]) * abs(float(phi[0]))
        + float(pnt_U[-1]) * abs(float(phi[-1]))
        + float(np.trapezoid(pnt_U * variation_density, a_grid))
    )
    exact_sup = float(np.max(exact_U))
    pnt_sup = float(np.max(pnt_U))

    return {
        "phi_endpoint_weight": finite_float(endpoint_weight),
        "variation_x": finite_float(variation_x),
        "sup_exact_abs_psi_minus_x_on_grid": finite_float(exact_sup),
        "sup_explicit_pnt_bound_on_grid": finite_float(pnt_sup),
        "exact_grid_weighted_variation_bound": finite_float(exact_weighted),
        "exact_grid_sup_variation_bound": finite_float(exact_sup * (endpoint_weight + variation_x)),
        "explicit_pnt_weighted_variation_bound": finite_float(pnt_weighted),
        "explicit_pnt_sup_variation_bound": finite_float(pnt_sup * (endpoint_weight + variation_x)),
        "max_abs_H": finite_float(float(np.max(np.abs(H)))),
        "L1_abs_H_da": finite_float(float(np.trapezoid(np.abs(H), a_grid))),
        "L1_abs_phi_dx_density": finite_float(
            float(np.trapezoid(np.exp(0.5 * a_grid) * np.abs(H), a_grid))
        ),
    }


def even_cosine_fourier_values(
    a_grid: np.ndarray,
    H: np.ndarray,
    u_grid: np.ndarray,
) -> np.ndarray:
    weights = np.zeros_like(a_grid, dtype=float)
    if len(a_grid) == 1:
        weights[0] = 1.0
    else:
        weights[1:-1] = 0.5 * (a_grid[2:] - a_grid[:-2])
        weights[0] = 0.5 * (a_grid[1] - a_grid[0])
        weights[-1] = 0.5 * (a_grid[-1] - a_grid[-2])
    cos_mat = np.cos(2.0 * math.pi * np.outer(u_grid, a_grid))
    return 2.0 * (cos_mat @ (weights * H))


def sampled_fourier_sign_summary(
    a_grid: np.ndarray,
    H: np.ndarray,
    *,
    u_max: float,
    u_points: int,
) -> dict[str, Any]:
    u_grid = np.linspace(0.0, float(u_max), int(u_points))
    hat = even_cosine_fourier_values(a_grid, H, u_grid)
    neg = np.maximum(-hat, 0.0)
    pos = np.maximum(hat, 0.0)
    neg_area = float(np.trapezoid(neg, u_grid))
    pos_area = float(np.trapezoid(pos, u_grid))
    abs_area = neg_area + pos_area
    neg_idx = np.flatnonzero(hat < -1e-10)
    min_idx = int(np.argmin(hat))
    max_idx = int(np.argmax(hat))
    return {
        "u_min": 0.0,
        "u_max": finite_float(float(u_max)),
        "u_points": int(u_points),
        "hat_min": finite_float(float(hat[min_idx])),
        "hat_min_u": finite_float(float(u_grid[min_idx])),
        "hat_max": finite_float(float(hat[max_idx])),
        "hat_max_u": finite_float(float(u_grid[max_idx])),
        "hat_at_zero": finite_float(float(hat[0])),
        "negative_sample_count": int(len(neg_idx)),
        "negative_sample_fraction": finite_float(float(len(neg_idx)) / float(len(u_grid))),
        "first_negative_u": None if len(neg_idx) == 0 else finite_float(float(u_grid[int(neg_idx[0])])),
        "negative_area": finite_float(neg_area),
        "positive_area": finite_float(pos_area),
        "negative_area_fraction": finite_float(0.0 if abs_area == 0.0 else neg_area / abs_area),
        "L1_abs_H_da": finite_float(float(np.trapezoid(np.abs(H), a_grid))),
        "integral_H_da": finite_float(float(np.trapezoid(H, a_grid))),
    }


def capture_count(values: list[float], fraction: float) -> int:
    if not values:
        return 0
    total = float(sum(values))
    if total <= 0.0:
        return 0
    running = 0.0
    for idx, value in enumerate(sorted(values, reverse=True), start=1):
        running += float(value)
        if running >= fraction * total:
            return idx
    return len(values)


def ratio_or_none(numerator: float, denominator: float) -> float | None:
    if denominator <= 0.0:
        return None
    return finite_float(float(numerator) / float(denominator))


def sampled_sign_change_count(values: np.ndarray, *, rel_tol: float = 1e-10) -> int:
    arr = np.asarray(values, dtype=float)
    if arr.size == 0:
        return 0
    threshold = rel_tol * max(1.0, float(np.max(np.abs(arr))))
    signs = np.sign(arr[np.abs(arr) > threshold])
    if signs.size < 2:
        return 0
    return int(np.count_nonzero(signs[1:] * signs[:-1] < 0.0))


def sampled_sign_partition_variation(
    a_grid: np.ndarray,
    phi_grid: np.ndarray,
    derivative_grid: np.ndarray,
    *,
    rel_tol: float = 1e-10,
) -> dict[str, Any]:
    """Diagnostic endpoint-variation after sampled derivative sign changes."""
    a = np.asarray(a_grid, dtype=float)
    phi = np.asarray(phi_grid, dtype=float)
    deriv = np.asarray(derivative_grid, dtype=float)
    if a.size < 2 or phi.size != a.size or deriv.size != a.size:
        return {
            "sampled_sign_partition_count": 0,
            "sampled_sign_partition_break_count": 0,
            "sampled_sign_partition_variation": 0.0,
            "sampled_sign_partition_variation_over_continuous": None,
            "sampled_sign_partition_max_width": 0.0,
        }

    threshold = rel_tol * max(1.0, float(np.max(np.abs(deriv))))
    signs = np.zeros_like(deriv, dtype=int)
    signs[deriv > threshold] = 1
    signs[deriv < -threshold] = -1

    break_indices = [0]
    prev_idx: int | None = None
    prev_sign = 0
    for idx, sign in enumerate(signs):
        if sign == 0:
            continue
        if prev_sign != 0 and int(sign) != prev_sign:
            if prev_idx is not None:
                break_indices.append(prev_idx)
            break_indices.append(idx)
        prev_idx = idx
        prev_sign = int(sign)
    break_indices.append(int(a.size - 1))
    break_indices = sorted(
        set(int(min(max(idx, 0), int(a.size - 1))) for idx in break_indices)
    )

    widths = [
        float(a[right] - a[left])
        for left, right in zip(break_indices[:-1], break_indices[1:])
    ]
    variation = sum(
        abs(float(phi[right]) - float(phi[left]))
        for left, right in zip(break_indices[:-1], break_indices[1:])
    )
    continuous_variation = float(np.trapezoid(np.abs(deriv), a))
    return {
        "sampled_sign_partition_count": int(max(0, len(break_indices) - 1)),
        "sampled_sign_partition_break_count": int(max(0, len(break_indices) - 2)),
        "sampled_sign_partition_variation": finite_float(float(variation)),
        "sampled_sign_partition_variation_over_continuous": ratio_or_none(
            variation, continuous_variation
        ),
        "sampled_sign_partition_max_width": finite_float(max(widths) if widths else 0.0),
    }


def sampled_root_brackets(
    a_grid: np.ndarray,
    values: np.ndarray,
    *,
    rel_tol: float = 1e-10,
    max_brackets: int = 16,
) -> list[dict[str, Any]]:
    a = np.asarray(a_grid, dtype=float)
    arr = np.asarray(values, dtype=float)
    if a.size < 2 or arr.size != a.size:
        return []
    threshold = rel_tol * max(1.0, float(np.max(np.abs(arr))))
    signs = np.zeros_like(arr, dtype=int)
    signs[arr > threshold] = 1
    signs[arr < -threshold] = -1
    brackets: list[dict[str, Any]] = []
    prev_idx: int | None = None
    prev_sign = 0
    for idx, sign in enumerate(signs):
        if sign == 0:
            continue
        if prev_sign != 0 and int(sign) != prev_sign and prev_idx is not None:
            brackets.append(
                {
                    "a_lo": finite_float(float(a[prev_idx])),
                    "a_hi": finite_float(float(a[idx])),
                    "value_lo": finite_float(float(arr[prev_idx])),
                    "value_hi": finite_float(float(arr[idx])),
                }
            )
            if len(brackets) >= max_brackets:
                break
        prev_idx = idx
        prev_sign = int(sign)
    return brackets


def interval_safety_stress_summary(
    *,
    min_abs: float,
    lipschitz_sample: float,
    max_mesh: float,
    safety_factors: list[float],
) -> dict[str, Any]:
    """Stress the sign guard under inflated derivative envelopes.

    This is a proof-generator audit only.  A future proof certificate must
    replace the sampled derivative by an outward-rounded interval bound.
    """
    rows: list[dict[str, Any]] = []
    passing: list[float] = []
    for factor in sorted(float(f) for f in safety_factors if float(f) > 0.0):
        inflated_guard = (
            float(min_abs) - 0.5 * factor * float(lipschitz_sample) * float(max_mesh)
        )
        row = {
            "factor": finite_float(factor),
            "inflated_guard": finite_float(inflated_guard),
            "passes": bool(inflated_guard > 0.0),
        }
        rows.append(row)
        if inflated_guard > 0.0:
            passing.append(factor)
    failing = [float(row["factor"]) for row in rows if not bool(row["passes"])]
    return {
        "route": "sampled_derivative_inflation_stress",
        "stress_factors": rows,
        "largest_passing_factor": None if not passing else finite_float(max(passing)),
        "first_failing_factor": None if not failing else finite_float(min(failing)),
        "proof_status": (
            "diagnostic_only: stress factors do not replace outward-rounded "
            "interval bounds for S and S'"
        ),
    }


def smooth_segment_sign_candidate(
    pilot: Any,
    packet: Any,
    D: np.ndarray,
    ell: float,
    coeffs: np.ndarray,
    *,
    seg_lo: float,
    seg_hi: float,
    correction_weight: Any,
    correction_weight_derivatives: Any | None = None,
    receiver_node_audit: Any | None = None,
    interval_safety_factors: list[float] | None = None,
    sample_count: int,
) -> dict[str, Any]:
    if seg_hi <= seg_lo:
        return {
            "a_lo": finite_float(float(seg_lo)),
            "a_hi": finite_float(float(seg_hi)),
            "sample_count": 0,
            "status": "empty_segment",
        }

    n = max(5, int(sample_count))
    a_grid = np.linspace(float(seg_lo), float(seg_hi), n)
    correction_weights = np.array([correction_weight(float(a)) for a in a_grid], dtype=float)
    if correction_weight_derivatives is None:
        weight_derivative = np.gradient(
            correction_weights, a_grid, edge_order=2 if len(a_grid) >= 3 else 1
        )
        weight_second_derivative = np.gradient(
            weight_derivative, a_grid, edge_order=2 if len(a_grid) >= 3 else 1
        )
        receiver_derivative_source = "sampled_finite_difference"
        receiver_derivative_fd_error = 0.0
        receiver_second_derivative_fd_error = 0.0
    else:
        (
            correction_weights,
            weight_derivative,
            weight_second_derivative,
        ) = correction_weight_derivatives(a_grid)
        weight_derivative_fd = np.gradient(
            correction_weights, a_grid, edge_order=2 if len(a_grid) >= 3 else 1
        )
        weight_second_derivative_fd = np.gradient(
            weight_derivative_fd, a_grid, edge_order=2 if len(a_grid) >= 3 else 1
        )
        receiver_derivative_source = "analytic_vaaler_polygamma_derivative"
        receiver_derivative_fd_error = float(
            np.nanmax(np.abs(weight_derivative - weight_derivative_fd))
        )
        receiver_second_derivative_fd_error = float(
            np.nanmax(np.abs(weight_second_derivative - weight_second_derivative_fd))
        )
    profile = packet_profile_grid(pilot, packet, D, ell, coeffs, a_grid)
    profile_derivative = packet_profile_derivative_grid(pilot, packet, D, ell, coeffs, a_grid)
    profile_second_derivative = packet_profile_second_derivative_grid(
        pilot, packet, D, ell, coeffs, a_grid
    )
    H = correction_weights * profile
    dH = weight_derivative * profile + correction_weights * profile_derivative
    ddH = (
        weight_second_derivative * profile
        + 2.0 * weight_derivative * profile_derivative
        + correction_weights * profile_second_derivative
    )
    signed_density = np.exp(-0.5 * a_grid) * (dH - 0.5 * H)
    signed_density_derivative = np.exp(-0.5 * a_grid) * (ddH - dH + 0.25 * H)
    phi = np.exp(-0.5 * a_grid) * H
    sign_changes = sampled_sign_change_count(signed_density)
    partition = sampled_sign_partition_variation(a_grid, phi, signed_density)
    root_brackets = sampled_root_brackets(a_grid, signed_density)
    spacing = np.diff(a_grid)
    max_mesh = float(np.max(spacing)) if spacing.size else 0.0
    lipschitz_sample = float(np.max(np.abs(signed_density_derivative)))
    max_abs = float(np.max(np.abs(signed_density)))
    min_abs = float(np.min(np.abs(signed_density)))
    sign_guard = min_abs - 0.5 * lipschitz_sample * max_mesh
    endpoint_variation = abs(float(phi[-1]) - float(phi[0]))
    continuous_variation = float(np.trapezoid(np.abs(signed_density), a_grid))
    node_audit = {} if receiver_node_audit is None else receiver_node_audit(a_grid)
    lipschitz_denominator = 0.5 * lipschitz_sample * max_mesh
    if lipschitz_denominator > 0.0:
        allowable_lipschitz_multiplier = min_abs / lipschitz_denominator
    else:
        allowable_lipschitz_multiplier = math.inf
    stress_summary = interval_safety_stress_summary(
        min_abs=min_abs,
        lipschitz_sample=lipschitz_sample,
        max_mesh=max_mesh,
        safety_factors=interval_safety_factors or [],
    )
    sign_orientation = (
        "positive"
        if float(np.min(signed_density)) > 0.0
        else "negative"
        if float(np.max(signed_density)) < 0.0
        else "mixed_sampled"
    )
    status = "needs_root_isolation"
    if sign_changes == 0 and sign_guard > 0.0:
        status = "sampled_sign_stable_candidate"
    elif sign_changes == 0:
        status = "sampled_sign_stable_but_guard_weak"
    if node_audit and node_audit.get("needs_local_node_treatment"):
        non_node_status = "not_non_node_segment"
    elif sign_changes != 0:
        non_node_status = "needs_root_isolation"
    elif sign_guard <= 0.0:
        non_node_status = "needs_tighter_lipschitz_bound"
    else:
        non_node_status = "candidate"
    non_node_interval_candidate = {
        "route": "direct_polygamma_lipschitz_grid",
        "status": non_node_status,
        "certificate_inequality": "min_abs_S > 0.5 * L_S * mesh",
        "sign_orientation": sign_orientation,
        "sampled_min_abs_S": finite_float(min_abs),
        "sampled_L_S": finite_float(lipschitz_sample),
        "sampled_mesh": finite_float(max_mesh),
        "sampled_guard": finite_float(sign_guard),
        "allowable_LS_multiplier": finite_float_or_none(allowable_lipschitz_multiplier),
        "allowable_LS_multiplier_slack": finite_float_or_none(
            allowable_lipschitz_multiplier - 1.0
        ),
        "interval_safety_stress": stress_summary,
        "proof_status": (
            "diagnostic_only: replace sampled extrema by outward-rounded interval "
            "bounds for S and S' before using this certificate"
        ),
    }
    return {
        "a_lo": finite_float(float(seg_lo)),
        "a_hi": finite_float(float(seg_hi)),
        "sample_count": int(n),
        "status": status,
        "signed_density_min": finite_float(float(np.min(signed_density))),
        "signed_density_max": finite_float(float(np.max(signed_density))),
        "signed_density_min_abs": finite_float(min_abs),
        "signed_density_max_abs": finite_float(max_abs),
        "sampled_lipschitz_signed_density": finite_float(lipschitz_sample),
        "signed_density_derivative_max_abs": finite_float(lipschitz_sample),
        "profile_derivative_source": "analytic_centered_b_spline_derivative",
        "receiver_derivative_source": receiver_derivative_source,
        "receiver_derivative_fd_max_abs_error": finite_float(receiver_derivative_fd_error),
        "receiver_second_derivative_fd_max_abs_error": finite_float(
            receiver_second_derivative_fd_error
        ),
        "profile_derivative_max_abs": finite_float(float(np.max(np.abs(profile_derivative)))),
        "profile_second_derivative_max_abs": finite_float(
            float(np.max(np.abs(profile_second_derivative)))
        ),
        "receiver_derivative_max_abs": finite_float(float(np.max(np.abs(weight_derivative)))),
        "receiver_second_derivative_max_abs": finite_float(
            float(np.max(np.abs(weight_second_derivative)))
        ),
        "receiver_node_audit": node_audit,
        "non_node_interval_candidate": non_node_interval_candidate,
        "sampled_mesh": finite_float(max_mesh),
        "sampled_sign_guard": finite_float(sign_guard),
        "sampled_sign_changes": int(sign_changes),
        "sampled_root_brackets": root_brackets,
        "continuous_variation_x": finite_float(continuous_variation),
        "endpoint_variation_x": finite_float(endpoint_variation),
        "endpoint_variation_over_continuous": ratio_or_none(
            endpoint_variation, continuous_variation
        ),
        **partition,
    }


def split_cell_at_edge_jumps(
    cell_lo: float,
    cell_hi: float,
    *,
    edge_lo: float,
    edge_hi: float,
    sample_count: int,
) -> tuple[list[tuple[float, float]], list[tuple[str, float]]]:
    width = max(float(cell_hi) - float(cell_lo), 0.0)
    eps = max(width / max(4.0 * float(max(2, sample_count - 1)), 1.0), 1e-12)
    jumps: list[tuple[str, float]] = []
    split_points: list[float] = [float(cell_lo), float(cell_hi)]
    for label, a0 in [("left_edge_jump", edge_lo), ("right_edge_jump", edge_hi)]:
        if float(cell_lo) - 1e-12 <= float(a0) <= float(cell_hi) + 1e-12:
            jumps.append((label, float(a0)))
            split_points.extend([float(a0) - eps, float(a0) + eps])
    split_points = sorted(
        set(float(min(max(point, cell_lo), cell_hi)) for point in split_points)
    )
    segments = [
        (left, right)
        for left, right in zip(split_points[:-1], split_points[1:])
        if right - left > 2.0e-12
        and not any(abs(0.5 * (left + right) - a0) <= eps for _, a0 in jumps)
    ]
    return segments, jumps


def run_finiteop(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        lo, hi = 2.0 * K, 4.0 * K
        ctx = build_packet_context(
            pilot,
            K=K,
            ell=args.ell,
            grid_delta=args.grid_delta,
            k_spline=args.k_spline,
            p0_na=args.p0_na,
        )
        params = ctx["params"]
        packet = ctx["packet"]
        D = ctx["D"]
        N = ctx["N"]
        Gc = ctx["Gc"]

        shifts = pilot.prime_power_shifts(params.L)
        edge_shifts = [sh for sh in shifts if lo <= sh.a <= hi]
        P_edge = np.zeros_like(D, dtype=float)
        for sh in edge_shifts:
            P_edge += sh.weight * shifted_packet_matrix(pilot, packet, D, params.ell, sh.a)
        P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, args.p0_na)
        Pnu_edge = pilot.sym(P_edge - P0_edge)

        A_edge = generalized_to_standard(pilot, project_matrix(pilot, Pnu_edge, N), Gc)
        C_edge = generalized_to_standard(pilot, project_matrix(pilot, P0_edge, N), Gc)
        eigs, evecs = np.linalg.eigh(A_edge)
        fro_norm = float(np.linalg.norm(A_edge, ord="fro"))
        nuclear_norm = float(np.sum(np.abs(eigs)))

        def eigen_row(label: str, idx: int) -> dict[str, Any]:
            y = evecs[:, idx]
            breakdown = rayleigh_shift_breakdown(
                pilot,
                packet,
                D,
                N,
                Gc,
                params.ell,
                edge_shifts,
                y,
                top=args.top,
            )
            continuum_rayleigh = float(y @ C_edge @ y)
            lambda_rayleigh = float(breakdown["prime_rayleigh"]) - continuum_rayleigh
            return {
                "label": label,
                "lambda": finite_float(float(eigs[idx])),
                "lambda_rayleigh_check": finite_float(lambda_rayleigh),
                "lambda_check_abs_error": finite_float(abs(float(eigs[idx]) - lambda_rayleigh)),
                "continuum_rayleigh": finite_float(continuum_rayleigh),
                **breakdown,
            }

        rows.append(
            {
                "mode": "finiteop",
                "K": finite_float(K),
                "raw_edge": [finite_float(lo), finite_float(hi)],
                "ell": finite_float(params.ell),
                "grid_delta": finite_float(params.delta),
                "k_spline": int(params.k_spline),
                "n_centers": int(len(ctx["u"])),
                "kerQ_dim": int(N.shape[1]),
                "prime_power_shifts_total": int(len(shifts)),
                "edge_prime_power_shifts": int(len(edge_shifts)),
                "finite_certificate": (
                    "projected finite model certifies "
                    "lambda_min*G <= P_edge-P0_edge <= lambda_max*G"
                ),
                "lambda_min": finite_float(float(eigs[0])),
                "lambda_max": finite_float(float(eigs[-1])),
                "two_sided_epsilon": finite_float(max(abs(float(eigs[0])), abs(float(eigs[-1])))),
                "fro_norm_standard": finite_float(fro_norm),
                "nuclear_norm_standard": finite_float(nuclear_norm),
                "effective_rank_fro": finite_float(0.0 if fro_norm == 0.0 else nuclear_norm**2 / fro_norm**2),
                "upper_worst": eigen_row("upper", -1),
                "lower_worst": eigen_row("lower", 0),
                "D2": "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), finite projected operator only",
            }
        )
    return rows


def run_finitesweep(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        lo, hi = 2.0 * K, 4.0 * K
        for ell in args.ell_values:
            for grid_delta in args.grid_delta_values:
                try:
                    ctx = build_packet_context(
                        pilot,
                        K=K,
                        ell=ell,
                        grid_delta=grid_delta,
                        k_spline=args.k_spline,
                        p0_na=args.p0_na,
                    )
                    params = ctx["params"]
                    packet = ctx["packet"]
                    D = ctx["D"]
                    N = ctx["N"]
                    Gc = ctx["Gc"]

                    shifts = pilot.prime_power_shifts(params.L)
                    edge_shifts = [sh for sh in shifts if lo <= sh.a <= hi]
                    P_edge = np.zeros_like(D, dtype=float)
                    for sh in edge_shifts:
                        P_edge += sh.weight * shifted_packet_matrix(pilot, packet, D, params.ell, sh.a)
                    P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, args.p0_na)
                    Pnu_edge = pilot.sym(P_edge - P0_edge)
                    A_edge = generalized_to_standard(pilot, project_matrix(pilot, Pnu_edge, N), Gc)
                    eigs = np.linalg.eigvalsh(A_edge)
                    epsilon = max(abs(float(eigs[0])), abs(float(eigs[-1])))
                    fro_norm = float(np.linalg.norm(A_edge, ord="fro"))
                    nuclear_norm = float(np.sum(np.abs(eigs)))
                    eig_G = np.linalg.eigvalsh(Gc)
                    rows.append(
                        {
                            "mode": "finitesweep",
                            "status": "ok",
                            "K": finite_float(K),
                            "raw_edge": [finite_float(lo), finite_float(hi)],
                            "ell": finite_float(ell),
                            "ell_over_K": finite_float(ell / K),
                            "grid_delta": finite_float(grid_delta),
                            "grid_delta_over_ell": finite_float(grid_delta / ell),
                            "k_spline": int(params.k_spline),
                            "n_centers": int(len(ctx["u"])),
                            "kerQ_dim": int(N.shape[1]),
                            "prime_power_shifts_total": int(len(shifts)),
                            "edge_prime_power_shifts": int(len(edge_shifts)),
                            "lambda_min": finite_float(float(eigs[0])),
                            "lambda_max": finite_float(float(eigs[-1])),
                            "two_sided_epsilon": finite_float(epsilon),
                            "epsilon_times_K": finite_float(epsilon * K),
                            "epsilon_times_sqrt_K": finite_float(epsilon * math.sqrt(K)),
                            "fro_norm_standard": finite_float(fro_norm),
                            "nuclear_norm_standard": finite_float(nuclear_norm),
                            "effective_rank_fro": finite_float(
                                0.0 if fro_norm == 0.0 else nuclear_norm**2 / fro_norm**2
                            ),
                            "eig_Gc_min": finite_float(float(eig_G[0])),
                            "eig_Gc_max": finite_float(float(eig_G[-1])),
                            "G_condition": finite_float(float(eig_G[-1] / eig_G[0])),
                            "D2": "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), packet-scale sweep",
                        }
                    )
                except Exception as exc:  # numerical probe should report bad scale choices.
                    rows.append(
                        {
                            "mode": "finitesweep",
                            "status": "error",
                            "K": finite_float(K),
                            "raw_edge": [finite_float(lo), finite_float(hi)],
                            "ell": finite_float(ell),
                            "ell_over_K": finite_float(ell / K),
                            "grid_delta": finite_float(grid_delta),
                            "grid_delta_over_ell": finite_float(grid_delta / ell),
                            "k_spline": int(args.k_spline),
                            "error": str(exc),
                            "D2": "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), packet-scale sweep",
                        }
                    )
    return rows


def run_finiteschedule(args: argparse.Namespace) -> list[dict[str, Any]]:
    sweep_rows = run_finitesweep(args)
    selected: list[dict[str, Any]] = []
    rejected_counts: dict[str, int] = {
        "error": 0,
        "kerQ_dim": 0,
        "G_condition": 0,
        "eig_Gc_min": 0,
    }

    for K in args.K:
        candidates: list[dict[str, Any]] = []
        for row in sweep_rows:
            if row.get("K") != float(K):
                continue
            if row.get("status") != "ok":
                rejected_counts["error"] += 1
                continue
            if int(row["kerQ_dim"]) < args.min_ker_dim:
                rejected_counts["kerQ_dim"] += 1
                continue
            if float(row["G_condition"]) > args.max_g_condition:
                rejected_counts["G_condition"] += 1
                continue
            if float(row["eig_Gc_min"]) < args.min_g_eig:
                rejected_counts["eig_Gc_min"] += 1
                continue
            candidates.append(row)

        if candidates:
            best = min(
                candidates,
                key=lambda row: (
                    float(row["two_sided_epsilon"]),
                    float(row["G_condition"]),
                    -int(row["kerQ_dim"]),
                ),
            )
            selected.append({**best, "mode": "finiteschedule_selected", "eligible_count": len(candidates)})
        else:
            selected.append(
                {
                    "mode": "finiteschedule_selected",
                    "status": "no_eligible_candidate",
                    "K": finite_float(K),
                    "eligible_count": 0,
                    "D2": "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), stability-filtered schedule",
                }
            )

    fit_candidates = [row for row in selected if row.get("status") == "ok"]
    fit: dict[str, Any] = {"status": "insufficient_points"}
    if len(fit_candidates) >= 2:
        ks = np.array([float(row["K"]) for row in fit_candidates], dtype=float)
        eps = np.array([float(row["two_sided_epsilon"]) for row in fit_candidates], dtype=float)
        slope, intercept = np.polyfit(np.log(ks), np.log(eps), 1)
        c_fit = -float(slope)
        C_fit = float(math.exp(intercept))
        fitted = C_fit * ks ** (-c_fit)
        fit = {
            "status": "ok",
            "power_c_fit": finite_float(c_fit),
            "power_C_fit": finite_float(C_fit),
            "max_abs_log_residual": finite_float(float(np.max(np.abs(np.log(eps) - np.log(fitted))))),
            "selected_K": [finite_float(x) for x in ks.tolist()],
            "selected_epsilon": [finite_float(x) for x in eps.tolist()],
        }

    summary = {
        "mode": "finiteschedule_summary",
        "status": "ok" if fit_candidates else "no_eligible_candidate",
        "K": [finite_float(float(K)) for K in args.K],
        "ell_values": [finite_float(float(x)) for x in args.ell_values],
        "grid_delta_values": [finite_float(float(x)) for x in args.grid_delta_values],
        "min_ker_dim": int(args.min_ker_dim),
        "max_g_condition": finite_float(args.max_g_condition),
        "min_g_eig": finite_float(args.min_g_eig),
        "p0_na": int(args.p0_na),
        "k_spline": int(args.k_spline),
        "total_sweep_rows": int(len(sweep_rows)),
        "selected_count": int(len(fit_candidates)),
        "rejected_counts": rejected_counts,
        "fit": fit,
        "D2": "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), stability-filtered schedule",
    }
    return [summary] + selected


def log_gap_summary(values: list[float]) -> dict[str, Any]:
    if len(values) < 2:
        return {
            "count": int(len(values)),
            "min_raw_log_gap": None,
            "median_raw_log_gap": None,
            "max_raw_log_gap": None,
            "min_q3_xi_gap": None,
            "hilbert_pi_over_min_raw_gap": None,
            "hilbert_pi_over_median_raw_gap": None,
        }
    gaps = np.diff(np.array(sorted(values), dtype=float))
    min_gap = float(np.min(gaps))
    median_gap = float(np.median(gaps))
    max_gap = float(np.max(gaps))
    return {
        "count": int(len(values)),
        "min_raw_log_gap": finite_float(min_gap),
        "median_raw_log_gap": finite_float(median_gap),
        "max_raw_log_gap": finite_float(max_gap),
        "min_q3_xi_gap": finite_float(min_gap / (2.0 * math.pi)),
        "hilbert_pi_over_min_raw_gap": finite_float(math.pi / min_gap),
        "hilbert_pi_over_median_raw_gap": finite_float(math.pi / median_gap),
    }


def run_spacing(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        lo, hi = 2.0 * K, 4.0 * K
        params = pilot.PilotParams(
            L=2.0 * K,
            ell=0.35,
            delta=0.5,
            k_spline=5,
            p0_na=3,
        )
        edge_shifts = [sh for sh in pilot.prime_power_shifts(params.L) if lo <= sh.a <= hi]
        ordinary = [sh for sh in edge_shifts if int(sh.r_pow) == 1]
        prime_powers = [sh for sh in edge_shifts if int(sh.r_pow) != 1]
        ordinary_logs = [float(sh.a) for sh in ordinary]
        all_logs = [float(sh.a) for sh in edge_shifts]
        integer_node_lower_gap_raw = math.log1p(math.exp(-hi))
        edge_length = hi - lo
        ordinary_weight_sum = sum(float(sh.weight) for sh in ordinary)
        all_weight_sum = sum(float(sh.weight) for sh in edge_shifts)
        row = {
            "mode": "spacing",
            "K": finite_float(K),
            "raw_edge": [finite_float(lo), finite_float(hi)],
            "edge_length_raw": finite_float(edge_length),
            "ordinary_primes": log_gap_summary(ordinary_logs),
            "all_prime_powers": log_gap_summary(all_logs),
            "edge_prime_power_shifts": int(len(edge_shifts)),
            "edge_ordinary_prime_shifts": int(len(ordinary)),
            "edge_nonordinary_prime_power_shifts": int(len(prime_powers)),
            "ordinary_weight_sum": finite_float(ordinary_weight_sum),
            "all_weight_sum": finite_float(all_weight_sum),
            "ordinary_weight_fraction": finite_float(
                0.0 if all_weight_sum == 0.0 else ordinary_weight_sum / all_weight_sum
            ),
            "average_ordinary_gap_raw": None
            if len(ordinary) < 2
            else finite_float(edge_length / float(len(ordinary) - 1)),
            "integer_node_lower_gap_raw": finite_float(integer_node_lower_gap_raw),
            "integer_node_lower_gap_q3_xi": finite_float(integer_node_lower_gap_raw / (2.0 * math.pi)),
            "hilbert_barrier_note": (
                "Montgomery-Vaughan/Hilbert separation-only constants scale like "
                "pi/min_gap in raw log frequency; this is a D2 obstruction, not a proof input."
            ),
            "D2": "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), spacing-only Hilbert barrier",
        }
        rows.append(row)
    return rows


def vaaler_K0(z: np.ndarray) -> np.ndarray:
    return np.sinc(z) ** 2


def vaaler_K0_derivatives(z: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    z = np.asarray(z, dtype=float)
    k0 = vaaler_K0(z)
    k1 = np.empty_like(z, dtype=float)
    k2 = np.empty_like(z, dtype=float)
    small = np.abs(z) < 1e-8
    zs = z[~small]
    if zs.size:
        sinp = np.sin(math.pi * zs)
        cosp = np.cos(math.pi * zs)
        k1[~small] = 2.0 * sinp * (math.pi * zs * cosp - sinp) / (math.pi**2 * zs**3)
        k2[~small] = (
            2.0
            * (
                (math.pi**2 * zs**2) * np.cos(2.0 * math.pi * zs)
                - 2.0 * math.pi * zs * np.sin(2.0 * math.pi * zs)
                + 3.0 * sinp**2
            )
            / (math.pi**2 * zs**4)
        )
    if np.any(small):
        zs0 = z[small]
        k1[small] = -(2.0 * math.pi**2 / 3.0) * zs0 + (4.0 * math.pi**4 / 45.0) * zs0**3
        k2[small] = -(2.0 * math.pi**2 / 3.0) + (4.0 * math.pi**4 / 15.0) * zs0**2
    return k0, k1, k2


def vaaler_H0(z: np.ndarray, *, integer_tol: float = 1e-10) -> np.ndarray:
    """Vaaler's H0 sign approximant in the B1 Fourier convention.

    The formula is the defining series rewritten through trigamma:
      sum_{m>=1} ((z-m)^-2 - (z+m)^-2) + 2/z
        = psi_1(1-z) - psi_1(1+z) + 2/z.
    Removable singularities at integers are filled by H0(n)=sgn(n).
    """
    z = np.asarray(z, dtype=float)
    out = np.empty_like(z, dtype=float)
    nearest = np.rint(z)
    integer_mask = np.abs(z - nearest) <= integer_tol
    out[integer_mask] = np.sign(nearest[integer_mask])
    regular = ~integer_mask
    zr = z[regular]
    if zr.size:
        series = special.polygamma(1, 1.0 - zr) - special.polygamma(1, 1.0 + zr) + 2.0 / zr
        out[regular] = (np.sin(math.pi * zr) / math.pi) ** 2 * series
    return out


def vaaler_H0_derivatives(
    z: np.ndarray,
    *,
    integer_tol: float = 1e-10,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return H0, H0', H0'' from the polygamma product formula.

    Values exactly at integers are filled for H0 only.  Derivatives at those
    removable points are left as NaN because the Track B smooth segments should
    split before Vaaler interpolation nodes.
    """
    z = np.asarray(z, dtype=float)
    h0 = vaaler_H0(z, integer_tol=integer_tol)
    h1 = np.full_like(z, np.nan, dtype=float)
    h2 = np.full_like(z, np.nan, dtype=float)
    nearest = np.rint(z)
    regular = np.abs(z - nearest) > integer_tol
    zr = z[regular]
    if zr.size:
        sinp = np.sin(math.pi * zr)
        A = (sinp / math.pi) ** 2
        A1 = np.sin(2.0 * math.pi * zr) / math.pi
        A2 = 2.0 * np.cos(2.0 * math.pi * zr)
        B = special.polygamma(1, 1.0 - zr) - special.polygamma(1, 1.0 + zr) + 2.0 / zr
        B1 = (
            -special.polygamma(2, 1.0 - zr)
            - special.polygamma(2, 1.0 + zr)
            - 2.0 / (zr**2)
        )
        B2 = (
            special.polygamma(3, 1.0 - zr)
            - special.polygamma(3, 1.0 + zr)
            + 4.0 / (zr**3)
        )
        h1[regular] = A1 * B + A * B1
        h2[regular] = A2 * B + 2.0 * A1 * B1 + A * B2
    return h0, h1, h2


def max_finite(values: np.ndarray) -> float | None:
    arr = np.asarray(values, dtype=float)
    finite = arr[np.isfinite(arr)]
    if finite.size == 0:
        return None
    return finite_float(float(np.max(finite)))


def max_abs_finite(values: np.ndarray) -> float | None:
    arr = np.asarray(values, dtype=float)
    finite = arr[np.isfinite(arr)]
    if finite.size == 0:
        return None
    return finite_float(float(np.max(np.abs(finite))))


def cancellation_ratio_summary(terms: list[np.ndarray], result: np.ndarray) -> dict[str, Any]:
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        abs_sum = np.zeros_like(np.asarray(result, dtype=float), dtype=float)
        for term in terms:
            abs_sum += np.abs(np.asarray(term, dtype=float))
        denom = np.abs(np.asarray(result, dtype=float))
        ratio = abs_sum / np.maximum(denom, 1e-300)
    return {
        "max_abs_term_sum": max_abs_finite(abs_sum),
        "max_cancellation_ratio": max_finite(ratio),
    }


def vaaler_H0_cancellation_summary(z: np.ndarray) -> dict[str, Any]:
    z = np.asarray(z, dtype=float)
    nearest = np.rint(z)
    regular = np.abs(z - nearest) > 1e-10
    zr = z[regular]
    if zr.size == 0:
        return {
            "regular_sample_count": 0,
            "B": {"max_abs_term_sum": None, "max_cancellation_ratio": None},
            "B_prime": {"max_abs_term_sum": None, "max_cancellation_ratio": None},
            "B_second": {"max_abs_term_sum": None, "max_cancellation_ratio": None},
            "H0_prime": {"max_abs_term_sum": None, "max_cancellation_ratio": None},
            "H0_second": {"max_abs_term_sum": None, "max_cancellation_ratio": None},
        }
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        sinp = np.sin(math.pi * zr)
        A = (sinp / math.pi) ** 2
        A1 = np.sin(2.0 * math.pi * zr) / math.pi
        A2 = 2.0 * np.cos(2.0 * math.pi * zr)

        B_terms = [
            special.polygamma(1, 1.0 - zr),
            -special.polygamma(1, 1.0 + zr),
            2.0 / zr,
        ]
        B = B_terms[0] + B_terms[1] + B_terms[2]
        B1_terms = [
            -special.polygamma(2, 1.0 - zr),
            -special.polygamma(2, 1.0 + zr),
            -2.0 / (zr**2),
        ]
        B1 = B1_terms[0] + B1_terms[1] + B1_terms[2]
        B2_terms = [
            special.polygamma(3, 1.0 - zr),
            -special.polygamma(3, 1.0 + zr),
            4.0 / (zr**3),
        ]
        B2 = B2_terms[0] + B2_terms[1] + B2_terms[2]
        H1_terms = [A1 * B, A * B1]
        H1 = H1_terms[0] + H1_terms[1]
        H2_terms = [A2 * B, 2.0 * A1 * B1, A * B2]
        H2 = H2_terms[0] + H2_terms[1] + H2_terms[2]
    return {
        "regular_sample_count": int(zr.size),
        "B": cancellation_ratio_summary(B_terms, B),
        "B_prime": cancellation_ratio_summary(B1_terms, B1),
        "B_second": cancellation_ratio_summary(B2_terms, B2),
        "H0_prime": cancellation_ratio_summary(H1_terms, H1),
        "H0_second": cancellation_ratio_summary(H2_terms, H2),
    }


def vaaler_node_axis_audit(a_grid: np.ndarray, z: np.ndarray, label: str) -> dict[str, Any]:
    a = np.asarray(a_grid, dtype=float)
    z_arr = np.asarray(z, dtype=float)
    nearest = np.rint(z_arr)
    distance = np.abs(z_arr - nearest)
    min_idx = int(np.argmin(distance))
    z_min = float(np.min(z_arr))
    z_max = float(np.max(z_arr))
    crossed = [
        int(n)
        for n in range(math.ceil(z_min), math.floor(z_max) + 1)
        if z_min <= float(n) <= z_max
    ]
    return {
        "label": label,
        "z_min": finite_float(z_min),
        "z_max": finite_float(z_max),
        "nearest_integer_at_min_distance": int(nearest[min_idx]),
        "min_distance_to_integer": finite_float(float(distance[min_idx])),
        "a_at_min_distance": finite_float(float(a[min_idx])),
        "crossed_integer_count": int(len(crossed)),
        "crossed_integers": crossed[:16],
        "samples_within_1e_minus_2": int(np.count_nonzero(distance <= 1e-2)),
        "samples_within_1e_minus_3": int(np.count_nonzero(distance <= 1e-3)),
        "samples_within_1e_minus_4": int(np.count_nonzero(distance <= 1e-4)),
        "needs_local_node_treatment": bool(float(distance[min_idx]) <= 1e-3 or crossed),
        "H0_cancellation": vaaler_H0_cancellation_summary(z_arr),
    }


def selberg_receiver_node_audit(
    a_grid: np.ndarray,
    *,
    lo: float,
    hi: float,
    receiver_delta: float,
) -> dict[str, Any]:
    a = np.asarray(a_grid, dtype=float)
    za = receiver_delta * (a - lo)
    zb = receiver_delta * (a - hi)
    left = vaaler_node_axis_audit(a, za, "z_left=delta*(a-2K)")
    right = vaaler_node_axis_audit(a, zb, "z_right=delta*(a-4K)")
    min_distance = min(
        float(left["min_distance_to_integer"]),
        float(right["min_distance_to_integer"]),
    )
    return {
        "left_axis": left,
        "right_axis": right,
        "min_distance_to_any_vaaler_integer": finite_float(min_distance),
        "needs_local_node_treatment": bool(
            left["needs_local_node_treatment"] or right["needs_local_node_treatment"]
        ),
    }


def selberg_interval_plus_derivatives(
    x: np.ndarray,
    *,
    lo: float,
    hi: float,
    receiver_delta: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if receiver_delta <= 0.0:
        raise ValueError("receiver_delta must be positive")
    x = np.asarray(x, dtype=float)
    za = receiver_delta * (x - lo)
    zb = receiver_delta * (x - hi)
    Ha0, Ha1, Ha2 = vaaler_H0_derivatives(za)
    Hb0, Hb1, Hb2 = vaaler_H0_derivatives(zb)
    Ka0, Ka1, Ka2 = vaaler_K0_derivatives(za)
    Kb0, Kb1, Kb2 = vaaler_K0_derivatives(zb)
    value = 0.5 * Ha0 - 0.5 * Hb0 + 0.5 * Ka0 + 0.5 * Kb0
    first = receiver_delta * (0.5 * Ha1 - 0.5 * Hb1 + 0.5 * Ka1 + 0.5 * Kb1)
    second = receiver_delta**2 * (0.5 * Ha2 - 0.5 * Hb2 + 0.5 * Ka2 + 0.5 * Kb2)
    return value, first, second


def selberg_interval_values(
    x: np.ndarray,
    *,
    lo: float,
    hi: float,
    receiver_delta: float,
    sign: str,
) -> np.ndarray:
    if receiver_delta <= 0.0:
        raise ValueError("receiver_delta must be positive")
    if sign not in {"plus", "minus"}:
        raise ValueError("sign must be 'plus' or 'minus'")
    x = np.asarray(x, dtype=float)
    za = receiver_delta * (x - lo)
    zb = receiver_delta * (x - hi)
    central = 0.5 * vaaler_H0(za) - 0.5 * vaaler_H0(zb)
    endpoint = 0.5 * vaaler_K0(za) + 0.5 * vaaler_K0(zb)
    return central + endpoint if sign == "plus" else central - endpoint


def indicator_interval_values(x: np.ndarray, *, lo: float, hi: float) -> np.ndarray:
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x, dtype=float)
    inside = (lo < x) & (x < hi)
    endpoints = np.isclose(x, lo, rtol=0.0, atol=1e-12) | np.isclose(x, hi, rtol=0.0, atol=1e-12)
    out[inside] = 1.0
    out[endpoints] = 0.5
    return out


def selberg_grid_sanity(*, lo: float, hi: float, receiver_delta: float, nt: int) -> dict[str, Any]:
    margin = max(8.0 / receiver_delta, 1.0)
    x = np.linspace(lo - margin, hi + margin, nt)
    chi = indicator_interval_values(x, lo=lo, hi=hi)
    m_plus = selberg_interval_values(x, lo=lo, hi=hi, receiver_delta=receiver_delta, sign="plus")
    m_minus = selberg_interval_values(x, lo=lo, hi=hi, receiver_delta=receiver_delta, sign="minus")
    plus_gap = m_plus - chi
    minus_gap = chi - m_minus
    return {
        "grid_nt": int(nt),
        "grid_margin": finite_float(margin),
        "min_Mplus_minus_chi": finite_float(float(np.min(plus_gap))),
        "min_chi_minus_Mminus": finite_float(float(np.min(minus_gap))),
        "trapz_Mplus_minus_chi": finite_float(float(np.trapezoid(plus_gap, x))),
        "trapz_chi_minus_Mminus": finite_float(float(np.trapezoid(minus_gap, x))),
        "expected_L1_error": finite_float(1.0 / receiver_delta),
    }


def run_clvrecv(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        lo, hi = 2.0 * K, 4.0 * K
        for receiver_delta in args.receiver_delta:
            ctx = build_packet_context(
                pilot,
                K=K,
                ell=args.ell,
                grid_delta=args.grid_delta,
                k_spline=args.k_spline,
                p0_na=args.p0_na,
            )
            params = ctx["params"]
            packet = ctx["packet"]
            D = ctx["D"]
            N = ctx["N"]
            Gc = ctx["Gc"]

            effective_max_a = effective_shift_cutoff(D, params.ell)
            shift_params = pilot.PilotParams(
                L=0.5 * effective_max_a,
                ell=params.ell,
                delta=params.delta,
                k_spline=params.k_spline,
                p0_na=args.p0_na,
            )
            shifts = pilot.prime_power_shifts(shift_params.L)

            def chi_weight(a: float) -> float:
                return 1.0 if lo <= a <= hi else 0.0

            def plus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]), lo=lo, hi=hi, receiver_delta=receiver_delta, sign="plus"
                    )[0]
                )

            def minus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]), lo=lo, hi=hi, receiver_delta=receiver_delta, sign="minus"
                    )[0]
                )

            P_edge = build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, chi_weight)
            P_plus = build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, plus_weight)
            P_minus = build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, minus_weight)
            P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, args.p0_na)
            P0_plus = build_continuum_matrix_for_weight(
                pilot,
                packet,
                D,
                params.ell,
                max_a=effective_max_a,
                p0_na=args.p0_na,
                weight_fn=plus_weight,
            )
            P0_minus = build_continuum_matrix_for_weight(
                pilot,
                packet,
                D,
                params.ell,
                max_a=effective_max_a,
                p0_na=args.p0_na,
                weight_fn=minus_weight,
            )

            def eig_row(label: str, M: np.ndarray) -> dict[str, Any]:
                eigs = projected_generalized_eigs(pilot, pilot.sym(M), N, Gc)
                return {
                    f"{label}_eig_min": finite_float(float(eigs[0])),
                    f"{label}_eig_max": finite_float(float(eigs[-1])),
                    f"{label}_opnorm": finite_float(max(abs(float(eigs[0])), abs(float(eigs[-1])))),
                }

            hard = P_edge - P0_edge
            plus = P_plus - P0_plus
            minus = P_minus - P0_minus
            edge_shift_count = sum(1 for sh in shifts if lo <= sh.a <= hi)
            shift_points = np.array([float(sh.a) for sh in shifts], dtype=float)
            plus_values = selberg_interval_values(
                shift_points, lo=lo, hi=hi, receiver_delta=receiver_delta, sign="plus"
            )
            minus_values = selberg_interval_values(
                shift_points, lo=lo, hi=hi, receiver_delta=receiver_delta, sign="minus"
            )
            chi_values = np.array([chi_weight(float(a)) for a in shift_points], dtype=float)

            row: dict[str, Any] = {
                "mode": "clvrecv",
                "K": finite_float(K),
                "raw_edge": [finite_float(lo), finite_float(hi)],
                "receiver_delta": finite_float(receiver_delta),
                "receiver_type": "Selberg-Vaaler interval M+ / M-",
                "receiver_exponential_type": finite_float(2.0 * math.pi * receiver_delta),
                "receiver_fourier_support": [
                    finite_float(-receiver_delta),
                    finite_float(receiver_delta),
                ],
                "receiver_L1_error_exact": finite_float(1.0 / receiver_delta),
                "max_a_effective": finite_float(effective_max_a),
                "ell": finite_float(params.ell),
                "grid_delta": finite_float(params.delta),
                "k_spline": int(params.k_spline),
                "n_centers": int(len(ctx["u"])),
                "kerQ_dim": int(N.shape[1]),
                "prime_power_shifts_total": int(len(shifts)),
                "edge_prime_power_shifts": int(edge_shift_count),
                "prime_scalar_Mplus_minus_chi_min": finite_float(float(np.min(plus_values - chi_values))),
                "prime_scalar_chi_minus_Mminus_min": finite_float(float(np.min(chi_values - minus_values))),
                "prime_scalar_Mplus_weight_sum": finite_float(
                    sum(float(sh.weight) * float(val) for sh, val in zip(shifts, plus_values))
                ),
                "prime_scalar_edge_weight_sum": finite_float(
                    sum(float(sh.weight) * float(val) for sh, val in zip(shifts, chi_values))
                ),
                "prime_scalar_Mminus_weight_sum": finite_float(
                    sum(float(sh.weight) * float(val) for sh, val in zip(shifts, minus_values))
                ),
                "grid_sanity": selberg_grid_sanity(
                    lo=lo,
                    hi=hi,
                    receiver_delta=receiver_delta,
                    nt=args.receiver_grid_nt,
                ),
                "D2": (
                    "raw a=r*log(p), Selberg receiver on edge=[2K,4K], "
                    "Q3 xi=a/(2*pi), operator probe only"
                ),
            }
            hard_row = eig_row("hard_edge_minus_continuum", hard)
            plus_row = eig_row("Mplus_minus_Mplus_continuum", plus)
            minus_row = eig_row("Mminus_minus_Mminus_continuum", minus)
            prime_plus_bridge_row = eig_row("prime_Mplus_minus_edge", P_plus - P_edge)
            prime_minus_bridge_row = eig_row("prime_edge_minus_Mminus", P_edge - P_minus)
            cont_plus_bridge_row = eig_row("continuum_Mplus_minus_edge", P0_plus - P0_edge)
            cont_minus_bridge_row = eig_row("continuum_edge_minus_Mminus", P0_edge - P0_minus)
            bridge_correction_plus = (P_plus - P_edge) - (P0_plus - P0_edge)
            bridge_correction_minus = (P_edge - P_minus) - (P0_edge - P0_minus)
            bridge_correction_plus_row = eig_row("bridge_correction_plus", bridge_correction_plus)
            bridge_correction_minus_row = eig_row("bridge_correction_minus", bridge_correction_minus)

            bridge_R_plus = max(
                0.0,
                -float(prime_plus_bridge_row["prime_Mplus_minus_edge_eig_min"]),
            )
            bridge_R_minus = max(
                0.0,
                -float(prime_minus_bridge_row["prime_edge_minus_Mminus_eig_min"]),
            )
            smooth_Mplus_epsilon = float(plus_row["Mplus_minus_Mplus_continuum_opnorm"])
            smooth_Mminus_epsilon = float(minus_row["Mminus_minus_Mminus_continuum_opnorm"])
            row.update(hard_row)
            row.update(plus_row)
            row.update(minus_row)
            row.update(prime_plus_bridge_row)
            row.update(prime_minus_bridge_row)
            row.update(cont_plus_bridge_row)
            row.update(cont_minus_bridge_row)
            row.update(bridge_correction_plus_row)
            row.update(bridge_correction_minus_row)
            row.update(
                {
                    "bridge_R_plus": finite_float(bridge_R_plus),
                    "bridge_R_minus": finite_float(bridge_R_minus),
                    "total_upper_budget_plus": finite_float(bridge_R_plus + smooth_Mplus_epsilon),
                    "total_upper_budget_minus": finite_float(bridge_R_minus + smooth_Mminus_epsilon),
                    "receiver_identity_plus_max_abs_error": finite_float(
                        float(np.max(np.abs(hard - (plus - bridge_correction_plus))))
                    ),
                    "receiver_identity_minus_max_abs_error": finite_float(
                        float(np.max(np.abs(hard - (minus + bridge_correction_minus))))
                    ),
                    "budget_note": (
                        "total_upper_budget_plus is the naive scalar-majorant route cost: "
                        "P(edge) <= P(M+) + R*G plus the smoothed receiver residual. "
                        "It is only a diagnostic, not a theorem certificate."
                    ),
                }
            )
            rows.append(row)
    return rows


def stable_receiver_ell(K: float, fallback: float) -> float:
    stable = {
        2.0: 0.75,
        2.5: 1.375,
        3.0: 0.75,
        3.5: 1.375,
    }
    rounded = round(float(K) * 2.0) / 2.0
    return stable.get(rounded, fallback)


def power_fit_rows(rows: list[dict[str, Any]], value_key: str) -> dict[str, Any]:
    candidates = [
        row
        for row in rows
        if row.get(value_key) is not None and float(row[value_key]) > 0.0
    ]
    if len(candidates) < 2:
        return {"status": "insufficient_points"}
    ks = np.array([float(row["K"]) for row in candidates], dtype=float)
    vals = np.array([float(row[value_key]) for row in candidates], dtype=float)
    slope, intercept = np.polyfit(np.log(ks), np.log(vals), 1)
    c_fit = -float(slope)
    C_fit = float(math.exp(intercept))
    fitted = C_fit * ks ** (-c_fit)
    return {
        "status": "ok",
        "value_key": value_key,
        "power_c_fit": finite_float(c_fit),
        "power_C_fit": finite_float(C_fit),
        "max_abs_log_residual": finite_float(float(np.max(np.abs(np.log(vals) - np.log(fitted))))),
        "selected_K": [finite_float(x) for x in ks.tolist()],
        "selected_values": [finite_float(x) for x in vals.tolist()],
    }


def run_clvprimary(args: argparse.Namespace) -> list[dict[str, Any]]:
    selected_rows: list[dict[str, Any]] = []
    for K in args.K:
        ell = stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        clv_args = argparse.Namespace(
            K=[float(K)],
            ell=float(ell),
            grid_delta=float(args.grid_delta),
            k_spline=int(args.k_spline),
            receiver_delta=[float(x) for x in args.receiver_delta],
            p0_na=int(args.p0_na),
            receiver_grid_nt=int(args.receiver_grid_nt),
        )
        rows = run_clvrecv(clv_args)
        best_smooth = min(
            rows,
            key=lambda row: (
                float(row["Mplus_minus_Mplus_continuum_opnorm"]),
                float(row["receiver_delta"]),
            ),
        )
        best_total = min(
            rows,
            key=lambda row: (
                float(row["total_upper_budget_plus"]),
                float(row["receiver_delta"]),
            ),
        )
        selected_rows.append(
            {
                "mode": "clvprimary_selected",
                "K": finite_float(float(K)),
                "schedule": args.schedule,
                "ell": finite_float(float(ell)),
                "grid_delta": finite_float(float(args.grid_delta)),
                "k_spline": int(args.k_spline),
                "p0_na": int(args.p0_na),
                "receiver_delta_values": [finite_float(float(x)) for x in args.receiver_delta],
                "best_smooth_delta": finite_float(float(best_smooth["receiver_delta"])),
                "best_smooth_epsilon": finite_float(
                    float(best_smooth["Mplus_minus_Mplus_continuum_opnorm"])
                ),
                "bridge_R_at_best_smooth": finite_float(float(best_smooth["bridge_R_plus"])),
                "bridge_correction_at_best_smooth": finite_float(
                    float(best_smooth["bridge_correction_plus_opnorm"])
                ),
                "total_at_best_smooth": finite_float(float(best_smooth["total_upper_budget_plus"])),
                "best_total_delta": finite_float(float(best_total["receiver_delta"])),
                "best_total_upper_budget": finite_float(float(best_total["total_upper_budget_plus"])),
                "smooth_at_best_total": finite_float(
                    float(best_total["Mplus_minus_Mplus_continuum_opnorm"])
                ),
                "bridge_R_at_best_total": finite_float(float(best_total["bridge_R_plus"])),
                "bridge_correction_at_best_total": finite_float(
                    float(best_total["bridge_correction_plus_opnorm"])
                ),
                "hard_edge_epsilon": finite_float(
                    float(best_smooth["hard_edge_minus_continuum_opnorm"])
                ),
                "receiver_primary_gap": (
                    "best_smooth_epsilon is B3-relevant only if the Selberg receiver is the "
                    "primary Hermitian-square explicit-formula test object; it does not by "
                    "itself bound the hard edge."
                ),
                "D2": (
                    "raw a=r*log(p), Selberg receiver on edge=[2K,4K], "
                    "Q3 xi=a/(2*pi), receiver-primary schedule diagnostic"
                ),
            }
        )

    summary = {
        "mode": "clvprimary_summary",
        "status": "ok" if selected_rows else "empty",
        "schedule": args.schedule,
        "K": [finite_float(float(K)) for K in args.K],
        "receiver_delta_values": [finite_float(float(x)) for x in args.receiver_delta],
        "grid_delta": finite_float(float(args.grid_delta)),
        "k_spline": int(args.k_spline),
        "p0_na": int(args.p0_na),
        "smooth_fit": power_fit_rows(selected_rows, "best_smooth_epsilon"),
        "hard_edge_fit": power_fit_rows(selected_rows, "hard_edge_epsilon"),
        "bridge_correction_fit": power_fit_rows(selected_rows, "bridge_correction_at_best_smooth"),
        "scalar_bridge_total_fit": power_fit_rows(selected_rows, "best_total_upper_budget"),
        "verdict_note": (
            "The smooth fit tests the receiver-primary B2b hypothesis. The scalar-bridge "
            "total fit tests the already-failing post-hoc hard-edge bridge. The bridge "
            "correction fit tests whether receiver-primary actually removed the original "
            "hard-edge fluctuation."
        ),
        "D2": (
            "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
            "receiver-primary schedule diagnostic"
        ),
    }
    return [summary] + selected_rows


def theta_grid(theta_min: float, theta_max: float, theta_count: int) -> np.ndarray:
    if theta_count <= 0:
        raise ValueError("theta-count must be positive")
    if theta_count == 1:
        return np.array([float(theta_min)], dtype=float)
    return np.linspace(float(theta_min), float(theta_max), int(theta_count), dtype=float)


def run_clvblend(args: argparse.Namespace) -> list[dict[str, Any]]:
    """Scan affine receivers R_theta = chi_I + theta * (M+ - chi_I).

    This does not search for a new proof by itself.  It tests whether the
    receiver-primary residual and bridge correction can both be made small
    inside the simplest CLV/Selberg affine span.
    """
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    thetas = theta_grid(args.theta_min, args.theta_max, args.theta_count)
    for K in args.K:
        ell = stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        lo, hi = 2.0 * float(K), 4.0 * float(K)
        for receiver_delta in args.receiver_delta:
            ctx = build_packet_context(
                pilot,
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
            )
            params = ctx["params"]
            packet = ctx["packet"]
            D = ctx["D"]
            N = ctx["N"]
            Gc = ctx["Gc"]

            effective_max_a = effective_shift_cutoff(D, params.ell)
            shift_params = pilot.PilotParams(
                L=0.5 * effective_max_a,
                ell=params.ell,
                delta=params.delta,
                k_spline=params.k_spline,
                p0_na=int(args.p0_na),
            )
            shifts = pilot.prime_power_shifts(shift_params.L)

            def chi_weight(a: float) -> float:
                return 1.0 if lo <= a <= hi else 0.0

            def plus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]),
                        lo=lo,
                        hi=hi,
                        receiver_delta=float(receiver_delta),
                        sign="plus",
                    )[0]
                )

            P_edge = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, chi_weight
            )
            P_plus = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, plus_weight
            )
            P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, int(args.p0_na))
            P0_plus = build_continuum_matrix_for_weight(
                pilot,
                packet,
                D,
                params.ell,
                max_a=effective_max_a,
                p0_na=int(args.p0_na),
                weight_fn=plus_weight,
            )

            hard = pilot.sym(P_edge - P0_edge)
            plus = pilot.sym(P_plus - P0_plus)
            correction = pilot.sym(plus - hard)

            def eig_stats(M: np.ndarray) -> tuple[float, float, float]:
                eigs = projected_generalized_eigs(pilot, pilot.sym(M), N, Gc)
                eig_min = float(eigs[0])
                eig_max = float(eigs[-1])
                return eig_min, eig_max, max(abs(eig_min), abs(eig_max))

            hard_min, hard_max, hard_op = eig_stats(hard)
            plus_min, plus_max, plus_op = eig_stats(plus)
            corr_min, corr_max, corr_op = eig_stats(correction)

            samples: list[dict[str, Any]] = []
            for theta in thetas:
                theta = float(theta)
                d_theta = hard + theta * correction
                b_theta = theta * correction
                d_min, d_max, d_op = eig_stats(d_theta)
                b_min, b_max, b_op = eig_stats(b_theta)
                triangle_total = d_op + b_op
                samples.append(
                    {
                        "theta": finite_float(theta),
                        "D_theta_eig_min": finite_float(d_min),
                        "D_theta_eig_max": finite_float(d_max),
                        "D_theta_opnorm": finite_float(d_op),
                        "B_theta_eig_min": finite_float(b_min),
                        "B_theta_eig_max": finite_float(b_max),
                        "B_theta_opnorm": finite_float(b_op),
                        "triangle_total": finite_float(triangle_total),
                        "triangle_total_minus_hard": finite_float(triangle_total - hard_op),
                        "receiver_identity_max_abs_error": finite_float(
                            float(np.max(np.abs(hard - (d_theta - b_theta))))
                        ),
                    }
                )

            best_total = min(samples, key=lambda row: (float(row["triangle_total"]), abs(float(row["theta"]))))
            best_smooth = min(samples, key=lambda row: (float(row["D_theta_opnorm"]), abs(float(row["theta"]))))
            theta_zero = min(samples, key=lambda row: abs(float(row["theta"])))
            theta_one = min(samples, key=lambda row: abs(float(row["theta"]) - 1.0))

            rows.append(
                {
                    "mode": "clvblend",
                    "K": finite_float(float(K)),
                    "schedule": args.schedule,
                    "ell": finite_float(float(ell)),
                    "raw_edge": [finite_float(lo), finite_float(hi)],
                    "receiver_delta": finite_float(float(receiver_delta)),
                    "theta_min": finite_float(float(args.theta_min)),
                    "theta_max": finite_float(float(args.theta_max)),
                    "theta_count": int(args.theta_count),
                    "p0_na": int(args.p0_na),
                    "hard_edge_eig_min": finite_float(hard_min),
                    "hard_edge_eig_max": finite_float(hard_max),
                    "hard_edge_opnorm": finite_float(hard_op),
                    "Mplus_receiver_eig_min": finite_float(plus_min),
                    "Mplus_receiver_eig_max": finite_float(plus_max),
                    "Mplus_receiver_opnorm": finite_float(plus_op),
                    "Mplus_correction_eig_min": finite_float(corr_min),
                    "Mplus_correction_eig_max": finite_float(corr_max),
                    "Mplus_correction_opnorm": finite_float(corr_op),
                    "best_total_theta": finite_float(float(best_total["theta"])),
                    "best_total_value": best_total["triangle_total"],
                    "best_total_minus_hard": best_total["triangle_total_minus_hard"],
                    "best_total_D_opnorm": best_total["D_theta_opnorm"],
                    "best_total_B_opnorm": best_total["B_theta_opnorm"],
                    "best_smooth_theta": finite_float(float(best_smooth["theta"])),
                    "best_smooth_D_opnorm": best_smooth["D_theta_opnorm"],
                    "best_smooth_B_opnorm": best_smooth["B_theta_opnorm"],
                    "theta0_total": theta_zero["triangle_total"],
                    "theta0_D_opnorm": theta_zero["D_theta_opnorm"],
                    "theta0_B_opnorm": theta_zero["B_theta_opnorm"],
                    "theta1_total": theta_one["triangle_total"],
                    "theta1_D_opnorm": theta_one["D_theta_opnorm"],
                    "theta1_B_opnorm": theta_one["B_theta_opnorm"],
                    "max_receiver_identity_error": finite_float(
                        max(float(row["receiver_identity_max_abs_error"]) for row in samples)
                    ),
                    "no_free_lunch_note": (
                        "For the exact identity D_I = D_theta - B_theta, any proof that "
                        "bounds D_theta and B_theta separately pays at least ||D_I|| by "
                        "the triangle inequality. This scan quantifies the finite "
                        "operator tradeoff inside the affine Selberg receiver span."
                    ),
                    "D2": (
                        "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
                        "R_theta=chi_I+theta*(Mplus-chi_I)"
                    ),
                }
            )

    summary = {
        "mode": "clvblend_summary",
        "status": "ok" if rows else "empty",
        "schedule": args.schedule,
        "K": [finite_float(float(K)) for K in args.K],
        "receiver_delta_values": [finite_float(float(x)) for x in args.receiver_delta],
        "theta_range": [
            finite_float(float(args.theta_min)),
            finite_float(float(args.theta_max)),
        ],
        "theta_count": int(args.theta_count),
        "best_total_fit": power_fit_rows(rows, "best_total_value"),
        "hard_edge_fit": power_fit_rows(rows, "hard_edge_opnorm"),
        "best_smooth_fit": power_fit_rows(rows, "best_smooth_D_opnorm"),
        "D2": (
            "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
            "affine receiver no-free-lunch diagnostic"
        ),
    }
    return [summary] + rows


def run_clvbreakdown(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        ell = stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        lo, hi = 2.0 * float(K), 4.0 * float(K)
        for receiver_delta in args.receiver_delta:
            ctx = build_packet_context(
                pilot,
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
            )
            params = ctx["params"]
            packet = ctx["packet"]
            D = ctx["D"]
            N = ctx["N"]
            Gc = ctx["Gc"]
            halo = float(args.halo_factor) / float(receiver_delta)
            effective_max_a = effective_shift_cutoff(D, params.ell)
            shift_params = pilot.PilotParams(
                L=0.5 * effective_max_a,
                ell=params.ell,
                delta=params.delta,
                k_spline=params.k_spline,
                p0_na=int(args.p0_na),
            )
            shifts = pilot.prime_power_shifts(shift_params.L)

            def chi_weight(a: float) -> float:
                return 1.0 if lo <= a <= hi else 0.0

            def plus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]),
                        lo=lo,
                        hi=hi,
                        receiver_delta=float(receiver_delta),
                        sign="plus",
                    )[0]
                )

            def correction_weight(a: float) -> float:
                return plus_weight(a) - chi_weight(a)

            P_edge = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, chi_weight
            )
            P_plus = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, plus_weight
            )
            P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, int(args.p0_na))
            P0_plus = build_continuum_matrix_for_weight(
                pilot,
                packet,
                D,
                params.ell,
                max_a=effective_max_a,
                p0_na=int(args.p0_na),
                weight_fn=plus_weight,
            )
            correction = pilot.sym((P_plus - P_edge) - (P0_plus - P0_edge))
            A_corr = generalized_to_standard(pilot, project_matrix(pilot, correction, N), Gc)
            eigs, evecs = np.linalg.eigh(A_corr)
            op_idx = int(np.argmax(np.abs(eigs)))
            directions = [
                ("lower", 0),
                ("upper", len(eigs) - 1),
                ("opnorm", op_idx),
            ]

            breakdown_rows: list[dict[str, Any]] = []
            for label, idx in directions:
                y = evecs[:, idx]
                prime_breakdown = rayleigh_weighted_shift_breakdown(
                    pilot,
                    packet,
                    D,
                    N,
                    Gc,
                    params.ell,
                    shifts,
                    y,
                    weight_fn=correction_weight,
                    lo=lo,
                    hi=hi,
                    halo=halo,
                    top=int(args.top),
                )
                cont_breakdown = rayleigh_correction_continuum_breakdown(
                    pilot,
                    packet,
                    D,
                    N,
                    Gc,
                    params.ell,
                    y,
                    plus_weight_fn=plus_weight,
                    lo=lo,
                    hi=hi,
                    halo=halo,
                    max_a=effective_max_a,
                    p0_na=int(args.p0_na),
                )
                lambda_check = (
                    float(prime_breakdown["prime_rayleigh"])
                    - float(cont_breakdown["continuum_rayleigh"])
                )
                prime_abs = float(prime_breakdown["prime_abs_contribution_sum"])
                cont_abs = float(cont_breakdown["continuum_abs_contribution_sum"])
                endpoint_regions = {
                    "left_outside_halo",
                    "left_inside_halo",
                    "right_inside_halo",
                    "right_outside_halo",
                }

                def endpoint_abs_fraction(rows: list[dict[str, Any]], total_abs: float) -> float:
                    if total_abs == 0.0:
                        return 0.0
                    endpoint_abs = sum(
                        float(row["abs_sum"])
                        for row in rows
                        if str(row["label"]) in endpoint_regions
                    )
                    return endpoint_abs / total_abs

                breakdown_rows.append(
                    {
                        "label": label,
                        "lambda": finite_float(float(eigs[idx])),
                        "lambda_rayleigh_check": finite_float(lambda_check),
                        "lambda_check_abs_error": finite_float(abs(float(eigs[idx]) - lambda_check)),
                        "prime_minus_continuum_abs_budget": finite_float(prime_abs + cont_abs),
                        "prime_abs_fraction_of_budget": finite_float(
                            0.0 if prime_abs + cont_abs == 0.0 else prime_abs / (prime_abs + cont_abs)
                        ),
                        "continuum_abs_fraction_of_budget": finite_float(
                            0.0 if prime_abs + cont_abs == 0.0 else cont_abs / (prime_abs + cont_abs)
                        ),
                        "prime_endpoint_abs_fraction": finite_float(
                            endpoint_abs_fraction(prime_breakdown["prime_by_region"], prime_abs)
                        ),
                        "continuum_endpoint_abs_fraction": finite_float(
                            endpoint_abs_fraction(cont_breakdown["continuum_by_region"], cont_abs)
                        ),
                        **prime_breakdown,
                        **cont_breakdown,
                    }
                )

            rows.append(
                {
                    "mode": "clvbreakdown",
                    "K": finite_float(float(K)),
                    "schedule": args.schedule,
                    "ell": finite_float(float(ell)),
                    "grid_delta": finite_float(float(args.grid_delta)),
                    "k_spline": int(args.k_spline),
                    "p0_na": int(args.p0_na),
                    "receiver_delta": finite_float(float(receiver_delta)),
                    "raw_edge": [finite_float(lo), finite_float(hi)],
                    "halo_width_raw": finite_float(halo),
                    "halo_factor": finite_float(float(args.halo_factor)),
                    "max_a_effective": finite_float(effective_max_a),
                    "kerQ_dim": int(N.shape[1]),
                    "prime_power_shifts_total": int(len(shifts)),
                    "correction_eig_min": finite_float(float(eigs[0])),
                    "correction_eig_max": finite_float(float(eigs[-1])),
                    "correction_opnorm": finite_float(
                        max(abs(float(eigs[0])), abs(float(eigs[-1])))
                    ),
                    "opnorm_label": "lower" if op_idx == 0 else "upper",
                    "breakdowns": breakdown_rows,
                    "classification_note": (
                        "Endpoint fractions near 1 would support an endpoint/boundary "
                        "cancellation route.  Small endpoint fractions and dominant r=1 "
                        "mass point toward a distributed ordinary-prime mean route."
                    ),
                    "D2": (
                        "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
                        "correction weight Mplus-chi_I"
                    ),
                }
            )
    return rows


def run_clvstructure(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    endpoint_regions = {
        "left_outside_halo",
        "left_inside_halo",
        "right_inside_halo",
        "right_outside_halo",
    }
    far_regions = {"below_far", "above_far"}

    for K in args.K:
        ell = stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        lo, hi = 2.0 * float(K), 4.0 * float(K)
        for receiver_delta in args.receiver_delta:
            ctx = build_packet_context(
                pilot,
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
            )
            params = ctx["params"]
            packet = ctx["packet"]
            D = ctx["D"]
            N = ctx["N"]
            Gc = ctx["Gc"]
            halo = float(args.halo_factor) / float(receiver_delta)
            effective_max_a = effective_shift_cutoff(D, params.ell)
            shift_params = pilot.PilotParams(
                L=0.5 * effective_max_a,
                ell=params.ell,
                delta=params.delta,
                k_spline=params.k_spline,
                p0_na=int(args.p0_na),
            )
            shifts = pilot.prime_power_shifts(shift_params.L)

            def chi_weight(a: float) -> float:
                return 1.0 if lo <= a <= hi else 0.0

            def plus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]),
                        lo=lo,
                        hi=hi,
                        receiver_delta=float(receiver_delta),
                        sign="plus",
                    )[0]
                )

            def correction_weight(a: float) -> float:
                return plus_weight(a) - chi_weight(a)

            prime_regions = build_prime_region_matrices(
                pilot,
                packet,
                D,
                params.ell,
                shifts,
                weight_fn=correction_weight,
                lo=lo,
                hi=hi,
                halo=halo,
            )
            continuum_regions = build_correction_continuum_region_matrices(
                pilot,
                packet,
                D,
                params.ell,
                plus_weight_fn=plus_weight,
                lo=lo,
                hi=hi,
                halo=halo,
                max_a=effective_max_a,
                p0_na=int(args.p0_na),
            )

            template = np.zeros_like(D, dtype=float)
            region_names = sorted(set(prime_regions) | set(continuum_regions))
            prime_total = sum_region_matrices(prime_regions, set(region_names), template)
            continuum_total = sum_region_matrices(continuum_regions, set(region_names), template)
            correction_total = pilot.sym(prime_total - continuum_total)

            A_prime = generalized_to_standard(pilot, project_matrix(pilot, prime_total, N), Gc)
            A_cont = generalized_to_standard(pilot, project_matrix(pilot, continuum_total, N), Gc)
            A_corr = generalized_to_standard(pilot, project_matrix(pilot, correction_total, N), Gc)

            endpoint_prime = sum_region_matrices(prime_regions, endpoint_regions, template)
            endpoint_cont = sum_region_matrices(continuum_regions, endpoint_regions, template)
            far_prime = sum_region_matrices(prime_regions, far_regions, template)
            far_cont = sum_region_matrices(continuum_regions, far_regions, template)
            bulk_regions = set(region_names) - endpoint_regions - far_regions
            bulk_prime = sum_region_matrices(prime_regions, bulk_regions, template)
            bulk_cont = sum_region_matrices(continuum_regions, bulk_regions, template)

            aggregate_components = {
                "prime_total": prime_total,
                "continuum_total": continuum_total,
                "correction_total": correction_total,
                "endpoint_correction": pilot.sym(endpoint_prime - endpoint_cont),
                "bulk_correction": pilot.sym(bulk_prime - bulk_cont),
                "far_correction": pilot.sym(far_prime - far_cont),
            }
            aggregate_summaries = [
                {
                    "label": label,
                    **standard_summary_for_matrix(pilot, M, N, Gc, top=int(args.top_eigs)),
                }
                for label, M in aggregate_components.items()
            ]

            region_summaries = []
            for region in region_names:
                P_region = prime_regions.get(region, template)
                C_region = continuum_regions.get(region, template)
                region_summaries.append(
                    {
                        "region": region,
                        "prime": standard_summary_for_matrix(
                            pilot, P_region, N, Gc, top=int(args.top_eigs)
                        ),
                        "continuum": standard_summary_for_matrix(
                            pilot, C_region, N, Gc, top=int(args.top_eigs)
                        ),
                        "signed_correction": standard_summary_for_matrix(
                            pilot, pilot.sym(P_region - C_region), N, Gc, top=int(args.top_eigs)
                        ),
                    }
                )

            prime_op = opnorm_sym(A_prime)
            cont_op = opnorm_sym(A_cont)
            corr_op = opnorm_sym(A_corr)
            prime_fro = float(np.linalg.norm(A_prime, ord="fro"))
            cont_fro = float(np.linalg.norm(A_cont, ord="fro"))
            corr_fro = float(np.linalg.norm(A_corr, ord="fro"))

            endpoint_A = generalized_to_standard(
                pilot,
                project_matrix(pilot, aggregate_components["endpoint_correction"], N),
                Gc,
            )
            bulk_A = generalized_to_standard(
                pilot,
                project_matrix(pilot, aggregate_components["bulk_correction"], N),
                Gc,
            )
            far_A = generalized_to_standard(
                pilot,
                project_matrix(pilot, aggregate_components["far_correction"], N),
                Gc,
            )
            split_op_sum = opnorm_sym(endpoint_A) + opnorm_sym(bulk_A) + opnorm_sym(far_A)
            split_fro_sum = (
                float(np.linalg.norm(endpoint_A, ord="fro"))
                + float(np.linalg.norm(bulk_A, ord="fro"))
                + float(np.linalg.norm(far_A, ord="fro"))
            )

            rebuild_error = float(
                np.max(
                    np.abs(
                        correction_total
                        - aggregate_components["endpoint_correction"]
                        - aggregate_components["bulk_correction"]
                        - aggregate_components["far_correction"]
                    )
                )
            )

            rows.append(
                {
                    "mode": "clvstructure",
                    "K": finite_float(float(K)),
                    "schedule": args.schedule,
                    "ell": finite_float(float(ell)),
                    "grid_delta": finite_float(float(args.grid_delta)),
                    "k_spline": int(args.k_spline),
                    "p0_na": int(args.p0_na),
                    "receiver_delta": finite_float(float(receiver_delta)),
                    "raw_edge": [finite_float(lo), finite_float(hi)],
                    "halo_width_raw": finite_float(halo),
                    "max_a_effective": finite_float(effective_max_a),
                    "kerQ_dim": int(N.shape[1]),
                    "prime_power_shifts_total": int(len(shifts)),
                    "aggregate_summaries": aggregate_summaries,
                    "region_summaries": region_summaries,
                    "prime_continuum_cancellation": {
                        "correction_opnorm": finite_float(corr_op),
                        "prime_opnorm": finite_float(prime_op),
                        "continuum_opnorm": finite_float(cont_op),
                        "opnorm_ratio_correction_over_prime_plus_continuum": finite_float(
                            0.0 if prime_op + cont_op == 0.0 else corr_op / (prime_op + cont_op)
                        ),
                        "correction_fro": finite_float(corr_fro),
                        "prime_fro": finite_float(prime_fro),
                        "continuum_fro": finite_float(cont_fro),
                        "fro_ratio_correction_over_prime_plus_continuum": finite_float(
                            0.0 if prime_fro + cont_fro == 0.0 else corr_fro / (prime_fro + cont_fro)
                        ),
                    },
                    "endpoint_bulk_far_cancellation": {
                        "correction_opnorm": finite_float(corr_op),
                        "split_opnorm_sum": finite_float(split_op_sum),
                        "opnorm_ratio_total_over_split_sum": finite_float(
                            0.0 if split_op_sum == 0.0 else corr_op / split_op_sum
                        ),
                        "correction_fro": finite_float(corr_fro),
                        "split_fro_sum": finite_float(split_fro_sum),
                        "fro_ratio_total_over_split_sum": finite_float(
                            0.0 if split_fro_sum == 0.0 else corr_fro / split_fro_sum
                        ),
                        "rebuild_max_abs_error": finite_float(rebuild_error),
                    },
                    "correction_row_column_concentration": row_column_concentration(
                        A_corr,
                        top_counts=[1, 2, 4, 8, 16],
                        top=int(args.top_rows),
                    ),
                    "D2": (
                        "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
                        "operator-level structure of B_R=(P(M+)-P(edge))-(P0(M+)-P0(edge))"
                    ),
                }
            )
    return rows


def run_clvquad(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        ell = stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        lo, hi = 2.0 * float(K), 4.0 * float(K)
        for receiver_delta in args.receiver_delta:
            ctx = build_packet_context(
                pilot,
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
            )
            params = ctx["params"]
            packet = ctx["packet"]
            D = ctx["D"]
            N = ctx["N"]
            Gc = ctx["Gc"]
            effective_max_a = effective_shift_cutoff(D, params.ell)
            shift_params = pilot.PilotParams(
                L=0.5 * effective_max_a,
                ell=params.ell,
                delta=params.delta,
                k_spline=params.k_spline,
                p0_na=int(args.p0_na),
            )
            shifts = pilot.prime_power_shifts(shift_params.L)

            def chi_weight(a: float) -> float:
                return 1.0 if lo <= a <= hi else 0.0

            def plus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]),
                        lo=lo,
                        hi=hi,
                        receiver_delta=float(receiver_delta),
                        sign="plus",
                    )[0]
                )

            def correction_weight(a: float) -> float:
                return plus_weight(a) - chi_weight(a)

            P_edge = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, chi_weight
            )
            P_plus = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, plus_weight
            )
            P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, int(args.p0_na))
            P0_plus = build_continuum_matrix_for_weight(
                pilot,
                packet,
                D,
                params.ell,
                max_a=effective_max_a,
                p0_na=int(args.p0_na),
                weight_fn=plus_weight,
            )
            correction = pilot.sym((P_plus - P_edge) - (P0_plus - P0_edge))
            A_corr = generalized_to_standard(pilot, project_matrix(pilot, correction, N), Gc)
            eigs, evecs = np.linalg.eigh(A_corr)
            op_idx = int(np.argmax(np.abs(eigs)))
            directions = [
                ("lower", 0),
                ("upper", len(eigs) - 1),
                ("opnorm", op_idx),
            ]

            a_grid = np.linspace(0.0, effective_max_a, int(args.quad_na))
            correction_weights_grid = np.array([correction_weight(float(a)) for a in a_grid], dtype=float)

            direction_rows: list[dict[str, Any]] = []
            for label, idx in directions:
                y = evecs[:, idx]
                coeffs = standardized_eigenvector_to_full_coeffs(Gc, N, y)
                profile_grid = packet_profile_grid(
                    pilot, packet, D, params.ell, coeffs, a_grid
                )
                H_grid = correction_weights_grid * profile_grid

                prime_sum = 0.0
                for sh in shifts:
                    w = correction_weight(float(sh.a))
                    if w == 0.0:
                        continue
                    prime_sum += (
                        float(sh.weight)
                        * w
                        * packet_profile_value(pilot, packet, D, params.ell, coeffs, float(sh.a))
                    )
                continuum_grid = float(np.trapezoid(np.exp(0.5 * a_grid) * H_grid, a_grid))
                direct_residual = prime_sum - continuum_grid
                variation = stieltjes_variation_bounds(a_grid, H_grid, shifts)
                actual_abs = abs(direct_residual)
                exact_weighted = float(variation["exact_grid_weighted_variation_bound"])
                pnt_weighted = float(variation["explicit_pnt_weighted_variation_bound"])

                direction_rows.append(
                    {
                        "label": label,
                        "matrix_lambda": finite_float(float(eigs[idx])),
                        "direct_prime_sum": finite_float(prime_sum),
                        "direct_continuum_grid": finite_float(continuum_grid),
                        "direct_residual": finite_float(direct_residual),
                        "matrix_minus_direct_abs_error": finite_float(
                            abs(float(eigs[idx]) - direct_residual)
                        ),
                        "actual_abs_over_exact_grid_weighted_bound": None
                        if exact_weighted == 0.0
                        else finite_float(actual_abs / exact_weighted),
                        "actual_abs_over_explicit_pnt_weighted_bound": None
                        if pnt_weighted == 0.0
                        else finite_float(actual_abs / pnt_weighted),
                        "explicit_pnt_weighted_bound_over_matrix_opnorm": finite_float(
                            pnt_weighted
                            / max(abs(float(eigs[0])), abs(float(eigs[-1])))
                        ),
                        **variation,
                    }
                )

            rows.append(
                {
                    "mode": "clvquad",
                    "K": finite_float(float(K)),
                    "schedule": args.schedule,
                    "ell": finite_float(float(ell)),
                    "grid_delta": finite_float(float(args.grid_delta)),
                    "k_spline": int(args.k_spline),
                    "p0_na": int(args.p0_na),
                    "quad_na": int(args.quad_na),
                    "receiver_delta": finite_float(float(receiver_delta)),
                    "raw_edge": [finite_float(lo), finite_float(hi)],
                    "max_a_effective": finite_float(effective_max_a),
                    "kerQ_dim": int(N.shape[1]),
                    "prime_power_shifts_total": int(len(shifts)),
                    "correction_eig_min": finite_float(float(eigs[0])),
                    "correction_eig_max": finite_float(float(eigs[-1])),
                    "correction_opnorm": finite_float(
                        max(abs(float(eigs[0])), abs(float(eigs[-1])))
                    ),
                    "directions": direction_rows,
                    "theorem_shape": (
                        "partial summation with phi(x)=x^(-1/2)*E_delta(log x)*F_v(log x); "
                        "bounds are diagnostics for a Chebyshev/PNT variation route"
                    ),
                    "D2": (
                        "raw a=r*log(p), x=exp(a), edge=[2K,4K], Q3 xi=a/(2*pi), "
                        "sum Lambda(n)n^(-1/2)H(log n) vs integral exp(a/2)H(a)da"
                    ),
                }
            )
    return rows


def run_clvfourier(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        ell = stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        lo, hi = 2.0 * float(K), 4.0 * float(K)
        for receiver_delta in args.receiver_delta:
            ctx = build_packet_context(
                pilot,
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
            )
            params = ctx["params"]
            packet = ctx["packet"]
            D = ctx["D"]
            N = ctx["N"]
            Gc = ctx["Gc"]
            effective_max_a = effective_shift_cutoff(D, params.ell)
            shift_params = pilot.PilotParams(
                L=0.5 * effective_max_a,
                ell=params.ell,
                delta=params.delta,
                k_spline=params.k_spline,
                p0_na=int(args.p0_na),
            )
            shifts = pilot.prime_power_shifts(shift_params.L)

            def chi_weight(a: float) -> float:
                return 1.0 if lo <= a <= hi else 0.0

            def plus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]),
                        lo=lo,
                        hi=hi,
                        receiver_delta=float(receiver_delta),
                        sign="plus",
                    )[0]
                )

            def correction_weight(a: float) -> float:
                return plus_weight(a) - chi_weight(a)

            P_edge = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, chi_weight
            )
            P_plus = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, plus_weight
            )
            P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, int(args.p0_na))
            P0_plus = build_continuum_matrix_for_weight(
                pilot,
                packet,
                D,
                params.ell,
                max_a=effective_max_a,
                p0_na=int(args.p0_na),
                weight_fn=plus_weight,
            )
            correction = pilot.sym((P_plus - P_edge) - (P0_plus - P0_edge))
            A_corr = generalized_to_standard(pilot, project_matrix(pilot, correction, N), Gc)
            eigs, evecs = np.linalg.eigh(A_corr)
            op_idx = int(np.argmax(np.abs(eigs)))
            directions = [
                ("lower", 0),
                ("upper", len(eigs) - 1),
                ("opnorm", op_idx),
            ]

            a_grid = np.linspace(0.0, effective_max_a, int(args.quad_na))
            correction_weights_grid = np.array([correction_weight(float(a)) for a in a_grid], dtype=float)

            direction_rows: list[dict[str, Any]] = []
            for label, idx in directions:
                y = evecs[:, idx]
                coeffs = standardized_eigenvector_to_full_coeffs(Gc, N, y)
                profile_grid = packet_profile_grid(
                    pilot, packet, D, params.ell, coeffs, a_grid
                )
                H_grid = correction_weights_grid * profile_grid
                profile_summary = sampled_fourier_sign_summary(
                    a_grid,
                    profile_grid,
                    u_max=float(args.fourier_u_max),
                    u_points=int(args.fourier_nu),
                )
                correction_summary = sampled_fourier_sign_summary(
                    a_grid,
                    H_grid,
                    u_max=float(args.fourier_u_max),
                    u_points=int(args.fourier_nu),
                )
                direction_rows.append(
                    {
                        "label": label,
                        "matrix_lambda": finite_float(float(eigs[idx])),
                        "profile_Fv_fourier": profile_summary,
                        "correction_Edelta_Fv_fourier": correction_summary,
                        "negative_area_fraction_ratio": None
                        if profile_summary["negative_area_fraction"] == 0.0
                        else finite_float(
                            float(correction_summary["negative_area_fraction"])
                            / float(profile_summary["negative_area_fraction"])
                        ),
                    }
                )

            rows.append(
                {
                    "mode": "clvfourier",
                    "K": finite_float(float(K)),
                    "schedule": args.schedule,
                    "ell": finite_float(float(ell)),
                    "grid_delta": finite_float(float(args.grid_delta)),
                    "k_spline": int(args.k_spline),
                    "p0_na": int(args.p0_na),
                    "quad_na": int(args.quad_na),
                    "fourier_u_max": finite_float(float(args.fourier_u_max)),
                    "fourier_nu": int(args.fourier_nu),
                    "receiver_delta": finite_float(float(receiver_delta)),
                    "raw_edge": [finite_float(lo), finite_float(hi)],
                    "max_a_effective": finite_float(effective_max_a),
                    "kerQ_dim": int(N.shape[1]),
                    "prime_power_shifts_total": int(len(shifts)),
                    "correction_eig_min": finite_float(float(eigs[0])),
                    "correction_eig_max": finite_float(float(eigs[-1])),
                    "correction_opnorm": finite_float(
                        max(abs(float(eigs[0])), abs(float(eigs[-1])))
                    ),
                    "directions": direction_rows,
                    "theorem_shape": (
                        "sampled Fourier sign of even raw test H(a)=E_delta(a)*F_v(a); "
                        "nonnegative Fourier would be a PSD/zero-side door"
                    ),
                    "D2": (
                        "raw a>=0 symmetrized to an even test, Fourier convention "
                        "hat(f)(u)=int f(a)exp(-2*pi*i*u*a)da, Q3 xi=a/(2*pi)"
                    ),
                }
            )
    return rows


def run_clvledger(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        ell = stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        lo, hi = 2.0 * float(K), 4.0 * float(K)
        for receiver_delta in args.receiver_delta:
            ctx = build_packet_context(
                pilot,
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
            )
            params = ctx["params"]
            packet = ctx["packet"]
            D = ctx["D"]
            N = ctx["N"]
            Gc = ctx["Gc"]
            effective_max_a = effective_shift_cutoff(D, params.ell)
            shift_params = pilot.PilotParams(
                L=0.5 * effective_max_a,
                ell=params.ell,
                delta=params.delta,
                k_spline=params.k_spline,
                p0_na=int(args.p0_na),
            )
            shifts = pilot.prime_power_shifts(shift_params.L)

            def chi_weight(a: float) -> float:
                return 1.0 if lo <= a <= hi else 0.0

            def plus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]),
                        lo=lo,
                        hi=hi,
                        receiver_delta=float(receiver_delta),
                        sign="plus",
                    )[0]
                )

            def correction_weight(a: float) -> float:
                return plus_weight(a) - chi_weight(a)

            P_edge = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, chi_weight
            )
            P_plus = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, plus_weight
            )
            P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, int(args.p0_na))
            P0_plus = build_continuum_matrix_for_weight(
                pilot,
                packet,
                D,
                params.ell,
                max_a=effective_max_a,
                p0_na=int(args.p0_na),
                weight_fn=plus_weight,
            )
            correction = pilot.sym((P_plus - P_edge) - (P0_plus - P0_edge))
            A_corr = generalized_to_standard(pilot, project_matrix(pilot, correction, N), Gc)
            eigs, evecs = np.linalg.eigh(A_corr)
            op_idx = int(np.argmax(np.abs(eigs)))
            if args.directions == "all":
                directions = [
                    ("lower", 0),
                    ("upper", len(eigs) - 1),
                    ("opnorm", op_idx),
                ]
            else:
                directions = [("opnorm", op_idx)]

            a_grid = np.linspace(0.0, effective_max_a, int(args.quad_na))
            psi_err = psi_error_on_grid(a_grid, shifts)
            pnt_err = explicit_psi_error_bound(a_grid)
            staircase_shift_a, staircase_cumulative = chebyshev_staircase_arrays(shifts)
            correction_weights_grid = np.array([correction_weight(float(a)) for a in a_grid], dtype=float)
            cell_edges = np.linspace(0.0, effective_max_a, int(args.ledger_cells) + 1)

            direction_rows: list[dict[str, Any]] = []
            for label, idx in directions:
                y = evecs[:, idx]
                coeffs = standardized_eigenvector_to_full_coeffs(Gc, N, y)
                profile_grid = packet_profile_grid(
                    pilot, packet, D, params.ell, coeffs, a_grid
                )
                H_grid = correction_weights_grid * profile_grid
                dH = np.gradient(H_grid, a_grid, edge_order=2 if len(a_grid) >= 3 else 1)
                phi = np.exp(-0.5 * a_grid) * H_grid
                phi_derivative_density = np.exp(-0.5 * a_grid) * (dH - 0.5 * H_grid)
                variation_density = np.abs(phi_derivative_density)

                shift_a = np.array([float(sh.a) for sh in shifts], dtype=float)
                shift_weight = np.array([float(sh.weight) for sh in shifts], dtype=float)
                shift_H = np.array(
                    [
                        correction_weight(float(sh.a))
                        * packet_profile_value(pilot, packet, D, params.ell, coeffs, float(sh.a))
                        for sh in shifts
                    ],
                    dtype=float,
                )

                cell_rows: list[dict[str, Any]] = []
                for cell_idx, (cell_lo, cell_hi) in enumerate(zip(cell_edges[:-1], cell_edges[1:])):
                    if cell_idx == len(cell_edges) - 2:
                        grid_mask = (a_grid >= cell_lo) & (a_grid <= cell_hi)
                        shift_mask = (shift_a >= cell_lo) & (shift_a <= cell_hi)
                    else:
                        grid_mask = (a_grid >= cell_lo) & (a_grid < cell_hi)
                        shift_mask = (shift_a >= cell_lo) & (shift_a < cell_hi)
                    if np.count_nonzero(grid_mask) < 2:
                        continue
                    ag = a_grid[grid_mask]
                    Hg = H_grid[grid_mask]
                    phig = phi[grid_mask]
                    vg = variation_density[grid_mask]
                    pdg = phi_derivative_density[grid_mask]
                    eg = np.abs(psi_err[grid_mask])
                    pg = pnt_err[grid_mask]
                    continuum = float(np.trapezoid(np.exp(0.5 * ag) * Hg, ag))
                    prime = float(np.sum(shift_weight[shift_mask] * shift_H[shift_mask]))
                    residual = prime - continuum
                    exact_bound = float(np.trapezoid(eg * vg, ag))
                    pnt_bound = float(np.trapezoid(pg * vg, ag))
                    variation_x = float(np.trapezoid(vg, ag))
                    peak_idx = int(np.argmax(vg))
                    finite_U = finite_chebyshev_error_sup_on_cell(
                        float(cell_lo),
                        float(cell_hi),
                        staircase_shift_a,
                        staircase_cumulative,
                    )
                    sign_partition = sampled_sign_partition_variation(ag, phig, pdg)
                    finite_sup = float(finite_U["finite_sup_abs_psi_minus_x"])
                    grid_sup = float(np.max(eg))
                    cell_rows.append(
                        {
                            "cell_index": int(cell_idx),
                            "a_lo": finite_float(float(cell_lo)),
                            "a_hi": finite_float(float(cell_hi)),
                            "prime_shift_count": int(np.count_nonzero(shift_mask)),
                            "direct_prime_sum": finite_float(prime),
                            "direct_continuum": finite_float(continuum),
                            "direct_residual": finite_float(residual),
                            "exact_grid_variation_bound": finite_float(exact_bound),
                            "explicit_pnt_variation_bound": finite_float(pnt_bound),
                            "continuous_variation_x": finite_float(variation_x),
                            "variation_x": finite_float(variation_x),
                            "jump_variation_x": 0.0,
                            "exact_jump_bound": 0.0,
                            "pnt_jump_bound": 0.0,
                            "finite_exact_jump_bound": 0.0,
                            "finiteU_continuous_variation_bound": finite_float(finite_sup * variation_x),
                            "finiteU_with_exact_jumps_bound": finite_float(finite_sup * variation_x),
                            "finiteU_conservative_total_variation_bound": finite_float(
                                finite_sup * variation_x
                            ),
                            "max_abs_psi_minus_x": finite_float(grid_sup),
                            "grid_sup_abs_psi_minus_x": finite_float(grid_sup),
                            "finiteU_over_grid_sup_abs_psi_minus_x": ratio_or_none(
                                finite_sup, grid_sup
                            ),
                            "max_pnt_bound": finite_float(float(np.max(pg))),
                            "max_abs_H": finite_float(float(np.max(np.abs(Hg)))),
                            "sampled_phi_derivative_min": finite_float(float(np.min(pdg))),
                            "sampled_phi_derivative_max": finite_float(float(np.max(pdg))),
                            "sampled_phi_derivative_max_abs": finite_float(float(np.max(np.abs(pdg)))),
                            "sampled_phi_derivative_peak_a": finite_float(float(ag[peak_idx])),
                            "sampled_phi_derivative_sign_changes": int(
                                sampled_sign_change_count(pdg)
                            ),
                            **sign_partition,
                            **finite_U,
                        }
                    )

                jump_events = [
                    ("left_edge_jump", lo, -packet_profile_value(pilot, packet, D, params.ell, coeffs, lo)),
                    ("right_edge_jump", hi, packet_profile_value(pilot, packet, D, params.ell, coeffs, hi)),
                ]
                for jump_label, jump_a, jump_H in jump_events:
                    if not (0.0 <= jump_a <= effective_max_a):
                        continue
                    cell_index = min(
                        int(args.ledger_cells) - 1,
                        max(0, int(math.floor((jump_a / effective_max_a) * int(args.ledger_cells)))),
                    )
                    target_rows = [row for row in cell_rows if int(row["cell_index"]) == cell_index]
                    if not target_rows:
                        continue
                    row = target_rows[0]
                    jump_phi = math.exp(-0.5 * jump_a) * abs(float(jump_H))
                    exact_jump = abs(
                        chebyshev_psi_error_at(
                            jump_a,
                            staircase_shift_a,
                            staircase_cumulative,
                            side="right",
                        )
                    ) * jump_phi
                    pnt_jump = float(explicit_psi_error_bound(np.array([jump_a]))[0]) * jump_phi
                    finite_sup = float(row["finite_sup_abs_psi_minus_x"])
                    row["jump_variation_x"] = finite_float(float(row["jump_variation_x"]) + jump_phi)
                    row["exact_jump_bound"] = finite_float(float(row["exact_jump_bound"]) + exact_jump)
                    row["pnt_jump_bound"] = finite_float(float(row["pnt_jump_bound"]) + pnt_jump)
                    row["finite_exact_jump_bound"] = finite_float(
                        float(row["finite_exact_jump_bound"]) + exact_jump
                    )
                    row["exact_grid_variation_bound"] = finite_float(
                        float(row["exact_grid_variation_bound"]) + exact_jump
                    )
                    row["explicit_pnt_variation_bound"] = finite_float(
                        float(row["explicit_pnt_variation_bound"]) + pnt_jump
                    )
                    row["variation_x"] = finite_float(float(row["variation_x"]) + jump_phi)
                    row["finiteU_with_exact_jumps_bound"] = finite_float(
                        float(row["finiteU_with_exact_jumps_bound"]) + exact_jump
                    )
                    row["finiteU_conservative_total_variation_bound"] = finite_float(
                        float(row["finiteU_conservative_total_variation_bound"])
                        + finite_sup * jump_phi
                    )
                    row.setdefault("jump_labels", [])
                    row["jump_labels"].append(jump_label)

                for row in cell_rows:
                    abs_residual = abs(float(row["direct_residual"]))
                    exact_bound = float(row["exact_grid_variation_bound"])
                    pnt_bound = float(row["explicit_pnt_variation_bound"])
                    finiteU_bound = float(row["finiteU_with_exact_jumps_bound"])
                    finiteU_conservative = float(row["finiteU_conservative_total_variation_bound"])
                    row["abs_direct_residual"] = finite_float(abs_residual)
                    row["exact_bound_over_abs_cell_residual"] = (
                        None if abs_residual <= 0.0 else finite_float(exact_bound / abs_residual)
                    )
                    row["pnt_bound_over_abs_cell_residual"] = (
                        None if abs_residual <= 0.0 else finite_float(pnt_bound / abs_residual)
                    )
                    row["required_exact_multiplier_to_cover_cell_residual"] = ratio_or_none(
                        abs_residual, exact_bound
                    )
                    row["required_pnt_multiplier_to_cover_cell_residual"] = ratio_or_none(
                        abs_residual, pnt_bound
                    )
                    row["finiteU_bound_over_abs_cell_residual"] = (
                        None if abs_residual <= 0.0 else finite_float(finiteU_bound / abs_residual)
                    )
                    row["finiteU_conservative_bound_over_abs_cell_residual"] = (
                        None
                        if abs_residual <= 0.0
                        else finite_float(finiteU_conservative / abs_residual)
                    )
                    row["required_finiteU_multiplier_to_cover_cell_residual"] = ratio_or_none(
                        abs_residual, finiteU_bound
                    )
                    row["sampled_exact_cell_underbound"] = bool(abs_residual > exact_bound)
                    row["sampled_exact_cell_deficit"] = finite_float(
                        max(0.0, abs_residual - exact_bound)
                    )
                    row["finiteU_cell_underbound"] = bool(abs_residual > finiteU_bound)
                    row["finiteU_cell_deficit"] = finite_float(
                        max(0.0, abs_residual - finiteU_bound)
                    )
                    row["sampled_pnt_cell_underbound"] = bool(abs_residual > pnt_bound)
                    row["sampled_pnt_cell_deficit"] = finite_float(
                        max(0.0, abs_residual - pnt_bound)
                    )

                total_prime = float(sum(float(row["direct_prime_sum"]) for row in cell_rows))
                total_cont = float(sum(float(row["direct_continuum"]) for row in cell_rows))
                total_residual = total_prime - total_cont
                continuous_variation_sum = float(
                    sum(float(row["continuous_variation_x"]) for row in cell_rows)
                )
                jump_variation_sum = float(sum(float(row["jump_variation_x"]) for row in cell_rows))
                exact_integral_bound = float(sum(float(row["exact_grid_variation_bound"]) for row in cell_rows))
                pnt_integral_bound = float(sum(float(row["explicit_pnt_variation_bound"]) for row in cell_rows))
                finiteU_integral_bound = float(
                    sum(float(row["finiteU_with_exact_jumps_bound"]) for row in cell_rows)
                )
                finiteU_conservative_bound = float(
                    sum(float(row["finiteU_conservative_total_variation_bound"]) for row in cell_rows)
                )
                abs_cell_sum = float(sum(abs(float(row["direct_residual"])) for row in cell_rows))
                exact_cell_deficit = float(sum(float(row["sampled_exact_cell_deficit"]) for row in cell_rows))
                finiteU_cell_deficit = float(sum(float(row["finiteU_cell_deficit"]) for row in cell_rows))
                pnt_cell_deficit = float(sum(float(row["sampled_pnt_cell_deficit"]) for row in cell_rows))
                exact_underbound_count = sum(
                    1 for row in cell_rows if bool(row["sampled_exact_cell_underbound"])
                )
                finiteU_underbound_count = sum(
                    1 for row in cell_rows if bool(row["finiteU_cell_underbound"])
                )
                pnt_underbound_count = sum(
                    1 for row in cell_rows if bool(row["sampled_pnt_cell_underbound"])
                )
                sign_change_total = sum(
                    int(row["sampled_phi_derivative_sign_changes"]) for row in cell_rows
                )
                sign_change_cell_count = sum(
                    1 for row in cell_rows if int(row["sampled_phi_derivative_sign_changes"]) > 0
                )
                sign_partition_variation_sum = float(
                    sum(float(row["sampled_sign_partition_variation"]) for row in cell_rows)
                )
                sign_partition_break_count = sum(
                    int(row["sampled_sign_partition_break_count"]) for row in cell_rows
                )
                sign_partition_cells_with_breaks = sum(
                    1 for row in cell_rows if int(row["sampled_sign_partition_break_count"]) > 0
                )
                endpoint_contribution_exact = (
                    abs(float(psi_err[0])) * abs(float(phi[0]))
                    + abs(float(psi_err[-1])) * abs(float(phi[-1]))
                )
                endpoint_contribution_pnt = (
                    float(pnt_err[0]) * abs(float(phi[0]))
                    + float(pnt_err[-1]) * abs(float(phi[-1]))
                )
                exact_total_with_endpoints = exact_integral_bound + endpoint_contribution_exact
                pnt_total_with_endpoints = pnt_integral_bound + endpoint_contribution_pnt
                exact_values = [float(row["exact_grid_variation_bound"]) for row in cell_rows]
                abs_residual_values = [abs(float(row["direct_residual"])) for row in cell_rows]

                by_bound = sorted(
                    cell_rows,
                    key=lambda row: -float(row["exact_grid_variation_bound"]),
                )[: int(args.top_cells)]
                by_residual = sorted(
                    cell_rows,
                    key=lambda row: -abs(float(row["direct_residual"])),
                )[: int(args.top_cells)]
                by_required = sorted(
                    cell_rows,
                    key=lambda row: -(
                        float(row["required_exact_multiplier_to_cover_cell_residual"])
                        if row["required_exact_multiplier_to_cover_cell_residual"] is not None
                        else 0.0
                    ),
                )[: int(args.top_cells)]
                by_deficit = sorted(
                    cell_rows,
                    key=lambda row: -float(row["sampled_exact_cell_deficit"]),
                )[: int(args.top_cells)]
                by_finiteU_bound = sorted(
                    cell_rows,
                    key=lambda row: -float(row["finiteU_with_exact_jumps_bound"]),
                )[: int(args.top_cells)]
                by_finiteU_deficit = sorted(
                    cell_rows,
                    key=lambda row: -float(row["finiteU_cell_deficit"]),
                )[: int(args.top_cells)]
                by_continuous_variation = sorted(
                    cell_rows,
                    key=lambda row: -float(row["continuous_variation_x"]),
                )[: int(args.top_cells)]
                by_sign_changes = sorted(
                    cell_rows,
                    key=lambda row: -int(row["sampled_phi_derivative_sign_changes"]),
                )[: int(args.top_cells)]
                by_sign_partition_breaks = sorted(
                    cell_rows,
                    key=lambda row: -int(row["sampled_sign_partition_break_count"]),
                )[: int(args.top_cells)]
                by_sign_partition_variation = sorted(
                    cell_rows,
                    key=lambda row: -float(row["sampled_sign_partition_variation"]),
                )[: int(args.top_cells)]

                direction_rows.append(
                    {
                        "label": label,
                        "matrix_lambda": finite_float(float(eigs[idx])),
                        "ledger_total_prime_sum": finite_float(total_prime),
                        "ledger_total_continuum": finite_float(total_cont),
                        "ledger_total_residual": finite_float(total_residual),
                        "matrix_minus_ledger_abs_error": finite_float(
                            abs(float(eigs[idx]) - total_residual)
                        ),
                        "sum_abs_cell_residuals": finite_float(abs_cell_sum),
                        "cancellation_ratio_abs_total_over_sum_abs_cells": finite_float(
                            0.0 if abs_cell_sum == 0.0 else abs(total_residual) / abs_cell_sum
                        ),
                        "continuous_variation_x_sum": finite_float(continuous_variation_sum),
                        "jump_variation_x_sum": finite_float(jump_variation_sum),
                        "sampled_phi_derivative_sign_changes_total": int(sign_change_total),
                        "sampled_phi_derivative_sign_change_cell_count": int(
                            sign_change_cell_count
                        ),
                        "sampled_sign_partition_variation_sum": finite_float(
                            sign_partition_variation_sum
                        ),
                        "sampled_sign_partition_variation_over_continuous_sum": ratio_or_none(
                            sign_partition_variation_sum, continuous_variation_sum
                        ),
                        "sampled_sign_partition_break_count_sum": int(
                            sign_partition_break_count
                        ),
                        "sampled_sign_partition_cells_with_breaks": int(
                            sign_partition_cells_with_breaks
                        ),
                        "exact_integral_variation_bound": finite_float(exact_integral_bound),
                        "exact_endpoint_contribution": finite_float(endpoint_contribution_exact),
                        "exact_total_with_endpoints": finite_float(exact_total_with_endpoints),
                        "pnt_integral_variation_bound": finite_float(pnt_integral_bound),
                        "pnt_endpoint_contribution": finite_float(endpoint_contribution_pnt),
                        "pnt_total_with_endpoints": finite_float(pnt_total_with_endpoints),
                        "finiteU_with_exact_jumps_bound": finite_float(finiteU_integral_bound),
                        "finiteU_conservative_total_variation_bound": finite_float(
                            finiteU_conservative_bound
                        ),
                        "finiteU_bound_over_abs_residual": finite_float(
                            0.0 if total_residual == 0.0 else finiteU_integral_bound / abs(total_residual)
                        ),
                        "finiteU_conservative_bound_over_abs_residual": finite_float(
                            0.0 if total_residual == 0.0 else finiteU_conservative_bound / abs(total_residual)
                        ),
                        "finiteU_bound_over_exact_grid_bound": ratio_or_none(
                            finiteU_integral_bound, exact_total_with_endpoints
                        ),
                        "sampled_exact_underbound_cell_count": int(exact_underbound_count),
                        "finiteU_underbound_cell_count": int(finiteU_underbound_count),
                        "sampled_pnt_underbound_cell_count": int(pnt_underbound_count),
                        "sampled_exact_cell_deficit_sum": finite_float(exact_cell_deficit),
                        "finiteU_cell_deficit_sum": finite_float(finiteU_cell_deficit),
                        "sampled_pnt_cell_deficit_sum": finite_float(pnt_cell_deficit),
                        "sampled_exact_cell_bound_over_sum_abs_residuals": finite_float(
                            0.0 if abs_cell_sum == 0.0 else exact_integral_bound / abs_cell_sum
                        ),
                        "finiteU_bound_over_sum_abs_residuals": finite_float(
                            0.0 if abs_cell_sum == 0.0 else finiteU_integral_bound / abs_cell_sum
                        ),
                        "sampled_pnt_cell_bound_over_sum_abs_residuals": finite_float(
                            0.0 if abs_cell_sum == 0.0 else pnt_integral_bound / abs_cell_sum
                        ),
                        "required_uniform_exact_multiplier_to_cover_sum_abs_cells": ratio_or_none(
                            abs_cell_sum, exact_integral_bound
                        ),
                        "required_uniform_pnt_multiplier_to_cover_sum_abs_cells": ratio_or_none(
                            abs_cell_sum, pnt_integral_bound
                        ),
                        "required_uniform_finiteU_multiplier_to_cover_sum_abs_cells": ratio_or_none(
                            abs_cell_sum, finiteU_integral_bound
                        ),
                        "exact_bound_over_abs_residual": finite_float(
                            0.0 if total_residual == 0.0 else exact_total_with_endpoints / abs(total_residual)
                        ),
                        "pnt_bound_over_abs_residual": finite_float(
                            0.0 if total_residual == 0.0 else pnt_total_with_endpoints / abs(total_residual)
                        ),
                        "cells_for_50pct_exact_bound": int(capture_count(exact_values, 0.5)),
                        "cells_for_80pct_exact_bound": int(capture_count(exact_values, 0.8)),
                        "cells_for_95pct_exact_bound": int(capture_count(exact_values, 0.95)),
                        "cells_for_50pct_abs_residual": int(capture_count(abs_residual_values, 0.5)),
                        "cells_for_80pct_abs_residual": int(capture_count(abs_residual_values, 0.8)),
                        "cells_for_95pct_abs_residual": int(capture_count(abs_residual_values, 0.95)),
                        "top_cells_by_exact_bound": by_bound,
                        "top_cells_by_abs_residual": by_residual,
                        "top_cells_by_required_exact_multiplier": by_required,
                        "top_cells_by_sampled_exact_deficit": by_deficit,
                        "top_cells_by_finiteU_bound": by_finiteU_bound,
                        "top_cells_by_finiteU_deficit": by_finiteU_deficit,
                        "top_cells_by_continuous_variation": by_continuous_variation,
                        "top_cells_by_phi_derivative_sign_changes": by_sign_changes,
                        "top_cells_by_sign_partition_breaks": by_sign_partition_breaks,
                        "top_cells_by_sign_partition_variation": by_sign_partition_variation,
                    }
                )

            rows.append(
                {
                    "mode": "clvledger",
                    "K": finite_float(float(K)),
                    "schedule": args.schedule,
                    "ell": finite_float(float(ell)),
                    "grid_delta": finite_float(float(args.grid_delta)),
                    "k_spline": int(args.k_spline),
                    "p0_na": int(args.p0_na),
                    "quad_na": int(args.quad_na),
                    "ledger_cells": int(args.ledger_cells),
                    "receiver_delta": finite_float(float(receiver_delta)),
                    "raw_edge": [finite_float(lo), finite_float(hi)],
                    "max_a_effective": finite_float(effective_max_a),
                    "kerQ_dim": int(N.shape[1]),
                    "prime_power_shifts_total": int(len(shifts)),
                    "correction_eig_min": finite_float(float(eigs[0])),
                    "correction_eig_max": finite_float(float(eigs[-1])),
                    "correction_opnorm": finite_float(
                        max(abs(float(eigs[0])), abs(float(eigs[-1])))
                    ),
                    "directions": direction_rows,
                    "theorem_shape": (
                        "finite raw-a ledger for int phi d(psi-x), decomposing the exact-grid "
                        "Chebyshev staircase variation by cells"
                    ),
                    "D2": (
                        "raw a=r*log(p), x=exp(a), phi=x^(-1/2)E_delta(log x)F_v(log x), "
                        "cell ledger for sum Lambda(n)n^(-1/2)H(log n)-int exp(a/2)H(a)da"
                    ),
                }
            )
    return rows


def run_clvmesh(args: argparse.Namespace) -> list[dict[str, Any]]:
    groups: dict[tuple[float, float, float, str], dict[str, Any]] = {}
    for quad_na in args.quad_na_values:
        ledger_args = argparse.Namespace(**vars(args))
        ledger_args.quad_na = int(quad_na)
        ledger_args.top_cells = int(args.top_cells)
        ledger_args.func = run_clvledger
        for ledger_row in run_clvledger(ledger_args):
            for direction in ledger_row["directions"]:
                key = (
                    float(ledger_row["K"]),
                    float(ledger_row["receiver_delta"]),
                    float(ledger_row["ell"]),
                    str(direction["label"]),
                )
                group = groups.setdefault(
                    key,
                    {
                        "mode": "clvmesh",
                        "K": ledger_row["K"],
                        "schedule": ledger_row["schedule"],
                        "ell": ledger_row["ell"],
                        "grid_delta": ledger_row["grid_delta"],
                        "k_spline": ledger_row["k_spline"],
                        "p0_na": ledger_row["p0_na"],
                        "ledger_cells": ledger_row["ledger_cells"],
                        "receiver_delta": ledger_row["receiver_delta"],
                        "raw_edge": ledger_row["raw_edge"],
                        "max_a_effective": ledger_row["max_a_effective"],
                        "kerQ_dim": ledger_row["kerQ_dim"],
                        "prime_power_shifts_total": ledger_row["prime_power_shifts_total"],
                        "direction": direction["label"],
                        "mesh_rows": [],
                        "D2": (
                            "raw a=r*log(p), x=exp(a); mesh audit varies quad_na for the "
                            "Stieltjes ledger of phi=x^(-1/2)E_delta(log x)F_v(log x)"
                        ),
                    },
                )
                group["mesh_rows"].append(
                    {
                        "quad_na": int(quad_na),
                        "matrix_lambda": direction["matrix_lambda"],
                        "ledger_total_residual": direction["ledger_total_residual"],
                        "matrix_minus_ledger_abs_error": direction["matrix_minus_ledger_abs_error"],
                        "exact_integral_variation_bound": direction["exact_integral_variation_bound"],
                        "exact_total_with_endpoints": direction["exact_total_with_endpoints"],
                        "exact_bound_over_abs_residual": direction["exact_bound_over_abs_residual"],
                        "continuous_variation_x_sum": direction["continuous_variation_x_sum"],
                        "jump_variation_x_sum": direction["jump_variation_x_sum"],
                        "sampled_phi_derivative_sign_changes_total": direction[
                            "sampled_phi_derivative_sign_changes_total"
                        ],
                        "sampled_phi_derivative_sign_change_cell_count": direction[
                            "sampled_phi_derivative_sign_change_cell_count"
                        ],
                        "sampled_sign_partition_variation_sum": direction[
                            "sampled_sign_partition_variation_sum"
                        ],
                        "sampled_sign_partition_variation_over_continuous_sum": direction[
                            "sampled_sign_partition_variation_over_continuous_sum"
                        ],
                        "sampled_sign_partition_break_count_sum": direction[
                            "sampled_sign_partition_break_count_sum"
                        ],
                        "sampled_sign_partition_cells_with_breaks": direction[
                            "sampled_sign_partition_cells_with_breaks"
                        ],
                        "finiteU_with_exact_jumps_bound": direction[
                            "finiteU_with_exact_jumps_bound"
                        ],
                        "finiteU_bound_over_abs_residual": direction[
                            "finiteU_bound_over_abs_residual"
                        ],
                        "finiteU_bound_over_exact_grid_bound": direction[
                            "finiteU_bound_over_exact_grid_bound"
                        ],
                        "sampled_exact_underbound_cell_count": direction[
                            "sampled_exact_underbound_cell_count"
                        ],
                        "finiteU_underbound_cell_count": direction["finiteU_underbound_cell_count"],
                        "sampled_exact_cell_deficit_sum": direction["sampled_exact_cell_deficit_sum"],
                        "finiteU_cell_deficit_sum": direction["finiteU_cell_deficit_sum"],
                        "required_uniform_exact_multiplier_to_cover_sum_abs_cells": direction[
                            "required_uniform_exact_multiplier_to_cover_sum_abs_cells"
                        ],
                        "required_uniform_finiteU_multiplier_to_cover_sum_abs_cells": direction[
                            "required_uniform_finiteU_multiplier_to_cover_sum_abs_cells"
                        ],
                    }
                )

    rows: list[dict[str, Any]] = []
    for group in groups.values():
        mesh_rows = sorted(group["mesh_rows"], key=lambda row: int(row["quad_na"]))
        group["mesh_rows"] = mesh_rows
        covering = [
            row for row in mesh_rows if float(row["exact_bound_over_abs_residual"]) >= 1.0
        ]
        group["first_quad_na_covering_total_residual"] = (
            None if not covering else int(covering[0]["quad_na"])
        )
        if len(mesh_rows) >= 2:
            prev = mesh_rows[-2]
            last = mesh_rows[-1]
            group["last_mesh_residual_abs_delta"] = finite_float(
                abs(float(last["ledger_total_residual"]) - float(prev["ledger_total_residual"]))
            )
            group["last_mesh_exact_total_abs_delta"] = finite_float(
                abs(float(last["exact_total_with_endpoints"]) - float(prev["exact_total_with_endpoints"]))
            )
        else:
            group["last_mesh_residual_abs_delta"] = None
            group["last_mesh_exact_total_abs_delta"] = None
        group["mesh_interpretation"] = (
            "global Stieltjes coverage is judged by exact_bound_over_abs_residual; "
            "cell residual ratios remain worklist heuristics because cell endpoint "
            "terms cancel only before taking absolute values"
        )
        rows.append(group)
    return rows


def run_clvsigncert(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        ell = stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        lo, hi = 2.0 * float(K), 4.0 * float(K)
        for receiver_delta in args.receiver_delta:
            ctx = build_packet_context(
                pilot,
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
            )
            params = ctx["params"]
            packet = ctx["packet"]
            D = ctx["D"]
            N = ctx["N"]
            Gc = ctx["Gc"]
            effective_max_a = effective_shift_cutoff(D, params.ell)
            shift_params = pilot.PilotParams(
                L=0.5 * effective_max_a,
                ell=params.ell,
                delta=params.delta,
                k_spline=params.k_spline,
                p0_na=int(args.p0_na),
            )
            shifts = pilot.prime_power_shifts(shift_params.L)
            staircase_shift_a, staircase_cumulative = chebyshev_staircase_arrays(shifts)

            def chi_weight(a: float) -> float:
                return 1.0 if lo <= a <= hi else 0.0

            def plus_weight(a: float) -> float:
                return float(
                    selberg_interval_values(
                        np.array([a]),
                        lo=lo,
                        hi=hi,
                        receiver_delta=float(receiver_delta),
                        sign="plus",
                    )[0]
                )

            def correction_weight(a: float) -> float:
                return plus_weight(a) - chi_weight(a)

            def correction_weight_derivatives_grid(
                a_values: np.ndarray,
            ) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
                values, first, second = selberg_interval_plus_derivatives(
                    a_values,
                    lo=lo,
                    hi=hi,
                    receiver_delta=float(receiver_delta),
                )
                chi_values = np.where((lo <= a_values) & (a_values <= hi), 1.0, 0.0)
                return values - chi_values, first, second

            def receiver_node_audit_grid(a_values: np.ndarray) -> dict[str, Any]:
                return selberg_receiver_node_audit(
                    a_values,
                    lo=lo,
                    hi=hi,
                    receiver_delta=float(receiver_delta),
                )

            P_edge = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, chi_weight
            )
            P_plus = build_prime_matrix_for_weight(
                pilot, packet, D, params.ell, shifts, plus_weight
            )
            P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, int(args.p0_na))
            P0_plus = build_continuum_matrix_for_weight(
                pilot,
                packet,
                D,
                params.ell,
                max_a=effective_max_a,
                p0_na=int(args.p0_na),
                weight_fn=plus_weight,
            )
            correction = pilot.sym((P_plus - P_edge) - (P0_plus - P0_edge))
            A_corr = generalized_to_standard(pilot, project_matrix(pilot, correction, N), Gc)
            eigs, evecs = np.linalg.eigh(A_corr)
            op_idx = int(np.argmax(np.abs(eigs)))
            if args.directions == "all":
                directions = [
                    ("lower", 0),
                    ("upper", len(eigs) - 1),
                    ("opnorm", op_idx),
                ]
            else:
                directions = [("opnorm", op_idx)]

            cell_edges = np.linspace(0.0, effective_max_a, int(args.ledger_cells) + 1)
            direction_rows: list[dict[str, Any]] = []
            for label, idx in directions:
                y = evecs[:, idx]
                coeffs = standardized_eigenvector_to_full_coeffs(Gc, N, y)
                cell_rows: list[dict[str, Any]] = []
                for cell_idx in args.cells:
                    if int(cell_idx) < 0 or int(cell_idx) >= int(args.ledger_cells):
                        cell_rows.append(
                            {
                                "cell_index": int(cell_idx),
                                "status": "invalid_cell_index",
                            }
                        )
                        continue
                    cell_lo = float(cell_edges[int(cell_idx)])
                    cell_hi = float(cell_edges[int(cell_idx) + 1])
                    segments, jumps = split_cell_at_edge_jumps(
                        cell_lo,
                        cell_hi,
                        edge_lo=lo,
                        edge_hi=hi,
                        sample_count=int(args.cert_na),
                    )
                    smooth_segments = [
                        smooth_segment_sign_candidate(
                            pilot,
                            packet,
                            D,
                            params.ell,
                            coeffs,
                            seg_lo=seg_lo,
                            seg_hi=seg_hi,
                            correction_weight=correction_weight,
                            correction_weight_derivatives=correction_weight_derivatives_grid,
                            receiver_node_audit=receiver_node_audit_grid,
                            interval_safety_factors=args.interval_safety_factors,
                            sample_count=int(args.cert_na),
                        )
                        for seg_lo, seg_hi in segments
                    ]
                    jump_terms: list[dict[str, Any]] = []
                    for jump_label, jump_a in jumps:
                        profile_at_jump = packet_profile_value(
                            pilot, packet, D, params.ell, coeffs, float(jump_a)
                        )
                        jump_H = -profile_at_jump if jump_label == "left_edge_jump" else profile_at_jump
                        jump_phi = math.exp(-0.5 * float(jump_a)) * abs(float(jump_H))
                        psi_left = chebyshev_psi_error_at(
                            float(jump_a),
                            staircase_shift_a,
                            staircase_cumulative,
                            side="left",
                        )
                        psi_right = chebyshev_psi_error_at(
                            float(jump_a),
                            staircase_shift_a,
                            staircase_cumulative,
                            side="right",
                        )
                        jump_terms.append(
                            {
                                "label": jump_label,
                                "a": finite_float(float(jump_a)),
                                "profile_at_jump": finite_float(profile_at_jump),
                                "delta_H": finite_float(float(jump_H)),
                                "jump_variation_x": finite_float(jump_phi),
                                "psi_error_left": finite_float(float(psi_left)),
                                "psi_error_right": finite_float(float(psi_right)),
                                "exact_jump_bound_left": finite_float(
                                    abs(float(psi_left)) * jump_phi
                                ),
                                "exact_jump_bound_right": finite_float(
                                    abs(float(psi_right)) * jump_phi
                                ),
                                "finite_jump_bound": finite_float(
                                    max(abs(float(psi_left)), abs(float(psi_right))) * jump_phi
                                ),
                            }
                        )

                    finite_U = finite_chebyshev_error_sup_on_cell(
                        cell_lo,
                        cell_hi,
                        staircase_shift_a,
                        staircase_cumulative,
                    )
                    finite_sup = float(finite_U["finite_sup_abs_psi_minus_x"])
                    smooth_endpoint_variation = float(
                        sum(float(seg.get("endpoint_variation_x", 0.0)) for seg in smooth_segments)
                    )
                    smooth_continuous_variation = float(
                        sum(float(seg.get("continuous_variation_x", 0.0)) for seg in smooth_segments)
                    )
                    smooth_partition_variation = float(
                        sum(
                            float(seg.get("sampled_sign_partition_variation", 0.0))
                            for seg in smooth_segments
                        )
                    )
                    jump_variation = float(
                        sum(float(jump["jump_variation_x"]) for jump in jump_terms)
                    )
                    finite_jump_bound = float(
                        sum(float(jump["finite_jump_bound"]) for jump in jump_terms)
                    )
                    stable_segments = sum(
                        1
                        for seg in smooth_segments
                        if seg.get("status") == "sampled_sign_stable_candidate"
                    )
                    weak_segments = sum(
                        1
                        for seg in smooth_segments
                        if seg.get("status") == "sampled_sign_stable_but_guard_weak"
                    )
                    root_segments = sum(
                        1 for seg in smooth_segments if seg.get("status") == "needs_root_isolation"
                    )
                    if root_segments > 0:
                        recommendation = "isolate_roots_then_sign_certify"
                    elif weak_segments > 0:
                        recommendation = "tighten_lipschitz_or_refine_mesh"
                    elif jump_terms:
                        recommendation = "smooth_sign_cert_plus_explicit_jump_cert"
                    else:
                        recommendation = "smooth_sign_cert_candidate"
                    node_distances = [
                        float(seg["receiver_node_audit"]["min_distance_to_any_vaaler_integer"])
                        for seg in smooth_segments
                        if "receiver_node_audit" in seg and seg["receiver_node_audit"]
                    ]
                    node_treatment_count = sum(
                        1
                        for seg in smooth_segments
                        if seg.get("receiver_node_audit", {}).get("needs_local_node_treatment")
                    )
                    h0_prime_cancel_ratios: list[float] = []
                    h0_second_cancel_ratios: list[float] = []
                    non_node_candidate_multipliers: list[float] = []
                    non_node_candidate_slacks: list[float] = []
                    non_node_candidate_count = 0
                    non_node_stress_passed_sets: list[set[float]] = []
                    for seg in smooth_segments:
                        audit = seg.get("receiver_node_audit", {})
                        for axis_key in ["left_axis", "right_axis"]:
                            axis = audit.get(axis_key, {})
                            h0_cancel = axis.get("H0_cancellation", {})
                            h0p = h0_cancel.get("H0_prime", {}).get("max_cancellation_ratio")
                            h0pp = h0_cancel.get("H0_second", {}).get("max_cancellation_ratio")
                            if h0p is not None and math.isfinite(float(h0p)):
                                h0_prime_cancel_ratios.append(float(h0p))
                            if h0pp is not None and math.isfinite(float(h0pp)):
                                h0_second_cancel_ratios.append(float(h0pp))
                        non_node_candidate = seg.get("non_node_interval_candidate", {})
                        if non_node_candidate.get("status") == "candidate":
                            non_node_candidate_count += 1
                            multiplier = non_node_candidate.get("allowable_LS_multiplier")
                            slack = non_node_candidate.get("allowable_LS_multiplier_slack")
                            if multiplier is not None and math.isfinite(float(multiplier)):
                                non_node_candidate_multipliers.append(float(multiplier))
                            if slack is not None and math.isfinite(float(slack)):
                                non_node_candidate_slacks.append(float(slack))
                            stress = non_node_candidate.get("interval_safety_stress", {})
                            passed = {
                                float(row["factor"])
                                for row in stress.get("stress_factors", [])
                                if bool(row.get("passes"))
                            }
                            non_node_stress_passed_sets.append(passed)
                    if non_node_stress_passed_sets:
                        common_stress_passed = sorted(
                            set.intersection(*non_node_stress_passed_sets)
                        )
                    else:
                        common_stress_passed = []
                    cell_rows.append(
                        {
                            "cell_index": int(cell_idx),
                            "a_lo": finite_float(cell_lo),
                            "a_hi": finite_float(cell_hi),
                            "smooth_segment_count": int(len(smooth_segments)),
                            "jump_count": int(len(jump_terms)),
                            "sampled_sign_stable_segment_count": int(stable_segments),
                            "sampled_sign_weak_segment_count": int(weak_segments),
                            "needs_root_isolation_segment_count": int(root_segments),
                            "receiver_node_treatment_segment_count": int(
                                node_treatment_count
                            ),
                            "receiver_min_distance_to_vaaler_integer": None
                            if not node_distances
                            else finite_float(min(node_distances)),
                            "receiver_H0_prime_max_cancellation_ratio": None
                            if not h0_prime_cancel_ratios
                            else finite_float(max(h0_prime_cancel_ratios)),
                            "receiver_H0_second_max_cancellation_ratio": None
                            if not h0_second_cancel_ratios
                            else finite_float(max(h0_second_cancel_ratios)),
                            "non_node_interval_candidate_segment_count": int(
                                non_node_candidate_count
                            ),
                            "non_node_min_allowable_LS_multiplier": None
                            if not non_node_candidate_multipliers
                            else finite_float(min(non_node_candidate_multipliers)),
                            "non_node_min_allowable_LS_multiplier_slack": None
                            if not non_node_candidate_slacks
                            else finite_float(min(non_node_candidate_slacks)),
                            "non_node_interval_common_passing_safety_factors": [
                                finite_float(factor) for factor in common_stress_passed
                            ],
                            "non_node_interval_largest_common_passing_safety_factor": None
                            if not common_stress_passed
                            else finite_float(max(common_stress_passed)),
                            "smooth_continuous_variation_x": finite_float(
                                smooth_continuous_variation
                            ),
                            "smooth_endpoint_variation_x": finite_float(
                                smooth_endpoint_variation
                            ),
                            "smooth_partition_variation_x": finite_float(
                                smooth_partition_variation
                            ),
                            "smooth_endpoint_over_continuous": ratio_or_none(
                                smooth_endpoint_variation, smooth_continuous_variation
                            ),
                            "smooth_partition_over_continuous": ratio_or_none(
                                smooth_partition_variation, smooth_continuous_variation
                            ),
                            "jump_variation_x": finite_float(jump_variation),
                            "finiteU_smooth_endpoint_bound": finite_float(
                                finite_sup * smooth_endpoint_variation
                            ),
                            "finiteU_smooth_partition_bound": finite_float(
                                finite_sup * smooth_partition_variation
                            ),
                            "finite_jump_bound": finite_float(finite_jump_bound),
                            "finiteU_endpoint_plus_jump_candidate_bound": finite_float(
                                finite_sup * smooth_endpoint_variation + finite_jump_bound
                            ),
                            "finiteU_partition_plus_jump_candidate_bound": finite_float(
                                finite_sup * smooth_partition_variation + finite_jump_bound
                            ),
                            "recommendation": recommendation,
                            "proof_status": (
                                "diagnostic_only: packet-profile derivatives use analytic centered "
                                "B-spline formulas and Selberg receiver derivatives use analytic "
                                "Vaaler/polygamma formulas, but sign guards are still sampled "
                                "and are not interval proof certificates"
                            ),
                            "smooth_segments": smooth_segments,
                            "jump_terms": jump_terms,
                            **finite_U,
                        }
                    )
                direction_rows.append(
                    {
                        "label": label,
                        "matrix_lambda": finite_float(float(eigs[idx])),
                        "cells": cell_rows,
                    }
                )

            rows.append(
                {
                    "mode": "clvsigncert",
                    "K": finite_float(float(K)),
                    "schedule": args.schedule,
                    "ell": finite_float(float(ell)),
                    "grid_delta": finite_float(float(args.grid_delta)),
                    "k_spline": int(args.k_spline),
                    "p0_na": int(args.p0_na),
                    "ledger_cells": int(args.ledger_cells),
                    "cert_na": int(args.cert_na),
                    "receiver_delta": finite_float(float(receiver_delta)),
                    "raw_edge": [finite_float(lo), finite_float(hi)],
                    "max_a_effective": finite_float(effective_max_a),
                    "kerQ_dim": int(N.shape[1]),
                    "prime_power_shifts_total": int(len(shifts)),
                    "correction_eig_min": finite_float(float(eigs[0])),
                    "correction_eig_max": finite_float(float(eigs[-1])),
                    "correction_opnorm": finite_float(
                        max(abs(float(eigs[0])), abs(float(eigs[-1])))
                    ),
                    "directions": direction_rows,
                    "theorem_shape": (
                        "prototype V_J certificate worklist: split edge jumps, then certify "
                        "sign of H_v'(a)-H_v(a)/2 on smooth raw-a subsegments; packet-profile "
                        "derivatives are analytic centered B-spline derivatives and receiver "
                        "derivatives are analytic Vaaler/polygamma derivatives"
                    ),
                    "D2": (
                        "raw a=r*log(p), x=exp(a), phi=x^(-1/2)E_delta(log x)F_v(log x); "
                        "Q3 xi=a/(2*pi), w_Q(n)=2*Lambda(n)/sqrt(n)"
                    ),
                }
            )
    return rows


def hat_r_ell(u: np.ndarray, *, ell: float, packet: Any) -> np.ndarray:
    return (ell / (packet.s_k * packet.c_k)) * np.sinc(ell * u / packet.s_k) ** (
        2 * packet.k_spline + 2
    )


def run_lowband(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    packet = pilot.SplinePacket.build(args.k_spline)
    rows: list[dict[str, Any]] = []
    for K in args.K:
        sigma = 1.0 / (12.0 * K)
        u = np.linspace(-sigma, sigma, args.band_nt)
        vals = hat_r_ell(u, ell=args.ell, packet=packet)
        mass = float(np.trapezoid(vals, u))
        rows.append(
            {
                "mode": "lowband",
                "K": finite_float(K),
                "sigma": finite_float(sigma),
                "ell": finite_float(args.ell),
                "k_spline": int(args.k_spline),
                "s_k": finite_float(packet.s_k),
                "c_k": finite_float(packet.c_k),
                "hat_r_ell_0": finite_float(hat_r_ell(np.array([0.0]), ell=args.ell, packet=packet)[0]),
                "band_mass": finite_float(mass),
                "total_mass_exact": 1.0,
                "band_nt": int(args.band_nt),
                "D2": "raw low-band survivor |u|<1/(12K) for edge=[2K,4K]",
            }
        )
    return rows


def gaussian_W(a: float, K: float) -> float:
    return math.exp(4.0 * math.pi) * math.exp(-math.pi * (a / (2.0 * K)) ** 2)


def hat_chi_sym(u: np.ndarray, lo: float, hi: float) -> np.ndarray:
    out = np.empty_like(u, dtype=float)
    small = np.abs(u) < 1e-14
    out[small] = 2.0 * (hi - lo)
    us = u[~small]
    out[~small] = (np.sin(2.0 * math.pi * hi * us) - np.sin(2.0 * math.pi * lo * us)) / (
        math.pi * us
    )
    return out


def gaussian_fourier_error_scan(K: float, *, u_nt: int) -> dict[str, Any]:
    lo, hi = 2.0 * K, 4.0 * K
    u_max = 2.0 / K
    u = np.linspace(0.0, u_max, u_nt)
    hat_W = math.exp(4.0 * math.pi) * (2.0 * K) * np.exp(-math.pi * (2.0 * K * u) ** 2)
    err = hat_W - hat_chi_sym(u, lo, hi)
    neg = np.flatnonzero(err < -1e-10)
    min_idx = int(np.argmin(err))
    return {
        "u_scan_max": finite_float(u_max),
        "u_scan_nt": int(u_nt),
        "first_negative_u": None if len(neg) == 0 else finite_float(u[int(neg[0])]),
        "min_u": finite_float(u[min_idx]),
        "min_hat_error": finite_float(err[min_idx]),
    }


def run_gaussian(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        lo, hi = 2.0 * K, 4.0 * K
        max_a_requested = args.max_a_factor * K
        max_a = max_a_requested
        ctx = build_packet_context(
            pilot,
            K=K,
            ell=args.ell,
            grid_delta=args.grid_delta,
            k_spline=args.k_spline,
            p0_na=3,
        )
        params = ctx["params"]
        packet = ctx["packet"]
        D = ctx["D"]
        N = ctx["N"]
        Gc = ctx["Gc"]

        shift_params = pilot.PilotParams(
            L=0.5 * max_a,
            ell=params.ell,
            delta=params.delta,
            k_spline=params.k_spline,
            p0_na=3,
        )
        shifts = pilot.prime_power_shifts(shift_params.L)
        P_diff = np.zeros_like(D, dtype=float)
        edge_count = 0
        for sh in shifts:
            in_edge = lo <= sh.a <= hi
            if in_edge:
                edge_count += 1
            coeff = gaussian_W(sh.a, K) - (1.0 if in_edge else 0.0)
            P_diff += sh.weight * coeff * shifted_packet_matrix(pilot, packet, D, params.ell, sh.a)

        eigs = projected_generalized_eigs(pilot, pilot.sym(P_diff), N, Gc)
        row = {
            "mode": "gaussian",
            "K": finite_float(K),
            "raw_edge": [finite_float(lo), finite_float(hi)],
            "max_a": finite_float(max_a),
            "max_a_factor": finite_float(args.max_a_factor),
            "ell": finite_float(params.ell),
            "grid_delta": finite_float(params.delta),
            "k_spline": int(params.k_spline),
            "n_centers": int(len(ctx["u"])),
            "kerQ_dim": int(N.shape[1]),
            "prime_power_shifts_total": int(len(shifts)),
            "edge_prime_power_shifts": int(edge_count),
            "W0": finite_float(gaussian_W(0.0, K)),
            "W_4K": finite_float(gaussian_W(4.0 * K, K)),
            "eig_G_min_PW_minus_Pedge": finite_float(eigs[0]),
            "eig_G_max_PW_minus_Pedge": finite_float(eigs[-1]),
            "D2": "raw a=r*log(p), W_K(a)=exp(4*pi)exp(-pi*(a/(2K))^2)",
        }
        row.update(gaussian_fourier_error_scan(K, u_nt=args.u_nt))
        rows.append(row)
    return rows


def gaussian_bump(a: float, *, width: float) -> float:
    if width <= 0:
        raise ValueError("width must be positive")
    return math.exp(-math.pi * (a / width) ** 2)


def two_point_gaussian_lift_value(a: float, *, center: float, width: float) -> float:
    """Autocorrelation of two equal Gaussian packets separated by `center`.

    Up to an irrelevant positive scale this has the form
      2 G_width(a) + G_width(a-center) + G_width(a+center).

    It is a positive-definite even function because it is an autocorrelation.
    """
    return (
        2.0 * gaussian_bump(a, width=width)
        + gaussian_bump(a - center, width=width)
        + gaussian_bump(a + center, width=width)
    )


def signed_packet_gaussian_lift_value(
    a: float,
    *,
    positions: list[float],
    coefficients: list[float],
    width: float,
) -> float:
    """Autocorrelation of a signed Gaussian packet.

    The Fourier transform is a positive Gaussian factor times
      |sum_j coefficients[j] * exp(-2*pi*i*u*positions[j])|^2,
    so every generated scalar lift is positive-definite.  The lift may be
    pointwise signed in raw-log space; that is the point of this B2b probe.
    """
    if len(positions) != len(coefficients):
        raise ValueError("positions and coefficients must have the same length")
    total = 0.0
    for ti, ai in zip(positions, coefficients):
        for tj, aj in zip(positions, coefficients):
            total += ai * aj * gaussian_bump(a - (ti - tj), width=width)
    return total


def normalized_coefficients(raw: list[float]) -> list[float]:
    norm = math.sqrt(sum(float(x) * float(x) for x in raw))
    if norm <= 0.0:
        raise ValueError("coefficient pattern has zero l2 norm")
    return [float(x) / norm for x in raw]


def signed_triplet_patterns() -> list[tuple[str, list[float], bool]]:
    """Small signed/multi-packet dictionary for the cost-wall probe.

    The `normalize` flag makes the signed triplets report one unit of diagonal
    self-correlation; the all-positive triplet is left unnormalized so that the
    probe also tests whether more adjacent pairs improve the zero-cost ratio.
    """
    return [
        ("triplet_plus_raw", [1.0, 1.0, 1.0], False),
        ("triplet_soft_notch_l2", [1.0, -0.25, 1.0], True),
        ("triplet_notch_l2", [1.0, -0.5, 1.0], True),
        ("triplet_alt_l2", [1.0, -1.0, 1.0], True),
        ("triplet_second_diff_l2", [1.0, -2.0, 1.0], True),
    ]


def build_lift_basis_specs(
    *,
    lift_family: str,
    centers: list[float],
    widths: list[float],
) -> list[dict[str, Any]]:
    specs: list[dict[str, Any]] = []

    if lift_family in {"two-point", "all"}:
        for center in centers:
            for width in widths:
                specs.append(
                    {
                        "family": "two-point",
                        "center": finite_float(center),
                        "width": finite_float(width),
                    }
                )

    if lift_family in {"signed-triplet", "all"}:
        patterns = signed_triplet_patterns()
        for center in centers:
            positions = [0.0, 0.5 * float(center), float(center)]
            for width in widths:
                for label, raw_coeffs, normalize in patterns:
                    coefficients = (
                        normalized_coefficients(raw_coeffs) if normalize else list(raw_coeffs)
                    )
                    specs.append(
                        {
                            "family": "signed-triplet",
                            "pattern": label,
                            "center": finite_float(center),
                            "width": finite_float(width),
                            "positions": [finite_float(x) for x in positions],
                            "coefficients": [finite_float(x) for x in coefficients],
                            "coeff_l2_sq": finite_float(
                                sum(float(x) * float(x) for x in coefficients)
                            ),
                        }
                    )

    if not specs:
        raise ValueError(f"unknown or empty lift family: {lift_family}")
    return specs


def lift_spec_value(a: float, spec: dict[str, Any]) -> float:
    family = spec["family"]
    if family == "two-point":
        return two_point_gaussian_lift_value(
            a,
            center=float(spec["center"]),
            width=float(spec["width"]),
        )
    if family == "signed-triplet":
        return signed_packet_gaussian_lift_value(
            a,
            positions=[float(x) for x in spec["positions"]],
            coefficients=[float(x) for x in spec["coefficients"]],
            width=float(spec["width"]),
        )
    raise ValueError(f"unknown lift spec family: {family}")


def default_lift_centers(K: float, n: int) -> list[float]:
    lo, hi = 2.0 * K, 4.0 * K
    if n <= 1:
        return [0.5 * (lo + hi)]
    return np.linspace(lo, hi, n).tolist()


def parse_float_list_or_default(raw: list[float] | None, default: list[float]) -> list[float]:
    return default if raw is None or len(raw) == 0 else [float(x) for x in raw]


def cutting_plane_lift_lp(
    *,
    A_edge: np.ndarray,
    A_basis: list[np.ndarray],
    coeff_budget: float,
    coeff_bound: float,
    eta_lower: float,
    eta_upper: float,
    max_iter: int,
    tol: float,
) -> dict[str, Any]:
    dim = A_edge.shape[0]
    n_basis = len(A_basis)
    if n_basis == 0:
        raise ValueError("liftsearch needs at least one basis matrix")

    # Start with enough directions to see the current edge operator.
    dirs: list[np.ndarray] = []
    edge_evals, edge_evecs = np.linalg.eigh(A_edge)
    for j in range(dim):
        dirs.append(np.eye(dim)[:, j])
        dirs.append(edge_evecs[:, j])

    c_obj = np.zeros(n_basis + 1)
    c_obj[-1] = 1.0
    bounds = [(0.0, coeff_bound) for _ in range(n_basis)] + [(eta_lower, eta_upper)]

    result = None
    min_eval = float("nan")
    worst_vec = None
    coeffs = np.zeros(n_basis)
    eta = eta_upper
    iterations = 0

    for iterations in range(1, max_iter + 1):
        a_ub: list[list[float]] = []
        b_ub: list[float] = []

        # Coefficient budget: sum c_m <= budget.
        a_ub.append([1.0] * n_basis + [0.0])
        b_ub.append(coeff_budget)

        # Directional PSD cuts:
        #   sum c_m <A_m x,x> + eta >= <A_edge x,x>.
        for x in dirs:
            x = x / np.linalg.norm(x)
            row = [-float(x @ A @ x) for A in A_basis] + [-1.0]
            rhs = -float(x @ A_edge @ x)
            a_ub.append(row)
            b_ub.append(rhs)

        result = linprog(
            c_obj,
            A_ub=np.array(a_ub, dtype=float),
            b_ub=np.array(b_ub, dtype=float),
            bounds=bounds,
            method="highs",
        )
        if not result.success:
            break

        coeffs = np.array(result.x[:n_basis], dtype=float)
        eta = float(result.x[-1])
        slack = -A_edge + eta * np.eye(dim)
        for c, A in zip(coeffs, A_basis):
            slack += c * A
        evals, evecs = np.linalg.eigh(0.5 * (slack + slack.T))
        min_eval = float(evals[0])
        worst_vec = evecs[:, 0]
        if min_eval >= -tol:
            break
        dirs.append(worst_vec)

    return {
        "success": bool(result is not None and result.success and min_eval >= -tol),
        "linprog_success": bool(result is not None and result.success),
        "linprog_message": None if result is None else str(result.message),
        "iterations": int(iterations),
        "num_cuts": int(len(dirs)),
        "coefficients": coeffs,
        "eta": finite_float(eta),
        "min_slack_eig": finite_float(min_eval),
    }


def cutting_plane_lift_cost_lp(
    *,
    A_edge: np.ndarray,
    A_basis: list[np.ndarray],
    C_edge: np.ndarray,
    C_basis: list[np.ndarray],
    coeff_budget: float,
    coeff_bound: float,
    eta_lower: float,
    eta_upper: float,
    gamma_lower: float,
    gamma_upper: float,
    eta_weight: float,
    cost_weight: float,
    max_iter: int,
    tol: float,
) -> dict[str, Any]:
    dim = A_edge.shape[0]
    n_basis = len(A_basis)
    if n_basis == 0 or len(C_basis) != n_basis:
        raise ValueError("cost liftsearch needs matching prime and continuum bases")

    prime_dirs: list[np.ndarray] = []
    cost_dirs: list[np.ndarray] = []
    edge_evals, edge_evecs = np.linalg.eigh(A_edge)
    cost_evals, cost_evecs = np.linalg.eigh(C_edge)
    for j in range(dim):
        basis_vec = np.eye(dim)[:, j]
        prime_dirs.append(basis_vec)
        cost_dirs.append(basis_vec)
        prime_dirs.append(edge_evecs[:, j])
        cost_dirs.append(cost_evecs[:, j])

    c_obj = np.zeros(n_basis + 2)
    c_obj[-2] = eta_weight
    c_obj[-1] = cost_weight
    bounds = (
        [(0.0, coeff_bound) for _ in range(n_basis)]
        + [(eta_lower, eta_upper), (gamma_lower, gamma_upper)]
    )

    result = None
    coeffs = np.zeros(n_basis)
    eta = eta_upper
    gamma = gamma_upper
    min_prime_slack = float("nan")
    max_cost_eig = float("nan")
    iterations = 0

    for iterations in range(1, max_iter + 1):
        a_ub: list[list[float]] = []
        b_ub: list[float] = []

        # Coefficient budget: sum c_m <= budget.
        a_ub.append([1.0] * n_basis + [0.0, 0.0])
        b_ub.append(coeff_budget)

        # Prime dominance:
        #   sum c_m <A_m x,x> + eta >= <A_edge x,x>.
        for x in prime_dirs:
            x = x / np.linalg.norm(x)
            row = [-float(x @ A @ x) for A in A_basis] + [-1.0, 0.0]
            rhs = -float(x @ A_edge @ x)
            a_ub.append(row)
            b_ub.append(rhs)

        # Continuum/arch upper cost:
        #   sum c_m <C_m y,y> - <C_edge y,y> <= gamma.
        for y in cost_dirs:
            y = y / np.linalg.norm(y)
            row = [float(y @ C @ y) for C in C_basis] + [0.0, -1.0]
            rhs = float(y @ C_edge @ y)
            a_ub.append(row)
            b_ub.append(rhs)

        result = linprog(
            c_obj,
            A_ub=np.array(a_ub, dtype=float),
            b_ub=np.array(b_ub, dtype=float),
            bounds=bounds,
            method="highs",
        )
        if not result.success:
            break

        coeffs = np.array(result.x[:n_basis], dtype=float)
        eta = float(result.x[-2])
        gamma = float(result.x[-1])

        prime_slack = -A_edge + eta * np.eye(dim)
        cost_mat = -C_edge
        for c, A, C in zip(coeffs, A_basis, C_basis):
            prime_slack += c * A
            cost_mat += c * C

        prime_evals, prime_evecs = np.linalg.eigh(0.5 * (prime_slack + prime_slack.T))
        cost_evals, cost_evecs = np.linalg.eigh(0.5 * (cost_mat + cost_mat.T))
        min_prime_slack = float(prime_evals[0])
        max_cost_eig = float(cost_evals[-1])

        added = False
        if min_prime_slack < -tol:
            prime_dirs.append(prime_evecs[:, 0])
            added = True
        if max_cost_eig > gamma + tol:
            cost_dirs.append(cost_evecs[:, -1])
            added = True
        if not added:
            break

    return {
        "success": bool(
            result is not None
            and result.success
            and min_prime_slack >= -tol
            and max_cost_eig <= gamma + tol
        ),
        "linprog_success": bool(result is not None and result.success),
        "linprog_message": None if result is None else str(result.message),
        "iterations": int(iterations),
        "num_prime_cuts": int(len(prime_dirs)),
        "num_cost_cuts": int(len(cost_dirs)),
        "coefficients": coeffs,
        "eta": finite_float(eta),
        "gamma": finite_float(gamma),
        "min_slack_eig": finite_float(min_prime_slack),
        "max_cost_eig": finite_float(max_cost_eig),
    }


def run_liftsearch(args: argparse.Namespace) -> list[dict[str, Any]]:
    pilot = load_step13()
    rows: list[dict[str, Any]] = []
    for K in args.K:
        lo, hi = 2.0 * K, 4.0 * K
        max_a_requested = args.max_a_factor * K
        centers = parse_float_list_or_default(args.centers, default_lift_centers(K, args.num_centers))
        widths = parse_float_list_or_default(args.widths, [0.25 * K, 0.5 * K, K, 2.0 * K])

        ctx = build_packet_context(
            pilot,
            K=K,
            ell=args.ell,
            grid_delta=args.grid_delta,
            k_spline=args.k_spline,
            p0_na=args.p0_na,
        )
        params = ctx["params"]
        packet = ctx["packet"]
        D = ctx["D"]
        N = ctx["N"]
        Gc = ctx["Gc"]

        edge_shifts = [sh for sh in pilot.prime_power_shifts(params.L) if lo <= sh.a <= hi]
        P_edge = np.zeros_like(D, dtype=float)
        for sh in edge_shifts:
            P_edge += sh.weight * shifted_packet_matrix(pilot, packet, D, params.ell, sh.a)
        P0_edge = build_P0_edge(pilot, packet, D, params.ell, lo, hi, args.p0_na)

        effective_max_a = min(max_a_requested, effective_shift_cutoff(D, params.ell))
        shift_params = pilot.PilotParams(
            L=0.5 * effective_max_a,
            ell=params.ell,
            delta=params.delta,
            k_spline=params.k_spline,
            p0_na=args.p0_na,
        )
        shifts = pilot.prime_power_shifts(shift_params.L)

        need_continuum = (
            args.continuum_proxy
            or args.cost_weight != 0.0
            or args.gamma_upper is not None
        )

        basis_specs = build_lift_basis_specs(
            lift_family=args.lift_family,
            centers=centers,
            widths=widths,
        )
        basis_meta: list[dict[str, Any]] = []
        P_basis: list[np.ndarray] = []
        P0_basis: list[np.ndarray] = []
        for spec in basis_specs:
            def weight_fn(a: float, spec: dict[str, Any] = spec) -> float:
                return lift_spec_value(a, spec)

            basis_meta.append(spec)
            P_basis.append(build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, weight_fn))
            if need_continuum:
                P0_basis.append(
                    build_continuum_matrix_for_weight(
                        pilot,
                        packet,
                        D,
                        params.ell,
                        max_a=effective_max_a,
                        p0_na=args.p0_na,
                        weight_fn=weight_fn,
                    )
                )

        P_edge_c = project_matrix(pilot, P_edge, N)
        A_edge = generalized_to_standard(pilot, P_edge_c, Gc)
        A_basis = [generalized_to_standard(pilot, project_matrix(pilot, P, N), Gc) for P in P_basis]

        edge_eigs = np.linalg.eigvalsh(A_edge)
        eta_upper = args.eta_upper
        if eta_upper is None:
            eta_upper = float(edge_eigs[-1] + 1.0)

        use_cost_lp = args.cost_weight != 0.0 or args.gamma_upper is not None
        C_edge = None
        C_basis = None
        gamma_upper = None
        if need_continuum:
            C_edge = generalized_to_standard(pilot, project_matrix(pilot, P0_edge, N), Gc)
            C_basis = [
                generalized_to_standard(pilot, project_matrix(pilot, P0, N), Gc)
                for P0 in P0_basis
            ]
            gamma_upper = args.gamma_upper
            if gamma_upper is None:
                gamma_upper = float(np.linalg.eigvalsh(C_edge)[-1] + 10.0)

        if use_cost_lp:
            if C_edge is None or C_basis is None or gamma_upper is None:
                raise RuntimeError("cost liftsearch unexpectedly lacks continuum basis")
            lp = cutting_plane_lift_cost_lp(
                A_edge=A_edge,
                A_basis=A_basis,
                C_edge=C_edge,
                C_basis=C_basis,
                coeff_budget=args.coeff_budget,
                coeff_bound=args.coeff_bound,
                eta_lower=args.eta_lower,
                eta_upper=eta_upper,
                gamma_lower=args.gamma_lower,
                gamma_upper=gamma_upper,
                eta_weight=args.eta_weight,
                cost_weight=args.cost_weight,
                max_iter=args.max_iter,
                tol=args.tol,
            )
        else:
            lp = cutting_plane_lift_lp(
                A_edge=A_edge,
                A_basis=A_basis,
                coeff_budget=args.coeff_budget,
                coeff_bound=args.coeff_bound,
                eta_lower=args.eta_lower,
                eta_upper=eta_upper,
                max_iter=args.max_iter,
                tol=args.tol,
            )

        coeffs = np.asarray(lp["coefficients"], dtype=float)
        P_lift = np.zeros_like(D, dtype=float)
        for c, P in zip(coeffs, P_basis):
            P_lift += float(c) * P
        lift_minus_edge_eigs = projected_generalized_eigs(pilot, pilot.sym(P_lift - P_edge), N, Gc)

        top_coeffs: list[dict[str, Any]] = []
        for idx in np.argsort(-coeffs)[: args.top]:
            if coeffs[idx] <= args.coeff_report_tol:
                continue
            top_coeffs.append(
                {
                    "index": int(idx),
                    "coefficient": finite_float(coeffs[idx]),
                    **basis_meta[int(idx)],
                }
            )

        row: dict[str, Any] = {
            "mode": "liftsearch",
            "K": finite_float(K),
            "raw_edge": [finite_float(lo), finite_float(hi)],
            "max_a_requested": finite_float(max_a_requested),
            "max_a_effective": finite_float(effective_max_a),
            "max_a_factor": finite_float(args.max_a_factor),
            "ell": finite_float(params.ell),
            "grid_delta": finite_float(params.delta),
            "k_spline": int(params.k_spline),
            "n_centers": int(len(ctx["u"])),
            "kerQ_dim": int(N.shape[1]),
            "prime_power_shifts_total": int(len(shifts)),
            "edge_prime_power_shifts": int(len(edge_shifts)),
            "basis_family": args.lift_family,
            "basis_description": (
                "two-point Gaussian autocorrelation"
                if args.lift_family == "two-point"
                else "signed/multi-packet Gaussian autocorrelation"
            ),
            "basis_count": int(len(P_basis)),
            "centers": [finite_float(x) for x in centers],
            "widths": [finite_float(x) for x in widths],
            "coeff_budget": finite_float(args.coeff_budget),
            "coeff_bound": finite_float(args.coeff_bound),
            "coeff_sum": finite_float(float(np.sum(coeffs))),
            "eta": lp["eta"],
            "gamma": lp.get("gamma"),
            "min_slack_eig": lp["min_slack_eig"],
            "max_cost_eig": lp.get("max_cost_eig"),
            "lp_success": bool(lp["success"]),
            "linprog_success": bool(lp["linprog_success"]),
            "linprog_message": lp["linprog_message"],
            "iterations": int(lp["iterations"]),
            "num_cuts": None if lp.get("num_cuts") is None else int(lp["num_cuts"]),
            "num_prime_cuts": lp.get("num_prime_cuts"),
            "num_cost_cuts": lp.get("num_cost_cuts"),
            "use_cost_lp": bool(use_cost_lp),
            "eta_weight": finite_float(args.eta_weight),
            "cost_weight": finite_float(args.cost_weight),
            "gamma_lower": finite_float(args.gamma_lower),
            "gamma_upper": None if gamma_upper is None else finite_float(gamma_upper),
            "eig_Pedge_G_min": finite_float(edge_eigs[0]),
            "eig_Pedge_G_max": finite_float(edge_eigs[-1]),
            "eig_Plift_minus_Pedge_G_min": finite_float(lift_minus_edge_eigs[0]),
            "eig_Plift_minus_Pedge_G_max": finite_float(lift_minus_edge_eigs[-1]),
            "top_coefficients": top_coeffs,
            "D2": "raw a=r*log(p), candidate lift is an autocorrelation/positive-definite scalar probe",
        }

        if need_continuum:
            P0_lift = np.zeros_like(D, dtype=float)
            for c, P0 in zip(coeffs, P0_basis):
                P0_lift += float(c) * P0
            continuum_eigs = projected_generalized_eigs(pilot, pilot.sym(P0_lift - P0_edge), N, Gc)
            row.update(
                {
                    "continuum_proxy_max_a": finite_float(effective_max_a),
                    "eig_P0lift_minus_P0edge_G_min": finite_float(continuum_eigs[0]),
                    "eig_P0lift_minus_P0edge_G_max": finite_float(continuum_eigs[-1]),
                    "opnorm_G_P0lift_minus_P0edge": finite_float(
                        max(abs(continuum_eigs[0]), abs(continuum_eigs[-1]))
                    ),
                }
            )

        rows.append(row)
    return rows


def add_common_packet_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--K", type=float, nargs="+", required=True)
    parser.add_argument("--ell", type=float, default=0.35)
    parser.add_argument("--grid-delta", type=float, default=0.5)
    parser.add_argument("--k-spline", type=int, default=5)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)

    edge = sub.add_parser("edge", help="projected edge-defect proxy")
    add_common_packet_args(edge)
    edge.add_argument("--p0-na", type=int, default=8001)
    edge.set_defaults(func=run_edge)

    finiteop = sub.add_parser("finiteop", help="direct projected finite-operator certificate")
    add_common_packet_args(finiteop)
    finiteop.add_argument("--p0-na", type=int, default=8001)
    finiteop.add_argument("--top", type=int, default=12)
    finiteop.set_defaults(func=run_finiteop)

    finitesweep = sub.add_parser("finitesweep", help="compact finiteop spectrum sweep over packet scales")
    finitesweep.add_argument("--K", type=float, nargs="+", required=True)
    finitesweep.add_argument("--ell-values", type=float, nargs="+", required=True)
    finitesweep.add_argument("--grid-delta-values", type=float, nargs="+", required=True)
    finitesweep.add_argument("--k-spline", type=int, default=5)
    finitesweep.add_argument("--p0-na", type=int, default=1001)
    finitesweep.set_defaults(func=run_finitesweep)

    finiteschedule = sub.add_parser(
        "finiteschedule",
        help="stability-filtered best finiteop packet-scale schedule",
    )
    finiteschedule.add_argument("--K", type=float, nargs="+", required=True)
    finiteschedule.add_argument("--ell-values", type=float, nargs="+", required=True)
    finiteschedule.add_argument("--grid-delta-values", type=float, nargs="+", required=True)
    finiteschedule.add_argument("--k-spline", type=int, default=5)
    finiteschedule.add_argument("--p0-na", type=int, default=1001)
    finiteschedule.add_argument("--min-ker-dim", type=int, default=8)
    finiteschedule.add_argument("--max-g-condition", type=float, default=20.0)
    finiteschedule.add_argument("--min-g-eig", type=float, default=1e-4)
    finiteschedule.set_defaults(func=run_finiteschedule)

    spacing = sub.add_parser("spacing", help="D2 log-spacing barrier for generic Hilbert bounds")
    spacing.add_argument("--K", type=float, nargs="+", required=True)
    spacing.set_defaults(func=run_spacing)

    clvrecv = sub.add_parser("clvrecv", help="Selberg-CLV smoothed receiver operator diagnostics")
    add_common_packet_args(clvrecv)
    clvrecv.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvrecv.add_argument("--p0-na", type=int, default=1001)
    clvrecv.add_argument("--receiver-grid-nt", type=int, default=20001)
    clvrecv.set_defaults(func=run_clvrecv)

    clvprimary = sub.add_parser("clvprimary", help="receiver-primary CLV schedule diagnostics")
    add_common_packet_args(clvprimary)
    clvprimary.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvprimary.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvprimary.add_argument("--p0-na", type=int, default=1001)
    clvprimary.add_argument("--receiver-grid-nt", type=int, default=4001)
    clvprimary.set_defaults(func=run_clvprimary)

    clvblend = sub.add_parser("clvblend", help="affine CLV receiver correction tradeoff")
    add_common_packet_args(clvblend)
    clvblend.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvblend.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvblend.add_argument("--theta-min", type=float, default=0.0)
    clvblend.add_argument("--theta-max", type=float, default=1.0)
    clvblend.add_argument("--theta-count", type=int, default=101)
    clvblend.add_argument("--p0-na", type=int, default=1001)
    clvblend.set_defaults(func=run_clvblend)

    clvbreakdown = sub.add_parser("clvbreakdown", help="endpoint/bulk correction anatomy")
    add_common_packet_args(clvbreakdown)
    clvbreakdown.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvbreakdown.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvbreakdown.add_argument(
        "--halo-factor",
        type=float,
        default=1.0,
        help="endpoint halo half-width is halo_factor / receiver_delta in raw a",
    )
    clvbreakdown.add_argument("--p0-na", type=int, default=1001)
    clvbreakdown.add_argument("--top", type=int, default=12)
    clvbreakdown.set_defaults(func=run_clvbreakdown)

    clvstructure = sub.add_parser(
        "clvstructure",
        help="operator-level rank/cancellation diagnostics for the Selberg correction",
    )
    add_common_packet_args(clvstructure)
    clvstructure.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvstructure.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvstructure.add_argument(
        "--halo-factor",
        type=float,
        default=1.0,
        help="endpoint halo half-width is halo_factor / receiver_delta in raw a",
    )
    clvstructure.add_argument("--p0-na", type=int, default=1001)
    clvstructure.add_argument("--top-eigs", type=int, default=8)
    clvstructure.add_argument("--top-rows", type=int, default=8)
    clvstructure.set_defaults(func=run_clvstructure)

    clvquad = sub.add_parser(
        "clvquad",
        help="partial-summation variation diagnostics for the Selberg correction",
    )
    add_common_packet_args(clvquad)
    clvquad.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvquad.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvquad.add_argument("--p0-na", type=int, default=1001)
    clvquad.add_argument("--quad-na", type=int, default=4001)
    clvquad.set_defaults(func=run_clvquad)

    clvfourier = sub.add_parser(
        "clvfourier",
        help="sampled Fourier-sign diagnostics for the smooth Selberg correction test",
    )
    add_common_packet_args(clvfourier)
    clvfourier.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvfourier.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvfourier.add_argument("--p0-na", type=int, default=1001)
    clvfourier.add_argument("--quad-na", type=int, default=4001)
    clvfourier.add_argument("--fourier-u-max", type=float, default=2.0)
    clvfourier.add_argument("--fourier-nu", type=int, default=1001)
    clvfourier.set_defaults(func=run_clvfourier)

    clvledger = sub.add_parser(
        "clvledger",
        help="finite psi-staircase ledger diagnostics for the smooth correction",
    )
    add_common_packet_args(clvledger)
    clvledger.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvledger.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvledger.add_argument(
        "--directions",
        choices=["opnorm", "all"],
        default="opnorm",
        help="which correction eigenvector directions to ledger",
    )
    clvledger.add_argument("--p0-na", type=int, default=1001)
    clvledger.add_argument("--quad-na", type=int, default=4001)
    clvledger.add_argument("--ledger-cells", type=int, default=120)
    clvledger.add_argument("--top-cells", type=int, default=12)
    clvledger.set_defaults(func=run_clvledger)

    clvmesh = sub.add_parser(
        "clvmesh",
        help="mesh-stability audit for the finite psi-staircase ledger",
    )
    add_common_packet_args(clvmesh)
    clvmesh.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvmesh.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvmesh.add_argument(
        "--directions",
        choices=["opnorm", "all"],
        default="opnorm",
        help="which correction eigenvector directions to audit",
    )
    clvmesh.add_argument("--p0-na", type=int, default=1001)
    clvmesh.add_argument("--quad-na-values", type=int, nargs="+", default=[2001, 4001, 8001])
    clvmesh.add_argument("--ledger-cells", type=int, default=120)
    clvmesh.add_argument("--top-cells", type=int, default=3)
    clvmesh.set_defaults(func=run_clvmesh)

    clvsigncert = sub.add_parser(
        "clvsigncert",
        help="smooth/jump split prototype for V_J sign-certificate cells",
    )
    add_common_packet_args(clvsigncert)
    clvsigncert.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    clvsigncert.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    clvsigncert.add_argument(
        "--directions",
        choices=["opnorm", "all"],
        default="opnorm",
        help="which correction eigenvector directions to inspect",
    )
    clvsigncert.add_argument("--p0-na", type=int, default=1001)
    clvsigncert.add_argument("--ledger-cells", type=int, default=120)
    clvsigncert.add_argument("--cert-na", type=int, default=801)
    clvsigncert.add_argument(
        "--interval-safety-factors",
        type=float,
        nargs="+",
        default=[2.0, 10.0, 100.0, 1000.0],
        help="diagnostic derivative-inflation factors for non-node sign guards",
    )
    clvsigncert.add_argument("--cells", type=int, nargs="+", required=True)
    clvsigncert.set_defaults(func=run_clvsigncert)

    lowband = sub.add_parser("lowband", help="Selberg-positive low-band mass")
    lowband.add_argument("--K", type=float, nargs="+", required=True)
    lowband.add_argument("--ell", type=float, default=0.35)
    lowband.add_argument("--k-spline", type=int, default=5)
    lowband.add_argument("--band-nt", type=int, default=20001)
    lowband.set_defaults(func=run_lowband)

    gaussian = sub.add_parser("gaussian", help="naive Gaussian majorant operator failure")
    add_common_packet_args(gaussian)
    gaussian.add_argument("--max-a-factor", type=float, default=8.0)
    gaussian.add_argument("--u-nt", type=int, default=200001)
    gaussian.set_defaults(func=run_gaussian)

    liftsearch = sub.add_parser("liftsearch", help="finite positive-definite lift operator search")
    add_common_packet_args(liftsearch)
    liftsearch.add_argument("--max-a-factor", type=float, default=8.0)
    liftsearch.add_argument(
        "--lift-family",
        choices=["two-point", "signed-triplet", "all"],
        default="two-point",
        help="positive-definite scalar lift dictionary to test",
    )
    liftsearch.add_argument("--centers", type=float, nargs="*")
    liftsearch.add_argument("--num-centers", type=int, default=5)
    liftsearch.add_argument("--widths", type=float, nargs="*")
    liftsearch.add_argument("--coeff-budget", type=float, default=10.0)
    liftsearch.add_argument("--coeff-bound", type=float, default=10.0)
    liftsearch.add_argument("--eta-lower", type=float, default=-100.0)
    liftsearch.add_argument("--eta-upper", type=float)
    liftsearch.add_argument("--eta-weight", type=float, default=1.0)
    liftsearch.add_argument("--cost-weight", type=float, default=0.0)
    liftsearch.add_argument("--gamma-lower", type=float, default=-100.0)
    liftsearch.add_argument("--gamma-upper", type=float)
    liftsearch.add_argument("--max-iter", type=int, default=40)
    liftsearch.add_argument("--tol", type=float, default=1e-9)
    liftsearch.add_argument("--p0-na", type=int, default=2001)
    liftsearch.add_argument("--top", type=int, default=8)
    liftsearch.add_argument("--coeff-report-tol", type=float, default=1e-9)
    liftsearch.add_argument(
        "--no-continuum-proxy",
        dest="continuum_proxy",
        action="store_false",
        help="skip the continuum prime-model proxy for speed",
    )
    liftsearch.set_defaults(func=run_liftsearch, continuum_proxy=True)

    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = args.func(args)
    print(json.dumps(rows, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
