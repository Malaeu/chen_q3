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
            row.update(eig_row("hard_edge_minus_continuum", hard))
            row.update(eig_row("Mplus_minus_Mplus_continuum", plus))
            row.update(eig_row("Mminus_minus_Mminus_continuum", minus))
            row.update(eig_row("prime_Mplus_minus_edge", P_plus - P_edge))
            row.update(eig_row("prime_edge_minus_Mminus", P_edge - P_minus))
            row.update(eig_row("continuum_Mplus_minus_edge", P0_plus - P0_edge))
            row.update(eig_row("continuum_edge_minus_Mminus", P0_edge - P0_minus))
            rows.append(row)
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
