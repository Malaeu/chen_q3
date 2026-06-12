#!/usr/bin/env python3
"""
Track B / E5' edge-operator probes.

This is reconnaissance code, not a proof certificate.  It reuses the Step13
B-spline packet pilot to make the current B2 obstruction checks reproducible:

  edge      projected edge-defect proxy on ker(Q)
  lowband   mass captured by the Selberg-positive ultra-low band
  gaussian  finite-packet failure of the naive PSD Gaussian majorant
  liftsearch finite operator-majorant search for positive-definite lifts

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


def two_point_gaussian_lift_value(a: float, *, center: float, width: float) -> float:
    """Autocorrelation of two equal Gaussian packets separated by `center`.

    Up to an irrelevant positive scale this has the form
      2 G_width(a) + G_width(a-center) + G_width(a+center).

    It is a positive-definite even function because it is an autocorrelation.
    """
    if width <= 0:
        raise ValueError("width must be positive")

    def g(x: float) -> float:
        return math.exp(-math.pi * (x / width) ** 2)

    return 2.0 * g(a) + g(a - center) + g(a + center)


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

        basis_meta: list[dict[str, float]] = []
        P_basis: list[np.ndarray] = []
        P0_basis: list[np.ndarray] = []
        for center in centers:
            for width in widths:
                def weight_fn(a: float, center: float = center, width: float = width) -> float:
                    return two_point_gaussian_lift_value(a, center=center, width=width)

                basis_meta.append({"center": finite_float(center), "width": finite_float(width)})
                P_basis.append(build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, weight_fn))
                if args.continuum_proxy:
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
            "basis_family": "two-point Gaussian autocorrelation",
            "basis_count": int(len(P_basis)),
            "centers": [finite_float(x) for x in centers],
            "widths": [finite_float(x) for x in widths],
            "coeff_budget": finite_float(args.coeff_budget),
            "coeff_bound": finite_float(args.coeff_bound),
            "coeff_sum": finite_float(float(np.sum(coeffs))),
            "eta": lp["eta"],
            "min_slack_eig": lp["min_slack_eig"],
            "lp_success": bool(lp["success"]),
            "linprog_success": bool(lp["linprog_success"]),
            "linprog_message": lp["linprog_message"],
            "iterations": int(lp["iterations"]),
            "num_cuts": int(lp["num_cuts"]),
            "eig_Pedge_G_min": finite_float(edge_eigs[0]),
            "eig_Pedge_G_max": finite_float(edge_eigs[-1]),
            "eig_Plift_minus_Pedge_G_min": finite_float(lift_minus_edge_eigs[0]),
            "eig_Plift_minus_Pedge_G_max": finite_float(lift_minus_edge_eigs[-1]),
            "top_coefficients": top_coeffs,
            "D2": "raw a=r*log(p), candidate lift is an autocorrelation/positive-definite scalar probe",
        }

        if args.continuum_proxy:
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
    liftsearch.add_argument("--centers", type=float, nargs="*")
    liftsearch.add_argument("--num-centers", type=int, default=5)
    liftsearch.add_argument("--widths", type=float, nargs="*")
    liftsearch.add_argument("--coeff-budget", type=float, default=10.0)
    liftsearch.add_argument("--coeff-bound", type=float, default=10.0)
    liftsearch.add_argument("--eta-lower", type=float, default=-100.0)
    liftsearch.add_argument("--eta-upper", type=float)
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
