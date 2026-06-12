#!/usr/bin/env python3
"""
Track B / E5' edge-operator probes.

This is reconnaissance code, not a proof certificate.  It reuses the Step13
B-spline packet pilot to make the current B2 obstruction checks reproducible:

  edge      projected edge-defect proxy on ker(Q)
  lowband   mass captured by the Selberg-positive ultra-low band
  gaussian  finite-packet failure of the naive PSD Gaussian majorant
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
