#!/usr/bin/env python3
"""
Track B / E5' edge-operator probes.

This is reconnaissance code, not a proof certificate.  It reuses the Step13
B-spline packet pilot to make the current B2 obstruction checks reproducible:

  edge      projected edge-defect proxy on ker(Q)
  lowband   mass captured by the Selberg-positive ultra-low band
  gaussian  finite-packet failure of the naive PSD Gaussian majorant

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


def build_P0_edge(pilot: Any, packet: Any, D: np.ndarray, ell: float, lo: float, hi: float, p0_na: int) -> np.ndarray:
    a_grid = np.linspace(lo, hi, p0_na)
    wa = pilot.trap_weights_uniform(a_grid)
    P0 = np.zeros_like(D, dtype=float)
    for a, w in zip(a_grid, wa):
        P0 += w * math.exp(0.5 * float(a)) * shifted_packet_matrix(pilot, packet, D, ell, float(a))
    return pilot.sym(P0)


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
        max_a = args.max_a_factor * K
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

    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = args.func(args)
    print(json.dumps(rows, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
