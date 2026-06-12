#!/usr/bin/env python3
"""
Track B / E5' non-node interval-atom audit.

This script is a proof-generator scaffold, not a proof certificate.  It
selects the same `clvsigncert` opnorm direction, focuses on one non-node mesh
interval, and emits the analytic atom ranges that the future outward-rounded
certificate must prove:

  E_delta^(j), F_v^(j), H_v^(j), S_v^(j).

The current ranges are directed-rounded sampled ranges.  They are useful for
checking the atom contract and slack budget, but they are not a replacement
for interval extension of the Selberg/Vaaler receiver and B-spline profile.

All coordinates are raw-log coordinates: a = r * log(p).
"""

from __future__ import annotations

import argparse
import json
import math
from typing import Any

import numpy as np

import trackb_edge_operator_probe as probe


def out_down(x: float) -> float:
    return float(math.nextafter(float(x), -math.inf))


def out_up(x: float) -> float:
    return float(math.nextafter(float(x), math.inf))


def directed_range(values: np.ndarray) -> dict[str, Any]:
    arr = np.asarray(values, dtype=float)
    finite = arr[np.isfinite(arr)]
    if finite.size == 0:
        return {"lo": None, "hi": None, "max_abs": None}
    lo = out_down(float(np.min(finite)))
    hi = out_up(float(np.max(finite)))
    max_abs = out_up(max(abs(lo), abs(hi)))
    return {
        "lo": lo,
        "hi": hi,
        "max_abs": max_abs,
    }


def abs_lower_from_endpoint_values(left: float, right: float) -> float:
    lower = min(abs(float(left)), abs(float(right)))
    return max(0.0, out_down(lower))


def abs_upper_from_endpoint_values(left: float, right: float) -> float:
    upper = max(abs(float(left)), abs(float(right)))
    return out_up(upper)


def selected_opnorm_context(
    *,
    K: float,
    ell: float,
    grid_delta: float,
    k_spline: int,
    p0_na: int,
    receiver_delta: float,
) -> dict[str, Any]:
    pilot = probe.load_step13()
    lo, hi = 2.0 * float(K), 4.0 * float(K)
    ctx = probe.build_packet_context(
        pilot,
        K=float(K),
        ell=float(ell),
        grid_delta=float(grid_delta),
        k_spline=int(k_spline),
        p0_na=int(p0_na),
    )
    params = ctx["params"]
    packet = ctx["packet"]
    D = ctx["D"]
    N = ctx["N"]
    Gc = ctx["Gc"]
    effective_max_a = probe.effective_shift_cutoff(D, params.ell)
    shift_params = pilot.PilotParams(
        L=0.5 * effective_max_a,
        ell=params.ell,
        delta=params.delta,
        k_spline=params.k_spline,
        p0_na=int(p0_na),
    )
    shifts = pilot.prime_power_shifts(shift_params.L)

    def chi_weight(a: float) -> float:
        return 1.0 if lo <= a <= hi else 0.0

    def plus_weight(a: float) -> float:
        return float(
            probe.selberg_interval_values(
                np.array([a]),
                lo=lo,
                hi=hi,
                receiver_delta=float(receiver_delta),
                sign="plus",
            )[0]
        )

    P_edge = probe.build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, chi_weight)
    P_plus = probe.build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, plus_weight)
    P0_edge = probe.build_P0_edge(pilot, packet, D, params.ell, lo, hi, int(p0_na))
    P0_plus = probe.build_continuum_matrix_for_weight(
        pilot,
        packet,
        D,
        params.ell,
        max_a=effective_max_a,
        p0_na=int(p0_na),
        weight_fn=plus_weight,
    )
    correction = pilot.sym((P_plus - P_edge) - (P0_plus - P0_edge))
    A_corr = probe.generalized_to_standard(pilot, probe.project_matrix(pilot, correction, N), Gc)
    eigs, evecs = np.linalg.eigh(A_corr)
    op_idx = int(np.argmax(np.abs(eigs)))
    coeffs = probe.standardized_eigenvector_to_full_coeffs(Gc, N, evecs[:, op_idx])
    return {
        "pilot": pilot,
        "params": params,
        "packet": packet,
        "D": D,
        "coeffs": coeffs,
        "lo": lo,
        "hi": hi,
        "effective_max_a": effective_max_a,
        "opnorm_eigenvalue": float(eigs[op_idx]),
        "correction_eig_min": float(eigs[0]),
        "correction_eig_max": float(eigs[-1]),
    }


def atom_samples(
    *,
    ctx: dict[str, Any],
    receiver_delta: float,
    a_grid: np.ndarray,
) -> dict[str, np.ndarray]:
    lo = float(ctx["lo"])
    hi = float(ctx["hi"])
    pilot = ctx["pilot"]
    packet = ctx["packet"]
    D = ctx["D"]
    ell = float(ctx["params"].ell)
    coeffs = ctx["coeffs"]

    mplus, e1, e2, e3 = probe.selberg_interval_plus_derivatives3(
        a_grid,
        lo=lo,
        hi=hi,
        receiver_delta=float(receiver_delta),
    )
    chi = np.where((lo <= a_grid) & (a_grid <= hi), 1.0, 0.0)
    e0 = mplus - chi
    f0 = probe.packet_profile_grid(pilot, packet, D, ell, coeffs, a_grid)
    f1 = probe.packet_profile_derivative_grid(pilot, packet, D, ell, coeffs, a_grid)
    f2 = probe.packet_profile_second_derivative_grid(pilot, packet, D, ell, coeffs, a_grid)
    f3 = probe.packet_profile_third_derivative_grid(pilot, packet, D, ell, coeffs, a_grid)
    h0 = e0 * f0
    h1 = e1 * f0 + e0 * f1
    h2 = e2 * f0 + 2.0 * e1 * f1 + e0 * f2
    h3 = e3 * f0 + 3.0 * e2 * f1 + 3.0 * e1 * f2 + e0 * f3
    exp_half = np.exp(-0.5 * a_grid)
    s0 = exp_half * (h1 - 0.5 * h0)
    s1 = exp_half * (h2 - h1 + 0.25 * h0)
    s2 = exp_half * (h3 - 1.5 * h2 + 0.75 * h1 - 0.125 * h0)
    return {
        "E0": e0,
        "E1": e1,
        "E2": e2,
        "E3": e3,
        "F0": f0,
        "F1": f1,
        "F2": f2,
        "F3": f3,
        "H0": h0,
        "H1": h1,
        "H2": h2,
        "H3": h3,
        "S0": s0,
        "S1": s1,
        "S2": s2,
    }


def run(args: argparse.Namespace) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for K in args.K:
        ell = probe.stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        for receiver_delta in args.receiver_delta:
            ctx = selected_opnorm_context(
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
                receiver_delta=float(receiver_delta),
            )
            cell_edges = np.linspace(
                0.0,
                float(ctx["effective_max_a"]),
                int(args.ledger_cells) + 1,
            )
            cell_idx = int(args.cell)
            if cell_idx < 0 or cell_idx >= int(args.ledger_cells):
                raise ValueError("cell must be inside ledger cell range")
            cell_lo = float(cell_edges[cell_idx])
            cell_hi = float(cell_edges[cell_idx + 1])
            mesh = np.linspace(cell_lo, cell_hi, int(args.cert_na))
            if args.mesh_index == "auto":
                # The current theorem-producing pilot is the worst leftmost
                # interval for K=3.5 cell 58.  For other cells, keep the same
                # deterministic first-interval default until a proof-grade
                # interval selector exists.
                mesh_idx = 0
            else:
                mesh_idx = int(args.mesh_index)
            if mesh_idx < 0 or mesh_idx >= len(mesh) - 1:
                raise ValueError("mesh-index must select an interval inside the cell mesh")
            a_lo = float(mesh[mesh_idx])
            a_hi = float(mesh[mesh_idx + 1])
            a_grid = np.linspace(a_lo, a_hi, int(args.atom_samples))
            samples = atom_samples(
                ctx=ctx,
                receiver_delta=float(receiver_delta),
                a_grid=a_grid,
            )
            ranges = {name: directed_range(values) for name, values in samples.items()}
            width = out_up(a_hi - a_lo)
            endpoint_abs_S_lower = abs_lower_from_endpoint_values(
                float(samples["S0"][0]),
                float(samples["S0"][-1]),
            )
            endpoint_abs_S1_upper = abs_upper_from_endpoint_values(
                float(samples["S1"][0]),
                float(samples["S1"][-1]),
            )
            sample_S2_abs_upper = ranges["S2"]["max_abs"]
            guards: list[dict[str, Any]] = []
            for factor in args.curvature_factors:
                derivative_envelope = out_up(
                    endpoint_abs_S1_upper
                    + 0.5 * float(factor) * float(sample_S2_abs_upper) * width
                )
                guard = out_down(endpoint_abs_S_lower - 0.5 * derivative_envelope * width)
                guards.append(
                    {
                        "curvature_factor": float(factor),
                        "endpoint_abs_S_lower": endpoint_abs_S_lower,
                        "endpoint_abs_S1_upper": endpoint_abs_S1_upper,
                        "sample_sup_abs_S2_upper": sample_S2_abs_upper,
                        "derivative_envelope_upper": derivative_envelope,
                        "mesh_guard_lower": guard,
                        "passes": bool(guard > 0.0),
                    }
                )
            node_audit = probe.selberg_receiver_node_audit(
                a_grid,
                lo=float(ctx["lo"]),
                hi=float(ctx["hi"]),
                receiver_delta=float(receiver_delta),
            )
            rows.append(
                {
                    "mode": "trackb_nonnode_interval_atom_audit",
                    "status": "diagnostic_only",
                    "interval_kind": "directed_rounded_sample_ranges_not_proof_grade",
                    "K": float(K),
                    "ell": float(ell),
                    "grid_delta": float(args.grid_delta),
                    "k_spline": int(args.k_spline),
                    "p0_na": int(args.p0_na),
                    "ledger_cells": int(args.ledger_cells),
                    "cert_na": int(args.cert_na),
                    "cell": cell_idx,
                    "mesh_index": mesh_idx,
                    "atom_samples": int(args.atom_samples),
                    "receiver_delta": float(receiver_delta),
                    "raw_edge": [float(ctx["lo"]), float(ctx["hi"])],
                    "cell_interval": [cell_lo, cell_hi],
                    "mesh_interval": [a_lo, a_hi],
                    "mesh_width_directed_upper": width,
                    "opnorm_eigenvalue": float(ctx["opnorm_eigenvalue"]),
                    "correction_eig_min": float(ctx["correction_eig_min"]),
                    "correction_eig_max": float(ctx["correction_eig_max"]),
                    "atom_ranges": ranges,
                    "mesh_guards": guards,
                    "receiver_node_audit": node_audit,
                    "proof_status": (
                        "diagnostic_only: fields are the future interval atoms, "
                        "but ranges are directed-rounded sampled ranges rather "
                        "than natural interval extensions of Vaaler/polygamma "
                        "and B-spline formulas"
                    ),
                    "next_certificate_contract": (
                        "replace each sampled range E_delta^(j), F_v^(j), "
                        "H_v^(j), S_v^(j) by an outward-rounded interval "
                        "extension over the same raw-a mesh interval"
                    ),
                    "D2": (
                        "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
                        "w_Q(n)=2*Lambda(n)/sqrt(n)"
                    ),
                }
            )
    return rows


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--K", type=float, nargs="+", required=True)
    parser.add_argument("--ell", type=float, default=0.35)
    parser.add_argument("--grid-delta", type=float, default=0.5)
    parser.add_argument("--k-spline", type=int, default=5)
    parser.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    parser.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    parser.add_argument("--p0-na", type=int, default=1001)
    parser.add_argument("--ledger-cells", type=int, default=120)
    parser.add_argument("--cert-na", type=int, default=801)
    parser.add_argument("--cell", type=int, required=True)
    parser.add_argument(
        "--mesh-index",
        default="auto",
        help="mesh interval index inside the selected cell, or auto",
    )
    parser.add_argument("--atom-samples", type=int, default=65)
    parser.add_argument(
        "--curvature-factors",
        type=float,
        nargs="+",
        default=[1.0, 1000.0, 10000.0],
        help="diagnostic inflation factors for sampled S'' ranges",
    )
    return parser.parse_args()


def main() -> None:
    rows = run(parse_args())
    print(json.dumps(rows, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
