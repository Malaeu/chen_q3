#!/usr/bin/env python3
"""
Track B / E5' compact multi-cell sweep for the non-node interval guard.

This is a diagnostic coverage helper.  It reuses one `clvsigncert` context and
runs the compact interval guard from `trackb_nonnode_interval_atom_audit.py`
over a list or range of ledger cells.  Each mesh interval is then optionally
checked again by exact dyadic rational guard arithmetic.

The script is not a proof of the interval enclosures, and cells crossing an
edge jump are reported separately because they need a jump-split certificate.
"""

from __future__ import annotations

import argparse
import json
from typing import Any

import numpy as np

import trackb_edge_operator_probe as probe
import trackb_interval_worklist_rationalize as rationalize
import trackb_nonnode_interval_atom_audit as atom


def parse_cell_spec(spec: str) -> list[int]:
    cells: list[int] = []
    for part in spec.split(","):
        token = part.strip()
        if not token:
            continue
        if ":" in token:
            pieces = token.split(":")
            if len(pieces) not in (2, 3):
                raise ValueError(f"bad cell range: {token}")
            start = int(pieces[0])
            stop = int(pieces[1])
            step = int(pieces[2]) if len(pieces) == 3 else 1
            cells.extend(range(start, stop, step))
        else:
            cells.append(int(token))
    return sorted(dict.fromkeys(cells))


def compact_cell_summary(
    *,
    args: argparse.Namespace,
    ctx: dict[str, Any],
    K: float,
    ell: float,
    receiver_delta: float,
    cell_idx: int,
) -> dict[str, Any]:
    cell_edges = np.linspace(
        0.0,
        float(ctx["effective_max_a"]),
        int(args.ledger_cells) + 1,
    )
    if cell_idx < 0 or cell_idx >= int(args.ledger_cells):
        raise ValueError(f"cell {cell_idx} outside ledger range")
    cell_lo = float(cell_edges[cell_idx])
    cell_hi = float(cell_edges[cell_idx + 1])
    mesh = np.linspace(cell_lo, cell_hi, int(args.cert_na))

    rows: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    for mesh_idx in range(len(mesh) - 1):
        try:
            rows.append(
                atom.audit_mesh_interval(
                    args=args,
                    ctx=ctx,
                    K=float(K),
                    ell=float(ell),
                    receiver_delta=float(receiver_delta),
                    cell_idx=cell_idx,
                    cell_lo=cell_lo,
                    cell_hi=cell_hi,
                    mesh=mesh,
                    mesh_idx=mesh_idx,
                    include_samples=False,
                    compact=True,
                )
            )
        except ValueError as exc:
            skipped.append(
                {
                    "mesh_index": mesh_idx,
                    "mesh_interval": [float(mesh[mesh_idx]), float(mesh[mesh_idx + 1])],
                    "reason": str(exc),
                }
            )

    rational_rows = [
        rationalize.guard_row(row, bits=int(args.dyadic_bits))
        for row in rows
    ]
    direct_failures = [row for row in rational_rows if not row["direct_S1_guard_passes"]]
    curvature_failures = [
        row for row in rational_rows if not row["curvature_S2_guard_passes"]
    ]

    worst_direct = sorted(
        rational_rows,
        key=lambda row: row["_direct_guard_fraction"],
    )[: int(args.worst_limit)]
    worst_curvature = sorted(
        rational_rows,
        key=lambda row: row["_curvature_guard_fraction"],
    )[: int(args.worst_limit)]

    return {
        "mode": "trackb_nonnode_interval_cell_sweep_row",
        "status": "diagnostic_only",
        "K": float(K),
        "ell": float(ell),
        "receiver_delta": float(receiver_delta),
        "receiver_interval_method": getattr(args, "receiver_interval_method", "polygamma"),
        "receiver_pole_split_radius": float(
            getattr(args, "receiver_pole_split_radius", 0.0)
        ),
        "receiver_taylor_samples": int(getattr(args, "receiver_taylor_samples", 0)),
        "receiver_taylor_inflation": float(
            getattr(args, "receiver_taylor_inflation", 0.0)
        ),
        "profile_interval_source_method": getattr(args, "profile_interval_method", "natural"),
        "profile_taylor_samples": int(getattr(args, "profile_taylor_samples", 0)),
        "profile_taylor_inflation": float(getattr(args, "profile_taylor_inflation", 0.0)),
        "ledger_cells": int(args.ledger_cells),
        "cert_na": int(args.cert_na),
        "cell": int(cell_idx),
        "cell_interval": [cell_lo, cell_hi],
        "mesh_intervals_total": len(mesh) - 1,
        "mesh_intervals_checked": len(rows),
        "edge_jump_skipped_count": len(skipped),
        "skipped_mesh_intervals": skipped[: int(args.worst_limit)],
        "dyadic_bits": int(args.dyadic_bits),
        "direct_S1_guard_pass_count": len(rational_rows) - len(direct_failures),
        "curvature_S2_guard_pass_count": len(rational_rows) - len(curvature_failures),
        "direct_S1_guard_failure_count": len(direct_failures),
        "curvature_S2_guard_failure_count": len(curvature_failures),
        "min_direct_S1_mesh_guard_lower": None
        if not rational_rows
        else rationalize.rational_to_record(
            min(row["_direct_guard_fraction"] for row in rational_rows)
        ),
        "min_curvature_S2_mesh_guard_lower": None
        if not rational_rows
        else rationalize.rational_to_record(
            min(row["_curvature_guard_fraction"] for row in rational_rows)
        ),
        "min_S0_abs_lower": None
        if not rational_rows
        else rationalize.rational_to_record(
            min(row["_s0_abs_lower_fraction"] for row in rational_rows)
        ),
        "max_S1_abs_upper": None
        if not rational_rows
        else rationalize.rational_to_record(
            max(row["_s1_abs_upper_fraction"] for row in rational_rows)
        ),
        "max_S2_abs_upper": None
        if not rational_rows
        else rationalize.rational_to_record(
            max(row["_s2_abs_upper_fraction"] for row in rational_rows)
        ),
        "worst_direct_S1_rows": [
            rationalize.strip_internal(row) for row in worst_direct
        ],
        "worst_curvature_S2_rows": [
            rationalize.strip_internal(row) for row in worst_curvature
        ],
        "D2": (
            "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
            "w_Q(n)=2*Lambda(n)/sqrt(n)"
        ),
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    K = float(args.K)
    ell = probe.stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
    receiver_delta = float(args.receiver_delta)
    ctx = atom.selected_opnorm_context(
        K=K,
        ell=float(ell),
        grid_delta=float(args.grid_delta),
        k_spline=int(args.k_spline),
        p0_na=int(args.p0_na),
        receiver_delta=receiver_delta,
    )
    cells = parse_cell_spec(args.cells)
    cell_rows = [
        compact_cell_summary(
            args=args,
            ctx=ctx,
            K=K,
            ell=float(ell),
            receiver_delta=receiver_delta,
            cell_idx=cell_idx,
        )
        for cell_idx in cells
    ]
    checked_rows = [row for row in cell_rows if row["mesh_intervals_checked"] > 0]
    direct_fail_cells = [
        row for row in checked_rows if row["direct_S1_guard_failure_count"] > 0
    ]
    curvature_fail_cells = [
        row for row in checked_rows if row["curvature_S2_guard_failure_count"] > 0
    ]
    skipped_cells = [row for row in cell_rows if row["edge_jump_skipped_count"] > 0]
    return {
        "mode": "trackb_nonnode_interval_cell_sweep",
        "status": "diagnostic_only",
        "K": K,
        "ell": float(ell),
        "receiver_delta": receiver_delta,
        "receiver_interval_method": getattr(args, "receiver_interval_method", "polygamma"),
        "receiver_pole_split_radius": float(
            getattr(args, "receiver_pole_split_radius", 0.0)
        ),
        "receiver_taylor_samples": int(getattr(args, "receiver_taylor_samples", 0)),
        "receiver_taylor_inflation": float(
            getattr(args, "receiver_taylor_inflation", 0.0)
        ),
        "profile_interval_source_method": getattr(args, "profile_interval_method", "natural"),
        "profile_taylor_samples": int(getattr(args, "profile_taylor_samples", 0)),
        "profile_taylor_inflation": float(getattr(args, "profile_taylor_inflation", 0.0)),
        "grid_delta": float(args.grid_delta),
        "k_spline": int(args.k_spline),
        "p0_na": int(args.p0_na),
        "ledger_cells": int(args.ledger_cells),
        "cert_na": int(args.cert_na),
        "dyadic_bits": int(args.dyadic_bits),
        "raw_edge": [float(ctx["lo"]), float(ctx["hi"])],
        "effective_max_a": float(ctx["effective_max_a"]),
        "cells_requested": cells,
        "cells_total": len(cell_rows),
        "cells_with_checked_mesh": len(checked_rows),
        "cells_with_edge_jump_skips": len(skipped_cells),
        "cells_with_direct_failures": len(direct_fail_cells),
        "cells_with_curvature_failures": len(curvature_fail_cells),
        "mesh_intervals_total": sum(row["mesh_intervals_total"] for row in cell_rows),
        "mesh_intervals_checked": sum(row["mesh_intervals_checked"] for row in cell_rows),
        "mesh_intervals_skipped": sum(row["edge_jump_skipped_count"] for row in cell_rows),
        "direct_S1_guard_pass_count": sum(
            row["direct_S1_guard_pass_count"] for row in checked_rows
        ),
        "curvature_S2_guard_pass_count": sum(
            row["curvature_S2_guard_pass_count"] for row in checked_rows
        ),
        "direct_S1_guard_failure_count": sum(
            row["direct_S1_guard_failure_count"] for row in checked_rows
        ),
        "curvature_S2_guard_failure_count": sum(
            row["curvature_S2_guard_failure_count"] for row in checked_rows
        ),
        "cell_rows": cell_rows,
        "proof_status": (
            "diagnostic_only: multi-cell coverage over floating source boxes "
            "with exact dyadic guard arithmetic; edge-jump cells need a "
            "separate jump-split source-box theorem"
        ),
        "D2": (
            "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
            "w_Q(n)=2*Lambda(n)/sqrt(n)"
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--K", type=float, required=True)
    parser.add_argument("--ell", type=float, default=0.35)
    parser.add_argument("--grid-delta", type=float, default=0.5)
    parser.add_argument("--k-spline", type=int, default=5)
    parser.add_argument("--receiver-delta", type=float, required=True)
    parser.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
    )
    parser.add_argument("--p0-na", type=int, default=1001)
    parser.add_argument("--ledger-cells", type=int, default=120)
    parser.add_argument("--cert-na", type=int, default=801)
    parser.add_argument(
        "--cells",
        required=True,
        help="comma list and/or Python-style ranges, e.g. 58,59 or 58:64",
    )
    parser.add_argument("--polygamma-tail-terms", type=int, default=400)
    parser.add_argument(
        "--receiver-interval-method",
        choices=["polygamma", "pole-split", "sampled-taylor", "centered-taylor"],
        default="polygamma",
    )
    parser.add_argument("--receiver-pole-split-radius", type=float, default=0.2)
    parser.add_argument("--receiver-taylor-samples", type=int, default=17)
    parser.add_argument("--receiver-taylor-inflation", type=float, default=2.0)
    parser.add_argument(
        "--profile-interval-method",
        choices=["natural", "sampled-taylor", "centered-taylor"],
        default="natural",
    )
    parser.add_argument("--profile-taylor-samples", type=int, default=17)
    parser.add_argument("--profile-taylor-inflation", type=float, default=2.0)
    parser.add_argument("--dyadic-bits", type=int, default=96)
    parser.add_argument("--worst-limit", type=int, default=3)
    parser.add_argument("--atom-samples", type=int, default=65)
    parser.add_argument("--curvature-factors", type=float, nargs="+", default=[10000.0])
    return parser.parse_args()


def main() -> None:
    print(json.dumps(run(parse_args()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
