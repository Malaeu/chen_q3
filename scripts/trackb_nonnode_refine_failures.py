#!/usr/bin/env python3
"""
Track B / E5' adaptive refinement probe for non-node interval guard failures.

The coarse multi-cell sweep intentionally uses a uniform mesh.  Near Vaaler
receiver halos this can be too wide even when the sampled atom is far from a
real sign change.  This helper refines only the coarse mesh intervals whose
exact dyadic guard arithmetic fails.

This is diagnostic scaffolding only:
- the source interval boxes are still the floating interval boxes emitted by
  trackb_nonnode_interval_atom_audit.py;
- exact arithmetic is used only after those boxes are supplied;
- edge-jump intervals are reported separately and need a jump-split theorem.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from typing import Any

import numpy as np

import trackb_edge_operator_probe as probe
import trackb_interval_worklist_rationalize as rationalize
import trackb_nonnode_cell_sweep as cell_sweep
import trackb_nonnode_interval_atom_audit as atom


def guard_passes(row: dict[str, Any]) -> bool:
    return bool(row["direct_S1_guard_passes"] and row["curvature_S2_guard_passes"])


def guard_fraction(row: dict[str, Any]) -> Fraction:
    return min(row["_direct_guard_fraction"], row["_curvature_guard_fraction"])


def refined_args(args: argparse.Namespace) -> argparse.Namespace:
    payload = vars(args).copy()
    payload["cert_na"] = (
        (int(args.cert_na) - 1) * int(args.refine_factor) ** int(args.refine_levels)
    ) + 1
    return argparse.Namespace(**payload)


def audit_row(
    *,
    args: argparse.Namespace,
    ctx: dict[str, Any],
    K: float,
    ell: float,
    receiver_delta: float,
    cell_idx: int,
    cell_lo: float,
    cell_hi: float,
    mesh: np.ndarray,
    mesh_idx: int,
) -> dict[str, Any]:
    row = atom.audit_mesh_interval(
        args=args,
        ctx=ctx,
        K=float(K),
        ell=float(ell),
        receiver_delta=float(receiver_delta),
        cell_idx=int(cell_idx),
        cell_lo=float(cell_lo),
        cell_hi=float(cell_hi),
        mesh=mesh,
        mesh_idx=int(mesh_idx),
        include_samples=False,
        compact=True,
    )
    rational = rationalize.guard_row(row, bits=int(args.dyadic_bits))
    return {
        "source_row": row,
        "rational_guard": rational,
        "guard_passes": guard_passes(rational),
    }


def compact_guard(row: dict[str, Any]) -> dict[str, Any]:
    rational = rationalize.strip_internal(row["rational_guard"])
    source = row["source_row"]
    return {
        "mesh_index": int(source["mesh_index"]),
        "mesh_interval": source["mesh_interval"],
        "S0_excludes_zero": bool(source["S0_excludes_zero"]),
        "direct_S1_guard_passes": bool(rational["direct_S1_guard_passes"]),
        "curvature_S2_guard_passes": bool(rational["curvature_S2_guard_passes"]),
        "direct_S1_mesh_guard_lower": rational["direct_S1_mesh_guard_lower"],
        "curvature_S2_mesh_guard_lower": rational["curvature_S2_mesh_guard_lower"],
        "S0_abs_lower": rational["S0_abs_lower"],
        "S1_abs_upper": rational["S1_abs_upper"],
        "S2_abs_upper": rational["S2_abs_upper"],
    }


def compact_guard_with_path(
    row: dict[str, Any],
    *,
    level: int,
    path: list[int],
) -> dict[str, Any]:
    record = compact_guard(row)
    record["refine_level"] = int(level)
    record["refine_path"] = [int(part) for part in path]
    return record


def merge_worst(
    records: list[dict[str, Any]],
    *,
    limit: int,
) -> list[dict[str, Any]]:
    return [
        item["record"]
        for item in sorted(records, key=lambda row: row["_guard_fraction"])[:limit]
    ]


def refine_interval_tree(
    *,
    args: argparse.Namespace,
    eval_args: argparse.Namespace,
    ctx: dict[str, Any],
    K: float,
    ell: float,
    receiver_delta: float,
    cell_idx: int,
    cell_lo: float,
    cell_hi: float,
    interval_lo: float,
    interval_hi: float,
    level: int,
    path: list[int],
) -> dict[str, Any]:
    submesh = np.linspace(float(interval_lo), float(interval_hi), int(args.refine_factor) + 1)
    skipped: list[dict[str, Any]] = []
    worst_failures: list[dict[str, Any]] = []
    min_guard: Fraction | None = None
    audited_count = 0
    leaf_pass_count = 0
    leaf_failure_count = 0
    max_level_reached = int(level)

    for sub_idx in range(int(args.refine_factor)):
        sub_path = [*path, int(sub_idx)]
        try:
            row = audit_row(
                args=eval_args,
                ctx=ctx,
                K=K,
                ell=ell,
                receiver_delta=receiver_delta,
                cell_idx=cell_idx,
                cell_lo=cell_lo,
                cell_hi=cell_hi,
                mesh=submesh,
                mesh_idx=sub_idx,
            )
        except ValueError as exc:
            skipped.append(
                {
                    "refine_level": int(level),
                    "refine_path": sub_path,
                    "sub_index": int(sub_idx),
                    "mesh_interval": [
                        float(submesh[sub_idx]),
                        float(submesh[sub_idx + 1]),
                    ],
                    "reason": str(exc),
                }
            )
            continue

        audited_count += 1
        row_guard = guard_fraction(row["rational_guard"])
        min_guard = row_guard if min_guard is None else min(min_guard, row_guard)

        if row["guard_passes"]:
            leaf_pass_count += 1
            continue

        if int(level) >= int(args.refine_levels):
            leaf_failure_count += 1
            worst_failures.append(
                {
                    "_guard_fraction": row_guard,
                    "record": compact_guard_with_path(
                        row,
                        level=int(level),
                        path=sub_path,
                    ),
                }
            )
            continue

        child = refine_interval_tree(
            args=args,
            eval_args=eval_args,
            ctx=ctx,
            K=K,
            ell=ell,
            receiver_delta=receiver_delta,
            cell_idx=cell_idx,
            cell_lo=cell_lo,
            cell_hi=cell_hi,
            interval_lo=float(submesh[sub_idx]),
            interval_hi=float(submesh[sub_idx + 1]),
            level=int(level) + 1,
            path=sub_path,
        )
        audited_count += int(child["audited_count"])
        leaf_pass_count += int(child["leaf_pass_count"])
        leaf_failure_count += int(child["leaf_failure_count"])
        max_level_reached = max(max_level_reached, int(child["max_level_reached"]))
        skipped.extend(child["skipped_rows"])
        worst_failures.extend(child["_worst_failure_records"])
        child_min = child["_min_guard_fraction"]
        if child_min is not None:
            min_guard = child_min if min_guard is None else min(min_guard, child_min)

    recovered = bool(leaf_pass_count > 0 and leaf_failure_count == 0 and not skipped)
    return {
        "audited_count": audited_count,
        "leaf_pass_count": leaf_pass_count,
        "leaf_failure_count": leaf_failure_count,
        "skipped_count": len(skipped),
        "skipped_rows": skipped,
        "recovered_by_refinement": recovered,
        "max_level_reached": max_level_reached,
        "min_refined_guard_lower": None
        if min_guard is None
        else rationalize.rational_to_record(min_guard),
        "worst_refined_failures": merge_worst(
            worst_failures,
            limit=int(args.worst_limit),
        ),
        "_min_guard_fraction": min_guard,
        "_worst_failure_records": worst_failures,
    }


def refine_coarse_failure(
    *,
    args: argparse.Namespace,
    ref_args: argparse.Namespace,
    ctx: dict[str, Any],
    K: float,
    ell: float,
    receiver_delta: float,
    cell_idx: int,
    cell_lo: float,
    cell_hi: float,
    coarse_mesh: np.ndarray,
    coarse_idx: int,
) -> dict[str, Any]:
    parent_lo = float(coarse_mesh[coarse_idx])
    parent_hi = float(coarse_mesh[coarse_idx + 1])
    tree = refine_interval_tree(
        args=args,
        eval_args=ref_args,
        ctx=ctx,
        K=K,
        ell=ell,
        receiver_delta=receiver_delta,
        cell_idx=cell_idx,
        cell_lo=cell_lo,
        cell_hi=cell_hi,
        interval_lo=parent_lo,
        interval_hi=parent_hi,
        level=1,
        path=[],
    )
    return {
        "parent_mesh_index": int(coarse_idx),
        "parent_mesh_interval": [parent_lo, parent_hi],
        "refine_factor": int(args.refine_factor),
        "refine_levels": int(args.refine_levels),
        "max_refine_level_reached": int(tree["max_level_reached"]),
        "refined_checked_count": int(tree["audited_count"]),
        "refined_skipped_count": int(tree["skipped_count"]),
        "refined_pass_count": int(tree["leaf_pass_count"]),
        "refined_failure_count": int(tree["leaf_failure_count"]),
        "recovered_by_refinement": bool(tree["recovered_by_refinement"]),
        "min_refined_guard_lower": tree["min_refined_guard_lower"],
        "skipped_refined_rows": tree["skipped_rows"][: int(args.worst_limit)],
        "worst_refined_failures": tree["worst_refined_failures"],
    }


def run_cell(
    *,
    args: argparse.Namespace,
    ref_args: argparse.Namespace,
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
    coarse_mesh = np.linspace(cell_lo, cell_hi, int(args.cert_na))

    coarse_rows: list[dict[str, Any]] = []
    coarse_skipped: list[dict[str, Any]] = []
    for mesh_idx in range(len(coarse_mesh) - 1):
        try:
            coarse_rows.append(
                audit_row(
                    args=args,
                    ctx=ctx,
                    K=K,
                    ell=ell,
                    receiver_delta=receiver_delta,
                    cell_idx=cell_idx,
                    cell_lo=cell_lo,
                    cell_hi=cell_hi,
                    mesh=coarse_mesh,
                    mesh_idx=mesh_idx,
                )
            )
        except ValueError as exc:
            coarse_skipped.append(
                {
                    "mesh_index": int(mesh_idx),
                    "mesh_interval": [
                        float(coarse_mesh[mesh_idx]),
                        float(coarse_mesh[mesh_idx + 1]),
                    ],
                    "reason": str(exc),
                }
            )

    failures = [row for row in coarse_rows if not row["guard_passes"]]
    refined = [
        refine_coarse_failure(
            args=args,
            ref_args=ref_args,
            ctx=ctx,
            K=K,
            ell=ell,
            receiver_delta=receiver_delta,
            cell_idx=cell_idx,
            cell_lo=cell_lo,
            cell_hi=cell_hi,
            coarse_mesh=coarse_mesh,
            coarse_idx=int(row["source_row"]["mesh_index"]),
        )
        for row in failures
    ]
    recovered = [row for row in refined if row["recovered_by_refinement"]]
    unresolved = [row for row in refined if not row["recovered_by_refinement"]]
    min_coarse_guard = None
    if coarse_rows:
        min_coarse_guard = rationalize.rational_to_record(
            min(guard_fraction(row["rational_guard"]) for row in coarse_rows)
        )

    return {
        "mode": "trackb_nonnode_refine_failures_cell",
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
        "refined_equivalent_cert_na": int(ref_args.cert_na),
        "refine_factor": int(args.refine_factor),
        "refine_levels": int(args.refine_levels),
        "cell": int(cell_idx),
        "cell_interval": [cell_lo, cell_hi],
        "dyadic_bits": int(args.dyadic_bits),
        "coarse_mesh_intervals_total": len(coarse_mesh) - 1,
        "coarse_mesh_intervals_checked": len(coarse_rows),
        "coarse_edge_jump_skipped_count": len(coarse_skipped),
        "coarse_pass_count": len(coarse_rows) - len(failures),
        "coarse_failure_count": len(failures),
        "coarse_min_guard_lower": min_coarse_guard,
        "coarse_skipped_mesh_intervals": coarse_skipped[: int(args.worst_limit)],
        "refined_parent_failure_count": len(refined),
        "refined_parent_recovered_count": len(recovered),
        "refined_parent_unresolved_count": len(unresolved),
        "refined_subintervals_checked": sum(
            row["refined_checked_count"] for row in refined
        ),
        "refined_subintervals_skipped": sum(
            row["refined_skipped_count"] for row in refined
        ),
        "refined_subintervals_failed": sum(
            row["refined_failure_count"] for row in refined
        ),
        "worst_coarse_failures": [
            compact_guard(row)
            for row in sorted(
                failures,
                key=lambda item: guard_fraction(item["rational_guard"]),
            )[: int(args.worst_limit)]
        ],
        "worst_unresolved_refined_parents": unresolved[: int(args.worst_limit)],
        "proof_status": (
            "diagnostic_only: adaptive refinement of coarse dyadic guard "
            "failures over the same floating source interval boxes; exact "
            "dyadic arithmetic checks only the guard layer after source boxes "
            "are accepted"
        ),
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
    ref_args = refined_args(args)
    cells = cell_sweep.parse_cell_spec(args.cells)
    cell_rows = [
        run_cell(
            args=args,
            ref_args=ref_args,
            ctx=ctx,
            K=K,
            ell=float(ell),
            receiver_delta=receiver_delta,
            cell_idx=cell_idx,
        )
        for cell_idx in cells
    ]
    return {
        "mode": "trackb_nonnode_refine_failures",
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
        "refine_factor": int(args.refine_factor),
        "refine_levels": int(args.refine_levels),
        "refined_equivalent_cert_na": int(ref_args.cert_na),
        "dyadic_bits": int(args.dyadic_bits),
        "raw_edge": [float(ctx["lo"]), float(ctx["hi"])],
        "effective_max_a": float(ctx["effective_max_a"]),
        "cells_requested": cells,
        "cells_total": len(cell_rows),
        "coarse_mesh_intervals_checked": sum(
            row["coarse_mesh_intervals_checked"] for row in cell_rows
        ),
        "coarse_mesh_intervals_skipped": sum(
            row["coarse_edge_jump_skipped_count"] for row in cell_rows
        ),
        "coarse_failure_count": sum(row["coarse_failure_count"] for row in cell_rows),
        "refined_parent_recovered_count": sum(
            row["refined_parent_recovered_count"] for row in cell_rows
        ),
        "refined_parent_unresolved_count": sum(
            row["refined_parent_unresolved_count"] for row in cell_rows
        ),
        "refined_subintervals_checked": sum(
            row["refined_subintervals_checked"] for row in cell_rows
        ),
        "refined_subintervals_skipped": sum(
            row["refined_subintervals_skipped"] for row in cell_rows
        ),
        "refined_subintervals_failed": sum(
            row["refined_subintervals_failed"] for row in cell_rows
        ),
        "cell_rows": cell_rows,
        "selection_rule": (
            "refine exactly those coarse rows whose exact dyadic direct or "
            "curvature guard fails"
        ),
        "proof_status": (
            "diagnostic_only: separates mesh-width halo failures from genuine "
            "edge-jump/source-box failures; not a proof of E5' and not a Lean "
            "certificate"
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
        help="comma list and/or Python-style ranges, e.g. 60,62 or 60:63",
    )
    parser.add_argument("--refine-factor", type=int, default=10)
    parser.add_argument("--refine-levels", type=int, default=1)
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
    parser.add_argument(
        "--curvature-factors",
        type=float,
        nargs="+",
        default=[10000.0],
        help="kept for audit namespace compatibility",
    )
    parser.add_argument(
        "--atom-samples",
        type=int,
        default=65,
        help="kept for audit namespace compatibility",
    )
    return parser.parse_args()


def main() -> None:
    print(json.dumps(run(parse_args()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
