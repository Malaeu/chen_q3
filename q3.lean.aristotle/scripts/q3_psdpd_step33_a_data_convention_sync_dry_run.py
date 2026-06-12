#!/usr/bin/env python3
"""
Step33A A data-convention sync dry-run.

This diagnostic is deliberately non-mutating.  It evaluates the next candidate
A convention after the Lean bridge

  centeredBSplineArchKernelProfile
    = step22OmegaEtaTransformedProfileWithArchSign

has been proved.  The candidate is the transformed Step22-Omega source with the
Arch sign, not a raw Q3.a_star data migration and not a -Q3.a_star scalar fit.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from decimal import Decimal
from pathlib import Path
from typing import Any

import numpy as np
from flint import acb, arb, ctx

import q3_psdpd_step33_a_source_sync_psd_sanity as sanity
from q3_psdpd_step19_entry_radii import decimal_grid_centers, set_precision, spline_packet_ball
from q3_psdpd_step21_p0_interval import ball_to_mid_rad
from q3_psdpd_step22_arch_interval import sinc_acb


DIM = 23
TWO_PI_DEC = Decimal("6.2831853071795864769252867665590057683943387987502")


def decimal_range(start: Decimal, stop: Decimal, step: Decimal) -> list[Decimal]:
    if step <= 0:
        raise ValueError("step must be positive")
    out: list[Decimal] = []
    x = start
    while x < stop:
        out.append(x)
        x += step
    out.append(stop)
    return out


def integrate_chunks(
    f,
    *,
    cutoff_t: Decimal,
    chunk_size: Decimal,
    rel_tol: str,
    abs_tol: str,
    deg_limit: int,
    eval_limit: int,
    depth_limit: int,
) -> acb:
    total = acb(0)
    points = decimal_range(Decimal(0), cutoff_t, chunk_size)
    for left, right in zip(points[:-1], points[1:]):
        total += acb.integral(
            f,
            arb(str(left)),
            arb(str(right)),
            rel_tol=arb(rel_tol),
            abs_tol=arb(abs_tol),
            deg_limit=deg_limit,
            eval_limit=eval_limit,
            depth_limit=depth_limit,
        )
    return total


def read_radius_csv(path: Path) -> dict[str, dict[tuple[int, int], Decimal]]:
    out: dict[str, dict[tuple[int, int], Decimal]] = {}
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            matrix = row["matrix"]
            i = int(row["i"])
            j = int(row["j"])
            out.setdefault(matrix, {})[(i, j)] = Decimal(row["rad"])
    return out


def decimal_to_sci(value: Decimal, digits: int = 30) -> str:
    return f"{value:.{digits}e}"


def float_to_sci(value: float) -> str:
    return f"{value:.16e}"


def transformed_step22_integrand(*, k_spline: int, ell: str, d: Decimal, sinc_terms: int):
    ell_acb = acb(arb(ell))
    d_acb = acb(arb(str(d)))
    two = acb(2)
    pi_acb = acb(arb.pi())
    two_pi = two * pi_acb
    i_unit = acb(0, 1)
    s_k, c_k = spline_packet_ball(k_spline)
    s_acb = acb(s_k)
    norm_acb = acb(1) / (acb(s_k) * acb(c_k))
    sinc_power = 2 * k_spline + 2
    log_pi = arb.pi().log()

    def f(eta: acb, analytic: bool) -> acb:
        z = acb(arb("0.25")) + i_unit * eta / two
        omega = z.digamma().real - log_pi
        xi = eta / two_pi
        x = ell_acb * xi / (two * s_acb)
        e2 = norm_acb * (sinc_acb(x, sinc_terms) ** sinc_power)
        return -acb(omega) * ell_acb * (xi * d_acb).cos() * e2

    return f


def load_receiver_bridge_values(audit: dict[str, Any], family: str) -> dict[int, dict[str, Decimal]]:
    for block in audit["families"]:
        if block["family"] == family:
            out: dict[int, dict[str, Decimal]] = {}
            for row in block["rows"]:
                idx = int(row["index"])
                out[idx] = {
                    "distance": Decimal(row["distance"]),
                    "transformed_step22_eta_cutoff_2pi260_mid": Decimal(row["lean_astar_full_even_mid"]),
                    "transformed_step22_eta_cutoff_2pi260_rad": Decimal(row["lean_astar_positive_rad"]) * Decimal(2),
                    "raw_step22_positive_mid": Decimal(row["step22_positive_mid"]),
                    "raw_step22_full_even_mid": Decimal(row["step22_full_even_mid"]),
                }
            if set(out) != set(range(DIM)):
                missing = sorted(set(range(DIM)) - set(out))
                raise ValueError(f"audit family {family} missing distance rows: {missing}")
            return out
    raise ValueError(f"audit family not found: {family}")


def matrix_from_distance_values(values: dict[int, Decimal], key: str) -> np.ndarray:
    return np.array(
        [[float(values[abs(i - j)][key]) for j in range(DIM)] for i in range(DIM)],
        dtype=float,
    )


def family_payload_inputs(root: Path, plan: dict[str, Any], family: str) -> dict[str, Any]:
    block = sanity.find_block(plan, family)
    midpoint_csv = sanity.resolve(root, Path(block["artifacts"]["midpoint_csv"]))
    radius_csv = sanity.resolve(root, Path(block["artifacts"]["radius_csv"]))
    midpoint = sanity.read_midpoint_csv(midpoint_csv)
    radius = read_radius_csv(radius_csv)
    penalty_import = root / "q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean"
    params = sanity.load_penalty_params(penalty_import, sanity.FAMILY_META[family]["prefix"])
    return {
        "block": block,
        "midpoint_csv": midpoint_csv,
        "radius_csv": radius_csv,
        "midpoint": midpoint,
        "radius": radius,
        "P": sanity.square(midpoint["P"]),
        "P0": sanity.square(midpoint["P0"]),
        "Q": sanity.boundary(midpoint["Q"]),
        "kappa": float(Decimal(str(block["parameters"]["kappa"]))),
        "theta": float(Decimal(str(block["parameters"]["theta"]))),
        "penalty_params": params,
    }


def current_imported_distance_values(payload_inputs: dict[str, Any]) -> dict[int, Decimal]:
    return {i: payload_inputs["midpoint"]["A"][(0, i)] for i in range(DIM)}


def current_imported_radius_values(payload_inputs: dict[str, Any]) -> dict[int, Decimal]:
    return {i: payload_inputs["radius"]["A"][(0, i)] for i in range(DIM)}


def penalty_block(
    *,
    A: np.ndarray,
    payload_inputs: dict[str, Any],
) -> dict[str, Any]:
    return sanity.penalty_summary(
        A=A,
        P=payload_inputs["P"],
        P0=payload_inputs["P0"],
        Q=payload_inputs["Q"],
        kappa=payload_inputs["kappa"],
        theta=payload_inputs["theta"],
        params=payload_inputs["penalty_params"],
    )


def radius_reuse_probe(
    *,
    current_mid: dict[int, Decimal],
    current_radius: dict[int, Decimal],
    transformed: dict[int, dict[str, Decimal]],
) -> dict[str, Any]:
    rows = []
    for idx in range(DIM):
        transformed_mid = transformed[idx]["transformed_step22_eta_cutoff_2pi260_mid"]
        center_error = abs(transformed_mid - current_mid[idx])
        current_rad = current_radius[idx]
        transformed_finite_rad = transformed[idx]["transformed_step22_eta_cutoff_2pi260_rad"]
        rows.append({
            "index": idx,
            "distance": str(transformed[idx]["distance"]),
            "current_raw_step22_mid": decimal_to_sci(current_mid[idx]),
            "transformed_step22_mid": decimal_to_sci(transformed_mid),
            "center_error": decimal_to_sci(center_error),
            "current_raw_ARadius": decimal_to_sci(current_rad),
            "bridge_finite_numeric_radius": decimal_to_sci(transformed_finite_rad, digits=6),
            "center_error_le_current_radius": bool(center_error <= current_rad),
        })
    worst = max(rows, key=lambda row: Decimal(row["center_error"]) - Decimal(row["current_raw_ARadius"]))
    return {
        "current_raw_radius_reuse_passes": all(row["center_error_le_current_radius"] for row in rows),
        "transformed_radius_policy_exists": False,
        "required_action": "generate transformed Step22-Omega A radius data before local recenter containment can be closed",
        "worst_current_radius_reuse_row": worst,
        "rows": rows,
    }


def direct_eta_samples(
    *,
    family: str,
    values: dict[int, dict[str, Decimal]],
    k_spline: int,
    ell: str,
    sample_indices: list[int],
    cutoff_xi: Decimal,
    raw_eta_cutoff: Decimal,
    chunk_size: Decimal,
    args: argparse.Namespace,
) -> list[dict[str, Any]]:
    receiver_eta_cutoff = TWO_PI_DEC * cutoff_xi
    rows = []
    for idx in sample_indices:
        if idx not in values:
            raise ValueError(f"sample index {idx} not available for {family}")
        distance = values[idx]["distance"]
        f = transformed_step22_integrand(
            k_spline=k_spline,
            ell=ell,
            d=distance,
            sinc_terms=args.sinc_terms,
        )
        raw_window_val = Decimal(2) * Decimal(str(ball_to_mid_rad(
            integrate_chunks(
                f,
                cutoff_t=raw_eta_cutoff,
                chunk_size=chunk_size,
                rel_tol=args.rel_tol,
                abs_tol=args.abs_tol,
                deg_limit=args.deg_limit,
                eval_limit=args.eval_limit,
                depth_limit=args.depth_limit,
            ).real
        )[0]))
        receiver_window_ball = integrate_chunks(
            f,
            cutoff_t=receiver_eta_cutoff,
            chunk_size=chunk_size,
            rel_tol=args.rel_tol,
            abs_tol=args.abs_tol,
            deg_limit=args.deg_limit,
            eval_limit=args.eval_limit,
            depth_limit=args.depth_limit,
        ).real
        receiver_mid_raw, receiver_rad_raw = ball_to_mid_rad(receiver_window_ball)
        receiver_mid = Decimal(2) * Decimal(str(receiver_mid_raw))
        receiver_rad = Decimal(2) * Decimal(str(receiver_rad_raw))
        bridge_mid = values[idx]["transformed_step22_eta_cutoff_2pi260_mid"]
        rows.append({
            "index": idx,
            "distance": str(distance),
            "raw_eta_260_transformed_full_even_mid": decimal_to_sci(raw_window_val),
            "eta_2pi_xi260_transformed_full_even_mid": decimal_to_sci(receiver_mid),
            "eta_2pi_xi260_transformed_full_even_rad": decimal_to_sci(receiver_rad, digits=6),
            "bridge_receiver_mid_from_existing_audit": decimal_to_sci(bridge_mid),
            "direct_eta_minus_bridge_abs": decimal_to_sci(abs(receiver_mid - bridge_mid), digits=6),
        })
    return rows


def audit_family(
    *,
    root: Path,
    plan: dict[str, Any],
    audit: dict[str, Any],
    family: str,
    sample_indices: list[int],
    args: argparse.Namespace,
) -> dict[str, Any]:
    payload_inputs = family_payload_inputs(root, plan, family)
    block = payload_inputs["block"]
    transformed = load_receiver_bridge_values(audit, family)
    current_mid = current_imported_distance_values(payload_inputs)
    current_radius = current_imported_radius_values(payload_inputs)

    current_a = sanity.square(payload_inputs["midpoint"]["A"])
    transformed_a = matrix_from_distance_values(transformed, "transformed_step22_eta_cutoff_2pi260_mid")
    raw_full_even_a = matrix_from_distance_values(transformed, "raw_step22_full_even_mid")

    center_errors = [
        abs(transformed[idx]["transformed_step22_eta_cutoff_2pi260_mid"] - current_mid[idx])
        for idx in range(DIM)
    ]
    worst_idx = max(range(DIM), key=lambda idx: center_errors[idx])

    return {
        "family": family,
        "block_id": block["block_id"],
        "k_spline": int(block["parameters"]["k_spline"]),
        "ell": str(block["parameters"]["ell"]),
        "midpoint_csv": str(payload_inputs["midpoint_csv"]),
        "radius_csv": str(payload_inputs["radius_csv"]),
        "candidate_name": "A_transformed_from_rawStep22",
        "candidate_convention": "Step22 Omega eta source with Arch sign, eta=2*pi*xi, cosine and packet argument transformed",
        "not_candidate": [
            "raw Q3.a_star migration",
            "-Q3.a_star scalar fit",
            "ARadius widening patch",
        ],
        "center_comparison": {
            "max_abs_current_raw_step22_vs_transformed": decimal_to_sci(center_errors[worst_idx]),
            "worst_index": worst_idx,
            "worst_distance": str(transformed[worst_idx]["distance"]),
            "current_raw_step22_mid": decimal_to_sci(current_mid[worst_idx]),
            "transformed_step22_mid": decimal_to_sci(
                transformed[worst_idx]["transformed_step22_eta_cutoff_2pi260_mid"]
            ),
        },
        "psd_sanity": {
            "current_raw_step22_import": penalty_block(A=current_a, payload_inputs=payload_inputs),
            "raw_step22_full_even_variant": penalty_block(A=raw_full_even_a, payload_inputs=payload_inputs),
            "transformed_step22_arch_sign_candidate": penalty_block(A=transformed_a, payload_inputs=payload_inputs),
            "negative_transformed_step22_arch_sign_probe": penalty_block(A=-transformed_a, payload_inputs=payload_inputs),
        },
        "radius_reuse_probe": radius_reuse_probe(
            current_mid=current_mid,
            current_radius=current_radius,
            transformed=transformed,
        ),
        "direct_eta_samples": direct_eta_samples(
            family=family,
            values=transformed,
            k_spline=int(block["parameters"]["k_spline"]),
            ell=str(block["parameters"]["ell"]),
            sample_indices=sample_indices,
            cutoff_xi=Decimal(args.cutoff_xi),
            raw_eta_cutoff=Decimal(args.raw_eta_cutoff),
            chunk_size=Decimal(args.chunk_size),
            args=args,
        ) if args.direct_eta_samples else [],
    }


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    lines = [
        "# Step33A A data-convention sync dry-run",
        "",
        "This is a non-mutating diagnostic for `Step33A.1-A-data-convention-sync`.",
        "It uses the convention proved by",
        "`centeredBSplineArchKernelProfile_eq_step22OmegaEtaTransformedProfileWithArchSign`.",
        "",
        "It does not edit A CSV files, `ARadius`, radius-floor data, LDL data, or Lean proof payloads.",
        "",
        "## Summary",
        "",
    ]
    for family in payload["families"]:
        psd = family["psd_sanity"]
        transformed = psd["transformed_step22_arch_sign_candidate"]
        neg_probe = psd["negative_transformed_step22_arch_sign_probe"]
        raw = psd["current_raw_step22_import"]
        radius_probe = family["radius_reuse_probe"]
        lines.extend([
            f"### {family['family']}",
            "",
            f"- candidate: `{family['candidate_name']}`",
            f"- convention: `{family['candidate_convention']}`",
            f"- max current raw-vs-transformed center error: `{family['center_comparison']['max_abs_current_raw_step22_vs_transformed']}`",
            f"- worst distance index: `{family['center_comparison']['worst_index']}`",
            f"- worst distance: `{family['center_comparison']['worst_distance']}`",
            f"- current raw Step22 D pass: `{raw['D_penalty_passes_floor']}`",
            f"- transformed candidate D pass: `{transformed['D_penalty_passes_floor']}`",
            f"- transformed candidate D min eig: `{float_to_sci(transformed['D_penalty_min_eigenvalue'])}`",
            f"- transformed candidate D floor: `{float_to_sci(transformed['D_penalty_floor'])}`",
            f"- transformed candidate R pass: `{transformed['R_penalty_passes_floor']}`",
            f"- negative transformed sign probe D pass: `{neg_probe['D_penalty_passes_floor']}`",
            f"- current raw radius reuse passes: `{radius_probe['current_raw_radius_reuse_passes']}`",
            f"- transformed radius policy exists: `{radius_probe['transformed_radius_policy_exists']}`",
            "",
        ])
        if family["direct_eta_samples"]:
            lines.extend([
                "Direct eta samples:",
                "",
                "| index | distance | eta 260 transformed | eta 2pi*260 transformed | bridge receiver | direct-bridge abs |",
                "| ---: | ---: | ---: | ---: | ---: | ---: |",
            ])
            for row in family["direct_eta_samples"]:
                lines.append(
                    f"| {row['index']} | {row['distance']} | "
                    f"{row['raw_eta_260_transformed_full_even_mid']} | "
                    f"{row['eta_2pi_xi260_transformed_full_even_mid']} | "
                    f"{row['bridge_receiver_mid_from_existing_audit']} | "
                    f"{row['direct_eta_minus_bridge_abs']} |"
                )
            lines.append("")
    lines.extend([
        "## Decision",
        "",
    ])
    transformed_passes = all(
        family["psd_sanity"]["transformed_step22_arch_sign_candidate"]["D_penalty_passes_floor"]
        and family["psd_sanity"]["transformed_step22_arch_sign_candidate"]["R_penalty_passes_floor"]
        for family in payload["families"]
    )
    if transformed_passes:
        lines.extend([
            "The transformed Step22-Omega candidate passes midpoint penalty sanity.",
            "The next action is a one-time A-dependent data sync with a transformed radius policy.",
        ])
    else:
        lines.extend([
            "The transformed Step22-Omega candidate does not pass midpoint penalty sanity.",
            "Do not migrate A data yet.  Keep the source bridge, but escalate the finite PSD",
            "sign/convention contour before any CSV/radius-floor/LDL rebuild.",
        ])
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    root = sanity.repo_root_from_cwd()
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--plan",
        type=Path,
        default=Path("q3.lean.aristotle/docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json"),
    )
    parser.add_argument(
        "--audit-json",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_convention_audit.json"),
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_data_convention_sync_dry_run.json"),
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_data_convention_sync_dry_run.md"),
    )
    parser.add_argument("--families", type=str, default="primary,control")
    parser.add_argument("--sample-indices", type=str, default="0,1,2")
    parser.add_argument("--direct-eta-samples", action="store_true")
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--cutoff-xi", type=str, default="260")
    parser.add_argument("--raw-eta-cutoff", type=str, default="260")
    parser.add_argument("--chunk-size", type=str, default="20")
    parser.add_argument("--rel-tol", type=str, default="1e-35")
    parser.add_argument("--abs-tol", type=str, default="1e-35")
    parser.add_argument("--deg-limit", type=int, default=192)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=128)
    parser.add_argument("--sinc-terms", type=int, default=64)
    args = parser.parse_args()

    set_precision(args.arb_prec)
    ctx.dps = max(50, args.arb_prec // 3)

    plan_path = sanity.resolve(root, args.plan)
    audit_path = sanity.resolve(root, args.audit_json)
    out_json = sanity.resolve(root, args.out_json)
    out_md = sanity.resolve(root, args.out_md)
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    families = [item.strip() for item in args.families.split(",") if item.strip()]
    sample_indices = [int(item.strip()) for item in args.sample_indices.split(",") if item.strip()]

    payload = {
        "schema": "q3_psdpd_step33_a_data_convention_sync_dry_run.v1",
        "non_mutating": True,
        "closed_prerequisite": "centeredBSplineArchKernelProfile_eq_step22OmegaEtaTransformedProfileWithArchSign",
        "gate": "Step33A.1-A-data-convention-sync",
        "inputs": {
            "plan": str(plan_path),
            "audit_json": str(audit_path),
        },
        "parameters": {
            "direct_eta_samples": args.direct_eta_samples,
            "sample_indices": sample_indices,
            "cutoff_xi": args.cutoff_xi,
            "receiver_eta_cutoff": str(TWO_PI_DEC * Decimal(args.cutoff_xi)),
            "raw_eta_cutoff": args.raw_eta_cutoff,
            "chunk_size": args.chunk_size,
            "arb_prec": args.arb_prec,
            "rel_tol": args.rel_tol,
            "abs_tol": args.abs_tol,
        },
        "families": [
            audit_family(
                root=root,
                plan=plan,
                audit=audit,
                family=family,
                sample_indices=sample_indices,
                args=args,
            )
            for family in families
        ],
    }
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(payload, out_md)


if __name__ == "__main__":
    main()
