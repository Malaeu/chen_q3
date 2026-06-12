#!/usr/bin/env python3
"""
Step33A transformed-A finite recert feasibility dry-run.

This diagnostic is deliberately non-mutating.  It checks whether the canonical
transformed Arch-sign A has an obvious finite PSD route under the existing
split shape after varying the signed P0 coefficient and theta.

The key necessary condition is boundary-null positivity.  The penalty term
tau * Q^T Q vanishes on ker(Q), so no tau scan can repair a negative restricted
D or R matrix there.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

import q3_psdpd_step33_a_source_sync_psd_sanity as sanity


DIM = 23


def square_from_distance(values: dict[int, float]) -> np.ndarray:
    return np.array([[values[abs(i - j)] for j in range(DIM)] for i in range(DIM)], dtype=float)


def transformed_distance_values(audit: dict[str, Any], family: str) -> dict[int, float]:
    for block in audit["families"]:
        if block["family"] == family:
            return {
                int(row["index"]): float(row["lean_astar_full_even_mid"])
                for row in block["rows"]
            }
    raise ValueError(f"missing source-convention audit family: {family}")


def nullspace_basis(Q: np.ndarray, tol: float = 1e-10) -> np.ndarray:
    _u, singular_values, vh = np.linalg.svd(Q, full_matrices=True)
    rank = int(np.sum(singular_values > tol))
    return vh[rank:].T


def restricted_matrix(M: np.ndarray, N: np.ndarray) -> np.ndarray:
    return N.T @ ((M + M.T) / 2.0) @ N


def eig_min(M: np.ndarray) -> float:
    return float(np.linalg.eigvalsh((M + M.T) / 2.0)[0])


def eig_minmax(M: np.ndarray) -> dict[str, float]:
    eigs = np.linalg.eigvalsh((M + M.T) / 2.0)
    return {
        "min": float(eigs[0]),
        "max": float(eigs[-1]),
    }


def signed_kappa_grid(max_abs: float) -> list[float]:
    vals: set[float] = {0.0}
    for value in np.linspace(-1000.0, 1000.0, 801):
        vals.add(float(value))
    exp = -3
    while 10**exp <= max_abs:
        lo = 10**exp
        hi = min(10 ** (exp + 1), max_abs)
        for value in np.linspace(lo, hi, 60):
            vals.add(float(value))
            vals.add(float(-value))
        exp += 1
    vals.add(float(max_abs))
    vals.add(float(-max_abs))
    return sorted(vals)


def theta_grid() -> list[float]:
    vals = {float(value) for value in np.linspace(0.0, 1.0, 201)}
    vals.update({1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 2.5e-2, 5e-2, 7.5e-2})
    return sorted(vals)


def scan_boundary_null(
    *,
    A: np.ndarray,
    P: np.ndarray,
    P0: np.ndarray,
    Q: np.ndarray,
    max_abs_signed_kappa: float,
) -> dict[str, Any]:
    N = nullspace_basis(Q)
    An = restricted_matrix(A, N)
    Pn = restricted_matrix(P, N)
    P0n = restricted_matrix(P0, N)
    kgrid = signed_kappa_grid(max_abs_signed_kappa)
    tgrid = theta_grid()

    best_R = {"min_eig": -float("inf"), "signed_kappa": None}
    best_D = {"min_eig": -float("inf"), "signed_kappa": None, "theta": None}
    best_joint = {
        "objective_min_D_R": -float("inf"),
        "signed_kappa": None,
        "theta": None,
        "R_min_eig_on_kerQ": None,
        "D_min_eig_on_kerQ": None,
    }
    for signed_kappa in kgrid:
        Rn = An - signed_kappa * P0n
        rmin = eig_min(Rn)
        if rmin > best_R["min_eig"]:
            best_R = {"min_eig": rmin, "signed_kappa": signed_kappa}
        for theta in tgrid:
            Dn = (1.0 - theta) * An - Pn + theta * signed_kappa * P0n
            dmin = eig_min(Dn)
            if dmin > best_D["min_eig"]:
                best_D = {"min_eig": dmin, "signed_kappa": signed_kappa, "theta": theta}
            objective = min(rmin, dmin)
            if objective > best_joint["objective_min_D_R"]:
                best_joint = {
                    "objective_min_D_R": objective,
                    "signed_kappa": signed_kappa,
                    "theta": theta,
                    "R_min_eig_on_kerQ": rmin,
                    "D_min_eig_on_kerQ": dmin,
                }

    return {
        "necessary_condition": "D and R must be nonnegative on ker(Q); tau*Q^TQ is zero there",
        "Q_rank": int(DIM - N.shape[1]),
        "kerQ_dim": int(N.shape[1]),
        "A_on_kerQ": eig_minmax(An),
        "P_on_kerQ": eig_minmax(Pn),
        "P0_on_kerQ": eig_minmax(P0n),
        "scan_domain": {
            "signed_kappa_min": -max_abs_signed_kappa,
            "signed_kappa_max": max_abs_signed_kappa,
            "signed_kappa_count": len(kgrid),
            "theta_min": 0.0,
            "theta_max": 1.0,
            "theta_count": len(tgrid),
        },
        "best_R": best_R,
        "best_D": best_D,
        "best_joint_D_R": best_joint,
        "boundary_null_feasible_in_scan": bool(best_joint["objective_min_D_R"] >= 0.0),
    }


def current_penalty_at_old_params(
    *,
    A: np.ndarray,
    P: np.ndarray,
    P0: np.ndarray,
    Q: np.ndarray,
    kappa: float,
    theta: float,
    params: dict[str, float],
) -> dict[str, Any]:
    return sanity.penalty_summary(A=A, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params)


def family_payload(root: Path, plan: dict[str, Any], audit: dict[str, Any], family: str) -> dict[str, Any]:
    block = sanity.find_block(plan, family)
    midpoint_csv = sanity.resolve(root, Path(block["artifacts"]["midpoint_csv"]))
    midpoint = sanity.read_midpoint_csv(midpoint_csv)
    penalty_import = root / "q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean"
    params = sanity.load_penalty_params(penalty_import, sanity.FAMILY_META[family]["prefix"])
    A = square_from_distance(transformed_distance_values(audit, family))
    P = sanity.square(midpoint["P"])
    P0 = sanity.square(midpoint["P0"])
    Q = sanity.boundary(midpoint["Q"])
    kappa = float(block["parameters"]["kappa"])
    theta = float(block["parameters"]["theta"])
    return {
        "family": family,
        "block_id": block["block_id"],
        "current_kappa": kappa,
        "current_theta": theta,
        "current_penalty_params": params,
        "old_param_penalty_sanity": current_penalty_at_old_params(
            A=A, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params
        ),
        "boundary_null_scan": scan_boundary_null(
            A=A,
            P=P,
            P0=P0,
            Q=Q,
            max_abs_signed_kappa=1.0e7,
        ),
    }


def decision(families: list[dict[str, Any]]) -> dict[str, Any]:
    feasible = all(f["boundary_null_scan"]["boundary_null_feasible_in_scan"] for f in families)
    worst = min(
        families,
        key=lambda f: f["boundary_null_scan"]["best_joint_D_R"]["objective_min_D_R"],
    )
    return {
        "transformed_A_recert_feasible_in_scan": feasible,
        "tau_can_fix_boundary_null_failure": False,
        "reason": (
            "tau*Q^TQ vanishes on ker(Q); the best scanned joint D/R "
            "boundary-null minimum stays negative"
        ),
        "worst_family": worst["family"],
        "worst_joint_boundary_null_min": worst["boundary_null_scan"]["best_joint_D_R"][
            "objective_min_D_R"
        ],
        "next_action": (
            "do not start LDL/radius-floor migration; escalate semantic/route choice or search a new split/P0 model"
            if not feasible
            else "boundary-null scan is feasible; proceed to full penalty/radius dry-run"
        ),
    }


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    lines = [
        "# Step33A Transformed-A Recert Feasibility Dry-Run",
        "",
        "This is a non-mutating diagnostic.  It scans the transformed Arch-sign A",
        "against the existing split shape without editing CSV, radius-floor, or LDL data.",
        "",
        "Key point: `tau * Q^T Q` vanishes on `ker(Q)`, so boundary-null negativity",
        "cannot be repaired by increasing `tau`.",
        "",
        "## Summary",
        "",
        "| family | old-param D pass | old-param R pass | best joint ker(Q) min | signed kappa | theta | R ker(Q) min | D ker(Q) min | feasible |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for family in payload["families"]:
        old = family["old_param_penalty_sanity"]
        scan = family["boundary_null_scan"]
        best = scan["best_joint_D_R"]
        lines.append(
            f"| {family['family']} | "
            f"{old['D_penalty_passes_floor']} | "
            f"{old['R_penalty_passes_floor']} | "
            f"{best['objective_min_D_R']:.16e} | "
            f"{best['signed_kappa']:.16e} | "
            f"{best['theta']:.16e} | "
            f"{best['R_min_eig_on_kerQ']:.16e} | "
            f"{best['D_min_eig_on_kerQ']:.16e} | "
            f"{scan['boundary_null_feasible_in_scan']} |"
        )
    lines.extend([
        "",
        "## Decision",
        "",
        f"- transformed-A recert feasible in scan: `{payload['decision']['transformed_A_recert_feasible_in_scan']}`",
        f"- tau can fix boundary-null failure: `{payload['decision']['tau_can_fix_boundary_null_failure']}`",
        f"- worst family: `{payload['decision']['worst_family']}`",
        f"- worst joint boundary-null min: `{payload['decision']['worst_joint_boundary_null_min']:.16e}`",
        f"- next action: `{payload['decision']['next_action']}`",
        "",
        "Interpretation:",
        "",
        "Under the existing split shape, transformed A does not have an immediate",
        "finite PSD recert path.  The obstruction is already visible on `ker(Q)`,",
        "so increasing penalty weights cannot repair it.",
        "",
    ])
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
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/transformed_a_recert_feasibility.json"),
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/transformed_a_recert_feasibility.md"),
    )
    parser.add_argument("--families", type=str, default="primary,control")
    args = parser.parse_args()

    plan_path = sanity.resolve(root, args.plan)
    audit_path = sanity.resolve(root, args.audit_json)
    out_json = sanity.resolve(root, args.out_json)
    out_md = sanity.resolve(root, args.out_md)
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    families = [item.strip() for item in args.families.split(",") if item.strip()]
    family_blocks = [family_payload(root, plan, audit, family) for family in families]
    payload = {
        "schema": "q3_psdpd_step33_transformed_a_recert_feasibility.v1",
        "non_mutating": True,
        "gate": "Step33A.1-A transformed-A finite recert feasibility",
        "inputs": {
            "plan": str(plan_path),
            "source_convention_audit_json": str(audit_path),
        },
        "families": family_blocks,
        "decision": decision(family_blocks),
    }
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(payload, out_md)


if __name__ == "__main__":
    main()
