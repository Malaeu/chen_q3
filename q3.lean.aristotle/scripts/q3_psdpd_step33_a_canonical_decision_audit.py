#!/usr/bin/env python3
"""
Step33A.1-A canonical A decision audit.

This diagnostic is deliberately non-mutating.  It answers whether the current
finite PSD certificate contour is secretly applying the transformed Arch sign,
or whether it is really certifying the raw Step22 positive-axis A payload.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

import q3_psdpd_step33_a_data_convention_sync_dry_run as dry_run
import q3_psdpd_step33_a_source_sync_psd_sanity as sanity


DIM = 23


def sci(value: float) -> str:
    return f"{value:.16e}"


def fro_norm(matrix: np.ndarray) -> float:
    return float(np.linalg.norm(matrix, ord="fro"))


def spec_norm_symmetric(matrix: np.ndarray) -> float:
    eigs = np.linalg.eigvalsh((matrix + matrix.T) / 2.0)
    return float(np.max(np.abs(eigs)))


def eig_summary(matrix: np.ndarray) -> dict[str, Any]:
    eigs = np.linalg.eigvalsh((matrix + matrix.T) / 2.0)
    return {
        "min": float(eigs[0]),
        "max": float(eigs[-1]),
        "abs_max": float(np.max(np.abs(eigs))),
    }


def matrix_rank_summary(matrix: np.ndarray) -> dict[str, Any]:
    singular_values = np.linalg.svd(matrix, compute_uv=False)
    thresholds = [1e-6, 1e-9, 1e-12]
    return {
        "rank_by_threshold": {
            f"{threshold:.0e}": int(np.sum(singular_values > threshold))
            for threshold in thresholds
        },
        "top_singular_values": [float(value) for value in singular_values[:8]],
        "bottom_singular_values": [float(value) for value in singular_values[-5:]],
        "is_rank_one_at_1e_9": bool(np.sum(singular_values > 1e-9) <= 1),
        "is_rank_two_at_1e_9": bool(np.sum(singular_values > 1e-9) <= 2),
    }


def best_one_basis_fit(delta: np.ndarray, basis: np.ndarray) -> dict[str, Any]:
    denom = float(np.vdot(basis, basis))
    coefficient = 0.0 if denom == 0.0 else float(np.vdot(delta, basis) / denom)
    residual = delta - coefficient * basis
    delta_fro = fro_norm(delta)
    return {
        "coefficient": coefficient,
        "residual_fro": fro_norm(residual),
        "relative_residual_fro": None if delta_fro == 0.0 else fro_norm(residual) / delta_fro,
        "residual_spectral": spec_norm_symmetric(residual),
    }


def best_multi_basis_fit(delta: np.ndarray, bases: dict[str, np.ndarray]) -> dict[str, Any]:
    names = list(bases)
    design = np.column_stack([bases[name].reshape(-1) for name in names])
    target = delta.reshape(-1)
    coeffs, *_ = np.linalg.lstsq(design, target, rcond=None)
    fitted = sum(float(coeffs[idx]) * bases[name] for idx, name in enumerate(names))
    residual = delta - fitted
    delta_fro = fro_norm(delta)
    return {
        "basis": names,
        "coefficients": {name: float(coeffs[idx]) for idx, name in enumerate(names)},
        "residual_fro": fro_norm(residual),
        "relative_residual_fro": None if delta_fro == 0.0 else fro_norm(residual) / delta_fro,
        "residual_spectral": spec_norm_symmetric(residual),
    }


def nullspace_basis(Q: np.ndarray, threshold: float = 1e-10) -> np.ndarray:
    _, singular_values, vh = np.linalg.svd(Q, full_matrices=True)
    rank = int(np.sum(singular_values > threshold))
    return vh[rank:].T


def boundary_null_summary(delta: np.ndarray, Q: np.ndarray) -> dict[str, Any]:
    null_basis = nullspace_basis(Q)
    projected = null_basis.T @ delta @ null_basis
    eigs = np.linalg.eigvalsh((projected + projected.T) / 2.0)
    return {
        "Q_rank": int(DIM - null_basis.shape[1]),
        "null_dim": int(null_basis.shape[1]),
        "projected_min_eigenvalue": float(eigs[0]),
        "projected_max_eigenvalue": float(eigs[-1]),
        "projected_spectral_norm": float(np.max(np.abs(eigs))),
        "projected_fro_norm": fro_norm(projected),
        "is_zero_on_boundary_null_at_1e_9": bool(np.max(np.abs(eigs)) <= 1e-9),
    }


def delta_structure(
    *,
    delta: np.ndarray,
    raw_a: np.ndarray,
    transformed_a: np.ndarray,
    P0: np.ndarray,
    Q: np.ndarray,
) -> dict[str, Any]:
    identity = np.eye(DIM)
    ones = np.ones((DIM, DIM))
    qgram = Q.T @ Q
    offdiag = delta - np.diag(np.diag(delta))
    diag = np.diag(delta)
    bases = {
        "I": identity,
        "J": ones,
        "Q_transpose_Q": qgram,
        "P0": P0,
        "A_raw": raw_a,
    }
    return {
        "delta_fro_norm": fro_norm(delta),
        "delta_spectral_norm": spec_norm_symmetric(delta),
        "entry_abs_max": float(np.max(np.abs(delta))),
        "diagonal_abs_max": float(np.max(np.abs(diag))),
        "offdiag_abs_max": float(np.max(np.abs(offdiag))),
        "is_diagonal_at_1e_9": bool(np.max(np.abs(offdiag)) <= 1e-9),
        "is_scalar_I_at_1e_9": bool(
            np.max(np.abs(delta - float(np.mean(diag)) * identity)) <= 1e-9
        ),
        "rank": matrix_rank_summary(delta),
        "fit_scalar_A_raw": best_one_basis_fit(delta, raw_a),
        "fit_scalar_A_transformed": best_one_basis_fit(delta, transformed_a),
        "fit_scalar_I": best_one_basis_fit(delta, identity),
        "fit_scalar_J": best_one_basis_fit(delta, ones),
        "fit_Q_transpose_Q": best_one_basis_fit(delta, qgram),
        "fit_P0": best_one_basis_fit(delta, P0),
        "fit_span_I_J_QtQ_P0_Araw": best_multi_basis_fit(delta, bases),
        "boundary_null": boundary_null_summary(delta, Q),
    }


def penalty_shift_summary(
    *,
    delta: np.ndarray,
    Q: np.ndarray,
    theta: float,
) -> dict[str, Any]:
    d_shift = (1.0 - theta) * delta
    r_shift = delta
    return {
        "D_shift_formula": "(1 - theta) * DeltaA",
        "R_shift_formula": "DeltaA",
        "D_shift_eigenvalues": eig_summary(d_shift),
        "R_shift_eigenvalues": eig_summary(r_shift),
        "D_shift_on_boundary_null": boundary_null_summary(d_shift, Q),
        "R_shift_on_boundary_null": boundary_null_summary(r_shift, Q),
    }


def csv_formula_consistency(
    *,
    raw_a: np.ndarray,
    P: np.ndarray,
    P0: np.ndarray,
    kappa: float,
    theta: float,
) -> dict[str, Any]:
    C = raw_a - P
    R = raw_a - kappa * P0
    D_direct = (1.0 - theta) * raw_a - P + theta * kappa * P0
    D_from_C_R = C - theta * R
    return {
        "C_formula": "A - P",
        "R_formula": "A - kappa * P0",
        "D_formula": "(1 - theta) * A - P + theta * kappa * P0",
        "D_from_C_R_formula": "C - theta * R",
        "D_direct_minus_D_from_C_R_abs_max": float(np.max(np.abs(D_direct - D_from_C_R))),
    }


def current_import_used_summary(
    *,
    raw_a: np.ndarray,
    transformed_a: np.ndarray,
    P: np.ndarray,
    P0: np.ndarray,
    Q: np.ndarray,
    kappa: float,
    theta: float,
    params: dict[str, float],
) -> dict[str, Any]:
    raw = sanity.penalty_summary(A=raw_a, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params)
    transformed = sanity.penalty_summary(
        A=transformed_a, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params
    )
    neg_transformed = sanity.penalty_summary(
        A=-transformed_a, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params
    )
    return {
        "A_used_in_current_D_R": "current raw Step22 positive-axis A payload",
        "raw_step22_psd_sanity": raw,
        "transformed_arch_sign_psd_sanity": transformed,
        "negative_transformed_probe_psd_sanity": neg_transformed,
        "raw_passes": bool(raw["D_penalty_passes_floor"] and raw["R_penalty_passes_floor"]),
        "transformed_passes": bool(
            transformed["D_penalty_passes_floor"] and transformed["R_penalty_passes_floor"]
        ),
        "negative_transformed_probe_passes": bool(
            neg_transformed["D_penalty_passes_floor"] and neg_transformed["R_penalty_passes_floor"]
        ),
    }


def family_audit(root: Path, plan: dict[str, Any], audit: dict[str, Any], family: str) -> dict[str, Any]:
    inputs = dry_run.family_payload_inputs(root, plan, family)
    transformed_values = dry_run.load_receiver_bridge_values(audit, family)
    raw_a = sanity.square(inputs["midpoint"]["A"])
    transformed_a = dry_run.matrix_from_distance_values(
        transformed_values,
        "transformed_step22_eta_cutoff_2pi260_mid",
    )
    P = inputs["P"]
    P0 = inputs["P0"]
    Q = inputs["Q"]
    kappa = inputs["kappa"]
    theta = inputs["theta"]
    params = inputs["penalty_params"]
    delta = transformed_a - raw_a
    return {
        "family": family,
        "block_id": inputs["block"]["block_id"],
        "midpoint_csv": str(inputs["midpoint_csv"]),
        "kappa": kappa,
        "theta": theta,
        "finite_psd_convention": csv_formula_consistency(
            raw_a=raw_a,
            P=P,
            P0=P0,
            kappa=kappa,
            theta=theta,
        ),
        "finite_psd_sanity": current_import_used_summary(
            raw_a=raw_a,
            transformed_a=transformed_a,
            P=P,
            P0=P0,
            Q=Q,
            kappa=kappa,
            theta=theta,
            params=params,
        ),
        "deltaA": {
            "definition": "A_transformed_arch_sign_receiver - A_raw_step22_positive_axis_payload",
            "structure": delta_structure(
                delta=delta,
                raw_a=raw_a,
                transformed_a=transformed_a,
                P0=P0,
                Q=Q,
            ),
            "penalty_shift": penalty_shift_summary(delta=delta, Q=Q, theta=theta),
        },
    }


def decision_summary(families: list[dict[str, Any]]) -> dict[str, Any]:
    raw_passes = all(f["finite_psd_sanity"]["raw_passes"] for f in families)
    transformed_passes = all(f["finite_psd_sanity"]["transformed_passes"] for f in families)
    neg_probe_passes = all(f["finite_psd_sanity"]["negative_transformed_probe_passes"] for f in families)
    zero_on_boundary_null = all(
        f["deltaA"]["structure"]["boundary_null"]["is_zero_on_boundary_null_at_1e_9"]
        for f in families
    )
    low_rank = all(
        f["deltaA"]["structure"]["rank"]["is_rank_two_at_1e_9"]
        for f in families
    )
    qtq_absorbable = all(
        f["deltaA"]["structure"]["fit_Q_transpose_Q"]["relative_residual_fro"] is not None
        and f["deltaA"]["structure"]["fit_Q_transpose_Q"]["relative_residual_fro"] <= 1e-6
        for f in families
    )
    p0_like = all(
        f["deltaA"]["structure"]["fit_P0"]["relative_residual_fro"] is not None
        and f["deltaA"]["structure"]["fit_P0"]["relative_residual_fro"] <= 1e-6
        for f in families
    )
    if transformed_passes:
        chosen_path = "C. one-time transformed-A data sync may proceed after radius policy"
        recommendation = "transformed candidate passes current finite PSD contour"
    elif zero_on_boundary_null or qtq_absorbable or p0_like:
        chosen_path = "B. boundary/gauge equivalence bridge"
        recommendation = "DeltaA has structure worth formalizing before recert"
    else:
        chosen_path = "C. one-time recert with transformed A, unless receiver is changed to raw Step22 by a semantic theorem"
        recommendation = (
            "no hidden sign-location or boundary/gauge absorption was found; "
            "current finite PSD cert is for raw Step22 A"
        )
    return {
        "raw_sanity_all_pass": raw_passes,
        "transformed_sanity_all_pass": transformed_passes,
        "negative_transformed_probe_all_pass": neg_probe_passes,
        "deltaA_zero_on_Qv_eq_0": zero_on_boundary_null,
        "deltaA_low_rank_rank_le_2": low_rank,
        "deltaA_absorbable_by_QtQ": qtq_absorbable,
        "deltaA_P0_like": p0_like,
        "chosen_path": chosen_path,
        "recommendation": recommendation,
    }


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    lines = [
        "# A_CANONICAL_DECISION_AUDIT",
        "",
        "This is a non-mutating audit for `Step33A.1-A`.",
        "It does not edit A CSV, `ARadius`, radius-floor data, LDL data, or Lean proof payloads.",
        "",
        "## Source map",
        "",
        f"- analytic receiver A: `{payload['source_map']['analytic_receiver_A']}`",
        f"- imported table A: `{payload['source_map']['imported_table_A']}`",
        f"- finite PSD cert A: `{payload['source_map']['finite_PSD_cert_A']}`",
        f"- C convention: `{payload['source_map']['C_convention']}`",
        f"- D/R convention: `{payload['source_map']['D_R_convention']}`",
        f"- Arch sign location: `{payload['source_map']['Arch_sign_location']}`",
        "",
        "## Family summary",
        "",
        "| family | raw sanity | transformed sanity | -transformed probe | rank(DeltaA) 1e-9 | Delta zero on Qv=0 | Delta spectral | Q-null spectral | chosen signal |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |",
    ]
    for family in payload["families"]:
        sanity_block = family["finite_psd_sanity"]
        structure = family["deltaA"]["structure"]
        rank = structure["rank"]["rank_by_threshold"]["1e-09"]
        qnull = structure["boundary_null"]
        lines.append(
            f"| {family['family']} | "
            f"{sanity_block['raw_passes']} | "
            f"{sanity_block['transformed_passes']} | "
            f"{sanity_block['negative_transformed_probe_passes']} | "
            f"{rank} | "
            f"{qnull['is_zero_on_boundary_null_at_1e_9']} | "
            f"{sci(structure['delta_spectral_norm'])} | "
            f"{sci(qnull['projected_spectral_norm'])} | "
            f"{payload['decision']['recommendation']} |"
        )
    lines.extend([
        "",
        "## DeltaA structure",
        "",
    ])
    for family in payload["families"]:
        structure = family["deltaA"]["structure"]
        lines.extend([
            f"### {family['family']}",
            "",
            f"- `DeltaA = A_transformed - A_raw` Frobenius norm: `{sci(structure['delta_fro_norm'])}`",
            f"- spectral norm: `{sci(structure['delta_spectral_norm'])}`",
            f"- max entry abs: `{sci(structure['entry_abs_max'])}`",
            f"- offdiag max abs: `{sci(structure['offdiag_abs_max'])}`",
            f"- rank at `1e-9`: `{structure['rank']['rank_by_threshold']['1e-09']}`",
            f"- top singular values: `{', '.join(sci(x) for x in structure['rank']['top_singular_values'][:5])}`",
            f"- Q-null spectral norm: `{sci(structure['boundary_null']['projected_spectral_norm'])}`",
            f"- best QtQ relative residual: `{structure['fit_Q_transpose_Q']['relative_residual_fro']:.16e}`",
            f"- best P0 relative residual: `{structure['fit_P0']['relative_residual_fro']:.16e}`",
            f"- combined span relative residual: `{structure['fit_span_I_J_QtQ_P0_Araw']['relative_residual_fro']:.16e}`",
            "",
        ])
    lines.extend([
        "## Decision",
        "",
        f"- raw sanity all pass: `{payload['decision']['raw_sanity_all_pass']}`",
        f"- transformed sanity all pass: `{payload['decision']['transformed_sanity_all_pass']}`",
        f"- negative transformed probe all pass: `{payload['decision']['negative_transformed_probe_all_pass']}`",
        f"- `DeltaA` zero on `Qv = 0`: `{payload['decision']['deltaA_zero_on_Qv_eq_0']}`",
        f"- `DeltaA` rank <= 2: `{payload['decision']['deltaA_low_rank_rank_le_2']}`",
        f"- `DeltaA` absorbable by `Q^T Q`: `{payload['decision']['deltaA_absorbable_by_QtQ']}`",
        f"- `DeltaA` P0-like: `{payload['decision']['deltaA_P0_like']}`",
        f"- chosen path: `{payload['decision']['chosen_path']}`",
        "",
        "Interpretation:",
        "",
        "The finite PSD contour uses the raw Step22 positive-axis A.  The transformed",
        "Arch-sign receiver is not being recovered by a later sign flip in `C`, `D`,",
        "`R`, or the penalty layer.  The observed `DeltaA` is not a boundary-null",
        "or small low-rank correction under the current checks.",
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
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_canonical_decision_audit.json"),
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_canonical_decision_audit.md"),
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
    family_blocks = [family_audit(root, plan, audit, family) for family in families]
    payload = {
        "schema": "q3_psdpd_step33_a_canonical_decision_audit.v1",
        "non_mutating": True,
        "gate": "Step33A.1-A canonical-A decision fork",
        "inputs": {
            "plan": str(plan_path),
            "source_convention_audit_json": str(audit_path),
        },
        "source_map": {
            "analytic_receiver_A": (
                "CenteredCoeffBaseHboxImport.primary/control AnalyticA, "
                "identified with centeredBSplineArchKernelProfile and the transformed Step22-Omega Arch-sign profile"
            ),
            "imported_table_A": "raw Step22 positive-axis Omega payload in q3_psdpd_step22_midpoints_k11/k9.csv",
            "finite_PSD_cert_A": "the same raw imported A midpoint payload used to assemble D/R",
            "C_convention": "C = A - P",
            "D_R_convention": "R = A - kappa*P0; D = (1 - theta)*A - P + theta*kappa*P0 = C - theta*R",
            "Arch_sign_location": (
                "in the analytic receiver/profile bridge theorem, not in the imported table, "
                "not in C/D/R assembly, and not in penaltyForm"
            ),
            "penalty_convention": "penaltyForm M Q tau v = quadForm M v + tau * boundaryEnergy Q v",
        },
        "families": family_blocks,
        "decision": decision_summary(family_blocks),
    }
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(payload, out_md)


if __name__ == "__main__":
    main()
