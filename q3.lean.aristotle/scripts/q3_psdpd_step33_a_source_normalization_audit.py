#!/usr/bin/env python3
"""
Step33A A-source normalization bridge audit.

This is a non-mutating diagnostic.  It compares the current imported Step22 A
table against the audited Step22-Omega and Q3.a_star finite-window candidates.

It does not edit CSV, radius, floor, LDL, or Lean proof files.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal
from pathlib import Path
from typing import Any

import numpy as np

import q3_psdpd_step33_a_source_sync_psd_sanity as sanity


DIM = 23
SAMPLED_SIGNED_DELTAS = (-2, -1, 0, 1, 2)


def decimal_to_float(x: Decimal) -> float:
    return float(x)


def row_value(row: dict[str, Any], key: str) -> Decimal:
    return Decimal(row[key])


def load_audit_family(audit: dict[str, Any], family: str) -> dict[int, dict[str, Decimal]]:
    for block in audit["families"]:
        if block["family"] == family:
            out: dict[int, dict[str, Decimal]] = {}
            for row in block["rows"]:
                idx = int(row["index"])
                q3_pos = row_value(row, "lean_astar_positive_mid")
                q3_full = row_value(row, "lean_astar_full_even_mid")
                step22_pos = row_value(row, "step22_positive_mid")
                step22_full = row_value(row, "step22_full_even_mid")
                out[idx] = {
                    "step22_positive": step22_pos,
                    "step22_full_even": step22_full,
                    "q3_astar_positive": q3_pos,
                    "q3_astar_full_even": q3_full,
                    "neg_q3_astar_positive": -q3_pos,
                    "neg_q3_astar_full_even": -q3_full,
                }
            return out
    raise ValueError(f"audit family not found: {family}")


def distance_vector(values: dict[int, Decimal], keys: dict[int, dict[str, Decimal]], key: str) -> np.ndarray:
    return np.array([decimal_to_float(keys[i][key]) for i in sorted(values)], dtype=float)


def target_vector(values: dict[int, Decimal]) -> np.ndarray:
    return np.array([decimal_to_float(values[i]) for i in sorted(values)], dtype=float)


def max_abs_error(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.max(np.abs(a - b)))


def fit_lambda(target: np.ndarray, candidate: np.ndarray) -> float:
    denom = float(candidate @ candidate)
    if denom == 0.0:
        return math.nan
    return float((target @ candidate) / denom)


def signed_delta_sample(
    *,
    imported: dict[int, Decimal],
    candidates: dict[int, dict[str, Decimal]],
    fitted: dict[str, float],
) -> list[dict[str, Any]]:
    rows = []
    for signed_delta in SAMPLED_SIGNED_DELTAS:
        idx = abs(signed_delta)
        imported_value = imported[idx]
        q3_full = candidates[idx]["q3_astar_full_even"]
        neg_q3_full = candidates[idx]["neg_q3_astar_full_even"]
        lambda_neg_q3_full = Decimal(str(fitted["lambda_neg_q3_astar_full_even"]))
        fitted_value = lambda_neg_q3_full * neg_q3_full
        rows.append({
            "signed_delta_index": signed_delta,
            "abs_distance_index": idx,
            "imported_A": f"{imported_value:.30e}",
            "step22_positive": f"{candidates[idx]['step22_positive']:.30e}",
            "step22_full_even": f"{candidates[idx]['step22_full_even']:.30e}",
            "q3_astar_full_even": f"{q3_full:.30e}",
            "neg_q3_astar_full_even": f"{neg_q3_full:.30e}",
            "imported_over_q3_astar_full_even": None if q3_full == 0 else f"{(imported_value / q3_full):.30e}",
            "imported_over_neg_q3_astar_full_even": None if neg_q3_full == 0 else f"{(imported_value / neg_q3_full):.30e}",
            "lambda_neg_q3_astar_full_even_fit_value": f"{fitted_value:.30e}",
            "lambda_neg_q3_astar_full_even_abs_error": f"{abs(imported_value - fitted_value):.30e}",
        })
    return rows


def candidate_matrix_from_distance_vector(values: np.ndarray) -> np.ndarray:
    return np.array([[values[abs(i - j)] for j in range(DIM)] for i in range(DIM)], dtype=float)


def psd_for_distance_candidate(
    *,
    root: Path,
    plan: dict[str, Any],
    penalty_import: Path,
    family: str,
    distance_values: np.ndarray,
) -> dict[str, Any]:
    block = sanity.find_block(plan, family)
    midpoint_csv = sanity.resolve(root, Path(block["artifacts"]["midpoint_csv"]))
    matrices = sanity.read_midpoint_csv(midpoint_csv)
    A = candidate_matrix_from_distance_vector(distance_values)
    P = sanity.square(matrices["P"])
    P0 = sanity.square(matrices["P0"])
    Q = sanity.boundary(matrices["Q"])
    params = sanity.load_penalty_params(penalty_import, sanity.FAMILY_META[family]["prefix"])
    return sanity.penalty_summary(
        A=A,
        P=P,
        P0=P0,
        Q=Q,
        kappa=float(Decimal(str(block["parameters"]["kappa"]))),
        theta=float(Decimal(str(block["parameters"]["theta"]))),
        params=params,
    )


def audit_family(
    *,
    root: Path,
    plan: dict[str, Any],
    audit: dict[str, Any],
    penalty_import: Path,
    family: str,
) -> dict[str, Any]:
    block = sanity.find_block(plan, family)
    midpoint_csv = sanity.resolve(root, Path(block["artifacts"]["midpoint_csv"]))
    matrices = sanity.read_midpoint_csv(midpoint_csv)
    imported = {
        i: matrices["A"][(0, i)]
        for i in range(DIM)
    }
    candidates = load_audit_family(audit, family)
    target = target_vector(imported)

    exact = []
    for key in (
        "step22_positive",
        "step22_full_even",
        "q3_astar_positive",
        "q3_astar_full_even",
        "neg_q3_astar_positive",
        "neg_q3_astar_full_even",
    ):
        vector = distance_vector(imported, candidates, key)
        exact.append({
            "formula": key,
            "max_abs_error": max_abs_error(target, vector),
            "mean_abs_error": float(np.mean(np.abs(target - vector))),
        })

    fitted: dict[str, float] = {}
    fitted_rows = []
    for key in (
        "q3_astar_positive",
        "q3_astar_full_even",
        "neg_q3_astar_positive",
        "neg_q3_astar_full_even",
    ):
        vector = distance_vector(imported, candidates, key)
        lam = fit_lambda(target, vector)
        fitted[f"lambda_{key}"] = lam
        scaled = lam * vector
        fitted_rows.append({
            "formula": f"lambda * {key}",
            "lambda": lam,
            "max_abs_error": max_abs_error(target, scaled),
            "mean_abs_error": float(np.mean(np.abs(target - scaled))),
        })

    best_exact = min(exact, key=lambda row: row["max_abs_error"])
    best_q3_fit = min(fitted_rows, key=lambda row: row["max_abs_error"])

    neg_q3_full = distance_vector(imported, candidates, "neg_q3_astar_full_even")
    lambda_neg_q3_full = fitted["lambda_neg_q3_astar_full_even"]
    lambda_neg_q3_full_psd = psd_for_distance_candidate(
        root=root,
        plan=plan,
        penalty_import=penalty_import,
        family=family,
        distance_values=lambda_neg_q3_full * neg_q3_full,
    )

    return {
        "family": family,
        "block_id": block["block_id"],
        "midpoint_csv": str(midpoint_csv),
        "receiver_source": "centeredBSplineArchKernelProfile / Q3.a_star",
        "imported_table_source": "Step22 Omega positive-axis payload",
        "psd_cert_source": "current imported A payload with derived C/R/D and finite penalty floors",
        "symbolic_relation": {
            "q3_a_star": "Q3.a_star(xi) = -2*pi*Omega(2*pi*xi)",
            "step22_integrand": "(ell/pi) * Omega(t) * E(t)^2 * cos(t*d)",
            "q3_receiver_integrand": "Q3.a_star(t) * ell * E(t)^2 * cos(t*d)",
            "eta_transform_effect": "eta=2*pi*xi changes sign, Jacobian, Omega argument, E argument, cosine argument, and finite-window cutoff variable",
        },
        "exact_hypotheses": exact,
        "fitted_hypotheses": fitted_rows,
        "best_exact_formula": best_exact,
        "best_q3_scalar_fit": best_q3_fit,
        "sampled_signed_deltas": signed_delta_sample(
            imported=imported,
            candidates=candidates,
            fitted=fitted,
        ),
        "psd_sanity_for_lambda_neg_q3_astar_full_even": lambda_neg_q3_full_psd,
    }


def fmt_float(value: float) -> str:
    return f"{value:.16e}"


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    lines = [
        "# Step33A A-source normalization audit",
        "",
        "This is a non-mutating diagnostic. It compares the imported Step22 A table",
        "against Step22-Omega and Q3.a_star finite-window candidates, including",
        "sign and scalar-fit probes.",
        "",
        "It does not edit CSV files, radius payloads, radius-floor data, LDL data,",
        "or Lean proof files.",
        "",
        "## Summary",
        "",
    ]
    for family in payload["families"]:
        lines.extend([
            f"### {family['family']}",
            "",
            f"- receiver source: `{family['receiver_source']}`",
            f"- imported table source: `{family['imported_table_source']}`",
            f"- PSD cert source: `{family['psd_cert_source']}`",
            f"- symbolic relation: `{family['symbolic_relation']['q3_a_star']}`",
            f"- best exact formula: `{family['best_exact_formula']['formula']}`",
            f"- best exact max error: `{fmt_float(family['best_exact_formula']['max_abs_error'])}`",
            f"- best Q3 scalar fit: `{family['best_q3_scalar_fit']['formula']}`",
            f"- best Q3 scalar lambda: `{fmt_float(family['best_q3_scalar_fit']['lambda'])}`",
            f"- best Q3 scalar max error: `{fmt_float(family['best_q3_scalar_fit']['max_abs_error'])}`",
            "",
            "| formula | max abs error | mean abs error |",
            "| --- | ---: | ---: |",
        ])
        for row in family["exact_hypotheses"]:
            lines.append(
                f"| {row['formula']} | {fmt_float(row['max_abs_error'])} | "
                f"{fmt_float(row['mean_abs_error'])} |"
            )
        lines.extend([
            "",
            "| fitted formula | lambda | max abs error | mean abs error |",
            "| --- | ---: | ---: | ---: |",
        ])
        for row in family["fitted_hypotheses"]:
            lines.append(
                f"| {row['formula']} | {fmt_float(row['lambda'])} | "
                f"{fmt_float(row['max_abs_error'])} | {fmt_float(row['mean_abs_error'])} |"
            )
        psd = family["psd_sanity_for_lambda_neg_q3_astar_full_even"]
        lines.extend([
            "",
            "PSD sanity for `lambda * neg_q3_astar_full_even`:",
            "",
            f"- D min eigenvalue: `{fmt_float(psd['D_penalty_min_eigenvalue'])}`",
            f"- D floor: `{fmt_float(psd['D_penalty_floor'])}`",
            f"- D passes: `{psd['D_penalty_passes_floor']}`",
            f"- R min eigenvalue: `{fmt_float(psd['R_penalty_min_eigenvalue'])}`",
            f"- R floor: `{fmt_float(psd['R_penalty_floor'])}`",
            f"- R passes: `{psd['R_penalty_passes_floor']}`",
            "",
            "Sampled signed delta rows:",
            "",
            "| signed delta | imported A | q3 full | -q3 full | imported / -q3 full | fitted error |",
            "| ---: | ---: | ---: | ---: | ---: | ---: |",
        ])
        for row in family["sampled_signed_deltas"]:
            lines.append(
                f"| {row['signed_delta_index']} | {row['imported_A']} | "
                f"{row['q3_astar_full_even']} | {row['neg_q3_astar_full_even']} | "
                f"{row['imported_over_neg_q3_astar_full_even']} | "
                f"{row['lambda_neg_q3_astar_full_even_abs_error']} |"
            )
        lines.append("")

    lines.extend([
        "## Interpretation",
        "",
        "The current imported A table matches the Step22 positive-axis Omega payload,",
        "not the literal current Q3.a_star receiver and not a constant scalar multiple",
        "of that receiver at useful accuracy. The sign probe is still valuable: it",
        "shows the finite PSD contour prefers the opposite Arch sign from the naive",
        "Q3.a_star migration, but the table itself is not simply `-Q3.a_star`.",
        "",
        "The next proof target should therefore be a source-normalization bridge,",
        "not a data mutation.  The bridge must account for sign, eta=2*pi*xi,",
        "Jacobian, packet-frequency, cosine-argument, and positive/full-window",
        "conventions before any A payload generation resumes.",
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
        "--source-audit-json",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_convention_audit.json"),
    )
    parser.add_argument(
        "--penalty-import",
        type=Path,
        default=Path("q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean"),
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_normalization_audit.json"),
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_normalization_audit.md"),
    )
    args = parser.parse_args()

    plan_path = sanity.resolve(root, args.plan)
    audit_path = sanity.resolve(root, args.source_audit_json)
    penalty_import = sanity.resolve(root, args.penalty_import)
    out_json = sanity.resolve(root, args.out_json)
    out_md = sanity.resolve(root, args.out_md)

    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    payload = {
        "schema": "q3_psdpd_step33_a_source_normalization_audit.v1",
        "inputs": {
            "plan": str(plan_path),
            "source_audit_json": str(audit_path),
            "penalty_import": str(penalty_import),
        },
        "families": [
            audit_family(
                root=root,
                plan=plan,
                audit=audit,
                penalty_import=penalty_import,
                family="primary",
            ),
            audit_family(
                root=root,
                plan=plan,
                audit=audit,
                penalty_import=penalty_import,
                family="control",
            ),
        ],
    }
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(payload, out_md)


if __name__ == "__main__":
    main()
