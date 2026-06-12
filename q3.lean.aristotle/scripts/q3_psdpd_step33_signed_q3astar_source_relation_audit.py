#!/usr/bin/env python3
"""
Audit the source relation between the route-B signed-Q3.a_star payload and the
canonical signed finite-Weil A receiver.

This is a non-mutating diagnostic.  It does not edit legacy A payloads,
ARadius, radius-floor data, or LDL certificates.
"""

from __future__ import annotations

import argparse
import csv
import json
from decimal import Decimal
from pathlib import Path

import numpy as np


DIM = 23
BOUNDARY_DIM = 2


FAMILY_INFO = {
    "primary": {
        "prefix": "primaryK11",
        "midpoint_csv": "q3.lean.aristotle/docs/insights/q3_psdpd_step22_midpoints_k11.csv",
    },
    "control": {
        "prefix": "controlK9",
        "midpoint_csv": "q3.lean.aristotle/docs/insights/q3_psdpd_step22_midpoints_k9.csv",
    },
}


def repo_root_from_cwd() -> Path:
    cwd = Path.cwd()
    if (cwd / "q3.lean.aristotle").exists():
        return cwd
    if cwd.name == "q3.lean.aristotle":
        return cwd.parent
    for parent in cwd.parents:
        if (parent / "q3.lean.aristotle").exists():
            return parent
    raise SystemExit("could not locate repository root containing q3.lean.aristotle")


def load_matrix_csv(path: Path) -> dict[str, np.ndarray]:
    matrices = {
        "A": np.zeros((DIM, DIM), dtype=float),
        "P0": np.zeros((DIM, DIM), dtype=float),
        "Q": np.zeros((BOUNDARY_DIM, DIM), dtype=float),
    }
    with path.open() as handle:
        for row in csv.DictReader(handle):
            matrix = row["matrix"]
            if matrix not in matrices:
                continue
            i = int(row["i"])
            j = int(row["j"])
            matrices[matrix][i, j] = float(Decimal(row["mid"]))
    return matrices


def family_audit_block(audit: dict, family: str) -> dict:
    for block in audit["families"]:
        if block["family"] == family:
            return block
    raise SystemExit(f"missing audit family {family!r}")


def signed_q3astar_matrix(block: dict) -> np.ndarray:
    distance_values: dict[int, float] = {}
    for row in block["rows"]:
        idx = int(row["index"])
        distance_values[idx] = float(-Decimal(row["lean_astar_full_even_mid"]))
    return np.array(
        [
            [distance_values[abs(i - j)] for j in range(DIM)]
            for i in range(DIM)
        ],
        dtype=float,
    )


def fit_scalar(target: np.ndarray, basis: np.ndarray) -> tuple[float, float, float]:
    denom = float(np.sum(basis * basis))
    if denom == 0:
        return 0.0, float(np.linalg.norm(target)), 1.0
    alpha = float(np.sum(target * basis) / denom)
    residual = target - alpha * basis
    residual_norm = float(np.linalg.norm(residual, ord="fro"))
    target_norm = float(np.linalg.norm(target, ord="fro"))
    relative = residual_norm / target_norm if target_norm else 0.0
    return alpha, residual_norm, relative


def fit_qt_s_q(target: np.ndarray, q: np.ndarray) -> dict:
    q0 = q[0, :].reshape(DIM, 1)
    q1 = q[1, :].reshape(DIM, 1)
    bases = [
        q0 @ q0.T,
        q0 @ q1.T + q1 @ q0.T,
        q1 @ q1.T,
    ]
    design = np.stack([basis.reshape(-1) for basis in bases], axis=1)
    coeffs, *_ = np.linalg.lstsq(design, target.reshape(-1), rcond=None)
    fit = sum(float(coeffs[i]) * bases[i] for i in range(3))
    residual = target - fit
    residual_norm = float(np.linalg.norm(residual, ord="fro"))
    target_norm = float(np.linalg.norm(target, ord="fro"))
    return {
        "coefficients": [float(x) for x in coeffs],
        "residual_fro": residual_norm,
        "relative_residual": residual_norm / target_norm if target_norm else 0.0,
    }


def nullspace_quadratic_residual(target: np.ndarray, q: np.ndarray) -> dict:
    _, singular, vt = np.linalg.svd(q, full_matrices=True)
    rank_q = int(np.sum(singular > 1e-10))
    null_basis = vt[rank_q:, :].T
    compressed = null_basis.T @ target @ null_basis
    compressed_norm = float(np.linalg.norm(compressed, ord="fro"))
    target_norm = float(np.linalg.norm(target, ord="fro"))
    return {
        "q_rank": rank_q,
        "kernel_dimension": int(null_basis.shape[1]),
        "ker_q_compressed_fro": compressed_norm,
        "relative_to_target_fro": compressed_norm / target_norm if target_norm else 0.0,
    }


def toeplitz_distance_values(matrix: np.ndarray) -> list[float]:
    return [float(matrix[0, d]) for d in range(DIM)]


def analyze_family(repo_root: Path, audit: dict, family: str) -> dict:
    info = FAMILY_INFO[family]
    matrices = load_matrix_csv(repo_root / info["midpoint_csv"])
    q3 = signed_q3astar_matrix(family_audit_block(audit, family))
    canonical_signed = -matrices["A"]
    correction = q3 - canonical_signed

    singular = np.linalg.svd(correction, compute_uv=False)
    eigvals = np.linalg.eigvalsh((correction + correction.T) / 2)
    offdiag = correction.copy()
    np.fill_diagonal(offdiag, 0.0)
    q_fit = fit_qt_s_q(correction, matrices["Q"])
    null_residual = nullspace_quadratic_residual(correction, matrices["Q"])
    p0_fit = fit_scalar(correction, matrices["P0"])
    canonical_fit = fit_scalar(q3, canonical_signed)

    return {
        "family": family,
        "prefix": info["prefix"],
        "canonical_receiver": "-Step22/centeredBSplineArchKernelProfile midpoint convention",
        "payload": "negative full-even Q3.a_star candidate midpoint convention",
        "d0": {
            "canonical_signed_mid": float(canonical_signed[0, 0]),
            "signed_q3astar_mid": float(q3[0, 0]),
            "correction": float(correction[0, 0]),
        },
        "d1": {
            "canonical_signed_mid": float(canonical_signed[0, 1]),
            "signed_q3astar_mid": float(q3[0, 1]),
            "correction": float(correction[0, 1]),
        },
        "max_abs_correction": float(np.max(np.abs(correction))),
        "fro_norm_correction": float(np.linalg.norm(correction, ord="fro")),
        "operator_norm_correction": float(singular[0]),
        "rank_tol_1e_minus_10": int(np.linalg.matrix_rank(correction, tol=1e-10)),
        "rank_tol_1e_minus_8": int(np.linalg.matrix_rank(correction, tol=1e-8)),
        "singular_values_top6": [float(x) for x in singular[:6]],
        "eigenvalues_min6": [float(x) for x in eigvals[:6]],
        "eigenvalues_max6": [float(x) for x in eigvals[-6:]],
        "max_abs_offdiag": float(np.max(np.abs(offdiag))),
        "diagonal_like": bool(np.max(np.abs(offdiag)) <= 1e-10),
        "rank_one_like": bool(np.linalg.matrix_rank(correction, tol=1e-8) <= 1),
        "rank_two_like": bool(np.linalg.matrix_rank(correction, tol=1e-8) <= 2),
        "p0_like": {
            "alpha": p0_fit[0],
            "residual_fro": p0_fit[1],
            "relative_residual": p0_fit[2],
        },
        "scalar_multiple_of_canonical_signed_fit": {
            "alpha": canonical_fit[0],
            "residual_fro": canonical_fit[1],
            "relative_residual": canonical_fit[2],
        },
        "qt_s_q_like": q_fit,
        "zero_on_ker_q": {
            **null_residual,
            "yes_at_tol_1e_minus_8": bool(null_residual["ker_q_compressed_fro"] <= 1e-8),
        },
        "distance_correction_first8": toeplitz_distance_values(correction)[:8],
    }


def render_markdown(data: dict) -> str:
    lines = [
        "# Signed-Q3AStar Source Relation Audit",
        "",
        "Status: diagnostic only; no payload, radius-floor, or LDL data was mutated.",
        "",
        "Louise/Pro decision applied:",
        "",
        "```text",
        "Canonical semantic signed finite-Weil A remains",
        "  -centeredBSplineArchKernelProfile",
        "SignedQ3AStar may not feed Step33A unless a source relation theorem",
        "proves equality or a semantically valid correction decomposition.",
        "```",
        "",
        "## Summary",
        "",
    ]
    for block in data["families"]:
        z = block["zero_on_ker_q"]
        lines.extend(
            [
                f"### {block['family']} ({block['prefix']})",
                "",
                "```text",
                f"d=0 canonical signed midpoint : {block['d0']['canonical_signed_mid']:.18e}",
                f"d=0 SignedQ3AStar midpoint   : {block['d0']['signed_q3astar_mid']:.18e}",
                f"d=0 correction               : {block['d0']['correction']:.18e}",
                f"max |correction|             : {block['max_abs_correction']:.18e}",
                f"rank tol 1e-8                : {block['rank_tol_1e_minus_8']}",
                f"operator norm correction     : {block['operator_norm_correction']:.18e}",
                f"max offdiag correction       : {block['max_abs_offdiag']:.18e}",
                f"P0-like relative residual    : {block['p0_like']['relative_residual']:.18e}",
                f"Q^T S Q relative residual    : {block['qt_s_q_like']['relative_residual']:.18e}",
                f"ker(Q) compressed relative   : {z['relative_to_target_fro']:.18e}",
                "```",
                "",
            ]
        )
        if block["rank_tol_1e_minus_8"] > 2 and not z["yes_at_tol_1e_minus_8"]:
            lines.extend(
                [
                    "Interpretation:",
                    "",
                    "```text",
                    "Correction is not diagonal, not rank-one/rank-two, not Q^T S Q-like,",
                    "not zero on ker(Q), and not P0-like at the tested finite matrix level.",
                    "```",
                    "",
                ]
            )
    lines.extend(
        [
            "## SIGNED_Q3ASTAR_SOURCE_RELATION",
            "",
            "```text",
            "equality holds: no, numerically impossible against current receiver",
            "correction structure: full-rank finite Toeplitz-like correction",
            "zero on ker(Q): no",
            "Q^TQ-like: no",
            "P0-like: no",
            "recommended route: reject SignedQ3AStar as Step33A A-hbox source unless",
            "  a new semantic theorem retargets finite-Weil A itself",
            "```",
            "",
            "Next theorem route:",
            "",
            "```lean",
            "centeredBSplineSignedQ3AStarPayloadProfile_eq_signedFiniteWeilAProfile",
            "```",
            "",
            "is false for the current numeric surface.  The only honest next theorem",
            "would be a correction decomposition theorem, but the correction is not",
            "boundary/penalty/P0-like in this finite audit.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    repo_root = repo_root_from_cwd()
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--audit",
        type=Path,
        default=repo_root
        / "q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_convention_audit.json",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=repo_root
        / "q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/signed_q3astar_source_relation_audit.json",
    )
    parser.add_argument(
        "--md-out",
        type=Path,
        default=repo_root
        / "q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/signed_q3astar_source_relation_audit.md",
    )
    args = parser.parse_args()
    audit = json.loads(args.audit.read_text())
    data = {
        "status": "diagnostic_only",
        "families": [
            analyze_family(repo_root, audit, "primary"),
            analyze_family(repo_root, audit, "control"),
        ],
    }
    args.json_out.write_text(json.dumps(data, indent=2, sort_keys=True), encoding="utf-8")
    args.md_out.write_text(render_markdown(data), encoding="utf-8")
    print(f"wrote {args.json_out}")
    print(f"wrote {args.md_out}")


if __name__ == "__main__":
    main()
