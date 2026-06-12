#!/usr/bin/env python3
"""
Step33A canonical-A kernel obstruction diagnostic.

This is a non-mutating diagnostic.  It checks the necessary boundary-null
condition for the actual Step32/Step33 finite form

    C = A - P

under the raw Step22 A, the transformed Arch-sign A, and the sign-flipped
transformed A.  If C is negative on ker(Q), no P0 split can prove the current
formula contract without changing the semantic receiver or the assembler sign.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

import q3_psdpd_step33_a_source_sync_psd_sanity as sanity
import q3_psdpd_step33_transformed_a_recert_feasibility as feasibility


def sym(M: np.ndarray) -> np.ndarray:
    return (M + M.T) / 2.0


def eig_range(M: np.ndarray) -> dict[str, float]:
    eigs = np.linalg.eigvalsh(sym(M))
    return {
        "min": float(eigs[0]),
        "max": float(eigs[-1]),
    }


def restricted(M: np.ndarray, N: np.ndarray) -> np.ndarray:
    return N.T @ sym(M) @ N


def source_summary(
    *,
    label: str,
    A: np.ndarray,
    raw_A: np.ndarray,
    transformed_A: np.ndarray,
    P: np.ndarray,
    N: np.ndarray,
) -> dict[str, Any]:
    C = A - P
    Cn = restricted(C, N)
    An = restricted(A, N)
    return {
        "source": label,
        "A_on_kerQ": eig_range(An),
        "C_eq_A_minus_P_on_kerQ": eig_range(Cn),
        "C_boundary_null_nonnegative": bool(eig_range(Cn)["min"] >= 0.0),
        "max_abs_A_minus_rawStep22": float(np.max(np.abs(A - raw_A))),
        "max_abs_A_minus_transformedArchSign": float(np.max(np.abs(A - transformed_A))),
        "max_abs_rawStep22_plus_transformedArchSign": float(np.max(np.abs(raw_A + transformed_A))),
    }


def family_payload(root: Path, plan: dict[str, Any], audit: dict[str, Any], family: str) -> dict[str, Any]:
    block = sanity.find_block(plan, family)
    midpoint_csv = sanity.resolve(root, Path(block["artifacts"]["midpoint_csv"]))
    midpoint = sanity.read_midpoint_csv(midpoint_csv)
    raw_A = sanity.square(midpoint["A"])
    transformed_A = feasibility.square_from_distance(
        feasibility.transformed_distance_values(audit, family)
    )
    P = sanity.square(midpoint["P"])
    Q = sanity.boundary(midpoint["Q"])
    N = feasibility.nullspace_basis(Q)

    sources = [
        source_summary(
            label="raw_step22_positive_axis",
            A=raw_A,
            raw_A=raw_A,
            transformed_A=transformed_A,
            P=P,
            N=N,
        ),
        source_summary(
            label="transformed_step22_omega_arch_sign",
            A=transformed_A,
            raw_A=raw_A,
            transformed_A=transformed_A,
            P=P,
            N=N,
        ),
        source_summary(
            label="negative_transformed_step22_omega_arch_sign",
            A=-transformed_A,
            raw_A=raw_A,
            transformed_A=transformed_A,
            P=P,
            N=N,
        ),
    ]
    transformed = next(
        source for source in sources if source["source"] == "transformed_step22_omega_arch_sign"
    )
    return {
        "family": family,
        "block_id": block["block_id"],
        "midpoint_csv": str(midpoint_csv),
        "Q_rank": int(23 - N.shape[1]),
        "kerQ_dim": int(N.shape[1]),
        "sources": sources,
        "necessary_obstruction": {
            "formula_contract": "C = A - P",
            "reason": "C must be nonnegative on ker(Q) before any P0 split can certify it",
            "transformed_C_min_on_kerQ": transformed["C_eq_A_minus_P_on_kerQ"]["min"],
            "transformed_C_passes": transformed["C_boundary_null_nonnegative"],
        },
    }


def decision(families: list[dict[str, Any]]) -> dict[str, Any]:
    transformed_ok = all(f["necessary_obstruction"]["transformed_C_passes"] for f in families)
    worst = min(families, key=lambda f: f["necessary_obstruction"]["transformed_C_min_on_kerQ"])
    return {
        "transformed_A_current_formula_contract_feasible": transformed_ok,
        "worst_family": worst["family"],
        "worst_transformed_C_min_on_kerQ": worst["necessary_obstruction"][
            "transformed_C_min_on_kerQ"
        ],
        "next_action": (
            "semantic sign/assembler review; do not search P0 split until C=A-P sign is resolved"
            if not transformed_ok
            else "C boundary-null condition passes; continue transformed-A split search"
        ),
    }


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    lines = [
        "# Step33A Canonical-A Kernel Obstruction",
        "",
        "This is a non-mutating diagnostic.  It checks the necessary condition",
        "for the current Step32/Step33 formula contract:",
        "",
        "```text",
        "C = A - P",
        "```",
        "",
        "If `C` is negative on `ker(Q)`, no `P0` split can certify the current",
        "receiver without changing the semantic receiver or the assembler sign.",
        "",
        "## Summary",
        "",
        "| family | source | A ker(Q) min | A ker(Q) max | C=A-P ker(Q) min | C=A-P ker(Q) max | C nonnegative |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for family in payload["families"]:
        for source in family["sources"]:
            a = source["A_on_kerQ"]
            c = source["C_eq_A_minus_P_on_kerQ"]
            lines.append(
                f"| {family['family']} | {source['source']} | "
                f"{a['min']:.16e} | {a['max']:.16e} | "
                f"{c['min']:.16e} | {c['max']:.16e} | "
                f"{source['C_boundary_null_nonnegative']} |"
            )
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"- transformed A feasible for current `C = A - P` contract: `{payload['decision']['transformed_A_current_formula_contract_feasible']}`",
            f"- worst family: `{payload['decision']['worst_family']}`",
            f"- worst transformed `C` minimum on `ker(Q)`: `{payload['decision']['worst_transformed_C_min_on_kerQ']:.16e}`",
            f"- next action: `{payload['decision']['next_action']}`",
            "",
            "Interpretation:",
            "",
            "The transformed Arch-sign receiver is not merely incompatible with the",
            "old `P0` split.  With the current formula contract `C = A - P`, the",
            "finite form itself is negative on the boundary-null subspace.  A new",
            "`P0` split cannot repair that, because any split still sums back to",
            "`C`.",
            "",
            "The raw Step22 payload passes this necessary test, and `-transformed`",
            "also passes numerically, but neither is acceptable as the analytic",
            "receiver without a checked semantic sign/assembler theorem.",
            "",
        ]
    )
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
        "--audit",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_convention_audit.json"),
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/canonical_a_kernel_obstruction.json"),
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/canonical_a_kernel_obstruction.md"),
    )
    args = parser.parse_args()

    plan = json.loads(sanity.resolve(root, args.plan).read_text(encoding="utf-8"))
    audit = json.loads(sanity.resolve(root, args.audit).read_text(encoding="utf-8"))
    families = [family_payload(root, plan, audit, family) for family in ("primary", "control")]
    payload = {
        "status": "non_mutating_diagnostic",
        "families": families,
        "decision": decision(families),
    }
    out_json = sanity.resolve(root, args.out_json)
    out_md = sanity.resolve(root, args.out_md)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    write_markdown(payload, out_md)
    print(f"wrote {out_json}")
    print(f"wrote {out_md}")
    print(json.dumps(payload["decision"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
