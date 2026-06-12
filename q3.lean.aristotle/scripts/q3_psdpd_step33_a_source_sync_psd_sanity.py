#!/usr/bin/env python3
"""
Step33A A-source sync PSD sanity diagnostic.

This tool is deliberately non-mutating. It takes the `Q3.a_star` candidate A
midpoints from `a_source_convention_audit.json`, plugs them into the current
finite payload contour, and checks the midpoint penalty matrices numerically.

It is not a Lean proof object and does not edit CSV, radius, floor, or LDL data.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from decimal import Decimal
from pathlib import Path
from typing import Any

import numpy as np


DIM = 23


FAMILY_META = {
    "primary": {
        "prefix": "primaryK11",
        "audit_family": "primary",
    },
    "control": {
        "prefix": "controlK9",
        "audit_family": "control",
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


def resolve(root: Path, path: Path) -> Path:
    return path if path.is_absolute() else root / path


def read_midpoint_csv(path: Path) -> dict[str, dict[tuple[int, int], Decimal]]:
    out: dict[str, dict[tuple[int, int], Decimal]] = {}
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            matrix = row["matrix"]
            i = int(row["i"])
            j = int(row["j"])
            out.setdefault(matrix, {})[(i, j)] = Decimal(row["mid"])
    return out


def square(entries: dict[tuple[int, int], Decimal]) -> np.ndarray:
    return np.array(
        [[float(entries[(i, j)]) for j in range(DIM)] for i in range(DIM)],
        dtype=float,
    )


def boundary(entries: dict[tuple[int, int], Decimal]) -> np.ndarray:
    return np.array(
        [[float(entries[(i, j)]) for j in range(DIM)] for i in range(2)],
        dtype=float,
    )


def rat_def(text: str, name: str) -> Decimal:
    pattern = (
        rf"def\s+{re.escape(name)}\s*:\s*Rat\s*:=\s*"
        rf"\(\(\s*([+-]?\d+)\s*:\s*Rat\s*\)"
        rf"(?:\s*/\s*([+-]?\d+))?\s*\)"
    )
    match = re.search(pattern, text)
    if not match:
        raise ValueError(f"missing Rat definition: {name}")
    num = Decimal(match.group(1))
    den = Decimal(match.group(2) or "1")
    return num / den


def load_penalty_params(path: Path, prefix: str) -> dict[str, float]:
    text = path.read_text(encoding="utf-8")
    return {
        "tauD": float(rat_def(text, f"{prefix}TauDRat")),
        "tauR": float(rat_def(text, f"{prefix}TauRRat")),
        "dFloor": float(rat_def(text, f"{prefix}DFloorRat")),
        "rFloor": float(rat_def(text, f"{prefix}RFloorRat")),
    }


def audit_distance_values(audit: dict[str, Any], family: str) -> dict[int, Decimal]:
    for block in audit["families"]:
        if block["family"] == family:
            values = {
                int(row["index"]): Decimal(row["lean_astar_full_even_mid"])
                for row in block["rows"]
            }
            if set(values) != set(range(DIM)):
                missing = sorted(set(range(DIM)) - set(values))
                raise ValueError(f"audit family {family} missing distance rows: {missing}")
            return values
    raise ValueError(f"audit family not found: {family}")


def candidate_a_from_distance_values(values: dict[int, Decimal]) -> np.ndarray:
    return np.array(
        [[float(values[abs(i - j)]) for j in range(DIM)] for i in range(DIM)],
        dtype=float,
    )


def penalty_summary(
    *,
    A: np.ndarray,
    P: np.ndarray,
    P0: np.ndarray,
    Q: np.ndarray,
    kappa: float,
    theta: float,
    params: dict[str, float],
) -> dict[str, Any]:
    C = A - P
    R = A - kappa * P0
    D = C - theta * R
    qgram = Q.T @ Q
    Dp = D + params["tauD"] * qgram
    Rp = R + params["tauR"] * qgram
    Dp = (Dp + Dp.T) / 2.0
    Rp = (Rp + Rp.T) / 2.0
    d_eigs = np.linalg.eigvalsh(Dp)
    r_eigs = np.linalg.eigvalsh(Rp)
    return {
        "A_diag": float(A[0, 0]),
        "A_min_entry": float(np.min(A)),
        "A_max_entry": float(np.max(A)),
        "D_penalty_min_eigenvalue": float(d_eigs[0]),
        "D_penalty_floor": params["dFloor"],
        "D_penalty_passes_floor": bool(d_eigs[0] >= params["dFloor"]),
        "R_penalty_min_eigenvalue": float(r_eigs[0]),
        "R_penalty_floor": params["rFloor"],
        "R_penalty_passes_floor": bool(r_eigs[0] >= params["rFloor"]),
    }


def find_block(plan: dict[str, Any], family: str) -> dict[str, Any]:
    for block in plan["blocks"]:
        if block.get("role") == family:
            return block
    raise ValueError(f"plan block not found for role={family}")


def run_family(
    *,
    root: Path,
    plan: dict[str, Any],
    audit: dict[str, Any],
    penalty_import: Path,
    family: str,
) -> dict[str, Any]:
    block = find_block(plan, family)
    meta = FAMILY_META[family]
    midpoint_csv = resolve(root, Path(block["artifacts"]["midpoint_csv"]))
    matrices = read_midpoint_csv(midpoint_csv)
    current_a = square(matrices["A"])
    candidate_a = candidate_a_from_distance_values(
        audit_distance_values(audit, meta["audit_family"])
    )
    P = square(matrices["P"])
    P0 = square(matrices["P0"])
    Q = boundary(matrices["Q"])
    params = load_penalty_params(penalty_import, meta["prefix"])
    kappa = float(Decimal(str(block["parameters"]["kappa"])))
    theta = float(Decimal(str(block["parameters"]["theta"])))
    return {
        "family": family,
        "block_id": block["block_id"],
        "midpoint_csv": str(midpoint_csv),
        "kappa": kappa,
        "theta": theta,
        "penalty_params": params,
        "current_step22_import": penalty_summary(
            A=current_a, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params
        ),
        "negative_current_step22_import": penalty_summary(
            A=-current_a, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params
        ),
        "candidate_lean_astar_import": penalty_summary(
            A=candidate_a, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params
        ),
        "negative_candidate_lean_astar_import": penalty_summary(
            A=-candidate_a, P=P, P0=P0, Q=Q, kappa=kappa, theta=theta, params=params
        ),
    }


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    lines = [
        "# Step33A A-source sync PSD sanity",
        "",
        "This is a non-mutating diagnostic. It plugs the `Q3.a_star` candidate A",
        "midpoints from `a_source_convention_audit.json` into the current finite",
        "payload contour and checks the midpoint penalty matrices numerically.",
        "",
        "It does not edit CSV files, radius payloads, radius-floor data, LDL data,",
        "or Lean proof files.",
        "",
        "## Summary",
        "",
        "| family | source | A(0,0) | D min eig | D floor | D pass | R min eig | R floor | R pass |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for family in payload["families"]:
        for key, label in (
            ("current_step22_import", "current Step22 import"),
            ("negative_current_step22_import", "-current Step22 import"),
            ("candidate_lean_astar_import", "candidate Q3.a_star import"),
            ("negative_candidate_lean_astar_import", "-candidate Q3.a_star import"),
        ):
            row = family[key]
            lines.append(
                f"| {family['family']} | {label} | "
                f"{row['A_diag']:.16e} | "
                f"{row['D_penalty_min_eigenvalue']:.16e} | "
                f"{row['D_penalty_floor']:.16e} | "
                f"{row['D_penalty_passes_floor']} | "
                f"{row['R_penalty_min_eigenvalue']:.16e} | "
                f"{row['R_penalty_floor']:.16e} | "
                f"{row['R_penalty_passes_floor']} |"
            )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            "A blind A-table migration to the currently audited `Q3.a_star` candidate",
            "does not preserve the existing finite penalty certificate contour. The",
            "`-Q3.a_star` sign variant is tracked only as a diagnostic hint; the",
            "source convention must be reconciled before mutating global A payloads.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    root = repo_root_from_cwd()
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
        "--penalty-import",
        type=Path,
        default=Path("q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean"),
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_sync_psd_sanity.json"),
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=Path("q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_sync_psd_sanity.md"),
    )
    args = parser.parse_args()

    plan_path = resolve(root, args.plan)
    audit_path = resolve(root, args.audit_json)
    penalty_import = resolve(root, args.penalty_import)
    out_json = resolve(root, args.out_json)
    out_md = resolve(root, args.out_md)

    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    payload = {
        "schema": "q3_psdpd_step33_a_source_sync_psd_sanity.v1",
        "inputs": {
            "plan": str(plan_path),
            "audit_json": str(audit_path),
            "penalty_import": str(penalty_import),
        },
        "families": [
            run_family(
                root=root,
                plan=plan,
                audit=audit,
                penalty_import=penalty_import,
                family="primary",
            ),
            run_family(
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
