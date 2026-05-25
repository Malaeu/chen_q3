#!/usr/bin/env python3
"""
Generate exact rational LDL certificates for the primary Step 32F coefficient
penalty lower bounds.

This is a proof generator, not a numerical import.  It consumes the already
checked rational midpoint payload and Step18 penalty parameters, computes an
exact no-pivot LDL decomposition over `Fraction`, and emits Lean data plus
`native_decide`-checked rational matrix identities.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable


DIM = 23
BOUNDARY_DIM = 2
GENERATED_HEADER = """import Q3.Proofs.PSD_CenteredCoeffPenaltyImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPenaltyImport

open CenteredCoeffPayloadImport

/-!
Generated exact rational LDL certificates for active Step 32F penalty lower
bounds.

The certificate checks the rational matrix identity

  M + tau * Q^T Q = floor * I + L * diag(w) * L^T

entrywise over `Rat`, then uses the reusable real receiver in
`PSD_PenaltyCertificate`.
-/

"""

GENERATED_FOOTER = """
end CenteredCoeffPenaltyImport
end PSDpd
end Q3
"""


@dataclass(frozen=True)
class Block:
    block_id: str
    role: str
    prefix: str
    midpoint_csv: Path
    kappa: Fraction
    theta: Fraction
    tau_d: Fraction
    tau_r: Fraction
    floor_d: Fraction
    floor_r: Fraction


def repo_path(repo_dir: Path, raw: str) -> Path:
    prefix = "q3.lean.aristotle/"
    candidates = [repo_dir / raw, repo_dir.parent / raw]
    if raw.startswith(prefix):
        candidates.append(repo_dir / raw[len(prefix):])
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return candidates[-1]


def parse_fraction(raw: str) -> Fraction:
    return Fraction(str(raw))


def block_prefix(block_id: str) -> str:
    if "k11" in block_id:
        return "primaryK11"
    if "k9" in block_id:
        return "controlK9"
    raise SystemExit(f"unsupported block id: {block_id}")


def extract_section(text: str, title_prefix: str) -> str:
    pattern = re.compile(
        r"^== (?P<title>(?:Dtheta|R_kappa).*?) penalty certificate ==\n"
        r"(?P<body>.*?)(?=^== |\Z)",
        re.MULTILINE | re.DOTALL,
    )
    for match in pattern.finditer(text):
        if match.group("title").strip().startswith(title_prefix):
            return match.group("body")
    raise SystemExit(f"missing Step18 section starting with {title_prefix!r}")


def extract_value(body: str, key: str) -> Fraction:
    match = re.search(rf"^{re.escape(key)}\s+=\s+([0-9.eE+-]+)\s*$", body, re.MULTILINE)
    if not match:
        raise SystemExit(f"missing Step18 value {key!r}")
    return parse_fraction(match.group(1))


def load_primary_block(repo_dir: Path, plan_path: Path, manifest_path: Path) -> Block:
    plan = json.loads(plan_path.read_text())
    raw = next((block for block in plan["blocks"] if block["role"] == "primary"), None)
    if raw is None:
        raise SystemExit("missing primary block in payload import plan")

    manifest_row = None
    with manifest_path.open() as f:
        for row in csv.DictReader(f):
            if row["block_id"] == raw["block_id"]:
                manifest_row = row
                break
    if manifest_row is None:
        raise SystemExit(f"missing manifest row for {raw['block_id']}")

    if (
        manifest_row["status"] != "PASS"
        or manifest_row["dtheta_pass"] != "True"
        or manifest_row["rkappa_pass"] != "True"
    ):
        raise SystemExit(f"{raw['block_id']}: manifest row is not passing")

    stdout = repo_path(repo_dir, manifest_row["stdout_path"]).read_text()
    d_body = extract_section(stdout, "Dtheta")
    r_body = extract_section(stdout, "R_kappa")
    params = raw["parameters"]
    return Block(
        block_id=raw["block_id"],
        role=raw["role"],
        prefix=block_prefix(raw["block_id"]),
        midpoint_csv=repo_path(repo_dir, raw["artifacts"]["midpoint_csv"]),
        kappa=parse_fraction(params["kappa"]),
        theta=parse_fraction(params["theta"]),
        tau_d=extract_value(d_body, "best_tau"),
        tau_r=extract_value(r_body, "best_tau"),
        floor_d=extract_value(d_body, "safe_lower"),
        floor_r=extract_value(r_body, "safe_lower"),
    )


def load_midpoint(path: Path) -> dict[str, dict[tuple[int, int], Fraction]]:
    matrices: dict[str, dict[tuple[int, int], Fraction]] = {
        name: {} for name in ("A", "P", "P0", "Q")
    }
    with path.open() as f:
        reader = csv.DictReader(f)
        required = {"matrix", "i", "j", "mid"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise SystemExit(f"{path}: missing columns {sorted(missing)}")
        for row in reader:
            matrix = row["matrix"]
            if matrix not in matrices:
                raise SystemExit(f"{path}: unexpected matrix {matrix!r}")
            matrices[matrix][(int(row["i"]), int(row["j"]))] = parse_fraction(row["mid"])
    return matrices


def ldl_decomposition(G: list[list[Fraction]]) -> tuple[list[Fraction], list[list[Fraction]]]:
    n = len(G)
    L = [[Fraction(0) for _ in range(n)] for __ in range(n)]
    d = [Fraction(0) for _ in range(n)]
    for i in range(n):
        for j in range(i):
            previous = sum(L[i][k] * L[j][k] * d[k] for k in range(j))
            L[i][j] = (G[i][j] - previous) / d[j]
        diagonal_previous = sum(L[i][k] * L[i][k] * d[k] for k in range(i))
        d[i] = G[i][i] - diagonal_previous
        if d[i] <= 0:
            raise SystemExit(f"nonpositive LDL pivot {i}: {d[i]}")
        L[i][i] = Fraction(1)

    for i in range(n):
        for j in range(n):
            reconstructed = sum(d[k] * L[i][k] * L[j][k] for k in range(n))
            if reconstructed != G[i][j]:
                raise SystemExit(f"LDL reconstruction failed at {(i, j)}")
    return d, L


def lean_rat(x: Fraction) -> str:
    if x == 0:
        return "0"
    if x.denominator == 1:
        return f"(({x.numerator} : Rat))"
    return f"(({x.numerator} : Rat) / {x.denominator})"


def emit_ldl(prefix: str, kind: str, weights: list[Fraction], rows: list[list[Fraction]]) -> str:
    stem = f"{prefix}{kind}LDL"
    lines: list[str] = []
    lines.append(f"/-- Exact LDL diagonal weights for `{prefix}` / `{kind}`. -/")
    lines.append(f"def {stem}WeightEntry : Nat -> Rat")
    for i, value in enumerate(weights):
        lines.append(f"  | {i} => {lean_rat(value)}")
    lines.append("  | _ => 0")
    lines.append("")
    lines.append(f"def {stem}Weight : CoeffIndex23 -> Rat :=")
    lines.append(f"  fun s => {stem}WeightEntry s.val")
    lines.append("")
    lines.append(f"/-- Exact unit-lower LDL row data for `{prefix}` / `{kind}`. -/")
    lines.append(f"def {stem}RowEntry : Nat -> Nat -> Rat")
    for s in range(DIM):
        for i in range(DIM):
            value = rows[i][s]
            if value != 0:
                lines.append(f"  | {s}, {i} => {lean_rat(value)}")
    lines.append("  | _, _ => 0")
    lines.append("")
    lines.append(f"def {stem}Row : CoeffIndex23 -> CoeffIndex23 -> Rat :=")
    lines.append(f"  fun s i => {stem}RowEntry s.val i.val")
    lines.append("")
    lines.append(f"theorem {stem}Weight_nonneg : ∀ s : CoeffIndex23, 0 <= {stem}Weight s := by")
    lines.append("  intro s")
    lines.append("  fin_cases s <;> native_decide")
    lines.append("")
    if kind == "D":
        matrix = f"{prefix}DRat"
        tau = f"{prefix}TauDRat"
        floor = f"{prefix}DFloorRat"
        lower = f"{prefix}DLowerBound"
    elif kind == "R":
        matrix = f"{prefix}RRat"
        tau = f"{prefix}TauRRat"
        floor = f"{prefix}RFloorRat"
        lower = f"{prefix}RLowerBound"
    else:
        raise AssertionError(kind)
    lines.append(f"theorem {stem}_identity : ∀ i j : CoeffIndex23,")
    lines.append(f"    {matrix} i j + {tau} * (∑ r : BoundaryIndex2, {prefix}QRat r i * {prefix}QRat r j) =")
    lines.append(f"      {floor} * (if i = j then (1 : Rat) else 0) +")
    lines.append(f"        Q3.Proofs.ratWeightedSquareMatrix {stem}Weight {stem}Row i j := by")
    lines.append("  intro i j")
    lines.append("  fin_cases i <;> fin_cases j <;> native_decide")
    lines.append("")
    lines.append(f"theorem {prefix}{kind}LowerBound_ldl : {lower} :=")
    lines.append("  Q3.Proofs.penalty_lower_bound_of_ratMatrixWeightedSquare_identity")
    lines.append(f"    {matrix} {prefix}QRat {tau} {floor}")
    lines.append(f"    {stem}Weight {stem}Row {stem}Weight_nonneg {stem}_identity")
    lines.append("")
    return "\n".join(lines)


def build_gram(
    matrix: Callable[[int, int], Fraction],
    q: Callable[[int, int], Fraction],
    tau: Fraction,
    floor: Fraction,
) -> list[list[Fraction]]:
    return [
        [
            matrix(i, j)
            + tau * sum(q(r, i) * q(r, j) for r in range(BOUNDARY_DIM))
            - (floor if i == j else 0)
            for j in range(DIM)
        ]
        for i in range(DIM)
    ]


def generate(repo_dir: Path, plan_path: Path, manifest_path: Path) -> str:
    block = load_primary_block(repo_dir, plan_path, manifest_path)
    matrices = load_midpoint(block.midpoint_csv)
    get = lambda name, i, j: matrices[name].get((i, j), Fraction(0))
    a = lambda i, j: get("A", i, j)
    p = lambda i, j: get("P", i, j)
    p0 = lambda i, j: get("P0", i, j)
    q = lambda r, i: get("Q", r, i)
    c = lambda i, j: a(i, j) - p(i, j)
    r_matrix = lambda i, j: a(i, j) - block.kappa * p0(i, j)
    d_matrix = lambda i, j: c(i, j) - block.theta * r_matrix(i, j)

    d_weights, d_rows = ldl_decomposition(
        build_gram(d_matrix, q, block.tau_d, block.floor_d)
    )
    r_weights, r_rows = ldl_decomposition(
        build_gram(r_matrix, q, block.tau_r, block.floor_r)
    )

    chunks = [GENERATED_HEADER]
    chunks.append(emit_ldl(block.prefix, "D", d_weights, d_rows))
    chunks.append(emit_ldl(block.prefix, "R", r_weights, r_rows))
    chunks.append(f"def {block.prefix}PenaltyLowerBoundCert_ldl :")
    chunks.append(f"    Q3.Proofs.FinitePenaltyLowerBoundCert {block.prefix}D {block.prefix}R {block.prefix}Q :=")
    chunks.append(f"  {block.prefix}PenaltyLowerBoundCert_of_bounds")
    chunks.append(f"    {block.prefix}DLowerBound_ldl")
    chunks.append(f"    {block.prefix}RLowerBound_ldl")
    chunks.append("")
    chunks.append(f"def {block.prefix}FinitePenaltyCert_ldl :")
    chunks.append(f"    Q3.Proofs.FinitePenaltyCert {block.prefix}D {block.prefix}R {block.prefix}Q :=")
    chunks.append("  Q3.Proofs.FinitePenaltyLowerBoundCert.toFinitePenaltyCert")
    chunks.append(f"    {block.prefix}PenaltyLowerBoundCert_ldl")
    chunks.append("")
    chunks.append(GENERATED_FOOTER)
    return "\n".join(chunks)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-dir", default=".")
    parser.add_argument(
        "--plan",
        default="docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json",
    )
    parser.add_argument(
        "--manifest",
        default="docs/insights/q3_psdpd_certificate_family_manifest.csv",
    )
    parser.add_argument(
        "--output",
        default="Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean",
    )
    args = parser.parse_args()

    repo_dir = Path(args.repo_dir).resolve()
    plan_path = repo_path(repo_dir, args.plan)
    manifest_path = repo_path(repo_dir, args.manifest)
    output_path = repo_dir / args.output
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(generate(repo_dir, plan_path, manifest_path))
    print(f"wrote {output_path}")


if __name__ == "__main__":
    main()
