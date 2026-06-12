#!/usr/bin/env python3
"""
Generate exact rational LDL certificates for the Step33 signed-Q3.a_star route.

This is a parallel proof payload.  It does not mutate the legacy positive A
payload, old radius-floor data, or the old penalty LDL import.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Callable


DIM = 23
BOUNDARY_DIM = 2

HEADER = """import Q3.Proofs.PSD_CenteredCoeffSignedArchReceiver

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd

open CenteredCoeffPayloadImport
open CenteredCoeffPenaltyImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffSignedQ3AStarPayloadImport

/-!
Generated exact rational LDL certificates for the Step33 route-B
signed-Q3.a_star finite penalty lower bounds.

The certificate checks the rational matrix identity

  M + tau * Q^T Q = floor * I + L * diag(w) * L^T

entrywise over `Rat`, then casts the result to the checked real
`primary/control SignedQ3AStar` `D/R` matrices.
-/

"""

FOOTER = """
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


def repo_path(repo_root: Path, raw: str | Path) -> Path:
    raw_str = str(raw)
    candidates = [repo_root / raw_str, repo_root / "q3.lean.aristotle" / raw_str]
    prefix = "q3.lean.aristotle/"
    if raw_str.startswith(prefix):
        candidates.append(repo_root / raw_str[len(prefix):])
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return candidates[0]


def parse_fraction(raw: str) -> Fraction:
    return Fraction(str(raw))


def parse_lean_rat_def(text: str, name: str) -> Fraction:
    pattern = re.compile(
        rf"^def\s+{re.escape(name)}\s*:\s*Rat\s*:=\s*"
        r"\(\((-?[0-9]+)\s*:\s*Rat\)\s*(?:/\s*([0-9]+))?\)",
        re.MULTILINE,
    )
    match = pattern.search(text)
    if not match:
        raise SystemExit(f"missing Lean Rat definition {name!r}")
    denominator = int(match.group(2)) if match.group(2) else 1
    return Fraction(int(match.group(1)), denominator)


def decimal_to_fraction(value: Decimal) -> Fraction:
    value = +value
    if value == 0:
        return Fraction(0)
    sign = -1 if value < 0 else 1
    value = abs(value)
    tup = value.as_tuple()
    digits = int("".join(str(d) for d in tup.digits))
    exp = tup.exponent
    if exp >= 0:
        num = digits * (10**exp)
        den = 1
    else:
        num = digits
        den = 10 ** (-exp)
    if sign < 0:
        num = -num
    return Fraction(num, den)


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


def load_blocks(repo_root: Path, plan_path: Path, manifest_path: Path) -> list[Block]:
    plan = json.loads(plan_path.read_text())
    manifest_rows = {}
    with manifest_path.open() as handle:
        for row in csv.DictReader(handle):
            manifest_rows[row["block_id"]] = row
    payload_import = repo_path(
        repo_root, "q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean"
    ).read_text()
    penalty_import = repo_path(
        repo_root, "q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean"
    ).read_text()

    blocks: list[Block] = []
    for raw in plan["blocks"]:
        if raw["role"] not in {"primary", "control"}:
            continue
        manifest_row = manifest_rows.get(raw["block_id"])
        if manifest_row is None:
            raise SystemExit(f"missing manifest row for {raw['block_id']}")
        prefix = block_prefix(raw["block_id"])
        blocks.append(
            Block(
                block_id=raw["block_id"],
                role=raw["role"],
                prefix=prefix,
                midpoint_csv=repo_path(repo_root, raw["artifacts"]["midpoint_csv"]),
                kappa=parse_lean_rat_def(payload_import, f"{prefix}KappaRat"),
                theta=parse_lean_rat_def(payload_import, f"{prefix}ThetaRat"),
                tau_d=parse_lean_rat_def(penalty_import, f"{prefix}TauDRat"),
                tau_r=parse_lean_rat_def(penalty_import, f"{prefix}TauRRat"),
                floor_d=parse_lean_rat_def(penalty_import, f"{prefix}DFloorRat"),
                floor_r=parse_lean_rat_def(penalty_import, f"{prefix}RFloorRat"),
            )
        )
    if not blocks:
        raise SystemExit("missing primary/control blocks in payload import plan")
    return blocks


def load_midpoint(path: Path) -> dict[str, dict[tuple[int, int], Fraction]]:
    matrices: dict[str, dict[tuple[int, int], Fraction]] = {
        name: {} for name in ("P", "P0", "Q")
    }
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            matrix = row["matrix"]
            if matrix in matrices:
                matrices[matrix][(int(row["i"]), int(row["j"]))] = parse_fraction(row["mid"])
    return matrices


def load_signed_q3astar_a(audit_path: Path) -> dict[str, dict[int, Fraction]]:
    data = json.loads(audit_path.read_text())
    out: dict[str, dict[int, Fraction]] = {}
    for block in data["families"]:
        family = block["family"]
        out[family] = {
            int(row["index"]): -decimal_to_fraction(Decimal(row["lean_astar_full_even_mid"]))
            for row in block["rows"]
        }
    return out


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


def emit_rat_bridge(prefix: str) -> str:
    lines = [
        f"def {prefix}SignedQ3AStarCRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=",
        f"  matrixSubRat {prefix}SignedQ3AStarARat {prefix}PRat",
        "",
        f"def {prefix}SignedQ3AStarRRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=",
        f"  matrixScaledSubRat {prefix}SignedQ3AStarARat {prefix}P0Rat {prefix}KappaRat",
        "",
        f"def {prefix}SignedQ3AStarDRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=",
        f"  matrixScaledSubRat {prefix}SignedQ3AStarCRat",
        f"    {prefix}SignedQ3AStarRRat {prefix}ThetaRat",
        "",
        f"theorem {prefix}SignedQ3AStarR_eq_rat :",
        f"    {prefix}SignedQ3AStarR =",
        f"      fun i j => ({prefix}SignedQ3AStarRRat i j : Real) := by",
        "  ext i j",
        f"  simp [{prefix}SignedQ3AStarR,",
        f"    CenteredCoeffSignedQ3AStarPayloadImport.{prefix}SignedQ3AStarR,",
        f"    {prefix}SignedQ3AStarRRat,",
        f"    CenteredCoeffSignedQ3AStarPayloadImport.{prefix}SignedQ3AStarA,",
        f"    {prefix}P0, {prefix}Kappa, {prefix}KappaRat, matrixRkappa,",
        "    matrixScaledSub, matrixScaledSubRat]",
        "",
        f"theorem {prefix}SignedQ3AStarD_eq_rat :",
        f"    {prefix}SignedQ3AStarD =",
        f"      fun i j => ({prefix}SignedQ3AStarDRat i j : Real) := by",
        "  ext i j",
        f"  simp [{prefix}SignedQ3AStarD,",
        f"    CenteredCoeffSignedQ3AStarPayloadImport.{prefix}SignedQ3AStarD,",
        f"    {prefix}SignedQ3AStarDRat, {prefix}SignedQ3AStarCRat,",
        f"    {prefix}SignedQ3AStarRRat,",
        f"    CenteredCoeffSignedQ3AStarPayloadImport.{prefix}SignedQ3AStarA,",
        f"    {prefix}P, {prefix}P0, {prefix}Kappa, {prefix}KappaRat,",
        f"    {prefix}Theta, {prefix}ThetaRat, matrixDtheta,",
        "    matrixSubRat, matrixScaledSubRat]",
        "  ring",
        "",
    ]
    return "\n".join(lines)


def emit_ldl(prefix: str, kind: str, weights: list[Fraction], rows: list[list[Fraction]]) -> str:
    stem = f"{prefix}SignedQ3AStar{kind}LDL"
    matrix = f"{prefix}SignedQ3AStar{kind}Rat"
    tau = f"{prefix}Tau{kind}Rat"
    floor = f"{prefix}{kind}FloorRat"
    lower_name = f"{prefix}SignedQ3AStar{kind}LowerBound_ldl"
    real_matrix = f"{prefix}SignedQ3AStar{kind}"
    eq_rat = f"{prefix}SignedQ3AStar{kind}_eq_rat"
    lines: list[str] = []
    lines.append(f"/-- Exact LDL diagonal weights for `{prefix}` signed-Q3.a_star / `{kind}`. -/")
    lines.append(f"def {stem}WeightEntry : Nat -> Rat")
    for i, value in enumerate(weights):
        lines.append(f"  | {i} => {lean_rat(value)}")
    lines.append("  | _ => 0")
    lines.append("")
    lines.append(f"def {stem}Weight : CoeffIndex23 -> Rat :=")
    lines.append(f"  fun s => {stem}WeightEntry s.val")
    lines.append("")
    lines.append(f"/-- Exact unit-lower LDL row data for `{prefix}` signed-Q3.a_star / `{kind}`. -/")
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
    lines.append(f"theorem {stem}_identity : ∀ i j : CoeffIndex23,")
    lines.append(f"    {matrix} i j + {tau} * (∑ r : BoundaryIndex2, {prefix}QRat r i * {prefix}QRat r j) =")
    lines.append(f"      {floor} * (if i = j then (1 : Rat) else 0) +")
    lines.append(f"        Q3.Proofs.ratWeightedSquareMatrix {stem}Weight {stem}Row i j := by")
    lines.append("  intro i j")
    lines.append("  fin_cases i <;> fin_cases j <;> native_decide")
    lines.append("")
    lines.append(f"theorem {lower_name} :")
    lines.append(f"    ∀ v : CoeffIndex23 -> Real,")
    lines.append(f"      {prefix}{kind}Floor * Q3.Proofs.euclideanEnergy v <=")
    lines.append(f"        Q3.Proofs.penaltyForm {real_matrix} {prefix}Q {prefix}Tau{kind} v := by")
    lines.append("  have h := Q3.Proofs.penalty_lower_bound_of_ratMatrixWeightedSquare_identity")
    lines.append(f"    {matrix} {prefix}QRat {tau} {floor}")
    lines.append(f"    {stem}Weight {stem}Row {stem}Weight_nonneg {stem}_identity")
    lines.append(f"  simpa [{eq_rat}, {prefix}Q, {prefix}Tau{kind}, {prefix}{kind}Floor] using h")
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


def generate(repo_root: Path, plan: Path, manifest: Path, audit: Path) -> str:
    chunks: list[str] = [HEADER]
    signed_a_by_family = load_signed_q3astar_a(audit)
    for block in load_blocks(repo_root, plan, manifest):
        matrices = load_midpoint(block.midpoint_csv)
        signed_a = signed_a_by_family[block.role]

        def get(name: str, i: int, j: int) -> Fraction:
            return matrices[name].get((i, j), Fraction(0))

        def a(i: int, j: int) -> Fraction:
            return signed_a[abs(j - i)]

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

        chunks.append(emit_rat_bridge(block.prefix))
        chunks.append(emit_ldl(block.prefix, "D", d_weights, d_rows))
        chunks.append(emit_ldl(block.prefix, "R", r_weights, r_rows))
        chunks.append(f"def {block.prefix}SignedQ3AStarPenaltyLowerBoundCert_ldl :")
        chunks.append(f"    {block.prefix}SignedQ3AStarFinitePenaltyLowerBoundCert where")
        chunks.append(f"  tauD := {block.prefix}TauD")
        chunks.append(f"  tauR := {block.prefix}TauR")
        chunks.append(f"  dFloor := {block.prefix}DFloor")
        chunks.append(f"  rFloor := {block.prefix}RFloor")
        chunks.append(f"  dFloor_pos := {block.prefix}DFloor_pos")
        chunks.append(f"  rFloor_pos := {block.prefix}RFloor_pos")
        chunks.append(f"  D_penalty_lower := {block.prefix}SignedQ3AStarDLowerBound_ldl")
        chunks.append(f"  R_penalty_lower := {block.prefix}SignedQ3AStarRLowerBound_ldl")
        chunks.append("")
        chunks.append(f"def {block.prefix}SignedQ3AStarFinitePenaltyCert_ldl :")
        chunks.append(f"    Q3.Proofs.FinitePenaltyCert")
        chunks.append(f"      {block.prefix}SignedQ3AStarD {block.prefix}SignedQ3AStarR {block.prefix}Q :=")
        chunks.append(f"  {block.prefix}SignedQ3AStarFinitePenaltyCert_of_lowerBoundCert")
        chunks.append(f"    {block.prefix}SignedQ3AStarPenaltyLowerBoundCert_ldl")
        chunks.append("")
    chunks.append(FOOTER)
    return "\n".join(chunks)


def main() -> None:
    repo_root = repo_root_from_cwd()
    q3_root = repo_root / "q3.lean.aristotle"
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--plan",
        type=Path,
        default=q3_root / "docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=q3_root / "docs/insights/q3_psdpd_certificate_family_manifest.csv",
    )
    parser.add_argument(
        "--audit",
        type=Path,
        default=q3_root / "ACTIVE/requests/step33_bootstrap/a_source_convention_audit.json",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=q3_root / "Q3/Proofs/PSD_CenteredCoeffSignedQ3AStarPenaltyLDLImport.lean",
    )
    args = parser.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(generate(repo_root, args.plan, args.manifest, args.audit), encoding="utf-8")
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
