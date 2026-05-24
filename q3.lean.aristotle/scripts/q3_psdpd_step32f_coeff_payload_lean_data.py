#!/usr/bin/env python3
"""
Generate the checked Lean data layer for the active Step 32F coefficient blocks.

This is intentionally a data importer, not a certificate prover.  It emits the
accepted midpoint matrices as exact rational Lean terms, defines the derived
midpoint matrices

  C = A - P
  R = A - kappa * P0
  D = C - theta * R

and proves the purely algebraic quadratic-form split

  quadForm C v = quadForm D v + theta * quadForm R v.

It does not construct `FinitePenaltyCert` or
`CertifiedCenteredBSplineCoeffBlock`; those require a separate Lean-checked
interval/SPD positivity bridge.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path
from typing import Any


EXPECTED_MATRICES = ("A", "P", "P0", "Q")
SQUARE_MATRICES = ("A", "P", "P0")
GENERATED_HEADER = """import Q3.Proofs.PSD_CenteredCardinalBSpline

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPayloadImport

/-!
Checked midpoint payload data for the active Step 32F coefficient blocks.

This generated file is a deliberately narrow import layer:

* it records the active CSV midpoint/radius artifacts as exact rational data;
* it defines midpoint `C`, `R`, and `D` matrices from `A`, `P`, `P0`;
* it proves the algebraic split `C = D + theta R` at quadratic-form level.

It does not claim a `FinitePenaltyCert`.  The interval-backed positivity proof
is the next required bridge before these payloads can become
`CertifiedCenteredBSplineCoeffBlock` values.
-/

abbrev CoeffIndex23 := Fin 23
abbrev BoundaryIndex2 := Fin 2

def matrixSub {rho sigma : Type*} (A B : Matrix rho sigma Real) :
    Matrix rho sigma Real :=
  fun i j => A i j - B i j

def matrixScaledSub {rho sigma : Type*} (A B : Matrix rho sigma Real)
    (c : Real) : Matrix rho sigma Real :=
  fun i j => A i j - c * B i j

theorem quadForm_pointwise_add {iota : Type*} [Fintype iota]
    (M N : Matrix iota iota Real) (v : iota -> Real) :
    Q3.Proofs.quadForm (fun i j => M i j + N i j) v =
      Q3.Proofs.quadForm M v + Q3.Proofs.quadForm N v := by
  unfold Q3.Proofs.quadForm
  simp_rw [mul_add]
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]

theorem quadForm_pointwise_smul {iota : Type*} [Fintype iota]
    (c : Real) (M : Matrix iota iota Real) (v : iota -> Real) :
    Q3.Proofs.quadForm (fun i j => c * M i j) v =
      c * Q3.Proofs.quadForm M v := by
  unfold Q3.Proofs.quadForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadForm_scaled_sub_split {iota : Type*} [Fintype iota]
    (C R : Matrix iota iota Real) (theta : Real) :
    forall v : iota -> Real,
      Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm (matrixScaledSub C R theta) v +
          theta * Q3.Proofs.quadForm R v := by
  intro v
  change Q3.Proofs.quadForm C v =
    Q3.Proofs.quadForm (fun i j => C i j - theta * R i j) v +
      theta * Q3.Proofs.quadForm R v
  have hpoint :
      C = (fun i j => (C i j - theta * R i j) + theta * R i j) := by
    funext i j
    ring
  calc
    Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm
          (fun i j => (C i j - theta * R i j) + theta * R i j) v := by
      conv_lhs => rw [hpoint]
    _ =
        Q3.Proofs.quadForm (fun i j => C i j - theta * R i j) v +
          Q3.Proofs.quadForm (fun i j => theta * R i j) v := by
      rw [quadForm_pointwise_add]
    _ =
        Q3.Proofs.quadForm (fun i j => C i j - theta * R i j) v +
          theta * Q3.Proofs.quadForm R v := by
      rw [quadForm_pointwise_smul]

structure CenteredCoeffPayloadData where
  label : FiniteSpaceLabel
  blockId : String
  role : String
  k : Nat
  ell : Real
  kappa : Real
  theta : Real
  theta_nonneg : 0 <= theta
  A : Matrix CoeffIndex23 CoeffIndex23 Real
  P : Matrix CoeffIndex23 CoeffIndex23 Real
  P0 : Matrix CoeffIndex23 CoeffIndex23 Real
  Q : Matrix BoundaryIndex2 CoeffIndex23 Real
  C : Matrix CoeffIndex23 CoeffIndex23 Real
  D : Matrix CoeffIndex23 CoeffIndex23 Real
  R : Matrix CoeffIndex23 CoeffIndex23 Real
  split :
    forall v : CoeffIndex23 -> Real,
      Q3.Proofs.quadForm C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v

"""

GENERATED_FOOTER = """
end CenteredCoeffPayloadImport
end PSDpd
end Q3
"""


@dataclass(frozen=True)
class Block:
    block_id: str
    role: str
    prefix: str
    k: int
    ell: str
    theta: str
    kappa: str
    label: str
    midpoint_csv: Path
    radius_csv: Path
    midpoint_sha256: str
    radius_sha256: str


def repo_path(repo_dir: Path, raw: str) -> Path:
    prefix = "q3.lean.aristotle/"
    candidates = [repo_dir / raw, repo_dir.parent / raw]
    if raw.startswith(prefix):
        candidates.append(repo_dir / raw[len(prefix):])
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return candidates[-1]


def decimal_to_lean(raw: str) -> str:
    dec = Decimal(str(raw))
    sign, digits, exp = dec.as_tuple()
    n = int("".join(str(d) for d in digits)) if digits else 0
    if sign:
        n = -n
    if exp >= 0:
        num = n * (10 ** exp)
        den = 1
    else:
        num = n
        den = 10 ** (-exp)
    if num == 0:
        return "0"
    g = math.gcd(abs(num), den)
    num //= g
    den //= g
    if den == 1:
        return f"(({num} : Real))"
    return f"(({num} : Real) / {den})"


def load_matrix_csv(path: Path, value_column: str) -> dict[str, dict[tuple[int, int], str]]:
    out: dict[str, dict[tuple[int, int], str]] = {name: {} for name in EXPECTED_MATRICES}
    with path.open() as f:
        reader = csv.DictReader(f)
        if reader.fieldnames is None:
            raise SystemExit(f"{path}: missing header")
        required = {"matrix", "i", "j", value_column}
        missing = required.difference(reader.fieldnames)
        if missing:
            raise SystemExit(f"{path}: missing columns {sorted(missing)}")
        for row in reader:
            matrix = row["matrix"].strip()
            if matrix not in EXPECTED_MATRICES:
                raise SystemExit(f"{path}: unexpected matrix {matrix!r}")
            key = (int(row["i"]), int(row["j"]))
            out[matrix][key] = row[value_column].strip()
    return out


def block_prefix(block_id: str) -> str:
    if "k11" in block_id:
        return "primaryK11"
    if "k9" in block_id:
        return "controlK9"
    raise SystemExit(f"unsupported block id: {block_id}")


def load_blocks(repo_dir: Path, plan_path: Path) -> list[Block]:
    plan = json.loads(plan_path.read_text())
    blocks = []
    for raw in plan["blocks"]:
        lean = raw["lean_bindings"]
        params = raw["parameters"]
        blocks.append(
            Block(
                block_id=raw["block_id"],
                role=raw["role"],
                prefix=block_prefix(raw["block_id"]),
                k=int(params["k_spline"]),
                ell=str(params["ell"]),
                theta=str(params["theta"]),
                kappa=str(params["kappa"]),
                label=lean["label"],
                midpoint_csv=repo_path(repo_dir, raw["artifacts"]["midpoint_csv"]),
                radius_csv=repo_path(repo_dir, raw["artifacts"]["radius_csv"]),
                midpoint_sha256=raw["artifacts"]["midpoint_sha256"],
                radius_sha256=raw["artifacts"]["radius_sha256"],
            )
        )
    return blocks


def lean_matrix_def(
    prefix: str,
    matrix_name: str,
    values: dict[tuple[int, int], str],
    *,
    boundary: bool = False,
) -> str:
    fn = f"{prefix}{matrix_name}Entry"
    rows = [f"def {fn} : Nat -> Nat -> Real"]
    for (i, j), raw in sorted(values.items()):
        rows.append(f"  | {i}, {j} => {decimal_to_lean(raw)}")
    rows.append("  | _, _ => 0")
    rows.append("")
    if boundary:
        rows.append(f"def {prefix}{matrix_name} : Matrix BoundaryIndex2 CoeffIndex23 Real :=")
    else:
        rows.append(f"def {prefix}{matrix_name} : Matrix CoeffIndex23 CoeffIndex23 Real :=")
    rows.append(f"  fun i j => {fn} i.val j.val")
    rows.append("")
    return "\n".join(rows)


def emit_block(block: Block) -> str:
    mid = load_matrix_csv(block.midpoint_csv, "mid")
    rad = load_matrix_csv(block.radius_csv, "rad")
    p = block.prefix
    lines: list[str] = []
    lines.append(f"/-- Generated exact midpoint payload for `{block.block_id}`. -/")
    lines.append(f"def {p}Ell : Real := {decimal_to_lean(block.ell)}")
    lines.append(f"def {p}Kappa : Real := {decimal_to_lean(block.kappa)}")
    lines.append(f"def {p}Theta : Real := {decimal_to_lean(block.theta)}")
    lines.append("")
    for name in EXPECTED_MATRICES:
        lines.append(lean_matrix_def(p, name, mid[name], boundary=(name == "Q")))
    for name in EXPECTED_MATRICES:
        rad_name = f"{name}Radius" if name != "Q" else "QRadius"
        lines.append(lean_matrix_def(p, rad_name, rad[name], boundary=(name == "Q")))
    lines.append(f"def {p}C : Matrix CoeffIndex23 CoeffIndex23 Real :=")
    lines.append(f"  matrixSub {p}A {p}P")
    lines.append("")
    lines.append(f"def {p}R : Matrix CoeffIndex23 CoeffIndex23 Real :=")
    lines.append(f"  matrixScaledSub {p}A {p}P0 {p}Kappa")
    lines.append("")
    lines.append(f"def {p}D : Matrix CoeffIndex23 CoeffIndex23 Real :=")
    lines.append(f"  matrixScaledSub {p}C {p}R {p}Theta")
    lines.append("")
    lines.append(f"theorem {p}Theta_nonneg : 0 <= {p}Theta := by")
    lines.append(f"  norm_num [{p}Theta]")
    lines.append("")
    lines.append(f"theorem {p}Split :")
    lines.append("    forall v : CoeffIndex23 -> Real,")
    lines.append(f"      Q3.Proofs.quadForm {p}C v =")
    lines.append(f"        Q3.Proofs.quadForm {p}D v +")
    lines.append(f"          {p}Theta * Q3.Proofs.quadForm {p}R v := by")
    lines.append(f"  exact quadForm_scaled_sub_split {p}C {p}R {p}Theta")
    lines.append("")
    lines.append(f"def {p}PayloadData : CenteredCoeffPayloadData where")
    lines.append(f"  label := {block.label}")
    lines.append(f"  blockId := \"{block.block_id}\"")
    lines.append(f"  role := \"{block.role}\"")
    lines.append(f"  k := {block.k}")
    lines.append(f"  ell := {p}Ell")
    lines.append(f"  kappa := {p}Kappa")
    lines.append(f"  theta := {p}Theta")
    lines.append(f"  theta_nonneg := {p}Theta_nonneg")
    lines.append(f"  A := {p}A")
    lines.append(f"  P := {p}P")
    lines.append(f"  P0 := {p}P0")
    lines.append(f"  Q := {p}Q")
    lines.append(f"  C := {p}C")
    lines.append(f"  D := {p}D")
    lines.append(f"  R := {p}R")
    lines.append(f"  split := {p}Split")
    lines.append("")
    return "\n".join(line for line in lines if line is not None)


def emit(repo_dir: Path, plan_path: Path, output_path: Path) -> None:
    blocks = load_blocks(repo_dir, plan_path)
    chunks = [GENERATED_HEADER]
    for block in blocks:
        chunks.append(emit_block(block))
    chunks.append(GENERATED_FOOTER)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text("\n".join(chunks))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-dir", default=".")
    parser.add_argument(
        "--plan",
        default="docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json",
    )
    parser.add_argument(
        "--output",
        default="Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean",
    )
    args = parser.parse_args()

    repo_dir = Path(args.repo_dir).resolve()
    plan_path = repo_dir / args.plan
    output_path = repo_dir / args.output
    emit(repo_dir, plan_path, output_path)
    print(f"wrote {output_path}")


if __name__ == "__main__":
    main()
