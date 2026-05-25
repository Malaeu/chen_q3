#!/usr/bin/env python3
"""
Generate Lean radius-floor data for the active Step 32F coefficient blocks.

This is a proof-data bridge, not an analytic enclosure proof.  It consumes the
existing Step22 midpoint/radius CSV payloads and emits:

  * penalized radius matrices for D and R penalty forms;
  * conservative total-radius scalar floors;
  * remaining positive interval floors `midpoint_floor - radius_floor`;
  * generic lower-bound adapters parameterized by the future analytic hbox.

The future analytic enclosure node only has to prove the entrywise hbox between
the analytic penalized matrices and the midpoint penalized matrices.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


HEADER = """import Q3.Proofs.PSD_CenteredCoeffPenaltyLDLImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffRadiusFloorImport

open CenteredCoeffPayloadImport
open CenteredCoeffPenaltyImport

/-!
Radius-floor import for the active Step 32F coefficient blocks.

The imported midpoint LDL certificates prove lower bounds for midpoint
penalized matrices.  This file records conservative radius floors and exposes
generic adapters: once a future analytic enclosure proves an entrywise hbox for
the analytic penalized matrix, the midpoint certificate transfers with the
remaining positive floor.
-/

"""

FOOTER = """
end CenteredCoeffRadiusFloorImport
end PSDpd
end Q3
"""


@dataclass(frozen=True)
class Block:
    prefix: str
    midpoint_csv: Path
    radius_csv: Path
    kappa: Fraction
    theta: Fraction
    tau_d: Fraction
    tau_r: Fraction
    floor_d: Fraction
    floor_r: Fraction


def dec_frac(text: str) -> Fraction:
    return Fraction(Decimal(text.strip()))


def lean_rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"(({value.numerator} : Rat))"
    return f"(({value.numerator} : Rat) / {value.denominator})"


def read_csv_matrix(path: Path, column: str) -> dict[str, dict[tuple[int, int], Fraction]]:
    out: dict[str, dict[tuple[int, int], Fraction]] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row["matrix"].strip()
            i = int(row["i"])
            j = int(row["j"])
            value = dec_frac(row[column])
            out.setdefault(name, {})[(i, j)] = value
    return out


def sym_get(mat: dict[tuple[int, int], Fraction], i: int, j: int) -> Fraction:
    return mat.get((i, j), mat.get((j, i), Fraction(0)))


def q_get(mat: dict[tuple[int, int], Fraction], r: int, i: int) -> Fraction:
    return mat.get((r, i), Fraction(0))


def qTq_radius(
    q_mid: dict[tuple[int, int], Fraction],
    q_rad: dict[tuple[int, int], Fraction],
    n: int,
    rows: int,
) -> list[list[Fraction]]:
    out: list[list[Fraction]] = []
    for i in range(n):
        row: list[Fraction] = []
        for j in range(n):
            total = Fraction(0)
            for r in range(rows):
                qi = q_get(q_mid, r, i)
                qj = q_get(q_mid, r, j)
                ri = q_get(q_rad, r, i)
                rj = q_get(q_rad, r, j)
                total += abs(qi) * rj + abs(qj) * ri + ri * rj
            row.append(total)
        out.append(row)
    return out


def square_radius_matrices(block: Block) -> tuple[list[list[Fraction]], list[list[Fraction]], list[list[Fraction]]]:
    mids = read_csv_matrix(block.midpoint_csv, "mid")
    rads = read_csv_matrix(block.radius_csv, "rad")
    n = 23
    rows = 2
    qtq = qTq_radius(mids["Q"], rads["Q"], n, rows)
    d_rad: list[list[Fraction]] = []
    r_rad: list[list[Fraction]] = []
    for i in range(n):
        d_row: list[Fraction] = []
        r_row: list[Fraction] = []
        for j in range(n):
            a = sym_get(rads["A"], i, j)
            p = sym_get(rads["P"], i, j)
            p0 = sym_get(rads["P0"], i, j)
            d_row.append((1 - block.theta) * a + p + block.theta * abs(block.kappa) * p0)
            r_row.append(a + abs(block.kappa) * p0)
        d_rad.append(d_row)
        r_rad.append(r_row)
    d_penalty = [
        [d_rad[i][j] + abs(block.tau_d) * qtq[i][j] for j in range(n)]
        for i in range(n)
    ]
    r_penalty = [
        [r_rad[i][j] + abs(block.tau_r) * qtq[i][j] for j in range(n)]
        for i in range(n)
    ]
    return qtq, d_penalty, r_penalty


def emit_matrix_entry(name: str, matrix: list[list[Fraction]]) -> list[str]:
    lines = [f"def {name}EntryRat : Nat -> Nat -> Rat"]
    for i, row in enumerate(matrix):
        for j, value in enumerate(row):
            if value != 0:
                lines.append(f"  | {i}, {j} => {lean_rat(value)}")
    lines.append("  | _, _ => 0")
    lines.append("")
    return lines


def emit_radius_pack(block: Block, kind: str, matrix: list[list[Fraction]]) -> list[str]:
    # kind is "D" or "R".
    prefix = block.prefix
    mat_name = f"{prefix}{kind}PenaltyRadius"
    floor = sum((value for row in matrix for value in row), Fraction(0))
    mid_floor = block.floor_d if kind == "D" else block.floor_r
    interval_floor = mid_floor - floor
    if interval_floor <= 0:
        raise SystemExit(
            f"{prefix}{kind}: interval floor is not positive: {interval_floor}"
        )
    existing_lower = f"{prefix}{kind}LowerBound_ldl"
    tau = f"{prefix}Tau{kind}"
    mid_matrix = f"{prefix}{kind}"
    mid_q = f"{prefix}Q"
    mid_floor_name = f"{prefix}{kind}Floor"

    lines: list[str] = []
    lines.extend(emit_matrix_entry(f"{mat_name}", matrix))
    lines.append(f"def {mat_name}Rat : Matrix CoeffIndex23 CoeffIndex23 Rat :=")
    lines.append(f"  fun i j => {mat_name}EntryRat i.val j.val")
    lines.append("")
    lines.append(f"def {mat_name} : Matrix CoeffIndex23 CoeffIndex23 Real :=")
    lines.append(f"  fun i j => ({mat_name}Rat i j : Real)")
    lines.append("")
    lines.append(f"def {mat_name}FloorRat : Rat := {lean_rat(floor)}")
    lines.append(f"def {mat_name}Floor : Real := ({mat_name}FloorRat : Real)")
    lines.append("")
    lines.append(f"def {prefix}{kind}IntervalFloorRat : Rat :=")
    lines.append(f"  {mid_floor_name}Rat - {mat_name}FloorRat")
    lines.append(f"def {prefix}{kind}IntervalFloor : Real :=")
    lines.append(f"  ({prefix}{kind}IntervalFloorRat : Real)")
    lines.append("")
    lines.append(f"theorem {mat_name}Rat_nonneg :")
    lines.append(f"    ∀ i j : CoeffIndex23, 0 <= {mat_name}Rat i j := by")
    lines.append("  native_decide")
    lines.append("")
    lines.append(f"theorem {mat_name}_nonneg :")
    lines.append(f"    ∀ i j : CoeffIndex23, 0 <= {mat_name} i j := by")
    lines.append("  intro i j")
    lines.append(f"  change 0 <= ({mat_name}Rat i j : Real)")
    lines.append(f"  exact_mod_cast {mat_name}Rat_nonneg i j")
    lines.append("")
    lines.append(f"theorem {mat_name}TotalRat_eq :")
    lines.append(f"    (∑ i : CoeffIndex23, ∑ j : CoeffIndex23, {mat_name}Rat i j) =")
    lines.append(f"      {mat_name}FloorRat := by")
    lines.append("  native_decide")
    lines.append("")
    lines.append(f"theorem {mat_name}Total_le :")
    lines.append(f"    (∑ i : CoeffIndex23, ∑ j : CoeffIndex23, {mat_name} i j) <=")
    lines.append(f"      {mat_name}Floor := by")
    lines.append(f"  change ((∑ i : CoeffIndex23, ∑ j : CoeffIndex23, {mat_name}Rat i j) : Real) <=")
    lines.append(f"      ({mat_name}FloorRat : Real)")
    lines.append(f"  exact_mod_cast le_of_eq {mat_name}TotalRat_eq")
    lines.append("")
    lines.append(f"theorem {mat_name}Energy_le :")
    lines.append(f"    ∀ v : CoeffIndex23 -> Real,")
    lines.append(f"      Q3.Proofs.quadFormAbsRadius {mat_name} v <=")
    lines.append(f"        {mat_name}Floor * Q3.Proofs.euclideanEnergy v :=")
    lines.append("  Q3.Proofs.quadFormAbsRadius_le_radiusFloor_mul_euclideanEnergy")
    lines.append(f"    {mat_name} {mat_name}Floor {mat_name}_nonneg {mat_name}Total_le")
    lines.append("")
    lines.append(f"theorem {prefix}{kind}IntervalFloorRat_pos :")
    lines.append(f"    0 < {prefix}{kind}IntervalFloorRat := by")
    lines.append("  native_decide")
    lines.append("")
    lines.append(f"theorem {prefix}{kind}IntervalFloor_pos :")
    lines.append(f"    0 < {prefix}{kind}IntervalFloor := by")
    lines.append(f"  change 0 < ({prefix}{kind}IntervalFloorRat : Real)")
    lines.append(f"  exact_mod_cast {prefix}{kind}IntervalFloorRat_pos")
    lines.append("")
    lines.append(f"theorem {prefix}{kind}MidpointLowerBound_with_radius_floor :")
    lines.append(f"    ∀ v : CoeffIndex23 -> Real,")
    lines.append(f"      ({prefix}{kind}IntervalFloor + {mat_name}Floor) *")
    lines.append(f"          Q3.Proofs.euclideanEnergy v <=")
    lines.append(f"        Q3.Proofs.quadForm")
    lines.append(f"          (Q3.Proofs.penaltyMatrix {mid_matrix} {mid_q} {tau}) v := by")
    lines.append("  intro v")
    lines.append(f"  have hfloor : {prefix}{kind}IntervalFloor + {mat_name}Floor = {mid_floor_name} := by")
    lines.append(f"    norm_num [{prefix}{kind}IntervalFloor, {prefix}{kind}IntervalFloorRat,")
    lines.append(f"      {mat_name}Floor, {mat_name}FloorRat, {mid_floor_name}, {mid_floor_name}Rat]")
    lines.append(f"  have hbase := {existing_lower} v")
    lines.append(f"  rw [Q3.Proofs.penaltyForm_eq_quadForm_penaltyMatrix] at hbase")
    lines.append("  simpa [hfloor] using hbase")
    lines.append("")
    lines.append(f"theorem {prefix}{kind}LowerBound_of_penalty_box")
    lines.append("    (M : Matrix CoeffIndex23 CoeffIndex23 Real)")
    lines.append("    (Q : Matrix BoundaryIndex2 CoeffIndex23 Real)")
    lines.append("    (hbox : Q3.Proofs.matrixEntrywiseAbsLe")
    lines.append(f"      (Q3.Proofs.penaltyMatrix M Q {tau})")
    lines.append(f"      (Q3.Proofs.penaltyMatrix {mid_matrix} {mid_q} {tau})")
    lines.append(f"      {mat_name}) :")
    lines.append(f"    ∀ v : CoeffIndex23 -> Real,")
    lines.append(f"      {prefix}{kind}IntervalFloor * Q3.Proofs.euclideanEnergy v <=")
    lines.append(f"        Q3.Proofs.penaltyForm M Q {tau} v :=")
    lines.append("  Q3.Proofs.penaltyForm_lower_bound_of_midpoint_lower_bound_and_radius_floor")
    lines.append(f"    M Q {tau} {prefix}{kind}IntervalFloor {mat_name}Floor")
    lines.append(f"    (Q3.Proofs.penaltyMatrix {mid_matrix} {mid_q} {tau})")
    lines.append(f"    {mat_name} hbox")
    lines.append(f"    {prefix}{kind}MidpointLowerBound_with_radius_floor")
    lines.append(f"    {mat_name}Energy_le")
    lines.append("")
    return lines


def build_blocks(root: Path) -> list[Block]:
    return [
        Block(
            prefix="primaryK11",
            midpoint_csv=root / "docs/insights/q3_psdpd_step22_midpoints_k11.csv",
            radius_csv=root / "docs/insights/q3_psdpd_step22_radii_k11.csv",
            kappa=Fraction(13, 4),
            theta=Fraction(1, 10000),
            tau_d=Fraction(25059361681363677, 50000000000000),
            tau_r=Fraction(7924465962305587, 500000000000),
            floor_d=Fraction(1528574356267451, 12500000000000000000),
            floor_r=Fraction(13569220780301769, 100000000000000000),
        ),
        Block(
            prefix="controlK9",
            midpoint_csv=root / "docs/insights/q3_psdpd_step22_midpoints_k9.csv",
            radius_csv=root / "docs/insights/q3_psdpd_step22_radii_k9.csv",
            kappa=Fraction(123, 40),
            theta=Fraction(1, 100000),
            tau_d=Fraction(100, 1),
            tau_r=Fraction(100000, 1),
            floor_d=Fraction(6318461466108783, 500000000000000000000),
            floor_r=Fraction(19590641960201293, 10000000000000000000),
        ),
    ]


def build_lean(root: Path) -> str:
    lines: list[str] = [HEADER.rstrip(), ""]
    for block in build_blocks(root):
        _, d_penalty, r_penalty = square_radius_matrices(block)
        lines.append(f"/-! Radius floors for `{block.prefix}`. -/")
        lines.append("")
        lines.extend(emit_radius_pack(block, "D", d_penalty))
        lines.extend(emit_radius_pack(block, "R", r_penalty))
    lines.append(FOOTER.strip())
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--out",
        default="Q3/Proofs/PSD_CenteredCoeffRadiusFloorImport.lean",
    )
    args = parser.parse_args()

    root = Path.cwd()
    out = root / args.out
    out.write_text(build_lean(root))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
