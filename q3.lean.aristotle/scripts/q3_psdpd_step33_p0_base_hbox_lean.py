#!/usr/bin/env python3
"""Generate the Step33 P0 base-hbox receiver layer.

This file deliberately emits a receiver, not the final scalar proof replay.
It compresses the 23x23 matrix hbox obligation to the 23 absolute packet
distances already present in the Step21/Step22 CSV payload.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


HEADER = """import Q3.Proofs.PSD_CenteredCoeffAnalyticP0Import

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffBaseP0HboxImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffAnalyticP0Import

/-!
Generated Step33 P0 base-hbox receiver layer.

The Step21/Step22 CSV payloads are Toeplitz/symmetric in `|i-j|`, and the
payload import exposes `P0`/`P0Radius` through compact absolute-distance tables.
This file does not prove the 23 scalar analytic interval enclosures.  Instead,
it proves the Lean receiver that turns those 23 absolute-distance hboxes into
the imported payload hbox.
-/

private theorem centeredBSplineR_even (k : Nat) (x : Real) :
    centeredBSplineR k (-x) = centeredBSplineR k x := by
  unfold centeredBSplineR
  have harg : bsplineScale k * (-x) = -(bsplineScale k * x) := by
    ring
  rw [harg, centeredCardinalBSpline_autocorrDegree_even k]

theorem centeredBSplineP0KernelProfile_even
    (k : Nat) (ell L d : Real) :
    centeredBSplineP0KernelProfile k ell L (-d) =
      centeredBSplineP0KernelProfile k ell L d := by
  unfold centeredBSplineP0KernelProfile
  apply intervalIntegral.integral_congr
  intro a _ha
  change
    Real.exp (a / 2) *
        (centeredBSplineR k ((-d - a) / ell) +
          centeredBSplineR k ((-d + a) / ell)) =
      Real.exp (a / 2) *
        (centeredBSplineR k ((d - a) / ell) +
          centeredBSplineR k ((d + a) / ell))
  have hleft : (-d - a) / ell = -((d + a) / ell) := by
    ring
  have hright : (-d + a) / ell = -((d - a) / ell) := by
    ring
  rw [hleft, hright, centeredBSplineR_even, centeredBSplineR_even]
  ring

def coeffAbsDistanceNat (i j : CoeffIndex23) : Nat :=
  if i.1 ≤ j.1 then j.1 - i.1 else i.1 - j.1

theorem coeffAbsDistanceNat_lt_23 (i j : CoeffIndex23) :
    coeffAbsDistanceNat i j < 23 := by
  unfold coeffAbsDistanceNat
  by_cases h : i.1 ≤ j.1
  · simp [h]
    exact lt_of_le_of_lt (Nat.sub_le j.1 i.1) j.2
  · simp [h]
    exact lt_of_le_of_lt (Nat.sub_le i.1 j.1) i.2

def coeffAbsDistanceFin (i j : CoeffIndex23) : CoeffIndex23 :=
  ⟨coeffAbsDistanceNat i j, coeffAbsDistanceNat_lt_23 i j⟩

private theorem abs_sub_le_of_lower_upper
    (x mid rad : Real)
    (hLower : mid - rad <= x)
    (hUpper : x <= mid + rad) :
    |x - mid| <= rad := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

"""

FOOTER = """
end CenteredCoeffBaseP0HboxImport
end PSDpd
end Q3
"""


@dataclass(frozen=True)
class Block:
    prefix: str
    theorem_prefix: str
    k: int
    ell: str
    mid_csv: Path
    rad_csv: Path


def decimal_to_lean_real(raw: str) -> str:
    dec = Decimal(str(raw))
    sign, digits, exp = dec.as_tuple()
    n = int("".join(str(d) for d in digits)) if digits else 0
    if sign:
        n = -n
    if exp >= 0:
        num = n * (10**exp)
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
    return f"(({num} : Real) / ({den} : Real))"


def read_p0(path: Path, col: str) -> dict[tuple[int, int], str]:
    out: dict[tuple[int, int], str] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["matrix"].strip() != "P0":
                continue
            out[(int(row["i"]), int(row["j"]))] = row[col].strip()
    expected = {(i, j) for i in range(23) for j in range(23)}
    missing = expected.difference(out)
    if missing:
        raise SystemExit(f"{path}: missing P0 entries, first={sorted(missing)[:5]}")
    return out


def abs_distance_values(block: Block) -> dict[int, tuple[str, str]]:
    mids = read_p0(block.mid_csv, "mid")
    rads = read_p0(block.rad_csv, "rad")
    out: dict[int, tuple[str, str]] = {}
    for dist in range(23):
        vals = {
            (mids[(i, j)], rads[(i, j)])
            for i in range(23)
            for j in range(23)
            if abs(j - i) == dist
        }
        if len(vals) != 1:
            raise SystemExit(
                f"{block.prefix}: P0 is not absolute-distance compressed at "
                f"distance {dist}; values={len(vals)}"
            )
        out[dist] = vals.pop()
    return out


def dist_name(dist: int) -> str:
    return "zero" if dist == 0 else f"abs{dist}"


def real_dist(dist: int) -> str:
    if dist == 0:
        return "(0 : Real)"
    frac = Fraction(dist, 4)
    if frac.denominator == 1:
        return f"({frac.numerator} : Real)"
    return f"(({frac.numerator} : Real) / ({frac.denominator} : Real))"


def real_index_dist(dist: int) -> str:
    return f"(({dist} : Real) / (4 : Real))"


def emit_abs_tables(block: Block) -> str:
    values = abs_distance_values(block)
    lines: list[str] = []
    lines.append(f"def {block.theorem_prefix}P0AbsEntryRat : Nat -> Rat")
    for dist in range(23):
        mid, _rad = values[dist]
        lines.append(f"  | {dist} => {decimal_to_lean_rat(mid)}")
    lines.append("  | _ => 0")
    lines.append("")
    lines.append(f"def {block.theorem_prefix}P0RadiusAbsEntryRat : Nat -> Rat")
    for dist in range(23):
        _mid, rad = values[dist]
        lines.append(f"  | {dist} => {decimal_to_lean_rat(rad)}")
    lines.append("  | _ => 0")
    lines.append("")
    lines.append(
        f"def {block.theorem_prefix}P0AbsDistanceMatrix : "
        "Matrix CoeffIndex23 CoeffIndex23 Real :="
    )
    lines.append(
        f"  fun i j => ({block.theorem_prefix}P0AbsEntryRat "
        "(coeffAbsDistanceNat i j) : Real)"
    )
    lines.append("")
    lines.append(
        f"def {block.theorem_prefix}P0RadiusAbsDistanceMatrix : "
        "Matrix CoeffIndex23 CoeffIndex23 Real :="
    )
    lines.append(
        f"  fun i j => ({block.theorem_prefix}P0RadiusAbsEntryRat "
        "(coeffAbsDistanceNat i j) : Real)"
    )
    lines.append("")
    return "\n".join(lines)


def decimal_to_lean_rat(raw: str) -> str:
    dec = Decimal(str(raw))
    sign, digits, exp = dec.as_tuple()
    n = int("".join(str(d) for d in digits)) if digits else 0
    if sign:
        n = -n
    if exp >= 0:
        num = n * (10**exp)
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
        return f"(({num} : Rat))"
    return f"(({num} : Rat) / {den})"


def emit_payload_entry_theorems(block: Block) -> str:
    return "\n".join(
        [
            f"private theorem {block.theorem_prefix}P0_entry_from_abs_distance "
            "(i j : CoeffIndex23) :",
            f"    {block.theorem_prefix}P0 i j =",
            f"      ({block.theorem_prefix}P0AbsDistanceEntryRat "
            "(natAbsDiff (i.1) (j.1)) : Real) := by",
            "  rfl",
            "",
            f"private theorem {block.theorem_prefix}P0Radius_entry_from_abs_distance "
            "(i j : CoeffIndex23) :",
            f"    {block.theorem_prefix}P0Radius i j =",
            f"      ({block.theorem_prefix}P0RadiusAbsDistanceEntryRat "
            "(natAbsDiff (i.1) (j.1)) : Real) := by",
            "  rfl",
            "",
        ]
    )


def emit_structure(block: Block) -> str:
    lines: list[str] = []
    lines.append(
        f"structure {block.theorem_prefix}AnalyticP0AbsDistanceHboxCert : Prop where"
    )
    lines.append("  h : ∀ n : CoeffIndex23,")
    lines.append(
        "    |centeredBSplineP0KernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)} (3 : Real) "
        "((n.1 : Real) / (4 : Real)) - "
        f"({block.theorem_prefix}P0AbsDistanceEntryRat (n.1) : Real)| <= "
        f"({block.theorem_prefix}P0RadiusAbsDistanceEntryRat (n.1) : Real)"
    )
    lines.append("")
    return "\n".join(lines)


def emit_interval_receiver(block: Block) -> str:
    p = block.theorem_prefix
    profile = (
        "centeredBSplineP0KernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)} (3 : Real) "
        "((n.1 : Real) / (4 : Real))"
    )
    mid = f"({p}P0AbsDistanceEntryRat (n.1) : Real)"
    rad = f"({p}P0RadiusAbsDistanceEntryRat (n.1) : Real)"
    lines: list[str] = []
    lines.append(f"def {p}AnalyticP0AbsDistanceLower (n : CoeffIndex23) : Real :=")
    lines.append(f"  {mid} - {rad}")
    lines.append("")
    lines.append(f"def {p}AnalyticP0AbsDistanceUpper (n : CoeffIndex23) : Real :=")
    lines.append(f"  {mid} + {rad}")
    lines.append("")
    lines.append(
        f"structure {p}AnalyticP0AbsDistanceIntervalCert : Prop where"
    )
    lines.append("  hLower : ∀ n : CoeffIndex23,")
    lines.append(f"    {p}AnalyticP0AbsDistanceLower n <= {profile}")
    lines.append("  hUpper : ∀ n : CoeffIndex23,")
    lines.append(f"    {profile} <= {p}AnalyticP0AbsDistanceUpper n")
    lines.append("")
    lines.append(
        f"theorem {p}AnalyticP0AbsDistanceHboxCert_of_interval_cert"
    )
    lines.append(f"    (cert : {p}AnalyticP0AbsDistanceIntervalCert) :")
    lines.append(f"    {p}AnalyticP0AbsDistanceHboxCert := by")
    lines.append("  refine ⟨?_⟩")
    lines.append("  intro n")
    lines.append("  exact abs_sub_le_of_lower_upper")
    lines.append(
        "    (x := centeredBSplineP0KernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)} (3 : Real) "
        "((n.1 : Real) / (4 : Real)))"
    )
    lines.append(f"    (mid := {mid})")
    lines.append(f"    (rad := {rad})")
    lines.append(
        f"    (by simpa [{p}AnalyticP0AbsDistanceLower] using cert.hLower n)"
    )
    lines.append(
        f"    (by simpa [{p}AnalyticP0AbsDistanceUpper] using cert.hUpper n)"
    )
    lines.append("")
    return "\n".join(lines)


def emit_distance_bounds_structure(block: Block) -> str:
    p = block.theorem_prefix
    profile = (
        "centeredBSplineP0KernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)} (3 : Real)"
    )
    lines: list[str] = []
    lines.append(f"structure {p}AnalyticP0AbsDistanceBoundsCert : Prop where")
    for dist in range(23):
        fin_dist = f"(⟨{dist}, by norm_num⟩ : CoeffIndex23)"
        dterm = real_index_dist(dist)
        lines.append(f"  hLower{dist} :")
        lines.append(
            f"    {p}AnalyticP0AbsDistanceLower {fin_dist} <= "
            f"{profile} {dterm}"
        )
        lines.append(f"  hUpper{dist} :")
        lines.append(
            f"    {profile} {dterm} <= "
            f"{p}AnalyticP0AbsDistanceUpper {fin_dist}"
        )
    lines.append("")
    return "\n".join(lines)


def emit_interval_constructor(block: Block) -> str:
    p = block.theorem_prefix
    profile = (
        "centeredBSplineP0KernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)} (3 : Real)"
    )
    lines: list[str] = []
    lines.append(f"theorem {p}AnalyticP0AbsDistanceIntervalCert_of_distance_bounds")
    for dist in range(23):
        fin_dist = f"(⟨{dist}, by norm_num⟩ : CoeffIndex23)"
        dterm = real_index_dist(dist)
        lines.append(f"    (hLower{dist} :")
        lines.append(
            f"      {p}AnalyticP0AbsDistanceLower {fin_dist} <= "
            f"{profile} {dterm})"
        )
        lines.append(f"    (hUpper{dist} :")
        lines.append(
            f"      {profile} {dterm} <= "
            f"{p}AnalyticP0AbsDistanceUpper {fin_dist})"
        )
    lines.append(f"    : {p}AnalyticP0AbsDistanceIntervalCert := by")
    lines.append("  constructor")
    lines.append("  · intro n")
    lines.append("    fin_cases n")
    for dist in range(23):
        lines.append(f"    · simpa using hLower{dist}")
    lines.append("  · intro n")
    lines.append("    fin_cases n")
    for dist in range(23):
        lines.append(f"    · simpa using hUpper{dist}")
    lines.append("")
    return "\n".join(lines)


def emit_interval_constructor_from_cert(block: Block) -> str:
    p = block.theorem_prefix
    lines: list[str] = []
    lines.append(f"theorem {p}AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert")
    lines.append(f"    (cert : {p}AnalyticP0AbsDistanceBoundsCert) :")
    lines.append(f"    {p}AnalyticP0AbsDistanceIntervalCert := by")
    lines.append(f"  exact {p}AnalyticP0AbsDistanceIntervalCert_of_distance_bounds")
    for dist in range(23):
        lines.append(f"    cert.hLower{dist}")
        lines.append(f"    cert.hUpper{dist}")
    lines.append("")
    return "\n".join(lines)


def emit_case(block: Block, i: int, j: int) -> list[str]:
    dist = abs(j - i)
    mid, rad = abs_distance_values(block)[dist]
    dterm = real_dist(dist)
    fin_dist = f"(⟨{dist}, by norm_num⟩ : CoeffIndex23)"
    lines = [
        "  · rw [",
        f"      {block.theorem_prefix}AnalyticP0_entry,",
        f"      {block.theorem_prefix}Center_sub_eq_index_delta,",
        f"      {block.theorem_prefix}P0_entry_from_abs_distance,",
        f"      {block.theorem_prefix}P0Radius_entry_from_abs_distance]",
        "    norm_num [",
        f"      {block.theorem_prefix}Ell, {block.theorem_prefix}EllRat,",
        "      activeL3SupportRadius, activeL3SupportRadiusRat,",
        f"      {block.theorem_prefix}P0AbsDistanceEntryRat,",
        f"      {block.theorem_prefix}P0RadiusAbsDistanceEntryRat,",
        "      natAbsDiff]",
    ]
    signed = j - i
    if signed < 0:
        lines.append(
            "    change "
            "|centeredBSplineP0KernelProfile "
            f"{block.k} {decimal_to_lean_real(block.ell)} (3 : Real) "
            f"(-{dterm}) - {decimal_to_lean_real(mid)}| <= "
            f"{decimal_to_lean_real(rad)}"
        )
        lines.append("    rw [centeredBSplineP0KernelProfile_even]")
    else:
        lines.append(
            "    change "
            "|centeredBSplineP0KernelProfile "
            f"{block.k} {decimal_to_lean_real(block.ell)} (3 : Real) "
            f"{dterm} - {decimal_to_lean_real(mid)}| <= "
            f"{decimal_to_lean_real(rad)}"
        )
    lines.append(f"    have hcert := cert.h {fin_dist}")
    lines.append(
        "    norm_num ["
        f"{block.theorem_prefix}P0AbsDistanceEntryRat, "
        f"{block.theorem_prefix}P0RadiusAbsDistanceEntryRat] at hcert"
    )
    lines.append("    simpa using hcert")
    return lines


def fin_lit(n: int) -> str:
    return f"(⟨{n}, by norm_num⟩ : CoeffIndex23)"


def emit_row_theorem(block: Block, i: int) -> str:
    lines: list[str] = []
    row_name = (
        f"{block.theorem_prefix}AnalyticP0_entry_hbox_row_{i}_"
        "of_abs_distance_cert"
    )
    lines.append(f"private theorem {row_name}")
    lines.append(
        f"    (cert : {block.theorem_prefix}AnalyticP0AbsDistanceHboxCert)"
        " (j : CoeffIndex23) :"
    )
    lines.append(
        f"    |{block.theorem_prefix}AnalyticP0 {fin_lit(i)} j - "
        f"{block.theorem_prefix}P0 {fin_lit(i)} j| <= "
        f"{block.theorem_prefix}P0Radius {fin_lit(i)} j := by"
    )
    lines.append("  fin_cases j")
    for j in range(23):
        lines.extend(emit_case(block, i, j))
    lines.append("")
    return "\n".join(lines)


def emit_theorem(block: Block) -> str:
    lines: list[str] = []
    for i in range(23):
        lines.append(emit_row_theorem(block, i))
    lines.append(
        f"theorem {block.theorem_prefix}AnalyticP0_entry_hbox_of_abs_distance_cert"
    )
    lines.append(
        f"    (cert : {block.theorem_prefix}AnalyticP0AbsDistanceHboxCert) :"
    )
    lines.append(
        f"    Q3.Proofs.matrixEntrywiseAbsLe {block.theorem_prefix}AnalyticP0 "
        f"{block.theorem_prefix}P0 "
        f"{block.theorem_prefix}P0Radius := by"
    )
    lines.append("  intro i j")
    for i in range(23):
        row_name = (
            f"{block.theorem_prefix}AnalyticP0_entry_hbox_row_{i}_"
            "of_abs_distance_cert"
        )
        prefix = "  fin_cases i" if i == 0 else ""
        if prefix:
            lines.append(prefix)
        lines.append(f"  · exact {row_name} cert j")
    lines.append("")
    return "\n".join(lines)


def emit(blocks: list[Block], output_path: Path) -> None:
    chunks = [HEADER]
    for block in blocks:
        chunks.append(emit_payload_entry_theorems(block))
        chunks.append(emit_structure(block))
        chunks.append(emit_interval_receiver(block))
        chunks.append(emit_distance_bounds_structure(block))
        chunks.append(emit_interval_constructor(block))
        chunks.append(emit_interval_constructor_from_cert(block))
        chunks.append(emit_theorem(block))
    chunks.append(FOOTER)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text("\n".join(chunks))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-dir", default=".")
    parser.add_argument(
        "--output",
        default="Q3/Proofs/PSD_CenteredCoeffBaseP0HboxImport.lean",
    )
    parser.add_argument("--include-control", action="store_true")
    args = parser.parse_args()

    repo_dir = Path(args.repo_dir).resolve()
    insights = repo_dir / "docs/insights"
    blocks = [
        Block(
            prefix="primaryK11",
            theorem_prefix="primaryK11",
            k=11,
            ell="0.30",
            mid_csv=insights / "q3_psdpd_step22_midpoints_k11.csv",
            rad_csv=insights / "q3_psdpd_step22_radii_k11.csv",
        )
    ]
    if args.include_control:
        blocks.append(
            Block(
                prefix="controlK9",
                theorem_prefix="controlK9",
                k=9,
                ell="0.30",
                mid_csv=insights / "q3_psdpd_step22_midpoints_k9.csv",
                rad_csv=insights / "q3_psdpd_step22_radii_k9.csv",
            )
        )
    emit(blocks, repo_dir / args.output)
    print(f"wrote {repo_dir / args.output}")


if __name__ == "__main__":
    main()
