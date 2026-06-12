#!/usr/bin/env python3
"""Generate the Step33 A base-hbox receiver layer.

This receiver follows the same anti-swamp shape as the P0 receiver: the
Step22 A payload is compressed by absolute packet distance, and Lean dispatches
the full 23x23 matrix hbox from 23 scalar distance facts.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


HEADER = """import Q3.Proofs.PSD_CenteredCoeffBaseHboxImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffBaseAHboxImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport

/-!
Generated Step33 A base-hbox receiver layer.

The Step22 `A` payloads are Toeplitz/symmetric in `|i-j|`, and the payload
import exposes `A`/`ARadius` through compact absolute-distance tables.  This
file proves the Lean receiver that turns 23 absolute-distance hboxes into the
imported payload hbox for both active primary/control blocks.
-/

theorem centeredBSplineArchKernelProfile_even
    (k : Nat) (ell d : Real) :
    centeredBSplineArchKernelProfile k ell (-d) =
      centeredBSplineArchKernelProfile k ell d := by
  unfold centeredBSplineArchKernelProfile
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  have harg : t * (-d) = -(t * d) := by
    ring
  rw [harg, Real.cos_neg]

theorem primaryK11AnalyticA_entry (i j : CoeffIndex23) :
    primaryK11AnalyticA i j =
      centeredBSplineArchKernelProfile
        11 primaryK11Ell (primaryK11Center j - primaryK11Center i) := by
  simp [primaryK11AnalyticA, primaryK11CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    PacketKernelPairingData.matrix, matrixOfKernel,
    centeredBSplineCoeffAnalyticKernelContract,
    centeredBSplineArchPacketCoeffKernelData]

theorem controlK9AnalyticA_entry (i j : CoeffIndex23) :
    controlK9AnalyticA i j =
      centeredBSplineArchKernelProfile
        9 controlK9Ell (controlK9Center j - controlK9Center i) := by
  simp [controlK9AnalyticA, controlK9CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    PacketKernelPairingData.matrix, matrixOfKernel,
    centeredBSplineCoeffAnalyticKernelContract,
    centeredBSplineArchPacketCoeffKernelData]

private theorem abs_sub_le_of_lower_upper
    (x mid rad : Real)
    (hLower : mid - rad <= x)
    (hUpper : x <= mid + rad) :
    |x - mid| <= rad := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

"""

FOOTER = """
end CenteredCoeffBaseAHboxImport
end PSDpd
end Q3
"""


@dataclass(frozen=True)
class Block:
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


def real_sub_mid_expr(profile: str, raw_mid: str) -> str:
    dec = Decimal(str(raw_mid))
    if dec < 0:
        return f"{profile} + {decimal_to_lean_real(str(-dec))}"
    return f"{profile} - {decimal_to_lean_real(raw_mid)}"


def read_a(path: Path, col: str) -> dict[tuple[int, int], str]:
    out: dict[tuple[int, int], str] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["matrix"].strip() != "A":
                continue
            out[(int(row["i"]), int(row["j"]))] = row[col].strip()
    expected = {(i, j) for i in range(23) for j in range(23)}
    missing = expected.difference(out)
    if missing:
        raise SystemExit(f"{path}: missing A entries, first={sorted(missing)[:5]}")
    return out


def abs_distance_values(block: Block) -> dict[int, tuple[str, str]]:
    mids = read_a(block.mid_csv, "mid")
    rads = read_a(block.rad_csv, "rad")
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
                f"{block.theorem_prefix}: A is not absolute-distance "
                f"compressed at distance {dist}; values={len(vals)}"
            )
        out[dist] = vals.pop()
    return out


def real_dist(dist: int) -> str:
    if dist == 0:
        return "(0 : Real)"
    frac = Fraction(dist, 4)
    if frac.denominator == 1:
        return f"({frac.numerator} : Real)"
    return f"(({frac.numerator} : Real) / ({frac.denominator} : Real))"


def real_index_dist(dist: int) -> str:
    return f"(({dist} : Real) / (4 : Real))"


def fin_lit(n: int) -> str:
    return f"(⟨{n}, by norm_num⟩ : CoeffIndex23)"


def emit_payload_entry_theorems(block: Block) -> str:
    p = block.theorem_prefix
    return "\n".join(
        [
            f"private theorem {p}A_entry_from_abs_distance (i j : CoeffIndex23) :",
            f"    {p}A i j =",
            f"      ({p}AAbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by",
            "  rfl",
            "",
            f"private theorem {p}ARadius_entry_from_abs_distance (i j : CoeffIndex23) :",
            f"    {p}ARadius i j =",
            f"      ({p}ARadiusAbsDistanceEntryRat (natAbsDiff (i.1) (j.1)) : Real) := by",
            "  rfl",
            "",
        ]
    )


def emit_structure(block: Block) -> str:
    p = block.theorem_prefix
    lines: list[str] = []
    lines.append(f"structure {p}AnalyticAAbsDistanceHboxCert : Prop where")
    lines.append("  h : ∀ n : CoeffIndex23,")
    lines.append(
        "    |centeredBSplineArchKernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)} "
        "((n.1 : Real) / (4 : Real)) - "
        f"({p}AAbsDistanceEntryRat (n.1) : Real)| <= "
        f"({p}ARadiusAbsDistanceEntryRat (n.1) : Real)"
    )
    lines.append("")
    return "\n".join(lines)


def emit_interval_receiver(block: Block) -> str:
    p = block.theorem_prefix
    profile = (
        "centeredBSplineArchKernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)} "
        "((n.1 : Real) / (4 : Real))"
    )
    mid = f"({p}AAbsDistanceEntryRat (n.1) : Real)"
    rad = f"({p}ARadiusAbsDistanceEntryRat (n.1) : Real)"
    lines: list[str] = []
    lines.append(f"def {p}AnalyticAAbsDistanceLower (n : CoeffIndex23) : Real :=")
    lines.append(f"  {mid} - {rad}")
    lines.append("")
    lines.append(f"def {p}AnalyticAAbsDistanceUpper (n : CoeffIndex23) : Real :=")
    lines.append(f"  {mid} + {rad}")
    lines.append("")
    lines.append(f"structure {p}AnalyticAAbsDistanceIntervalCert : Prop where")
    lines.append("  hLower : ∀ n : CoeffIndex23,")
    lines.append(f"    {p}AnalyticAAbsDistanceLower n <= {profile}")
    lines.append("  hUpper : ∀ n : CoeffIndex23,")
    lines.append(f"    {profile} <= {p}AnalyticAAbsDistanceUpper n")
    lines.append("")
    lines.append(f"theorem {p}AnalyticAAbsDistanceHboxCert_of_interval_cert")
    lines.append(f"    (cert : {p}AnalyticAAbsDistanceIntervalCert) :")
    lines.append(f"    {p}AnalyticAAbsDistanceHboxCert := by")
    lines.append("  refine ⟨?_⟩")
    lines.append("  intro n")
    lines.append("  exact abs_sub_le_of_lower_upper")
    lines.append(
        "    (x := centeredBSplineArchKernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)} "
        "((n.1 : Real) / (4 : Real)))"
    )
    lines.append(f"    (mid := {mid})")
    lines.append(f"    (rad := {rad})")
    lines.append(
        f"    (by simpa [{p}AnalyticAAbsDistanceLower] using cert.hLower n)"
    )
    lines.append(
        f"    (by simpa [{p}AnalyticAAbsDistanceUpper] using cert.hUpper n)"
    )
    lines.append("")
    return "\n".join(lines)


def emit_distance_bounds_structure(block: Block) -> str:
    p = block.theorem_prefix
    profile = (
        "centeredBSplineArchKernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)}"
    )
    lines: list[str] = []
    lines.append(f"structure {p}AnalyticAAbsDistanceBoundsCert : Prop where")
    for dist in range(23):
        fin_dist = f"(⟨{dist}, by norm_num⟩ : CoeffIndex23)"
        dterm = real_index_dist(dist)
        lines.append(f"  hLower{dist} :")
        lines.append(
            f"    {p}AnalyticAAbsDistanceLower {fin_dist} <= "
            f"{profile} {dterm}"
        )
        lines.append(f"  hUpper{dist} :")
        lines.append(
            f"    {profile} {dterm} <= "
            f"{p}AnalyticAAbsDistanceUpper {fin_dist}"
        )
    lines.append("")
    return "\n".join(lines)


def emit_interval_constructor(block: Block) -> str:
    p = block.theorem_prefix
    profile = (
        "centeredBSplineArchKernelProfile "
        f"{block.k} {decimal_to_lean_real(block.ell)}"
    )
    lines: list[str] = []
    lines.append(f"theorem {p}AnalyticAAbsDistanceIntervalCert_of_distance_bounds")
    for dist in range(23):
        fin_dist = f"(⟨{dist}, by norm_num⟩ : CoeffIndex23)"
        dterm = real_index_dist(dist)
        lines.append(f"    (hLower{dist} :")
        lines.append(
            f"      {p}AnalyticAAbsDistanceLower {fin_dist} <= "
            f"{profile} {dterm})"
        )
        lines.append(f"    (hUpper{dist} :")
        lines.append(
            f"      {profile} {dterm} <= "
            f"{p}AnalyticAAbsDistanceUpper {fin_dist})"
        )
    lines.append(f"    : {p}AnalyticAAbsDistanceIntervalCert := by")
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
    lines.append(f"theorem {p}AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert")
    lines.append(f"    (cert : {p}AnalyticAAbsDistanceBoundsCert) :")
    lines.append(f"    {p}AnalyticAAbsDistanceIntervalCert := by")
    lines.append(f"  exact {p}AnalyticAAbsDistanceIntervalCert_of_distance_bounds")
    for dist in range(23):
        lines.append(f"    cert.hLower{dist}")
        lines.append(f"    cert.hUpper{dist}")
    lines.append("")
    return "\n".join(lines)


def emit_case(block: Block, i: int, j: int) -> list[str]:
    p = block.theorem_prefix
    dist = abs(j - i)
    mid, rad = abs_distance_values(block)[dist]
    dterm = real_dist(dist)
    fin_dist = f"(⟨{dist}, by norm_num⟩ : CoeffIndex23)"
    lines = [
        "  · rw [",
        f"      {p}AnalyticA_entry,",
        f"      {p}Center_sub_eq_index_delta,",
        f"      {p}A_entry_from_abs_distance,",
        f"      {p}ARadius_entry_from_abs_distance]",
        "    norm_num [",
        f"      {p}Ell, {p}EllRat,",
        f"      {p}AAbsDistanceEntryRat,",
        f"      {p}ARadiusAbsDistanceEntryRat,",
        "      natAbsDiff]",
    ]
    signed = j - i
    if signed < 0:
        profile = (
            "centeredBSplineArchKernelProfile "
            f"{block.k} {decimal_to_lean_real(block.ell)} (-{dterm})"
        )
        lines.append(
            "    change "
            f"|{real_sub_mid_expr(profile, mid)}| <= "
            f"{decimal_to_lean_real(rad)}"
        )
        lines.append("    rw [centeredBSplineArchKernelProfile_even]")
    else:
        profile = (
            "centeredBSplineArchKernelProfile "
            f"{block.k} {decimal_to_lean_real(block.ell)} {dterm}"
        )
        lines.append(
            "    change "
            f"|{real_sub_mid_expr(profile, mid)}| <= "
            f"{decimal_to_lean_real(rad)}"
        )
    lines.append(f"    have hcert := cert.h {fin_dist}")
    lines.append(
        "    norm_num ["
        f"{p}AAbsDistanceEntryRat, {p}ARadiusAbsDistanceEntryRat] at hcert"
    )
    lines.append("    simpa using hcert")
    return lines


def emit_row_theorem(block: Block, i: int) -> str:
    p = block.theorem_prefix
    row_name = f"{p}AnalyticA_entry_hbox_row_{i}_of_abs_distance_cert"
    lines: list[str] = []
    lines.append(f"private theorem {row_name}")
    lines.append(f"    (cert : {p}AnalyticAAbsDistanceHboxCert) (j : CoeffIndex23) :")
    lines.append(
        f"    |{p}AnalyticA {fin_lit(i)} j - "
        f"{p}A {fin_lit(i)} j| <= "
        f"{p}ARadius {fin_lit(i)} j := by"
    )
    lines.append("  fin_cases j")
    for j in range(23):
        lines.extend(emit_case(block, i, j))
    lines.append("")
    return "\n".join(lines)


def emit_theorem(block: Block) -> str:
    p = block.theorem_prefix
    lines: list[str] = []
    for i in range(23):
        lines.append(emit_row_theorem(block, i))
    lines.append(f"theorem {p}AnalyticA_entry_hbox_of_abs_distance_cert")
    lines.append(f"    (cert : {p}AnalyticAAbsDistanceHboxCert) :")
    lines.append(
        f"    Q3.Proofs.matrixEntrywiseAbsLe {p}AnalyticA "
        f"{p}A {p}ARadius := by"
    )
    lines.append("  intro i j")
    for i in range(23):
        row_name = f"{p}AnalyticA_entry_hbox_row_{i}_of_abs_distance_cert"
        if i == 0:
            lines.append("  fin_cases i")
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
        default="Q3/Proofs/PSD_CenteredCoeffBaseAHboxImport.lean",
    )
    parser.add_argument("--include-control", action="store_true")
    args = parser.parse_args()

    repo_dir = Path(args.repo_dir).resolve()
    insights = repo_dir / "docs/insights"
    blocks = [
        Block(
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
