#!/usr/bin/env python3
"""
Generate Lean parameter targets for the Step 32F finite penalty lower bounds.

This is intentionally not a positivity prover.  It reads the accepted Step 18
penalty-guard outputs, imports the exact `tau` and `safe_lower` values as
`Rat` constants with real casts, and emits narrow theorem targets:

  D lower bound + R lower bound
  -> FinitePenaltyLowerBoundCert
  -> FinitePenaltyCert

The next checker/proof generator should fill only those lower-bound hypotheses.
"""

from __future__ import annotations

import argparse
import csv
import math
import re
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path


GENERATED_HEADER = """import Q3.Proofs.PSD_CenteredCoeffPayloadImport
import Q3.Proofs.PSD_PenaltyCertificate

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPenaltyImport

open CenteredCoeffPayloadImport

/-!
Checked Step 18 penalty lower-bound parameters for the active Step 32F
coefficient blocks.

This generated file imports only exact parameter data and receiver adapters.
It does not prove the lower bounds.  The next proof-generating checker must
close the named `DLowerBound` and `RLowerBound` propositions below.
-/

"""

GENERATED_FOOTER = """
end CenteredCoeffPenaltyImport
end PSDpd
end Q3
"""


@dataclass(frozen=True)
class PenaltyBlock:
    block_id: str
    role: str
    prefix: str
    d_tau: str
    r_tau: str
    d_floor: str
    r_floor: str


def repo_path(repo_dir: Path, raw: str) -> Path:
    prefix = "q3.lean.aristotle/"
    candidates = [repo_dir / raw, repo_dir.parent / raw]
    if raw.startswith(prefix):
        candidates.append(repo_dir / raw[len(prefix):])
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return candidates[-1]


def output_path(repo_dir: Path, raw: str) -> Path:
    path = Path(raw)
    if path.is_absolute():
        return path
    return repo_dir / path


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
        return f"(({num} : Rat))"
    return f"(({num} : Rat) / {den})"


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


def extract_value(body: str, key: str) -> str:
    match = re.search(rf"^{re.escape(key)}\s+=\s+([0-9.eE+-]+)\s*$", body, re.MULTILINE)
    if not match:
        raise SystemExit(f"missing Step18 value {key!r}")
    return match.group(1)


def load_blocks(repo_dir: Path, manifest_path: Path) -> list[PenaltyBlock]:
    blocks: list[PenaltyBlock] = []
    with manifest_path.open() as f:
        reader = csv.DictReader(f)
        required = {"block_id", "role", "status", "dtheta_pass", "rkappa_pass", "stdout_path"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise SystemExit(f"{manifest_path}: missing columns {sorted(missing)}")
        for row in reader:
            if row["status"] != "PASS" or row["dtheta_pass"] != "True" or row["rkappa_pass"] != "True":
                raise SystemExit(f"{row['block_id']}: manifest row is not a passing penalty guard")
            stdout_path = repo_path(repo_dir, row["stdout_path"])
            if not stdout_path.exists():
                raise SystemExit(f"{row['block_id']}: missing Step18 output {stdout_path}")
            text = stdout_path.read_text()
            d_body = extract_section(text, "Dtheta")
            r_body = extract_section(text, "R_kappa")
            blocks.append(
                PenaltyBlock(
                    block_id=row["block_id"],
                    role=row["role"],
                    prefix=block_prefix(row["block_id"]),
                    d_tau=extract_value(d_body, "best_tau"),
                    r_tau=extract_value(r_body, "best_tau"),
                    d_floor=extract_value(d_body, "safe_lower"),
                    r_floor=extract_value(r_body, "safe_lower"),
                )
            )
    return blocks


def emit_block(block: PenaltyBlock) -> str:
    p = block.prefix
    lines: list[str] = []
    lines.append(f"/-- Step 18 penalty parameters for `{block.block_id}`. -/")
    lines.append(f"def {p}TauDRat : Rat := {decimal_to_lean(block.d_tau)}")
    lines.append(f"def {p}TauRRat : Rat := {decimal_to_lean(block.r_tau)}")
    lines.append(f"def {p}DFloorRat : Rat := {decimal_to_lean(block.d_floor)}")
    lines.append(f"def {p}RFloorRat : Rat := {decimal_to_lean(block.r_floor)}")
    lines.append("")
    lines.append(f"def {p}TauD : Real := ({p}TauDRat : Real)")
    lines.append(f"def {p}TauR : Real := ({p}TauRRat : Real)")
    lines.append(f"def {p}DFloor : Real := ({p}DFloorRat : Real)")
    lines.append(f"def {p}RFloor : Real := ({p}RFloorRat : Real)")
    lines.append("")
    lines.append(f"theorem {p}DFloorRat_pos : 0 < {p}DFloorRat := by")
    lines.append("  native_decide")
    lines.append("")
    lines.append(f"theorem {p}RFloorRat_pos : 0 < {p}RFloorRat := by")
    lines.append("  native_decide")
    lines.append("")
    lines.append(f"theorem {p}DFloor_pos : 0 < {p}DFloor := by")
    lines.append(f"  change 0 < ({p}DFloorRat : Real)")
    lines.append(f"  exact_mod_cast {p}DFloorRat_pos")
    lines.append("")
    lines.append(f"theorem {p}RFloor_pos : 0 < {p}RFloor := by")
    lines.append(f"  change 0 < ({p}RFloorRat : Real)")
    lines.append(f"  exact_mod_cast {p}RFloorRat_pos")
    lines.append("")
    lines.append(f"/-- Remaining checked lower-bound target for `{block.block_id}` / D. -/")
    lines.append(f"def {p}DLowerBound : Prop :=")
    lines.append("  ∀ v : CoeffIndex23 -> Real,")
    lines.append(f"    {p}DFloor * Q3.Proofs.euclideanEnergy v <=")
    lines.append(f"      Q3.Proofs.penaltyForm {p}D {p}Q {p}TauD v")
    lines.append("")
    lines.append(f"/-- Remaining checked lower-bound target for `{block.block_id}` / R. -/")
    lines.append(f"def {p}RLowerBound : Prop :=")
    lines.append("  ∀ v : CoeffIndex23 -> Real,")
    lines.append(f"    {p}RFloor * Q3.Proofs.euclideanEnergy v <=")
    lines.append(f"      Q3.Proofs.penaltyForm {p}R {p}Q {p}TauR v")
    lines.append("")
    lines.append(f"/-- Convert an exact weighted-square identity into `{p}DLowerBound`.")
    lines.append("")
    lines.append("The proof-generating SOS/LDL checker only needs to supply nonnegative")
    lines.append("weights and the exact identity; the reusable algebraic receiver proves")
    lines.append("the Euclidean lower bound. -/")
    lines.append(f"def {p}DLowerBound_of_weightedSquareSum")
    lines.append("    {σ : Type} [Fintype σ]")
    lines.append("    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)")
    lines.append("    (hw : ∀ s, 0 <= w s)")
    lines.append("    (hidentity : ∀ v : CoeffIndex23 -> Real,")
    lines.append(f"      Q3.Proofs.penaltyForm {p}D {p}Q {p}TauD v =")
    lines.append(f"        {p}DFloor * Q3.Proofs.euclideanEnergy v +")
    lines.append("          Q3.Proofs.weightedSquareSum w L v) :")
    lines.append(f"    {p}DLowerBound :=")
    lines.append("  Q3.Proofs.penalty_lower_bound_of_weightedSquareSum_identity")
    lines.append(f"    {p}D {p}Q {p}TauD {p}DFloor w L hw hidentity")
    lines.append("")
    lines.append(f"/-- Convert an exact weighted-Gram matrix identity into `{p}DLowerBound`.")
    lines.append("")
    lines.append("This is the preferred landing surface for generated 23-by-23 LDL/SOS")
    lines.append("certificates, because it checks matrix entries instead of expanding one")
    lines.append("large coefficient polynomial. -/")
    lines.append(f"def {p}DLowerBound_of_weightedSquareMatrix")
    lines.append("    {σ : Type} [Fintype σ]")
    lines.append("    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)")
    lines.append("    (hw : ∀ s, 0 <= w s)")
    lines.append("    (hidentity : ∀ i j : CoeffIndex23,")
    lines.append(f"      {p}D i j + {p}TauD * (∑ r : BoundaryIndex2, {p}Q r i * {p}Q r j) =")
    lines.append(f"        {p}DFloor * (if i = j then (1 : Real) else 0) +")
    lines.append("          Q3.Proofs.weightedSquareMatrix w L i j) :")
    lines.append(f"    {p}DLowerBound :=")
    lines.append("  Q3.Proofs.penalty_lower_bound_of_weightedSquareMatrix_identity")
    lines.append(f"    {p}D {p}Q {p}TauD {p}DFloor w L hw hidentity")
    lines.append("")
    lines.append(f"/-- Convert an exact weighted-square identity into `{p}RLowerBound`.")
    lines.append("")
    lines.append("The proof-generating SOS/LDL checker only needs to supply nonnegative")
    lines.append("weights and the exact identity; the reusable algebraic receiver proves")
    lines.append("the Euclidean lower bound. -/")
    lines.append(f"def {p}RLowerBound_of_weightedSquareSum")
    lines.append("    {σ : Type} [Fintype σ]")
    lines.append("    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)")
    lines.append("    (hw : ∀ s, 0 <= w s)")
    lines.append("    (hidentity : ∀ v : CoeffIndex23 -> Real,")
    lines.append(f"      Q3.Proofs.penaltyForm {p}R {p}Q {p}TauR v =")
    lines.append(f"        {p}RFloor * Q3.Proofs.euclideanEnergy v +")
    lines.append("          Q3.Proofs.weightedSquareSum w L v) :")
    lines.append(f"    {p}RLowerBound :=")
    lines.append("  Q3.Proofs.penalty_lower_bound_of_weightedSquareSum_identity")
    lines.append(f"    {p}R {p}Q {p}TauR {p}RFloor w L hw hidentity")
    lines.append("")
    lines.append(f"/-- Convert an exact weighted-Gram matrix identity into `{p}RLowerBound`.")
    lines.append("")
    lines.append("This is the preferred landing surface for generated 23-by-23 LDL/SOS")
    lines.append("certificates, because it checks matrix entries instead of expanding one")
    lines.append("large coefficient polynomial. -/")
    lines.append(f"def {p}RLowerBound_of_weightedSquareMatrix")
    lines.append("    {σ : Type} [Fintype σ]")
    lines.append("    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)")
    lines.append("    (hw : ∀ s, 0 <= w s)")
    lines.append("    (hidentity : ∀ i j : CoeffIndex23,")
    lines.append(f"      {p}R i j + {p}TauR * (∑ r : BoundaryIndex2, {p}Q r i * {p}Q r j) =")
    lines.append(f"        {p}RFloor * (if i = j then (1 : Real) else 0) +")
    lines.append("          Q3.Proofs.weightedSquareMatrix w L i j) :")
    lines.append(f"    {p}RLowerBound :=")
    lines.append("  Q3.Proofs.penalty_lower_bound_of_weightedSquareMatrix_identity")
    lines.append(f"    {p}R {p}Q {p}TauR {p}RFloor w L hw hidentity")
    lines.append("")
    lines.append(f"/-- Package the two checked lower bounds for `{block.block_id}`. -/")
    lines.append(f"def {p}PenaltyLowerBoundCert_of_bounds")
    lines.append(f"    (hD : {p}DLowerBound)")
    lines.append(f"    (hR : {p}RLowerBound) :")
    lines.append(f"    Q3.Proofs.FinitePenaltyLowerBoundCert {p}D {p}R {p}Q where")
    lines.append(f"  tauD := {p}TauD")
    lines.append(f"  tauR := {p}TauR")
    lines.append(f"  dFloor := {p}DFloor")
    lines.append(f"  rFloor := {p}RFloor")
    lines.append(f"  dFloor_pos := {p}DFloor_pos")
    lines.append(f"  rFloor_pos := {p}RFloor_pos")
    lines.append("  D_penalty_lower := hD")
    lines.append("  R_penalty_lower := hR")
    lines.append("")
    lines.append(f"/-- Convert the checked lower bounds for `{block.block_id}` into the")
    lines.append("existing finite penalty certificate receiver. -/")
    lines.append(f"def {p}FinitePenaltyCert_of_bounds")
    lines.append(f"    (hD : {p}DLowerBound)")
    lines.append(f"    (hR : {p}RLowerBound) :")
    lines.append(f"    Q3.Proofs.FinitePenaltyCert {p}D {p}R {p}Q :=")
    lines.append("  Q3.Proofs.FinitePenaltyLowerBoundCert.toFinitePenaltyCert")
    lines.append(f"    ({p}PenaltyLowerBoundCert_of_bounds hD hR)")
    lines.append("")
    return "\n".join(lines)


def generate(repo_dir: Path, manifest_path: Path) -> str:
    blocks = load_blocks(repo_dir, manifest_path)
    body = "\n".join(emit_block(block) for block in blocks)
    return GENERATED_HEADER + body + GENERATED_FOOTER


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--manifest",
        default="docs/insights/q3_psdpd_certificate_family_manifest.csv",
        help="Active Step 32F certificate family manifest.",
    )
    parser.add_argument(
        "--output",
        default="Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean",
        help="Lean output path.",
    )
    args = parser.parse_args()

    repo_dir = Path.cwd().resolve()
    manifest = repo_path(repo_dir, args.manifest)
    output = output_path(repo_dir, args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(generate(repo_dir, manifest))
    print(f"wrote {output}")


if __name__ == "__main__":
    main()
