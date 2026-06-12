#!/usr/bin/env python3
"""
Generate the Step33 signed-Q3.a_star A payload Lean import.

This is intentionally a parallel signed-A data surface.  It does not mutate the
legacy Step22 A payload, ARadius, radius-floor, or LDL files.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal
from pathlib import Path


FAMILY_PREFIX = {
    "primary": "primaryK11",
    "control": "controlK9",
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


def decimal_to_rat_literal(value: Decimal) -> str:
    value = +value
    if value == 0:
        return "((0 : Rat))"
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
    if den == 1:
        return f"(({num} : Rat))"
    return f"(({num} : Rat) / {den})"


def family_block(data: dict, family: str) -> dict:
    for block in data["families"]:
        if block["family"] == family:
            return block
    raise ValueError(f"family not found: {family}")


def emit_distance_table(lines: list[str], name: str, values: list[Decimal]) -> None:
    lines.append(f"def {name} : Nat -> Rat")
    for idx, value in enumerate(values):
        lines.append(f"  | {idx} => {decimal_to_rat_literal(value)}")
    lines.append("  | _ => 0")
    lines.append("")


def emit_family(lines: list[str], block: dict) -> None:
    family = block["family"]
    prefix = FAMILY_PREFIX[family]
    rows = sorted(block["rows"], key=lambda row: int(row["index"]))
    mids = [-Decimal(row["lean_astar_full_even_mid"]) for row in rows]
    radii = [Decimal(row["lean_astar_positive_rad"]) * Decimal(2) for row in rows]

    emit_distance_table(lines, f"{prefix}SignedQ3AStarAAbsDistanceEntryRat", mids)
    emit_distance_table(lines, f"{prefix}SignedQ3AStarARadiusAbsDistanceEntryRat", radii)

    lines.extend(
        [
            f"def {prefix}SignedQ3AStarAEntryRat (i j : Nat) : Rat :=",
            f"  {prefix}SignedQ3AStarAAbsDistanceEntryRat (natAbsDiff i j)",
            "",
            f"def {prefix}SignedQ3AStarARadiusEntryRat (i j : Nat) : Rat :=",
            f"  {prefix}SignedQ3AStarARadiusAbsDistanceEntryRat (natAbsDiff i j)",
            "",
            f"def {prefix}SignedQ3AStarARat : Matrix CoeffIndex23 CoeffIndex23 Rat :=",
            f"  fun i j => {prefix}SignedQ3AStarAEntryRat i.val j.val",
            "",
            f"def {prefix}SignedQ3AStarA : Matrix CoeffIndex23 CoeffIndex23 Real :=",
            f"  fun i j => ({prefix}SignedQ3AStarARat i j : Real)",
            "",
            f"def {prefix}SignedQ3AStarARadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=",
            f"  fun i j => {prefix}SignedQ3AStarARadiusEntryRat i.val j.val",
            "",
            f"def {prefix}SignedQ3AStarARadius : Matrix CoeffIndex23 CoeffIndex23 Real :=",
            f"  fun i j => ({prefix}SignedQ3AStarARadiusRat i j : Real)",
            "",
            f"def {prefix}SignedQ3AStarR : Matrix CoeffIndex23 CoeffIndex23 Real :=",
            f"  matrixRkappa {prefix}SignedQ3AStarA {prefix}P0 {prefix}Kappa",
            "",
            f"def {prefix}SignedQ3AStarD : Matrix CoeffIndex23 CoeffIndex23 Real :=",
            f"  matrixDtheta {prefix}SignedQ3AStarA {prefix}P {prefix}P0",
            f"    {prefix}Kappa {prefix}Theta",
            "",
            f"def {prefix}SignedQ3AStarRBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=",
            f"  fun i j =>",
            f"    {prefix}SignedQ3AStarARadiusRat i j +",
            f"      |{prefix}KappaRat| * {prefix}P0RadiusRat i j",
            "",
            f"def {prefix}SignedQ3AStarRBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=",
            f"  fun i j => ({prefix}SignedQ3AStarRBaseRadiusRat i j : Real)",
            "",
            f"def {prefix}SignedQ3AStarDBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=",
            f"  fun i j =>",
            f"    (1 - {prefix}ThetaRat) * {prefix}SignedQ3AStarARadiusRat i j +",
            f"      {prefix}PRadiusRat i j +",
            f"        {prefix}ThetaRat * |{prefix}KappaRat| * {prefix}P0RadiusRat i j",
            "",
            f"def {prefix}SignedQ3AStarDBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=",
            f"  fun i j => ({prefix}SignedQ3AStarDBaseRadiusRat i j : Real)",
            "",
        ]
    )


def render(data: dict) -> str:
    lines: list[str] = [
        "import Q3.Proofs.PSD_CenteredCoeffBaseHboxImport",
        "",
        "set_option linter.mathlibStandardSet false",
        "set_option maxHeartbeats 0",
        "",
        "noncomputable section",
        "",
        "namespace Q3",
        "namespace PSDpd",
        "namespace CenteredCoeffSignedQ3AStarPayloadImport",
        "",
        "open CenteredCoeffPayloadImport",
        "open CenteredCoeffBaseHboxImport",
        "",
        "/-!",
        "Signed-Q3.a_star A midpoint payload for Step33 route B.",
        "",
        "The legacy Step22 A table is intentionally left untouched.  These",
        "midpoints are the negative full-even `Q3.a_star` candidate rows from",
        "`a_source_convention_audit.json`; radii are doubled positive-window",
        "integration radii from the same audit.",
        "-/",
        "",
    ]
    for family in ("primary", "control"):
        emit_family(lines, family_block(data, family))
    lines.extend(
        [
            "end CenteredCoeffSignedQ3AStarPayloadImport",
            "end PSDpd",
            "end Q3",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    root = repo_root_from_cwd()
    parser.add_argument(
        "--audit",
        type=Path,
        default=root
        / "q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_source_convention_audit.json",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=root
        / "q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffSignedQ3AStarPayloadImport.lean",
    )
    args = parser.parse_args()
    with args.audit.open(encoding="utf-8") as handle:
        data = json.load(handle)
    args.out.write_text(render(data), encoding="utf-8")
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
