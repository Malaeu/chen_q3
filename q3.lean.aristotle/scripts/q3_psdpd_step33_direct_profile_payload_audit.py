#!/usr/bin/env python3
"""Audit the direct Step33 finite-prime profile payload shape.

This script does not prove Lean theorems.  It checks whether the direct
Step20 Arb finite-prime profile evaluator reproduces the already imported
Step22 `P/PRadius` midpoint/radius payload closely enough for the compiled
direct-profile Lean receiver shape.

The required Lean payload is:

  |centeredBSplineFinitePrimeKernelProfile ... - profileMid i j|
    <= profileRad i j
  profileMid i j = imported P i j
  profileRad i j <= imported PRadius i j

This audit checks the numerical source side of that contract before a real
Lean replay generator is written.
"""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path
from typing import Any

from q3_psdpd_step19_entry_radii import decimal_grid_centers, set_precision
from q3_psdpd_step20_midpoint_contract import build_P_midrad_arb


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Block:
    name: str
    k_spline: int
    midpoint_csv: Path
    radius_csv: Path


BLOCKS = {
    "primary": Block(
        name="primary",
        k_spline=11,
        midpoint_csv=ROOT / "docs/insights/q3_psdpd_step22_midpoints_k11.csv",
        radius_csv=ROOT / "docs/insights/q3_psdpd_step22_radii_k11.csv",
    ),
    "control": Block(
        name="control",
        k_spline=9,
        midpoint_csv=ROOT / "docs/insights/q3_psdpd_step22_midpoints_k9.csv",
        radius_csv=ROOT / "docs/insights/q3_psdpd_step22_radii_k9.csv",
    ),
}


def load_p_payload(path: Path, column: str) -> dict[tuple[int, int], Decimal]:
    out: dict[tuple[int, int], Decimal] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["matrix"].strip() != "P":
                continue
            out[(int(row["i"]), int(row["j"]))] = Decimal(row[column])
    return out


def decimal_from_float_csv(x: float) -> Decimal:
    return Decimal(f"{float(x):.18e}")


def audit_block(block: Block, *, arb_prec: int) -> dict[str, Any]:
    set_precision(arb_prec)

    centers_dec = decimal_grid_centers("3.0", "0.30", "0.25")
    direct_mid, direct_rad = build_P_midrad_arb(
        centers_dec=centers_dec,
        L="3.0",
        ell="0.30",
        k_spline=block.k_spline,
    )

    imported_mid = load_p_payload(block.midpoint_csv, "mid")
    imported_rad = load_p_payload(block.radius_csv, "rad")

    failures = 0
    max_mid_drift = Decimal(0)
    max_required_radius = Decimal(0)
    min_slack: Decimal | None = None
    worst: dict[str, str | int] | None = None

    n = len(centers_dec)
    for i in range(n):
        for j in range(n):
            generated_mid = decimal_from_float_csv(float(direct_mid[i, j]))
            generated_rad = decimal_from_float_csv(float(direct_rad[i, j]))
            mid_drift = abs(generated_mid - imported_mid[(i, j)])
            required_radius = generated_rad + mid_drift
            slack = imported_rad[(i, j)] - required_radius

            if mid_drift > max_mid_drift:
                max_mid_drift = mid_drift
            if required_radius > max_required_radius:
                max_required_radius = required_radius
            if min_slack is None or slack < min_slack:
                min_slack = slack
                worst = {
                    "i": i,
                    "j": j,
                    "generated_mid": str(generated_mid),
                    "imported_mid": str(imported_mid[(i, j)]),
                    "generated_rad": str(generated_rad),
                    "required_radius": str(required_radius),
                    "imported_radius": str(imported_rad[(i, j)]),
                    "slack": str(slack),
                }
            if slack < 0:
                failures += 1

    return {
        "block": block.name,
        "k_spline": block.k_spline,
        "midpoint_csv": str(block.midpoint_csv),
        "radius_csv": str(block.radius_csv),
        "arb_prec": arb_prec,
        "entries": n * n,
        "failed_entries": failures,
        "max_mid_drift": str(max_mid_drift),
        "max_required_radius": str(max_required_radius),
        "min_slack": str(min_slack),
        "worst": worst,
        "verdict": "direct_profile_payload_fits_imported_radius"
        if failures == 0
        else "direct_profile_payload_exceeds_imported_radius",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--block",
        choices=["primary", "control", "both"],
        default="both",
    )
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--primary-midpoint-csv", type=Path)
    parser.add_argument("--primary-radius-csv", type=Path)
    parser.add_argument("--control-midpoint-csv", type=Path)
    parser.add_argument("--control-radius-csv", type=Path)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    names = ["primary", "control"] if args.block == "both" else [args.block]
    blocks: list[Block] = []
    for name in names:
        block = BLOCKS[name]
        if name == "primary":
            blocks.append(
                Block(
                    name=block.name,
                    k_spline=block.k_spline,
                    midpoint_csv=args.primary_midpoint_csv or block.midpoint_csv,
                    radius_csv=args.primary_radius_csv or block.radius_csv,
                )
            )
        else:
            blocks.append(
                Block(
                    name=block.name,
                    k_spline=block.k_spline,
                    midpoint_csv=args.control_midpoint_csv or block.midpoint_csv,
                    radius_csv=args.control_radius_csv or block.radius_csv,
                )
            )

    results = [audit_block(block, arb_prec=args.arb_prec) for block in blocks]

    for result in results:
        print(
            f"{result['block']}: {result['failed_entries']}/{result['entries']} "
            f"entries exceed imported P radius; verdict={result['verdict']}"
        )
        print(
            f"  max_mid_drift={result['max_mid_drift']} "
            f"max_required_radius={result['max_required_radius']}"
        )
        print(f"  min_slack={result['min_slack']} worst={result['worst']}")

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(results, indent=2) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
