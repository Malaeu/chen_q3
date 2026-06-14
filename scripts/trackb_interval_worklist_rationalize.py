#!/usr/bin/env python3
"""
Track B / E5p dyadic rational guard verifier for interval worklists.

This consumes the compact rows emitted by:

  trackb_nonnode_interval_atom_audit.py --mesh-index all

and rounds the recorded floating interval endpoints outward to dyadic
rationals.  It then verifies the mesh sign guards by exact Fraction
arithmetic.

This is not a proof of the source interval enclosures.  It only proves that
once those intervals are accepted as input boxes, the finite guard arithmetic
can be represented as exact rational certificate data.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
from typing import Any


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def dyadic_floor_float(x: float, bits: int) -> Fraction:
    scale = 1 << int(bits)
    return Fraction(floor_fraction(Fraction.from_float(float(x)) * scale), scale)


def dyadic_ceil_float(x: float, bits: int) -> Fraction:
    scale = 1 << int(bits)
    return Fraction(ceil_fraction(Fraction.from_float(float(x)) * scale), scale)


def interval_to_dyadic(row: dict[str, Any], bits: int) -> tuple[Fraction, Fraction]:
    lo = dyadic_floor_float(float(row["lo"]), bits)
    hi = dyadic_ceil_float(float(row["hi"]), bits)
    if lo > hi:
        raise ValueError(f"bad dyadic interval: {row}")
    return lo, hi


def abs_lower_of_interval(x: tuple[Fraction, Fraction]) -> Fraction:
    lo, hi = x
    if lo <= 0 <= hi:
        return Fraction(0, 1)
    return min(abs(lo), abs(hi))


def abs_upper_of_interval(x: tuple[Fraction, Fraction]) -> Fraction:
    lo, hi = x
    return max(abs(lo), abs(hi))


def rational_to_record(x: Fraction, *, decimal_digits: int = 24) -> dict[str, Any]:
    return {
        "num": str(x.numerator),
        "den": str(x.denominator),
        "decimal": format(float(x), f".{decimal_digits}g"),
    }


def interval_to_record(x: tuple[Fraction, Fraction]) -> dict[str, Any]:
    return {
        "lo": rational_to_record(x[0]),
        "hi": rational_to_record(x[1]),
    }


def guard_row(row: dict[str, Any], *, bits: int) -> dict[str, Any]:
    s0 = interval_to_dyadic(row["S0_interval"], bits)
    s1 = interval_to_dyadic(row["S1_interval"], bits)
    s2 = interval_to_dyadic(row["S2_interval"], bits)
    width = dyadic_ceil_float(float(row["mesh_width_directed_upper"]), bits)

    s0_abs_lower = abs_lower_of_interval(s0)
    s1_abs_upper = abs_upper_of_interval(s1)
    s2_abs_upper = abs_upper_of_interval(s2)
    direct_guard = s0_abs_lower - Fraction(1, 2) * s1_abs_upper * width
    curvature_guard = s0_abs_lower - Fraction(1, 2) * (
        s1_abs_upper + Fraction(1, 2) * s2_abs_upper * width
    ) * width

    return {
        "mesh_index": int(row["mesh_index"]),
        "mesh_interval": row["mesh_interval"],
        "S0_interval_dyadic": interval_to_record(s0),
        "S1_interval_dyadic": interval_to_record(s1),
        "S2_interval_dyadic": interval_to_record(s2),
        "mesh_width_upper_dyadic": rational_to_record(width),
        "S0_abs_lower": rational_to_record(s0_abs_lower),
        "S1_abs_upper": rational_to_record(s1_abs_upper),
        "S2_abs_upper": rational_to_record(s2_abs_upper),
        "direct_S1_mesh_guard_lower": rational_to_record(direct_guard),
        "curvature_S2_mesh_guard_lower": rational_to_record(curvature_guard),
        "direct_S1_guard_passes": bool(direct_guard > 0),
        "curvature_S2_guard_passes": bool(curvature_guard > 0),
        "_direct_guard_fraction": direct_guard,
        "_curvature_guard_fraction": curvature_guard,
        "_s0_abs_lower_fraction": s0_abs_lower,
        "_s1_abs_upper_fraction": s1_abs_upper,
        "_s2_abs_upper_fraction": s2_abs_upper,
    }


def strip_internal(row: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in row.items() if not key.startswith("_")}


def load_worklist(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    if not isinstance(data, list) or not data:
        raise ValueError("expected a nonempty JSON list")
    summary = data[0]
    if summary.get("mode") != "trackb_nonnode_interval_atom_full_cell_worklist":
        raise ValueError(f"unexpected mode: {summary.get('mode')}")
    rows = summary.get("worklist_rows")
    if not isinstance(rows, list) or not rows:
        raise ValueError("input summary must contain worklist_rows; rerun without --worklist-omit-rows")
    return summary


def run(args: argparse.Namespace) -> dict[str, Any]:
    summary = load_worklist(Path(args.input))
    bits = int(args.dyadic_bits)
    rational_rows = [guard_row(row, bits=bits) for row in summary["worklist_rows"]]
    direct_failures = [row for row in rational_rows if not row["direct_S1_guard_passes"]]
    curvature_failures = [row for row in rational_rows if not row["curvature_S2_guard_passes"]]
    worst_direct = sorted(rational_rows, key=lambda row: row["_direct_guard_fraction"])[
        : int(args.worst_limit)
    ]
    worst_curvature = sorted(rational_rows, key=lambda row: row["_curvature_guard_fraction"])[
        : int(args.worst_limit)
    ]

    result: dict[str, Any] = {
        "mode": "trackb_interval_worklist_dyadic_rational_guard",
        "status": "diagnostic_exact_guard_arithmetic_only",
        "source_mode": summary.get("mode"),
        "dyadic_bits": bits,
        "K": summary.get("K"),
        "ell": summary.get("ell"),
        "receiver_delta": summary.get("receiver_delta"),
        "ledger_cells": summary.get("ledger_cells"),
        "cert_na": summary.get("cert_na"),
        "cell": summary.get("cell"),
        "raw_edge": summary.get("raw_edge"),
        "cell_interval": summary.get("cell_interval"),
        "mesh_intervals_total": len(rational_rows),
        "direct_S1_guard_pass_count": len(rational_rows) - len(direct_failures),
        "curvature_S2_guard_pass_count": len(rational_rows) - len(curvature_failures),
        "direct_S1_guard_failure_count": len(direct_failures),
        "curvature_S2_guard_failure_count": len(curvature_failures),
        "min_direct_S1_mesh_guard_lower": rational_to_record(
            min(row["_direct_guard_fraction"] for row in rational_rows)
        ),
        "min_curvature_S2_mesh_guard_lower": rational_to_record(
            min(row["_curvature_guard_fraction"] for row in rational_rows)
        ),
        "min_S0_abs_lower": rational_to_record(
            min(row["_s0_abs_lower_fraction"] for row in rational_rows)
        ),
        "max_S1_abs_upper": rational_to_record(
            max(row["_s1_abs_upper_fraction"] for row in rational_rows)
        ),
        "max_S2_abs_upper": rational_to_record(
            max(row["_s2_abs_upper_fraction"] for row in rational_rows)
        ),
        "worst_direct_S1_rows": [strip_internal(row) for row in worst_direct],
        "worst_curvature_S2_rows": [strip_internal(row) for row in worst_curvature],
        "proof_status": (
            "diagnostic_only: exact dyadic rational guard arithmetic over "
            "floating interval boxes; source interval enclosure proofs and "
            "Lean theorem integration are still missing"
        ),
        "D2": (
            "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
            "w_Q(n)=2*Lambda(n)/sqrt(n)"
        ),
    }
    if args.emit_rows:
        result["rational_rows"] = [strip_internal(row) for row in rational_rows]
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, help="full-cell worklist JSON with worklist_rows")
    parser.add_argument("--dyadic-bits", type=int, default=96)
    parser.add_argument("--worst-limit", type=int, default=5)
    parser.add_argument("--emit-rows", action="store_true")
    return parser.parse_args()


def main() -> None:
    result = run(parse_args())
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
