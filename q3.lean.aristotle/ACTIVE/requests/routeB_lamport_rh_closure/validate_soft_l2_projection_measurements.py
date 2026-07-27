#!/usr/bin/env python3
"""Fail-closed checks for SOFT_L2 edge and lag measurement artifacts."""

from __future__ import annotations

import csv
import json
from decimal import Decimal
from pathlib import Path


HERE = Path(__file__).resolve().parent


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    edge = json.loads((HERE / "SOFT_L2_EDGE_MASS_PROFILE.json").read_text())
    lag = json.loads((HERE / "SOFT_L2_LAG_LEDGER_13_120.json").read_text())
    report = (HERE / "SOFT_L2_PROJECTION_MEASUREMENTS_REPORT_2026-07-13.md").read_text()

    require(len(edge["summaries"]) == 7, "SOFT_L2_EDGE_CELL_MISSING")
    require(
        edge["prediction"]["high_precision_strictly_increasing_exponent"],
        "SOFT_L2_EDGE_HIGH_PRECISION_EXPONENT_NOT_INCREASING",
    )
    require(
        len(edge["prediction"]["float64_floor_limited_cells"]) == 2,
        "SOFT_L2_EDGE_FLOAT64_FLOOR_NOT_REGISTERED",
    )
    require(not edge["claims"]["UREL_proved"], "SOFT_L2_UREL_SMUGGLED")
    require(not edge["claims"]["smallness_proved"], "SOFT_L2_EDGE_SMALLNESS_SMUGGLED")
    require(not edge["claims"]["RH"], "SOFT_L2_EDGE_RH_SMUGGLED")

    with (HERE / "SOFT_L2_EDGE_MASS_PROFILE.csv").open() as f:
        edge_rows = list(csv.DictReader(f))
    require(len(edge_rows) == 7 * 52, "SOFT_L2_EDGE_ALL_DEPTH_ROWS_MISSING")
    require((HERE / "SOFT_L2_EDGE_MASS_PROFILE_LOG.png").stat().st_size > 10000, "SOFT_L2_EDGE_PLOT_MISSING")

    rows = lag["rows"]
    require(len(rows) == 13, "SOFT_L2_LAG_GRID_INCOMPLETE")
    require(lag["cell"] == {"lambda_sq": 13, "N": 120, "L": lag["cell"]["L"], "mu": lag["cell"]["mu"]}, "SOFT_L2_LAG_CELL_WRONG")
    zero = next(r for r in rows if r["t_over_L"] == 0.0)
    require(Decimal(zero["window_D_sum"]["re"]) == 0, "SOFT_L2_WINDOW_T0_NONZERO")
    require(lag["t0_matrix_anchor"]["exact_residual"] == "0", "SOFT_L2_T0_ANCHOR_MISSING")

    left = rows[0]
    right = rows[-1]
    require(
        abs(Decimal(left["abs_remainder"]) - Decimal(right["abs_remainder"])) < Decimal("1e-30"),
        "SOFT_L2_LAG_PARITY_MISMATCH",
    )
    require(Decimal(right["abs_remainder"]) > Decimal("1"), "SOFT_L2_AGGREGATE_REMAINDER_SMALL_AT_EDGE")
    require(
        lag["prediction"]["outcome"] == "SUPPORTED_FOR_AGGREGATE_REMAINDER_ON_GRID",
        "SOFT_L2_AGGREGATE_PREDICTION_NOT_RECORDED",
    )
    require("not pure Galerkin" in lag["remainder_scope"], "SOFT_L2_PURE_GALERKIN_OVERCLAIM")
    require(not lag["claims"]["smallness"], "SOFT_L2_LAG_SMALLNESS_SMUGGLED")
    require(not lag["claims"]["compact_support_proved"], "SOFT_L2_SUPPORT_INFERRED_FROM_GRID")
    require(not lag["claims"]["RH"], "SOFT_L2_LAG_RH_SMUGGLED")

    for token in (
        "window `E_win` from `D_(a,L)`",
        "aggregate remainder",
        "Bus 010 was not",
        "NOT_RH",
    ):
        require(token in report, f"SOFT_L2_MEASUREMENT_REPORT_TOKEN_MISSING:{token}")

    print("SOFT_L2_MEASUREMENTS_COMPLETE")
    print("SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED")
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
