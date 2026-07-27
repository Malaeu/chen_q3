#!/usr/bin/env python3
"""Float64 B0 probe for the SOFT-1 bare kTrial transform.

This is diagnostic only.  It does not mutate Route-B state, select N(m),
create Bus 010, or promote a fitted exponent to a theorem.
"""

from __future__ import annotations

import csv
import json
import math
from pathlib import Path

import numpy as np

import off_axis_growth_probe as base


REQUEST_DIR = Path(__file__).resolve().parent
RESULT_JSON = REQUEST_DIR / "B0_VALUE_PROBE.json"
RESULT_CSV = REQUEST_DIR / "B0_VALUE_PROBE.csv"
RESULT_MD = REQUEST_DIR / "B0_VALUE_PROBE.md"
OFF_AXIS_JSON = REQUEST_DIR / "OFF_AXIS_GROWTH_PROBE.json"

EXISTING_CELLS = ((13, 90), (13, 120), (14, 120), (53, 120), (101, 120))
NEW_CELLS = ((149, 120), (197, 120), (257, 120))
MODEL_DEGREES = {149: 1536, 197: 2048, 257: 2560}
MODEL_COMPARE_DEGREES = {149: 1400, 197: 1850, 257: 2350}
QUAD_LOW = 64
QUAD_HIGH = 128
DELTA_DIAGNOSTIC = 0.85


def b0_from_c0(m: int, c0: complex) -> float:
    return math.sqrt(math.log(m)) * abs(c0)


def load_existing() -> list[dict[str, object]]:
    payload = json.loads(OFF_AXIS_JSON.read_text(encoding="utf-8"))
    by_cell = {
        (int(row["lambda_sq"]), int(row["N"])): row for row in payload["cells"]
    }
    rows: list[dict[str, object]] = []
    for m, n_bound in EXISTING_CELLS:
        source = by_cell[(m, n_bound)]
        c0_data = source["c0_float64"]
        c0 = complex(float(c0_data["re"]), float(c0_data["im"]))
        rows.append(
            {
                "m": m,
                "N": n_bound,
                "L_m": math.log(m),
                "abs_c0": abs(c0),
                "abs_B0": b0_from_c0(m, c0),
                "source": source["source"],
                "convergence": source["source"].get("convergence"),
                "fresh": False,
            }
        )
    return rows


def compute_new(m: int, n_bound: int) -> dict[str, object]:
    degree = MODEL_DEGREES[m]
    compare_degree = MODEL_COMPARE_DEGREES[m]
    print(f"[B0] m={m} N={n_bound}: degree={degree}, q={QUAD_HIGH}", flush=True)
    coeff_high, meta_high = base.integrate_g04_coefficients(
        m, n_bound, degree, QUAD_HIGH
    )
    print(f"[B0] m={m} N={n_bound}: q={QUAD_LOW}", flush=True)
    coeff_q_low, _ = base.integrate_g04_coefficients(
        m, n_bound, degree, QUAD_LOW
    )
    print(
        f"[B0] m={m} N={n_bound}: compare_degree={compare_degree}",
        flush=True,
    )
    coeff_degree_low, _ = base.integrate_g04_coefficients(
        m, n_bound, compare_degree, QUAD_HIGH
    )
    c0 = complex(coeff_high[n_bound])
    b0 = b0_from_c0(m, c0)
    return {
        "m": m,
        "N": n_bound,
        "L_m": math.log(m),
        "abs_c0": abs(c0),
        "abs_B0": b0,
        "source": {
            "kind": "fresh_float64_breakpoint_constructor",
            "max_degree": degree,
            "compare_degree": compare_degree,
            "quad_high": QUAD_HIGH,
            "quad_low": QUAD_LOW,
        },
        "convergence": {
            "abs_B0_q64_minus_q128": abs(
                b0_from_c0(m, complex(coeff_q_low[n_bound])) - b0
            ),
            "abs_B0_compare_degree_minus_final": abs(
                b0_from_c0(m, complex(coeff_degree_low[n_bound])) - b0
            ),
            "max_abs_coeff_q64_minus_q128": float(
                np.max(np.abs(coeff_q_low - coeff_high))
            ),
            "max_abs_coeff_compare_degree_minus_final": float(
                np.max(np.abs(coeff_degree_low - coeff_high))
            ),
            "last_ten_legendre_mass": float(meta_high["last_ten_legendre_mass"]),
        },
        "fresh": True,
    }


def fit_rows(rows: list[dict[str, object]]) -> dict[str, object]:
    fit_rows_ = [row for row in rows if int(row["N"]) == 120]
    x = np.log(np.array([float(row["m"]) for row in fit_rows_], dtype=np.float64))
    y = np.log(
        np.array([float(row["abs_B0"]) for row in fit_rows_], dtype=np.float64)
    )
    design = np.column_stack([np.ones(x.size), x])
    coeff, *_ = np.linalg.lstsq(design, y, rcond=None)
    fitted = design @ coeff
    residual = y - fitted
    ss_res = float(residual @ residual)
    ss_tot = float(((y - y.mean()) ** 2).sum())
    slope = float(coeff[1])
    return {
        "model": "log|B0| = intercept + beta*log(m)",
        "cells": [[int(row["m"]), int(row["N"])] for row in fit_rows_],
        "intercept": float(coeff[0]),
        "beta": slope,
        "alpha_if_decay": max(0.0, -slope),
        "r_squared": 1.0 - ss_res / ss_tot if ss_tot else 1.0,
        "min_abs_B0": min(float(row["abs_B0"]) for row in fit_rows_),
        "max_abs_B0": max(float(row["abs_B0"]) for row in fit_rows_),
        "delta_diagnostic": DELTA_DIAGNOSTIC,
        "sampled_floor_pass": all(
            float(row["abs_B0"]) > DELTA_DIAGNOSTIC for row in fit_rows_
        ),
    }


def write_outputs(rows: list[dict[str, object]], fit: dict[str, object]) -> None:
    verdict = (
        "SAMPLED_INF_GT_DELTA_NO_COMPENSATION_DIAGNOSTIC"
        if fit["sampled_floor_pass"] and float(fit["beta"]) >= -0.02
        else "B0_DECAY_COMPENSATION_REQUIRED"
    )
    payload = {
        "schema": "route_b_b0_value_probe.v1",
        "arithmetic": "IEEE754_BINARY64_ONLY",
        "object": "B_(m,N)(0)=sqrt(log(m))*c0(kTrial_(m,N))",
        "rows": rows,
        "fit": fit,
        "verdict": verdict,
        "status": "DIAGNOSTIC_ONLY_FIT_NOT_LAW",
        "explicit_nonclaims": [
            "NO_UNIFORM_LOWER_BOUND_THEOREM",
            "NO_N_OF_M_SELECTOR",
            "NO_S1_CLOSURE",
            "NO_BUS_010",
            "NO_RH",
        ],
    }
    RESULT_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with RESULT_CSV.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["m", "N", "L_m", "abs_c0", "abs_B0", "fresh"])
        for row in rows:
            writer.writerow(
                [
                    row["m"],
                    row["N"],
                    f"{float(row['L_m']):.17g}",
                    f"{float(row['abs_c0']):.17g}",
                    f"{float(row['abs_B0']):.17g}",
                    str(bool(row["fresh"])).lower(),
                ]
            )

    table = [
        "| m | N | |c0| | |B(0)| | source |",
        "|---:|---:|---:|---:|---|",
    ]
    for row in rows:
        table.append(
            f"| {row['m']} | {row['N']} | "
            f"`{float(row['abs_c0']):.12g}` | "
            f"`{float(row['abs_B0']):.12g}` | "
            f"{'fresh' if row['fresh'] else 'persisted'} |"
        )
    report = f"""# B0_VALUE_PROBE

Status: `DIAGNOSTIC_ONLY / FIT_NOT_LAW / NOT_RH`.
Verdict: `{verdict}`.

{chr(10).join(table)}

Fit:

```text
|B_(m,120)(0)| ~= exp({float(fit['intercept']):.12g}) * m^({float(fit['beta']):.12g})
alpha_if_decay = {float(fit['alpha_if_decay']):.12g}
R^2 = {float(fit['r_squared']):.12g}
sampled min = {float(fit['min_abs_B0']):.12g}
sampled max = {float(fit['max_abs_B0']):.12g}
delta_diagnostic = {DELTA_DIAGNOSTIC}
```

The finite sample supports an uncompensated S1 statement.  It is not a proof
of a uniform positive lower bound; the theorem-facing obligation remains an
explicit lower-bound input.
"""
    RESULT_MD.write_text(report, encoding="utf-8")


def main() -> int:
    rows = load_existing()
    for cell in NEW_CELLS:
        rows.append(compute_new(*cell))
    rows.sort(key=lambda row: (int(row["m"]), int(row["N"])))
    fit = fit_rows(rows)
    write_outputs(rows, fit)
    print(json.dumps({"fit": fit, "result": str(RESULT_JSON)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
