#!/usr/bin/env python3
"""Float64 D0 unprojected central-mass and norm ladder."""

from __future__ import annotations

import csv
import json
import math
import platform
import sys
from pathlib import Path
from typing import Any

import numpy as np

import strip_growth_probe as strip


REQUEST_DIR = Path(__file__).resolve().parent
RESULT_JSON = REQUEST_DIR / "UNPROJECTED_MASS_NORM_PROBE.json"
RESULT_CSV = REQUEST_DIR / "UNPROJECTED_MASS_NORM_PROBE.csv"
RESULT_MD = REQUEST_DIR / "UNPROJECTED_MASS_NORM_PROBE.md"

M_MIN = 13
M_MAX = 257
N_BOUND = 120
QUAD_ORDER = 128


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, np.ndarray):
        return json_safe(value.tolist())
    if isinstance(value, np.generic):
        return json_safe(value.item())
    return value


def cell(m: int) -> dict[str, Any]:
    degree = strip.model_degree(m)
    h_grid, h_values, metadata = strip.h_trial_grid(m, degree)
    lam = math.sqrt(m)
    length = math.log(m)
    nodes, weights = np.polynomial.legendre.leggauss(QUAD_ORDER)
    frequencies = np.arange(-N_BOUND, N_BOUND + 1, dtype=np.float64)
    coefficients = np.zeros(2 * N_BOUND + 1, dtype=np.complex128)
    unprojected_norm_sq = 0.0

    for j in range(m, 1, -1):
        left = math.log(m / j)
        right = math.log(m / (j - 1))
        half = (right - left) / 2
        x = (left + right) / 2 + half * nodes
        quadrature_weights = half * weights
        exp_x = np.exp(x)
        multiplicity = j - 1
        arguments = (
            np.arange(1, multiplicity + 1, dtype=np.float64)[:, None]
            * exp_x[None, :]
            / m
        )
        starred_sum = np.interp(
            arguments.ravel(), h_grid, h_values
        ).reshape(multiplicity, QUAD_ORDER).sum(axis=0)
        g_values = np.sqrt(exp_x / lam) * starred_sum
        unprojected_norm_sq += float(
            np.dot(quadrature_weights, np.abs(g_values) ** 2)
        )
        phases = np.exp(
            -2j * math.pi * np.outer(x, frequencies) / length
        )
        with np.errstate(all="ignore"):
            block = (
                (quadrature_weights * g_values)
                @ phases
                / math.sqrt(length)
            )
        if not np.all(np.isfinite(block)):
            raise RuntimeError(f"NONFINITE_MASS_NORM_BLOCK:{m}:{j}")
        coefficients += block

    projected_norm = float(np.linalg.norm(coefficients))
    unprojected_norm = math.sqrt(unprojected_norm_sq)
    central_overlap = complex(coefficients[N_BOUND])
    central_mass = math.sqrt(length) * central_overlap
    anchor_control = abs(central_mass) / projected_norm
    return {
        "m": m,
        "N": N_BOUND,
        "M_real": central_mass.real,
        "M_imag": central_mass.imag,
        "abs_M": abs(central_mass),
        "gTrial_norm": unprojected_norm,
        "PgTrial_norm": projected_norm,
        "abs_M_over_PgTrial_norm": anchor_control,
        "projection_contraction_ratio": projected_norm / unprojected_norm,
        "model_degree": degree,
        "last_ten_legendre_mass": float(
            metadata["last_ten_legendre_mass"]
        ),
    }


def fit(rows: list[dict[str, Any]], key: str) -> dict[str, Any]:
    x = np.log(np.array([row["m"] for row in rows], dtype=np.float64))
    y = np.log(np.array([row[key] for row in rows], dtype=np.float64))
    design = np.column_stack([np.ones(x.size), x])
    intercept, beta = np.linalg.lstsq(design, y, rcond=None)[0]
    fitted = design @ np.array([intercept, beta])
    residual = y - fitted
    sse = float(residual @ residual)
    centered = y - y.mean()
    sst = float(centered @ centered)
    sigma2 = sse / (x.size - 2)
    beta_stderr = math.sqrt(
        sigma2 / float(((x - x.mean()) ** 2).sum())
    )
    return {
        "model": f"log({key}) = intercept + beta*log(m)",
        "intercept": float(intercept),
        "prefactor": math.exp(float(intercept)),
        "beta": float(beta),
        "beta_standard_error": beta_stderr,
        "r_squared": 1 - sse / sst if sst else 1.0,
        "min": min(float(row[key]) for row in rows),
        "max": max(float(row[key]) for row in rows),
        "endpoint_ratio_257_over_13":
            float(rows[-1][key] / rows[0][key]),
    }


def run() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for m in range(M_MIN, M_MAX + 1):
        row = cell(m)
        rows.append(row)
        if m == M_MIN or m == M_MAX or (m - M_MIN + 1) % 8 == 0:
            print(
                f"[{m - M_MIN + 1:3d}/{M_MAX - M_MIN + 1}] "
                f"m={m} M={row['M_real']:.12g} "
                f"norm={row['gTrial_norm']:.12g}",
                flush=True,
            )
    return {
        "schema": "UNPROJECTED_MASS_NORM_PROBE_V1",
        "numeric_type": "float64/complex128",
        "parameters": {
            "m_min": M_MIN,
            "m_max": M_MAX,
            "N": N_BOUND,
            "quadrature_order": QUAD_ORDER,
        },
        "rows": rows,
        "fits": {
            key: fit(rows, key)
            for key in (
                "abs_M",
                "gTrial_norm",
                "abs_M_over_PgTrial_norm",
            )
        },
        "checks": {
            "all_M_real_negative":
                all(row["M_real"] < 0 for row in rows),
            "max_abs_M_imag":
                max(abs(row["M_imag"]) for row in rows),
            "max_projection_contraction_ratio":
                max(row["projection_contraction_ratio"] for row in rows),
        },
        "runtime": {
            "python": sys.version.split()[0],
            "numpy": np.__version__,
            "platform": platform.platform(),
        },
    }


def write_csv(result: dict[str, Any]) -> None:
    fields = [
        "m",
        "N",
        "M_real",
        "M_imag",
        "abs_M",
        "gTrial_norm",
        "PgTrial_norm",
        "abs_M_over_PgTrial_norm",
        "projection_contraction_ratio",
        "model_degree",
        "last_ten_legendre_mass",
    ]
    with RESULT_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(result["rows"])


def write_markdown(result: dict[str, Any]) -> None:
    lines = [
        "# UNPROJECTED_MASS_NORM_PROBE",
        "",
        "Float64/complex128; every integer `m=13,...,257`; `N=120`.",
        "",
        "| m | Re M_m | |M_m| | ||gTrial_m|| | ||P gTrial_m|| | "
        "|M_m|/||P gTrial_m|| |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in result["rows"]:
        lines.append(
            f"| {row['m']} | {row['M_real']:.12g} | "
            f"{row['abs_M']:.12g} | {row['gTrial_norm']:.12g} | "
            f"{row['PgTrial_norm']:.12g} | "
            f"{row['abs_M_over_PgTrial_norm']:.12g} |"
        )
    lines.extend(
        [
            "",
            "## Power fits",
            "",
            "`log y = intercept + beta log m`",
            "",
            "| y | beta | SE(beta) | R^2 | y(257)/y(13) | min | max |",
            "|---|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for key in ("abs_M", "gTrial_norm", "abs_M_over_PgTrial_norm"):
        item = result["fits"][key]
        lines.append(
            f"| {key} | {item['beta']:.12g} | "
            f"{item['beta_standard_error']:.12g} | "
            f"{item['r_squared']:.12g} | "
            f"{item['endpoint_ratio_257_over_13']:.12g} | "
            f"{item['min']:.12g} | {item['max']:.12g} |"
        )
    checks = result["checks"]
    lines.extend(
        [
            "",
            "## Checks",
            "",
            "| check | value |",
            "|---|---:|",
            f"| all Re M_m < 0 | {checks['all_M_real_negative']} |",
            f"| max |Im M_m| | {checks['max_abs_M_imag']:.12g} |",
            "| max ||P gTrial_m|| / ||gTrial_m|| | "
            f"{checks['max_projection_contraction_ratio']:.12g} |",
            "",
        ]
    )
    RESULT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    result = run()
    RESULT_JSON.write_text(
        json.dumps(json_safe(result), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv(result)
    write_markdown(result)
    print(f"WROTE {RESULT_JSON}")
    print(f"WROTE {RESULT_CSV}")
    print(f"WROTE {RESULT_MD}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
