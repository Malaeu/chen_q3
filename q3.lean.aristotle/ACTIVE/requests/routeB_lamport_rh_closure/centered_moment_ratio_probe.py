#!/usr/bin/env python3
"""Float64 measurements of D0 centeredMomentLeakage.

For each requested cell, compute

  R_(m,N)(sigma)
    = integral |q_(m,N)(t)| exp(sigma |t|) dt / |rawFplus_(m,N)(0)|

from the normalized post-Galerkin coefficient row.  This is a diagnostic
only: it does not mutate STATE or promote a fitted exponent to a theorem.
"""

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
RESULT_JSON = REQUEST_DIR / "CENTERED_MOMENT_RATIO_PROBE.json"
RESULT_CSV = REQUEST_DIR / "CENTERED_MOMENT_RATIO_PROBE.csv"
RESULT_MD = REQUEST_DIR / "CENTERED_MOMENT_RATIO_PROBE.md"

M_MIN = 13
M_MAX = 257
N_BOUND = 120
SIGMAS = (0.10, 0.25, 0.40, 0.45)
SENSITIVITY_M = 53
SENSITIVITY_N = (90, 150)
FFT_GRID = 32768
FFT_GRID_CHECK = 16384
QUAD_ORDER = 128


def sigma_key(sigma: float) -> str:
    return f"R_sigma_{sigma:.2f}".replace(".", "p")


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, np.ndarray):
        return json_safe(value.tolist())
    if isinstance(value, np.generic):
        return json_safe(value.item())
    if isinstance(value, complex):
        return {"re": float(value.real), "im": float(value.imag)}
    return value


def coefficients(
    m: int, n_bound: int, quad_order: int = QUAD_ORDER
) -> tuple[np.ndarray, dict[str, Any]]:
    """D0 gTrial projection using the registered STRIP_GROWTH backend."""

    degree = strip.model_degree(m)
    h_grid, h_values, metadata = strip.h_trial_grid(m, degree)
    lam = math.sqrt(m)
    length = math.log(m)
    nodes, weights = np.polynomial.legendre.leggauss(quad_order)
    frequencies = np.arange(-n_bound, n_bound + 1, dtype=np.float64)
    result = np.zeros(2 * n_bound + 1, dtype=np.complex128)

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
        ).reshape(multiplicity, quad_order).sum(axis=0)
        e_values = np.sqrt(exp_x / lam) * starred_sum
        phases = np.exp(
            -2j * math.pi * np.outer(x, frequencies) / length
        )
        # NumPy/Accelerate may emit spurious floating-point warnings inside
        # complex GEMV even when every input and output is finite.  Check the
        # actual block explicitly and fail closed on a genuine nonfinite.
        with np.errstate(all="ignore"):
            block = (
                (quadrature_weights * e_values)
                @ phases
                / math.sqrt(length)
            )
        if not np.all(np.isfinite(block)):
            raise RuntimeError(f"NONFINITE_G04_BLOCK:{m}:{n_bound}:{j}")
        result += block

    projected_norm = float(np.linalg.norm(result))
    if not projected_norm > 0:
        raise RuntimeError(f"ZERO_G04_PROJECTION:{m}:{n_bound}")
    result /= projected_norm
    metadata.update(
        {
            "m": m,
            "N": n_bound,
            "quad_order": quad_order,
            "projected_norm_before_normalization": projected_norm,
            "coefficient_norm": float(np.linalg.norm(result)),
        }
    )
    return result, metadata


def ratios(
    m: int, n_bound: int, coeff: np.ndarray, grid_size: int
) -> dict[str, float]:
    """Periodic trapezoid evaluation of the exact finite Fourier row."""

    if grid_size <= 2 * n_bound:
        raise ValueError("FFT grid aliases the coefficient row")
    spectrum = np.zeros(grid_size, dtype=np.complex128)
    frequencies = np.arange(-n_bound, n_bound + 1, dtype=np.int64)
    spectrum[np.mod(frequencies, grid_size)] = coeff
    values = np.fft.ifft(spectrum) * grid_size
    x = np.arange(grid_size, dtype=np.float64) / grid_size
    abs_values = np.abs(values)
    length = math.log(m)
    denominator = abs(coeff[n_bound])
    if not denominator > 0:
        raise RuntimeError(f"ZERO_CENTRAL_COEFFICIENT:{m}:{n_bound}")
    return {
        sigma_key(sigma): float(
            np.mean(
                abs_values
                * np.exp(sigma * length * np.abs(x - 0.5))
            )
            / denominator
        )
        for sigma in SIGMAS
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
        "endpoint_ratio_257_over_13": float(rows[-1][key] / rows[0][key]),
    }


def run() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    max_grid_relative_delta = 0.0
    coefficient_norm_error = 0.0

    for m in range(M_MIN, M_MAX + 1):
        coeff, metadata = coefficients(m, N_BOUND)
        high = ratios(m, N_BOUND, coeff, FFT_GRID)
        low = ratios(m, N_BOUND, coeff, FFT_GRID_CHECK)
        row: dict[str, Any] = {"m": m, "N": N_BOUND}
        row.update(high)
        rows.append(row)
        coefficient_norm_error = max(
            coefficient_norm_error,
            abs(float(metadata["coefficient_norm"]) - 1.0),
        )
        for sigma in SIGMAS:
            key = sigma_key(sigma)
            max_grid_relative_delta = max(
                max_grid_relative_delta,
                abs(high[key] - low[key]) / high[key],
            )
        if m == M_MIN or m == M_MAX or (m - M_MIN + 1) % 8 == 0:
            print(
                f"[{m - M_MIN + 1:3d}/{M_MAX - M_MIN + 1}] "
                f"m={m} R(0.45)={high[sigma_key(0.45)]:.12g}",
                flush=True,
            )

    fits = {
        sigma_key(sigma): fit(rows, sigma_key(sigma)) for sigma in SIGMAS
    }
    baseline = next(row for row in rows if row["m"] == SENSITIVITY_M)
    sensitivity: list[dict[str, Any]] = []
    for n_bound in SENSITIVITY_N:
        coeff, _ = coefficients(SENSITIVITY_M, n_bound)
        measured = ratios(SENSITIVITY_M, n_bound, coeff, FFT_GRID)
        item: dict[str, Any] = {"m": SENSITIVITY_M, "N": n_bound}
        item.update(measured)
        for sigma in SIGMAS:
            key = sigma_key(sigma)
            item[f"{key}_over_N120"] = measured[key] / baseline[key]
        sensitivity.append(item)

    return {
        "schema": "CENTERED_MOMENT_RATIO_PROBE_V1",
        "numeric_type": "float64/complex128",
        "definition": (
            "integral |q_(m,N)(t)| exp(sigma|t|) dt "
            "/ |rawFplus_(m,N)(0)|"
        ),
        "parameters": {
            "m_min": M_MIN,
            "m_max": M_MAX,
            "N": N_BOUND,
            "sigmas": SIGMAS,
            "sensitivity_m": SENSITIVITY_M,
            "sensitivity_N": SENSITIVITY_N,
            "quadrature_order": QUAD_ORDER,
            "fft_grid": FFT_GRID,
            "fft_grid_check": FFT_GRID_CHECK,
        },
        "rows": rows,
        "fits": fits,
        "N_sensitivity": sensitivity,
        "numeric_checks": {
            "max_relative_delta_fft_32768_vs_16384":
                max_grid_relative_delta,
            "max_coefficient_norm_error": coefficient_norm_error,
        },
        "runtime": {
            "python": sys.version.split()[0],
            "numpy": np.__version__,
            "platform": platform.platform(),
        },
    }


def write_csv(result: dict[str, Any]) -> None:
    fields = ["kind", "m", "N"] + [
        sigma_key(sigma) for sigma in SIGMAS
    ]
    with RESULT_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, lineterminator="\n"
        )
        writer.writeheader()
        for row in result["rows"]:
            writer.writerow({"kind": "ladder", **row})
        for row in result["N_sensitivity"]:
            writer.writerow(
                {
                    "kind": "N_sensitivity",
                    **{field: row[field] for field in fields if field != "kind"},
                }
            )


def write_markdown(result: dict[str, Any]) -> None:
    lines = [
        "# Numerator measurements",
        "",
        "## R ladder: N = 120",
        "",
        "| m | R(0.10) | R(0.25) | R(0.40) | R(0.45) |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in result["rows"]:
        values = [
            f"{row[sigma_key(sigma)]:.12g}" for sigma in SIGMAS
        ]
        lines.append(f"| {row['m']} | " + " | ".join(values) + " |")

    lines.extend(
        [
            "",
            "## Power fits on m = 13..257",
            "",
            "`log R = intercept + beta log m`",
            "",
            "| sigma | beta | SE(beta) | R^2 | R(257)/R(13) | min R | max R |",
            "|---:|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for sigma in SIGMAS:
        item = result["fits"][sigma_key(sigma)]
        lines.append(
            f"| {sigma:.2f} | {item['beta']:.12g} | "
            f"{item['beta_standard_error']:.12g} | "
            f"{item['r_squared']:.12g} | "
            f"{item['endpoint_ratio_257_over_13']:.12g} | "
            f"{item['min']:.12g} | {item['max']:.12g} |"
        )

    lines.extend(
        [
            "",
            "## N sensitivity at m = 53",
            "",
            "| N | R(0.10) / N120 | R(0.25) / N120 | "
            "R(0.40) / N120 | R(0.45) / N120 |",
            "|---:|---:|---:|---:|---:|",
        ]
    )
    for row in result["N_sensitivity"]:
        values = [
            (
                f"{row[sigma_key(sigma)]:.12g} / "
                f"{row[f'{sigma_key(sigma)}_over_N120']:.12g}"
            )
            for sigma in SIGMAS
        ]
        lines.append(f"| {row['N']} | " + " | ".join(values) + " |")

    checks = result["numeric_checks"]
    lines.extend(
        [
            "",
            "## Float64 checks",
            "",
            "| check | value |",
            "|---|---:|",
            "| max relative delta, FFT 32768 vs 16384 | "
            f"{checks['max_relative_delta_fft_32768_vs_16384']:.12g} |",
            "| max coefficient norm error | "
            f"{checks['max_coefficient_norm_error']:.12g} |",
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
