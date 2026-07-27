#!/usr/bin/env python3
"""Float64 upper-edge sign diagnostic for the canonical D0 hTrial.

The prolate tails are far below the cancellation floor of a direct Legendre
sum.  This runner therefore evaluates each source mode by backward integration
from the regular singular endpoint, rescales the linear ODE solution between
short segments, and combines the two modes in signed-log form.  All ODE and
eigenvalue arithmetic remains float64.

This is not a proof.  It does not mutate STATE or create Bus 010.
"""

from __future__ import annotations

import csv
import json
import math
import platform
from pathlib import Path
from typing import Any

import numpy as np
from scipy import integrate, linalg

import strip_growth_probe as strip


REQUEST_DIR = Path(__file__).resolve().parent
RESULT_JSON = REQUEST_DIR / "UPPER_EDGE_SIGN_PROBE.json"
RESULT_CSV = REQUEST_DIR / "UPPER_EDGE_SIGN_PROBE.csv"

M_VALUES = (13, 53, 257)
GRID_COUNT = 2001
ENDPOINT_EPS = 1e-8
SEGMENT_LENGTH = 0.01
SERIES_ORDER = 30


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


def canonical_spectral_data(m: int) -> dict[str, Any]:
    """Float64 even-sector eigenpairs and source-normalized mode data."""

    degree = strip.model_degree(m)
    degrees = np.arange(0, degree + 1, 2, dtype=np.float64)
    c = 2 * math.pi * m
    x2_diag, x2_off = strip.legendre_x2_tridiagonal(degrees)
    eigenvalues, eigenvectors = linalg.eigh_tridiagonal(
        degrees * (degrees + 1) + c * c * x2_diag,
        c * c * x2_off,
        select="i",
        select_range=(0, 4),
        check_finite=True,
    )
    for column in range(5):
        if eigenvectors[0, column] < 0:
            eigenvectors[:, column] *= -1

    lam = math.sqrt(m)
    mode_data: dict[int, dict[str, Any]] = {}
    for column in (0, 2):
        scaled = eigenvectors[:, column] * np.sqrt(
            (2 * degrees + 1) / (2 * lam)
        )
        mode_data[column] = {
            "chi": float(eigenvalues[column]),
            "integral": float(
                eigenvectors[0, column] * math.sqrt(2 * lam)
            ),
            "center_value": float(np.polynomial.legendre.legval(0.0, scaled)),
            "last_ten_coefficient_mass": float(
                np.linalg.norm(eigenvectors[-10:, column])
            ),
        }
    return {
        "m": m,
        "lambda": lam,
        "c": c,
        "degree": degree,
        "eigenvalues_0_8": eigenvalues,
        "modes": mode_data,
    }


def endpoint_series(c: float, chi: float) -> tuple[float, float]:
    """Regular Frobenius solution at t = 1 - ENDPOINT_EPS, with y(1)=1."""

    q0 = chi - c * c
    q1 = 2 * c * c
    q2 = -c * c
    coefficients = [1.0]
    for n in range(SERIES_ORDER):
        previous = coefficients[n - 1] if n >= 1 else 0.0
        previous2 = coefficients[n - 2] if n >= 2 else 0.0
        numerator = (
            (q0 - n * (n + 1)) * coefficients[n]
            + q1 * previous
            + q2 * previous2
        )
        coefficients.append(-numerator / (2 * (n + 1) ** 2))

    eps = ENDPOINT_EPS
    value = sum(a * eps**k for k, a in enumerate(coefficients))
    derivative = -sum(
        k * coefficients[k] * eps ** (k - 1)
        for k in range(1, len(coefficients))
    )
    return value, derivative


def mode_signed_logs(
    spectral: dict[str, Any],
    column: int,
    targets: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    """Evaluate one L2-normalized source mode as sign plus log-absolute-value."""

    c = float(spectral["c"])
    chi = float(spectral["modes"][column]["chi"])
    center_value = float(spectral["modes"][column]["center_value"])
    start = 1.0 - ENDPOINT_EPS
    state = np.array(endpoint_series(c, chi), dtype=np.float64)
    log_scale = 0.0

    target_signs = np.zeros(targets.size, dtype=np.int8)
    target_logs = np.full(targets.size, -math.inf, dtype=np.float64)
    pending = targets.size - 1

    def ode(t: float, y: np.ndarray) -> tuple[float, float]:
        return (
            y[1],
            (2 * t * y[1] - (chi - c * c * t * t) * y[0])
            / (1 - t * t),
        )

    right = start
    segment_count = 0
    while right > 0:
        left = max(0.0, right - SEGMENT_LENGTH)
        solution = integrate.solve_ivp(
            ode,
            (right, left),
            state,
            method="DOP853",
            rtol=2e-12,
            atol=1e-300,
            dense_output=True,
            max_step=0.002,
        )
        if not solution.success:
            raise RuntimeError(
                f"ODE_BACKWARD_FAILURE:{spectral['m']}:{column}:"
                f"{solution.message}"
            )

        while pending >= 0 and left <= targets[pending] <= right:
            value = float(solution.sol(float(targets[pending]))[0])
            target_signs[pending] = 1 if value > 0 else -1 if value < 0 else 0
            target_logs[pending] = (
                math.log(abs(value)) + log_scale
                if value != 0
                else -math.inf
            )
            pending -= 1

        state = np.asarray(solution.y[:, -1], dtype=np.float64)
        balance = max(abs(float(state[0])), abs(float(state[1])) / max(c, 1.0))
        if not math.isfinite(balance) or balance <= 0:
            raise RuntimeError(
                f"ODE_RESCALE_FAILURE:{spectral['m']}:{column}:{right}:{left}"
            )
        state /= balance
        log_scale += math.log(balance)
        right = left
        segment_count += 1

    if pending != -1:
        raise RuntimeError(
            f"ODE_TARGET_COVERAGE_FAILURE:{spectral['m']}:{column}:{pending}"
        )

    endpoint_center_sign = 1 if state[0] > 0 else -1
    endpoint_center_log = math.log(abs(float(state[0]))) + log_scale
    normalization_sign = (1 if center_value > 0 else -1) * endpoint_center_sign
    normalization_log = math.log(abs(center_value)) - endpoint_center_log
    target_signs *= normalization_sign
    target_logs += normalization_log

    return target_signs, target_logs, {
        "segments": segment_count,
        "endpoint_center_log_abs": endpoint_center_log,
        "center_value_from_legendre": center_value,
        "normalization_log": normalization_log,
    }


def signed_log_difference(
    sign_a: int,
    log_a: float,
    sign_b: int,
    log_b: float,
) -> tuple[int, float]:
    """Return signed-log representation of a - b."""

    terms = [(sign_a, log_a), (-sign_b, log_b)]
    largest = max(log_a, log_b)
    scaled = sum(sign * math.exp(log_value - largest) for sign, log_value in terms)
    if scaled == 0:
        return 0, -math.inf
    return (1 if scaled > 0 else -1), largest + math.log(abs(scaled))


def to_float(sign: int, log_abs: float) -> float:
    if sign == 0 or log_abs < math.log(np.nextafter(0.0, 1.0)):
        return math.copysign(0.0, sign)
    return sign * math.exp(log_abs)


def cell(m: int) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    spectral = canonical_spectral_data(m)
    lam = float(spectral["lambda"])
    targets = np.linspace(0.5, 1.0, GRID_COUNT + 2, dtype=np.float64)[1:-1]

    signs0, logs0, ode0 = mode_signed_logs(spectral, 0, targets)
    signs4, logs4, ode4 = mode_signed_logs(spectral, 2, targets)
    i0 = float(spectral["modes"][0]["integral"])
    i4 = float(spectral["modes"][2]["integral"])
    denominator = math.hypot(i0, i4)

    signs = np.zeros(GRID_COUNT, dtype=np.int8)
    logs = np.full(GRID_COUNT, -math.inf, dtype=np.float64)
    values = np.zeros(GRID_COUNT, dtype=np.float64)
    for index in range(GRID_COUNT):
        signs[index], numerator_log = signed_log_difference(
            int(signs0[index]),
            float(logs0[index] + math.log(i4)),
            int(signs4[index]),
            float(logs4[index] + math.log(i0)),
        )
        logs[index] = numerator_log - math.log(denominator)
        values[index] = to_float(int(signs[index]), float(logs[index]))

    change_indices = np.flatnonzero(signs[:-1] != signs[1:])
    root_brackets = [
        {
            "t_left": float(targets[index]),
            "t_right": float(targets[index + 1]),
            "x_left": float(lam * targets[index]),
            "x_right": float(lam * targets[index + 1]),
            "gap_from_lambda_left": float(lam * (1 - targets[index])),
            "gap_from_lambda_right": float(lam * (1 - targets[index + 1])),
        }
        for index in change_indices
    ]

    min_log_index = int(np.argmin(logs))
    max_log_index = int(np.argmax(logs))
    row = {
        "m": m,
        "lambda": lam,
        "grid_count": GRID_COUNT,
        "grid_t_min": float(targets[0]),
        "grid_t_max": float(targets[-1]),
        "sign_changes": int(change_indices.size),
        "root_brackets": root_brackets,
        "sign_on_grid": (
            "POSITIVE"
            if np.all(signs > 0)
            else "NEGATIVE"
            if np.all(signs < 0)
            else "MIXED"
        ),
        "min_abs_h_float64": abs(float(values[min_log_index])),
        "min_abs_h_log10": float(logs[min_log_index] / math.log(10)),
        "min_abs_h_t": float(targets[min_log_index]),
        "max_abs_h_float64": abs(float(values[max_log_index])),
        "max_abs_h_log10": float(logs[max_log_index] / math.log(10)),
        "h_at_first_grid_point": float(values[0]),
        "h_at_last_grid_point": float(values[-1]),
        "I0": i0,
        "I4": i4,
        "D": denominator,
        "coefficient_h0": i4 / denominator,
        "coefficient_h4": -i0 / denominator,
        "degree": int(spectral["degree"]),
        "eigenvalues_0_8": spectral["eigenvalues_0_8"],
        "last_ten_mode0_coefficient_mass": spectral["modes"][0][
            "last_ten_coefficient_mass"
        ],
        "last_ten_mode4_coefficient_mass": spectral["modes"][2][
            "last_ten_coefficient_mass"
        ],
        "ode_mode0": ode0,
        "ode_mode4": ode4,
    }
    samples = [
        {
            "m": m,
            "lambda": lam,
            "grid_index": index,
            "t": float(t),
            "x": float(lam * t),
            "sign_h": int(signs[index]),
            "log10_abs_h": float(logs[index] / math.log(10)),
            "h_float64": float(values[index]),
        }
        for index, t in enumerate(targets)
    ]
    return row, samples


def main() -> None:
    rows: list[dict[str, Any]] = []
    samples: list[dict[str, Any]] = []
    for m in M_VALUES:
        row, row_samples = cell(m)
        rows.append(row)
        samples.extend(row_samples)

    verdict = (
        "UPPER_EDGE_DIAG_SIGN_CHANGE"
        if any(row["sign_changes"] > 0 for row in rows)
        else "UPPER_EDGE_DIAG_SINGLE_SIGN"
    )
    payload = {
        "status": verdict,
        "epistemic_status": "FLOAT64_DIAGNOSTIC_NOT_A_PROOF",
        "coefficient_line": "(I4*h0 - I0*h4)/sqrt(I0^2 + I4^2)",
        "grid_rule": "linspace(1/2,1,2003)[1:-1]",
        "method": (
            "float64 even-sector eigenvalues; regular endpoint Frobenius "
            "series; dynamically rescaled backward DOP853; signed-log mixing"
        ),
        "environment": {
            "python": platform.python_version(),
            "numpy": np.__version__,
        },
        "rows": rows,
    }
    RESULT_JSON.write_text(
        json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    with RESULT_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(samples[0]),
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(samples)
    print(json.dumps(json_safe(payload), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
