#!/usr/bin/env python3
"""Full-window tooth-band sign diagnostic for the canonical D0 h_lambda.

The probe enumerates every open tooth band separately and evaluates the
canonical plus-phase packet with a dynamically rescaled prolate ODE solver.
At teeth the support-endpoint term has weight one half.  Three independent
spectral/ODE resolution levels are compared.

This is a numerical diagnostic, not a proof.  It does not mutate STATE,
create Bus 010, or port the cloud Muntz code.
"""

from __future__ import annotations

import csv
import json
import math
import platform
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
from scipy import integrate, linalg

import strip_growth_probe as strip


REQUEST_DIR = Path(__file__).resolve().parent
RESULT_JSON = REQUEST_DIR / "E_STAR_FULL_WINDOW_SIGN_PROBE.json"
BAND_CSV = REQUEST_DIR / "E_STAR_FULL_WINDOW_SIGN_PROBE_BANDS.csv"
TOOTH_CSV = REQUEST_DIR / "E_STAR_FULL_WINDOW_SIGN_PROBE_TEETH.csv"

M_VALUES = (13, 53, 257)
BAND_POINTS = 65
SERIES_ORDER = 36


@dataclass(frozen=True)
class PrecisionLevel:
    name: str
    degree_factor: float
    endpoint_eps: float
    segment_length: float
    rtol: float
    max_step: float


LEVELS = (
    PrecisionLevel("P1", 6.0, 2e-8, 0.020, 2e-10, 0.004),
    PrecisionLevel("P2", 8.0, 1e-8, 0.010, 2e-12, 0.002),
    PrecisionLevel("P3", 10.0, 5e-9, 0.005, 3e-13, 0.001),
)


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(item) for item in value]
    if isinstance(value, np.ndarray):
        return json_safe(value.tolist())
    if isinstance(value, np.generic):
        return json_safe(value.item())
    return value


def signed_log_sum(signs: np.ndarray, logs: np.ndarray) -> tuple[int, float]:
    finite = (signs != 0) & np.isfinite(logs)
    if not np.any(finite):
        return 0, -math.inf
    selected_logs = logs[finite]
    selected_signs = signs[finite].astype(np.float64)
    largest = float(np.max(selected_logs))
    scaled = float(np.sum(selected_signs * np.exp(selected_logs - largest)))
    if scaled == 0.0:
        return 0, -math.inf
    return (1 if scaled > 0 else -1), largest + math.log(abs(scaled))


def signed_log_to_float(sign: int, log_abs: float) -> float:
    if sign == 0 or not math.isfinite(log_abs):
        return 0.0
    if log_abs < math.log(np.nextafter(0.0, 1.0)):
        return math.copysign(0.0, sign)
    if log_abs > math.log(np.finfo(np.float64).max):
        return math.copysign(math.inf, sign)
    return sign * math.exp(log_abs)


def canonical_spectral_data(
    m: int, level: PrecisionLevel
) -> dict[str, Any]:
    degree = max(180, 2 * math.ceil(level.degree_factor * m))
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
    modes: dict[int, dict[str, Any]] = {}
    for column in (0, 2):
        scaled = eigenvectors[:, column] * np.sqrt(
            (2 * degrees + 1) / (2 * lam)
        )
        modes[column] = {
            "characteristic": float(eigenvalues[column]),
            "integral": float(
                eigenvectors[0, column] * math.sqrt(2 * lam)
            ),
            "center": float(np.polynomial.legendre.legval(0.0, scaled)),
            "tail_mass": float(np.linalg.norm(eigenvectors[-10:, column])),
        }
    return {
        "m": m,
        "lambda": lam,
        "c": c,
        "degree": degree,
        "modes": modes,
        "eigenvalues_0_8": eigenvalues,
    }


def endpoint_series(
    c: float,
    characteristic: float,
    eps: float,
) -> tuple[float, float]:
    q0 = characteristic - c * c
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
    level: PrecisionLevel,
) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    c = float(spectral["c"])
    characteristic = float(spectral["modes"][column]["characteristic"])
    center = float(spectral["modes"][column]["center"])
    start = 1.0 - level.endpoint_eps
    state = np.array(
        endpoint_series(c, characteristic, level.endpoint_eps),
        dtype=np.float64,
    )
    log_scale = 0.0

    raw_signs = np.zeros(targets.size, dtype=np.int8)
    raw_logs = np.full(targets.size, -math.inf, dtype=np.float64)

    def ode(t: float, y: np.ndarray) -> tuple[float, float]:
        return (
            y[1],
            (
                2 * t * y[1]
                - (characteristic - c * c * t * t) * y[0]
            )
            / (1 - t * t),
        )

    right = start
    segment_count = 0
    while right > 0:
        left = max(0.0, right - level.segment_length)
        solution = integrate.solve_ivp(
            ode,
            (right, left),
            state,
            method="DOP853",
            rtol=level.rtol,
            atol=1e-300,
            dense_output=True,
            max_step=level.max_step,
        )
        if not solution.success:
            raise RuntimeError(
                f"ODE_BACKWARD_FAILURE:{spectral['m']}:{level.name}:"
                f"{column}:{solution.message}"
            )

        lo = int(np.searchsorted(targets, left, side="left"))
        hi = int(np.searchsorted(targets, right, side="right"))
        if hi > lo:
            values = np.asarray(solution.sol(targets[lo:hi])[0])
            raw_signs[lo:hi] = np.sign(values).astype(np.int8)
            nonzero = values != 0
            raw_logs[lo:hi][nonzero] = (
                np.log(np.abs(values[nonzero])) + log_scale
            )

        state = np.asarray(solution.y[:, -1], dtype=np.float64)
        balance = max(
            abs(float(state[0])),
            abs(float(state[1])) / max(c, 1.0),
        )
        if not math.isfinite(balance) or balance <= 0:
            raise RuntimeError(
                f"ODE_RESCALE_FAILURE:{spectral['m']}:{level.name}:"
                f"{column}:{right}:{left}"
            )
        state /= balance
        log_scale += math.log(balance)
        right = left
        segment_count += 1

    if np.any(raw_signs == 0):
        missing = int(np.count_nonzero(raw_signs == 0))
        raise RuntimeError(
            f"ODE_TARGET_COVERAGE_OR_ZERO:{spectral['m']}:{level.name}:"
            f"{column}:{missing}"
        )

    center_ode_sign = 1 if state[0] > 0 else -1
    center_ode_log = math.log(abs(float(state[0]))) + log_scale
    normalization_sign = (1 if center > 0 else -1) * center_ode_sign
    normalization_log = math.log(abs(center)) - center_ode_log
    signs = raw_signs * normalization_sign
    logs = raw_logs + normalization_log
    return signs, logs, {
        "segments": segment_count,
        "center_ode_log_abs": center_ode_log,
        "normalization_sign": normalization_sign,
        "normalization_log": normalization_log,
        "endpoint_sign": normalization_sign,
        "endpoint_log_abs": normalization_log,
    }


def make_evaluation_plan(m: int) -> tuple[np.ndarray, list[dict[str, Any]]]:
    lam = math.sqrt(m)
    targets: list[float] = []
    records: list[dict[str, Any]] = []

    for r in range(1, m):
        left = lam / (r + 1)
        right = lam / r
        for point in range(1, BAND_POINTS + 1):
            fraction = point / (BAND_POINTS + 1)
            u = left + fraction * (right - left)
            offset = len(targets)
            targets.extend(n * u / lam for n in range(1, r + 1))
            records.append(
                {
                    "kind": "band",
                    "r": r,
                    "point": point,
                    "u": u,
                    "offset": offset,
                    "count": r,
                }
            )

    for r in range(1, m + 1):
        u = lam / r
        offset = len(targets)
        targets.extend(n / r for n in range(1, r))
        records.append(
            {
                "kind": "tooth",
                "r": r,
                "point": 0,
                "u": u,
                "offset": offset,
                "count": r - 1,
            }
        )

    target_array = np.asarray(targets, dtype=np.float64)
    unique, inverse = np.unique(target_array, return_inverse=True)
    for record in records:
        offset = int(record["offset"])
        count = int(record["count"])
        record["indices"] = inverse[offset : offset + count]
    return unique, records


def canonical_h_logs(
    spectral: dict[str, Any],
    mode0_signs: np.ndarray,
    mode0_logs: np.ndarray,
    mode4_signs: np.ndarray,
    mode4_logs: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    i0 = float(spectral["modes"][0]["integral"])
    i4 = float(spectral["modes"][2]["integral"])
    denominator = math.hypot(i0, i4)
    log_a = mode0_logs + math.log(i4 / denominator)
    log_b = mode4_logs + math.log(i0 / denominator)
    largest = np.maximum(log_a, log_b)
    scaled = (
        mode0_signs.astype(np.float64) * np.exp(log_a - largest)
        - mode4_signs.astype(np.float64) * np.exp(log_b - largest)
    )
    signs = np.sign(scaled).astype(np.int8)
    logs = np.full(scaled.size, -math.inf, dtype=np.float64)
    nonzero = scaled != 0
    logs[nonzero] = largest[nonzero] + np.log(np.abs(scaled[nonzero]))
    return signs, logs


def combine_endpoint(
    spectral: dict[str, Any],
    mode0_meta: dict[str, Any],
    mode4_meta: dict[str, Any],
) -> tuple[int, float]:
    i0 = float(spectral["modes"][0]["integral"])
    i4 = float(spectral["modes"][2]["integral"])
    denominator = math.hypot(i0, i4)
    signs = np.asarray(
        [mode0_meta["endpoint_sign"], -mode4_meta["endpoint_sign"]],
        dtype=np.int8,
    )
    logs = np.asarray(
        [
            mode0_meta["endpoint_log_abs"] + math.log(i4 / denominator),
            mode4_meta["endpoint_log_abs"] + math.log(i0 / denominator),
        ],
        dtype=np.float64,
    )
    return signed_log_sum(signs, logs)


def evaluate_level(
    m: int,
    level: PrecisionLevel,
    targets: np.ndarray,
    records: list[dict[str, Any]],
) -> dict[str, Any]:
    spectral = canonical_spectral_data(m, level)
    signs0, logs0, meta0 = mode_signed_logs(
        spectral, 0, targets, level
    )
    signs4, logs4, meta4 = mode_signed_logs(
        spectral, 2, targets, level
    )
    h_signs, h_logs = canonical_h_logs(
        spectral, signs0, logs0, signs4, logs4
    )
    endpoint_sign, endpoint_log = combine_endpoint(
        spectral, meta0, meta4
    )

    i0 = float(spectral["modes"][0]["integral"])
    i4 = float(spectral["modes"][2]["integral"])
    denominator = math.hypot(i0, i4)
    h_center = (
        i4 * float(spectral["modes"][0]["center"])
        - i0 * float(spectral["modes"][2]["center"])
    ) / denominator

    band_samples: dict[int, list[dict[str, Any]]] = {}
    teeth: list[dict[str, Any]] = []
    for record in records:
        indices = np.asarray(record["indices"], dtype=np.int64)
        term_signs = h_signs[indices]
        term_logs = h_logs[indices]
        if record["kind"] == "tooth":
            term_signs = np.concatenate(
                [term_signs, np.asarray([endpoint_sign], dtype=np.int8)]
            )
            term_logs = np.concatenate(
                [
                    term_logs,
                    np.asarray([endpoint_log - math.log(2)], dtype=np.float64),
                ]
            )
        sign, log_abs = signed_log_sum(term_signs, term_logs)
        log_abs += 0.5 * math.log(float(record["u"]))
        row = {
            "m": m,
            "level": level.name,
            "r": int(record["r"]),
            "point": int(record["point"]),
            "u": float(record["u"]),
            "sign": sign,
            "log10_abs": log_abs / math.log(10),
            "value_float64": signed_log_to_float(sign, log_abs),
        }
        if record["kind"] == "band":
            band_samples.setdefault(int(record["r"]), []).append(row)
        else:
            teeth.append(row)

    bands: list[dict[str, Any]] = []
    for r, samples in sorted(band_samples.items()):
        signs = np.asarray([row["sign"] for row in samples], dtype=np.int8)
        logs = np.asarray(
            [row["log10_abs"] for row in samples], dtype=np.float64
        )
        positive = np.flatnonzero(signs > 0)
        negative = np.flatnonzero(signs < 0)
        bands.append(
            {
                "m": m,
                "level": level.name,
                "r": r,
                "u_left": math.sqrt(m) / (r + 1),
                "u_right": math.sqrt(m) / r,
                "positive_points": int(positive.size),
                "negative_points": int(negative.size),
                "zero_points": int(np.count_nonzero(signs == 0)),
                "max_positive_log10": (
                    float(np.max(logs[positive]))
                    if positive.size
                    else None
                ),
                "max_abs_log10": float(np.max(logs)),
                "min_abs_log10": float(np.min(logs)),
                "samples": samples,
            }
        )

    lower_tooth = teeth[-1]
    lam = math.sqrt(m)
    trap_error = (
        signed_log_to_float(lower_tooth["sign"], lower_tooth["log10_abs"] * math.log(10))
        + h_center / (2 * math.sqrt(lam))
    ) / math.sqrt(lam)
    counterterm = -h_center / (2 * math.sqrt(lam))
    reconstructed = math.sqrt(lam) * trap_error + counterterm

    return {
        "m": m,
        "level": level.name,
        "parameters": {
            "degree_factor": level.degree_factor,
            "degree": spectral["degree"],
            "endpoint_eps": level.endpoint_eps,
            "segment_length": level.segment_length,
            "rtol": level.rtol,
            "max_step": level.max_step,
            "band_points": BAND_POINTS,
        },
        "spectral": {
            "eigenvalues_0_8": spectral["eigenvalues_0_8"],
            "mode0_tail_mass": spectral["modes"][0]["tail_mass"],
            "mode4_tail_mass": spectral["modes"][2]["tail_mass"],
            "I0": i0,
            "I4": i4,
            "D": denominator,
            "coefficient_h0": i4 / denominator,
            "coefficient_h4": -i0 / denominator,
        },
        "h_lambda_0": h_center,
        "h_lambda_endpoint": {
            "sign": endpoint_sign,
            "log10_abs": endpoint_log / math.log(10),
            "value_float64": signed_log_to_float(
                endpoint_sign, endpoint_log
            ),
        },
        "bands": bands,
        "teeth": teeth,
        "lower_endpoint_trapezoid": {
            "u": 1 / lam,
            "E_star": lower_tooth["value_float64"],
            "E_star_sign": lower_tooth["sign"],
            "E_star_log10_abs": lower_tooth["log10_abs"],
            "trap_error": trap_error,
            "sqrt_lambda_times_trap_error": math.sqrt(lam) * trap_error,
            "origin_counterterm": counterterm,
            "reconstructed_E_star": reconstructed,
            "absolute_reconstruction_residual": abs(
                reconstructed - lower_tooth["value_float64"]
            ),
        },
        "ode": {"mode0": meta0, "mode4": meta4},
    }


def stable_interval(level_results: list[dict[str, Any]], r: int) -> dict[str, Any] | None:
    by_level = []
    for result in level_results:
        band = result["bands"][r - 1]
        by_level.append(band["samples"])
    signs = np.asarray(
        [[row["sign"] for row in samples] for samples in by_level],
        dtype=np.int8,
    )
    logs = np.asarray(
        [[row["log10_abs"] for row in samples] for samples in by_level],
        dtype=np.float64,
    )
    stable = np.all(signs > 0, axis=0)
    indices = np.flatnonzero(stable)
    if indices.size < 3:
        return None

    runs: list[np.ndarray] = []
    start = 0
    for index in range(1, indices.size):
        if indices[index] != indices[index - 1] + 1:
            runs.append(indices[start:index])
            start = index
    runs.append(indices[start:])
    runs = [run for run in runs if run.size >= 3]
    if not runs:
        return None
    run = max(runs, key=lambda item: item.size)
    left_index = int(run[0])
    right_index = int(run[-1])
    return {
        "r": r,
        "u_left_sample": by_level[0][left_index]["u"],
        "u_right_sample": by_level[0][right_index]["u"],
        "sample_count": int(run.size),
        "min_log10_margin_across_levels_and_interval": float(
            np.min(logs[:, run])
        ),
        "max_log10_value_across_levels_and_interval": float(
            np.max(logs[:, run])
        ),
    }


def summarize_m(m: int, results: list[dict[str, Any]]) -> dict[str, Any]:
    stable_positive = []
    for r in range(1, m):
        interval = stable_interval(results, r)
        if interval is not None:
            stable_positive.append(interval)

    signs_by_level = []
    for result in results:
        signs_by_level.extend(
            sample["sign"]
            for band in result["bands"]
            for sample in band["samples"]
        )
        signs_by_level.extend(tooth["sign"] for tooth in result["teeth"])
    unresolved_zero = any(sign == 0 for sign in signs_by_level)
    return {
        "m": m,
        "lambda": math.sqrt(m),
        "band_count": m - 1,
        "band_points_per_level": BAND_POINTS,
        "tooth_count_per_level": m,
        "stable_positive_interval_count": len(stable_positive),
        "first_stable_positive_interval": (
            stable_positive[0] if stable_positive else None
        ),
        "widest_stable_positive_interval": (
            max(stable_positive, key=lambda item: item["sample_count"])
            if stable_positive
            else None
        ),
        "unresolved_zero_sample": unresolved_zero,
        "h_lambda_0_by_level": [
            {
                "level": result["level"],
                "value": result["h_lambda_0"],
            }
            for result in results
        ],
        "lower_endpoint_by_level": [
            {
                "level": result["level"],
                **result["lower_endpoint_trapezoid"],
            }
            for result in results
        ],
    }


def run() -> dict[str, Any]:
    all_results: dict[int, list[dict[str, Any]]] = {}
    band_rows: list[dict[str, Any]] = []
    tooth_rows: list[dict[str, Any]] = []

    for m in M_VALUES:
        targets, records = make_evaluation_plan(m)
        level_results = []
        for level in LEVELS:
            print(
                f"[E_STAR_FULL_WINDOW] m={m} level={level.name} "
                f"unique_targets={targets.size}",
                flush=True,
            )
            result = evaluate_level(m, level, targets, records)
            level_results.append(result)
            for band in result["bands"]:
                band_rows.append(
                    {key: value for key, value in band.items() if key != "samples"}
                )
            tooth_rows.extend(result["teeth"])
        all_results[m] = level_results

    summaries = [
        summarize_m(m, all_results[m])
        for m in M_VALUES
    ]
    any_positive = any(
        summary["stable_positive_interval_count"] > 0
        for summary in summaries
    )
    any_unresolved = any(
        summary["unresolved_zero_sample"] for summary in summaries
    )
    if any_positive:
        verdict = "ESTAR_PHASE_SIGN_KILLED"
    elif any_unresolved:
        verdict = "INSTRUMENT_FLOOR_UNRESOLVED"
    else:
        verdict = "ESTAR_FULL_WINDOW_DIAG_SINGLE_SIGN"

    payload = {
        "verdict": verdict,
        "epistemic_status": "NUMERICAL_DIAGNOSTIC_NOT_A_THEOREM",
        "coefficient_line": "(I4*h0-I0*h4)/sqrt(I0^2+I4^2)",
        "source_phase": "+",
        "starred_tooth_rule": (
            "at u=lambda/r the last active support-endpoint term h(lambda) "
            "has weight 1/2"
        ),
        "precision_levels": [level.__dict__ for level in LEVELS],
        "band_points": BAND_POINTS,
        "dual_residual": "RESIDUAL_SKIPPED_NO_LOCAL_DUAL_EVALUATOR",
        "environment": {
            "python": platform.python_version(),
            "numpy": np.__version__,
        },
        "summaries": summaries,
        "results": {
            str(m): all_results[m] for m in M_VALUES
        },
    }

    RESULT_JSON.write_text(
        json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    with BAND_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(band_rows[0]),
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(band_rows)
    with TOOTH_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(tooth_rows[0]),
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(tooth_rows)

    print(json.dumps(json_safe({
        "verdict": verdict,
        "summaries": summaries,
        "dual_residual": payload["dual_residual"],
    }), indent=2, sort_keys=True))
    return payload


if __name__ == "__main__":
    run()
