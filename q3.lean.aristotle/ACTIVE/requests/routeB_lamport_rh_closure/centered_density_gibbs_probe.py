#!/usr/bin/env python3
"""Gibbs and signed-mass diagnostics for the centered D0 density."""

from __future__ import annotations

import csv
import json
import math
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np

import centered_moment_ratio_probe as ratio


REQUEST_DIR = Path(__file__).resolve().parent
RESULT_JSON = REQUEST_DIR / "CENTERED_DENSITY_GIBBS_PROBE.json"
RESULT_CSV = REQUEST_DIR / "CENTERED_DENSITY_NEGATIVE_MASS_PROFILE.csv"
RESULT_MD = REQUEST_DIR / "CENTERED_DENSITY_GIBBS_PROBE.md"

MINIMUM_CELLS = ((53, 120), (53, 240), (257, 120), (257, 240))
MINIMUM_GRID = 4001
M_MIN = 13
M_MAX = 257
N_BOUND = 120
INTEGRAL_GRID = 65536
INTEGRAL_GRID_CHECK = 32768
MP_THRESHOLD = 1.0e-12
MP_DPS = 50


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


def aligned_values(
    m: int, n_bound: int, coeff: np.ndarray, grid_size: int
) -> tuple[np.ndarray, float]:
    spectrum = np.zeros(grid_size, dtype=np.complex128)
    frequencies = np.arange(-n_bound, n_bound + 1, dtype=np.int64)
    spectrum[np.mod(frequencies, grid_size)] = coeff
    values = np.fft.ifft(spectrum) * grid_size / math.sqrt(math.log(m))
    phase_sign = 1.0 if coeff[n_bound].real >= 0 else -1.0
    return phase_sign * values.real, phase_sign


def minimum_on_previous_grid(
    m: int, n_bound: int, coeff: np.ndarray
) -> dict[str, Any]:
    frequencies = np.arange(-n_bound, n_bound + 1, dtype=np.float64)
    x = np.arange(MINIMUM_GRID, dtype=np.float64) / (MINIMUM_GRID - 1)
    with np.errstate(all="ignore"):
        values = (
            np.exp(2j * math.pi * np.outer(x, frequencies))
            @ coeff
            / math.sqrt(math.log(m))
        )
    phase_sign = 1.0 if coeff[n_bound].real >= 0 else -1.0
    aligned = phase_sign * values.real
    index = int(np.argmin(aligned))
    return {
        "m": m,
        "N": n_bound,
        "grid_count": MINIMUM_GRID,
        "minimum_aligned_density": float(aligned[index]),
        "minimum_grid_index": index,
        "minimum_x": float(x[index]),
        "phase_sign": phase_sign,
    }


def signed_mass_ratio_float(
    m: int, coeff: np.ndarray, grid_size: int
) -> tuple[dict[str, float], np.ndarray]:
    aligned, _ = aligned_values(m, N_BOUND, coeff, grid_size)
    negative_mass = float(np.mean(np.maximum(-aligned, 0.0)))
    positive_mass = float(np.mean(np.maximum(aligned, 0.0)))
    if not positive_mass > 0:
        raise RuntimeError(f"NONPOSITIVE_POSITIVE_MASS:{m}")
    return {
        "negative_mass": negative_mass,
        "positive_mass": positive_mass,
        "negative_over_positive": negative_mass / positive_mass,
    }, aligned


def mp_discrete_correction(
    m: int, coeff: np.ndarray, aligned_float: np.ndarray
) -> dict[str, Any]:
    """Correct the tiny discrete negative mass with 50-digit summation.

    The binary64 coefficient row is held fixed.  Points safely above the
    float error scale cannot contribute to the negative part, so only the
    low-valued candidates and the 40 worst points are re-summed.
    """

    mp.mp.dps = MP_DPS
    grid_size = aligned_float.size
    frequencies = range(-N_BOUND, N_BOUND + 1)
    coeff_mp = [
        mp.mpc(mp.mpf(float(value.real)), mp.mpf(float(value.imag)))
        for value in coeff
    ]
    phase_sign = mp.mpf(1 if coeff[N_BOUND].real >= 0 else -1)
    candidate = set(np.flatnonzero(aligned_float < 1.0e-11).tolist())
    candidate.update(
        int(index) for index in np.argsort(aligned_float)[:40]
    )
    negative_sum = mp.mpf(0)
    minimum = mp.inf
    negative_count = 0
    for index in sorted(candidate):
        x = mp.mpf(index) / mp.mpf(grid_size)
        value = mp.mpc(0)
        for offset, frequency in enumerate(frequencies):
            value += coeff_mp[offset] * mp.exp(
                2j * mp.pi * frequency * x
            )
        aligned = phase_sign * mp.re(value) / mp.sqrt(mp.log(m))
        minimum = min(minimum, aligned)
        if aligned < 0:
            negative_sum -= aligned
            negative_count += 1
    negative_mass = negative_sum / mp.mpf(grid_size)
    total_mass = (
        phase_sign
        * mp.re(coeff_mp[N_BOUND])
        / mp.sqrt(mp.log(m))
    )
    positive_mass = total_mass + negative_mass
    corrected_ratio = (
        negative_mass / positive_mass if positive_mass > 0 else mp.nan
    )
    return {
        "mpmath_dps": MP_DPS,
        "candidate_count": len(candidate),
        "negative_candidate_count": negative_count,
        "minimum_candidate_aligned": mp.nstr(minimum, 52),
        "negative_mass_discrete": mp.nstr(negative_mass, 52),
        "positive_mass_discrete": mp.nstr(positive_mass, 52),
        "negative_over_positive_discrete": mp.nstr(corrected_ratio, 52),
    }


def fit(rows: list[dict[str, Any]], key: str) -> dict[str, Any]:
    positive_rows = [row for row in rows if float(row[key]) > 0]
    x = np.log(np.array([row["m"] for row in positive_rows]))
    y = np.log(np.array([float(row[key]) for row in positive_rows]))
    design = np.column_stack([np.ones(x.size), x])
    intercept, beta = np.linalg.lstsq(design, y, rcond=None)[0]
    fitted = design @ np.array([intercept, beta])
    residual = y - fitted
    sse = float(residual @ residual)
    centered = y - y.mean()
    sst = float(centered @ centered)
    return {
        "model": f"log({key}) = intercept + beta*log(m)",
        "row_count": len(positive_rows),
        "intercept": float(intercept),
        "prefactor": math.exp(float(intercept)),
        "beta": float(beta),
        "r_squared": 1.0 if sst == 0 else 1.0 - sse / sst,
        "min": min(float(row[key]) for row in positive_rows),
        "max": max(float(row[key]) for row in positive_rows),
        "endpoint_ratio_257_over_13":
            float(positive_rows[-1][key]) / float(positive_rows[0][key]),
    }


def run() -> dict[str, Any]:
    coefficient_cache: dict[tuple[int, int], np.ndarray] = {}
    minima: list[dict[str, Any]] = []
    for m, n_bound in MINIMUM_CELLS:
        coeff, _ = ratio.coefficients(m, n_bound)
        coefficient_cache[(m, n_bound)] = coeff
        item = minimum_on_previous_grid(m, n_bound, coeff)
        minima.append(item)
        print(
            f"minimum ({m},{n_bound})="
            f"{item['minimum_aligned_density']:.12g}",
            flush=True,
        )

    rows: list[dict[str, Any]] = []
    max_grid_relative_delta = 0.0
    mp_cells = 0
    for m in range(M_MIN, M_MAX + 1):
        coeff = coefficient_cache.get((m, N_BOUND))
        if coeff is None:
            coeff, _ = ratio.coefficients(m, N_BOUND)
        high, aligned = signed_mass_ratio_float(
            m, coeff, INTEGRAL_GRID
        )
        low, _ = signed_mass_ratio_float(
            m, coeff, INTEGRAL_GRID_CHECK
        )
        high_ratio = high["negative_over_positive"]
        low_ratio = low["negative_over_positive"]
        relative_delta = (
            abs(high_ratio - low_ratio) / high_ratio
            if high_ratio > 0
            else 0.0
        )
        max_grid_relative_delta = max(
            max_grid_relative_delta, relative_delta
        )
        row: dict[str, Any] = {
            "m": m,
            "N": N_BOUND,
            **high,
            "grid_check_ratio": low_ratio,
            "grid_relative_delta": relative_delta,
            "mpmath_refined": high_ratio < MP_THRESHOLD,
        }
        if high_ratio < MP_THRESHOLD:
            correction = mp_discrete_correction(m, coeff, aligned)
            row["mpmath"] = correction
            row["ratio_for_fit"] = float(
                mp.mpf(correction["negative_over_positive_discrete"])
            )
            mp_cells += 1
        else:
            row["mpmath"] = None
            row["ratio_for_fit"] = high_ratio
        rows.append(row)
        if m == M_MIN or m == M_MAX or (m - M_MIN + 1) % 16 == 0:
            print(
                f"[{m - M_MIN + 1:3d}/{M_MAX - M_MIN + 1}] "
                f"m={m} ratio={row['ratio_for_fit']:.12g}",
                flush=True,
            )

    comparisons = []
    for m in (53, 257):
        n120 = next(
            item for item in minima if item["m"] == m and item["N"] == 120
        )
        n240 = next(
            item for item in minima if item["m"] == m and item["N"] == 240
        )
        old = abs(float(n120["minimum_aligned_density"]))
        new = abs(float(n240["minimum_aligned_density"]))
        comparisons.append(
            {
                "m": m,
                "N120_minimum": n120["minimum_aligned_density"],
                "N240_minimum": n240["minimum_aligned_density"],
                "absolute_violation_ratio_N240_over_N120":
                    new / old if old > 0 else math.nan,
                "absolute_violation_reduction_factor":
                    old / new if new > 0 else math.inf,
            }
        )

    mode_doubling_verdict = (
        "GIBBS_CONFIRMED"
        if all(
            item["absolute_violation_ratio_N240_over_N120"] < 1.0
            for item in comparisons
        )
        else "GIBBS_NOT_CONFIRMED"
    )
    return {
        "schema": "CENTERED_DENSITY_GIBBS_PROBE_V1",
        "numeric_type": "float64/complex128; selective mpmath50",
        "minimum_grid": MINIMUM_GRID,
        "integral_grid": INTEGRAL_GRID,
        "integral_grid_check": INTEGRAL_GRID_CHECK,
        "mode_doubling_verdict": mode_doubling_verdict,
        "minima": minima,
        "comparisons": comparisons,
        "negative_mass_rows": rows,
        "fit": fit(rows, "ratio_for_fit"),
        "checks": {
            "mpmath_refined_cell_count": mp_cells,
            "max_grid_relative_delta": max_grid_relative_delta,
            "all_ratios_nonnegative":
                all(row["ratio_for_fit"] >= 0 for row in rows),
        },
    }


def write_csv(result: dict[str, Any]) -> None:
    fields = [
        "m",
        "N",
        "negative_mass",
        "positive_mass",
        "negative_over_positive",
        "grid_check_ratio",
        "grid_relative_delta",
        "mpmath_refined",
        "ratio_for_fit",
    ]
    with RESULT_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, extrasaction="ignore",
            lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(result["negative_mass_rows"])


def write_markdown(result: dict[str, Any]) -> None:
    lines = [
        "# CENTERED_DENSITY_GIBBS_PROBE",
        "",
        f"Verdict: `{result['mode_doubling_verdict']}`.",
        "",
        "## Mode-doubling minimum",
        "",
        "| m | min aligned q, N=120 | min aligned q, N=240 | "
        "|violation 240|/|violation 120| | reduction factor |",
        "|---:|---:|---:|---:|---:|",
    ]
    for item in result["comparisons"]:
        lines.append(
            f"| {item['m']} | {item['N120_minimum']:.12g} | "
            f"{item['N240_minimum']:.12g} | "
            f"{item['absolute_violation_ratio_N240_over_N120']:.12g} | "
            f"{item['absolute_violation_reduction_factor']:.12g} |"
        )
    lines.extend(
        [
            "",
            "## Negative/positive mass profile",
            "",
            "| m | negative mass | positive mass | ratio | "
            "grid-check ratio | mp50 refined |",
            "|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for row in result["negative_mass_rows"]:
        lines.append(
            f"| {row['m']} | {row['negative_mass']:.12g} | "
            f"{row['positive_mass']:.12g} | "
            f"{row['ratio_for_fit']:.12g} | "
            f"{row['grid_check_ratio']:.12g} | "
            f"{row['mpmath_refined']} |"
        )
    fit_result = result["fit"]
    lines.extend(
        [
            "",
            "## Fit",
            "",
            f"`ratio = {fit_result['prefactor']:.12g} "
            f"* m^{fit_result['beta']:.12g}`",
            "",
            f"`R^2 = {fit_result['r_squared']:.12g}`; "
            f"`min = {fit_result['min']:.12g}`; "
            f"`max = {fit_result['max']:.12g}`.",
        ]
    )
    RESULT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


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
