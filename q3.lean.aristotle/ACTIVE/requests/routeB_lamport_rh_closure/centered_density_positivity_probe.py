#!/usr/bin/env python3
"""Float64 positivity micro-probe for the exact centered D0 density."""

from __future__ import annotations

import csv
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import centered_moment_ratio_probe as ratio


REQUEST_DIR = Path(__file__).resolve().parent
RESULT_JSON = REQUEST_DIR / "CENTERED_DENSITY_POSITIVITY_PROBE.json"
RESULT_CSV = REQUEST_DIR / "CENTERED_DENSITY_POSITIVITY_PROBE.csv"
RESULT_MD = REQUEST_DIR / "CENTERED_DENSITY_POSITIVITY_PROBE.md"

CELLS = ((53, 120), (257, 120))
GRID_COUNT = 4001


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


def evaluate_cell(
    m: int, n_bound: int
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    coeff, metadata = ratio.coefficients(m, n_bound)
    length = math.log(m)
    t = np.linspace(
        -length / 2, length / 2, GRID_COUNT, dtype=np.float64
    )
    frequencies_int = np.arange(-n_bound, n_bound + 1, dtype=np.int64)
    frequencies = frequencies_int.astype(np.float64)
    signs = np.where(frequencies_int % 2 == 0, 1.0, -1.0)
    phases = np.exp(
        2j
        * math.pi
        * np.outer(t / length, frequencies)
    )
    with np.errstate(all="ignore"):
        density = phases @ (signs * coeff) / math.sqrt(length)

    # Independent recentered-coordinate evaluation of the same finite sum.
    x = t / length + 0.5
    with np.errstate(all="ignore"):
        recentered = (
            np.exp(2j * math.pi * np.outer(x, frequencies))
            @ coeff
            / math.sqrt(length)
        )
    crosscheck = float(np.max(np.abs(density - recentered)))
    if not np.all(np.isfinite(density)):
        raise RuntimeError(f"NONFINITE_CENTERED_DENSITY:{m}:{n_bound}")

    real = density.real
    imag = density.imag
    negative = real < 0.0
    min_index = int(np.argmin(real))
    max_index = int(np.argmax(real))
    minimum = float(real[min_index])
    maximum = float(real[max_index])
    central_coefficient = coeff[n_bound]
    phase_sign = 1.0 if central_coefficient.real >= 0 else -1.0
    phase_aligned_real = phase_sign * real
    summary = {
        "m": m,
        "N": n_bound,
        "grid_count": GRID_COUNT,
        "window_length": length,
        "min_real_q": minimum,
        "min_real_q_t": float(t[min_index]),
        "max_real_q": maximum,
        "max_real_q_t": float(t[max_index]),
        "min_real_over_max_real": minimum / maximum,
        "max_abs_imag_q": float(np.max(np.abs(imag))),
        "negative_count": int(np.count_nonzero(negative)),
        "negative_fraction": float(np.mean(negative)),
        "central_coefficient_real": float(central_coefficient.real),
        "central_coefficient_imag": float(central_coefficient.imag),
        "phase_sign_from_c0": phase_sign,
        "phase_aligned_min_real": float(np.min(phase_aligned_real)),
        "phase_aligned_max_real": float(np.max(phase_aligned_real)),
        "phase_aligned_min_over_max": float(
            np.min(phase_aligned_real) / np.max(phase_aligned_real)
        ),
        "phase_aligned_negative_fraction": float(
            np.mean(phase_aligned_real < 0.0)
        ),
        "center_value_real": float(real[(GRID_COUNT - 1) // 2]),
        "endpoint_value_real": float(real[0]),
        "direct_vs_recentered_max_abs_delta": crosscheck,
        "coefficient_norm": float(metadata["coefficient_norm"]),
    }
    rows = [
        {
            "m": m,
            "N": n_bound,
            "index": index,
            "t": float(t_value),
            "real_q": float(value.real),
            "imag_q": float(value.imag),
        }
        for index, (t_value, value) in enumerate(zip(t, density))
    ]
    return summary, rows


def write_csv(rows: list[dict[str, Any]]) -> None:
    fields = ["m", "N", "index", "t", "real_q", "imag_q"]
    with RESULT_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def write_markdown(result: dict[str, Any]) -> None:
    lines = [
        "# CENTERED_DENSITY_POSITIVITY_PROBE",
        "",
        "Float64/complex128; exact `centeredTrialDensity` finite sum; "
        "4001 equally spaced points including both window endpoints.",
        "",
        "| (m,N) | min Re q | max Re q | min/max | max |Im q| | "
        "Re q < 0 count | fraction |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for item in result["cells"]:
        lines.append(
            f"| ({item['m']},{item['N']}) | "
            f"{item['min_real_q']:.12g} | "
            f"{item['max_real_q']:.12g} | "
            f"{item['min_real_over_max_real']:.12g} | "
            f"{item['max_abs_imag_q']:.12g} | "
            f"{item['negative_count']} | "
            f"{item['negative_fraction']:.12g} |"
        )
    lines.extend(
        [
            "",
            "| (m,N) | Re c0 | phase sign | aligned min/max | "
            "aligned negative fraction |",
            "|---|---:|---:|---:|---:|",
        ]
    )
    for item in result["cells"]:
        lines.append(
            f"| ({item['m']},{item['N']}) | "
            f"{item['central_coefficient_real']:.12g} | "
            f"{item['phase_sign_from_c0']:.0f} | "
            f"{item['phase_aligned_min_over_max']:.12g} | "
            f"{item['phase_aligned_negative_fraction']:.12g} |"
        )
    lines.extend(
        [
            "",
            "| (m,N) | direct/recentered max abs delta | "
            "coefficient norm |",
            "|---|---:|---:|",
        ]
    )
    for item in result["cells"]:
        lines.append(
            f"| ({item['m']},{item['N']}) | "
            f"{item['direct_vs_recentered_max_abs_delta']:.12g} | "
            f"{item['coefficient_norm']:.12g} |"
        )
    RESULT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    summaries: list[dict[str, Any]] = []
    profile_rows: list[dict[str, Any]] = []
    for m, n_bound in CELLS:
        summary, rows = evaluate_cell(m, n_bound)
        summaries.append(summary)
        profile_rows.extend(rows)
        print(
            f"({m},{n_bound}) "
            f"min_Re={summary['min_real_q']:.12g} "
            f"max_abs_Im={summary['max_abs_imag_q']:.12g} "
            f"negative_fraction={summary['negative_fraction']:.12g}",
            flush=True,
        )
    result = {
        "schema": "CENTERED_DENSITY_POSITIVITY_PROBE_V1",
        "numeric_type": "float64/complex128",
        "grid_count": GRID_COUNT,
        "cells": summaries,
    }
    RESULT_JSON.write_text(
        json.dumps(json_safe(result), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv(profile_rows)
    write_markdown(result)
    print(f"WROTE {RESULT_JSON}")
    print(f"WROTE {RESULT_CSV}")
    print(f"WROTE {RESULT_MD}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
