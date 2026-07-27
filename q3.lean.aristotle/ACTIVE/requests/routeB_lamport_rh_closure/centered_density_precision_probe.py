#!/usr/bin/env python3
"""50-digit resummation of the worst phase-aligned density points."""

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
RESULT_JSON = REQUEST_DIR / "CENTERED_DENSITY_PRECISION_PROBE.json"
RESULT_CSV = REQUEST_DIR / "CENTERED_DENSITY_PRECISION_PROBE.csv"
RESULT_MD = REQUEST_DIR / "CENTERED_DENSITY_PRECISION_PROBE.md"

CELLS = ((53, 120), (257, 120))
GRID_COUNT = 4001
WORST_COUNT = 20
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


def mp_complex_from_binary64(value: complex) -> mp.mpc:
    return mp.mpc(mp.mpf(float(value.real)), mp.mpf(float(value.imag)))


def evaluate_mp(
    coeff_mp: list[mp.mpc], n_bound: int, index: int, m: int
) -> mp.mpc:
    x = mp.mpf(index) / mp.mpf(GRID_COUNT - 1)
    total = mp.mpc(0)
    for offset, n in enumerate(range(-n_bound, n_bound + 1)):
        total += coeff_mp[offset] * mp.exp(2j * mp.pi * n * x)
    return total / mp.sqrt(mp.log(m))


def cell(m: int, n_bound: int) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    coeff, _ = ratio.coefficients(m, n_bound)
    frequencies = np.arange(-n_bound, n_bound + 1, dtype=np.float64)
    x = np.arange(GRID_COUNT, dtype=np.float64) / (GRID_COUNT - 1)
    with np.errstate(all="ignore"):
        density = (
            np.exp(2j * math.pi * np.outer(x, frequencies))
            @ coeff
            / math.sqrt(math.log(m))
        )
    if not np.all(np.isfinite(density)):
        raise RuntimeError(f"NONFINITE_FLOAT_DENSITY:{m}:{n_bound}")
    phase_sign = 1.0 if coeff[n_bound].real >= 0 else -1.0
    aligned_float = phase_sign * density.real
    worst_indices = np.argsort(aligned_float)[:WORST_COUNT]

    mp.mp.dps = MP_DPS
    coeff_mp = [mp_complex_from_binary64(value) for value in coeff]

    rows: list[dict[str, Any]] = []
    worst_mp_value: mp.mpf | None = None
    for rank, index_np in enumerate(worst_indices, start=1):
        index = int(index_np)
        value_mp = phase_sign * evaluate_mp(
            coeff_mp, n_bound, index, m
        )
        real_mp = mp.re(value_mp)
        imag_mp = mp.im(value_mp)
        if worst_mp_value is None or real_mp < worst_mp_value:
            worst_mp_value = real_mp
        rows.append(
            {
                "m": m,
                "N": n_bound,
                "rank": rank,
                "grid_index": index,
                "x": mp.nstr(
                    mp.mpf(index) / mp.mpf(GRID_COUNT - 1), 52
                ),
                "t": mp.nstr(
                    mp.log(m)
                    * (
                        mp.mpf(index) / mp.mpf(GRID_COUNT - 1)
                        - mp.mpf("0.5")
                    ),
                    52,
                ),
                "aligned_float64": float(aligned_float[index]),
                "aligned_mp50_real": mp.nstr(real_mp, 52),
                "aligned_mp50_imag": mp.nstr(imag_mp, 52),
                "mp50_minus_float64": mp.nstr(
                    real_mp - mp.mpf(float(aligned_float[index])), 52
                ),
            }
        )

    center_mp = phase_sign * evaluate_mp(
        coeff_mp, n_bound, (GRID_COUNT - 1) // 2, m
    )
    assert worst_mp_value is not None
    return {
        "m": m,
        "N": n_bound,
        "phase_sign": phase_sign,
        "c0_real_binary64": float(coeff[n_bound].real),
        "worst_aligned_float64": float(np.min(aligned_float)),
        "worst_aligned_mp50": mp.nstr(worst_mp_value, 52),
        "center_aligned_mp50": mp.nstr(mp.re(center_mp), 52),
        "worst_over_center_mp50": mp.nstr(
            worst_mp_value / mp.re(center_mp), 52
        ),
        "max_abs_mp50_minus_float64_on_worst20": mp.nstr(
            max(abs(mp.mpf(row["mp50_minus_float64"])) for row in rows),
            52,
        ),
        "all_worst20_remain_negative_mp50":
            all(mp.mpf(row["aligned_mp50_real"]) < 0 for row in rows),
    }, rows


def write_csv(rows: list[dict[str, Any]]) -> None:
    fields = [
        "m",
        "N",
        "rank",
        "grid_index",
        "x",
        "t",
        "aligned_float64",
        "aligned_mp50_real",
        "aligned_mp50_imag",
        "mp50_minus_float64",
    ]
    with RESULT_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def write_markdown(result: dict[str, Any]) -> None:
    lines = [
        "# CENTERED_DENSITY_PRECISION_PROBE",
        "",
        "The coefficient row is constructed in binary64 and held fixed.  The "
        "finite Fourier sum at the selected grid points is then recomputed "
        "with `mpmath`, `mp.dps=50`.",
        "",
        "## Summary",
        "",
        "| (m,N) | worst aligned float64 | worst aligned mp50 | "
        "worst/center mp50 | max |mp50-float64| | all 20 negative |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for item in result["cells"]:
        lines.append(
            f"| ({item['m']},{item['N']}) | "
            f"{item['worst_aligned_float64']:.12g} | "
            f"{item['worst_aligned_mp50']} | "
            f"{item['worst_over_center_mp50']} | "
            f"{item['max_abs_mp50_minus_float64_on_worst20']} | "
            f"{item['all_worst20_remain_negative_mp50']} |"
        )
    lines.extend(
        [
            "",
            "## Worst 20 points per cell",
            "",
            "| (m,N) | rank | grid index | t | aligned float64 | "
            "aligned mp50 | mp50-float64 |",
            "|---|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for row in result["rows"]:
        lines.append(
            f"| ({row['m']},{row['N']}) | {row['rank']} | "
            f"{row['grid_index']} | {row['t']} | "
            f"{row['aligned_float64']:.12g} | "
            f"{row['aligned_mp50_real']} | "
            f"{row['mp50_minus_float64']} |"
        )
    RESULT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    summaries: list[dict[str, Any]] = []
    all_rows: list[dict[str, Any]] = []
    for m, n_bound in CELLS:
        summary, rows = cell(m, n_bound)
        summaries.append(summary)
        all_rows.extend(rows)
        print(
            f"({m},{n_bound}) "
            f"worst_mp50={summary['worst_aligned_mp50']} "
            f"all20negative={summary['all_worst20_remain_negative_mp50']}",
            flush=True,
        )
    magnitude_53 = abs(mp.mpf(summaries[0]["worst_aligned_mp50"]))
    magnitude_257 = abs(mp.mpf(summaries[1]["worst_aligned_mp50"]))
    two_point_beta = mp.log(magnitude_257 / magnitude_53) / mp.log(
        mp.mpf(257) / mp.mpf(53)
    )
    result = {
        "schema": "CENTERED_DENSITY_PRECISION_PROBE_V1",
        "scope": (
            "binary64 coefficient row held fixed; Fourier resummation "
            "at exact rational grid positions in mpmath"
        ),
        "mpmath_dps": MP_DPS,
        "grid_count": GRID_COUNT,
        "worst_count_per_cell": WORST_COUNT,
        "cells": summaries,
        "rows": all_rows,
        "two_point_abs_violation_beta_m53_to_m257":
            mp.nstr(two_point_beta, 52),
        "violation_magnitude_ratio_257_over_53":
            mp.nstr(magnitude_257 / magnitude_53, 52),
    }
    RESULT_JSON.write_text(
        json.dumps(json_safe(result), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv(all_rows)
    write_markdown(result)
    print(f"WROTE {RESULT_JSON}")
    print(f"WROTE {RESULT_CSV}")
    print(f"WROTE {RESULT_MD}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
