#!/usr/bin/env python3
"""Float64 PhaseStructureProbe for the SOFT_2 centrally anchored bare transform."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
LADDER = HERE.parent / "routeB_twolevel_spectral_ladder"
OUT = LADDER / "out"
ZERO_SOURCE = OUT / "anchor_locked_zeros_first_200.json"
RESULT = HERE / "PHASE_STRUCTURE_PROBE.json"
CSV_RESULT = HERE / "PHASE_STRUCTURE_PROBE.csv"
REPORT = HERE / "PHASE_STRUCTURE_PROBE.md"
STATE = HERE / "STATE.json"

CELLS = ((13, 120), (14, 120), (53, 120), (101, 120))
GRID_COUNT = 2**12
XI_ZERO_FLOAT64 = 0.4971207781883142
RIGID_SD = 0.05
FREE_SD = 0.3
# "Systematic drift" was qualitative in the fork.  Before this run it is
# operationalized at the same 0.3-radian phase-free scale, with R^2>=0.9.
DRIFT_EXCURSION = 0.3
DRIFT_R2 = 0.9
ZERO_DILATION = 1


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return str(path.relative_to(REPO))


def coefficient_path(m: int, n_bound: int) -> Path:
    if m in (53, 101):
        return OUT / f"off_axis_k1_coeffs_lambda_sq_{m}_N_{n_bound}_float64.json"
    return OUT / f"portable_k_coeffs_lambda_sq_{m}_N_{n_bound}.json"


def load_coefficients(m: int, n_bound: int) -> tuple[np.ndarray, Path]:
    path = coefficient_path(m, n_bound)
    payload = json.loads(path.read_text(encoding="utf-8"))
    coeffs = np.asarray(
        [complex(float(row["re"]), float(row["im"])) for row in payload["coefficients"]],
        dtype=np.complex128,
    )
    if coeffs.size != 2 * n_bound + 1:
        raise RuntimeError(f"PHASE_COEFFICIENT_COUNT:{m}:{n_bound}")
    return coeffs, path


def stable_integral(alpha: np.ndarray, length: float) -> np.ndarray:
    w = 1j * alpha * length
    out = np.empty_like(w, dtype=np.complex128)
    small = np.abs(w) < 1e-10
    ws = w[small]
    out[small] = length * (1 + ws / 2 + ws**2 / 6 + ws**3 / 24)
    out[~small] = length * np.expm1(w[~small]) / w[~small]
    return out


def bare_transform(coeffs: np.ndarray, m: int, n_bound: int, x: np.ndarray) -> np.ndarray:
    length = math.log(m)
    frequencies = 2 * math.pi * np.arange(-n_bound, n_bound + 1) / length
    result = np.empty(x.size, dtype=np.complex128)
    for start in range(0, x.size, 512):
        block = x[start : start + 512]
        integrals = stable_integral(block[:, None] + frequencies[None, :], length)
        result[start : start + block.size] = (integrals @ coeffs) / math.sqrt(length)
    return result


def dilated_zero_mask(abs_b: np.ndarray) -> tuple[np.ndarray, float, int]:
    threshold = 10 * np.finfo(np.float64).eps * float(np.max(abs_b))
    raw = abs_b <= threshold
    mask = raw.copy()
    for shift in range(1, ZERO_DILATION + 1):
        mask[shift:] |= raw[:-shift]
        mask[:-shift] |= raw[shift:]
    return mask, threshold, int(np.count_nonzero(raw))


def axial_statistics(theta: np.ndarray) -> dict[str, float]:
    doubled = np.exp(2j * theta)
    mean_vector = np.mean(doubled)
    mean_phase = 0.5 * np.angle(mean_vector)
    residual = 0.5 * np.angle(np.exp(2j * (theta - mean_phase)))
    return {
        "mean_phase_mod_pi": float(mean_phase),
        "sd_theta_mod_pi": float(np.sqrt(np.mean(residual**2))),
        "axial_resultant": float(abs(mean_vector)),
        "residual_max_abs": float(np.max(np.abs(residual))),
    }


def contiguous_segments(keep: np.ndarray) -> list[np.ndarray]:
    indices = np.flatnonzero(keep)
    if indices.size == 0:
        return []
    cuts = np.where(np.diff(indices) > 1)[0] + 1
    return [part for part in np.split(indices, cuts) if part.size >= 3]


def drift_statistics(x: np.ndarray, theta: np.ndarray, keep: np.ndarray) -> dict[str, Any]:
    rows: list[dict[str, float]] = []
    for segment in contiguous_segments(keep):
        xs = x[segment]
        ys = np.unwrap(2 * theta[segment]) / 2
        slope, intercept = np.polyfit(xs, ys, 1)
        fitted = slope * xs + intercept
        ss_res = float(np.sum((ys - fitted) ** 2))
        ss_tot = float(np.sum((ys - np.mean(ys)) ** 2))
        r2 = 1.0 if ss_tot == 0 and ss_res == 0 else (0.0 if ss_tot == 0 else 1 - ss_res / ss_tot)
        excursion = float(abs(slope) * (xs[-1] - xs[0]))
        rows.append({
            "point_count": int(segment.size),
            "x_min": float(xs[0]),
            "x_max": float(xs[-1]),
            "slope_rad_per_x": float(slope),
            "fitted_excursion_rad": excursion,
            "r2": r2,
        })
    if not rows:
        return {"segments": [], "systematic": False, "max_fitted_excursion_rad": math.nan}
    strongest = max(rows, key=lambda row: row["fitted_excursion_rad"] if row["r2"] >= DRIFT_R2 else -1)
    systematic = any(row["r2"] >= DRIFT_R2 and row["fitted_excursion_rad"] >= DRIFT_EXCURSION for row in rows)
    return {
        "segments": rows,
        "systematic": systematic,
        "strongest_segment": strongest,
        "max_fitted_excursion_rad": max(row["fitted_excursion_rad"] for row in rows),
    }


def classify(sd: float, systematic: bool) -> str:
    if sd < RIGID_SD and not systematic:
        return "C2_PHASE_RIGID"
    if sd >= FREE_SD or systematic:
        return "C2_PHASE_FREE"
    return "EXTEND"


def run_probe() -> dict[str, Any]:
    state = json.loads(STATE.read_text(encoding="utf-8"))
    node = state["nodes"]["D0.7e.5a"]
    if node["proof_status"] != "BLOCKED" or node["activity"] != "ACTIVE":
        raise RuntimeError("SOFT_2_5A_STATE_DRIFT")
    if list((LADDER / "bus").glob("010_*")):
        raise RuntimeError("SOFT_2_BUS_010_PRESENT")

    zeros = json.loads(ZERO_SOURCE.read_text(encoding="utf-8"))["zeros"]
    gamma_1 = float(zeros[0]["gamma"])
    gamma_11 = float(zeros[10]["gamma"])
    x = np.linspace(gamma_1, gamma_11, GRID_COUNT, dtype=np.float64)

    rows: list[dict[str, Any]] = []
    for m, n_bound in CELLS:
        coeffs, source = load_coefficients(m, n_bound)
        b = bare_transform(coeffs, m, n_bound, x)
        b0 = bare_transform(coeffs, m, n_bound, np.asarray([0.0]))[0]
        if abs(b0) == 0:
            raise RuntimeError(f"SOFT_2_B_ZERO:{m}:{n_bound}")
        h = XI_ZERO_FLOAT64 * b / b0
        abs_b = np.abs(b)
        zero_mask, floor, raw_excluded = dilated_zero_mask(abs_b)
        keep = ~zero_mask
        if np.count_nonzero(keep) < 3:
            raise RuntimeError(f"SOFT_2_TOO_FEW_PHASE_POINTS:{m}:{n_bound}")
        theta = np.angle(h)
        axial = axial_statistics(theta[keep])
        drift = drift_statistics(x, theta, keep)
        verdict = classify(axial["sd_theta_mod_pi"], drift["systematic"])
        symmetry_error = float(np.max(np.abs(coeffs - np.conjugate(coeffs[::-1]))))
        inversion_symmetry_error = float(np.max(np.abs(coeffs - coeffs[::-1])))
        max_imaginary_coefficient = float(np.max(np.abs(coeffs.imag)))
        strongest = drift.get("strongest_segment")
        expected_half_shift_slope = 0.5 * math.log(m)
        slope_minus_log_lambda = (
            float(strongest["slope_rad_per_x"] - expected_half_shift_slope) if strongest else math.nan
        )
        rows.append({
            "lambda_sq": m,
            "N": n_bound,
            "source": rel(source),
            "source_sha256": sha256(source),
            "B_zero": {"re": float(b0.real), "im": float(b0.imag), "abs": float(abs(b0))},
            "H_zero_float64": {"re": float((XI_ZERO_FLOAT64 * b0 / b0).real), "im": float((XI_ZERO_FLOAT64 * b0 / b0).imag)},
            "conjugate_coefficient_symmetry_max_abs_error": symmetry_error,
            "inversion_coefficient_symmetry_diagnostic_max_abs_error": inversion_symmetry_error,
            "max_abs_imaginary_coefficient_diagnostic": max_imaginary_coefficient,
            "expected_half_shift_slope_L_over_2_equals_log_lambda": expected_half_shift_slope,
            "phase_slope_minus_log_lambda_diagnostic": slope_minus_log_lambda,
            "zero_exclusion": {
                "definition": "abs(B)<=10*eps64*max_grid_abs_B, dilated by one grid neighbor",
                "threshold": floor,
                "raw_point_count": raw_excluded,
                "dilated_point_count": int(np.count_nonzero(zero_mask)),
                "kept_point_count": int(np.count_nonzero(keep)),
            },
            "phase": axial,
            "drift": drift,
            "verdict": verdict,
        })

    verdicts = [row["verdict"] for row in rows]
    overall = "C2_PHASE_FREE" if "C2_PHASE_FREE" in verdicts else (
        "C2_PHASE_RIGID" if all(code == "C2_PHASE_RIGID" for code in verdicts) else "EXTEND"
    )
    return {
        "schema": "route_b_soft_2_phase_structure_probe_v1",
        "status": "COMPLETED_FLOAT64_DIAGNOSTIC_NOT_THEOREM",
        "object": {
            "formula": "H_(m,N)(x)=Xi(0)*B_(m,N)(x)/B_(m,N)(0)",
            "B_formula": "L^(-1/2)*sum_n c_n*integral_0^L exp(i*(x+2*pi*n/L)*t)dt",
            "completion_factor_removed": True,
        },
        "window": {
            "definition": "[gamma_1,gamma_11]",
            "gamma_1": gamma_1,
            "gamma_11": gamma_11,
            "grid_count": GRID_COUNT,
            "zero_source": rel(ZERO_SOURCE),
            "zero_source_sha256": sha256(ZERO_SOURCE),
        },
        "arithmetic": {"dtype": "float64/complex128", "dps_escalation": False},
        "registered_judges": {
            "rigid": "sd(theta mod pi)<0.05 and no systematic drift",
            "free": "sd(theta mod pi)>=0.3 or systematic drift",
            "between": "EXTEND",
            "systematic_drift_operationalization": "fitted phase excursion>=0.3 rad and R^2>=0.9 on a contiguous kept segment",
        },
        "cells": rows,
        "verdict_code": overall,
        "phase_slope_diagnostic": {
            "code": "PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC",
            "expected_slope": "L/2=log(lambda)=0.5*log(lambda_sq)",
            "meaning": "half-shift signature and completion-gauge consistency",
            "use": "diagnostic input for the V1 parity-closure question",
            "status": "DIAGNOSTIC_NOT_PARITY_THEOREM_NOT_RH",
            "preserves_verdict": "C2_PHASE_FREE",
        },
        "interpretation": "NUMERICAL_FALSIFIER_FOR_C2_AS_STATED_NOT_A_SYMMETRY_THEOREM_NOT_RH",
        "rh_status": "NOT_RH",
    }


def csv_text(result: dict[str, Any]) -> str:
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["lambda_sq", "N", "sd_theta_mod_pi", "mean_phase_mod_pi", "axial_resultant", "systematic_drift", "slope_rad_per_x", "slope_minus_log_lambda", "fitted_excursion_rad", "r2", "excluded", "verdict"])
    for row in result["cells"]:
        strongest = row["drift"].get("strongest_segment", {})
        writer.writerow([
            row["lambda_sq"], row["N"], row["phase"]["sd_theta_mod_pi"], row["phase"]["mean_phase_mod_pi"],
            row["phase"]["axial_resultant"], row["drift"]["systematic"], strongest.get("slope_rad_per_x"),
            row["phase_slope_minus_log_lambda_diagnostic"], strongest.get("fitted_excursion_rad"), strongest.get("r2"), row["zero_exclusion"]["dilated_point_count"], row["verdict"],
        ])
    return buf.getvalue()


def report_text(result: dict[str, Any]) -> str:
    lines = [
        "# SOFT_2 PhaseStructureProbe",
        "",
        "Status: `FLOAT64_DIAGNOSTIC / NOT_THEOREM / NOT_RH`",
        "",
        "The object is `H=Xi(0)B/B(0)` with the completion gauge removed.",
        "The axial phase statistic is branch-safe modulo pi.  Sampled zero-floor",
        "points and one neighboring grid point on each side are excluded.",
        "The registered `PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC` compares the",
        "fitted slope with `L/2=log(lambda)`.  Agreement is a half-shift signature",
        "and a completion-gauge consistency check only.  It is diagnostic input",
        "for the V1 parity-closure question, not a parity theorem and not RH.",
        "",
        "| (m,N) | sd(theta mod pi) | mean mod pi | axial R | drift slope | slope-log(lambda) | excursion | R2 | excluded | code |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---|",
    ]
    for row in result["cells"]:
        s = row["drift"]["strongest_segment"]
        lines.append(
            f"| ({row['lambda_sq']},{row['N']}) | {row['phase']['sd_theta_mod_pi']:.12g} | "
            f"{row['phase']['mean_phase_mod_pi']:.12g} | {row['phase']['axial_resultant']:.12g} | "
            f"{s['slope_rad_per_x']:.12g} | {row['phase_slope_minus_log_lambda_diagnostic']:.12g} | "
            f"{s['fitted_excursion_rad']:.12g} | {s['r2']:.12g} | "
            f"{row['zero_exclusion']['dilated_point_count']} | `{row['verdict']}` |"
        )
    lines += [
        "",
        f"Verdict: `{result['verdict_code']}`.",
        "Diagnostic: `PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC`.",
        "The diagnostic preserves `C2_PHASE_FREE`.",
        "",
        "This probes C2 as stated. It is not proof of a packet symmetry, S2, or RH.",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = run_probe()
    if args.write:
        csv_payload = csv_text(result)
        report_payload = report_text(result)
        CSV_RESULT.write_text(csv_payload, encoding="utf-8")
        REPORT.write_text(report_payload, encoding="utf-8")
        result["raw_csv"] = {"path": rel(CSV_RESULT), "sha256": sha256(CSV_RESULT)}
        result["report"] = {"path": rel(REPORT), "sha256": sha256(REPORT)}
        RESULT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
