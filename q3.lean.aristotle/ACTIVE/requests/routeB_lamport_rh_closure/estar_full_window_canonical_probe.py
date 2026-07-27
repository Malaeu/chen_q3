#!/usr/bin/env python3
"""Goal 021: full-window E_star sign diagnostic for the canonical packet.

This repeats the 018 protocol with the Route-B raw-t packet locked by 020:

  htrial(lambda*t)
    = (J4*phi0(t) - J0*phi4(t))
      / (sqrt(lambda)*sqrt(J0^2*N4^2 + J4^2*N0^2)).

For every precision level, J, N, c and the packet are rebuilt from the same
endpoint-normalized raw ODE modes.  Every open tooth-band is sampled
separately and every tooth uses the primal star half-weight.

This is a numerical diagnostic, not a theorem.  It does not evaluate a
Fejer sum, a Poisson residual, or the external Fourier/G3 branch.  It does
not mutate STATE and does not create Bus 010.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import platform
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
from scipy import special

import dual_prolate_residual_probe as d19
import estar_full_window_sign_probe as e18
import prolate_coordinate_lock_probe as p20


REQUEST_DIR = Path(__file__).resolve().parent
GOAL = REQUEST_DIR / "021_estar_full_window_canonical.goal.md"
RESULT_JSON = REQUEST_DIR / "E_STAR_FULL_WINDOW_CANONICAL.json"
BAND_CSV = REQUEST_DIR / "E_STAR_FULL_WINDOW_CANONICAL_BANDS.csv"
TOOTH_CSV = REQUEST_DIR / "E_STAR_FULL_WINDOW_CANONICAL_TEETH.csv"
FINGERPRINT_CSV = REQUEST_DIR / "E_STAR_FULL_WINDOW_CANONICAL_FINGERPRINT.csv"
POSITIVE_CSV = (
    REQUEST_DIR
    / "E_STAR_FULL_WINDOW_CANONICAL_CANDIDATE_POSITIVE_RUNS.csv"
)

M_VALUES = (13, 53, 257)
LEVELS = e18.LEVELS
BAND_POINTS = e18.BAND_POINTS
NORM_GAUSS_ORDER = 4096
FINGERPRINT_TARGETS = (0.0, 0.25, 0.5, 0.75)


@dataclass
class RawModeData:
    column: int
    source_name: str
    phase: int
    log_J: float
    log_N: float
    centre_raw_sign: int
    centre_log_abs: float
    norm_nodes: np.ndarray
    norm_weights: np.ndarray
    norm_raw_signs: np.ndarray
    norm_raw_logs: np.ndarray


@dataclass
class PacketData:
    spectral: dict[str, Any]
    level: e18.PrecisionLevel
    mode0: RawModeData
    mode4: RawModeData
    denominator_log: float
    centre_sign: int
    centre_log_abs: float
    endpoint_sign: int
    endpoint_log_abs: float
    L2_norm: float
    integral: float
    integral_scale: float
    fingerprint: list[dict[str, Any]]


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


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def signed_log_difference_arrays(
    signs_a: np.ndarray,
    logs_a: np.ndarray,
    signs_b: np.ndarray,
    logs_b: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    largest = np.maximum(logs_a, logs_b)
    scaled = (
        signs_a.astype(np.float64) * np.exp(logs_a - largest)
        - signs_b.astype(np.float64) * np.exp(logs_b - largest)
    )
    signs = np.sign(scaled).astype(np.int8)
    logs = np.full(scaled.size, -math.inf, dtype=np.float64)
    nonzero = scaled != 0
    logs[nonzero] = largest[nonzero] + np.log(np.abs(scaled[nonzero]))
    return signs, logs


def signed_log_difference_scalar(
    sign_a: int,
    log_a: float,
    sign_b: int,
    log_b: float,
) -> tuple[int, float]:
    signs, logs = signed_log_difference_arrays(
        np.asarray([sign_a], dtype=np.int8),
        np.asarray([log_a], dtype=np.float64),
        np.asarray([sign_b], dtype=np.int8),
        np.asarray([log_b], dtype=np.float64),
    )
    return int(signs[0]), float(logs[0])


def signed_log_to_float(sign: int, log_abs: float) -> float:
    return e18.signed_log_to_float(sign, log_abs)


def build_raw_mode(
    spectral: dict[str, Any],
    column: int,
    source_name: str,
    level: e18.PrecisionLevel,
) -> RawModeData:
    nodes, raw_weights = special.roots_legendre(NORM_GAUSS_ORDER)
    positive_targets = (nodes + 1) / 2
    weights = raw_weights / 2
    targets = np.concatenate(([0.0], positive_targets))
    raw_signs, raw_logs, _, _ = p20.raw_signed_logs(
        spectral, column, targets, level
    )

    log_N = 0.5 * (
        math.log(2)
        + float(special.logsumexp(2 * raw_logs[1:], b=weights))
    )
    J_sign, half_log_J = d19.signed_log_weighted_sum(
        raw_signs[1:], raw_logs[1:], weights
    )
    if J_sign == 0:
        raise RuntimeError(
            f"CANONICAL_RAW_MODE_ZERO_INTEGRAL:"
            f"{spectral['m']}:{level.name}:{source_name}"
        )
    phase = int(J_sign)
    log_J = math.log(2) + float(half_log_J)
    centre_raw_sign = int(raw_signs[0])
    if phase * centre_raw_sign == 0:
        raise RuntimeError(
            f"CANONICAL_RAW_MODE_ZERO_CENTRE:"
            f"{spectral['m']}:{level.name}:{source_name}"
        )
    return RawModeData(
        column=column,
        source_name=source_name,
        phase=phase,
        log_J=log_J,
        log_N=log_N,
        centre_raw_sign=centre_raw_sign,
        centre_log_abs=float(raw_logs[0]),
        norm_nodes=positive_targets,
        norm_weights=weights,
        norm_raw_signs=raw_signs[1:],
        norm_raw_logs=raw_logs[1:],
    )


def packet_logs_from_raw(
    packet: PacketData,
    signs0: np.ndarray,
    logs0: np.ndarray,
    signs4: np.ndarray,
    logs4: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    term0_signs = packet.mode0.phase * signs0
    term4_signs = packet.mode4.phase * signs4
    term0_logs = logs0 + packet.mode4.log_J
    term4_logs = logs4 + packet.mode0.log_J
    signs, logs = signed_log_difference_arrays(
        term0_signs,
        term0_logs,
        term4_signs,
        term4_logs,
    )
    return signs, logs - packet.denominator_log


def packet_scalar_from_raw(
    packet: PacketData,
    sign0: int,
    log0: float,
    sign4: int,
    log4: float,
) -> tuple[int, float]:
    sign, log_abs = signed_log_difference_scalar(
        packet.mode0.phase * sign0,
        log0 + packet.mode4.log_J,
        packet.mode4.phase * sign4,
        log4 + packet.mode0.log_J,
    )
    return sign, log_abs - packet.denominator_log


def make_packet(
    m: int,
    level: e18.PrecisionLevel,
) -> PacketData:
    spectral = d19.canonical_spectral_full(m, level)
    lam = float(spectral["lambda"])
    mode0 = build_raw_mode(spectral, 0, "h0", level)
    mode4 = build_raw_mode(spectral, 2, "h4", level)
    denominator_log = (
        0.5 * math.log(lam)
        + 0.5
        * float(
            np.logaddexp(
                2 * mode0.log_J + 2 * mode4.log_N,
                2 * mode4.log_J + 2 * mode0.log_N,
            )
        )
    )

    provisional = PacketData(
        spectral=spectral,
        level=level,
        mode0=mode0,
        mode4=mode4,
        denominator_log=denominator_log,
        centre_sign=0,
        centre_log_abs=-math.inf,
        endpoint_sign=0,
        endpoint_log_abs=-math.inf,
        L2_norm=math.nan,
        integral=math.nan,
        integral_scale=math.nan,
        fingerprint=[],
    )
    centre_sign, centre_log = packet_scalar_from_raw(
        provisional,
        mode0.centre_raw_sign,
        mode0.centre_log_abs,
        mode4.centre_raw_sign,
        mode4.centre_log_abs,
    )
    endpoint_sign, endpoint_log = packet_scalar_from_raw(
        provisional,
        1,
        0.0,
        1,
        0.0,
    )

    signs, logs = packet_logs_from_raw(
        provisional,
        mode0.norm_raw_signs,
        mode0.norm_raw_logs,
        mode4.norm_raw_signs,
        mode4.norm_raw_logs,
    )
    values = np.zeros(signs.size, dtype=np.float64)
    representable = (
        (signs != 0)
        & (logs >= math.log(np.nextafter(0.0, 1.0)))
        & (logs <= math.log(np.finfo(np.float64).max))
    )
    values[representable] = (
        signs[representable].astype(np.float64)
        * np.exp(logs[representable])
    )
    L2_norm = math.sqrt(
        float(2 * lam * np.sum(mode0.norm_weights * values**2))
    )
    integral = float(2 * lam * np.sum(mode0.norm_weights * values))
    integral_scale = float(
        2 * lam * np.sum(mode0.norm_weights * np.abs(values))
    )

    packet = PacketData(
        spectral=spectral,
        level=level,
        mode0=mode0,
        mode4=mode4,
        denominator_log=denominator_log,
        centre_sign=centre_sign,
        centre_log_abs=centre_log,
        endpoint_sign=endpoint_sign,
        endpoint_log_abs=endpoint_log,
        L2_norm=L2_norm,
        integral=integral,
        integral_scale=integral_scale,
        fingerprint=[],
    )

    fingerprint_targets = np.asarray(
        [
            *FINGERPRINT_TARGETS,
            1.0 - level.endpoint_eps,
        ],
        dtype=np.float64,
    )
    raw0_signs, raw0_logs, _, _ = p20.raw_signed_logs(
        spectral, 0, fingerprint_targets, level
    )
    raw4_signs, raw4_logs, _, _ = p20.raw_signed_logs(
        spectral, 2, fingerprint_targets, level
    )
    fp_signs, fp_logs = packet_logs_from_raw(
        packet,
        raw0_signs,
        raw0_logs,
        raw4_signs,
        raw4_logs,
    )
    labels = ("0", "0.25", "0.5", "0.75", "1_minus_endpoint_eps")
    packet.fingerprint = [
        {
            "m": m,
            "level": level.name,
            "t_label": label,
            "t": repr(float(target)),
            "sign": int(sign),
            "log10_abs": repr(float(log_abs / math.log(10))),
            "value_float64": repr(
                signed_log_to_float(int(sign), float(log_abs))
            ),
        }
        for label, target, sign, log_abs in zip(
            labels,
            fingerprint_targets,
            fp_signs,
            fp_logs,
        )
    ]
    return packet


def evaluate_level(
    m: int,
    level: e18.PrecisionLevel,
    targets: np.ndarray,
    records: list[dict[str, Any]],
) -> dict[str, Any]:
    packet = make_packet(m, level)
    spectral = packet.spectral
    raw0_signs, raw0_logs, _, _ = p20.raw_signed_logs(
        spectral, 0, targets, level
    )
    raw4_signs, raw4_logs, _, _ = p20.raw_signed_logs(
        spectral, 2, targets, level
    )
    h_signs, h_logs = packet_logs_from_raw(
        packet,
        raw0_signs,
        raw0_logs,
        raw4_signs,
        raw4_logs,
    )

    band_samples: dict[int, list[dict[str, Any]]] = {}
    teeth: list[dict[str, Any]] = []
    for record in records:
        indices = np.asarray(record["indices"], dtype=np.int64)
        term_signs = h_signs[indices]
        term_logs = h_logs[indices]
        if record["kind"] == "tooth":
            term_signs = np.concatenate(
                [
                    term_signs,
                    np.asarray([packet.endpoint_sign], dtype=np.int8),
                ]
            )
            term_logs = np.concatenate(
                [
                    term_logs,
                    np.asarray(
                        [packet.endpoint_log_abs - math.log(2)],
                        dtype=np.float64,
                    ),
                ]
            )
        sign, log_abs = e18.signed_log_sum(term_signs, term_logs)
        log_abs += 0.5 * math.log(float(record["u"]))
        row = {
            "m": m,
            "level": level.name,
            "r": int(record["r"]),
            "point": int(record["point"]),
            "u": repr(float(record["u"])),
            "sign": sign,
            "log10_abs": repr(log_abs / math.log(10)),
            "value_float64": repr(
                signed_log_to_float(sign, log_abs)
            ),
        }
        if record["kind"] == "band":
            band_samples.setdefault(int(record["r"]), []).append(row)
        else:
            teeth.append(row)

    bands: list[dict[str, Any]] = []
    for r, samples in sorted(band_samples.items()):
        signs = np.asarray(
            [int(row["sign"]) for row in samples], dtype=np.int8
        )
        logs = np.asarray(
            [float(row["log10_abs"]) for row in samples],
            dtype=np.float64,
        )
        positive = np.flatnonzero(signs > 0)
        bands.append(
            {
                "m": m,
                "level": level.name,
                "r": r,
                "u_left": repr(math.sqrt(m) / (r + 1)),
                "u_right": repr(math.sqrt(m) / r),
                "positive_points": int(positive.size),
                "negative_points": int(np.count_nonzero(signs < 0)),
                "zero_points": int(np.count_nonzero(signs == 0)),
                "max_positive_log10": (
                    repr(float(np.max(logs[positive])))
                    if positive.size
                    else ""
                ),
                "max_abs_log10": repr(float(np.max(logs))),
                "min_abs_log10": repr(float(np.min(logs))),
                "samples": samples,
            }
        )

    lower_tooth = teeth[-1]
    lam = math.sqrt(m)
    h_center = signed_log_to_float(
        packet.centre_sign, packet.centre_log_abs
    )
    E_lower = float(lower_tooth["value_float64"])
    counterterm = -h_center / (2 * math.sqrt(lam))
    sqrt_lambda_times_trap = E_lower - counterterm
    trap_error = sqrt_lambda_times_trap / math.sqrt(lam)
    reconstructed = sqrt_lambda_times_trap + counterterm

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
            "normalization_Gauss_order": NORM_GAUSS_ORDER,
        },
        "packet": {
            "formula": (
                "(J4*phi0-J0*phi4)/"
                "(sqrt(lambda)*sqrt(J0^2*N4^2+J4^2*N0^2))"
            ),
            "mode0_phase": packet.mode0.phase,
            "mode4_phase": packet.mode4.phase,
            "mode0_log10_J": (
                packet.mode0.log_J / math.log(10)
            ),
            "mode4_log10_J": (
                packet.mode4.log_J / math.log(10)
            ),
            "mode0_log10_N": (
                packet.mode0.log_N / math.log(10)
            ),
            "mode4_log10_N": (
                packet.mode4.log_N / math.log(10)
            ),
            "L2_norm": packet.L2_norm,
            "integral": packet.integral,
            "integral_scale": packet.integral_scale,
            "fingerprint": packet.fingerprint,
        },
        "htrial_zero": {
            "sign": packet.centre_sign,
            "log10_abs": packet.centre_log_abs / math.log(10),
            "value_float64": h_center,
        },
        "htrial_endpoint": {
            "sign": packet.endpoint_sign,
            "log10_abs": packet.endpoint_log_abs / math.log(10),
            "value_float64": signed_log_to_float(
                packet.endpoint_sign,
                packet.endpoint_log_abs,
            ),
        },
        "bands": bands,
        "teeth": teeth,
        "lower_endpoint_trapezoid": {
            "u": 1 / lam,
            "E_star": E_lower,
            "sqrt_lambda_times_trap_error": (
                sqrt_lambda_times_trap
            ),
            "trap_error": trap_error,
            "origin_counterterm": counterterm,
            "reconstructed_E_star": reconstructed,
            "absolute_reconstruction_residual": abs(
                reconstructed - E_lower
            ),
        },
    }


def same_sign_positive_run(
    level_results: list[dict[str, Any]],
    r: int,
) -> dict[str, Any] | None:
    samples_by_level = [
        result["bands"][r - 1]["samples"]
        for result in level_results
    ]
    signs = np.asarray(
        [
            [int(row["sign"]) for row in samples]
            for samples in samples_by_level
        ],
        dtype=np.int8,
    )
    logs = np.asarray(
        [
            [float(row["log10_abs"]) for row in samples]
            for samples in samples_by_level
        ],
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
    left = int(run[0])
    right = int(run[-1])
    return {
        "r": r,
        "u_left_sample": samples_by_level[0][left]["u"],
        "u_right_sample": samples_by_level[0][right]["u"],
        "sample_count": int(run.size),
        "min_log10_margin": float(np.min(logs[:, run])),
        "max_log10_value": float(np.max(logs[:, run])),
    }


def summarize_m(
    m: int,
    level_results: list[dict[str, Any]],
) -> dict[str, Any]:
    candidate_positive_runs = [
        interval
        for r in range(1, m)
        if (
            interval := same_sign_positive_run(
                level_results, r
            )
        )
        is not None
    ]
    band_signs = np.asarray(
        [
            [
                int(sample["sign"])
                for band in result["bands"]
                for sample in band["samples"]
            ]
            for result in level_results
        ],
        dtype=np.int8,
    )
    tooth_signs = np.asarray(
        [
            [int(row["sign"]) for row in result["teeth"]]
            for result in level_results
        ],
        dtype=np.int8,
    )
    band_logs = np.asarray(
        [
            [
                float(sample["log10_abs"])
                for band in result["bands"]
                for sample in band["samples"]
            ]
            for result in level_results
        ],
        dtype=np.float64,
    )
    tooth_logs = np.asarray(
        [
            [float(row["log10_abs"]) for row in result["teeth"]]
            for result in level_results
        ],
        dtype=np.float64,
    )
    cross_level_disagreement = bool(
        np.any(band_signs != band_signs[0])
        or np.any(tooth_signs != tooth_signs[0])
    )
    any_zero = bool(
        np.any(band_signs == 0) or np.any(tooth_signs == 0)
    )
    any_positive_sample = bool(
        np.any(band_signs > 0) or np.any(tooth_signs > 0)
    )
    band_disagreement_count = int(
        np.count_nonzero(np.any(band_signs != band_signs[0], axis=0))
    )
    tooth_disagreement_count = int(
        np.count_nonzero(
            np.any(tooth_signs != tooth_signs[0], axis=0)
        )
    )
    band_drift = np.abs(band_logs[0] - band_logs[-1])
    tooth_drift = np.abs(tooth_logs[0] - tooth_logs[-1])
    finite_band_drift = band_drift[np.isfinite(band_drift)]
    finite_tooth_drift = tooth_drift[np.isfinite(tooth_drift)]
    local_instrument_unresolved = (
        any_zero
        or cross_level_disagreement
        or (
            any_positive_sample
            and not candidate_positive_runs
        )
    )
    return {
        "m": m,
        "lambda": math.sqrt(m),
        "band_count": m - 1,
        "band_points_per_level": BAND_POINTS,
        "band_samples_per_level": (m - 1) * BAND_POINTS,
        "tooth_count_per_level": m,
        "candidate_same_sign_positive_run_count": len(
            candidate_positive_runs
        ),
        "candidate_same_sign_positive_runs": candidate_positive_runs,
        "instrument_certified_positive_interval_count": (
            0
            if local_instrument_unresolved
            else len(candidate_positive_runs)
        ),
        "any_positive_sample": any_positive_sample,
        "any_zero": any_zero,
        "band_zero_count": int(np.count_nonzero(band_signs == 0)),
        "tooth_zero_count": int(np.count_nonzero(tooth_signs == 0)),
        "cross_level_sign_disagreement": (
            cross_level_disagreement
        ),
        "band_cross_level_disagreement_count": (
            band_disagreement_count
        ),
        "tooth_cross_level_disagreement_count": (
            tooth_disagreement_count
        ),
        "max_finite_band_P1_P3_log10_drift": (
            float(np.max(finite_band_drift))
            if finite_band_drift.size
            else None
        ),
        "max_finite_tooth_P1_P3_log10_drift": (
            float(np.max(finite_tooth_drift))
            if finite_tooth_drift.size
            else None
        ),
        "htrial_zero_by_level": [
            {
                "level": result["level"],
                **result["htrial_zero"],
            }
            for result in level_results
        ],
        "lower_endpoint_by_level": [
            {
                "level": result["level"],
                **result["lower_endpoint_trapezoid"],
            }
            for result in level_results
        ],
        "packet_checks_by_level": [
            {
                "level": result["level"],
                "L2_norm": result["packet"]["L2_norm"],
                "integral": result["packet"]["integral"],
                "integral_scale": result["packet"][
                    "integral_scale"
                ],
            }
            for result in level_results
        ],
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise RuntimeError(f"EMPTY_OUTPUT:{path}")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(rows[0]),
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(rows)


def run() -> dict[str, Any]:
    all_results: dict[int, list[dict[str, Any]]] = {}
    band_rows: list[dict[str, Any]] = []
    tooth_rows: list[dict[str, Any]] = []
    fingerprint_rows: list[dict[str, Any]] = []

    for m in M_VALUES:
        targets, records = e18.make_evaluation_plan(m)
        level_results = []
        for level in LEVELS:
            print(
                f"[021_CANONICAL_ESTAR] m={m} level={level.name} "
                f"unique_targets={targets.size}",
                flush=True,
            )
            result = evaluate_level(m, level, targets, records)
            level_results.append(result)
            fingerprint_rows.extend(result["packet"]["fingerprint"])
            for band in result["bands"]:
                band_rows.append(
                    {
                        key: value
                        for key, value in band.items()
                        if key != "samples"
                    }
                )
            tooth_rows.extend(result["teeth"])
        all_results[m] = level_results

    summaries = [
        summarize_m(m, all_results[m])
        for m in M_VALUES
    ]
    positive_rows = [
        {"m": summary["m"], **interval}
        for summary in summaries
        for interval in summary[
            "candidate_same_sign_positive_runs"
        ]
    ]
    any_positive_interval = any(
        summary["candidate_same_sign_positive_run_count"] > 0
        for summary in summaries
    )
    any_unresolved = any(
        summary["any_zero"]
        or summary["cross_level_sign_disagreement"]
        or (
            summary["any_positive_sample"]
            and summary["candidate_same_sign_positive_run_count"] == 0
        )
        for summary in summaries
    )
    # A positive run is route-killing only after the three-level instrument
    # check is green.  The canonical packet is a cancellation object, so a
    # cross-level sign disagreement or an exact float64 zero preempts any
    # apparent same-sign run elsewhere.
    if any_unresolved:
        verdict = "INSTRUMENT_FLOOR_UNRESOLVED"
    elif any_positive_interval:
        verdict = "ESTAR_PHASE_SIGN_KILLED_CANONICAL"
    else:
        verdict = "ESTAR_FULL_WINDOW_CANONICAL_SINGLE_SIGN"

    payload = {
        "verdict": verdict,
        "epistemic_status": (
            "NUMERICAL_GRID_DIAGNOSTIC_NOT_A_THEOREM_NOT_RH"
        ),
        "source": {
            "goal": str(GOAL),
            "goal_sha256": sha256(GOAL),
            "canonical_lock_020": str(
                REQUEST_DIR / "020_prolate_coordinate_lock.answer.md"
            ),
        },
        "object": {
            "name": "canonical Route-B raw-t packet",
            "formula": (
                "(J4*phi0-J0*phi4)/"
                "(sqrt(lambda)*sqrt(J0^2*N4^2+J4^2*N0^2))"
            ),
            "phase_rule": "each raw mode phased so J_j>0",
            "route_A_B_020_lock": "approximately 1e-16",
        },
        "protocol": {
            "m_values": M_VALUES,
            "total_bands_per_level": sum(m - 1 for m in M_VALUES),
            "total_band_rows": sum(m - 1 for m in M_VALUES)
            * len(LEVELS),
            "total_teeth_per_level": sum(M_VALUES),
            "total_tooth_rows": sum(M_VALUES) * len(LEVELS),
            "band_points": BAND_POINTS,
            "star_rule": (
                "at u=lambda/r the support-endpoint h(lambda) "
                "has weight 1/2"
            ),
            "precision_levels": [
                level.__dict__ for level in LEVELS
            ],
            "signed_log": True,
        },
        "guards": {
            "coefficients_or_phase_changed": False,
            "Fejer_evaluated": False,
            "residual_evaluated": False,
            "external_G3_evaluated": False,
            "STATE_mutated": False,
            "Bus_010_created": False,
        },
        "summaries": summaries,
        "results": {
            str(m): all_results[m] for m in M_VALUES
        },
        "environment": {
            "python": platform.python_version(),
            "numpy": np.__version__,
        },
    }

    write_csv(BAND_CSV, band_rows)
    write_csv(TOOTH_CSV, tooth_rows)
    write_csv(FINGERPRINT_CSV, fingerprint_rows)
    write_csv(POSITIVE_CSV, positive_rows)
    RESULT_JSON.write_text(
        json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            json_safe(
                {
                    "verdict": verdict,
                    "summaries": summaries,
                    "row_counts": {
                        "bands": len(band_rows),
                        "teeth": len(tooth_rows),
                        "fingerprint": len(fingerprint_rows),
                        "candidate_positive_runs": len(positive_rows),
                    },
                }
            ),
            indent=2,
            sort_keys=True,
        )
    )
    return payload


if __name__ == "__main__":
    run()
