#!/usr/bin/env python3
"""Goal 020: same-mode t-to-x normalization and Fourier K1 diagnostic.

The raw modes are the endpoint-normalized Frobenius/ODE modes used by the
013/018 constructor before its centre-value rescaling.  Every quantity
N, J, c and every Fourier integral is rebuilt from that same raw mode.
The old 019 multipliers are never repaired or divided by a guessed power.

This is a report-only numerical object lock.  It does not evaluate a Fejer
sum, does not form a Poisson residual, does not mutate STATE, and does not
create Bus 010.
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
from scipy import integrate, special

import dual_prolate_residual_probe as d19
import estar_full_window_sign_probe as e18


REQUEST_DIR = Path(__file__).resolve().parent
GOAL = REQUEST_DIR / "020_prolate_coordinate_lock.goal.md"
SAVED_019 = REQUEST_DIR / "DUAL_MU_FACTORS.csv"

MODE_CSV = REQUEST_DIR / "PROLATE_SAME_MODE_LOCK.csv"
PACKET_CSV = REQUEST_DIR / "PROLATE_PACKET_CROSSCHECK.csv"
FOURIER_CSV = REQUEST_DIR / "PROLATE_FOURIER_K1.csv"
RESULT_JSON = REQUEST_DIR / "PROLATE_COORDINATE_LOCK_DIAGNOSTIC.json"

M_VALUES = (13, 53, 257)
MODE_MAP = ((0, "h0", 0), (2, "h4", 4))
LEVEL = e18.LEVELS[-1]
NORM_GAUSS_ORDER = 4096
GAUSS_PANEL_ORDER = 16
FOURIER_PANELS_FACTOR = 20
ARITHMETIC_FLOOR = 1e-13
SCALE_RTOL = 2e-9
MU_RTOL = 2e-9
ORTHOGONALITY_ATOL = 2e-9
PACKET_RTOL = 2e-9
FOURIER_ATOL = 2e-11
FOURIER_RTOL = 2e-8


@dataclass
class RawMode:
    m: int
    column: int
    source_name: str
    j_label: int
    phase: int
    raw_c_sign_after_phase: int
    log_raw_c_abs: float
    log_raw_J_abs: float
    log_raw_N: float
    log_scale_l2: float
    log_scale_integral: float
    log_scale_center: float
    scale_l2: float
    scale_integral: float
    scale_center: float
    I_x: float
    h_x_zero: float
    saved_I: float
    saved_h_zero: float
    mu_from_t: float
    mu_from_x: float
    mu_from_saved: float
    scale_relative_spread: float
    mu_relative_spread: float
    quadrature_nodes: np.ndarray
    quadrature_weights: np.ndarray
    psi_values: np.ndarray
    h_x_values: np.ndarray
    constructor_values: np.ndarray


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


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_saved_019_centres() -> dict[tuple[int, str], tuple[float, float]]:
    output: dict[tuple[int, str], tuple[float, float]] = {}
    with SAVED_019.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            output[(int(row["m"]), row["mode"])] = (
                float(row["stored_I"]),
                float(row["stable_L2_h_at_zero_diagnostic"]),
            )
    return output


def relative_spread_from_logs(logs: list[float]) -> float:
    return max(
        abs(math.expm1(left - right))
        for left in logs
        for right in logs
    )


def safe_exp(log_value: float) -> float:
    if log_value < math.log(np.nextafter(0.0, 1.0)):
        return 0.0
    return math.exp(log_value)


def raw_signed_logs(
    spectral: dict[str, Any],
    column: int,
    targets: np.ndarray,
    level: e18.PrecisionLevel = LEVEL,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Return the raw endpoint-normalized mode and the old 018 mode."""

    signs, logs, metadata = e18.mode_signed_logs(
        spectral, column, targets, level
    )
    raw_signs, raw_logs = d19.undo_constructor_normalization(
        signs, logs, metadata
    )
    return raw_signs, raw_logs, signs, logs


def build_raw_mode(
    spectral: dict[str, Any],
    column: int,
    source_name: str,
    j_label: int,
    saved: dict[tuple[int, str], tuple[float, float]],
) -> RawMode:
    m = int(spectral["m"])
    lam = float(spectral["lambda"])
    nodes, raw_weights = special.roots_legendre(NORM_GAUSS_ORDER)
    positive_targets = (nodes + 1) / 2
    weights = raw_weights / 2
    targets = np.concatenate(([0.0], positive_targets))
    raw_signs, raw_logs, old_signs, old_logs = raw_signed_logs(
        spectral, column, targets
    )

    log_N = 0.5 * (
        math.log(2)
        + float(special.logsumexp(2 * raw_logs[1:], b=weights))
    )
    J_sign, half_log_J = d19.signed_log_weighted_sum(
        raw_signs[1:], raw_logs[1:], weights
    )
    if J_sign == 0:
        raise RuntimeError(f"RAW_MODE_ZERO_INTEGRAL:{m}:{source_name}")
    phase = J_sign
    log_J = math.log(2) + float(half_log_J)
    c_sign_after_phase = phase * int(raw_signs[0])
    if c_sign_after_phase == 0:
        raise RuntimeError(f"RAW_MODE_ZERO_CENTRE:{m}:{source_name}")
    log_c = float(raw_logs[0])

    log_scale_l2 = -0.5 * math.log(lam) - log_N
    saved_I, saved_h_zero = saved[(m, source_name)]
    log_scale_integral = (
        math.log(abs(saved_I)) - math.log(lam) - log_J
    )
    log_scale_center = (
        math.log(abs(saved_h_zero)) - log_c
    )
    scale_l2 = safe_exp(log_scale_l2)
    scale_integral = safe_exp(log_scale_integral)
    scale_center = safe_exp(log_scale_center)

    I_x = math.exp(0.5 * math.log(lam) + log_J - log_N)
    h_x_zero = (
        c_sign_after_phase * math.exp(log_c + log_scale_l2)
    )
    mu_from_t = (
        c_sign_after_phase
        * math.exp(math.log(lam) + log_J - log_c)
    )
    mu_from_x = I_x / h_x_zero
    mu_from_saved = saved_I / saved_h_zero

    psi_values = (
        phase
        * raw_signs[1:].astype(np.float64)
        * np.exp(raw_logs[1:] - log_N)
    )
    h_x_values = psi_values / math.sqrt(lam)
    constructor_values = (
        old_signs[1:].astype(np.float64) * np.exp(old_logs[1:])
    )
    return RawMode(
        m=m,
        column=column,
        source_name=source_name,
        j_label=j_label,
        phase=phase,
        raw_c_sign_after_phase=c_sign_after_phase,
        log_raw_c_abs=log_c,
        log_raw_J_abs=log_J,
        log_raw_N=log_N,
        log_scale_l2=log_scale_l2,
        log_scale_integral=log_scale_integral,
        log_scale_center=log_scale_center,
        scale_l2=scale_l2,
        scale_integral=scale_integral,
        scale_center=scale_center,
        I_x=I_x,
        h_x_zero=h_x_zero,
        saved_I=saved_I,
        saved_h_zero=saved_h_zero,
        mu_from_t=mu_from_t,
        mu_from_x=mu_from_x,
        mu_from_saved=mu_from_saved,
        scale_relative_spread=relative_spread_from_logs(
            [log_scale_l2, log_scale_integral, log_scale_center]
        ),
        mu_relative_spread=relative_spread(
            [mu_from_t, mu_from_x, mu_from_saved]
        ),
        quadrature_nodes=positive_targets,
        quadrature_weights=weights,
        psi_values=psi_values,
        h_x_values=h_x_values,
        constructor_values=constructor_values,
    )


def raw_l2_values(
    spectral: dict[str, Any],
    mode: RawMode,
    targets: np.ndarray,
    level: e18.PrecisionLevel = LEVEL,
) -> np.ndarray:
    raw_signs, raw_logs, _, _ = raw_signed_logs(
        spectral, mode.column, targets, level
    )
    return (
        mode.phase
        * raw_signs.astype(np.float64)
        * np.exp(raw_logs + mode.log_scale_l2)
    )


def composite_gauss_nodes(
    m: int,
    factor: int = FOURIER_PANELS_FACTOR,
    min_panels: int = 1024,
) -> tuple[np.ndarray, np.ndarray, int]:
    panels = max(min_panels, factor * m)
    nodes, weights = special.roots_legendre(GAUSS_PANEL_ORDER)
    indices = np.arange(panels, dtype=np.float64)[:, None]
    targets = (indices + 0.5 + 0.5 * nodes[None, :]) / panels
    target_weights = np.broadcast_to(
        weights[None, :] / (2 * panels), targets.shape
    )
    return targets.ravel(), target_weights.ravel(), panels


def direct_fourier(
    spectral: dict[str, Any],
    mode: RawMode,
    y_values: np.ndarray,
    *,
    panel_factor: int = FOURIER_PANELS_FACTOR,
    min_panels: int = 1024,
) -> tuple[np.ndarray, int]:
    targets, weights, panels = composite_gauss_nodes(
        int(spectral["m"]), panel_factor, min_panels
    )
    values = raw_l2_values(spectral, mode, targets)
    phases = (
        2
        * math.pi
        * float(spectral["lambda"])
        * y_values[:, None]
        * targets[None, :]
    )
    result = (
        2
        * float(spectral["lambda"])
        * ((np.cos(phases) * weights[None, :]) @ values)
    )
    return result, panels


def simpson_outer_ladder(
    spectral: dict[str, Any],
    mode: RawMode,
    y_values: np.ndarray,
) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for points_per_cycle in (16, 32, 64):
        point_count = max(
            8193,
            int(
                math.ceil(
                    points_per_cycle * 5 * float(spectral["m"])
                )
            )
            + 1,
        )
        if point_count % 2 == 0:
            point_count += 1
        right = 1 - LEVEL.endpoint_eps
        targets = np.linspace(0.0, right, point_count)
        values = raw_l2_values(spectral, mode, targets)
        phases = (
            2
            * math.pi
            * float(spectral["lambda"])
            * y_values[:, None]
            * targets[None, :]
        )
        transforms = [
            float(
                2
                * float(spectral["lambda"])
                * integrate.simpson(values * np.cos(phase), x=targets)
            )
            for phase in phases
        ]
        output.append(
            {
                "points_per_cycle": points_per_cycle,
                "point_count": point_count,
                "values": transforms,
            }
        )
    return output


def mode_at_closed_t(
    spectral: dict[str, Any],
    mode: RawMode,
    t: float,
) -> float:
    if t == 1.0:
        return mode.phase * mode.scale_l2
    return float(
        raw_l2_values(
            spectral, mode, np.asarray([abs(t)], dtype=np.float64)
        )[0]
    )


def crosscheck_points(lam: float) -> list[tuple[str, float, str]]:
    return [
        ("zero", 0.0, "inside"),
        ("lambda_over_4", lam / 4, "inside"),
        ("lambda_over_2", lam / 2, "inside"),
        ("lambda_one_minus_1e_8", lam * (1 - 1e-8), "inside"),
        ("lambda", lam, "interior_limit"),
        ("lambda_one_plus_1e_8", lam * (1 + 1e-8), "outside"),
        ("two_lambda", 2 * lam, "outside"),
        ("five_lambda", 5 * lam, "outside"),
    ]


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


def packet_precheck(
    m: int,
    level: e18.PrecisionLevel,
    saved: dict[tuple[int, str], tuple[float, float]],
) -> dict[str, Any]:
    spectral = d19.canonical_spectral_full(m, level)
    lam = float(spectral["lambda"])
    modes = {
        column: build_raw_mode(
            spectral, column, source_name, j_label, saved
        )
        for column, source_name, j_label in MODE_MAP
    }
    mode0 = modes[0]
    mode4 = modes[2]
    weights = mode0.quadrature_weights

    inner = float(
        2
        * lam
        * np.sum(weights * mode0.h_x_values * mode4.h_x_values)
    )
    d_x = math.hypot(mode0.I_x, mode4.I_x)
    route_a = (
        mode4.I_x * mode0.h_x_values
        - mode0.I_x * mode4.h_x_values
    ) / d_x

    jbar0 = math.exp(mode0.log_raw_J_abs - mode0.log_raw_N)
    jbar4 = math.exp(mode4.log_raw_J_abs - mode4.log_raw_N)
    route_b = (
        jbar4 * mode0.psi_values - jbar0 * mode4.psi_values
    ) / (
        math.sqrt(lam) * math.hypot(jbar0, jbar4)
    )
    route_difference = math.sqrt(
        float(2 * lam * np.sum(weights * (route_a - route_b) ** 2))
    )
    route_norm = math.sqrt(
        float(2 * lam * np.sum(weights * route_a**2))
    )
    route_integral = float(
        2 * lam * np.sum(weights * route_a)
    )
    route_integral_scale = float(
        2 * lam * np.sum(weights * np.abs(route_a))
    )

    old_i0 = float(spectral["modes"][0]["integral"])
    old_i4 = float(spectral["modes"][2]["integral"])
    old_d = math.hypot(old_i0, old_i4)
    old_018 = (
        old_i4 * mode0.constructor_values
        - old_i0 * mode4.constructor_values
    ) / old_d
    old_norm = math.sqrt(
        float(2 * lam * np.sum(weights * old_018**2))
    )
    old_difference = math.sqrt(
        float(2 * lam * np.sum(weights * (old_018 - route_b) ** 2))
    )
    old_relative_difference = old_difference / max(
        old_norm, route_norm, np.finfo(np.float64).tiny
    )
    canonical_pass = (
        route_difference <= PACKET_RTOL
        and abs(route_norm - 1) <= PACKET_RTOL
        and abs(route_integral)
        <= PACKET_RTOL * max(route_integral_scale, 1.0)
        and abs(inner) <= ORTHOGONALITY_ATOL
    )
    identity_confirmed = old_relative_difference <= 1e-10
    return {
        "m": m,
        "level": level.name,
        "degree": spectral["degree"],
        "mode_inner_product": repr(inner),
        "route_A_L2_norm": repr(route_norm),
        "route_A_integral": repr(route_integral),
        "route_A_integral_scale": repr(route_integral_scale),
        "route_A_B_L2_difference": repr(route_difference),
        "canonical_packet_pass": canonical_pass,
        "old_018_packet_L2_norm": repr(old_norm),
        "old_018_vs_canonical_L2_difference": repr(old_difference),
        "old_018_vs_canonical_relative_difference": repr(
            old_relative_difference
        ),
        "identity_code": (
            "018_CANONICAL_IDENTITY_CONFIRMED"
            if identity_confirmed
            else "018_CANONICAL_IDENTITY_REJECTED_REPEAT_REQUIRED"
        ),
        "repeat_320_bands_required": not identity_confirmed,
    }


def run() -> dict[str, Any]:
    saved = load_saved_019_centres()
    mode_rows: list[dict[str, Any]] = []
    packet_rows: list[dict[str, Any]] = []
    fourier_rows: list[dict[str, Any]] = []
    summaries: list[dict[str, Any]] = []

    all_same_mode_green = True
    all_canonical_packets_green = True
    old_packet_identity_green = True
    stable_k1_green = True
    global_continuation_green = True
    any_global_floor = False

    for m in M_VALUES:
        print(f"[020] same-mode lock m={m}", flush=True)
        spectral = d19.canonical_spectral_full(m, LEVEL)
        lam = float(spectral["lambda"])
        modes = {
            column: build_raw_mode(
                spectral, column, source_name, j_label, saved
            )
            for column, source_name, j_label in MODE_MAP
        }

        m_same_mode_green = True
        for column, source_name, j_label in MODE_MAP:
            mode = modes[column]
            scale_pass = mode.scale_relative_spread <= SCALE_RTOL
            mu_agreement_pass = mode.mu_relative_spread <= MU_RTOL
            mu_interval_pass = (
                mode.mu_from_t > 0
                and mode.mu_from_t <= 1 + 5e-12
            )
            mode_pass = (
                scale_pass and mu_agreement_pass and mu_interval_pass
            )
            m_same_mode_green = m_same_mode_green and mode_pass
            mode_rows.append(
                {
                    "m": m,
                    "lambda": repr(lam),
                    "mode": source_name,
                    "j": j_label,
                    "raw_reference": "endpoint_Frobenius_phi(1)=1",
                    "phase_epsilon": mode.phase,
                    "raw_N_log10": repr(
                        mode.log_raw_N / math.log(10)
                    ),
                    "raw_J_sign_after_phase": 1,
                    "raw_J_log10_abs": repr(
                        mode.log_raw_J_abs / math.log(10)
                    ),
                    "raw_c_sign_after_phase": (
                        mode.raw_c_sign_after_phase
                    ),
                    "raw_c_log10_abs": repr(
                        mode.log_raw_c_abs / math.log(10)
                    ),
                    "scale_L2": repr(mode.scale_l2),
                    "scale_L2_log10": repr(
                        mode.log_scale_l2 / math.log(10)
                    ),
                    "scale_integral": repr(mode.scale_integral),
                    "scale_integral_log10": repr(
                        mode.log_scale_integral / math.log(10)
                    ),
                    "scale_center": repr(mode.scale_center),
                    "scale_center_log10": repr(
                        mode.log_scale_center / math.log(10)
                    ),
                    "scale_relative_spread": repr(
                        mode.scale_relative_spread
                    ),
                    "scale_check_pass": scale_pass,
                    "I_x_rebuilt": repr(mode.I_x),
                    "I_x_saved": repr(mode.saved_I),
                    "h_x_zero_rebuilt": repr(mode.h_x_zero),
                    "h_x_zero_saved_019": repr(mode.saved_h_zero),
                    "mu_from_t": repr(mode.mu_from_t),
                    "mu_from_x": repr(mode.mu_from_x),
                    "mu_from_saved": repr(mode.mu_from_saved),
                    "mu_relative_spread": repr(
                        mode.mu_relative_spread
                    ),
                    "mu_agreement_pass": mu_agreement_pass,
                    "mu_interval_0_lt_mu_le_1_with_float_tolerance": (
                        mu_interval_pass
                    ),
                    "same_mode_pass": mode_pass,
                    "operator_prefactor": (
                        "1 (kernel exp(2*pi*i*lambda^2*s*t)); "
                        "mu=lambda*kappa"
                    ),
                }
            )
        all_same_mode_green = (
            all_same_mode_green and m_same_mode_green
        )

        print(f"[020] packet pre-check m={m}", flush=True)
        m_packet_rows = [
            packet_precheck(m, precision, saved)
            for precision in e18.LEVELS
        ]
        packet_rows.extend(m_packet_rows)
        m_canonical_green = all(
            bool(row["canonical_packet_pass"])
            for row in m_packet_rows
        )
        m_old_identity = all(
            row["identity_code"]
            == "018_CANONICAL_IDENTITY_CONFIRMED"
            for row in m_packet_rows
        )
        all_canonical_packets_green = (
            all_canonical_packets_green and m_canonical_green
        )
        old_packet_identity_green = (
            old_packet_identity_green and m_old_identity
        )

        points = crosscheck_points(lam)
        y_values = np.asarray([point[1] for point in points])
        outer_y = y_values[5:]
        backend_a: dict[int, np.ndarray] = {}
        backend_b: dict[int, np.ndarray] = {}
        outer_ladders: dict[int, list[dict[str, Any]]] = {}
        g1_rows: list[dict[str, Any]] = []

        for column, source_name, _ in MODE_MAP:
            print(f"[020] Fourier A/B m={m} mode={source_name}", flush=True)
            mode = modes[column]
            values, panels = direct_fourier(
                spectral, mode, y_values
            )
            backend_a[column] = values
            backend_b[column] = np.asarray(
                [
                    d19.l2_fourier_bessel(
                        spectral, column, float(y)
                    )
                    for y in y_values
                ]
            )
            outer_ladders[column] = simpson_outer_ladder(
                spectral, mode, outer_y
            )

            for point_index, (point_name, y, region) in enumerate(
                points
            ):
                a_value = float(backend_a[column][point_index])
                b_value = float(backend_b[column][point_index])
                scale = max(abs(a_value), abs(b_value))
                absolute_error = abs(a_value - b_value)
                relative_error = absolute_error / max(
                    scale, np.finfo(np.float64).tiny
                )
                if region in ("inside", "interior_limit"):
                    h_x = mode_at_closed_t(
                        spectral, mode, y / lam
                    )
                    mu_h_x = mode.mu_from_t * h_x
                    triple_scale = max(
                        abs(a_value), abs(b_value), abs(mu_h_x)
                    )
                    triple_error = max(
                        abs(a_value - b_value),
                        abs(a_value - mu_h_x),
                        abs(b_value - mu_h_x),
                    )
                    triple_relative_error = triple_error / max(
                        triple_scale, np.finfo(np.float64).tiny
                    )
                else:
                    h_x = ""
                    mu_h_x = ""
                    triple_error = ""
                    triple_relative_error = ""

                point_pass = (
                    scale >= ARITHMETIC_FLOOR
                    and absolute_error
                    <= FOURIER_ATOL + FOURIER_RTOL * scale
                )
                if region in ("inside", "interior_limit"):
                    point_pass = (
                        point_pass
                        and isinstance(triple_error, float)
                        and triple_error
                        <= FOURIER_ATOL
                        + FOURIER_RTOL
                        * max(
                            abs(a_value),
                            abs(b_value),
                            abs(float(mu_h_x)),
                        )
                    )

                if region == "outside":
                    outer_index = point_index - 5
                    simpson_values = [
                        float(run["values"][outer_index])
                        for run in outer_ladders[column]
                    ]
                    last_delta = abs(
                        simpson_values[-1] - simpson_values[-2]
                    )
                    outer_scale = max(
                        abs(a_value),
                        abs(b_value),
                        *(abs(value) for value in simpson_values),
                    )
                    outer_pass = (
                        outer_scale >= ARITHMETIC_FLOOR
                        and last_delta <= 1e-7 * outer_scale
                        and abs(simpson_values[-1] - a_value)
                        <= 1e-7 * outer_scale
                        and absolute_error
                        <= FOURIER_ATOL + FOURIER_RTOL * outer_scale
                    )
                    outer_status = (
                        "PASS"
                        if outer_pass
                        else (
                            "FLOOR_UNRESOLVED"
                            if outer_scale < ARITHMETIC_FLOOR
                            else "INDEPENDENT_QUADRATURE_MISMATCH"
                        )
                    )
                    global_continuation_green = (
                        global_continuation_green and outer_pass
                    )
                    any_global_floor = (
                        any_global_floor
                        or outer_status == "FLOOR_UNRESOLVED"
                    )
                    simpson_json = json.dumps(
                        [
                            {
                                "points_per_cycle": run[
                                    "points_per_cycle"
                                ],
                                "point_count": run["point_count"],
                                "value": run["values"][outer_index],
                            }
                            for run in outer_ladders[column]
                        ],
                        separators=(",", ":"),
                    )
                    g3_delta = repr(last_delta)
                    g3_status = outer_status
                    g3_pass: bool | str = outer_pass
                else:
                    simpson_json = ""
                    g3_delta = ""
                    g3_status = "NOT_OUTSIDE"
                    g3_pass = ""

                if region in ("inside", "interior_limit"):
                    if scale < ARITHMETIC_FLOOR:
                        point_status = "ARITHMETIC_FLOOR_UNRESOLVED"
                    else:
                        point_status = "PASS" if point_pass else "FAIL"
                    if scale >= ARITHMETIC_FLOOR:
                        stable_k1_green = stable_k1_green and point_pass
                else:
                    point_status = g3_status

                fourier_rows.append(
                    {
                        "m": m,
                        "lambda": repr(lam),
                        "mode": source_name,
                        "point": point_name,
                        "region": region,
                        "y": repr(y),
                        "backend_A_raw_t_composite_gauss": repr(a_value),
                        "backend_B_global_legendre_continuation": repr(
                            b_value
                        ),
                        "mu_from_same_raw_mode": repr(mode.mu_from_t),
                        "h_x_at_y_inside_or_limit": (
                            repr(h_x) if h_x != "" else ""
                        ),
                        "mu_times_h_x_inside_or_limit": (
                            repr(mu_h_x) if mu_h_x != "" else ""
                        ),
                        "absolute_A_B_error": repr(absolute_error),
                        "relative_A_B_error": repr(relative_error),
                        "triple_max_absolute_error": (
                            repr(triple_error)
                            if triple_error != ""
                            else ""
                        ),
                        "triple_relative_error": (
                            repr(triple_relative_error)
                            if triple_relative_error != ""
                            else ""
                        ),
                        "composite_gauss_panels": panels,
                        "G3_simpson_ladder": simpson_json,
                        "G3_last_step_delta": g3_delta,
                        "G3_status": g3_status,
                        "G3_pass": g3_pass,
                        "point_status": point_status,
                    }
                )

        mode0 = modes[0]
        mode4 = modes[2]
        d_x = math.hypot(mode0.I_x, mode4.I_x)
        for factor, label in ((10, "Q1"), (20, "Q2"), (40, "Q3")):
            a0, panels0 = direct_fourier(
                spectral,
                mode0,
                np.asarray([0.0]),
                panel_factor=factor,
                min_panels=256,
            )
            a4, panels4 = direct_fourier(
                spectral,
                mode4,
                np.asarray([0.0]),
                panel_factor=factor,
                min_panels=256,
            )
            term0 = mode4.I_x * float(a0[0]) / d_x
            term4 = mode0.I_x * float(a4[0]) / d_x
            trial_zero = term0 - term4
            cancellation_scale = abs(term0) + abs(term4)
            g1_rows.append(
                {
                    "level": label,
                    "panels_mode0": panels0,
                    "panels_mode4": panels4,
                    "hat_htrial_zero_unforced": trial_zero,
                    "cancellation_scale": cancellation_scale,
                    "epsilon0": (
                        abs(trial_zero) / cancellation_scale
                        if cancellation_scale > 0
                        else math.inf
                    ),
                }
            )

        summaries.append(
            {
                "m": m,
                "lambda": lam,
                "same_mode_green": m_same_mode_green,
                "canonical_packet_A_B_green": m_canonical_green,
                "old_018_packet_identity_green": m_old_identity,
                "old_018_repeat_320_bands_required": (
                    not m_old_identity
                ),
                "G1_epsilon0_quadrature_ladder": g1_rows,
                "G1_final_epsilon0_at_floor": (
                    g1_rows[-1]["epsilon0"]
                    <= 256 * np.finfo(np.float64).eps
                ),
                "Fejer_or_residual_evaluated": False,
            }
        )

    if not all_same_mode_green:
        primary = "T_TO_X_MODE_NORMALIZATION_MISMATCH"
    elif not all_canonical_packets_green:
        primary = "CANONICAL_PACKET_NORMALIZATION_MISMATCH"
    elif not old_packet_identity_green:
        primary = "CANONICAL_PACKET_MISMATCH"
    elif not stable_k1_green:
        primary = "COMPRESSED_FOURIER_LAMBDA_FACTOR_MISMATCH"
    elif not global_continuation_green and any_global_floor:
        primary = "GLOBAL_CONTINUATION_FLOOR_UNRESOLVED"
    elif not global_continuation_green:
        primary = "GLOBAL_PROLATE_CONTINUATION_MISMATCH"
    else:
        primary = "PROLATE_COORDINATE_AND_NORMALIZATION_LOCK_GREEN"

    payload = {
        "primary_verdict": primary,
        "epistemic_status": (
            "REPORT_ONLY_NUMERICAL_OBJECT_LOCK_NOT_A_THEOREM_NOT_RH"
        ),
        "convention": {
            "t_domain": "[-1,1]",
            "x": "lambda*t",
            "y": "lambda*s",
            "Fourier_x": "integral h(x)*exp(2*pi*i*x*y) dx",
            "C": "2*pi*lambda^2",
            "sqrt_2pi_prefactor": False,
            "operator_prefactor": (
                "1 for raw t-kernel; mu=lambda*kappa"
            ),
        },
        "source_locks": {
            "goal": str(GOAL),
            "goal_sha256": file_sha256(GOAL),
            "constructor_018": str(
                REQUEST_DIR / "estar_full_window_sign_probe.py"
            ),
            "diagnostic_019": str(
                REQUEST_DIR / "dual_prolate_residual_probe.py"
            ),
            "saved_019_centres": str(SAVED_019),
        },
        "guards": {
            "old_mu_divided_or_repaired": False,
            "same_mode_recomputed": True,
            "backend_A_from_raw_t_mode": True,
            "backend_B_global_not_zero_extended": True,
            "G3_independent_quadrature": (
                "composite Gauss versus uniform-grid Simpson"
            ),
            "Fejer_evaluated": False,
            "residual_evaluated": False,
            "STATE_mutated": False,
            "Bus_010_created": False,
        },
        "aggregate": {
            "same_mode_green": all_same_mode_green,
            "canonical_packet_A_B_green": (
                all_canonical_packets_green
            ),
            "old_018_packet_identity_green": (
                old_packet_identity_green
            ),
            "stable_above_floor_K1_green": stable_k1_green,
            "global_continuation_G3_green": (
                global_continuation_green
            ),
            "global_continuation_floor_seen": any_global_floor,
        },
        "precision": {
            "spectral_and_ode": LEVEL.__dict__,
            "normalization_Gauss_order": NORM_GAUSS_ORDER,
            "Fourier_composite_Gauss_order": GAUSS_PANEL_ORDER,
            "Fourier_panels": "max(1024,20*m)",
            "G3_Simpson_points_per_cycle": [16, 32, 64],
            "arithmetic_floor": ARITHMETIC_FLOOR,
        },
        "summaries": summaries,
        "environment": {
            "python": platform.python_version(),
            "numpy": np.__version__,
        },
    }

    write_csv(MODE_CSV, mode_rows)
    write_csv(PACKET_CSV, packet_rows)
    write_csv(FOURIER_CSV, fourier_rows)
    RESULT_JSON.write_text(
        json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(json_safe(payload), indent=2, sort_keys=True))
    return payload


if __name__ == "__main__":
    run()
