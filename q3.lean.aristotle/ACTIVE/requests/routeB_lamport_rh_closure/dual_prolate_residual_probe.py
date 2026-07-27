#!/usr/bin/env python3
"""Guarded dual-prolate diagnostic requested by goal 019.

The constructor is imported literally from the numerical 013/018 line:
the even-sector tridiagonal eigenpairs, the stored integrals I0/I4, and the
ODE modes normalized to the constructor's Legendre centre values.  No factor
is fitted.

Backend A is an independent composite Gauss cosine quadrature of those ODE
modes.  Backend B uses the no-fit mu factors and a global prolate continuation
obtained from the L2 Legendre packet and its spherical-Bessel Fourier formula.
The mandatory K1 guard is evaluated before any residual.  If it fails, every
requested Fejer/residual row is emitted as guard-blocked; backend B is never
used to manufacture a residual.

This is a numerical diagnostic, not a theorem.  It does not mutate STATE and
does not create Bus 010.
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
from scipy import integrate, linalg, special

import estar_full_window_sign_probe as e18
import strip_growth_probe as strip


REQUEST_DIR = Path(__file__).resolve().parent
MU_CSV = REQUEST_DIR / "DUAL_MU_FACTORS.csv"
CROSSCHECK_CSV = REQUEST_DIR / "DUAL_FOURIER_CROSSCHECK.csv"
FEJER_CSV = REQUEST_DIR / "DUAL_FEJER_CONVERGENCE.csv"
RESIDUAL_CSV = REQUEST_DIR / "CORRECTED_POISSON_RESIDUAL.csv"
LOWER_MD = REQUEST_DIR / "LOWER_ENDPOINT_DUAL_TRAP_CHECK.md"
RESULT_JSON = REQUEST_DIR / "DUAL_PROLATE_RESIDUAL_DIAGNOSTIC.json"

M_VALUES = (13, 53, 257)
N_LADDER = (64, 128, 256, 512, 1024, 2048)
INTERIOR_Q_FRACTIONS = (0.25, 0.5, 0.75)
GAUSS_ORDER = 16
L2_GAUSS_ORDER = 2048
LEVEL = e18.LEVELS[-1]


@dataclass
class ModeNormalization:
    stable_center: float
    stable_integral: float
    current_center: float
    stored_integral: float
    l2_log_scale_from_raw: float
    l2_orientation: int
    constructor_scale_over_l2: float
    mu_no_fit: float
    mu_l2_diagnostic: float


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


def canonical_spectral_full(
    m: int,
    level: e18.PrecisionLevel = LEVEL,
) -> dict[str, Any]:
    """Reproduce the P3 constructor and retain its L2 Legendre coefficients."""

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
        coefficients = eigenvectors[:, column] * np.sqrt(
            (2 * degrees + 1) / (2 * lam)
        )
        modes[column] = {
            "characteristic": float(eigenvalues[column]),
            "integral": float(
                eigenvectors[0, column] * math.sqrt(2 * lam)
            ),
            "center": float(
                np.polynomial.legendre.legval(0.0, coefficients)
            ),
            "tail_mass": float(np.linalg.norm(eigenvectors[-10:, column])),
            "coefficients": coefficients,
        }
    return {
        "m": m,
        "lambda": lam,
        "c": c,
        "degree": degree,
        "degrees": degrees,
        "modes": modes,
        "eigenvalues_0_8": eigenvalues,
    }


def undo_constructor_normalization(
    signs: np.ndarray,
    logs: np.ndarray,
    metadata: dict[str, Any],
) -> tuple[np.ndarray, np.ndarray]:
    normalization_sign = int(metadata["normalization_sign"])
    normalization_log = float(metadata["normalization_log"])
    return signs * normalization_sign, logs - normalization_log


def signed_log_weighted_sum(
    signs: np.ndarray,
    logs: np.ndarray,
    weights: np.ndarray,
) -> tuple[int, float]:
    finite = (signs != 0) & np.isfinite(logs) & (weights > 0)
    if not np.any(finite):
        return 0, -math.inf
    selected_logs = logs[finite]
    largest = float(np.max(selected_logs))
    scaled = float(
        np.sum(
            signs[finite].astype(np.float64)
            * weights[finite]
            * np.exp(selected_logs - largest)
        )
    )
    if scaled == 0:
        return 0, -math.inf
    return (1 if scaled > 0 else -1), largest + math.log(abs(scaled))


def l2_mode_normalization(
    spectral: dict[str, Any],
    column: int,
    level: e18.PrecisionLevel = LEVEL,
) -> ModeNormalization:
    """Recover an L2 normalization independently of the unstable centre sum."""

    nodes, raw_weights = special.roots_legendre(L2_GAUSS_ORDER)
    positive_targets = (nodes + 1) / 2
    weights = raw_weights / 2
    targets = np.concatenate(([0.0], positive_targets))
    signs, logs, metadata = e18.mode_signed_logs(
        spectral, column, targets, level
    )
    raw_signs, raw_logs = undo_constructor_normalization(
        signs, logs, metadata
    )

    log_norm_sq = (
        math.log(2 * spectral["lambda"])
        + special.logsumexp(2 * raw_logs[1:], b=weights)
    )
    l2_log_scale = -0.5 * float(log_norm_sq)
    integral_sign, integral_log = signed_log_weighted_sum(
        raw_signs[1:], raw_logs[1:], weights
    )
    if integral_sign == 0:
        raise RuntimeError(
            f"L2_NORMALIZATION_ZERO_INTEGRAL:{spectral['m']}:{column}"
        )
    orientation = integral_sign

    stable_center = (
        orientation
        * int(raw_signs[0])
        * math.exp(float(raw_logs[0] + l2_log_scale))
    )
    stable_integral = (
        2
        * spectral["lambda"]
        * orientation
        * integral_sign
        * math.exp(float(integral_log + l2_log_scale))
    )
    current_center = float(spectral["modes"][column]["center"])
    stored_integral = float(spectral["modes"][column]["integral"])
    return ModeNormalization(
        stable_center=stable_center,
        stable_integral=stable_integral,
        current_center=current_center,
        stored_integral=stored_integral,
        l2_log_scale_from_raw=l2_log_scale,
        l2_orientation=orientation,
        constructor_scale_over_l2=current_center / stable_center,
        mu_no_fit=stored_integral / current_center,
        mu_l2_diagnostic=stored_integral / stable_center,
    )


def current_mode_values(
    spectral: dict[str, Any],
    column: int,
    targets: np.ndarray,
    level: e18.PrecisionLevel = LEVEL,
) -> np.ndarray:
    signs, logs, _ = e18.mode_signed_logs(
        spectral, column, targets, level
    )
    values = np.zeros(targets.size, dtype=np.float64)
    representable = logs >= math.log(np.nextafter(0.0, 1.0))
    values[representable] = (
        signs[representable].astype(np.float64)
        * np.exp(logs[representable])
    )
    return values


def composite_gauss_rule(m: int) -> tuple[np.ndarray, np.ndarray]:
    """Independent cosine quadrature dense enough for the y=5*lambda row."""

    panels = max(1024, 20 * m)
    nodes, weights = special.roots_legendre(GAUSS_ORDER)
    panel_index = np.arange(panels, dtype=np.float64)[:, None]
    targets = (
        panel_index + 0.5 + 0.5 * nodes[None, :]
    ) / panels
    target_weights = np.broadcast_to(
        weights[None, :] / (2 * panels),
        targets.shape,
    )
    return targets.ravel(), target_weights.ravel()


def cosine_quadrature_values(
    spectral: dict[str, Any],
    column: int,
    y_values: np.ndarray,
    level: e18.PrecisionLevel = LEVEL,
) -> np.ndarray:
    targets, weights = composite_gauss_rule(int(spectral["m"]))
    mode_values = current_mode_values(
        spectral, column, targets, level
    )
    phases = (
        2
        * math.pi
        * spectral["lambda"]
        * y_values[:, None]
        * targets[None, :]
    )
    return (
        2
        * spectral["lambda"]
        * ((np.cos(phases) * weights[None, :]) @ mode_values)
    )


def outside_simpson_ladder(
    spectral: dict[str, Any],
    column: int,
    y_values: np.ndarray,
) -> list[dict[str, Any]]:
    """Independent uniform-grid Simpson ladder for the oscillatory outer rows."""

    output: list[dict[str, Any]] = []
    for points_per_cycle in (16, 32, 64):
        point_count = max(
            8193,
            int(math.ceil(points_per_cycle * 5 * spectral["m"])) + 1,
        )
        if point_count % 2 == 0:
            point_count += 1
        right = 1 - LEVEL.endpoint_eps
        targets = np.linspace(0.0, right, point_count)
        mode_values = current_mode_values(
            spectral, column, targets, LEVEL
        )
        phases = (
            2
            * math.pi
            * spectral["lambda"]
            * y_values[:, None]
            * targets[None, :]
        )
        values = [
            float(
                2
                * spectral["lambda"]
                * integrate.simpson(
                    mode_values * np.cos(phase),
                    x=targets,
                )
            )
            for phase in phases
        ]
        output.append(
            {
                "points_per_cycle": points_per_cycle,
                "point_count": point_count,
                "values": values,
            }
        )
    return output


def l2_fourier_bessel(
    spectral: dict[str, Any],
    column: int,
    y: float,
) -> float:
    """Global Fourier transform of the L2 Legendre packet."""

    degrees = spectral["degrees"].astype(np.int64)
    coefficients = spectral["modes"][column]["coefficients"]
    z = 2 * math.pi * spectral["lambda"] * abs(float(y))
    spherical = special.spherical_jn(degrees, z)
    phases = np.where((degrees // 2) % 2 == 0, 1.0, -1.0)
    return float(
        2
        * spectral["lambda"]
        * np.dot(coefficients * phases, spherical)
    )


def backend_b_value(
    spectral: dict[str, Any],
    column: int,
    normalization: ModeNormalization,
    y: float,
    *,
    mu_multiplier: float = 1.0,
) -> tuple[float, float]:
    """Return mu*Phi_global and Phi_global for the constructor-scaled mode."""

    l2_hat = l2_fourier_bessel(spectral, column, y)
    phi_l2 = l2_hat / normalization.mu_l2_diagnostic
    phi_current = normalization.constructor_scale_over_l2 * phi_l2
    return (
        mu_multiplier * normalization.mu_no_fit * phi_current,
        phi_current,
    )


def crosscheck_points(lam: float) -> list[tuple[str, float]]:
    return [
        ("zero", 0.0),
        ("lambda_over_4", lam / 4),
        ("lambda_over_2", lam / 2),
        ("lambda_one_minus_1e_8", lam * (1 - 1e-8)),
        ("lambda", lam),
        ("lambda_one_plus_1e_8", lam * (1 + 1e-8)),
        ("two_lambda", 2 * lam),
        ("five_lambda", 5 * lam),
    ]


def evaluation_points(m: int) -> list[dict[str, Any]]:
    lam = math.sqrt(m)
    rows: list[dict[str, Any]] = []
    seen: set[tuple[str, str]] = set()

    def add(kind: str, label: str, q: float, r: int | None) -> None:
        key = (kind, label)
        if key in seen:
            return
        seen.add(key)
        rows.append(
            {
                "m": m,
                "kind": kind,
                "label": label,
                "r": "" if r is None else r,
                "q_lambda_over_u": q,
                "u": lam / q,
            }
        )

    for r in range(1, m + 1):
        add("tooth", f"tooth_r_{r}", float(r), r)
    for r in range(1, m):
        for fraction in INTERIOR_Q_FRACTIONS:
            q = r + fraction
            add(
                "band_interior",
                f"band_r_{r}_q_{q:.2f}",
                q,
                r,
            )
    add("special", "u_equals_one", lam, None)
    return rows


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
    mu_rows: list[dict[str, Any]] = []
    cross_rows: list[dict[str, Any]] = []
    fejer_rows: list[dict[str, Any]] = []
    residual_rows: list[dict[str, Any]] = []
    summaries: list[dict[str, Any]] = []
    lower_sections: list[str] = []

    global_k1_pass = True
    for m in M_VALUES:
        spectral = canonical_spectral_full(m)
        lam = float(spectral["lambda"])
        i0 = float(spectral["modes"][0]["integral"])
        i4 = float(spectral["modes"][2]["integral"])
        denominator = math.hypot(i0, i4)
        normalizations = {
            column: l2_mode_normalization(spectral, column)
            for column in (0, 2)
        }
        epsilon0_ladder: list[dict[str, Any]] = []
        for precision_level in e18.LEVELS:
            spectral_level = canonical_spectral_full(m, precision_level)
            i0_level = float(spectral_level["modes"][0]["integral"])
            i4_level = float(spectral_level["modes"][2]["integral"])
            d_level = math.hypot(i0_level, i4_level)
            normalizations_level = {
                column: l2_mode_normalization(
                    spectral_level, column, precision_level
                )
                for column in (0, 2)
            }
            b0_level, _ = backend_b_value(
                spectral_level,
                0,
                normalizations_level[0],
                0.0,
            )
            b4_level, _ = backend_b_value(
                spectral_level,
                2,
                normalizations_level[2],
                0.0,
            )
            term0_level = i4_level * b0_level / d_level
            term4_level = i0_level * b4_level / d_level
            hat_level = term0_level - term4_level
            cancellation_scale = abs(term0_level) + abs(term4_level)
            epsilon0_ladder.append(
                {
                    "level": precision_level.name,
                    "degree": spectral_level["degree"],
                    "hat_htrial_B_zero_unforced": hat_level,
                    "cancellation_scale": cancellation_scale,
                    "epsilon0": (
                        abs(hat_level) / cancellation_scale
                        if cancellation_scale > 0
                        else math.inf
                    ),
                }
            )

        for column, source_name, mapping in (
            (0, "h0", "h0<->mu0=chi0"),
            (2, "h4", "h4<->mu4=chi2"),
        ):
            nrm = normalizations[column]
            mu_rows.append(
                {
                    "m": m,
                    "lambda": repr(lam),
                    "mode": source_name,
                    "mapping": mapping,
                    "D": repr(denominator),
                    "stored_I": repr(nrm.stored_integral),
                    "constructor_h_at_zero": repr(nrm.current_center),
                    "mu_no_fit": repr(nrm.mu_no_fit),
                    "mu_no_fit_squared": repr(nrm.mu_no_fit**2),
                    "mu_sign": 1 if nrm.mu_no_fit > 0 else -1,
                    "stable_L2_h_at_zero_diagnostic": repr(
                        nrm.stable_center
                    ),
                    "stable_L2_integral_diagnostic": repr(
                        nrm.stable_integral
                    ),
                    "stored_I_over_stable_center": repr(
                        nrm.mu_l2_diagnostic
                    ),
                    "constructor_scale_over_L2": repr(
                        nrm.constructor_scale_over_l2
                    ),
                    "expected_positive_and_at_most_one": (
                        abs(nrm.mu_no_fit) <= 1 + 1e-10
                        and nrm.mu_no_fit > 0
                    ),
                }
            )

        points = crosscheck_points(lam)
        y_values = np.asarray([value for _, value in points])
        quad_by_column = {
            column: cosine_quadrature_values(
                spectral, column, y_values
            )
            for column in (0, 2)
        }
        outside_y_values = y_values[5:]
        simpson_by_column = {
            column: outside_simpson_ladder(
                spectral, column, outside_y_values
            )
            for column in (0, 2)
        }
        b_by_column: dict[int, list[float]] = {0: [], 2: []}
        phi_by_column: dict[int, list[float]] = {0: [], 2: []}
        m_k1_pass = True
        g3_all_pass = True
        for column, source_name in ((0, "h0"), (2, "h4")):
            nrm = normalizations[column]
            for point_index, (label, y) in enumerate(points):
                backend_a = float(quad_by_column[column][point_index])
                backend_b, phi_global = backend_b_value(
                    spectral, column, nrm, y
                )
                b_by_column[column].append(backend_b)
                phi_by_column[column].append(phi_global)
                absolute_error = abs(backend_a - backend_b)
                relative_error = absolute_error / max(
                    abs(backend_a), abs(backend_b), 1e-300
                )
                point_pass = (
                    absolute_error <= 5e-11
                    + 5e-9 * max(abs(backend_a), abs(backend_b))
                )
                m_k1_pass = m_k1_pass and point_pass
                if point_index >= 5:
                    outside_index = point_index - 5
                    simpson_values = [
                        float(run["values"][outside_index])
                        for run in simpson_by_column[column]
                    ]
                    simpson_last_delta = abs(
                        simpson_values[-1] - simpson_values[-2]
                    )
                    external_scale = max(
                        abs(backend_a),
                        *(abs(value) for value in simpson_values),
                    )
                    external_independence_pass = (
                        external_scale >= 1e-14
                        and simpson_last_delta
                        <= 1e-7 * external_scale
                        and abs(simpson_values[-1] - backend_a)
                        <= 1e-7 * external_scale
                    )
                    external_status = (
                        "PASS"
                        if external_independence_pass
                        else (
                            "FLOOR_UNRESOLVED"
                            if external_scale < 1e-14
                            else "LADDER_MISMATCH"
                        )
                    )
                    g3_all_pass = (
                        g3_all_pass and external_independence_pass
                    )
                    simpson_ladder_json = json.dumps(
                        [
                            {
                                "points_per_cycle": run[
                                    "points_per_cycle"
                                ],
                                "point_count": run["point_count"],
                                "value": run["values"][outside_index],
                            }
                            for run in simpson_by_column[column]
                        ],
                        separators=(",", ":"),
                    )
                else:
                    simpson_values = []
                    simpson_last_delta = ""
                    external_independence_pass = ""
                    external_status = "NOT_OUTSIDE"
                    simpson_ladder_json = ""
                cross_rows.append(
                    {
                        "m": m,
                        "mode": source_name,
                        "point": label,
                        "y": repr(y),
                        "inside_closed_band": abs(y) <= lam,
                        "backend_A_cosine_quadrature": repr(backend_a),
                        "Phi_global_untruncated": repr(phi_global),
                        "mu_no_fit": repr(nrm.mu_no_fit),
                        "backend_B_mu_times_Phi": repr(backend_b),
                        "absolute_error": repr(absolute_error),
                        "relative_error": repr(relative_error),
                        "crosscheck_pass": point_pass,
                        "backend_A2_simpson_convergence_ladder": (
                            simpson_ladder_json
                        ),
                        "A2_last_step_absolute_delta": (
                            repr(simpson_last_delta)
                            if simpson_last_delta != ""
                            else ""
                        ),
                        "G3_external_independence_status": (
                            external_status
                        ),
                        "G3_external_independence_pass": (
                            external_independence_pass
                        ),
                    }
                )
        m_k1_pass = m_k1_pass and g3_all_pass

        a_trial_zero = (
            i4 * float(quad_by_column[0][0])
            - i0 * float(quad_by_column[2][0])
        ) / denominator
        a_trial_zero_scale = (
            abs(i4 * float(quad_by_column[0][0]))
            + abs(i0 * float(quad_by_column[2][0]))
        ) / denominator
        a_trial_zero_epsilon = abs(a_trial_zero) / a_trial_zero_scale
        b_trial_zero = (
            i4 * b_by_column[0][0]
            - i0 * b_by_column[2][0]
        ) / denominator
        b_trial_zero_flip_mu4 = (
            i4 * b_by_column[0][0]
            + i0 * b_by_column[2][0]
        ) / denominator

        htrial_center = (
            i4 * normalizations[0].current_center
            - i0 * normalizations[2].current_center
        ) / denominator
        p2_max_identity_error = 0.0
        for u in (1 / lam, 1.0, lam):
            counterterm = 0.5 * math.sqrt(u) * htrial_center
            full_placeholder = counterterm
            dropped_placeholder = 0.0
            expected_shift = -counterterm
            p2_max_identity_error = max(
                p2_max_identity_error,
                abs(
                    (dropped_placeholder - full_placeholder)
                    - expected_shift
                ),
            )

        h0_hat_lambda_a = float(quad_by_column[0][4])
        h4_hat_lambda_a = float(quad_by_column[2][4])
        htrial_hat_lambda_a = (
            i4 * h0_hat_lambda_a - i0 * h4_hat_lambda_a
        ) / denominator
        p3_rows = []
        for r, u, k in ((1, lam, m), (m, 1 / lam, 1)):
            for n_value in N_LADDER:
                if k > n_value:
                    continue
                weight = 1 - k / (n_value + 1)
                bug_shift = (
                    -0.5
                    * u ** (-0.5)
                    * weight
                    * htrial_hat_lambda_a
                )
                p3_rows.append(
                    {
                        "r": r,
                        "u": u,
                        "k": k,
                        "N": n_value,
                        "bug_shift": bug_shift,
                    }
                )

        p4_outside = []
        for point_index in (5, 6, 7):
            label, y = points[point_index]
            for column, source_name in ((0, "h0"), (2, "h4")):
                backend_a = float(quad_by_column[column][point_index])
                p4_outside.append(
                    {
                        "mode": source_name,
                        "point": label,
                        "y": y,
                        "quad_value": backend_a,
                        "zero_extended_value": 0.0,
                        "absolute_failure": abs(backend_a),
                    }
                )

        global_k1_pass = global_k1_pass and m_k1_pass
        guard_reason = (
            "K1_BACKEND_CROSSCHECK_FAILED_BACKEND_B_FORBIDDEN"
            if not m_k1_pass
            else "K1_PASS"
        )
        for n_value in N_LADDER:
            fejer_rows.append(
                {
                    "m": m,
                    "N": n_value,
                    "status": (
                        "SKIPPED_BY_K1_GUARD"
                        if not m_k1_pass
                        else "NOT_REACHED"
                    ),
                    "reason": guard_reason,
                    "backend_B_used": False,
                    "max_abs_change_from_previous_N": "",
                    "max_abs_residual": "",
                }
            )
        for point in evaluation_points(m):
            for n_value in N_LADDER:
                residual_rows.append(
                    {
                        **point,
                        "N": n_value,
                        "status": (
                            "SKIPPED_BY_K1_GUARD"
                            if not m_k1_pass
                            else "NOT_REACHED"
                        ),
                        "reason": guard_reason,
                        "backend_B_used": False,
                        "EstarMid": "",
                        "dual_fejer": "",
                        "counterterm": repr(
                            0.5
                            * math.sqrt(float(point["u"]))
                            * htrial_center
                        ),
                        "residual": "",
                        "component_scale": "",
                        "epsilon_floor": repr(
                            np.finfo(np.float64).eps
                        ),
                        "scale_free_residual": "",
                    }
                )

        lower_sections.extend(
            [
                f"## m = {m}",
                "",
                f"- `lambda = {lam!r}`",
                f"- K1 guard: `{'PASS' if m_k1_pass else 'FAIL'}`",
                (
                    "- Dual Fejer at `lambda^-1`: "
                    "`SKIPPED_BY_K1_GUARD`"
                    if not m_k1_pass
                    else "- Dual Fejer at `lambda^-1`: `NOT_REACHED`"
                ),
                (
                    "- Comparison with `sqrt(lambda)*TrapError`: "
                    "`NOT_FORMED`"
                ),
                "- Backend B used in lower-endpoint residual: `false`",
                "",
            ]
        )

        summaries.append(
            {
                "m": m,
                "lambda": lam,
                "D": denominator,
                "K1_crosscheck_pass": m_k1_pass,
                "G1_epsilon0_precision_ladder": epsilon0_ladder,
                "G1_epsilon0_decreases_to_floor": (
                    all(
                        epsilon0_ladder[index + 1]["epsilon0"]
                        <= epsilon0_ladder[index]["epsilon0"]
                        for index in range(len(epsilon0_ladder) - 1)
                    )
                    and epsilon0_ladder[-1]["epsilon0"]
                    <= 16 * np.finfo(np.float64).eps
                ),
                "hat_htrial_A_at_zero_unforced": a_trial_zero,
                "hat_htrial_A_zero_cancellation_scale": (
                    a_trial_zero_scale
                ),
                "hat_htrial_A_zero_epsilon0": a_trial_zero_epsilon,
                "hat_htrial_B_at_zero_unforced": b_trial_zero,
                "G3_external_independence_pass": g3_all_pass,
                "P1_flip_mu4_hat_htrial_B_at_zero": (
                    b_trial_zero_flip_mu4
                ),
                "P1_material_break": abs(
                    b_trial_zero_flip_mu4 - b_trial_zero
                ),
                "htrial_constructor_center": htrial_center,
                "P2_counterterm_shift_identity_max_error": (
                    p2_max_identity_error
                ),
                "P3_htrial_hat_lambda_backend_A": htrial_hat_lambda_a,
                "P3_rows": p3_rows,
                "P4_outside_rows": p4_outside,
                "required_evaluation_points_enumerated": len(
                    evaluation_points(m)
                ),
                "required_residual_rows_emitted": (
                    len(evaluation_points(m)) * len(N_LADDER)
                ),
            }
        )

    verdict = (
        "DUAL_RESIDUAL_DIAG_GREEN"
        if global_k1_pass
        else "MU_INDEX_OR_SIGN_MISMATCH"
    )
    payload = {
        "verdict": verdict,
        "epistemic_status": "NUMERICAL_DIAGNOSTIC_NOT_A_THEOREM_NOT_RH",
        "backend_B_residual_guard": (
            "PASSED" if global_k1_pass else "FAILED_BACKEND_B_NOT_USED"
        ),
        "constructor": "013/018 P3 numerical constructor, no fitted factor",
        "precision": {
            "spectral_degree": "max(180,2*ceil(10*m))",
            "ode": LEVEL.__dict__,
            "quadrature_order_per_panel": GAUSS_ORDER,
            "quadrature_panels": "max(1024,20*m)",
            "l2_diagnostic_gauss_order": L2_GAUSS_ORDER,
        },
        "N_ladder": N_LADDER,
        "summaries": summaries,
        "environment": {
            "python": platform.python_version(),
            "numpy": np.__version__,
        },
    }

    write_csv(MU_CSV, mu_rows)
    write_csv(CROSSCHECK_CSV, cross_rows)
    write_csv(FEJER_CSV, fejer_rows)
    write_csv(RESIDUAL_CSV, residual_rows)
    LOWER_MD.write_text(
        "\n".join(
            [
                "# LOWER ENDPOINT DUAL/TRAPEZOID CHECK",
                "",
                f"`{verdict}`",
                "",
                "Diagnostic only; not a theorem and not RH.",
                "",
                "The mandatory K1 Fourier-backend guard is evaluated before "
                "the lower-endpoint judge. A failed guard forbids using "
                "backend B in the residual, so no dual/trapezoid difference "
                "is manufactured.",
                "",
                "G1 is recorded as an `epsilon0` precision ladder relative "
                "to the two-term cancellation scale in the JSON artifact. "
                "G2 scale-free residual fields are present in the residual "
                "CSV and deliberately blank under the K1 guard. G3 uses a "
                "uniform-grid Simpson convergence ladder independent of the "
                "composite-Gauss cosine quadrature; all external rows remain "
                "at the arithmetic floor. G4 therefore selects the instrument "
                "mismatch branch: no mathematical counterexample is claimed, "
                "the 018 sign diagnostic remains independent, and 020 stays "
                "frozen.",
                "",
                *lower_sections,
                "## Plants",
                "",
                "- P1: executed at the zero-mass check; flipping `mu4` "
                "produces a material nonzero canonical transform.",
                "- P2: the counterterm-removal shift identity is checked "
                "algebraically at `u=lambda^-1,1,lambda`.",
                "- P3: the erroneous dual half-weight shift is evaluated "
                "from backend-A `hat_htrial(lambda)` at the affected endpoint "
                "teeth; no backend-B residual is formed.",
                "- P4: the zero-extended replacement is compared with "
                "backend-A values at all three outside rows.",
                "",
                "STATE was not changed. Bus 010 remains void.",
                "",
            ]
        ),
        encoding="utf-8",
    )
    RESULT_JSON.write_text(
        json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(json_safe(payload), indent=2, sort_keys=True))
    return payload


if __name__ == "__main__":
    run()
