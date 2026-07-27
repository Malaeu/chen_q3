#!/usr/bin/env python3
"""Float64 OffAxisGrowthProbe for the locked D0.7e.2 tracker.

The runner is diagnostic only.  It does not mutate STATE.json, close D0.7e.5a,
mint WPrime, or create a bus goal.  Run through uv so NumPy/SciPy versions are
isolated and explicit:

  uv run --no-project --with numpy --with scipy python off_axis_growth_probe.py
  uv run --no-project --with numpy --with scipy python off_axis_growth_probe.py --write
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import platform
import sys
from pathlib import Path
from typing import Any, Iterable

import numpy as np
from numpy.polynomial import legendre
from scipy import linalg, special


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
LADDER_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder"
OUT_DIR = LADDER_DIR / "out"

RESULT_JSON = REQUEST_DIR / "OFF_AXIS_GROWTH_PROBE.json"
RESULT_CSV = REQUEST_DIR / "OFF_AXIS_GROWTH_PROBE.csv"
RESULT_MD = REQUEST_DIR / "OFF_AXIS_GROWTH_PROBE.md"
STATE = REQUEST_DIR / "STATE.json"
ZERO_SOURCE = OUT_DIR / "anchor_locked_zeros_first_200.json"

EXISTING_CELLS = ((13, 90), (13, 120), (14, 120))
NEW_CELLS = ((53, 120), (101, 120))
FIT_CELLS = ((13, 120), (14, 120), (53, 120), (101, 120))
Y_GRID = (0.1, 0.2, 0.3, 0.4)
X_GRID_COUNT = 32769
QUAD_LOW = 64
QUAD_HIGH = 128
MODEL_DEGREES = {53: 650, 101: 1024}
MODEL_COMPARE_DEGREES = {53: 550, 101: 900}
ZETA_HALF_FLOAT64 = -1.4603545088095868


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


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


def primes_up_to(limit: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % p for p in primes if p * p <= candidate):
            primes.append(candidate)
    return primes


def prime_powers_up_to(limit: int) -> list[int]:
    values: set[int] = set()
    for prime in primes_up_to(limit):
        power = prime
        while power <= limit:
            values.add(power)
            power *= prime
    return sorted(values)


def legendre_x2_matrix(degrees: list[int]) -> np.ndarray:
    index = {degree: i for i, degree in enumerate(degrees)}
    matrix = np.zeros((len(degrees), len(degrees)), dtype=np.float64)
    for degree in degrees:
        a = (degree + 1) / (2 * degree + 1)
        b = degree / (2 * degree + 1) if degree else 0.0
        upper = degree + 1
        terms = [
            (upper + 1, a * (upper + 1) / (2 * upper + 1)),
            (upper - 1, a * upper / (2 * upper + 1)),
        ]
        if degree:
            lower = degree - 1
            terms.append((lower + 1, b * (lower + 1) / (2 * lower + 1)))
            if lower:
                terms.append((lower - 1, b * lower / (2 * lower + 1)))
        for target, coefficient in terms:
            if target in index:
                matrix[index[target], index[degree]] += coefficient * math.sqrt(
                    (2 * degree + 1) / (2 * target + 1)
                )
    return (matrix + matrix.T) / 2


def build_g04_model(lambda_sq: int, max_degree: int) -> dict[str, Any]:
    lam = math.sqrt(lambda_sq)
    degrees = list(range(0, max_degree + 1, 2))
    c = 2 * math.pi * lambda_sq
    operator = np.diag([degree * (degree + 1) for degree in degrees])
    operator = operator + c * c * legendre_x2_matrix(degrees)
    eigenvalues, eigenvectors = linalg.eigh(
        operator,
        subset_by_index=[0, 4],
        driver="evr",
        check_finite=True,
    )
    for column in range(5):
        if eigenvectors[0, column] < 0:
            eigenvectors[:, column] *= -1

    integrals = eigenvectors[0, :] * math.sqrt(2 * lam)
    g04_mix = np.array([integrals[2], -integrals[0]], dtype=np.float64)
    g04_mix /= np.linalg.norm(g04_mix)
    legendre_coefficients = (
        g04_mix[0] * eigenvectors[:, 0] + g04_mix[1] * eigenvectors[:, 2]
    )
    scaled = legendre_coefficients * np.sqrt(
        (2 * np.asarray(degrees, dtype=np.float64) + 1) / (2 * lam)
    )
    return {
        "degrees": degrees,
        "scaled_g04": scaled,
        "eigenvalues_0_8": eigenvalues,
        "g04_mix": g04_mix,
        "last_ten_legendre_mass": float(np.linalg.norm(legendre_coefficients[-10:])),
    }


def integrate_g04_coefficients(
    lambda_sq: int,
    n_bound: int,
    max_degree: int,
    quad_order: int,
) -> tuple[np.ndarray, dict[str, Any]]:
    """Same g04 -> E-star -> breakpoint Fourier pipeline, in float64 only."""

    model = build_g04_model(lambda_sq, max_degree)
    full_legendre = np.zeros(max_degree + 1, dtype=np.float64)
    full_legendre[::2] = model["scaled_g04"]

    lam = math.sqrt(lambda_sq)
    length = math.log(lambda_sq)
    nodes, weights = np.polynomial.legendre.leggauss(quad_order)
    frequencies = np.arange(-n_bound, n_bound + 1, dtype=np.float64)
    coefficients = np.zeros(2 * n_bound + 1, dtype=np.complex128)
    raw_norm_sq = 0.0

    # Breakpoints x=log(m/j) make floor(m/exp(x)) constant per interval.
    for j in range(lambda_sq, 1, -1):
        left = math.log(lambda_sq / j)
        right = math.log(lambda_sq / (j - 1))
        half = (right - left) / 2
        x = (left + right) / 2 + half * nodes
        quadrature_weights = half * weights
        exp_x = np.exp(x)
        multiplicity = j - 1
        arguments = (
            np.arange(1, multiplicity + 1, dtype=np.float64)[:, None]
            * exp_x[None, :]
            / lambda_sq
        ).ravel()
        starred_sum = legendre.legval(arguments, full_legendre).reshape(
            multiplicity, quad_order
        ).sum(axis=0)
        e_values = np.sqrt(exp_x / lam) * starred_sum
        raw_norm_sq += float(np.dot(quadrature_weights, e_values * e_values))
        phases = np.exp(-2j * math.pi * np.outer(x, frequencies) / length)
        coefficients += (
            (quadrature_weights * e_values) @ phases / math.sqrt(length)
        )

    projected_norm = float(np.linalg.norm(coefficients))
    if not projected_norm > 0:
        raise RuntimeError(f"ZERO_G04_PROJECTION:{lambda_sq}:{n_bound}")
    coefficients /= projected_norm
    return coefficients, {
        "lambda_sq": lambda_sq,
        "lambda": lam,
        "N": n_bound,
        "max_degree": max_degree,
        "quad_order": quad_order,
        "interval_count": lambda_sq - 1,
        "raw_norm_g04": math.sqrt(max(raw_norm_sq, 0.0)),
        "pN_norm_g04": projected_norm,
        "coefficient_norm": float(np.linalg.norm(coefficients)),
        "c0": coefficients[n_bound],
        "prolate_eigenvalues_0_8": model["eigenvalues_0_8"],
        "g04_mix": model["g04_mix"],
        "last_ten_legendre_mass": model["last_ten_legendre_mass"],
    }


def existing_coefficients(lambda_sq: int, n_bound: int) -> tuple[np.ndarray, dict[str, Any]]:
    path = OUT_DIR / f"portable_k_coeffs_lambda_sq_{lambda_sq}_N_{n_bound}.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    coefficients = np.array(
        [complex(float(row["re"]), float(row["im"])) for row in payload["coefficients"]],
        dtype=np.complex128,
    )
    return coefficients, {
        "source": rel(path),
        "source_sha256": sha256(path),
        "source_arithmetic": f"persisted_dps_{payload['dps']}_cast_once_to_float64",
        "coefficient_norm_float64": float(np.linalg.norm(coefficients)),
        "c0_float64": coefficients[n_bound],
    }


def stable_exp_integral(w: np.ndarray, length: float) -> np.ndarray:
    """Return L*expm1(w)/w with its removable value at w=0."""

    result = np.empty_like(w, dtype=np.complex128)
    small = np.abs(w) < 1e-10
    ws = w[small]
    result[small] = length * (1 + ws / 2 + ws * ws / 6 + ws**3 / 24)
    result[~small] = length * np.expm1(w[~small]) / w[~small]
    return result


def completed_tracker_logabs(
    lambda_sq: int,
    n_bound: int,
    coefficients: np.ndarray,
    x_grid: np.ndarray,
    y: float,
) -> np.ndarray:
    """log|gammaC(1/2+iz) Fplus(z)|; division by bDet cancels in R."""

    length = math.log(lambda_sq)
    log_lambda = 0.5 * length
    frequencies = np.arange(-n_bound, n_bound + 1, dtype=np.float64)
    result = np.empty(x_grid.size, dtype=np.float64)
    for start in range(0, x_grid.size, 1024):
        x = x_grid[start : start + 1024]
        z = x + 1j * y
        alpha = z[:, None] + 2 * math.pi * frequencies[None, :] / length
        integrals = stable_exp_integral(1j * alpha * length, length)
        # u=exp(x)/lambda gives the required lambda^(-iz) completion.
        fplus = (
            np.exp(-1j * z * log_lambda)
            * (integrals @ coefficients)
            / math.sqrt(length)
        )
        s = 0.5 + 1j * z
        logabs_gamma_c = (
            math.log(0.5)
            + np.log(np.abs(s))
            + np.log(np.abs(s - 1))
            - 0.5 * np.real(s) * math.log(math.pi)
            + np.real(special.loggamma(s / 2))
        )
        result[start : start + x.size] = np.log(np.abs(fplus)) + logabs_gamma_c
    return result


def coefficient_payload(
    coefficients: np.ndarray,
    metadata: dict[str, Any],
    convergence: dict[str, Any],
) -> dict[str, Any]:
    lambda_sq = int(metadata["lambda_sq"])
    n_bound = int(metadata["N"])
    rows = [
        {
            "n": n,
            "re": repr(float(value.real)),
            "im": repr(float(value.imag)),
            "abs": repr(float(abs(value))),
        }
        for n, value in zip(range(-n_bound, n_bound + 1), coefficients)
    ]
    return {
        "schema": "route_b_off_axis_k1_float64.v1",
        "status": "DIAGNOSTIC_ONLY_NOT_CANONICAL_SOURCE",
        "lambda_sq": lambda_sq,
        "lambda": math.sqrt(lambda_sq),
        "L_m": math.log(lambda_sq),
        "N": n_bound,
        "logical_vector": "k1=kTrial",
        "packet": "g04",
        "arithmetic": "IEEE754_BINARY64_ONLY_NO_DPS_ESCALATION",
        "constructor": "g04_prolate_legendre_then_breakpoint_E_star_then_Fourier",
        "integer_breakpoints": "x=log(lambda_sq/j), j=lambda_sq,...,1",
        "operator_prime_support_note": (
            "primes and prime powers <= lambda_sq are recorded for same-cell provenance; "
            "D0.7e.2 tracker evaluation itself does not consume the Weil matrix prime term"
        ),
        "primes_le_m": primes_up_to(lambda_sq),
        "prime_powers_le_m": prime_powers_up_to(lambda_sq),
        "metadata": metadata,
        "convergence": convergence,
        "coefficients": rows,
        "rh_status": "NOT_RH",
    }


def run_probe() -> tuple[dict[str, Any], dict[tuple[int, int], dict[str, Any]]]:
    state = json.loads(STATE.read_text(encoding="utf-8"))
    node = state["nodes"]["D0.7e.5a"]
    if node["proof_status"] != "BLOCKED" or node["activity"] != "ACTIVE":
        raise RuntimeError("D0_7E_5A_STATE_CHANGED_BEFORE_PROBE")
    bus_dir = LADDER_DIR / "bus"
    if list(bus_dir.glob("010_*")):
        raise RuntimeError("BUS_010_PRESENT_BEFORE_PROBE")

    zero_payload = json.loads(ZERO_SOURCE.read_text(encoding="utf-8"))
    gamma_1 = float(zero_payload["zeros"][0]["gamma"])
    gamma_11 = float(zero_payload["zeros"][10]["gamma"])
    x_grid = np.linspace(gamma_1, gamma_11, X_GRID_COUNT, dtype=np.float64)

    coefficients: dict[tuple[int, int], np.ndarray] = {}
    source_metadata: dict[tuple[int, int], dict[str, Any]] = {}
    new_payloads: dict[tuple[int, int], dict[str, Any]] = {}

    for cell in EXISTING_CELLS:
        coefficients[cell], source_metadata[cell] = existing_coefficients(*cell)

    # Validate the float64 reconstruction against the locked (13,120) vector.
    validation_low, _ = integrate_g04_coefficients(13, 120, 180, QUAD_LOW)
    validation_high, validation_meta = integrate_g04_coefficients(13, 120, 180, QUAD_HIGH)
    persisted_13_120 = coefficients[(13, 120)]
    constructor_validation = {
        "cell": [13, 120],
        "max_abs_q64_vs_q128": float(np.max(np.abs(validation_low - validation_high))),
        "max_abs_q128_vs_persisted_cast": float(
            np.max(np.abs(validation_high - persisted_13_120))
        ),
        "q128_metadata": validation_meta,
    }

    for lambda_sq, n_bound in NEW_CELLS:
        degree = MODEL_DEGREES[lambda_sq]
        compare_degree = MODEL_COMPARE_DEGREES[lambda_sq]
        low_q, _ = integrate_g04_coefficients(lambda_sq, n_bound, degree, QUAD_LOW)
        final, final_metadata = integrate_g04_coefficients(
            lambda_sq, n_bound, degree, QUAD_HIGH
        )
        degree_compare, _ = integrate_g04_coefficients(
            lambda_sq, n_bound, compare_degree, QUAD_HIGH
        )
        convergence = {
            "max_abs_q64_vs_q128": float(np.max(np.abs(low_q - final))),
            "max_abs_compare_degree_vs_final_degree": float(
                np.max(np.abs(degree_compare - final))
            ),
            "compare_degree": compare_degree,
            "final_degree": degree,
            "quad_low": QUAD_LOW,
            "quad_high": QUAD_HIGH,
        }
        coefficients[(lambda_sq, n_bound)] = final
        source_metadata[(lambda_sq, n_bound)] = {
            "source": "fresh_float64_breakpoint_constructor",
            "source_arithmetic": "IEEE754_BINARY64_ONLY_NO_DPS_ESCALATION",
            "coefficient_norm_float64": float(np.linalg.norm(final)),
            "c0_float64": final[n_bound],
            "convergence": convergence,
        }
        new_payloads[(lambda_sq, n_bound)] = coefficient_payload(
            final, final_metadata, convergence
        )

    cells: list[dict[str, Any]] = []
    for lambda_sq, n_bound in (*EXISTING_CELLS, *NEW_CELLS):
        coeffs = coefficients[(lambda_sq, n_bound)]
        base = completed_tracker_logabs(
            lambda_sq, n_bound, coeffs, x_grid, 0.0
        )
        base_index = int(np.argmax(base))
        base_sup_log = float(base[base_index])
        ratios: dict[str, Any] = {}
        for y in Y_GRID:
            values = completed_tracker_logabs(
                lambda_sq, n_bound, coeffs, x_grid, y
            )
            index = int(np.argmax(values))
            sup_log = float(values[index])
            ratios[f"{y:.1f}"] = {
                "R": math.exp(sup_log - base_sup_log),
                "log_R": sup_log - base_sup_log,
                "x_argmax": float(x_grid[index]),
                "numerator_log_sup": sup_log,
            }
        c0 = coeffs[n_bound]
        bdet = math.sqrt(math.log(lambda_sq)) * float(c0.real) / ZETA_HALF_FLOAT64
        cells.append(
            {
                "lambda_sq": lambda_sq,
                "lambda": math.sqrt(lambda_sq),
                "L_m": math.log(lambda_sq),
                "N": n_bound,
                "source": source_metadata[(lambda_sq, n_bound)],
                "c0_float64": c0,
                "bDet_float64_nonzero_check": bdet,
                "denominator": {
                    "log_sup": base_sup_log,
                    "x_argmax": float(x_grid[base_index]),
                },
                "ratios": ratios,
            }
        )

    by_cell = {(row["lambda_sq"], row["N"]): row for row in cells}
    fit_x = np.array([math.log(m) for m, _ in FIT_CELLS], dtype=np.float64)
    fit_y = np.array(
        [by_cell[cell]["ratios"]["0.3"]["log_R"] for cell in FIT_CELLS],
        dtype=np.float64,
    )
    design = np.column_stack([np.ones_like(fit_x), fit_x])
    intercept, slope = np.linalg.lstsq(design, fit_y, rcond=None)[0]
    fitted = intercept + slope * fit_x
    residuals = fit_y - fitted
    sse = float(np.dot(residuals, residuals))
    sst = float(np.dot(fit_y - fit_y.mean(), fit_y - fit_y.mean()))
    slope_stderr = math.sqrt(
        (sse / (fit_x.size - 2)) / float(np.dot(fit_x - fit_x.mean(), fit_x - fit_x.mean()))
    )
    if slope <= 0.03:
        verdict = "OFF_AXIS_PROBE_NONDECISIVE_FALSIFIER_PASS"
    elif slope >= 0.10:
        verdict = "SOFT_ROUTE_DEAD_RAW"
    else:
        verdict = "EXTEND_M"

    result = {
        "schema": "route_b_off_axis_growth_probe.v1",
        "task": "OffAxisGrowthProbe",
        "status": "COMPLETE_DIAGNOSTIC_ONLY",
        "verdict_code": verdict,
        "rh_status": "NOT_RH",
        "arithmetic": {
            "dtype": "float64/complex128",
            "dps_escalation": False,
            "numpy": np.__version__,
            "scipy": __import__("scipy").__version__,
            "python": sys.version.split()[0],
            "platform": platform.platform(),
        },
        "object_lock": {
            "object": "G_m_N=Fhat_m_N/bDet_m_N on BDetNonzero",
            "formula": (
                "Fhat(z)=gammaC(1/2+i*z)*lambda^(-i*z)/sqrt(L)"
                "*sum_n c_n*integral_0^L exp(i*(z+2*pi*n/L)*x) dx"
            ),
            "ratio_cancellation": "bDet is independent of x,y and cancels exactly in R",
            "d0_7e_source": rel(REQUEST_DIR / "D0_7E_CENTRAL_MELLIN_CALIBRATION.md"),
            "d0_7e_source_sha256": sha256(
                REQUEST_DIR / "D0_7E_CENTRAL_MELLIN_CALIBRATION.md"
            ),
        },
        "window": {
            "source": rel(ZERO_SOURCE),
            "source_sha256": sha256(ZERO_SOURCE),
            "definition": "[gamma_1,gamma_11], exactly ten empirical mean zero spacings",
            "x_min": gamma_1,
            "x_max": gamma_11,
            "mean_spacing": (gamma_11 - gamma_1) / 10,
            "width": gamma_11 - gamma_1,
            "grid_count": X_GRID_COUNT,
            "grid_step": float(x_grid[1] - x_grid[0]),
            "y_grid": list(Y_GRID),
        },
        "new_cell_policy": {
            "N": 120,
            "classification": "FIXED_DIAGNOSTIC_N_NOT_A_SELECTOR_N_OF_LAMBDA",
            "cells": [list(cell) for cell in NEW_CELLS],
            "prime_support": "primes and prime powers <= m recorded in new coefficient payloads",
        },
        "constructor_validation": constructor_validation,
        "cells": cells,
        "fit": {
            "response": "log R(0.3;m)",
            "predictor": "L_m=log(m)",
            "cells": [list(cell) for cell in FIT_CELLS],
            "duplicate_m_policy": "use N=120 once; (13,90) is an N-stability probe",
            "method": "ordinary least squares with intercept",
            "slope": float(slope),
            "slope_standard_error": slope_stderr,
            "intercept": float(intercept),
            "r_squared": 1 - sse / sst if sst else 1.0,
            "registered_thresholds": {
                "slope_le_0.03": "OFF_AXIS_PROBE_NONDECISIVE_FALSIFIER_PASS",
                "slope_ge_0.10": "SOFT_ROUTE_DEAD_RAW",
                "otherwise": "EXTEND_M",
            },
        },
        "interpretation_lock": {
            "classification": "NONDECISIVE_FALSIFIER_ONLY",
            "meaning": "registered sampled raw blow-up threshold did not fire",
            "completion_class_invariant": False,
            "gauge_rule": "multiplication by lambda^(-i*c*z) multiplies R(y;m) by lambda^(c*y) and shifts the L_m slope by c*y/2",
            "slope_y_0_3_extra_lambda_phase": float(slope + 0.15),
            "slope_y_0_3_inverse_lambda_phase": float(slope - 0.15),
            "does_not_prove": ["LOCAL_NORMALITY", "S2_IDENTIFICATION", "RH"],
        },
        "next_normalization_policy": {
            "code": "CENTRAL_ANCHOR_NORMALIZATION_LOCKED",
            "formula": "F_j(z)=Xi(0)/Ghat_j(0)*Ghat_j(z) on Ghat_j(0)!=0",
            "anchor": "F_j(0)=Xi(0)!=0",
            "forbidden": "PER_COMPACT_OR_STRIP_SUP_NORMALIZATION",
        },
        "control_plane_guards": {
            "state_revision_observed": state["revision"],
            "D0.7e.5a_proof_status": node["proof_status"],
            "D0.7e.5a_activity": node["activity"],
            "mint_activated": False,
            "bus_010_created": False,
            "state_mutated": False,
        },
        "explicit_nonclaims": [
            "NO_ASYMPTOTIC_LAW",
            "NO_COMPLETION_CLASS_INVARIANCE",
            "NO_LOCAL_NORMALITY_FROM_PROBE",
            "NO_S2_IDENTIFICATION_FROM_PROBE",
            "NO_H3E_CLOSURE",
            "NO_WPRIME_MINT",
            "NO_D0_7E_5A_CLOSURE",
            "NO_N_OF_LAMBDA_SELECTOR",
            "NO_BUS_010",
            "NO_RH",
        ],
    }
    return result, new_payloads


def csv_text(result: dict[str, Any]) -> str:
    stream = io.StringIO()
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow(
        [
            "lambda_sq",
            "N",
            "L_m",
            "R_0_1",
            "R_0_2",
            "R_0_3",
            "R_0_4",
            "x_argmax_0_1",
            "x_argmax_0_2",
            "x_argmax_0_3",
            "x_argmax_0_4",
        ]
    )
    for cell in result["cells"]:
        ratios = cell["ratios"]
        writer.writerow(
            [
                cell["lambda_sq"],
                cell["N"],
                repr(cell["L_m"]),
                *[repr(ratios[f"{y:.1f}"]["R"]) for y in Y_GRID],
                *[repr(ratios[f"{y:.1f}"]["x_argmax"]) for y in Y_GRID],
            ]
        )
    return stream.getvalue()


def markdown_text(result: dict[str, Any]) -> str:
    lines = [
        "# OffAxisGrowthProbe — D0.7e.2 completed tracker",
        "",
        "Status: `COMPLETE_DIAGNOSTIC_ONLY / NOT_RH`.",
        f"Verdict: `{result['verdict_code']}`.",
        "",
        "The computation is IEEE-754 float64/complex128 only. The normalized",
        "tracker is evaluated with both the `lambda^(-iz)` phase and",
        "`gammaC(1/2+iz)` completion. The constant `bDet` cancels in `R`.",
        "This verdict means only that the registered sampled falsifier did not",
        "fire; it is not a proof that the soft route is alive.",
        "",
        "| m | N | R(0.1) | R(0.2) | R(0.3) | R(0.4) |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for cell in result["cells"]:
        ratios = cell["ratios"]
        lines.append(
            "| {m} | {n} | `{r1:.12g}` | `{r2:.12g}` | `{r3:.12g}` | `{r4:.12g}` |".format(
                m=cell["lambda_sq"],
                n=cell["N"],
                r1=ratios["0.1"]["R"],
                r2=ratios["0.2"]["R"],
                r3=ratios["0.3"]["R"],
                r4=ratios["0.4"]["R"],
            )
        )
    fit = result["fit"]
    lines.extend(
        [
            "",
            f"OLS slope `d log R(0.3;m) / d L_m = {fit['slope']:.12g}` ",
            f"(standard error `{fit['slope_standard_error']:.4g}`, R2 `{fit['r_squared']:.8g}`).",
            "The fit uses one `N=120` cell per distinct m; `(13,90)` is the",
            "N-stability duplicate and is not double-weighted.",
            "",
            "The window is `[gamma_1,gamma_11]` from the persisted zero cache,",
            "exactly ten empirical mean spacings. New cells `(53,120)` and",
            "`(101,120)` use the same g04 -> E-star breakpoint -> Fourier",
            "pipeline in float64; fixed N=120 is diagnostic, not an N(lambda)",
            "selector. Their prime/prime-power support through m is recorded",
            "for provenance but is not consumed by the D0.7e.2 tracker itself.",
            "",
            "The statistic is not invariant under the zero-free completion class:",
            "multiplication by `lambda^(-i*c*z)` shifts the fitted slope by",
            "`c*y/2` without changing zeros. The next theorem-facing family must",
            "use the fixed central anchor `F_j(0)=Xi(0)!=0`, never a sup norm.",
            "",
            "`D0.7e.5a` remains BLOCKED/ACTIVE; mint inactive; no Bus 010.",
        ]
    )
    return "\n".join(lines) + "\n"


def write_outputs(
    result: dict[str, Any],
    new_payloads: dict[tuple[int, int], dict[str, Any]],
) -> None:
    for (lambda_sq, n_bound), payload in new_payloads.items():
        path = OUT_DIR / (
            f"off_axis_k1_coeffs_lambda_sq_{lambda_sq}_N_{n_bound}_float64.json"
        )
        path.write_text(
            json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        result.setdefault("generated_coefficient_artifacts", []).append(
            {"path": rel(path), "sha256": sha256(path)}
        )
    RESULT_CSV.write_text(csv_text(result), encoding="utf-8")
    result["raw_csv"] = {"path": rel(RESULT_CSV), "sha256": sha256(RESULT_CSV)}
    RESULT_MD.write_text(markdown_text(result), encoding="utf-8")
    result["report"] = {"path": rel(RESULT_MD), "sha256": sha256(RESULT_MD)}
    RESULT_JSON.write_text(
        json.dumps(json_safe(result), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result, new_payloads = run_probe()
    if args.write:
        write_outputs(result, new_payloads)
    print(json.dumps(json_safe(result), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
