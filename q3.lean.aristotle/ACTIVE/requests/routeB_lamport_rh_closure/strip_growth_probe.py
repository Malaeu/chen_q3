#!/usr/bin/env python3
"""Float64 STRIP_GROWTH probe for the SOFT-1 bare transform.

Computes |B_(m,120)(-i)| and |B_(m,120)(-i/4)| for every integer
13 <= m <= 257.  This is diagnostic only: it does not mutate STATE, choose an
N(m), create Bus 010, or promote a fitted exponent to a theorem.
"""

from __future__ import annotations

import csv
import json
import math
import platform
import sys
from pathlib import Path
from typing import Any

import numpy as np
from scipy import linalg

import off_axis_growth_probe as base


REQUEST_DIR = Path(__file__).resolve().parent
RESULT_JSON = REQUEST_DIR / "STRIP_GROWTH_PROBE.json"
RESULT_CSV = REQUEST_DIR / "STRIP_GROWTH_PROBE.csv"
RESULT_MD = REQUEST_DIR / "STRIP_GROWTH_PROBE.md"

M_MIN = 13
M_MAX = 257
N_BOUND = 120
QUAD_ORDER = 128
H_GRID_COUNT = 32769
Z_OUTSIDE = -1j
Z_INSIDE = -0.25j


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


def model_degree(m: int) -> int:
    """Even Legendre cutoff; dominates the previously validated cutoffs."""

    return max(180, 2 * math.ceil(6 * m))


def legendre_x2_tridiagonal(degrees: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Matrix of x^2 in the normalized even Legendre basis."""

    diagonal = (degrees + 1) ** 2 / (
        (2 * degrees + 1) * (2 * degrees + 3)
    )
    positive = degrees > 0
    d = degrees[positive]
    diagonal[positive] += d**2 / ((2 * d + 1) * (2 * d - 1))

    lower = degrees[:-1]
    off_diagonal = (
        (lower + 1)
        * (lower + 2)
        / ((2 * lower + 1) * (2 * lower + 3))
        * np.sqrt((2 * lower + 1) / (2 * lower + 5))
    )
    return diagonal, off_diagonal


def h_trial_grid(m: int, degree: int) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    """D0 hTrial from the h_0/h_4 prolate modes, sampled in x/lambda."""

    degrees = np.arange(0, degree + 1, 2, dtype=np.float64)
    c = 2 * math.pi * m
    x2_diag, x2_off = legendre_x2_tridiagonal(degrees)
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
    integrals = eigenvectors[0, :] * math.sqrt(2 * lam)
    mix = np.array([integrals[2], -integrals[0]], dtype=np.float64)
    mix /= np.linalg.norm(mix)
    legendre_coefficients = (
        mix[0] * eigenvectors[:, 0] + mix[1] * eigenvectors[:, 2]
    )
    scaled = legendre_coefficients * np.sqrt((2 * degrees + 1) / (2 * lam))
    full = np.zeros(degree + 1, dtype=np.float64)
    full[::2] = scaled

    grid = np.linspace(0.0, 1.0, H_GRID_COUNT, dtype=np.float64)
    values = np.polynomial.legendre.legval(grid, full)
    return grid, values, {
        "degree": degree,
        "last_ten_legendre_mass": float(
            np.linalg.norm(legendre_coefficients[-10:])
        ),
        "eigenvalues_0_8": eigenvalues,
        "mix_h0_h4": mix,
    }


def coefficients(m: int, quad_order: int = QUAD_ORDER) -> tuple[np.ndarray, dict[str, Any]]:
    """Breakpoint Gauss integration of gTrial followed by P_(m,N)."""

    degree = model_degree(m)
    h_grid, h_values, metadata = h_trial_grid(m, degree)
    lam = math.sqrt(m)
    length = math.log(m)
    nodes, weights = np.polynomial.legendre.leggauss(quad_order)
    frequencies = np.arange(-N_BOUND, N_BOUND + 1, dtype=np.float64)
    result = np.zeros(2 * N_BOUND + 1, dtype=np.complex128)

    for j in range(m, 1, -1):
        left = math.log(m / j)
        right = math.log(m / (j - 1))
        half = (right - left) / 2
        x = (left + right) / 2 + half * nodes
        quadrature_weights = half * weights
        exp_x = np.exp(x)
        multiplicity = j - 1
        arguments = (
            np.arange(1, multiplicity + 1, dtype=np.float64)[:, None]
            * exp_x[None, :]
            / m
        )
        starred_sum = np.interp(
            arguments.ravel(), h_grid, h_values
        ).reshape(multiplicity, quad_order).sum(axis=0)
        e_values = np.sqrt(exp_x / lam) * starred_sum
        phases = np.exp(
            -2j * math.pi * np.outer(x, frequencies) / length
        )
        result += (
            (quadrature_weights * e_values) @ phases / math.sqrt(length)
        )

    projected_norm = float(np.linalg.norm(result))
    if not projected_norm > 0:
        raise RuntimeError(f"ZERO_G04_PROJECTION:{m}:{N_BOUND}")
    result /= projected_norm
    metadata.update(
        {
            "quad_order": quad_order,
            "projected_norm_before_normalization": projected_norm,
            "coefficient_norm": float(np.linalg.norm(result)),
        }
    )
    return result, metadata


def bare_transform(m: int, coeff: np.ndarray, z: complex) -> complex:
    """B(z)=lambda^(iz)Fplus(z), with the lambda^(-iz) phase cancelled."""

    length = math.log(m)
    frequencies = np.arange(-N_BOUND, N_BOUND + 1, dtype=np.float64)
    alpha = z + 2 * math.pi * frequencies / length
    integrals = base.stable_exp_integral(1j * alpha * length, length)
    return complex(integrals @ coeff / math.sqrt(length))


def fit(rows: list[dict[str, Any]], key: str) -> dict[str, Any]:
    x = np.log(np.array([row["m"] for row in rows], dtype=np.float64))
    y = np.log(np.array([row[key] for row in rows], dtype=np.float64))
    design = np.column_stack([np.ones(x.size), x])
    intercept, beta = np.linalg.lstsq(design, y, rcond=None)[0]
    fitted = design @ np.array([intercept, beta])
    residual = y - fitted
    sse = float(residual @ residual)
    centered = y - y.mean()
    sst = float(centered @ centered)
    sigma2 = sse / (x.size - 2)
    beta_stderr = math.sqrt(
        sigma2 / float(((x - x.mean()) ** 2).sum())
    )
    return {
        "model": f"log({key}) = intercept + beta*log(m)",
        "intercept": float(intercept),
        "prefactor": math.exp(float(intercept)),
        "beta": float(beta),
        "beta_standard_error": beta_stderr,
        "r_squared": 1 - sse / sst if sst else 1.0,
        "min": min(float(row[key]) for row in rows),
        "max": max(float(row[key]) for row in rows),
        "endpoint_ratio_257_over_13": float(rows[-1][key] / rows[0][key]),
    }


def run() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    tail_masses: list[float] = []
    for m in range(M_MIN, M_MAX + 1):
        coeff, metadata = coefficients(m)
        outside = bare_transform(m, coeff, Z_OUTSIDE)
        inside = bare_transform(m, coeff, Z_INSIDE)
        tail_masses.append(float(metadata["last_ten_legendre_mass"]))
        rows.append(
            {
                "m": m,
                "N": N_BOUND,
                "abs_B_minus_i": abs(outside),
                "abs_B_minus_i_over_4": abs(inside),
                "B_minus_i": outside,
                "B_minus_i_over_4": inside,
                "model_degree": int(metadata["degree"]),
                "last_ten_legendre_mass": metadata[
                    "last_ten_legendre_mass"
                ],
            }
        )
        if m == M_MIN or m == M_MAX or m % 16 == 0:
            print(
                f"[STRIP_GROWTH] m={m}/{M_MAX} "
                f"|B(-i)|={abs(outside):.9g} "
                f"|B(-i/4)|={abs(inside):.9g}",
                flush=True,
            )

    fit_outside = fit(rows, "abs_B_minus_i")
    fit_inside = fit(rows, "abs_B_minus_i_over_4")
    growth_confirmed = (
        fit_outside["beta"] > 0.05
        and fit_outside["endpoint_ratio_257_over_13"] > 2
    )
    verdict = "UNIV_GROWTH_CONFIRMED" if growth_confirmed else "UNIV_SAFE"

    # Independent checks at the low anchor and at three points across the grid.
    persisted_13, _ = base.existing_coefficients(13, N_BOUND)
    computed_13, _ = coefficients(13)
    convergence: dict[str, Any] = {
        "max_abs_coeff_m13_vs_persisted": float(
            np.max(np.abs(computed_13 - persisted_13))
        ),
        "anchors_q64_vs_q128": {},
        "max_last_ten_legendre_mass": max(tail_masses),
    }
    by_m = {row["m"]: row for row in rows}
    for m in (13, 101, 257):
        q64, _ = coefficients(m, 64)
        q128, _ = coefficients(m, 128)
        convergence["anchors_q64_vs_q128"][str(m)] = {
            "max_abs_coeff": float(np.max(np.abs(q64 - q128))),
            "abs_B_minus_i": abs(
                bare_transform(m, q64, Z_OUTSIDE)
                - bare_transform(m, q128, Z_OUTSIDE)
            ),
            "abs_B_minus_i_over_4": abs(
                bare_transform(m, q64, Z_INSIDE)
                - bare_transform(m, q128, Z_INSIDE)
            ),
            "reported_abs_B_minus_i": by_m[m]["abs_B_minus_i"],
        }

    return {
        "schema": "route_b_strip_growth_probe.v1",
        "status": "COMPLETE_DIAGNOSTIC_ONLY",
        "verdict": verdict,
        "arithmetic": {
            "dtype": "float64/complex128",
            "numpy": np.__version__,
            "scipy": __import__("scipy").__version__,
            "python": sys.version.split()[0],
            "platform": platform.platform(),
        },
        "grid": {
            "m": [M_MIN, M_MAX, "all integers inclusive"],
            "N": N_BOUND,
            "z_outside": "-i",
            "z_inside_control": "-i/4",
            "quad_order_per_breakpoint_interval": QUAD_ORDER,
            "h_trial_interpolation_grid": H_GRID_COUNT,
        },
        "object": (
            "B_(m,N)(z)=1/sqrt(L_m)*sum_n c_n*"
            "integral_0^L exp(i(z+2*pi*n/L)x)dx"
        ),
        "rows": rows,
        "fit": {
            "outside_minus_i": fit_outside,
            "inside_minus_i_over_4": fit_inside,
        },
        "convergence": convergence,
        "memlp": (
            "YES_IF_MEASURABLE: bounded compact support on a finite-measure "
            "window implies L2; Lean still needs measurability/boundedness "
            "certificates for the midpoint prolate representative."
        ),
        "control_plane": {
            "state_mutated": False,
            "bus_010_created": False,
            "rh_status": "NOT_RH",
        },
        "explicit_nonclaims": [
            "NO_ASYMPTOTIC_LAW_FROM_FINITE_FIT",
            "NO_SKELETON_EDIT_BEFORE_MYTHOS_SCORING",
            "NO_STATE_MUTATION",
            "NO_BUS_010",
            "NO_RH",
        ],
    }


def write(result: dict[str, Any]) -> None:
    RESULT_JSON.write_text(
        json.dumps(json_safe(result), indent=2) + "\n", encoding="utf-8"
    )
    with RESULT_CSV.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "m",
                "N",
                "abs_B_minus_i",
                "abs_B_minus_i_over_4",
                "model_degree",
                "last_ten_legendre_mass",
            ]
        )
        for row in result["rows"]:
            writer.writerow(
                [
                    row["m"],
                    row["N"],
                    f"{row['abs_B_minus_i']:.17g}",
                    f"{row['abs_B_minus_i_over_4']:.17g}",
                    row["model_degree"],
                    f"{row['last_ten_legendre_mass']:.17g}",
                ]
            )

    lines = [
        "# STRIP_GROWTH_PROBE",
        "",
        "Status: `DIAGNOSTIC_ONLY / FLOAT64 / NOT_RH`.",
        f"Verdict: `{result['verdict']}`.",
        "",
        "| m | N | |B(-i)| | |B(-i/4)| |",
        "|---:|---:|---:|---:|",
    ]
    for row in result["rows"]:
        lines.append(
            f"| {row['m']} | {row['N']} | "
            f"`{row['abs_B_minus_i']:.12g}` | "
            f"`{row['abs_B_minus_i_over_4']:.12g}` |"
        )
    outside = result["fit"]["outside_minus_i"]
    inside = result["fit"]["inside_minus_i_over_4"]
    lines.extend(
        [
            "",
            "Fits:",
            "",
            "```text",
            f"|B(-i)| ~= {outside['prefactor']:.12g} * m^({outside['beta']:.12g})",
            f"beta stderr = {outside['beta_standard_error']:.6g}",
            f"R^2 = {outside['r_squared']:.12g}",
            f"endpoint ratio = {outside['endpoint_ratio_257_over_13']:.12g}",
            "",
            f"|B(-i/4)| ~= {inside['prefactor']:.12g} * m^({inside['beta']:.12g})",
            f"beta stderr = {inside['beta_standard_error']:.6g}",
            f"R^2 = {inside['r_squared']:.12g}",
            f"endpoint ratio = {inside['endpoint_ratio_257_over_13']:.12g}",
            "```",
            "",
            "MemLp: `YES_IF_MEASURABLE` — bounded compact support on the",
            "finite-measure window implies L2; Lean needs the explicit",
            "measurability/boundedness certificates.",
            "",
            "STATE unchanged. Bus 010 absent.",
        ]
    )
    RESULT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    result = run()
    write(result)
    print(
        json.dumps(
            {
                "verdict": result["verdict"],
                "fit": result["fit"],
                "convergence": result["convergence"],
                "result": str(RESULT_JSON),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
