#!/usr/bin/env python3
"""Binary64 pilot for the split H2a penalty certificate.

This is a diagnostic finite-matrix run.  It rebuilds the source-locked full
Weil matrix ``Mfin_(m,N)=WeilMat_(m,N)`` on a registered small grid, computes
the even/odd sector spectra, and tests

    K - beta G + tau (Gq)(Gq)* >= 0

with ``G=I``, ``K=Mfin``, ``q`` the numerical even ground vector,
``beta=(lambda1+lambda2)/2``, and ``tau=lambda2-lambda1``.

The output is not an exact certificate and never discharges
``ExactSectorOrdering``.

Run:

  uv run --no-project --with numpy --with scipy --with tqdm \
    python h2a_cert_split_pilot.py --write
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from pathlib import Path
from typing import Any

import numpy as np
from scipy import special
from tqdm import tqdm


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
JSON_OUT = HERE / "H2A_CERT_SPLIT_PILOT.json"
REPORT_OUT = HERE / "H2A_CERT_SPLIT_PILOT_REPORT_2026-07-25.md"
STATE = HERE / "STATE.json"
BUS = HERE.parent / "routeB_twolevel_spectral_ladder" / "bus"

# Registered before the final run.  N=5 is already near the binary64
# eigengap floor, so the pilot deliberately stops at N=4.
CELLS = tuple((m, n) for m in (12, 13, 14) for n in (2, 3, 4))
QUAD_ORDER = 256
ROUND_GUARD_MULTIPLIER = 128.0


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, np.ndarray):
        return json_safe(value.tolist())
    if isinstance(value, np.generic):
        return value.item()
    return value


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))


def prime_powers_up_to(limit: int) -> list[tuple[int, float]]:
    result: list[tuple[int, float]] = []
    for k in range(2, limit + 1):
        for prime in range(2, k + 1):
            if not is_prime(prime):
                continue
            power = prime
            while power < k:
                power *= prime
            if power == k:
                result.append((k, math.log(prime)))
                break
    return result


def hyp2f1_one_a_a1(a: complex, z: float) -> complex:
    """Return 2F1(1,a;a+1;z) using a binary64 series."""

    total = 0.0j
    z_power = 1.0
    for k in range(64):
        term = z_power / (a + k)
        total += term
        if abs(a * term) <= 8 * np.finfo(np.float64).eps:
            break
        z_power *= z
    return a * total


def lerch_phi_s2(a: complex, z: float) -> complex:
    """Return Phi(z,2,a) using its rapidly convergent series."""

    total = 0.0j
    z_power = 1.0
    for k in range(64):
        term = z_power / (a + k) ** 2
        total += term
        if abs(term) <= 8 * np.finfo(np.float64).eps:
            break
        z_power *= z
    return total


def trigamma_complex(a: complex) -> complex:
    """Binary64 trigamma by recurrence plus its asymptotic expansion."""

    total = 0.0j
    x = complex(a)
    while x.real < 24:
        total += 1 / x**2
        x += 1
    inv = 1 / x
    inv2 = inv * inv
    return (
        total
        + inv
        + inv2 / 2
        + inv * inv2 / 6
        - inv * inv2**2 / 30
        + inv * inv2**3 / 42
        - inv * inv2**4 / 30
        + 5 * inv * inv2**5 / 66
    )


def coefficient_tables(m: int, n_bound: int) -> tuple[float, np.ndarray, np.ndarray, np.ndarray]:
    """Float64 alpha/beta/gamma tables used by the locked Weil matrix."""

    length = math.log(m)
    z = math.exp(-2 * length)
    exp_half = math.exp(-length / 2)

    nodes, weights = np.polynomial.legendre.leggauss(QUAD_ORDER)
    x = (nodes + 1) * length / 2
    w = weights * length / 2
    rho = np.exp(1.5 * x) / np.expm1(2 * x)
    exp_correction = float(w @ ((1 - np.exp(-x / 2)) * rho))
    constant = 0.5 * (
        np.euler_gamma + math.log(4 * math.pi * (m - 1) / (m + 1))
    )
    h0 = hyp2f1_one_a_a1(0.25, z).real

    alpha = np.zeros(n_bound + 1, dtype=np.float64)
    beta = np.zeros(n_bound + 1, dtype=np.float64)
    gamma = np.zeros(n_bound + 1, dtype=np.float64)
    beta[0] = float(w @ (x * rho) / length)
    gamma[0] = exp_correction + constant

    for n in range(1, n_bound + 1):
        a = 0.25 + 1j * math.pi * n / length
        hyp = hyp2f1_one_a_a1(a, z)
        alpha[n] = (
            exp_half * ((2 * length / (length + 4j * math.pi * n)) * hyp).imag
            + 0.5 * special.digamma(a).imag
        ) / math.pi
        beta[n] = (
            -length
            * exp_half
            * ((2 * length / (4 * math.pi * n - 1j * length)) * hyp).imag
            - exp_half * lerch_phi_s2(a, z).real / 4
            + trigamma_complex(a).real / 4
        ) / length
        gamma[n] = (
            -exp_half
            * ((2 * length / (length + 4j * math.pi * n)) * hyp).real
            + 2 * exp_half * h0
            - 0.5 * (special.digamma(a).real - special.digamma(0.25))
            + exp_correction
            + constant
        )
    return length, alpha, beta, gamma


def build_weil_matrix(m: int, n_bound: int) -> tuple[np.ndarray, dict[str, float]]:
    """Build the full real-symmetric Weil matrix in IEEE-754 binary64."""

    length, alpha_pos, beta_pos, gamma_pos = coefficient_tables(m, n_bound)
    modes = np.arange(-n_bound, n_bound + 1)
    row = modes[:, None]
    col = modes[None, :]
    difference = row - col
    diagonal = row == col

    w02 = (
        32
        * length
        * math.sinh(length / 4) ** 2
        * (length**2 - 16 * math.pi**2 * row * col)
        / (
            (length**2 + 16 * math.pi**2 * row**2)
            * (length**2 + 16 * math.pi**2 * col**2)
        )
    )

    alpha = np.sign(modes) * alpha_pos[np.abs(modes)]
    wr = np.empty_like(w02, dtype=np.float64)
    wr[diagonal] = 2 * gamma_pos[np.abs(modes)] - 2 * beta_pos[np.abs(modes)]
    wr[~diagonal] = (alpha[None, :] - alpha[:, None])[~diagonal] / difference[~diagonal]

    prime = np.zeros_like(w02, dtype=np.float64)
    for k, mangoldt in prime_powers_up_to(m):
        y = math.log(k)
        q = np.empty_like(w02, dtype=np.float64)
        q[diagonal] = (
            2
            * (1 - y / length)
            * np.cos(2 * math.pi * modes * y / length)
        )
        q[~diagonal] = (
            np.sin(2 * math.pi * col * y / length)
            - np.sin(2 * math.pi * row * y / length)
        )[~diagonal] / (math.pi * difference[~diagonal])
        prime += mangoldt / math.sqrt(k) * q

    raw = w02 - wr - prime
    symmetry_error = float(np.max(np.abs(raw - raw.T)))
    parity_error = float(np.max(np.abs(raw - raw[::-1, ::-1])))

    # Both identities are exact in the source.  Their average only removes
    # binary64 evaluation-order noise and is recorded as a diagnostic.
    matrix = (raw + raw.T + raw[::-1, ::-1] + raw[::-1, ::-1].T) / 4
    correction = float(np.max(np.abs(matrix - raw)))
    return matrix, {
        "raw_symmetry_error": symmetry_error,
        "raw_parity_error": parity_error,
        "exact_identity_roundoff_correction": correction,
    }


def sector_bases(n_bound: int) -> tuple[np.ndarray, np.ndarray]:
    size = 2 * n_bound + 1
    even = np.zeros((size, n_bound + 1), dtype=np.float64)
    odd = np.zeros((size, n_bound), dtype=np.float64)
    even[n_bound, 0] = 1
    for k in range(1, n_bound + 1):
        even[n_bound - k, k] = 1 / math.sqrt(2)
        even[n_bound + k, k] = 1 / math.sqrt(2)
        odd[n_bound - k, k - 1] = 1 / math.sqrt(2)
        odd[n_bound + k, k - 1] = -1 / math.sqrt(2)
    return even, odd


def evaluate_cell(m: int, n_bound: int) -> dict[str, Any]:
    matrix, construction = build_weil_matrix(m, n_bound)
    even_basis, odd_basis = sector_bases(n_bound)
    even_matrix = even_basis.T @ matrix @ even_basis
    odd_matrix = odd_basis.T @ matrix @ odd_basis
    even_values, even_vectors = np.linalg.eigh(even_matrix)
    odd_values = np.linalg.eigvalsh(odd_matrix)

    epsilon_plus_1 = float(even_values[0])
    epsilon_plus_2 = float(even_values[1])
    epsilon_minus_1 = float(odd_values[0])
    lambda_1 = epsilon_plus_1
    lambda_2 = min(epsilon_plus_2, epsilon_minus_1)
    full_values = np.linalg.eigvalsh(matrix)
    union_values = np.sort(np.concatenate((even_values, odd_values)))
    union_error = float(np.max(np.abs(full_values - union_values)))

    q = even_basis @ even_vectors[:, 0]
    q /= np.linalg.norm(q)
    rayleigh = float(q @ (matrix @ q))
    residual = float(np.linalg.norm(matrix @ q - rayleigh * q))
    parity_residual = float(np.linalg.norm(q[::-1] - q))

    beta = (lambda_1 + lambda_2) / 2
    tau = lambda_2 - lambda_1
    cert = matrix - beta * np.eye(matrix.shape[0]) + tau * np.outer(q, q)
    cert_values = np.linalg.eigvalsh(cert)
    min_eig_cert = float(cert_values[0])
    ideal_margin = tau / 2
    scale = max(
        1.0,
        float(np.linalg.norm(matrix, ord=2)),
        abs(beta),
        abs(tau),
    )
    roundoff_guard = (
        ROUND_GUARD_MULTIPLIER * np.finfo(np.float64).eps * scale
    )

    tau_zero_cert = matrix - beta * np.eye(matrix.shape[0])
    tau_zero_min = float(np.linalg.eigvalsh(tau_zero_cert)[0])
    ordering = (
        epsilon_plus_1 < epsilon_minus_1
        and epsilon_plus_1 < epsilon_plus_2
    )
    psd_achievable = bool(
        ordering
        and tau > roundoff_guard
        and min_eig_cert > roundoff_guard
        and tau_zero_min < -roundoff_guard
    )

    return {
        "m": m,
        "N": n_bound,
        "dimension": matrix.shape[0],
        "lambda_1": lambda_1,
        "lambda_2": lambda_2,
        "epsilon_plus_1": epsilon_plus_1,
        "epsilon_plus_2": epsilon_plus_2,
        "epsilon_minus_1": epsilon_minus_1,
        "even_internal_margin": epsilon_plus_2 - epsilon_plus_1,
        "even_odd_bottom_margin": epsilon_minus_1 - epsilon_plus_1,
        "beta": beta,
        "tau": tau,
        "rayleigh_a": rayleigh,
        "min_eig_cert": min_eig_cert,
        "ideal_min_eig_cert": ideal_margin,
        "min_eig_cert_error": min_eig_cert - ideal_margin,
        "roundoff_guard": roundoff_guard,
        "tau_zero_min_eig_cert": tau_zero_min,
        "ground_eigen_residual": residual,
        "ground_parity_residual": parity_residual,
        "sector_union_spectrum_error": union_error,
        "construction": construction,
        "numeric_exact_sector_ordering": ordering,
        "psd_achievable": psd_achievable,
    }


def render_report(payload: dict[str, Any]) -> str:
    lines = [
        "# H2a certificate split — binary64 pilot",
        "",
        "Status: `CERT_PILOT_EXECUTED / CERT_EXACT_OPEN / NOT_RH`",
        "",
        "## Split",
        "",
        "- `cert.pilot`: binary64 diagnostic on the registered small grid.",
        "- `cert.exact`: exact theorem leaf `ExactSectorOrdering`, still open.",
        "- Exact consumer: Layer-B `PenaltyPilotFamily` / exact `PencilData`.",
        "",
        "The pilot uses `G=I`, `K=Mfin_(m,N)=WeilMat_(m,N)`, the numerical",
        "even-sector ground `q`,",
        "`beta=(lambda_1+lambda_2)/2`, and `tau=lambda_2-lambda_1`.",
        "",
        "## Results",
        "",
        "| (m,N) | beta | tau | min_eig_cert | guard | result |",
        "|---:|---:|---:|---:|---:|:---|",
    ]
    for row in payload["cells"]:
        lines.append(
            "| "
            f"({row['m']},{row['N']}) | "
            f"{row['beta']:.12e} | "
            f"{row['tau']:.12e} | "
            f"{row['min_eig_cert']:.12e} | "
            f"{row['roundoff_guard']:.3e} | "
            f"{'PSD' if row['psd_achievable'] else 'NO'} |"
        )
    lines.extend(
        [
            "",
            f"Verdict: `{payload['verdict']}`.",
            "",
            "The `tau=0` planted control is negative beyond the binary64 guard",
            "in every row.  The positive pilot margin is numerical evidence only.",
            "",
            "## Exact queue leaf",
            "",
            "```text",
            "ExactSectorOrdering:",
            "  epsilon_plus_1(m,N) < epsilon_minus_1(m,N)",
            "  and",
            "  epsilon_plus_1(m,N) < epsilon_plus_2(m,N)",
            "```",
            "",
            "Consumer:",
            "",
            "```text",
            "ExactSectorOrdering",
            "  -> exact beta/tau penalty certificate",
            "  -> ProjectApprox.PenaltyPilotFamily",
            "  -> supply_H2a_Pstar_of_penaltyPilot",
            "```",
            "",
            "Stop: `H2A_EXACT_SECTOR_ORDERING_MISSING`.",
            "",
            "No state file was modified; Bus 010 was not created.",
            "",
        ]
    )
    return "\n".join(lines)


def run() -> dict[str, Any]:
    if list(BUS.glob("010_*")):
        raise RuntimeError("BUS_010_PRESENT")
    state_before = sha256(STATE)
    cells = [
        evaluate_cell(m, n_bound)
        for m, n_bound in tqdm(CELLS, desc="H2a cert.pilot", unit="cell")
    ]
    verdict = (
        "PSD_ACHIEVABLE_ON_REGISTERED_SMALL_GRID"
        if all(row["psd_achievable"] for row in cells)
        else "PSD_NOT_ACHIEVABLE_ON_REGISTERED_SMALL_GRID"
    )
    payload = {
        "schema": "route_b_h2a_cert_split_pilot.v1",
        "status": "DIAGNOSTIC_ONLY_NOT_EXACT_CERTIFICATE",
        "arithmetic": "IEEE754_BINARY64",
        "python": platform.python_version(),
        "numpy": np.__version__,
        "scipy": special.__version__ if hasattr(special, "__version__") else None,
        "registered_cells": CELLS,
        "quad_order": QUAD_ORDER,
        "round_guard_multiplier": ROUND_GUARD_MULTIPLIER,
        "matrix": {
            "G": "identity",
            "K": "Mfin_m_N=WeilMat_m_N",
            "q": "binary64 even-sector lowest eigenvector",
            "beta": "(lambda_1+lambda_2)/2",
            "tau": "lambda_2-lambda_1",
        },
        "cert_split": {
            "cert.pilot": "EXECUTED_BINARY64_DIAGNOSTIC",
            "cert.exact": "OPEN",
            "exact_leaf": "ExactSectorOrdering",
            "exact_statement": [
                "epsilon_plus_1(m,N)<epsilon_minus_1(m,N)",
                "epsilon_plus_1(m,N)<epsilon_plus_2(m,N)",
            ],
            "consumer": (
                "ProjectApprox.PenaltyPilotFamily exact PencilData -> "
                "supply_H2a_Pstar_of_penaltyPilot"
            ),
            "stop": "H2A_EXACT_SECTOR_ORDERING_MISSING",
        },
        "cells": cells,
        "verdict": verdict,
        "state_sha256_before": state_before,
        "state_sha256_after": sha256(STATE),
        "bus_010_absent": not bool(list(BUS.glob("010_*"))),
        "rh_status": "NOT_RH",
    }
    if payload["state_sha256_before"] != payload["state_sha256_after"]:
        raise RuntimeError("STATE_CHANGED_DURING_PILOT")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    payload = run()
    if args.write:
        JSON_OUT.write_text(
            json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        REPORT_OUT.write_text(render_report(payload), encoding="utf-8")
        print(JSON_OUT)
        print(REPORT_OUT)
    else:
        print(json.dumps(json_safe(payload), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
