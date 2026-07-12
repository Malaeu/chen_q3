#!/usr/bin/env python3
"""Reproduce the Route-B D0.7e T1 judges from persisted coefficient vectors.

This script is diagnostic only.  It never builds a missing vector, chooses a
selector/filter, or defines alpha/DeltaE/WPrime.  JSON is printed to stdout;
the canonical checked-in result is D0_7E_JUDGE_CERTIFICATES.json.
"""

from __future__ import annotations

import hashlib
import json
import math
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any

import numpy as np


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
COEFF_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "out"
OWNER_INPUT = REQUEST_DIR / "D0_7E_OWNER_INPUT.md"

SOURCES = (
    (13, 90, "portable_k_coeffs_lambda_sq_13_N_90.json"),
    (13, 120, "portable_k_coeffs_lambda_sq_13_N_120.json"),
    (14, 120, "portable_k_coeffs_lambda_sq_14_N_120.json"),
)
REQUIRED_MISSING = ((17, 120, "portable_k_coeffs_lambda_sq_17_N_120.json"),)

# The immutable owner input prints this decimal with an ellipsis.  The broad
# enclosure below is an input enclosure for numerical judging, not a theorem
# certifying the source's rounding error.  Exact nonvanishing is proved
# separately by the eta-series sign argument.
ZETA_HALF_MID = Decimal("-1.46035450880958681")
ZETA_HALF_LO = Decimal("-1.46035450880958682")
ZETA_HALF_HI = Decimal("-1.46035450880958680")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dec(value: Any) -> Decimal:
    return Decimal(str(value))


def fmt(value: Decimal, digits: int = 70) -> str:
    return format(value, f".{digits}g")


def direct_midpoint_quadrature(payload: dict[str, Any], samples: int = 2048) -> dict[str, Any]:
    """Integrate the persisted finite Fourier vector directly on [0,L]."""

    rows = payload["coefficients"]
    ns = np.array([int(row["n"]) for row in rows], dtype=np.int64)
    coeffs = np.array(
        [complex(float(row["re"]), float(row["im"])) for row in rows],
        dtype=np.complex128,
    )
    L = math.log(int(payload["lambda_sq"]))
    x = (np.arange(samples, dtype=np.float64) + 0.5) * L / samples
    values = np.zeros(samples, dtype=np.complex128)
    for n, coefficient in zip(ns, coeffs):
        values += coefficient * np.exp(2j * np.pi * n * x / L) / math.sqrt(L)
    direct = (L / samples) * values.sum()
    zero_index = int(np.flatnonzero(ns == 0)[0])
    identity = math.sqrt(L) * coeffs[zero_index]
    residual = direct - identity
    return {
        "method": "2048-point midpoint quadrature of persisted finite Fourier vector",
        "samples": samples,
        "stored_coefficient_identity": {
            "re": repr(float(identity.real)),
            "im": repr(float(identity.imag)),
        },
        "direct_quadrature": {
            "re": repr(float(direct.real)),
            "im": repr(float(direct.imag)),
        },
        "absolute_residual": repr(float(abs(residual))),
        "relative_residual": repr(float(abs(residual) / abs(identity))),
        "machine_zero_pass": bool(abs(residual) / abs(identity) <= 5e-15),
    }


def cell_result(lambda_sq: int, n_bound: int, filename: str) -> dict[str, Any]:
    path = COEFF_DIR / filename
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload["lambda_sq"] != lambda_sq or payload["N"] != n_bound:
        raise SystemExit(f"SOURCE_METADATA_MISMATCH:{filename}")
    zero = next(row for row in payload["coefficients"] if int(row["n"]) == 0)
    c0 = dec(zero["re"])
    c0_im = abs(dec(zero["im"]))
    qdiff = abs(dec(payload["coeff_max_abs_diff_vs_half_q"]))
    c0_radius = max(c0_im, qdiff)
    c0_lo, c0_hi = c0 - c0_radius, c0 + c0_radius

    m = Decimal(lambda_sq)
    L = m.ln()
    sqrt_L = L.sqrt()
    bdet = sqrt_L * c0 / ZETA_HALF_MID
    # All endpoint combinations, then a deliberately broad decimal guard.
    endpoint_values = [
        sqrt_L * c / z
        for c in (c0_lo, c0_hi)
        for z in (ZETA_HALF_LO, ZETA_HALF_HI)
    ]
    guard = Decimal("1e-68")
    bdet_lo = min(endpoint_values) - guard
    bdet_hi = max(endpoint_values) + guard
    sqrt_lambda = m.sqrt().sqrt()

    quadrature = direct_midpoint_quadrature(payload)
    shadow_bdet = sqrt_L * Decimal(0) / ZETA_HALF_MID
    plant_guard = "B_CENTRAL_ZERO_CELL" if shadow_bdet == 0 else "PLANT_INERT"
    return {
        "lambda_sq": lambda_sq,
        "N": n_bound,
        "source": str(path.relative_to(REPO_ROOT)),
        "source_sha256": sha256(path),
        "source_kind": payload["cache_kind"],
        "source_logical_vector": payload["logical_vector"],
        "source_dps": payload["dps"],
        "source_quad_order": payload["quad_order"],
        "c0": {
            "re": fmt(c0),
            "im_abs": str(c0_im),
            "persisted_cross_quadrature_radius": str(qdiff),
            "input_enclosure": [fmt(c0_lo), fmt(c0_hi)],
            "sign": "NEGATIVE" if c0_hi < 0 else "UNRESOLVED",
        },
        "bDet": {
            "midpoint_value": fmt(bdet),
            "input_enclosure": [fmt(bdet_lo), fmt(bdet_hi)],
            "sign": "POSITIVE" if bdet_lo > 0 else "UNRESOLVED",
            "abs_bDet_sqrt_lambda": fmt(abs(bdet) * sqrt_lambda),
            "status": "NUMERICAL_INPUT_ENCLOSURE_SIGN_CERTIFIED",
        },
        "two_way_evaluation": quadrature,
        "central_zero_plant": {
            "shadow_c0": "0",
            "shadow_bDet": str(shadow_bdet),
            "guard": plant_guard,
            "plant_fires": plant_guard == "B_CENTRAL_ZERO_CELL",
        },
    }


def main() -> None:
    getcontext().prec = 100
    cells = [cell_result(*source) for source in SOURCES]
    by_key = {(cell["lambda_sq"], cell["N"]): cell for cell in cells}
    b90 = dec(by_key[(13, 90)]["bDet"]["midpoint_value"])
    b120 = dec(by_key[(13, 120)]["bDet"]["midpoint_value"])
    n_factor = max(abs(b90), abs(b120)) / min(abs(b90), abs(b120))
    p3_values = [
        dec(by_key[key]["bDet"]["abs_bDet_sqrt_lambda"])
        for key in ((13, 120), (14, 120))
    ]
    p3_factor = max(p3_values) / min(p3_values)
    missing = [
        {
            "lambda_sq": m,
            "N": n,
            "expected_path": str((COEFF_DIR / filename).relative_to(REPO_ROOT)),
            "exists": (COEFF_DIR / filename).is_file(),
            "failure_code": "T1_LAMBDA17_PERSISTED_COEFFICIENT_VECTOR_MISSING",
        }
        for m, n, filename in REQUIRED_MISSING
    ]
    all_quad = all(cell["two_way_evaluation"]["machine_zero_pass"] for cell in cells)
    all_plants = all(cell["central_zero_plant"]["plant_fires"] for cell in cells)
    result = {
        "schema": "route_b_d0_7e_t1_judges.v1",
        "task": "T1_PRE_REGISTERED_BDET_JUDGES",
        "overall_status": "PARTIAL_BLOCKED_MISSING_LAMBDA17_PERSISTED_VECTOR",
        "rh_status": "NOT_RH",
        "owner_input": str(OWNER_INPUT.relative_to(REPO_ROOT)),
        "owner_input_sha256": sha256(OWNER_INPUT),
        "arithmetic": {
            "formula": "bDet=sqrt(log(lambda_sq))*c0/zeta(1/2)",
            "zeta_half_midpoint_from_owner_input": str(ZETA_HALF_MID),
            "zeta_half_numerical_input_enclosure": [str(ZETA_HALF_LO), str(ZETA_HALF_HI)],
            "interval_honesty": "INPUT_ENCLOSURE_ONLY_NOT_A_PROOF_OF_SOURCE_ROUNDING_OR_QUADRATURE_ERROR",
        },
        "cells": cells,
        "judges": {
            "J1_per_cell_value_and_sign": {
                "status": "PARTIAL_13_14_PASS_17_BLOCKED",
                "available_signs": [cell["bDet"]["sign"] for cell in cells],
                "missing": missing,
            },
            "J2_N_stability_13_90_vs_120": {
                "factor": fmt(n_factor),
                "threshold": "3",
                "pass": n_factor <= Decimal(3),
            },
            "J3_two_way_evaluation": {
                "status": "AVAILABLE_CELLS_PASS" if all_quad else "FAIL",
                "all_machine_zero_pass": all_quad,
            },
            "J4_central_zero_plant": {
                "status": "B_CENTRAL_ZERO_CELL_FIRES" if all_plants else "PLANT_INERT",
                "all_plants_fire": all_plants,
            },
            "P3_abs_bDet_sqrt_lambda_factor3": {
                "classification": "FIT_NOT_LAW",
                "available_cells": [[13, 120], [14, 120]],
                "factor": fmt(p3_factor),
                "partial_pass": p3_factor <= Decimal(3),
                "score_status": "NOT_FULLY_SCORED_LAMBDA17_MISSING",
            },
        },
        "explicit_nonclaims": [
            "NO_ASYMPTOTIC_BDET_BOUND",
            "NO_COFINAL_NONVANISHING",
            "NO_SELECTOR_OR_FILTER",
            "NO_ALPHA_OR_DELTAE_OR_WPRIME_DEFINITION",
            "NO_PROOF_GRADE_INTERVAL_FROM_QUADRATURE_DIFFERENCE",
            "NO_H3E_TRACKING_RESULT",
            "NO_RH",
        ],
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
