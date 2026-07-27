#!/usr/bin/env python3
"""Fail-closed float64 execution of §5 of the owner-mint draft.

R0 was observed with scalar sTrial in vector positions.  While the probe was
running, V2 revised the physical draft to R2: the executable rVec/P1 lines now
use kTrial and P2 has the gap in the numerator.  This runner scores the current
R2 bytes, preserves the historical misses separately, and never edits the
draft or STATE.json or activates the mint.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
LADDER_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder"
OUT_DIR = LADDER_DIR / "out"

DRAFT = REQUEST_DIR / "D0_7E_5A_OWNER_MINT_DRAFT_WPRIME_CONSUMER.md"
D0_7_CERT = REQUEST_DIR / "D0_7_CERTIFICATE.json"
JUDGES = REQUEST_DIR / "D0_7E_JUDGE_CERTIFICATES.json"
STATE = REQUEST_DIR / "STATE.json"
RESULT = REQUEST_DIR / "D0_7E_5A_PRE_MINT_FALSIFIER_BATTERY.json"
REPORT = REQUEST_DIR / "D0_7E_5A_PRE_MINT_FALSIFIER_BATTERY.md"

CELLS = ((13, 90), (13, 120), (14, 120))
ZETA_HALF = -1.4603545088095868
P1_THRESHOLD = 1e-12


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


def parse_complex(value: Any) -> complex:
    return complex(str(value).strip("()").replace(" ", ""))


def load_bdet() -> dict[tuple[int, int], float]:
    payload = json.loads(JUDGES.read_text(encoding="utf-8"))
    return {
        (int(cell["lambda_sq"]), int(cell["N"])): float(
            cell["bDet"]["midpoint_value"]
        )
        for cell in payload["cells"]
    }


def p1_s0_shadow(lambda_sq: int, n_bound: int) -> dict[str, Any]:
    path = OUT_DIR / f"parity_block_lambda_sq_{lambda_sq}_N_{n_bound}.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    matrix = np.array(
        [[parse_complex(value) for value in row] for row in payload["even"]["S0"]],
        dtype=np.complex128,
    )
    matrix = (matrix + matrix.conj().T) / 2
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    trial = np.array([1.0, 0.0], dtype=np.complex128)
    residual = (matrix - eigenvalues[0] * np.eye(2)) @ trial
    lhs = float(np.vdot(residual, residual).real)
    xi3_overlap = float(abs(np.vdot(trial, eigenvectors[:, 1])))
    rhs = float(
        (eigenvalues[1] - eigenvalues[0]) ** 2 * xi3_overlap**2
    )
    relative_residual = abs(lhs - rhs) / max(
        abs(lhs), abs(rhs), np.finfo(np.float64).tiny
    )
    return {
        "lambda_sq": lambda_sq,
        "N": n_bound,
        "source": rel(path),
        "source_sha256": sha256(path),
        "carrier_warning": "S0_IS_DIAGNOSTIC_SCHUR_NOT_CANONICAL_MFIN",
        "theta1": float(eigenvalues[0]),
        "theta3": float(eigenvalues[1]),
        "gap": float(eigenvalues[1] - eigenvalues[0]),
        "abs_inner_k1_xi3": xi3_overlap,
        "lhs_norm_r_squared": lhs,
        "rhs_gap_squared_overlap_squared": rhs,
        "relative_residual": relative_residual,
        "threshold": P1_THRESHOLD,
        "diagnostic_pass": relative_residual < P1_THRESHOLD,
    }


def p1_full_cache_13_120() -> dict[str, Any]:
    coeff_path = OUT_DIR / "portable_k_coeffs_lambda_sq_13_N_120.json"
    xi_path = OUT_DIR / "nconv_anchor_lambda_sq_13_N_120.json"
    coeff_payload = json.loads(coeff_path.read_text(encoding="utf-8"))
    xi_payload = json.loads(xi_path.read_text(encoding="utf-8"))

    def vector(rows: list[dict[str, Any]]) -> np.ndarray:
        return np.array(
            [complex(float(row["re"]), float(row["im"])) for row in rows],
            dtype=np.complex128,
        )

    ktrial = vector(coeff_payload["coefficients"])
    xi1_entry = xi_payload["xi_m_y_cache"][0]
    xi3_entry = xi_payload["xi_m_y_cache"][2]
    xi1 = vector(xi1_entry["xi_vector"])
    xi3 = vector(xi3_entry["xi_vector"])
    mu1 = float(xi1_entry["mu"])
    mu3 = float(xi3_entry["mu"])
    c1 = np.vdot(xi1, ktrial)
    c3 = np.vdot(xi3, ktrial)
    projected = c1 * xi1 + c3 * xi3
    residual = (mu3 - mu1) * c3 * xi3
    lhs = float(np.vdot(residual, residual).real)
    rhs = float((mu3 - mu1) ** 2 * abs(c3) ** 2)
    relative_residual = abs(lhs - rhs) / max(
        abs(lhs), abs(rhs), np.finfo(np.float64).tiny
    )
    return {
        "cell": [13, 120],
        "coefficient_source": rel(coeff_path),
        "coefficient_source_sha256": sha256(coeff_path),
        "xi_source": rel(xi_path),
        "xi_source_sha256": sha256(xi_path),
        "warning": "NO_PERSISTED_MFIN_MATVEC; EIGENPAIR_REPRESENTATION_ONLY",
        "norm_kTrial": float(np.linalg.norm(ktrial)),
        "norm_projected": float(np.linalg.norm(projected)),
        "abs_inner_kTrial_xi3": float(abs(c3)),
        "gap": mu3 - mu1,
        "lhs_norm_r_squared": lhs,
        "rhs_gap_squared_overlap_squared": rhs,
        "relative_residual": relative_residual,
        "threshold": P1_THRESHOLD,
        "diagnostic_pass": relative_residual < P1_THRESHOLD,
    }


def scalar_cell(lambda_sq: int, n_bound: int, bdet: float) -> dict[str, Any]:
    path = OUT_DIR / f"lambda_sq_{lambda_sq}_N_{n_bound}.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    mu1 = float(payload["mu1"])
    mu3 = float(payload["mu3"])
    a1 = float(payload["a1"])
    eta1 = float(payload["eta1"])
    gap = mu3 - mu1
    # eta1 is ||(M-a1 I)k1||.  Orthogonality to k1 yields this identity.
    full_r2_float64 = eta1 * eta1 + (a1 - mu1) ** 2
    b2 = bdet * bdet
    b4 = b2 * b2
    historical_r0_alpha_bcal = full_r2_float64 / (gap * b2)
    historical_r0_alpha_inverse = full_r2_float64 / (gap / b2)
    current_r2_alpha_bcal = full_r2_float64 * gap / b2
    current_r2_alpha_inverse = full_r2_float64 * gap * b2
    return {
        "lambda_sq": lambda_sq,
        "N": n_bound,
        "source": rel(path),
        "source_sha256": sha256(path),
        "mu1": mu1,
        "mu3": mu3,
        "gap_mu3_minus_mu1": gap,
        "a1": a1,
        "eta1_rayleigh_residual": eta1,
        "full_rVec_norm_squared_float64_proxy": full_r2_float64,
        "bCal": bdet,
        "abs_bCal_fourth": b4,
        "historical_R0_alpha_probe_bCal": historical_r0_alpha_bcal,
        "historical_R0_alpha_probe_bCal_inverse": historical_r0_alpha_inverse,
        "current_R2_alpha_probe_bCal": current_r2_alpha_bcal,
        "current_R2_alpha_probe_bCal_inverse": current_r2_alpha_inverse,
        "current_R2_orientation_ratio_inverse_over_direct": (
            current_r2_alpha_inverse / current_r2_alpha_bcal
        ),
        "current_R2_orientation_ratio_relative_error_vs_bCal_fourth": abs(
            current_r2_alpha_inverse / current_r2_alpha_bcal - b4
        )
        / b4,
        "historical_R0_over_current_R2_factor": 1 / (gap * gap),
        "bCal_within_factor_ten_of_one": 0.1 <= abs(bdet) <= 10,
        "orientation_classification": "ZERO_CONSISTENT_UNDECIDABLE",
        # If alpha is the registered two-level Rayleigh excess r^2/gap,
        # LHS/RHS of 5c is gap^2/b^2 or gap^2*b^2 respectively.
        "two_level_rayleigh_alpha_closure_ratio_bCal": gap * gap / b2,
        "two_level_rayleigh_alpha_closure_ratio_bCal_inverse": gap * gap * b2,
    }


def slope(x1: float, y1: float, x2: float, y2: float) -> float:
    return math.log(y2 / y1) / math.log(x2 / x1)


def run() -> dict[str, Any]:
    state = json.loads(STATE.read_text(encoding="utf-8"))
    node = state["nodes"]["D0.7e.5a"]
    if node["proof_status"] != "BLOCKED" or node["activity"] != "ACTIVE":
        raise RuntimeError("D0_7E_5A_STATE_CHANGED_BEFORE_BATTERY")
    if list((LADDER_DIR / "bus").glob("010_*")):
        raise RuntimeError("BUS_010_PRESENT_BEFORE_BATTERY")

    d0_7 = json.loads(D0_7_CERT.read_text(encoding="utf-8"))
    trial = d0_7["trial_lock"]
    if not trial["scale"].startswith("sTrial_m_N=norm(gTrial_m_N)^(-1)"):
        raise RuntimeError("D0_7_STRIAL_SOURCE_DRIFT")
    if not trial["normalized"].startswith("kTrial_m_N=sTrial_m_N*gTrial_m_N"):
        raise RuntimeError("D0_7_KTRIAL_SOURCE_DRIFT")
    draft_text = DRAFT.read_text(encoding="utf-8")
    if "Revision: R2" not in draft_text:
        raise RuntimeError("D0_7E_5A_EXPECTED_R2_DRAFT_MISSING")
    if "(Mfin_(m,N) - mu1_(m,N) Id) kTrial_(m,N)" not in draft_text:
        raise RuntimeError("D0_7E_5A_R2_KTRIAL_REPAIR_MISSING")
    if "||rVec||^2 * (mu3-mu1) / |b|^2" not in draft_text:
        raise RuntimeError("D0_7E_5A_R2_P2_GAP_NUMERATOR_REPAIR_MISSING")

    bdet = load_bdet()
    p1_cells = [p1_s0_shadow(*cell) for cell in CELLS]
    scalar_cells = [scalar_cell(*cell, bdet[cell]) for cell in CELLS]

    gamma_c_half = (
        0.5
        * 0.5
        * (-0.5)
        * math.pi ** (-0.25)
        * math.gamma(0.25)
    )
    xi_zero = gamma_c_half * ZETA_HALF
    p3_cells = []
    for cell in scalar_cells:
        b = cell["bCal"]
        detreg_abs = b * abs(ZETA_HALF)
        draft_bcal_xi_abs = b * abs(xi_zero)
        p3_cells.append(
            {
                "lambda_sq": cell["lambda_sq"],
                "N": cell["N"],
                "abs_detreg_equals_abs_Fplus_zero": detreg_abs,
                "draft_abs_bCal_times_abs_Xi_zero": draft_bcal_xi_abs,
                "central_crosswalk_ratio": draft_bcal_xi_abs / detreg_abs,
                "expected_ratio_abs_gammaC_half": abs(gamma_c_half),
                "reduced_5c_relation": (
                    "abs(bCal)^4*abs(Xi(0))^2*DeltaE=lambda*alpha"
                ),
                "independent_WPrime_degree_of_freedom": False,
                "plant": "SLOT_VACUITY",
            }
        )

    p1_by_cell = {
        (cell["lambda_sq"], cell["N"]): cell for cell in p1_cells
    }
    scalar_by_cell = {
        (cell["lambda_sq"], cell["N"]): cell for cell in scalar_cells
    }
    lambda13 = math.sqrt(13)
    lambda14 = math.sqrt(14)
    rproj13 = math.sqrt(p1_by_cell[(13, 120)]["lhs_norm_r_squared"])
    rproj14 = math.sqrt(p1_by_cell[(14, 120)]["lhs_norm_r_squared"])
    wproj13 = math.sqrt(lambda13) * rproj13
    wproj14 = math.sqrt(lambda14) * rproj14
    beta_r_projected = slope(lambda13, rproj13, lambda14, rproj14)
    beta_w_projected = slope(lambda13, wproj13, lambda14, wproj14)

    rfull13 = math.sqrt(
        scalar_by_cell[(13, 120)]["full_rVec_norm_squared_float64_proxy"]
    )
    rfull14 = math.sqrt(
        scalar_by_cell[(14, 120)]["full_rVec_norm_squared_float64_proxy"]
    )
    wfull13 = math.sqrt(lambda13) * rfull13
    wfull14 = math.sqrt(lambda14) * rfull14
    beta_r_full = slope(lambda13, rfull13, lambda14, rfull14)
    beta_w_full = slope(lambda13, wfull13, lambda14, wfull14)

    return {
        "schema": "route_b_d0_7e_5a_pre_mint_falsifier_battery.v1",
        "status": "INVALID_EXECUTABLE_SPEC_AS_WRITTEN",
        "overall_code": "MINT_MENU_REVISION_REQUIRED",
        "rh_status": "NOT_RH",
        "arithmetic": "IEEE754_BINARY64_ONLY_NO_DPS_ESCALATION",
        "draft": {"path": rel(DRAFT), "sha256": sha256(DRAFT)},
        "draft_revision_audit": {
            "revision": "R2_V2_SELF_CORRECTION",
            "sTrial": trial["scale"],
            "kTrial": trial["normalized"],
            "R2_executable_lines": "rVec and P1 now use kTrial correctly",
            "remaining_reference_drift": [
                "allowed alphabet still names scalar sTrial instead of vector kTrial",
                "spectral expansion paragraph still writes inner(sTrial,xi_k)",
            ],
            "historical_R0_misses_acknowledged_in_draft": [
                "TYPE_ERROR_STRIAL_SCALAR",
                "P2_ALPHA_PROBE_GAP_INVERSION",
            ],
            "finding": "R2_PARTIAL_STRIAL_REFERENCE_DRIFT",
        },
        "scores": {
            "P1": {
                "status": "FAIL",
                "registered_prediction": "PASS_relative_residual_lt_1e-12",
                "registered_score": "DIAGNOSTIC_HIT_BUT_CANONICAL_SCORE_FAIL_CLOSED",
                "codes": [
                    "P1_PERSISTED_MFIN_XI_INPUT_INCOMPLETE",
                    "R2_RESIDUAL_EXPANSION_STRIAL_REFERENCE_DRIFT",
                ],
                "shadow_reduced_S0": {
                    "status": "DIAGNOSTIC_PASS_NOT_MFIN_CERT",
                    "cells": p1_cells,
                    "all_relative_residuals_below_threshold": all(
                        cell["diagnostic_pass"] for cell in p1_cells
                    ),
                },
                "shadow_full_eigenpair_cache_13_120": p1_full_cache_13_120(),
            },
            "P2": {
                "status": "FAIL",
                "registered_score": (
                    "HIT_FACTOR_AND_ZERO_CONSISTENT_OUTCOME_BUT_FAILS_RAYLEIGH_ALPHA_CROSSWALK"
                ),
                "registered_factor_check": "HIT_bCal_fourth_but_nondiscriminating",
                "codes": [
                    "P2_R2_GAP_NUMERATOR_REPAIR_PRESENT",
                    "P2_ORIENTATION_ZERO_CONSISTENT_UNDECIDABLE",
                    "P2_TWO_LEVEL_RAYLEIGH_ALPHA_5C_MISMATCH",
                ],
                "derivation": {
                    "given": "W_A^2=lambda*r^2 and W_A^2*gap=abs(b)^2*lambda*alpha",
                    "forced_alpha": "alpha=r^2*gap/abs(b)^2",
                    "current_R2_alpha_probe": "alpha_probe=r^2*gap/abs(b)^2",
                    "current_R2_formula_check": "PASS",
                    "historical_R0_formula": "alpha_probe=r^2/(gap*abs(b)^2)",
                    "historical_R0_error_factor": "gap^(-2)",
                },
                "cells": scalar_cells,
            },
            "P3": {
                "status": "PASS",
                "registered_prediction": "SLOT_VACUITY_must_fire",
                "registered_score": "HIT",
                "code": "SLOT_VACUITY",
                "symbolic_reduction": (
                    "W_B=abs(bCal)*abs(Xi(0)), bW=bCal^(-1) => "
                    "abs(bCal)^4*abs(Xi(0))^2*DeltaE=lambda*alpha"
                ),
                "warning": (
                    "draft also equates abs(detreg)=abs(Fplus(0)) with "
                    "abs(bCal)*abs(Xi(0)); D0.7e gives an extra abs(gammaC(1/2)) factor"
                ),
                "gammaC_half": gamma_c_half,
                "Xi_zero_float64": xi_zero,
                "cells": p3_cells,
            },
            "P4": {
                "status": "FAIL",
                "registered_prediction": "slope_consistent_with_sqrt_lambda_prefactor",
                "registered_score": "MISS_UNSCORABLE_NO_REGISTERED_TOLERANCE",
                "codes": [
                    "P4_NO_REGISTERED_SLOPE_TOLERANCE",
                    "P4_RAW_SLOPE_CARRIER_AMBIGUITY",
                ],
                "correct_identity": "beta_W=beta_r+1/2",
                "two_level_S0_N120": {
                    "r_13": rproj13,
                    "r_14": rproj14,
                    "WPrime_A_13": wproj13,
                    "WPrime_A_14": wproj14,
                    "beta_r": beta_r_projected,
                    "beta_W": beta_w_projected,
                    "beta_W_minus_beta_r": beta_w_projected - beta_r_projected,
                },
                "full_float64_residual_proxy_N120": {
                    "r_13": rfull13,
                    "r_14": rfull14,
                    "WPrime_A_13": wfull13,
                    "WPrime_A_14": wfull14,
                    "beta_r": beta_r_full,
                    "beta_W": beta_w_full,
                    "beta_W_minus_beta_r": beta_w_full - beta_r_full,
                },
                "interpretation": (
                    "the +1/2 increment passes tautologically; the raw beta_W is neither "
                    "registered against a numerical band nor stable across the two carriers"
                ),
            },
        },
        "control_plane_guards": {
            "state_revision_observed": state["revision"],
            "D0.7e.5a_proof_status": node["proof_status"],
            "D0.7e.5a_activity": node["activity"],
            "mint_activated": False,
            "bus_010_created": False,
            "draft_mutated": False,
            "state_mutated": False,
        },
        "explicit_nonclaims": [
            "NO_MINT_ACTIVATION",
            "NO_D0_7E_5A_CLOSURE",
            "NO_CANONICAL_ALPHA_MINT",
            "NO_CANONICAL_MFIN_CERT_FROM_S0",
            "NO_BUS_010",
            "NO_RH",
        ],
    }


def markdown(result: dict[str, Any]) -> str:
    scores = result["scores"]
    lines = [
        "# D0.7e.5a pre-mint falsifier battery",
        "",
        "Status: `INVALID_EXECUTABLE_SPEC_AS_WRITTEN / MINT_MENU_REVISION_REQUIRED / NOT_RH`.",
        "",
        "| probe | literal score | decisive finding |",
        "|---|---|---|",
        "| P1 | FAIL | R2 uses kTrial, but full persisted Mfin/xi data are incomplete |",
        "| P2 | FAIL | R2 formula is repaired; factor test is nondiscriminating and Rayleigh-alpha 5c fails |",
        "| P3 | PASS | planted `SLOT_VACUITY` fires |",
        "| P4 | FAIL | no registered tolerance; raw slope depends on carrier |",
        "",
        "R2's repaired `kTrial` line makes the reduced S0 P1",
        "residuals `5.68e-16`, `1.83e-16`, `3.80e-16`, all below `1e-12`,",
        "but S0 is a diagnostic Schur object, not canonical Mfin.",
        "",
        "P2 R2's orientation ratios equal `|bCal|^4` (about 0.123) exactly as",
        "registered, but this is algebraic for both the wrong and repaired",
        "alpha formula and cannot choose orientation. Every bCal is within a",
        "factor ten of one, so the declared outcome is ZERO_CONSISTENT_UNDECIDABLE.",
        "For the registered two-level Rayleigh-excess candidate, the direct",
        "5c closure ratios are about `6.94e-102`, `4.91e-102`, `2.51e-112`,",
        "not one.",
        "",
        "P4 at N=120 gives beta_W=-321.891809286 on the reduced two-level",
        "carrier and beta_W=4.71336008648 on the full float64 residual proxy;",
        "both satisfy beta_W-beta_r=0.5 by definition, so that increment is",
        "not an independent falsifier.",
        "",
        "D0.7e.5a remains BLOCKED/ACTIVE. Mint inactive. No Bus 010.",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = run()
    if args.write:
        REPORT.write_text(markdown(result), encoding="utf-8")
        result["report"] = {"path": rel(REPORT), "sha256": sha256(REPORT)}
        RESULT.write_text(
            json.dumps(json_safe(result), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(json.dumps(json_safe(result), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
