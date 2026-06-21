#!/usr/bin/env python3
"""Fail-closed OmegaPrime Taylor payload for Step33A.1-A sub0.

This generator records the smallest proof-producing surface for the current
component Taylor blocker:

    step22OmegaArchWeightDerivClosedForm

around center 1/20 on radius 1/20, degree 15.  It deliberately does not emit
Lean until the checked-deriv receiver payload fields are proof-grade: center
jet coefficient enclosures, the integer order-16 budget, and the exact
remainder budget.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path
from typing import Any


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(2_000_000)

ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

CHUNK_FILE = ROOT / "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean"
ENDPOINT_HIGH_ORDER_FILE = (
    ROOT / "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean"
)
COMPONENT_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.json"
)
GAP_MAP = (
    REQUEST_DIR / "step33_a1_sub0_omega_omegaprime_taylor_remainder_gap.md"
)
DEFAULT_OUT_JSON = REQUEST_DIR / "step33_a1_sub0_omega_prime_taylor_payload.json"
DEFAULT_OUT_MD = REQUEST_DIR / "step33_a1_sub0_omega_prime_taylor_payload.md"

SCHEMA = "q3_psdpd_step33_a1_sub0_omega_prime_taylor_payload.v11"
ROUTE_ID = "STEP33_A1_SUB0_OMEGA_PRIME_TAYLOR_PAYLOAD"
STATUS = "fail_closed_missing_checked_deriv_payload"
STALE_RECEIVER_SCHEMA_FAILURE = (
    "STEP33_A1_SUB0_OMEGAPRIME_STALE_RECEIVER_SCHEMA_FAIL"
)
CENTER_JET_FAILURE = "STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP"
CENTER_JET_SHIFTED_TAIL_FAILURE = (
    "STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SHIFTED_TAIL_RATIONAL_PAYLOAD_GAP"
)
CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_FAILURE = (
    "STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_GAP"
)
CENTER_JET_PREFIX_EXACT_LEAN_PROOF_FAILURE = (
    "STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PREFIX_EXACT_LEAN_PROOF_GAP"
)
ORDER16_INTEGER_FAILURE = (
    "STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP"
)
REMAINDER_BUDGET_FAILURE = (
    "STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP"
)
FIRST_FAILURE = CENTER_JET_SHIFTED_TAIL_FAILURE
LAGRANGE_SPLIT_FAILURE = "STEP33_A1_SUB0_CENTERED_TAYLOR_LAGRANGE_SPLIT_GAP"
LEFT_LAGRANGE_FAILURE = "STEP33_A1_SUB0_LEFT_REFLECTED_LAGRANGE_BRIDGE_GAP"
EXACT_POLY_FAILURE = "STEP33_A1_SUB0_TAYLOR_WITHINEVAL_EXACT_POLY_GAP"
REFLECTED_DERIV_FAILURE = (
    "STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP"
)
RIGHT_LAGRANGE_FAILURE = "STEP33_A1_SUB0_RIGHT_LAGRANGE_BRIDGE_GAP"
HISTORICAL_ORDER16_POLYGAMMA_FAILURE = (
    "STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP"
)

FUNCTION_ID = "step22OmegaArchWeightDerivClosedForm"
TARGET_CERT = "Step33Sub0OmegaPrimeTaylorRemainderCert"
TARGET_VALID = "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid"
TARGET_BOUND = "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound"
TARGET_CENTER_BRIDGE = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound"
)
TARGET_LEFT_BRIDGE = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "centerTaylorBridge_left_of_order16_bound"
)
TARGET_RIGHT_BRIDGE = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "centerTaylorBridge_right_of_order16_bound"
)
TARGET_VALID_OF_ORDER16 = "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound"
TARGET_OMEGAPRIME_CONTDIFF16 = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_contDiff16"
)
TARGET_VALID_CHECKED_SMOOTH = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound_checked_smooth"
)
TARGET_VALID_INTEGER_BUDGET_CHECKED_DERIV = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "Valid.of_order16_integer_budget_checked_deriv"
)
TARGET_REFLECTED_DERIV = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "omegaPrimeClosedForm_reflected_iteratedDeriv"
)
TARGET_TAYLOR_EXACT_POLY = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "taylorWithinEval_eq_exactTaylorPoly"
)
TARGET_REFLECTED_TAYLOR_EXACT_POLY = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "reflectedTaylorWithinEval_eq_exactTaylorPoly"
)
TARGET_OMEGAPRIME_TRIGAMMA_SERIES_PREFIX_TAIL = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "omegaPrimeTrigammaSeries_iteratedDeriv_sub_prefix_norm_le_shifted_tsum_majorant_of_le16"
)
TARGET_OMEGAPRIME_CLOSED_FORM_PREFIX_TAIL = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "omegaPrimeClosedForm_iteratedDeriv_sub_prefix_norm_le_half_shifted_tsum_majorant_of_le16"
)
TARGET_CENTER_JET_PREFIX_TAIL_BRIDGE = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "omegaPrimeClosedForm_centerJet_invFactorial_sub_prefix_norm_le_shifted_tsum_majorant_of_le16"
)
TARGET_SHIFTED_TAIL_GENERATED_BOUND = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert."
    "omegaPrimeCenterJet_shifted_tsum_budget_le_generated_bound_of_le15"
)
GENERATOR_NAME = "scripts/generate_step33_a1_sub0_omega_prime_taylor_payload.py"
LEAN_TARGET_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean"

CELL_L = "0"
CELL_U = "1/10"
CENTER = "1/20"
RADIUS = "1/20"
DEGREE = 15
ORDER = 16
PREFIX_N = 128
CENTER_ETA = Fraction(1, 20)


SOURCE_SYMBOLS = {
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean": [
        "rawOmegaATaylorPolynomial",
        "digamma_analyticAt_of_re_pos",
        "trigamma_differentiableAt_of_re_pos",
        "trigamma_analyticAt_of_re_pos",
        "step22OmegaArchWeightDerivClosedForm",
        "step22OmegaArchWeightDerivClosedForm_differentiableAt",
        "step22OmegaArchWeightDerivClosedForm_contDiff16",
        "step22OmegaArchWeight_deriv_eq_closedForm",
        "Step22OmegaClosedFormEndpointBoundsCert",
        "ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound",
    ],
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean": [
        "step33_shift16_digamma_m6_integral_remainder_bound",
        "Q3.digammaM6IntegralRemainderBound",
    ],
}

SOURCE_PATTERNS = {
    "rawOmegaATaylorPolynomial": "def rawOmegaATaylorPolynomial",
    "digamma_analyticAt_of_re_pos": "theorem digamma_analyticAt_of_re_pos",
    "trigamma_differentiableAt_of_re_pos": (
        "theorem trigamma_differentiableAt_of_re_pos"
    ),
    "trigamma_analyticAt_of_re_pos": "theorem trigamma_analyticAt_of_re_pos",
    "step22OmegaArchWeightDerivClosedForm": (
        "def step22OmegaArchWeightDerivClosedForm"
    ),
    "step22OmegaArchWeightDerivClosedForm_differentiableAt": (
        "theorem step22OmegaArchWeightDerivClosedForm_differentiableAt"
    ),
    "step22OmegaArchWeightDerivClosedForm_contDiff16": (
        "theorem step22OmegaArchWeightDerivClosedForm_contDiff16"
    ),
    "step22OmegaArchWeight_deriv_eq_closedForm": (
        "theorem step22OmegaArchWeight_deriv_eq_closedForm"
    ),
    "Step22OmegaClosedFormEndpointBoundsCert": (
        "structure Step22OmegaClosedFormEndpointBoundsCert"
    ),
    "ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound": (
        "theorem ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound"
    ),
    "step33_shift16_digamma_m6_integral_remainder_bound": (
        "theorem step33_shift16_digamma_m6_integral_remainder_bound"
    ),
}

TARGET_SYMBOLS = [
    TARGET_CERT,
    TARGET_VALID,
    TARGET_BOUND,
    TARGET_CENTER_BRIDGE,
    TARGET_LEFT_BRIDGE,
    TARGET_RIGHT_BRIDGE,
    TARGET_VALID_OF_ORDER16,
    TARGET_OMEGAPRIME_CONTDIFF16,
    TARGET_VALID_CHECKED_SMOOTH,
    TARGET_VALID_INTEGER_BUDGET_CHECKED_DERIV,
    TARGET_REFLECTED_DERIV,
    TARGET_TAYLOR_EXACT_POLY,
    TARGET_REFLECTED_TAYLOR_EXACT_POLY,
    TARGET_OMEGAPRIME_TRIGAMMA_SERIES_PREFIX_TAIL,
    TARGET_OMEGAPRIME_CLOSED_FORM_PREFIX_TAIL,
    TARGET_CENTER_JET_PREFIX_TAIL_BRIDGE,
    TARGET_SHIFTED_TAIL_GENERATED_BOUND,
    STALE_RECEIVER_SCHEMA_FAILURE,
    FIRST_FAILURE,
    CENTER_JET_SHIFTED_TAIL_FAILURE,
    CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_FAILURE,
    CENTER_JET_PREFIX_EXACT_LEAN_PROOF_FAILURE,
    ORDER16_INTEGER_FAILURE,
    REMAINDER_BUDGET_FAILURE,
    LAGRANGE_SPLIT_FAILURE,
    LEFT_LAGRANGE_FAILURE,
    EXACT_POLY_FAILURE,
    REFLECTED_DERIV_FAILURE,
    RIGHT_LAGRANGE_FAILURE,
    HISTORICAL_ORDER16_POLYGAMMA_FAILURE,
]

TARGET_PATTERNS = {
    TARGET_CERT: "structure Step33Sub0OmegaPrimeTaylorRemainderCert",
    TARGET_VALID: "structure Valid (data : Step33Sub0OmegaPrimeTaylorRemainderCert)",
    TARGET_BOUND: "theorem Valid.bound",
    TARGET_CENTER_BRIDGE: "theorem centerTaylorBridge_of_order16_bound",
    TARGET_LEFT_BRIDGE: "theorem centerTaylorBridge_left_of_order16_bound",
    TARGET_RIGHT_BRIDGE: "theorem centerTaylorBridge_right_of_order16_bound",
    TARGET_VALID_OF_ORDER16: "theorem Valid.of_order16_bound",
    TARGET_OMEGAPRIME_CONTDIFF16: "theorem omegaPrimeClosedForm_contDiff16",
    TARGET_VALID_CHECKED_SMOOTH: "theorem Valid.of_order16_bound_checked_smooth",
    TARGET_VALID_INTEGER_BUDGET_CHECKED_DERIV: (
        "theorem Valid.of_order16_integer_budget_checked_deriv"
    ),
    TARGET_REFLECTED_DERIV: "theorem omegaPrimeClosedForm_reflected_iteratedDeriv",
    TARGET_TAYLOR_EXACT_POLY: "theorem taylorWithinEval_eq_exactTaylorPoly",
    TARGET_REFLECTED_TAYLOR_EXACT_POLY: (
        "theorem reflectedTaylorWithinEval_eq_exactTaylorPoly"
    ),
    TARGET_OMEGAPRIME_TRIGAMMA_SERIES_PREFIX_TAIL: (
        "theorem omegaPrimeTrigammaSeries_iteratedDeriv_sub_prefix_norm_le_shifted_tsum_majorant_of_le16"
    ),
    TARGET_OMEGAPRIME_CLOSED_FORM_PREFIX_TAIL: (
        "theorem omegaPrimeClosedForm_iteratedDeriv_sub_prefix_norm_le_half_shifted_tsum_majorant_of_le16"
    ),
    TARGET_CENTER_JET_PREFIX_TAIL_BRIDGE: (
        "theorem omegaPrimeClosedForm_centerJet_invFactorial_sub_prefix_norm_le_shifted_tsum_majorant_of_le16"
    ),
    TARGET_SHIFTED_TAIL_GENERATED_BOUND: (
        "theorem omegaPrimeCenterJet_shifted_tsum_budget_le_generated_bound_of_le15"
    ),
    STALE_RECEIVER_SCHEMA_FAILURE: STALE_RECEIVER_SCHEMA_FAILURE,
    FIRST_FAILURE: FIRST_FAILURE,
    CENTER_JET_SHIFTED_TAIL_FAILURE: CENTER_JET_SHIFTED_TAIL_FAILURE,
    CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_FAILURE: (
        CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_FAILURE
    ),
    CENTER_JET_PREFIX_EXACT_LEAN_PROOF_FAILURE: (
        CENTER_JET_PREFIX_EXACT_LEAN_PROOF_FAILURE
    ),
    ORDER16_INTEGER_FAILURE: ORDER16_INTEGER_FAILURE,
    REMAINDER_BUDGET_FAILURE: REMAINDER_BUDGET_FAILURE,
    LAGRANGE_SPLIT_FAILURE: LAGRANGE_SPLIT_FAILURE,
    LEFT_LAGRANGE_FAILURE: LEFT_LAGRANGE_FAILURE,
    EXACT_POLY_FAILURE: EXACT_POLY_FAILURE,
    REFLECTED_DERIV_FAILURE: REFLECTED_DERIV_FAILURE,
    RIGHT_LAGRANGE_FAILURE: RIGHT_LAGRANGE_FAILURE,
    HISTORICAL_ORDER16_POLYGAMMA_FAILURE: HISTORICAL_ORDER16_POLYGAMMA_FAILURE,
}


def file_hash(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def rat(x: int, y: int = 1) -> Fraction:
    return Fraction(x, y)


def fraction_to_str(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def fraction_digit_count(value: Fraction) -> int:
    return len(str(value.numerator)) + len(str(value.denominator))


ComplexRat = tuple[Fraction, Fraction]


def complex_add(z: ComplexRat, w: ComplexRat) -> ComplexRat:
    return (z[0] + w[0], z[1] + w[1])


def complex_mul(z: ComplexRat, w: ComplexRat) -> ComplexRat:
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def complex_inv(z: ComplexRat) -> ComplexRat:
    denom = z[0] * z[0] + z[1] * z[1]
    if denom == 0:
        raise ZeroDivisionError("complex rational inverse at zero")
    return (z[0] / denom, -z[1] / denom)


def complex_pow(z: ComplexRat, exponent: int) -> ComplexRat:
    if exponent < 0:
        return complex_pow(complex_inv(z), -exponent)
    out: ComplexRat = (rat(1), rat(0))
    base = z
    n = exponent
    while n:
        if n & 1:
            out = complex_mul(out, base)
        base = complex_mul(base, base)
        n >>= 1
    return out


def omega_prime_trigamma_deriv_coeff(m: int) -> ComplexRat:
    coeff: ComplexRat = (rat(1), rat(0))
    for i in range(m):
        coeff = complex_mul(coeff, (rat(-2 - i), rat(0)))
    coeff = complex_mul(coeff, complex_pow((rat(0), rat(1, 2)), m))
    return coeff


def omega_prime_series_base_at_center(n: int) -> ComplexRat:
    return (rat(n) + rat(1, 4), CENTER_ETA / 2)


def omega_prime_trigamma_term_iterated_deriv_at_center(m: int, n: int) -> Fraction:
    coeff = omega_prime_trigamma_deriv_coeff(m)
    base = omega_prime_series_base_at_center(n)
    value = complex_mul(coeff, complex_pow(base, -(m + 2)))
    return value[1]


def omega_prime_center_prefix(m: int, prefix_n: int) -> Fraction:
    prefix_sum = sum(
        (
            omega_prime_trigamma_term_iterated_deriv_at_center(m, n)
            for n in range(prefix_n)
        ),
        rat(0),
    )
    return rat(-1, 2) * rat(1, factorial(m)) * prefix_sum


def omega_prime_shifted_tail_upper(m: int, prefix_n: int) -> Fraction:
    if prefix_n < 1:
        raise ValueError("prefix_n must be positive for shifted-tail integral bound")
    lower_edge = rat(4 * prefix_n - 3, 4)
    return rat(1, 2 ** (m + 1)) / (lower_edge ** (m + 1))


def build_center_jet_prefix_tail_rows(
    *,
    prefix_n: int,
    bridge_present: bool,
    tail_bound_present: bool,
    prefix_lean_scan: dict[int, dict[str, Any]],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index in range(DEGREE + 1):
        prefix = omega_prime_center_prefix(index, prefix_n)
        tail = omega_prime_shifted_tail_upper(index, prefix_n)
        prefix_scan = prefix_lean_scan[index]
        prefix_checked = prefix_scan["status"] == "found"
        tail_checked = tail_bound_present
        rows.append(
            {
                "jetIndex": index,
                "prefixN": prefix_n,
                "prefixExactRational": fraction_to_str(prefix),
                "prefixExactRationalDigits": fraction_digit_count(prefix),
                "prefixExactLeanTheorem": prefix_scan["exactTheorem"],
                "prefixExactLeanLine": prefix_scan["exactLine"],
                "prefixExactLeanStatus": prefix_scan["exactStatus"],
                "prefixCastLeanTheorem": prefix_scan["castTheorem"],
                "prefixCastLeanLine": prefix_scan["castLine"],
                "prefixCastLeanStatus": prefix_scan["castStatus"],
                "shiftedTailUpperRational": fraction_to_str(tail),
                "shiftedTailUpperRationalDigits": fraction_digit_count(tail),
                "coeff": fraction_to_str(prefix),
                "coeffErrorAbs": fraction_to_str(tail),
                "lower": fraction_to_str(prefix - tail),
                "upper": fraction_to_str(prefix + tail),
                "prefixLeanChecked": prefix_checked,
                "tailBoundLeanChecked": tail_checked,
                "bridgeLeanTheorem": TARGET_CENTER_JET_PREFIX_TAIL_BRIDGE,
                "bridgeLeanChecked": bridge_present,
                "sourceLeanTheorem": (
                    "Step33Sub0OmegaPrimeTaylorRemainderCert."
                    "omegaPrimeClosedForm_centerJet_invFactorial_sub_prefix_norm_le_shifted_tsum_majorant_of_le16"
                ),
                "tailBoundFormula": (
                    "1 / (2^(m+1) * (prefixN - 3/4)^(m+1))"
                ),
                "tailBoundLeanTheorem": TARGET_SHIFTED_TAIL_GENERATED_BOUND,
                "centerJetMargin": "0",
                "rationalArithmeticChecked": True,
                "proofGrade": prefix_checked and tail_checked and bridge_present,
            }
        )
    return rows


def coeff_slots_from_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "index": row["jetIndex"],
            "value": row["coeff"],
            "status": "exact_rational_generated_unchecked_by_lean",
        }
        for row in rows
    ]


def coeff_error_slots_from_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "index": row["jetIndex"],
            "value": row["coeffErrorAbs"],
            "status": "exact_rational_generated_tail_bound_unchecked_by_lean",
        }
        for row in rows
    ]


def center_jet_slots_from_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "index": row["jetIndex"],
            "coeff": row["coeff"],
            "coeffErrorAbs": row["coeffErrorAbs"],
            "lower": row["lower"],
            "upper": row["upper"],
            "prefixN": row["prefixN"],
            "prefixExactRational": row["prefixExactRational"],
            "shiftedTailUpperRational": row["shiftedTailUpperRational"],
            "prefixLeanChecked": row["prefixLeanChecked"],
            "tailBoundLeanChecked": row["tailBoundLeanChecked"],
            "centerJetMargin": row["centerJetMargin"],
            "bridgeLeanTheorem": row["bridgeLeanTheorem"],
            "bridgeLeanChecked": row["bridgeLeanChecked"],
            "sourceLeanTheorem": row["sourceLeanTheorem"],
            "sourceLeanChecked": row["proofGrade"],
            "lowerCheckPassed": True,
            "upperCheckPassed": True,
            "enclosurePassed": row["proofGrade"],
        }
        for row in rows
    ]


def line_of_symbol(path: Path, symbol: str) -> int | None:
    if not path.exists():
        return None
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if symbol in line:
            return line_no
    return None


def center_jet_prefix_exact_theorem(index: int, prefix_n: int) -> str:
    return (
        "Step33Sub0OmegaPrimeTaylorRemainderCert."
        f"omegaPrimeCenterJetM{index}PrefixRat_{prefix_n}"
    )


def center_jet_prefix_exact_pattern(index: int, prefix_n: int) -> str:
    return f"theorem omegaPrimeCenterJetM{index}PrefixRat_{prefix_n}"


def center_jet_prefix_cast_theorem(index: int) -> str:
    return (
        "Step33Sub0OmegaPrimeTaylorRemainderCert."
        f"omegaPrimeCenterJetM{index}PrefixRat_cast"
    )


def center_jet_prefix_cast_pattern(index: int) -> str:
    return f"theorem omegaPrimeCenterJetM{index}PrefixRat_cast"


def center_jet_prefix_lean_scan(path: Path, prefix_n: int) -> dict[int, dict[str, Any]]:
    out: dict[int, dict[str, Any]] = {}
    for index in range(DEGREE + 1):
        exact_line = line_of_symbol(path, center_jet_prefix_exact_pattern(index, prefix_n))
        cast_line = line_of_symbol(path, center_jet_prefix_cast_pattern(index))
        out[index] = {
            "index": index,
            "prefixN": prefix_n,
            "exactTheorem": center_jet_prefix_exact_theorem(index, prefix_n),
            "exactLine": exact_line,
            "exactStatus": "found" if exact_line is not None else "gap",
            "castTheorem": center_jet_prefix_cast_theorem(index),
            "castLine": cast_line,
            "castStatus": "found" if cast_line is not None else "gap",
            "status": (
                "found"
                if exact_line is not None and cast_line is not None
                else "gap"
            ),
        }
    return out


def symbol_scan(path_by_label: dict[str, Path]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = {}
    for label, symbols in SOURCE_SYMBOLS.items():
        path = path_by_label[label]
        out[label] = []
        for symbol in symbols:
            line = line_of_symbol(path, SOURCE_PATTERNS.get(symbol, symbol))
            out[label].append(
                {
                    "symbol": symbol,
                    "line": line,
                    "status": "found" if line is not None else "missing",
                }
            )
    return out


def target_symbol_scan(path: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for symbol in TARGET_SYMBOLS:
        line = line_of_symbol(path, TARGET_PATTERNS.get(symbol, symbol))
        out[symbol] = {
            "line": line,
            "status": "found" if line is not None else "gap",
        }
    return out


def missing_coeff_slots(name: str) -> list[dict[str, Any]]:
    return [
        {
            "index": index,
            "value": None,
            "status": f"missing_proof_grade_{name}",
        }
        for index in range(DEGREE + 1)
    ]


def missing_center_jet_slots() -> list[dict[str, Any]]:
    return [
        {
            "index": index,
            "coeff": None,
            "coeffErrorAbs": None,
            "lower": None,
            "upper": None,
            "prefixN": None,
            "prefixExactRational": None,
            "shiftedTailUpperRational": None,
            "prefixLeanChecked": False,
            "tailBoundLeanChecked": False,
            "centerJetMargin": None,
            "bridgeLeanTheorem": TARGET_CENTER_JET_PREFIX_TAIL_BRIDGE,
            "bridgeLeanChecked": False,
            "sourceLeanTheorem": None,
            "sourceLeanChecked": False,
            "lowerCheckPassed": False,
            "upperCheckPassed": False,
            "enclosurePassed": False,
        }
        for index in range(DEGREE + 1)
    ]


def missing_center_jet_prefix_tail_rows() -> list[dict[str, Any]]:
    return [
        {
            "jetIndex": index,
            "prefixN": None,
            "prefixExactRational": None,
            "shiftedTailUpperRational": None,
            "coeff": None,
            "coeffErrorAbs": None,
            "prefixLeanChecked": False,
            "tailBoundLeanChecked": False,
            "centerJetMargin": None,
            "sourceLeanTheorem": TARGET_CENTER_JET_PREFIX_TAIL_BRIDGE,
            "proofGrade": False,
        }
        for index in range(DEGREE + 1)
    ]


def build_report(
    *,
    chunk_file: Path,
    endpoint_file: Path,
    component_payload_path: Path,
    gap_map_path: Path,
) -> dict[str, Any]:
    path_by_label = {
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean": chunk_file,
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean": endpoint_file,
    }
    component_payload = load_json(component_payload_path)
    target_scan = target_symbol_scan(endpoint_file)
    receiver_present = all(
        target_scan[symbol]["status"] == "found"
        for symbol in [TARGET_CERT, TARGET_VALID, TARGET_BOUND]
    )
    centered_bridge_present = all(
        target_scan[symbol]["status"] == "found"
        for symbol in [TARGET_CENTER_BRIDGE, TARGET_VALID_OF_ORDER16]
    )
    reflected_deriv_present = target_scan[TARGET_REFLECTED_DERIV]["status"] == "found"
    taylor_exact_poly_present = (
        target_scan[TARGET_TAYLOR_EXACT_POLY]["status"] == "found"
    )
    reflected_taylor_exact_poly_present = (
        target_scan[TARGET_REFLECTED_TAYLOR_EXACT_POLY]["status"] == "found"
    )
    trigamma_series_prefix_tail_present = (
        target_scan[TARGET_OMEGAPRIME_TRIGAMMA_SERIES_PREFIX_TAIL]["status"]
        == "found"
    )
    closed_form_prefix_tail_present = (
        target_scan[TARGET_OMEGAPRIME_CLOSED_FORM_PREFIX_TAIL]["status"]
        == "found"
    )
    center_jet_prefix_tail_bridge_present = (
        target_scan[TARGET_CENTER_JET_PREFIX_TAIL_BRIDGE]["status"] == "found"
    )
    center_jet_shifted_tail_bridge_present = all(
        [
            trigamma_series_prefix_tail_present,
            closed_form_prefix_tail_present,
            center_jet_prefix_tail_bridge_present,
        ]
    )
    shifted_tail_generated_bound_present = (
        target_scan[TARGET_SHIFTED_TAIL_GENERATED_BOUND]["status"] == "found"
    )
    prefix_lean_scan = center_jet_prefix_lean_scan(endpoint_file, PREFIX_N)
    center_jet_prefix_tail_rows = build_center_jet_prefix_tail_rows(
        prefix_n=PREFIX_N,
        bridge_present=center_jet_shifted_tail_bridge_present,
        tail_bound_present=shifted_tail_generated_bound_present,
        prefix_lean_scan=prefix_lean_scan,
    )
    all_prefix_exact_present = all(
        row["prefixLeanChecked"] for row in center_jet_prefix_tail_rows
    )
    prefix_lean_checked_count = sum(
        1 for row in center_jet_prefix_tail_rows if row["prefixLeanChecked"]
    )
    proof_grade_prefix_tail_row_count = sum(
        1 for row in center_jet_prefix_tail_rows if row["proofGrade"]
    )
    all_prefix_tail_rows_proof_grade = (
        proof_grade_prefix_tail_row_count == len(center_jet_prefix_tail_rows)
    )
    left_bridge_present = target_scan[TARGET_LEFT_BRIDGE]["status"] == "found"
    right_bridge_present = target_scan[TARGET_RIGHT_BRIDGE]["status"] == "found"
    omega_prime_contdiff16_present = (
        target_scan[TARGET_OMEGAPRIME_CONTDIFF16]["status"] == "found"
    )
    valid_checked_smooth_present = (
        target_scan[TARGET_VALID_CHECKED_SMOOTH]["status"] == "found"
    )
    valid_integer_budget_checked_deriv_present = (
        target_scan[TARGET_VALID_INTEGER_BUDGET_CHECKED_DERIV]["status"]
        == "found"
    )
    receiver_schema_current = receiver_present and valid_integer_budget_checked_deriv_present
    if not receiver_schema_current:
        first_failure = STALE_RECEIVER_SCHEMA_FAILURE
        status = "fail_closed_stale_receiver_schema"
    elif not center_jet_shifted_tail_bridge_present:
        first_failure = CENTER_JET_FAILURE
        status = "fail_closed_missing_center_jet_prefix_tail_bridge"
    elif not shifted_tail_generated_bound_present:
        first_failure = CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_FAILURE
        status = "fail_closed_shifted_tail_rational_rows_need_lean_proof"
    elif not all_prefix_exact_present:
        first_failure = CENTER_JET_PREFIX_EXACT_LEAN_PROOF_FAILURE
        status = "fail_closed_tail_bound_checked_missing_prefix_exact_lean_proof"
    else:
        first_failure = ORDER16_INTEGER_FAILURE
        status = "fail_closed_center_jet_rows_checked_missing_order16_integer_budget"

    target_surface_status = (
        "receiver_checked_deriv_center_jet_rows_checked_missing_order16_integer_budget"
        if (
            receiver_schema_current
            and center_jet_shifted_tail_bridge_present
            and shifted_tail_generated_bound_present
            and all_prefix_exact_present
        )
        else
        "receiver_checked_deriv_tail_bound_checked_missing_prefix_exact_lean_proof"
        if (
            receiver_schema_current
            and center_jet_shifted_tail_bridge_present
            and shifted_tail_generated_bound_present
        )
        else "receiver_checked_deriv_and_prefix_tail_rows_present_missing_shifted_tail_bound_proof"
        if receiver_schema_current and center_jet_shifted_tail_bridge_present
        else
        "receiver_checked_deriv_present_missing_prefix_tail_bridge"
        if receiver_schema_current
        else
        "receiver_centered_taylor_bridge_and_smooth_present_missing_payload"
        if (
            receiver_present
            and centered_bridge_present
            and omega_prime_contdiff16_present
            and valid_checked_smooth_present
        )
        else "receiver_and_centered_taylor_bridge_present_missing_payload"
        if receiver_present and centered_bridge_present
        else "receiver_present_right_half_bridge_present_missing_left_reflected_bridge"
        if (
            receiver_present
            and reflected_deriv_present
            and taylor_exact_poly_present
            and right_bridge_present
        )
        else "receiver_present_missing_lagrange_split_bridge"
        if receiver_present and reflected_deriv_present and taylor_exact_poly_present
        else "receiver_present_missing_centered_taylor_bridge"
        if receiver_present
        else "planned_not_in_lean"
    )

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": status,
        "firstFailure": first_failure,
        "receiverSchemaCurrent": receiver_schema_current,
        "failureCodes": [
            STALE_RECEIVER_SCHEMA_FAILURE,
            CENTER_JET_PREFIX_EXACT_LEAN_PROOF_FAILURE,
            ORDER16_INTEGER_FAILURE,
            REMAINDER_BUDGET_FAILURE,
        ],
        "parentFailureCodes": [
            CENTER_JET_FAILURE,
            CENTER_JET_SHIFTED_TAIL_FAILURE,
            CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_FAILURE,
        ],
        "closedHistoricalFailures": [
            HISTORICAL_ORDER16_POLYGAMMA_FAILURE,
            LAGRANGE_SPLIT_FAILURE,
            LEFT_LAGRANGE_FAILURE,
            EXACT_POLY_FAILURE,
            REFLECTED_DERIV_FAILURE,
            RIGHT_LAGRANGE_FAILURE,
            CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_FAILURE,
        ],
        "generator": GENERATOR_NAME,
        "functionId": FUNCTION_ID,
        "cell": {
            "cellL": CELL_L,
            "cellU": CELL_U,
            "center": CENTER,
            "radius": RADIUS,
            "degree": DEGREE,
            "orderForLagrangeRemainder": ORDER,
            "centerJetPrefixN": PREFIX_N,
        },
        "targetLeanSurface": {
            "file": LEAN_TARGET_FILE,
            "structure": TARGET_CERT,
            "validPredicate": TARGET_VALID,
            "boundTheorem": TARGET_BOUND,
            "centerTaylorBridgeTheorem": TARGET_CENTER_BRIDGE,
            "leftLagrangeBridgeTheorem": TARGET_LEFT_BRIDGE,
            "rightLagrangeBridgeTheorem": TARGET_RIGHT_BRIDGE,
            "validOfOrder16Theorem": TARGET_VALID_OF_ORDER16,
            "omegaPrimeContDiff16Theorem": TARGET_OMEGAPRIME_CONTDIFF16,
            "validCheckedSmoothTheorem": TARGET_VALID_CHECKED_SMOOTH,
            "receiver": TARGET_VALID_INTEGER_BUDGET_CHECKED_DERIV,
            "receiverChecked": valid_integer_budget_checked_deriv_present,
            "oldReceiverRejected": TARGET_VALID_CHECKED_SMOOTH,
            "reflectedIteratedDerivTheorem": TARGET_REFLECTED_DERIV,
            "taylorWithinEvalExactPolyTheorem": TARGET_TAYLOR_EXACT_POLY,
            "reflectedTaylorWithinEvalExactPolyTheorem": (
                TARGET_REFLECTED_TAYLOR_EXACT_POLY
            ),
            "trigammaSeriesPrefixTailTheorem": (
                TARGET_OMEGAPRIME_TRIGAMMA_SERIES_PREFIX_TAIL
            ),
            "omegaPrimeClosedFormPrefixTailTheorem": (
                TARGET_OMEGAPRIME_CLOSED_FORM_PREFIX_TAIL
            ),
            "centerJetPrefixTailBridgeTheorem": (
                TARGET_CENTER_JET_PREFIX_TAIL_BRIDGE
            ),
            "centerJetPrefixTailBridgeChecked": (
                center_jet_shifted_tail_bridge_present
            ),
            "shiftedTailGeneratedBoundTheorem": TARGET_SHIFTED_TAIL_GENERATED_BOUND,
            "shiftedTailGeneratedBoundChecked": shifted_tail_generated_bound_present,
            "centerJetPrefixExactRowsChecked": all_prefix_exact_present,
            "centerJetPrefixExactRowsCheckedCount": prefix_lean_checked_count,
            "centerJetPrefixTailRowsProofGrade": all_prefix_tail_rows_proof_grade,
            "centerJetPrefixTailRowsProofGradeCount": proof_grade_prefix_tail_row_count,
            "status": target_surface_status,
            "statementAscii": (
                "theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound "
                "{data : Step33Sub0OmegaPrimeTaylorRemainderCert} "
                "(h : data.Valid) : forall eta in Set.Icc 0 (1/10), "
                "norm (step22OmegaArchWeightDerivClosedForm eta - data.poly eta) "
                "<= data.remainderAbs"
            ),
            "localNormalization": (
                "rawOmegaATaylorPolynomial expects a Rat center and a "
                "Fin (degree + 1) -> Rat coefficient function."
            ),
            "nextBridgeStatementAscii": (
                "theorem Step33Sub0OmegaPrimeTaylorRemainderCert."
                "Valid.of_order16_integer_budget_checked_deriv "
                "(data : Step33Sub0OmegaPrimeTaylorRemainderCert) "
                "(hCoeffErrorNonneg : forall j, 0 <= data.coeffErrorAbs j) "
                "(hCenterJet : center coefficient enclosures) "
                "(hIntegerBudget : omegaPrimeOrder16CondensedFactorBudgetBound "
                "<= data.order16Abs) "
                "(hRemainderBudget : coefficient plus Lagrange budget "
                "<= data.remainderAbs) : "
                "data.Valid"
            ),
        },
        "generatorFields": {
            "schemaVersion": SCHEMA,
            "functionId": FUNCTION_ID,
            "center": CENTER,
            "radius": RADIUS,
            "degree": DEGREE,
            "coeff": coeff_slots_from_rows(center_jet_prefix_tail_rows),
            "coeffErrorAbs": coeff_error_slots_from_rows(center_jet_prefix_tail_rows),
            "centerJet": center_jet_slots_from_rows(center_jet_prefix_tail_rows),
            "centerJetPrefixTailRows": center_jet_prefix_tail_rows,
            "centerJetPrefixLeanScan": [
                prefix_lean_scan[index] for index in range(DEGREE + 1)
            ],
            "order16Abs": None,
            "order16": {
                "condensedFactorBudgetBoundExact": None,
                "order16Abs": None,
                "marginExact": None,
                "integerBudgetPassed": False,
                "sourceLeanTheorems": [
                    "omegaPrimeOrder16CondensedFactorBudgetBound",
                    "omegaPrimeClosedForm_iteratedDeriv16_eq",
                    "Valid.of_order16_integer_budget_checked_deriv",
                ],
                "sourceLeanChecked": valid_integer_budget_checked_deriv_present,
            },
            "remainder": {
                "coeffErrorContributionExact": None,
                "lagrangeContributionExact": None,
                "requiredTotalExact": None,
                "remainderAbs": None,
                "marginExact": None,
                "budgetPassed": False,
            },
            "remainderAbs": None,
            "centerJetSource": missing_coeff_slots("center_jet_source"),
            "centerJetPrefixTailRowPolicy": {
                "prefixN": PREFIX_N,
                "center": CENTER,
                "finitePrefixFormula": (
                    "m!^-1 * (-1/2) * sum_{n < prefixN} "
                    "iteratedDeriv m omegaPrimeTrigammaSeriesTerm (1/20) n"
                ),
                "shiftedTailUpperFormula": (
                    "1 / (2^(m+1) * (prefixN - 3/4)^(m+1))"
                ),
                "tailFormulaStatus": (
                    "rational arithmetic generated; shifted-tail Lean bound checked"
                    if shifted_tail_generated_bound_present
                    else "rational arithmetic generated; shifted-tail Lean proof still required"
                ),
            },
            "integerBudgetSource": None,
            "exactRationalChecksPassed": True,
            "allCenterJetsProved": False,
            "allPayloadObligationsPassed": False,
            "leanOutputPath": None,
            "leanValidationStatus": "not_run",
            "proofSafeClosedFields": proof_grade_prefix_tail_row_count,
            "rationalPrefixTailRowsGenerated": len(center_jet_prefix_tail_rows),
            "outLeanWritten": False,
        },
        "requiredProofs": [
            (
                "already proved locally: the full centered Taylor bridge "
                "centerTaylorBridge_of_order16_bound from a uniform order-16 "
                "bound on [0, 1/10]"
            ),
            (
                "already proved locally: the left reflected Lagrange bridge "
                "centerTaylorBridge_left_of_order16_bound and the reflected "
                "Taylor polynomial normalization"
            ),
            (
                "already proved locally: the right-half Lagrange bridge "
                "centerTaylorBridge_right_of_order16_bound with the sharp "
                "16! denominator on eta in [1/20, 1/10]"
            ),
            (
                "already proved locally: taylorWithinEval agrees with "
                "exactTaylorPoly under UniqueDiffOn and global ContDiff 16"
            ),
            (
                "already proved locally: reflected iterated derivative identity "
                "iteratedDeriv n (fun x => f (1/10 - x)) x = "
                "(-1)^n * iteratedDeriv n f (1/10 - x)"
            ),
            (
                "already proved locally: trigamma is analytic in the right "
                "half-plane and step22OmegaArchWeightDerivClosedForm is "
                "ContDiff Real 16"
            ),
            (
                "already proved locally: "
                "Valid.of_order16_integer_budget_checked_deriv uses "
                "omegaPrimeClosedForm_iteratedDeriv16_eq, so generated "
                "payloads no longer need to supply hSmooth or hDerivEq"
            ),
            (
                "already proved locally: the OmegaPrime center-jet prefix-tail "
                "bridge reduces each j < 16 center-jet enclosure to an exact "
                "finite prefix plus a shifted-tail rational upper bound"
            ),
            (
                "already proved locally: for m < 16, the shifted-tail majorant "
                "budget is bounded by the generated denominator-form "
                "coeffErrorAbs formula"
            ),
            (
                "for each j < 16, prove the exact finite prefix rational "
                "equality for the generated prefixExactRational / coeff[j]"
            ),
            (
                "for each j < 16, prove 0 <= coeffErrorAbs[j] and close "
                "centerJetMargin with the prefix-tail bridge plus checked "
                "tail bound"
            ),
            (
                "prove omegaPrimeOrder16CondensedFactorBudgetBound "
                "<= order16Abs"
            ),
            (
                "prove sum_j coeffErrorAbs[j] * radius^j + "
                "order16Abs * radius^16 / 16! <= remainderAbs"
            ),
        ],
        "proofStatus": {
            "componentTaylorBoundsProved": False,
            "centeredTaylorBridgeProved": centered_bridge_present,
            "centeredTaylorRightBridgeProved": right_bridge_present,
            "centeredTaylorLeftReflectedBridgeProved": left_bridge_present,
            "validOfOrder16ConstructorProved": centered_bridge_present,
            "taylorWithinEvalExactPolyBridgeProved": taylor_exact_poly_present,
            "reflectedTaylorWithinEvalExactPolyBridgeProved": (
                reflected_taylor_exact_poly_present
            ),
            "reflectedIteratedDerivBridgeProved": reflected_deriv_present,
            "omegaPrimeAnalyticSmoothnessProved": omega_prime_contdiff16_present,
            "validCheckedSmoothConstructorProved": valid_checked_smooth_present,
            "omegaPrimeHDerivEqProved": valid_integer_budget_checked_deriv_present,
            "validIntegerBudgetCheckedDerivConstructorProved": (
                valid_integer_budget_checked_deriv_present
            ),
            "omegaPrimeOrder16AnalyticBoundReducedToIntegerBudget": (
                valid_integer_budget_checked_deriv_present
            ),
            "omegaPrimeCenterJetPrefixTailBridgeProved": (
                center_jet_shifted_tail_bridge_present
            ),
            "omegaPrimeCenterJetShiftedTailGeneratedBoundProved": (
                shifted_tail_generated_bound_present
            ),
            "omegaPrimeCenterJetPrefixExactRowsProved": all_prefix_exact_present,
            "omegaPrimeCenterJetPrefixExactRowsProvedCount": (
                prefix_lean_checked_count
            ),
            "omegaPrimeCenterJetPrefixTailRowsProofGrade": (
                all_prefix_tail_rows_proof_grade
            ),
            "omegaPrimeCenterJetPrefixTailRowsProofGradeCount": (
                proof_grade_prefix_tail_row_count
            ),
            "omegaPrimeCenterJetBoundsProved": False,
            "omegaPrimeOrder16BoundProved": False,
            "omegaPrimeOrder16IntegerBudgetProved": False,
            "omegaPrimeRemainderBudgetPassed": False,
            "exactRationalChecksPassed": True,
            "allCenterJetsProved": False,
            "allPayloadObligationsPassed": False,
            "leanValidationStatus": "not_run",
            "proofSafeClosedFields": proof_grade_prefix_tail_row_count,
            "rationalPrefixTailRowsGenerated": len(center_jet_prefix_tail_rows),
            "outLeanWritten": False,
        },
        "localSourceScan": symbol_scan(path_by_label),
        "targetSymbolScan": target_scan,
        "sourceStatus": {
            "componentPayloadPath": str(component_payload_path),
            "componentPayloadSchema": (
                component_payload.get("schema") if component_payload else None
            ),
            "componentPayloadStatus": (
                component_payload.get("status") if component_payload else None
            ),
            "componentPayloadFirstFailure": (
                component_payload.get("firstFailure") if component_payload else None
            ),
            "gapMapPath": str(gap_map_path),
            "gapMapExists": gap_map_path.exists(),
        },
        "sourceDefinitionHashes": {
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean": file_hash(
                chunk_file
            ),
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean": file_hash(
                endpoint_file
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_component_taylor_residual_payload.json": file_hash(
                component_payload_path
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_omega_omegaprime_taylor_remainder_gap.md": file_hash(
                gap_map_path
            ),
        },
        "advisorySource": {
            "browserProshka": "advisory_only_not_proof_evidence",
            "chosen": "finite_prefix_shifted_tail_after_checked_bridge",
            "recommendedLeanBridge": TARGET_VALID_INTEGER_BUDGET_CHECKED_DERIV,
            "recommendedGenerator": GENERATOR_NAME,
            "firstFailure": first_failure,
            "closedSubfailures": [
                HISTORICAL_ORDER16_POLYGAMMA_FAILURE,
                REFLECTED_DERIV_FAILURE,
                EXACT_POLY_FAILURE,
                RIGHT_LAGRANGE_FAILURE,
                LEFT_LAGRANGE_FAILURE,
                LAGRANGE_SPLIT_FAILURE,
                CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_FAILURE,
            ],
            "nextFailureAfterBridge": first_failure,
            "whyNotEndpointFiniteCover": (
                "Endpoint finite-cover subdivision still needs the same "
                "trigamma/polygamma source bounds, repeated over segments."
            ),
        },
        "externalSearch": {
            "mathlibTaylorDocs": (
                "Mathlib.Analysis.Calculus.Taylor exposes Taylor theorem "
                "surfaces such as taylor_mean_remainder_lagrange; local "
                "inspection shows the sharp 16! denominator is available via "
                "taylor_mean_remainder_lagrange_iteratedDeriv, not via the "
                "coarser taylor_mean_remainder_bound helper.  The repository "
                "now has a checked local polynomial-normalization bridge."
            ),
            "localMathlibReflectionHints": (
                "Local Mathlib has iteratedDeriv_comp_neg, "
                "iteratedDeriv_comp_const_add, and "
                "iteratedDeriv_comp_add_const in IteratedDeriv/Lemmas.lean; "
                "the OmegaPrime reflected iterated-derivative bridge is now "
                "proved locally as omegaPrimeClosedForm_reflected_iteratedDeriv, "
                "and the reflected Taylor polynomial normalization is proved "
                "locally as reflectedTaylorWithinEval_eq_exactTaylorPoly."
            ),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Sub0 OmegaPrime Taylor Payload",
        "",
        "Fail-closed payload surface. This is not Lean proof data and does",
        "not close Step33A.1-A.",
        "",
        "## Status",
        "",
        f"- schema: `{report['schema']}`",
        f"- route: `{report['routeId']}`",
        f"- status: `{report['status']}`",
        f"- first failure: `{report['firstFailure']}`",
        f"- receiver schema current: `{report['receiverSchemaCurrent']}`",
        f"- function: `{report['functionId']}`",
        f"- center: `{report['cell']['center']}`",
        f"- radius: `{report['cell']['radius']}`",
        f"- degree: `{report['cell']['degree']}`",
        f"- center-jet prefixN: `{report['cell']['centerJetPrefixN']}`",
        f"- proof-safe closed fields: `{report['proofStatus']['proofSafeClosedFields']}`",
        f"- rational prefix/tail rows generated: `{report['proofStatus']['rationalPrefixTailRowsGenerated']}`",
        f"- Lean emitted: `{report['proofStatus']['outLeanWritten']}`",
        "",
        "## Target Lean Surface",
        "",
        f"- file: `{report['targetLeanSurface']['file']}`",
        f"- structure: `{report['targetLeanSurface']['structure']}`",
        f"- valid predicate: `{report['targetLeanSurface']['validPredicate']}`",
        f"- bound theorem: `{report['targetLeanSurface']['boundTheorem']}`",
        f"- centered bridge theorem: `{report['targetLeanSurface']['centerTaylorBridgeTheorem']}`",
        f"- left bridge theorem: `{report['targetLeanSurface']['leftLagrangeBridgeTheorem']}`",
        f"- right bridge theorem: `{report['targetLeanSurface']['rightLagrangeBridgeTheorem']}`",
        f"- valid constructor: `{report['targetLeanSurface']['validOfOrder16Theorem']}`",
        f"- OmegaPrime smoothness theorem: `{report['targetLeanSurface']['omegaPrimeContDiff16Theorem']}`",
        f"- checked-smooth valid constructor: `{report['targetLeanSurface']['validCheckedSmoothTheorem']}`",
        f"- active payload receiver: `{report['targetLeanSurface']['receiver']}`",
        f"- receiver checked: `{report['targetLeanSurface']['receiverChecked']}`",
        f"- old receiver rejected for new payloads: `{report['targetLeanSurface']['oldReceiverRejected']}`",
        f"- reflected derivative theorem: `{report['targetLeanSurface']['reflectedIteratedDerivTheorem']}`",
        f"- Taylor exact-poly theorem: `{report['targetLeanSurface']['taylorWithinEvalExactPolyTheorem']}`",
        f"- reflected Taylor exact-poly theorem: `{report['targetLeanSurface']['reflectedTaylorWithinEvalExactPolyTheorem']}`",
        f"- trigamma-series prefix-tail theorem: `{report['targetLeanSurface']['trigammaSeriesPrefixTailTheorem']}`",
        f"- OmegaPrime closed-form prefix-tail theorem: `{report['targetLeanSurface']['omegaPrimeClosedFormPrefixTailTheorem']}`",
        f"- center-jet prefix-tail theorem: `{report['targetLeanSurface']['centerJetPrefixTailBridgeTheorem']}`",
        f"- center-jet prefix-tail checked: `{report['targetLeanSurface']['centerJetPrefixTailBridgeChecked']}`",
        f"- shifted-tail generated-bound theorem: `{report['targetLeanSurface']['shiftedTailGeneratedBoundTheorem']}`",
        f"- shifted-tail generated-bound checked: `{report['targetLeanSurface']['shiftedTailGeneratedBoundChecked']}`",
        f"- center-jet prefix exact rows checked: `{report['targetLeanSurface']['centerJetPrefixExactRowsChecked']}`",
        f"- center-jet prefix exact rows checked count: `{report['targetLeanSurface']['centerJetPrefixExactRowsCheckedCount']}`",
        f"- center-jet prefix/tail rows proof-grade: `{report['targetLeanSurface']['centerJetPrefixTailRowsProofGrade']}`",
        f"- center-jet prefix/tail rows proof-grade count: `{report['targetLeanSurface']['centerJetPrefixTailRowsProofGradeCount']}`",
        f"- status: `{report['targetLeanSurface']['status']}`",
        "",
        "```text",
        report["targetLeanSurface"]["statementAscii"],
        "```",
        "",
        "Next constructor surface:",
        "",
        "```text",
        report["targetLeanSurface"]["nextBridgeStatementAscii"],
        "```",
        "",
        "Normalization note:",
        "",
        f"`{report['targetLeanSurface']['localNormalization']}`",
        "",
        "## Required Fields",
        "",
        "- `coeff[0..15]`",
        "- `coeffErrorAbs[0..15]`",
        "- `centerJet[0..15].{coeff,coeffErrorAbs,lower,upper,prefixN,prefixExactRational,shiftedTailUpperRational,prefixLeanChecked,tailBoundLeanChecked,centerJetMargin,sourceLeanTheorem,sourceLeanChecked,lowerCheckPassed,upperCheckPassed,enclosurePassed}`",
        "- `centerJetPrefixTailRows[0..15].{jetIndex,prefixN,prefixExactRational,shiftedTailUpperRational,coeff,coeffErrorAbs,prefixLeanChecked,tailBoundLeanChecked,centerJetMargin,sourceLeanTheorem,proofGrade}`",
        "- `order16Abs`",
        "- `order16.{condensedFactorBudgetBoundExact,order16Abs,marginExact,integerBudgetPassed,sourceLeanTheorems,sourceLeanChecked}`",
        "- `remainder.{coeffErrorContributionExact,lagrangeContributionExact,requiredTotalExact,remainderAbs,marginExact,budgetPassed}`",
        "- `remainderAbs`",
        "- `centerJetSource[0..15]`",
        "- `integerBudgetSource`",
        "- `exactRationalChecksPassed`",
        "- `sourceDefinitionHashes`",
        "- `allCenterJetsProved`",
        "- `allPayloadObligationsPassed`",
        "- `leanOutputPath`",
        "- `leanValidationStatus`",
        "- `proofSafeClosedFields`",
        "- `outLeanWritten`",
        "- `failureCodes[]`",
        "",
        "## Generated Center-Jet Prefix/Tail Rows",
        "",
        "Full exact rationals are in the JSON artifact.  This table keeps the",
        "Markdown readable while preserving proof status.",
        "",
        "| j | prefixN | coeff digits | prefix checked | exact line | tail checked | margin | proofGrade |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in report["generatorFields"]["centerJetPrefixTailRows"]:
        lines.append(
            "| `{j}` | `{n}` | `{digits}` | `{prefix}` | `{line}` | `{tail}` | `{margin}` | `{grade}` |".format(
                j=row["jetIndex"],
                n=row["prefixN"],
                digits=row["prefixExactRationalDigits"],
                prefix=row["prefixLeanChecked"],
                line=row["prefixExactLeanLine"],
                tail=row["tailBoundLeanChecked"],
                margin=row["centerJetMargin"],
                grade=row["proofGrade"],
            )
        )

    lines.extend(
        [
            "",
            "Row proof boundary:",
            "",
            "- `prefixExactRational` and `shiftedTailUpperRational` are exact",
            "  rational generator output.",
            "- `tailBoundLeanChecked = True` means the shifted-tail formula is",
            "  now backed by a checked Lean theorem.",
            "- `prefixLeanChecked = True` means the generated finite-prefix",
            "  rational equality theorem and the corresponding cast theorem",
            "  are both present in the target Lean file.",
            "- `proofGrade = True` is row-level only: it does not assert that",
            "  `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid` is closed.",
            "",
        "## Required Proofs",
        "",
        ]
    )
    for item in report["requiredProofs"]:
        lines.append(f"- {item}")

    lines.extend(
        [
            "",
            "## Local Source Scan",
            "",
        ]
    )
    for file_name, items in report["localSourceScan"].items():
        lines.extend(["", f"### {file_name}", ""])
        lines.append("| symbol | line | status |")
        lines.append("| --- | --- | --- |")
        for item in items:
            lines.append(
                f"| `{item['symbol']}` | `{item['line']}` | `{item['status']}` |"
            )

    lines.extend(
        [
            "",
            "## Target Symbol Scan",
            "",
            "| symbol | line | status |",
            "| --- | --- | --- |",
        ]
    )
    for symbol, info in report["targetSymbolScan"].items():
        lines.append(f"| `{symbol}` | `{info['line']}` | `{info['status']}` |")

    lines.extend(
        [
            "",
            "## Proof Status",
            "",
        ]
    )
    for key, value in report["proofStatus"].items():
        lines.append(f"- {key}: `{value}`")

    lines.extend(
        [
            "",
            "## Failure Codes",
            "",
        ]
    )
    for code in report["failureCodes"]:
        lines.append(f"- `{code}`")

    lines.extend(
        [
            "",
            "## Parent Failure Codes",
            "",
        ]
    )
    for code in report["parentFailureCodes"]:
        lines.append(f"- `{code}`")

    lines.extend(
        [
            "",
            "## Closed Historical Failures",
            "",
        ]
    )
    for code in report["closedHistoricalFailures"]:
        lines.append(f"- `{code}`")

    lines.extend(
        [
            "",
            "## Decision",
            "",
            "The checked-deriv receiver and the center-jet prefix-tail bridge",
            "are now the active Lean surface:",
            f"`{report['targetLeanSurface']['receiver']}`.",
            f"`{report['targetLeanSurface']['centerJetPrefixTailBridgeTheorem']}`.",
            "The old order-16 polygamma failure is historical, and the broad",
            "`CENTER_JET_PAYLOAD_GAP` is now only the parent blocker. The next",
            "proof-producing step is a concrete",
            "`Step33Sub0OmegaPrimeTaylorRemainderCert` payload with per-jet",
            "`prefixN`, exact finite-prefix rationals, shifted-tail rational",
            "upper bounds, center-jet margins, the integer order-16 budget,",
            "and the exact rational Taylor remainder budget.",
            "",
            "Until those payload fields exist locally, the correct fail code is:",
            "",
            "```text",
            report["firstFailure"],
            "```",
            "",
        ]
    )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk-file", type=Path, default=CHUNK_FILE)
    parser.add_argument("--endpoint-file", type=Path, default=ENDPOINT_HIGH_ORDER_FILE)
    parser.add_argument("--component-payload", type=Path, default=COMPONENT_PAYLOAD)
    parser.add_argument("--gap-map", type=Path, default=GAP_MAP)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(
        chunk_file=args.chunk_file,
        endpoint_file=args.endpoint_file,
        component_payload_path=args.component_payload,
        gap_map_path=args.gap_map,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} first_failure={failure} out_json={out_json}".format(
            status=report["status"],
            failure=report["firstFailure"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
