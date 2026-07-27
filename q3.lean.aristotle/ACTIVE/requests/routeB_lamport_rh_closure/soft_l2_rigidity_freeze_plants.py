#!/usr/bin/env python3
"""Executable PL1--PL4 and Proshka P5 for SOFT_L2_RigidityFreeze."""

from __future__ import annotations

import cmath
import json
import math
from typing import Any, Sequence


TOL = 1e-10


def full_autocorrelation(q: Sequence[complex]) -> list[complex]:
    """Lags -(n-1),...,(n-1), with conjugation in the second slot."""
    n = len(q)
    out: list[complex] = []
    for lag in range(-(n - 1), n):
        total = 0j
        for i in range(n):
            j = i - lag
            if 0 <= j < n:
                total += q[i] * q[j].conjugate()
        out.append(total)
    return out


def convolution(q: Sequence[complex], p: Sequence[complex]) -> list[complex]:
    out = [0j] * (len(q) + len(p) - 1)
    for i, x in enumerate(q):
        for j, y in enumerate(p):
            out[i + j] += x * y
    return out


def max_abs_diff(xs: Sequence[complex], ys: Sequence[complex]) -> float:
    return max(abs(x - y) for x, y in zip(xs, ys, strict=True))


def is_even_packet(q: Sequence[complex]) -> bool:
    return max_abs_diff(q, list(reversed(q))) <= TOL


def is_real_packet(q: Sequence[complex]) -> bool:
    return max(abs(x.imag) for x in q) <= TOL


def polynomial_square_root(a: Sequence[complex]) -> list[complex]:
    """Triangular square root with the positive-real leading branch."""
    if not a or abs(a[0]) <= TOL:
        raise ValueError("ZERO_LEADING_COEFFICIENT")
    if abs(a[0].imag) > TOL or a[0].real <= 0:
        raise ValueError("NO_POSITIVE_REAL_LEADING_BRANCH")
    b = [0j] * ((len(a) + 1) // 2)
    b[0] = complex(math.sqrt(a[0].real), 0.0)
    for n in range(1, len(b)):
        middle = sum(b[j] * b[n - j] for j in range(1, n))
        b[n] = (a[n] - middle) / (2 * b[0])
    if max_abs_diff(convolution(b, b), a) > 1e-9:
        raise ValueError("NOT_A_POLYNOMIAL_SQUARE")
    return b


def relative_error(xs: Sequence[complex], ys: Sequence[complex]) -> float:
    numerator = math.sqrt(sum(abs(x - y) ** 2 for x, y in zip(xs, ys, strict=True)))
    denominator = math.sqrt(sum(abs(x) ** 2 for x in ys))
    return numerator / denominator


def anchor_i_quarter(q: Sequence[complex]) -> float:
    half = (len(q) - 1) // 2
    value = sum(x.real * math.exp((j - half) / 4) for j, x in enumerate(q))
    return value


def transform_value(q: Sequence[complex], x: float) -> complex:
    half = (len(q) - 1) // 2
    return sum(a * cmath.exp(-1j * x * (j - half)) for j, a in enumerate(q))


def reconstruction_preflight(spec: dict[str, Any]) -> str:
    required_true = (
        "entire",
        "nonzero",
        "even_entire",
        "nonnegative_on_real",
        "integrable_on_real",
        "type_at_most_2R",
        "ord0_multiple_four",
    )
    if not all(spec.get(key) is True for key in required_true):
        return "SQUARE_ROOT_INPUT_CONTRACT_INCOMPLETE"
    if spec.get("even_zero_certificate") is not True:
        return "EVEN_ZERO_CERTIFICATE_MISSING_OR_FALSE"
    if spec.get("known_odd_zero_multiplicity") is True:
        return "ODD_ZERO_MULTIPLICITY_DETECTED"
    return "ACCEPT_FOR_RECONSTRUCTION"


def run_plants() -> dict[str, Any]:
    # PL1: real-even normalized control; A is literally a polynomial square.
    raw = [1.0, 2.0, 3.0, 2.0, 1.0]
    norm = math.sqrt(sum(x * x for x in raw))
    q = [complex(x / norm, 0.0) for x in raw]
    A = full_autocorrelation(q)
    square_match = max_abs_diff(A, convolution(q, q))
    recovered = polynomial_square_root(A)
    if anchor_i_quarter(recovered) < 0:
        recovered = [-x for x in recovered]
    pl1_error = relative_error(recovered, q)
    pl1_code = (
        "PL1_EVEN_REAL_RECONSTRUCTION_PASS"
        if is_even_packet(q) and is_real_packet(q) and square_match < TOL and pl1_error < TOL
        else "PL1_EVEN_REAL_RECONSTRUCTION_FAIL"
    )

    # PL2: exact round-6 twins.  Same full A, two different non-even sources.
    twin_a = [1 + 0j, 5 + 0j, 6 + 0j]
    twin_b = [3 + 0j, 7 + 0j, 2 + 0j]
    A_a = full_autocorrelation(twin_a)
    A_b = full_autocorrelation(twin_b)
    twins_same_A = max_abs_diff(A_a, A_b)
    twins_distinct = max_abs_diff(twin_a, twin_b)
    pl2_code = (
        "PL2_NON_EVEN_TWINS_AMBIGUITY_DETECTED"
        if twins_same_A < TOL and twins_distinct > 1 and
        not is_even_packet(twin_a) and not is_even_packet(twin_b)
        else "PL2_NON_EVEN_TWINS_PLANT_INERT"
    )

    # PL3: an even but genuinely complex packet has FFsharp != F^2.
    complex_even = [1 + 1j, 2 + 0.5j, 1 + 1j]
    sample_x = 0.37
    F = transform_value(complex_even, sample_x)
    FFsharp = F * F.conjugate()
    Fsquare = F * F
    pl3_gap = abs(FFsharp - Fsquare)
    pl3_code = (
        "PL3_COMPLEX_EVEN_SHARP_SQUARE_MISMATCH_DETECTED"
        if is_even_packet(complex_even) and not is_real_packet(complex_even) and pl3_gap > 1e-3
        else "PL3_COMPLEX_EVEN_PLANT_INERT"
    )

    # PL4: q and -q have the same A; the positive i/4 anchor selects q.
    q_flipped = [-x for x in q]
    A_flipped = full_autocorrelation(q_flipped)
    recovered_flip = polynomial_square_root(A_flipped)
    if anchor_i_quarter(recovered_flip) < 0:
        recovered_flip = [-x for x in recovered_flip]
    pl4_code = (
        "PL4_POSITIVE_ANCHOR_SELECTS_GLOBAL_SIGN"
        if max_abs_diff(A, A_flipped) < TOL and
        anchor_i_quarter(q) > 0 > anchor_i_quarter(q_flipped) and
        relative_error(recovered_flip, q) < TOL
        else "PL4_SIGN_ANCHOR_PLANT_INERT"
    )

    # Proshka plant: H=(z^2+1)(sin z/z)^4 has simple zeros at +/-i.
    # All other displayed Round-12 scalar conditions are registered true, but
    # no valid even-zero certificate exists.  The reconstructor must refuse
    # before attempting a square root.
    p5_input = {
        "formula": "H(z)=(z^2+1)*(sin(z)/z)^4, removable at z=0",
        "R": 2.0,
        "entire": True,
        "nonzero": True,
        "even_entire": True,
        "nonnegative_on_real": True,
        "integrable_on_real": True,
        "type_at_most_2R": True,
        "ord0_multiple_four": True,
        "even_zero_certificate": None,
        "known_odd_zero_multiplicity": True,
        "odd_zero_witnesses": {"+i": 1, "-i": 1},
    }
    p5_missing_code = reconstruction_preflight(p5_input)
    p5_forged = dict(p5_input, even_zero_certificate=True)
    p5_forged_code = reconstruction_preflight(p5_forged)
    p5_code = (
        "P5_PROSHKA_RECONSTRUCTOR_REFUSED"
        if p5_missing_code == "EVEN_ZERO_CERTIFICATE_MISSING_OR_FALSE" and
        p5_forged_code == "ODD_ZERO_MULTIPLICITY_DETECTED"
        else "P5_PROSHKA_REFUSAL_PLANT_INERT"
    )

    expected = {
        "PL1": "PL1_EVEN_REAL_RECONSTRUCTION_PASS",
        "PL2": "PL2_NON_EVEN_TWINS_AMBIGUITY_DETECTED",
        "PL3": "PL3_COMPLEX_EVEN_SHARP_SQUARE_MISMATCH_DETECTED",
        "PL4": "PL4_POSITIVE_ANCHOR_SELECTS_GLOBAL_SIGN",
        "P5": "P5_PROSHKA_RECONSTRUCTOR_REFUSED",
    }
    observed = {
        "PL1": pl1_code,
        "PL2": pl2_code,
        "PL3": pl3_code,
        "PL4": pl4_code,
        "P5": p5_code,
    }

    return {
        "schema": "soft_l2_rigidity_freeze_plants_v1",
        "status": "ALL_PLANTS_LIVE" if observed == expected else "PLANT_INERT",
        "plants": {
            "PL1": {
                "expected": expected["PL1"],
                "observed": pl1_code,
                "relative_error": pl1_error,
                "square_match_max_abs": square_match,
                "anchor_i_quarter": anchor_i_quarter(recovered),
            },
            "PL2": {
                "expected": expected["PL2"],
                "observed": pl2_code,
                "same_A_max_abs": twins_same_A,
                "source_distance_max_abs": twins_distinct,
                "autocorrelation_lags_minus2_to_2": [x.real for x in A_a],
            },
            "PL3": {
                "expected": expected["PL3"],
                "observed": pl3_code,
                "sample_x": sample_x,
                "abs_FFsharp_minus_Fsquare": pl3_gap,
            },
            "PL4": {
                "expected": expected["PL4"],
                "observed": pl4_code,
                "anchor_positive": anchor_i_quarter(q),
                "anchor_flipped": anchor_i_quarter(q_flipped),
                "selected_relative_error": relative_error(recovered_flip, q),
            },
            "P5": {
                "expected": expected["P5"],
                "observed": p5_code,
                "input": p5_input,
                "missing_certificate_code": p5_missing_code,
                "forged_certificate_code": p5_forged_code,
            },
        },
        "output_codes": [
            "SOFT_L2_SOURCE_INJECTIVITY_LOCKED",
            "SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED",
        ],
        "rh_status": "NOT_RH",
        "bus_010_created": False,
    }


def main() -> None:
    result = run_plants()
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["status"] != "ALL_PLANTS_LIVE":
        raise SystemExit("SOFT_L2_RIGIDITY_FREEZE_PLANT_INERT")


if __name__ == "__main__":
    main()
