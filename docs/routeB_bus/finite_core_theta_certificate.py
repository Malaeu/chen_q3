#!/usr/bin/env python3
"""Exact rational certificate generator for Route-B goal 028.

The Arb enclosures from goal 026 are converted to rational coefficient
intervals.  All subsequent polynomial, budget, and Bernstein operations are
performed in exact ``fmpq`` arithmetic.  The registered priority cells are
judged first; an exact negative upper certificate terminates the transaction
before any lower-priority cell is considered.
"""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import arb, fmpq, fmpq_poly


sys.set_int_max_str_digits(100_000)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
GOAL = HERE / "028_finite_core_theta_order.goal.md"
AUDIT_026 = HERE / "LAMBDA_BRACKET_RESUME_AUDIT.json"
SCRIPT_026 = HERE / "lambda_bracket_resume_audit.py"
ANSWER_027 = HERE / "027_hlambda_outer_lobe_gate.answer.md"
SCRIPT_027 = HERE / "hlambda_outer_lobe_gate_audit.py"
PEN = HERE / "proshka" / "PROSHKA_PEN_REDUCTIONS_2026-07-27.md"
RESYNC_AUDIT = HERE / "proshka" / "PROSHKA_RESYNC_AUDIT_2026-07-27.md"
LEDGER = HERE / "PROOF_COMPILER_SEVEN_GATES_2026-07-27.json"
GENERATOR = Path(__file__).resolve()
CHECKER = HERE / "check_finite_core_theta_certificate.py"
OUTPUT = HERE / "FINITE_CORE_THETA_CERT.json"

M = 257
DEGREES = (0, 4)
COEFFICIENT_DIGITS = 140
PRIORITY_R = (256, 255)
FATAL_CODE = "DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL"

sys.path.insert(0, str(HERE))
import hlambda_outer_lobe_gate_audit as cert027  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def decimal_fraction(integer: int, exponent: int) -> Fraction:
    integer = int(integer)
    exponent = int(exponent)
    if exponent >= 0:
        return Fraction(integer * 10**exponent)
    return Fraction(integer, 10 ** (-exponent))


def rational_hull(value: arb, digits: int) -> tuple[Fraction, Fraction]:
    midpoint, radius, exponent = value.mid_rad_10exp(digits)
    lower = decimal_fraction(midpoint - radius, exponent)
    upper = decimal_fraction(midpoint + radius, exponent)
    if lower > upper:
        raise ArithmeticError("invalid rational hull")
    return lower, upper


def rat(value: Fraction) -> dict[str, str]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
    }


def fq(value: Fraction) -> fmpq:
    return fmpq(value.numerator, value.denominator)


def fraction_of(value: fmpq) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def interval_record(
    lower: Fraction, upper: Fraction
) -> dict[str, dict[str, str]]:
    return {"lower": rat(lower), "upper": rat(upper)}


def legendre_polynomials(degree: int) -> list[fmpq_poly]:
    polynomials = [fmpq_poly([1])]
    if degree == 0:
        return polynomials
    x = fmpq_poly([0, 1])
    polynomials.append(x)
    for n in range(1, degree):
        polynomials.append(
            ((2 * n + 1) * x * polynomials[n] - n * polynomials[n - 1])
            / (n + 1)
        )
    return polynomials


def coefficient_enclosures(
    case: dict[str, Any],
) -> tuple[list[dict[str, Any]], list[tuple[int, Fraction, Fraction]]]:
    records: list[dict[str, Any]] = []
    values: list[tuple[int, Fraction, Fraction]] = []
    for degree, coefficient in cert027.raw_coefficients(case):
        lower, upper = rational_hull(coefficient, COEFFICIENT_DIGITS)
        records.append(
            {
                "legendre_degree": degree,
                **interval_record(lower, upper),
            }
        )
        values.append((degree, lower, upper))
    return records, values


def center_mode(
    target_degree: int,
    enclosures: list[tuple[int, Fraction, Fraction]],
    legendre: list[fmpq_poly],
) -> tuple[fmpq_poly, Fraction]:
    polynomial = fmpq_poly([])
    error = Fraction(0)
    for degree, lower, upper in enclosures:
        center = (lower + upper) / 2
        radius = (upper - lower) / 2
        k = (degree - target_degree) // 2
        phase = -1 if k % 2 else 1
        polynomial += fq(phase * center) * legendre[degree]
        error += radius
    return polynomial, error


def power_sums(r: int, degree: int) -> list[int]:
    sums = [0] * (degree + 1)
    for n in range(1, r + 1):
        power = 1
        for k in range(degree + 1):
            sums[k] += power
            power *= n
    return sums


def band_polynomial(psi: fmpq_poly, r: int) -> fmpq_poly:
    sums = power_sums(r, psi.degree())
    return fmpq_poly([psi[k] * sums[k] for k in range(psi.degree() + 1)])


def add_constant(polynomial: fmpq_poly, value: Fraction) -> fmpq_poly:
    coefficients = polynomial.coeffs()
    if not coefficients:
        coefficients = [fmpq(0)]
    coefficients[0] += fq(value)
    return fmpq_poly(coefficients)


def bernstein_coefficients(
    polynomial: fmpq_poly, lower: Fraction, upper: Fraction
) -> list[fmpq]:
    """Exact power-to-Bernstein transform on a rational interval.

    If q(u)=p(lower+(upper-lower)u)=sum a_j u^j and d=deg p, then
    b_k=sum_{j<=k} a_j binom(k,j)/binom(d,j).  The binomial transform is
    evaluated as one exact polynomial convolution.
    """

    degree = polynomial.degree()
    transformed = polynomial(
        fmpq_poly([fq(lower), fq(upper - lower)])
    )
    power = transformed.coeffs()
    power.extend([fmpq(0)] * (degree + 1 - len(power)))
    factorial = [1]
    for k in range(1, degree + 1):
        factorial.append(factorial[-1] * k)
    left = fmpq_poly(
        [
            power[j] * factorial[degree - j] / factorial[degree]
            for j in range(degree + 1)
        ]
    )
    exponential = fmpq_poly(
        [fmpq(1, factorial[j]) for j in range(degree + 1)]
    )
    convolution = (left * exponential).truncate(degree + 1)
    return [
        convolution[k] * factorial[k]
        for k in range(degree + 1)
    ]


def exact_max_record(values: list[fmpq]) -> dict[str, Any]:
    maximum = max(values)
    return {
        "index": values.index(maximum),
        "value": rat(fraction_of(maximum)),
        "strictly_negative": bool(maximum < 0),
    }


def exact_min_record(values: list[fmpq]) -> dict[str, Any]:
    minimum = min(values)
    return {
        "index": values.index(minimum),
        "value": rat(fraction_of(minimum)),
        "strictly_positive": bool(minimum > 0),
    }


def canonical_inventory(m: int) -> dict[str, Any]:
    floor_sqrt = int(m**0.5)
    while (floor_sqrt + 1) ** 2 <= m:
        floor_sqrt += 1
    while floor_sqrt**2 > m:
        floor_sqrt -= 1
    bands = list(range(floor_sqrt, m))
    teeth = list(range(floor_sqrt + 1, m + 1))
    return {
        "m": m,
        "floor_sqrt_m": floor_sqrt,
        "band_r_first": bands[0],
        "band_r_last": bands[-1],
        "band_count": len(bands),
        "tooth_r_first": teeth[0],
        "tooth_r_last": teeth[-1],
        "tooth_count": len(teeth),
    }


def main() -> None:
    sources = (
        GOAL,
        AUDIT_026,
        SCRIPT_026,
        ANSWER_027,
        SCRIPT_027,
        PEN,
        RESYNC_AUDIT,
        LEDGER,
        GENERATOR,
        CHECKER,
    )
    for path in sources:
        if not path.is_file():
            raise SystemExit(f"missing source: {path}")

    audit = json.loads(AUDIT_026.read_text())
    by_case = {
        (int(case["m"]), int(case["target_degree"])): case
        for case in audit["cases"]
    }
    cases = {degree: by_case[(M, degree)] for degree in DEGREES}
    raw_arb = {
        degree: cert027.raw_coefficients(cases[degree])
        for degree in DEGREES
    }
    enclosure_records: dict[int, list[dict[str, Any]]] = {}
    enclosures: dict[int, list[tuple[int, Fraction, Fraction]]] = {}
    for degree in DEGREES:
        enclosure_records[degree], enclosures[degree] = (
            coefficient_enclosures(cases[degree])
        )

    maximum_degree = max(int(cases[d]["N0"]) for d in DEGREES)
    legendre = legendre_polynomials(maximum_degree)
    mode: dict[int, fmpq_poly] = {}
    mode_error: dict[int, Fraction] = {}
    for degree in DEGREES:
        mode[degree], mode_error[degree] = center_mode(
            degree, enclosures[degree], legendre
        )
    psi = (mode[4] - mode[0]) / 2
    core_error = (mode_error[0] + mode_error[4]) / 2

    normalization = {
        degree: cert027.normalization_data(cases[degree], raw_arb[degree])
        for degree in DEGREES
    }
    j_intervals: dict[int, tuple[Fraction, Fraction]] = {}
    epsilon_intervals: dict[int, tuple[Fraction, Fraction]] = {}
    for degree in DEGREES:
        j_intervals[degree] = rational_hull(
            normalization[degree]["J"], COEFFICIENT_DIGITS
        )
        epsilon_intervals[degree] = rational_hull(
            normalization[degree]["epsilon"], COEFFICIENT_DIGITS
        )
        if j_intervals[degree][0] <= 0:
            raise ArithmeticError("source integral lower bound is not positive")
        if epsilon_intervals[degree][0] < 0:
            raise ArithmeticError("tail epsilon enclosure crosses zero")
    tail_upper = sum(
        (
            epsilon_intervals[degree][1] / j_intervals[degree][0]
            for degree in DEGREES
        ),
        Fraction(0),
    )

    priority_bands: list[dict[str, Any]] = []
    for r in PRIORITY_R:
        lower = Fraction(1, r + 1)
        upper = Fraction(1, r)
        center = band_polynomial(psi, r)
        lower_target = add_constant(
            center, -core_error - r * tail_upper
        )
        upper_target = add_constant(
            center, core_error - r * tail_upper
        )
        lower_bernstein = bernstein_coefficients(
            lower_target, lower, upper
        )
        upper_bernstein = bernstein_coefficients(
            upper_target, lower, upper
        )
        upper_record = exact_max_record(upper_bernstein)
        if not upper_record["strictly_negative"]:
            raise ArithmeticError(
                f"priority band r={r} lacks a strict negative upper witness"
            )
        priority_bands.append(
            {
                "m": M,
                "r": r,
                "exact_domain": interval_record(lower, upper),
                "center_polynomial_ref": "object_lock.psi_center_power_coefficients",
                "coefficient_error": rat(core_error),
                "tail_budget": rat(r * tail_upper),
                "lower_bernstein_minimum": exact_min_record(
                    lower_bernstein
                ),
                "upper_bernstein_maximum": upper_record,
                "subdivision": [interval_record(lower, upper)],
                "verdict": "TARGET_UPPER_STRICTLY_NEGATIVE",
            }
        )

    # A strict interior interval on r=255 where even the finite core itself,
    # before the infinite-tail allowance is applied, has a negative upper
    # Bernstein certificate.
    r = 255
    band_lower = Fraction(1, r + 1)
    band_width = Fraction(1, r) - band_lower
    witness_lower = band_lower + band_width * Fraction(1, 256)
    witness_upper = band_lower + band_width * Fraction(2, 256)
    finite_core_upper = add_constant(
        band_polynomial(psi, r), core_error
    )
    finite_core_bernstein = bernstein_coefficients(
        finite_core_upper, witness_lower, witness_upper
    )
    finite_core_maximum = exact_max_record(finite_core_bernstein)
    if not finite_core_maximum["strictly_negative"]:
        raise ArithmeticError("finite-core negative witness did not certify")
    reported_negative_upper = Fraction(-1, 10**97)
    if fraction_of(max(finite_core_bernstein)) > reported_negative_upper:
        raise ArithmeticError("simple reported negative upper bound failed")

    psi_coefficients = [
        rat(fraction_of(psi[k])) for k in range(psi.degree() + 1)
    ]
    payload = {
        "schema": "route_b_finite_core_theta_certificate.v1",
        "status": "CHALLENGER / NOT_RH",
        "verdict": FATAL_CODE,
        "scope": {
            "kind": "FINITE_CELL",
            "requested_cells": [13, 53, 257],
            "terminated_at_cell": M,
            "not_cofinal_family": True,
        },
        "method": (
            "exact rational Bernstein upper certificates from rational "
            "enclosures of the Arb coefficient balls"
        ),
        "object_lock": {
            "m": M,
            "degree_pair": list(DEGREES),
            "coefficient_decimal_digits": COEFFICIENT_DIGITS,
            "source_hashes": [
                {
                    "path": str(path.relative_to(ROOT)),
                    "sha256": sha256(path),
                }
                for path in sources
            ],
            "theta_intervals": {
                str(degree): cases[degree]["Theta_bracket"]
                for degree in DEGREES
            },
            "coefficient_enclosures": {
                str(degree): enclosure_records[degree]
                for degree in DEGREES
            },
            "psi_center_power_coefficients": psi_coefficients,
            "psi_degree": psi.degree(),
            "psi_coefficient_error": rat(core_error),
            "positive_source_integrals": {
                str(degree): interval_record(*j_intervals[degree])
                for degree in DEGREES
            },
            "tail_epsilons": {
                str(degree): interval_record(
                    *epsilon_intervals[degree]
                )
                for degree in DEGREES
            },
            "epsilon_psi_upper": rat(tail_upper),
        },
        "registered_validation_order": [
            {"m": M, "r": r} for r in PRIORITY_R
        ],
        "bands": priority_bands,
        "teeth": [],
        "fatal_witness": {
            "m": M,
            "r": r,
            "kind": "FINITE_CORE_UPPER_STRICTLY_NEGATIVE",
            "strict_interior_interval": interval_record(
                witness_lower, witness_upper
            ),
            "upper_bernstein_maximum": finite_core_maximum,
            "reported_exact_negative_upper_bound": rat(
                reported_negative_upper
            ),
            "coefficient_error_consumed": rat(core_error),
            "tail_effect": (
                "the finite core is already strictly negative; subtracting "
                "the required positive tail budget makes the target upper "
                "bound still smaller"
            ),
        },
        "coverage": {
            "canonical_inventory": [
                canonical_inventory(m) for m in (13, 53, 257)
            ],
            "priority_bands_checked_in_order": [
                {"m": M, "r": r} for r in PRIORITY_R
            ],
            "complete": False,
            "termination": (
                "exact fatal certificate on registered priority bands; "
                "remaining bands and teeth are not admissible work after kill"
            ),
        },
        "guards": {
            "sample_or_grid_sign_used": False,
            "coefficient_centers_treated_as_exact": False,
            "coefficient_error_consumed": True,
            "infinite_tail_consumed": True,
            "mu_substituted_by_one": False,
            "cofinal_family_claimed": False,
            "state_changed": False,
            "bus_010_created": False,
        },
    }
    OUTPUT.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(FATAL_CODE)
    for band in priority_bands:
        maximum = band["upper_bernstein_maximum"]
        print(
            f"m={M} r={band['r']} adjusted_upper_max_index="
            f"{maximum['index']} strictly_negative="
            f"{maximum['strictly_negative']}"
        )
    print(
        f"finite_core_negative_interval="
        f"{witness_lower.numerator}/{witness_lower.denominator},"
        f"{witness_upper.numerator}/{witness_upper.denominator}"
    )


if __name__ == "__main__":
    main()
