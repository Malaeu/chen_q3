#!/usr/bin/env python3
"""Independent exact-rational checker for FINITE_CORE_THETA_CERT.json.

This checker imports neither the generator nor Arb.  It reconstructs the
center polynomial from the stored rational Legendre coefficient intervals,
recomputes every budget and Bernstein coefficient, verifies the registered
priority order and canonical inventory, and accepts incomplete coverage only
after an exact fatal witness.
"""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import fmpq, fmpq_poly


sys.set_int_max_str_digits(100_000)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CERTIFICATE = HERE / "FINITE_CORE_THETA_CERT.json"
EXPECTED_VERDICT = "DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_rat(record: dict[str, str]) -> Fraction:
    denominator = int(record["denominator"])
    require(denominator > 0, "nonpositive rational denominator")
    return Fraction(int(record["numerator"]), denominator)


def fq(value: Fraction) -> fmpq:
    return fmpq(value.numerator, value.denominator)


def fraction_of(value: fmpq) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def read_interval(
    record: dict[str, dict[str, str]]
) -> tuple[Fraction, Fraction]:
    lower = read_rat(record["lower"])
    upper = read_rat(record["upper"])
    require(lower <= upper, "reversed rational interval")
    return lower, upper


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


def reconstruct_mode(
    target_degree: int,
    records: list[dict[str, Any]],
    legendre: list[fmpq_poly],
) -> tuple[fmpq_poly, Fraction]:
    polynomial = fmpq_poly([])
    error = Fraction(0)
    previous_degree = -2
    for record in records:
        degree = int(record["legendre_degree"])
        require(degree == previous_degree + 2, "noncontiguous even degree")
        previous_degree = degree
        lower, upper = read_interval(record)
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
    require(lower < upper, "empty Bernstein interval")
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


def verify_extreme(
    record: dict[str, Any], values: list[fmpq], maximum: bool
) -> None:
    extreme = max(values) if maximum else min(values)
    index = values.index(extreme)
    require(index == int(record["index"]), "extreme index mismatch")
    require(
        fraction_of(extreme) == read_rat(record["value"]),
        "extreme rational mismatch",
    )
    if maximum:
        require(extreme < 0, "upper Bernstein coefficient is not negative")
        require(
            record["strictly_negative"] is True,
            "negative verdict field mismatch",
        )
    else:
        require(
            (extreme > 0) == bool(record["strictly_positive"]),
            "lower Bernstein sign field mismatch",
        )


def floor_sqrt(m: int) -> int:
    value = int(m**0.5)
    while (value + 1) ** 2 <= m:
        value += 1
    while value**2 > m:
        value -= 1
    return value


def main() -> None:
    certificate = json.loads(CERTIFICATE.read_text())
    require(certificate["verdict"] == EXPECTED_VERDICT, "wrong verdict")
    require(
        certificate["scope"]["kind"] == "FINITE_CELL",
        "scope is not finite-cell",
    )
    require(
        certificate["scope"]["not_cofinal_family"] is True,
        "cofinal guard missing",
    )

    for source in certificate["object_lock"]["source_hashes"]:
        path = ROOT / source["path"]
        require(path.is_file(), f"missing source {path}")
        require(sha256(path) == source["sha256"], f"hash drift {path}")

    object_lock = certificate["object_lock"]
    require(int(object_lock["m"]) == 257, "wrong object m")
    require(object_lock["degree_pair"] == [0, 4], "wrong degree pair")
    coefficient_records = object_lock["coefficient_enclosures"]
    maximum_degree = max(
        int(records[-1]["legendre_degree"])
        for records in coefficient_records.values()
    )
    legendre = legendre_polynomials(maximum_degree)
    modes: dict[int, fmpq_poly] = {}
    errors: dict[int, Fraction] = {}
    for degree in (0, 4):
        modes[degree], errors[degree] = reconstruct_mode(
            degree, coefficient_records[str(degree)], legendre
        )
    psi = (modes[4] - modes[0]) / 2
    core_error = (errors[0] + errors[4]) / 2
    require(
        core_error == read_rat(object_lock["psi_coefficient_error"]),
        "core error mismatch",
    )
    stored_psi = [
        read_rat(record)
        for record in object_lock["psi_center_power_coefficients"]
    ]
    actual_psi = [
        fraction_of(psi[k]) for k in range(psi.degree() + 1)
    ]
    require(actual_psi == stored_psi, "psi center polynomial mismatch")
    require(psi.degree() == int(object_lock["psi_degree"]), "degree mismatch")

    tail_upper = Fraction(0)
    for degree in (0, 4):
        j_lower, _ = read_interval(
            object_lock["positive_source_integrals"][str(degree)]
        )
        _, epsilon_upper = read_interval(
            object_lock["tail_epsilons"][str(degree)]
        )
        require(j_lower > 0, "source integral lower bound is not positive")
        require(epsilon_upper >= 0, "negative epsilon upper bound")
        tail_upper += epsilon_upper / j_lower
    require(
        tail_upper == read_rat(object_lock["epsilon_psi_upper"]),
        "tail ratio budget mismatch",
    )

    expected_order = [{"m": 257, "r": 256}, {"m": 257, "r": 255}]
    require(
        certificate["registered_validation_order"] == expected_order,
        "registered validation order mismatch",
    )
    require(len(certificate["bands"]) == 2, "priority band count mismatch")
    for expected, band in zip(expected_order, certificate["bands"]):
        require(
            {"m": int(band["m"]), "r": int(band["r"])} == expected,
            "priority band order mismatch",
        )
        r = int(band["r"])
        lower, upper = read_interval(band["exact_domain"])
        require(
            (lower, upper) == (Fraction(1, r + 1), Fraction(1, r)),
            "noncanonical band domain",
        )
        require(
            read_rat(band["coefficient_error"]) == core_error,
            "band core error mismatch",
        )
        require(
            read_rat(band["tail_budget"]) == r * tail_upper,
            "band tail budget mismatch",
        )
        center = band_polynomial(psi, r)
        lower_target = add_constant(
            center, -core_error - r * tail_upper
        )
        upper_target = add_constant(
            center, core_error - r * tail_upper
        )
        lower_values = bernstein_coefficients(
            lower_target, lower, upper
        )
        upper_values = bernstein_coefficients(
            upper_target, lower, upper
        )
        verify_extreme(
            band["lower_bernstein_minimum"], lower_values, maximum=False
        )
        verify_extreme(
            band["upper_bernstein_maximum"], upper_values, maximum=True
        )
        require(
            band["verdict"] == "TARGET_UPPER_STRICTLY_NEGATIVE",
            "band verdict mismatch",
        )

    witness = certificate["fatal_witness"]
    require(
        (int(witness["m"]), int(witness["r"])) == (257, 255),
        "fatal witness cell mismatch",
    )
    witness_lower, witness_upper = read_interval(
        witness["strict_interior_interval"]
    )
    band_lower = Fraction(1, 256)
    band_upper = Fraction(1, 255)
    require(
        band_lower < witness_lower < witness_upper < band_upper,
        "fatal interval is not strict interior",
    )
    finite_core_upper = add_constant(
        band_polynomial(psi, 255), core_error
    )
    finite_core_values = bernstein_coefficients(
        finite_core_upper, witness_lower, witness_upper
    )
    verify_extreme(
        witness["upper_bernstein_maximum"],
        finite_core_values,
        maximum=True,
    )
    reported_upper = read_rat(
        witness["reported_exact_negative_upper_bound"]
    )
    require(reported_upper < 0, "reported witness upper bound is not negative")
    require(
        fraction_of(max(finite_core_values)) <= reported_upper,
        "reported witness upper bound is not implied by exact coefficients",
    )
    require(
        witness["kind"] == "FINITE_CORE_UPPER_STRICTLY_NEGATIVE",
        "fatal witness kind mismatch",
    )

    inventory = certificate["coverage"]["canonical_inventory"]
    require([row["m"] for row in inventory] == [13, 53, 257], "inventory m")
    for row in inventory:
        m = int(row["m"])
        root = floor_sqrt(m)
        require(int(row["floor_sqrt_m"]) == root, "sqrt floor mismatch")
        require(int(row["band_r_first"]) == root, "first band mismatch")
        require(int(row["band_r_last"]) == m - 1, "last band mismatch")
        require(int(row["band_count"]) == m - root, "band count mismatch")
        require(int(row["tooth_r_first"]) == root + 1, "first tooth mismatch")
        require(int(row["tooth_r_last"]) == m, "last tooth mismatch")
        require(int(row["tooth_count"]) == m - root, "tooth count mismatch")
    require(certificate["coverage"]["complete"] is False, "false completeness")
    require(certificate["teeth"] == [], "teeth should not run after fatal")

    guards = certificate["guards"]
    require(guards["sample_or_grid_sign_used"] is False, "grid guard")
    require(
        guards["coefficient_centers_treated_as_exact"] is False,
        "coefficient uncertainty dropped",
    )
    require(guards["coefficient_error_consumed"] is True, "core not consumed")
    require(guards["infinite_tail_consumed"] is True, "tail not consumed")
    require(guards["mu_substituted_by_one"] is False, "mu guard")
    require(guards["state_changed"] is False, "state guard")
    require(guards["bus_010_created"] is False, "bus guard")

    print("FINITE_CORE_THETA_CERT_CHECK_OK")
    print(EXPECTED_VERDICT)


if __name__ == "__main__":
    main()
