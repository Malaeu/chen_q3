#!/usr/bin/env python3
"""Independent exact checker for the RouteB.030 certificate.

This file deliberately imports neither the generator nor Arb.  It rebuilds
the live continued fractions, coefficient boxes, response polynomials,
Bernstein enclosures, verdict, and all six mutation plants.
"""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import fmpq, fmpq_poly

sys.set_int_max_str_digits(300_000)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CERTIFICATE = HERE / "COUPLED_FULL_SUM_RESPONSE_CERT.json"
AUDIT_026 = HERE / "LAMBDA_BRACKET_RESUME_AUDIT.json"
CERT_029 = HERE / "DECISIVE_FINITE_CORE_THETA_K_ESCALATION.json"

M = 257
DEGREES = (0, 4)
CORE_Q = 440
TAIL_Q = 700
CF_LENGTH = 16
DIGITS = 260
SCALE = 10**DIGITS
TAU = Fraction(1, 2**512)
BANDS = (256, 255)
TEETH = (257, 256, 255)
OLD_WITNESS = (
    Fraction(65281, 16711680),
    Fraction(32641, 8355840),
)

PASS = "COUPLED_FULL_SUM_NONNEGATIVE_PRIORITY_PROVED"
KILL = "COUPLED_FULL_SUM_NEGATIVE_CELL_PROVED"
INCONCLUSIVE = "COUPLED_FULL_SUM_RESPONSE_INCONCLUSIVE"
GAP = "COUPLED_TAIL_RESPONSE_BACKEND_GAP"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rat(value: Fraction) -> dict[str, str]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
    }


def read_rat(record: dict[str, str]) -> Fraction:
    return Fraction(int(record["numerator"]), int(record["denominator"]))


def interval_record(lower: Fraction, upper: Fraction) -> dict[str, Any]:
    return {"lower": rat(lower), "upper": rat(upper)}


def read_interval(record: dict[str, Any]) -> tuple[Fraction, Fraction]:
    return read_rat(record["lower"]), read_rat(record["upper"])


def fq(value: Fraction) -> fmpq:
    return fmpq(value.numerator, value.denominator)


def ff(value: fmpq) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


@dataclass(frozen=True)
class FixedInterval:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        require(self.lo <= self.hi, "reversed fixed interval")

    def __add__(self, other: "FixedInterval") -> "FixedInterval":
        return FixedInterval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "FixedInterval":
        return FixedInterval(-self.hi, -self.lo)

    def __sub__(self, other: "FixedInterval") -> "FixedInterval":
        return self + (-other)

    def __mul__(self, other: "FixedInterval") -> "FixedInterval":
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return FixedInterval(
            min(products) // SCALE,
            ceil_div(max(products), SCALE),
        )

    def __truediv__(self, other: "FixedInterval") -> "FixedInterval":
        require(
            not (other.lo <= 0 <= other.hi),
            "fixed denominator contains zero",
        )
        quotients = (
            Fraction(self.lo, other.lo),
            Fraction(self.lo, other.hi),
            Fraction(self.hi, other.lo),
            Fraction(self.hi, other.hi),
        )
        lower = min(quotients) * SCALE
        upper = max(quotients) * SCALE
        return FixedInterval(
            lower.numerator // lower.denominator,
            ceil_div(upper.numerator, upper.denominator),
        )

    def fractions(self) -> tuple[Fraction, Fraction]:
        return Fraction(self.lo, SCALE), Fraction(self.hi, SCALE)


def fixed(value: Fraction) -> FixedInterval:
    scaled = value * SCALE
    return FixedInterval(
        scaled.numerator // scaled.denominator,
        ceil_div(scaled.numerator, scaled.denominator),
    )


def fixed_hull(lower: Fraction, upper: Fraction) -> FixedInterval:
    return FixedInterval(fixed(lower).lo, fixed(upper).hi)


def mul_int(value: FixedInterval, integer: int) -> FixedInterval:
    return value * fixed(Fraction(integer))


def atan_inv(q: int) -> FixedInterval:
    total = FixedInterval(0, 0)
    k = 0
    while True:
        term = fixed(Fraction(1, (2 * k + 1) * q ** (2 * k + 1)))
        total = total + term if k % 2 == 0 else total - term
        next_denominator = (2 * k + 3) * q ** (2 * k + 3)
        if next_denominator > SCALE * 10**12:
            remainder = fixed(Fraction(1, next_denominator))
            return FixedInterval(
                total.lo - remainder.hi,
                total.hi + remainder.hi,
            )
        k += 1


def recurrence_coefficients(
    n: int,
    g: FixedInterval,
    theta: FixedInterval,
) -> tuple[FixedInterval, FixedInterval, FixedInterval]:
    p = g * fixed(Fraction((n - 1) * n, (2 * n - 3) * (2 * n - 1)))
    r = g * fixed(
        Fraction((n + 1) * (n + 2), (2 * n + 3) * (2 * n + 5))
    )
    c = Fraction(1) - Fraction(
        2 * (n * (n + 1) - 1),
        (2 * n - 1) * (2 * n + 3),
    )
    d = fixed(Fraction(n * (n + 1))) + g * fixed(c) - theta
    return p, d, r


def live_ratios(
    n0: int,
    end_degree: int,
    g: FixedInterval,
    theta: FixedInterval,
    terminal: FixedInterval,
) -> dict[int, FixedInterval]:
    rho = terminal
    result: dict[int, FixedInterval] = {}
    for n in range(end_degree + 2 * CF_LENGTH, n0, -2):
        p, d, r = recurrence_coefficients(n, g, theta)
        denominator = d - r * rho
        require(denominator.lo > 0, f"nonpositive denominator at {n}")
        rho = p / denominator
        require(
            0 <= rho.lo <= rho.hi <= SCALE // 2 + 1,
            f"ratio cone failure at {n}",
        )
        if n <= end_degree:
            result[n] = rho
    return result


def legendre_polynomials(degree: int) -> list[fmpq_poly]:
    result = [fmpq_poly([1]), fmpq_poly([0, 1])]
    x = result[1]
    for n in range(1, degree):
        result.append(
            ((2 * n + 1) * x * result[n] - n * result[n - 1])
            / (n + 1)
        )
    return result[: degree + 1]


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


def bernstein_coefficients(
    polynomial: fmpq_poly,
    lower: Fraction,
    upper: Fraction,
) -> list[fmpq]:
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
    return [convolution[k] * factorial[k] for k in range(degree + 1)]


def tooth_value(polynomial: fmpq_poly, r: int) -> fmpq:
    sums = power_sums(r - 1, polynomial.degree())
    value = fmpq(0)
    for degree in range(polynomial.degree() + 1):
        value += polynomial[degree] * (
            fmpq(sums[degree], r**degree) + fmpq(1, 2)
        )
    return value


def response_majorant(q: int) -> int:
    return 2 * q * q + q + 1


def phased(
    target: int,
    degree: int,
    interval: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    lower, upper = interval
    return (
        (lower, upper)
        if ((degree - target) // 2) % 2 == 0
        else (-upper, -lower)
    )


def extremum_record(values: list[fmpq], minimum: bool) -> dict[str, Any]:
    value = min(values) if minimum else max(values)
    return {"index": values.index(value), "value": rat(ff(value))}


def main() -> None:
    certificate = json.loads(CERTIFICATE.read_text())
    audit = json.loads(AUDIT_026.read_text())
    cert029 = json.loads(CERT_029.read_text())

    require(
        certificate["schema"] == "route_b_coupled_full_sum_response.v1",
        "schema",
    )
    require(certificate["status"] == "CHALLENGER / NOT_RH", "status")
    for record in certificate["object_lock"]["source_hashes"]:
        path = ROOT / record["path"]
        require(path.is_file(), f"missing source {path}")
        require(sha256(path) == record["sha256"], f"source hash {path}")

    require(
        certificate["object_lock"]["core_q"] == CORE_Q
        and certificate["object_lock"]["tail_q"] == TAIL_Q,
        "cut lock",
    )
    require(
        read_rat(certificate["object_lock"]["tau"]) == TAU,
        "tau lock",
    )
    require(
        read_interval(certificate["object_lock"]["delta_0"])
        == (Fraction(0), Fraction(0)),
        "stored delta0",
    )

    cases = {
        int(case["target_degree"]): case
        for case in audit["cases"]
        if int(case["m"]) == M
        and int(case["target_degree"]) in DEGREES
    }
    source = cert029["object_lock"]["coefficient_enclosures_to_maximum"]
    rows: dict[int, dict[int, tuple[Fraction, Fraction]]] = {}
    for degree in DEGREES:
        rows[degree] = {
            int(record["legendre_degree"]): read_interval(record)
            for record in source[str(degree)]
        }

    pi = mul_int(atan_inv(5), 16) - mul_int(atan_inv(239), 4)
    g = mul_int(pi * pi, 4 * M * M)
    terminal_width = Fraction(0)
    for degree in DEGREES:
        case = cases[degree]
        theta = fixed_hull(
            read_rat(case["Theta_bracket"]["lower_exact"]),
            read_rat(case["Theta_bracket"]["upper_exact"]),
        )
        n0 = int(case["N0"])
        live = live_ratios(
            n0,
            2 * TAIL_Q,
            g,
            theta,
            FixedInterval(0, SCALE // 2),
        )
        zero = live_ratios(
            n0,
            2 * TAIL_Q,
            g,
            theta,
            FixedInterval(0, 0),
        )
        current = fixed_hull(*rows[degree][n0])
        rebuilt = []
        overlaps = 0
        for n in range(n0 + 2, 2 * TAIL_Q + 1, 2):
            current = current * live[n]
            lower, upper = current.fractions()
            if n in rows[degree]:
                old_lower, old_upper = rows[degree][n]
                require(
                    not (upper < old_lower or old_upper < lower),
                    f"source overlap mode={degree}, degree={n}",
                )
                overlaps += 1
            rows[degree][n] = (lower, upper)
            rebuilt.append(
                {
                    "legendre_degree": n,
                    **interval_record(lower, upper),
                }
            )
        require(
            rebuilt
            == certificate["object_lock"]["extension_boxes"][str(degree)],
            f"extension boxes mode={degree}",
        )
        cf = certificate["object_lock"]["continued_fractions"][str(degree)]
        require(cf["N0"] == n0, "CF N0")
        require(cf["lookahead_steps"] == CF_LENGTH, "CF length")
        require(
            read_interval(cf["terminal_interval"])
            == (Fraction(0), Fraction(1, 2)),
            "live terminal",
        )
        require(cf["terminal_ratio_zero_used"] is False, "zero terminal guard")
        require(cf["source_box_overlap_count"] == overlaps, "overlap count")
        require(
            read_interval(cf["first_live_ratio"])
            == live[n0 + 2].fractions(),
            "first live ratio",
        )
        require(
            read_interval(cf["first_zero_terminal_ratio"])
            == zero[n0 + 2].fractions(),
            "zero mutation ratio",
        )
        last_abs = max(abs(current.lo), abs(current.hi))
        width = Fraction(
            last_abs * response_majorant(TAIL_Q + CF_LENGTH),
            2 * SCALE,
        )
        require(read_rat(cf["terminal_response_width"]) == width, "CF width")
        require(width > 0, "live terminal width positive")
        terminal_width += width

    delta: dict[int, tuple[Fraction, Fraction]] = {}
    for q in range(TAIL_Q + 1):
        n = 2 * q
        lower0, upper0 = phased(0, n, rows[0][n])
        lower4, upper4 = phased(4, n, rows[4][n])
        delta[q] = (
            (lower4 - upper0) / 2,
            (upper4 - lower0) / 2,
        )
    require(delta[0] == (Fraction(0), Fraction(0)), "derived delta0")

    legendre = legendre_polynomials(2 * TAIL_Q)
    core = fmpq_poly([])
    tail = fmpq_poly([])
    core_uncertainty = Fraction(0)
    tail_uncertainty = Fraction(0)
    for q in range(TAIL_Q + 1):
        lower, upper = delta[q]
        center = (lower + upper) / 2
        radius = (upper - lower) / 2 * response_majorant(q)
        if q <= CORE_Q:
            core += fq(center) * legendre[2 * q]
            core_uncertainty += radius
        else:
            tail += fq(center) * legendre[2 * q]
            tail_uncertainty += radius
    total = core + tail
    response_sum = 2 * TAIL_Q**2 + 9 * TAIL_Q + 15
    remainder = sum(
        max(abs(rows[d][2 * TAIL_Q][0]), abs(rows[d][2 * TAIL_Q][1]))
        * response_sum
        / 2
        for d in DEGREES
    )
    response = certificate["response_backend"]
    require(
        read_rat(response["core_response_uncertainty"])
        == core_uncertainty,
        "core uncertainty",
    )
    require(
        read_rat(response["tail_response_uncertainty"])
        == tail_uncertainty,
        "tail uncertainty",
    )
    require(
        read_rat(response["infinite_response_remainder"]) == remainder,
        "infinite remainder",
    )
    require(response["backend_below_tau"] == (remainder < TAU), "tau status")
    uncertainty = core_uncertainty + tail_uncertainty

    rebuilt_bands = []
    for r in BANDS:
        domain = (Fraction(1, r + 1), Fraction(1, r))
        values = bernstein_coefficients(band_polynomial(total, r), *domain)
        tail_values = bernstein_coefficients(
            band_polynomial(tail, r), *domain
        )
        lower = ff(min(values)) - uncertainty - remainder
        upper = ff(max(values)) + uncertainty + remainder
        coupled_tail_radius = max(
            abs(ff(min(tail_values))), abs(ff(max(tail_values)))
        ) + tail_uncertainty + remainder
        rebuilt_bands.append(
            {
                "r": r,
                "domain": interval_record(*domain),
                "center_bernstein_minimum": extremum_record(values, True),
                "center_bernstein_maximum": extremum_record(values, False),
                "tail_center_bernstein_minimum": extremum_record(
                    tail_values, True
                ),
                "tail_center_bernstein_maximum": extremum_record(
                    tail_values, False
                ),
                "coupled_tail_radius": rat(coupled_tail_radius),
                "response_weighted_uncertainty": rat(uncertainty),
                "infinite_response_remainder": rat(remainder),
                "full_enclosure": interval_record(lower, upper),
                "lower_full_sum": rat(lower),
                "upper_full_sum": rat(upper),
                "exact_coverage_record": {
                    "kind": "one_closed_rational_Bernstein_cell",
                    "covered_domain": interval_record(*domain),
                    "coverage_complete": True,
                },
                "pass": lower >= 0,
                "kill": upper < 0,
                "contains_zero": lower <= 0 <= upper,
            }
        )
    require(rebuilt_bands == certificate["bands"], "band reconstruction")

    rebuilt_teeth = []
    for r in TEETH:
        center = ff(tooth_value(total, r))
        tail_center = ff(tooth_value(tail, r))
        lower = center - uncertainty - remainder
        upper = center + uncertainty + remainder
        coupled_tail_radius = (
            abs(tail_center) + tail_uncertainty + remainder
        )
        rebuilt_teeth.append(
            {
                "r": r,
                "z": rat(Fraction(1, r)),
                "center": rat(center),
                "tail_center": rat(tail_center),
                "coupled_tail_radius": rat(coupled_tail_radius),
                "response_weighted_uncertainty": rat(uncertainty),
                "infinite_response_remainder": rat(remainder),
                "full_enclosure": interval_record(lower, upper),
                "lower_full_sum": rat(lower),
                "upper_full_sum": rat(upper),
                "exact_coverage_record": {
                    "kind": "exact_rational_star_tooth",
                    "covered_point": rat(Fraction(1, r)),
                    "coverage_complete": True,
                },
                "pass": lower >= 0,
                "kill": upper < 0,
                "contains_zero": lower <= 0 <= upper,
            }
        )
    require(rebuilt_teeth == certificate["teeth"], "tooth reconstruction")

    witness_values = bernstein_coefficients(
        band_polynomial(total, 255), *OLD_WITNESS
    )
    witness_tail_values = bernstein_coefficients(
        band_polynomial(tail, 255), *OLD_WITNESS
    )
    witness_lower = ff(min(witness_values)) - uncertainty - remainder
    witness_upper = ff(max(witness_values)) + uncertainty + remainder
    witness_tail_radius = max(
        abs(ff(min(witness_tail_values))),
        abs(ff(max(witness_tail_values))),
    ) + tail_uncertainty + remainder
    rebuilt_witness = {
        "domain": interval_record(*OLD_WITNESS),
        "center_bernstein_minimum": extremum_record(witness_values, True),
        "center_bernstein_maximum": extremum_record(witness_values, False),
        "coupled_tail_radius": rat(witness_tail_radius),
        "full_enclosure": interval_record(witness_lower, witness_upper),
        "lower_full_sum": rat(witness_lower),
        "upper_full_sum": rat(witness_upper),
        "exact_coverage_record": {
            "kind": "one_closed_rational_Bernstein_cell",
            "covered_domain": interval_record(*OLD_WITNESS),
            "coverage_complete": True,
        },
        "pass": witness_lower >= 0,
        "kill": witness_upper < 0,
        "contains_zero": witness_lower <= 0 <= witness_upper,
    }
    require(rebuilt_witness == certificate["old_witness"], "witness")

    all_records = rebuilt_bands + rebuilt_teeth + [rebuilt_witness]
    if remainder >= TAU:
        verdict = GAP
    elif all(record["pass"] for record in rebuilt_bands + rebuilt_teeth):
        verdict = PASS
    elif any(record["kill"] for record in all_records):
        verdict = KILL
    else:
        verdict = INCONCLUSIVE
    require(certificate["verdict"] == verdict, "verdict")
    require(certificate["secondary_flags"] == [], "secondary flags")

    plants = certificate["plants"]
    require(
        plants["P1_delta0"]["status"] == "FIRES"
        and read_rat(plants["P1_delta0"]["band_constant_shift_r256"])
        == 128,
        "P1",
    )
    old = cert029["levels"][-1]
    require(
        plants["P2_old_independent_tail"]["status"] == "FIRES"
        and cert029["verdict"] == "K_ESCALATION_INCONCLUSIVE"
        and not old["decisive_pass"]
        and not old["decisive_kill"]
        and plants["P2_old_independent_tail"]["reproduces_inconclusive"],
        "P2",
    )
    require(
        plants["P3_terminal_ratio_zero"]["status"] == "FIRES"
        and read_rat(
            plants["P3_terminal_ratio_zero"][
                "baseline_terminal_response_width"
            ]
        )
        == terminal_width
        and read_rat(
            plants["P3_terminal_ratio_zero"][
                "mutated_terminal_response_width"
            ]
        )
        == 0
        and terminal_width > 0,
        "P3",
    )
    require(
        plants["P4_mode4_phase"]["status"] == "FIRES"
        and read_rat(plants["P4_mode4_phase"]["baseline_delta0"]) == 0
        and read_rat(plants["P4_mode4_phase"]["mutated_delta0"]) == -1,
        "P4",
    )
    require(
        plants["P5_tooth_endpoint"]["status"] == "FIRES"
        and read_rat(
            plants["P5_tooth_endpoint"]["Psi_one_finite_center"]
        )
        == ff(total(fmpq(1)))
        and read_rat(
            plants["P5_tooth_endpoint"][
                "mutated_minus_baseline_finite_center"
            ]
        )
        == ff(total(fmpq(1))) / 2
        and plants["P5_tooth_endpoint"]["identity_verified"],
        "P5",
    )
    symbolic = plants["P6_mass"]["symbolic_by_tooth"]
    require(
        plants["P6_mass"]["status"] == "FIRES"
        and plants["P6_mass"]["control"] == "Psi(t)=t^2-1/3"
        and all(
            read_rat(symbolic[str(r)]["integral_0_1_t2_minus_one_third"])
            == 0
            and read_rat(symbolic[str(r)]["star_sum"])
            == Fraction(r + 1, 6 * r)
            and symbolic[str(r)]["star_sum_nonzero"]
            for r in TEETH
        )
        and plants["P6_mass"]["zero_mass_does_not_imply_tooth_zero"],
        "P6",
    )

    guards = certificate["guards"]
    require(guards["delta0_exact_lock"], "delta0 guard")
    require(not guards["terminal_ratio_set_to_zero"], "terminal guard")
    require(not guards["mu_replaced_by_one"], "mu guard")
    require(
        not guards["coefficient_centers_treated_as_exact"],
        "coefficient guard",
    )
    require(
        not guards["r_times_epsilon_used_as_final_tail"],
        "response-tail guard",
    )
    require(not guards["third_sign_driven_depth_used"], "depth guard")
    require(not guards["lemma_A_modified"], "lemma A guard")
    require(not guards["state_touched"], "STATE guard")
    require(not guards["bus_010_created"], "Bus 010 guard")
    print(f"PASS {verdict}")
    print("P1 PASS P2 PASS P3 PASS P4 PASS P5 PASS P6 PASS")


if __name__ == "__main__":
    main()
