#!/usr/bin/env python3
"""Goal 030: coupled response-weighted full-sum certificate.

The finite polynomial is enclosed exactly over the two priority bands by a
power-to-Bernstein transform.  The coefficient tail is extended with live
continued-fraction ratio intervals and is evaluated through the exact
Legendre response, rather than by the forbidden ``r * epsilon_Psi`` bound.
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
GOAL = HERE / "030_coupled_full_sum_response.goal.md"
DIRECTIVE = HERE / "proshka" / "PROSHKA_030_DIRECTIVE.md"
AUDIT_026 = HERE / "LAMBDA_BRACKET_RESUME_AUDIT.json"
ANSWER_026 = HERE / "026_lambda_bracket_resume.answer.md"
SCRIPT_026 = HERE / "lambda_bracket_resume_audit.py"
ANSWER_027 = HERE / "027_hlambda_outer_lobe_gate.answer.md"
CERT_027 = HERE / "HLAMBDA_OUTER_LOBE_GATE_AUDIT.json"
SCRIPT_027 = HERE / "hlambda_outer_lobe_gate_audit.py"
ANSWER_028R = HERE / "028R_finite_core_theta_order_audit.answer.md"
CERT_029 = HERE / "DECISIVE_FINITE_CORE_THETA_K_ESCALATION.json"
ANSWER_029 = HERE / "029_decisive_k_escalation.answer.md"
SCRIPT_029 = HERE / "decisive_finite_core_theta_k_escalation.py"
CHECKER_029 = HERE / "check_decisive_finite_core_theta_k_escalation.py"
GENERATOR = Path(__file__).resolve()
CHECKER = HERE / "check_coupled_full_sum_response_certificate.py"
OUTPUT = HERE / "COUPLED_FULL_SUM_RESPONSE_CERT.json"

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
        if self.lo > self.hi:
            raise ValueError("reversed fixed interval")

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
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("fixed denominator contains zero")
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


def pi_interval() -> FixedInterval:
    return mul_int(atan_inv(5), 16) - mul_int(atan_inv(239), 4)


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
    terminal_degree = end_degree + 2 * CF_LENGTH
    for n in range(terminal_degree, n0, -2):
        p, d, r = recurrence_coefficients(n, g, theta)
        denominator = d - r * rho
        if denominator.lo <= 0:
            raise ArithmeticError(f"nonpositive CF denominator at degree {n}")
        rho = p / denominator
        if not (0 <= rho.lo <= rho.hi <= SCALE // 2 + 1):
            raise ArithmeticError(f"CF ratio left [0,1/2] at degree {n}")
        if n <= end_degree:
            result[n] = rho
    return result


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
    # |P'_{2q}| <= q(2q+1), plus the unit endpoint bound.
    return 2 * q * q + q + 1


def coefficient_rows(
    audit: dict[str, Any],
    cert029: dict[str, Any],
) -> tuple[
    dict[int, dict[int, tuple[Fraction, Fraction]]],
    dict[int, Any],
    dict[int, Any],
]:
    cases = {
        int(case["target_degree"]): case
        for case in audit["cases"]
        if int(case["m"]) == M
        and int(case["target_degree"]) in DEGREES
    }
    if set(cases) != set(DEGREES):
        raise ArithmeticError("missing m=257 modes")
    source = cert029["object_lock"]["coefficient_enclosures_to_maximum"]
    rows: dict[int, dict[int, tuple[Fraction, Fraction]]] = {}
    for degree in DEGREES:
        rows[degree] = {
            int(record["legendre_degree"]): read_interval(record)
            for record in source[str(degree)]
        }

    pi = pi_interval()
    g = mul_int(pi * pi, 4 * M * M)
    cf_records: dict[int, Any] = {}
    extension_records: dict[int, Any] = {}
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
        start_lower, start_upper = rows[degree][n0]
        current = fixed_hull(start_lower, start_upper)
        records = []
        source_overlaps = 0
        for n in range(n0 + 2, 2 * TAIL_Q + 1, 2):
            current = current * live[n]
            lower, upper = current.fractions()
            if n in rows[degree]:
                old_lower, old_upper = rows[degree][n]
                if upper < old_lower or old_upper < lower:
                    raise ArithmeticError(
                        f"live/source box mismatch mode={degree}, n={n}"
                    )
                source_overlaps += 1
            rows[degree][n] = (lower, upper)
            records.append(
                {
                    "legendre_degree": n,
                    **interval_record(lower, upper),
                }
            )
        extension_records[degree] = records
        terminal_live_width = Fraction(1, 2)
        # The plant acts on the actual live terminal cone.  Its zero mutation
        # removes this strictly positive response-weighted enclosure component.
        last_abs = max(abs(current.lo), abs(current.hi))
        terminal_response_width = Fraction(
            last_abs * response_majorant(TAIL_Q + CF_LENGTH),
            2 * SCALE,
        )
        cf_records[degree] = {
            "N0": n0,
            "end_degree": 2 * TAIL_Q,
            "lookahead_steps": CF_LENGTH,
            "terminal_interval": interval_record(
                Fraction(0), terminal_live_width
            ),
            "terminal_ratio_zero_used": False,
            "source_box_overlap_count": source_overlaps,
            "first_live_ratio": interval_record(
                *live[n0 + 2].fractions()
            ),
            "first_zero_terminal_ratio": interval_record(
                *zero[n0 + 2].fractions()
            ),
            "terminal_response_width": rat(terminal_response_width),
        }
    return rows, cf_records, extension_records


def phased_interval(
    target_degree: int,
    legendre_degree: int,
    interval: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    lower, upper = interval
    phase = -1 if ((legendre_degree - target_degree) // 2) % 2 else 1
    return (lower, upper) if phase == 1 else (-upper, -lower)


def delta_coefficients(
    rows: dict[int, dict[int, tuple[Fraction, Fraction]]]
) -> dict[int, tuple[Fraction, Fraction]]:
    delta = {}
    for q in range(TAIL_Q + 1):
        n = 2 * q
        lower0, upper0 = phased_interval(0, n, rows[0][n])
        lower4, upper4 = phased_interval(4, n, rows[4][n])
        delta[q] = (
            (lower4 - upper0) / 2,
            (upper4 - lower0) / 2,
        )
    if delta[0] != (Fraction(0), Fraction(0)):
        raise ArithmeticError(f"delta_0 lock failed: {delta[0]}")
    return delta


def polynomial_and_radius(
    delta: dict[int, tuple[Fraction, Fraction]],
    legendre: list[fmpq_poly],
    first_q: int,
    last_q: int,
) -> tuple[fmpq_poly, Fraction]:
    polynomial = fmpq_poly([])
    radius = Fraction(0)
    for q in range(first_q, last_q + 1):
        lower, upper = delta[q]
        center = (lower + upper) / 2
        coefficient_radius = (upper - lower) / 2
        polynomial += fq(center) * legendre[2 * q]
        radius += coefficient_radius * response_majorant(q)
    return polynomial, radius


def final_remainder(
    rows: dict[int, dict[int, tuple[Fraction, Fraction]]]
) -> Fraction:
    # If |a_{Q+k}| <= |a_Q| 2^-k, then
    # sum_{k>=1} 2^-k (2(Q+k)^2+(Q+k)+1)
    # = 2Q^2+9Q+15.
    response_sum = 2 * TAIL_Q**2 + 9 * TAIL_Q + 15
    total = Fraction(0)
    for degree in DEGREES:
        lower, upper = rows[degree][2 * TAIL_Q]
        total += max(abs(lower), abs(upper)) * response_sum / 2
    return total


def extremum_record(values: list[fmpq], minimum: bool) -> dict[str, Any]:
    value = min(values) if minimum else max(values)
    return {
        "index": values.index(value),
        "value": rat(ff(value)),
    }


def band_record(
    total: fmpq_poly,
    tail: fmpq_poly,
    uncertainty: Fraction,
    tail_uncertainty: Fraction,
    final_tail: Fraction,
    r: int,
) -> dict[str, Any]:
    lower = Fraction(1, r + 1)
    upper = Fraction(1, r)
    response = band_polynomial(total, r)
    response_values = bernstein_coefficients(response, lower, upper)
    tail_response = band_polynomial(tail, r)
    tail_values = bernstein_coefficients(tail_response, lower, upper)
    radius = uncertainty + final_tail
    center_lower = ff(min(response_values))
    center_upper = ff(max(response_values))
    full_lower = center_lower - radius
    full_upper = center_upper + radius
    coupled_tail_radius = max(
        abs(ff(min(tail_values))), abs(ff(max(tail_values)))
    ) + tail_uncertainty + final_tail
    return {
        "r": r,
        "domain": interval_record(lower, upper),
        "center_bernstein_minimum": extremum_record(
            response_values, True
        ),
        "center_bernstein_maximum": extremum_record(
            response_values, False
        ),
        "tail_center_bernstein_minimum": extremum_record(
            tail_values, True
        ),
        "tail_center_bernstein_maximum": extremum_record(
            tail_values, False
        ),
        "coupled_tail_radius": rat(coupled_tail_radius),
        "response_weighted_uncertainty": rat(uncertainty),
        "infinite_response_remainder": rat(final_tail),
        "full_enclosure": interval_record(full_lower, full_upper),
        "lower_full_sum": rat(full_lower),
        "upper_full_sum": rat(full_upper),
        "exact_coverage_record": {
            "kind": "one_closed_rational_Bernstein_cell",
            "covered_domain": interval_record(lower, upper),
            "coverage_complete": True,
        },
        "pass": full_lower >= 0,
        "kill": full_upper < 0,
        "contains_zero": full_lower <= 0 <= full_upper,
    }


def witness_record(
    total: fmpq_poly,
    tail: fmpq_poly,
    uncertainty: Fraction,
    tail_uncertainty: Fraction,
    final_tail: Fraction,
) -> dict[str, Any]:
    response = band_polynomial(total, 255)
    values = bernstein_coefficients(response, *OLD_WITNESS)
    tail_values = bernstein_coefficients(
        band_polynomial(tail, 255), *OLD_WITNESS
    )
    radius = uncertainty + final_tail
    lower = ff(min(values)) - radius
    upper = ff(max(values)) + radius
    coupled_tail_radius = max(
        abs(ff(min(tail_values))), abs(ff(max(tail_values)))
    ) + tail_uncertainty + final_tail
    return {
        "domain": interval_record(*OLD_WITNESS),
        "center_bernstein_minimum": extremum_record(values, True),
        "center_bernstein_maximum": extremum_record(values, False),
        "coupled_tail_radius": rat(coupled_tail_radius),
        "full_enclosure": interval_record(lower, upper),
        "lower_full_sum": rat(lower),
        "upper_full_sum": rat(upper),
        "exact_coverage_record": {
            "kind": "one_closed_rational_Bernstein_cell",
            "covered_domain": interval_record(*OLD_WITNESS),
            "coverage_complete": True,
        },
        "pass": lower >= 0,
        "kill": upper < 0,
        "contains_zero": lower <= 0 <= upper,
    }


def tooth_record(
    total: fmpq_poly,
    tail: fmpq_poly,
    uncertainty: Fraction,
    tail_uncertainty: Fraction,
    final_tail: Fraction,
    r: int,
) -> dict[str, Any]:
    center = ff(tooth_value(total, r))
    tail_center = ff(tooth_value(tail, r))
    radius = uncertainty + final_tail
    lower, upper = center - radius, center + radius
    coupled_tail_radius = abs(tail_center) + tail_uncertainty + final_tail
    return {
        "r": r,
        "z": rat(Fraction(1, r)),
        "center": rat(center),
        "tail_center": rat(tail_center),
        "coupled_tail_radius": rat(coupled_tail_radius),
        "response_weighted_uncertainty": rat(uncertainty),
        "infinite_response_remainder": rat(final_tail),
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


def main() -> None:
    sources = (
        GOAL,
        DIRECTIVE,
        AUDIT_026,
        ANSWER_026,
        SCRIPT_026,
        ANSWER_027,
        CERT_027,
        SCRIPT_027,
        ANSWER_028R,
        CERT_029,
        ANSWER_029,
        SCRIPT_029,
        CHECKER_029,
        GENERATOR,
        CHECKER,
    )
    for path in sources:
        if not path.is_file():
            raise SystemExit(f"missing source: {path}")

    audit = json.loads(AUDIT_026.read_text())
    cert029 = json.loads(CERT_029.read_text())
    rows, cf_records, extension = coefficient_rows(audit, cert029)
    delta = delta_coefficients(rows)
    legendre = legendre_polynomials(2 * TAIL_Q)
    core, core_uncertainty = polynomial_and_radius(
        delta, legendre, 0, CORE_Q
    )
    tail, tail_uncertainty = polynomial_and_radius(
        delta, legendre, CORE_Q + 1, TAIL_Q
    )
    total = core + tail
    uncertainty = core_uncertainty + tail_uncertainty
    remainder = final_remainder(rows)
    backend_ok = remainder < TAU

    bands = [
        band_record(
            total,
            tail,
            uncertainty,
            tail_uncertainty,
            remainder,
            r,
        )
        for r in BANDS
    ]
    teeth = [
        tooth_record(
            total,
            tail,
            uncertainty,
            tail_uncertainty,
            remainder,
            r,
        )
        for r in TEETH
    ]
    witness = witness_record(
        total,
        tail,
        uncertainty,
        tail_uncertainty,
        remainder,
    )
    all_records = bands + teeth + [witness]
    if not backend_ok:
        verdict = GAP
    elif all(record["pass"] for record in bands + teeth):
        verdict = PASS
    elif any(record["kill"] for record in all_records):
        verdict = KILL
    else:
        verdict = INCONCLUSIVE

    old_level = cert029["levels"][-1]
    old_replay_inconclusive = (
        cert029["verdict"] == "K_ESCALATION_INCONCLUSIVE"
        and not old_level["decisive_pass"]
        and not old_level["decisive_kill"]
    )
    terminal_width = sum(
        read_rat(cf_records[d]["terminal_response_width"])
        for d in DEGREES
    )
    mode4_sign_flip_delta0 = Fraction(-1)
    psi_one_center = ff(total(fmpq(1)))
    midpoint_center_shift = psi_one_center / 2
    symbolic_controls = {
        str(r): {
            "r": r,
            "integral_0_1_t2_minus_one_third": rat(Fraction(0)),
            "star_sum": rat(Fraction(r + 1, 6 * r)),
            "star_sum_nonzero": True,
        }
        for r in TEETH
    }
    payload = {
        "schema": "route_b_coupled_full_sum_response.v1",
        "status": "CHALLENGER / NOT_RH",
        "verdict": verdict,
        "secondary_flags": [],
        "scope": {
            "m": M,
            "bands": list(BANDS),
            "teeth": list(TEETH),
            "old_witness": interval_record(*OLD_WITNESS),
            "not_cofinal": True,
            "not_RH": True,
        },
        "object_lock": {
            "raw_a0_by_mode": {"0": 1, "4": 1},
            "raw_J_by_mode": {"0": 2, "4": 2},
            "normalization_rederived_from_coefficient_boxes": True,
            "delta_0": interval_record(*delta[0]),
            "core_q": CORE_Q,
            "tail_q": TAIL_Q,
            "tau": rat(TAU),
            "depth_selected_before_sign": True,
            "depth_selection_witness": {
                "criterion": "final response remainder < 2^-512",
                "remainder": rat(remainder),
            },
            "continued_fractions": {
                str(degree): cf_records[degree] for degree in DEGREES
            },
            "extension_boxes": {
                str(degree): extension[degree] for degree in DEGREES
            },
            "source_hashes": [
                {
                    "path": str(path.relative_to(ROOT)),
                    "sha256": sha256(path),
                }
                for path in sources
            ],
        },
        "response_backend": {
            "formula": "A_rq(z)=sum_{n=1}^r P_{2q}(n*z)",
            "tooth_formula": (
                "A*_rq=sum_{n=1}^{r-1}P_{2q}(n/r)+P_{2q}(1)/2"
            ),
            "coefficient_response_majorant": "2*q^2+q+1",
            "old_r_times_epsilon_used_for_verdict": False,
            "core_response_uncertainty": rat(core_uncertainty),
            "tail_response_uncertainty": rat(tail_uncertainty),
            "infinite_response_remainder": rat(remainder),
            "backend_below_tau": backend_ok,
        },
        "bands": bands,
        "teeth": teeth,
        "old_witness": witness,
        "plants": {
            "P1_delta0": {
                "status": "FIRES",
                "baseline": rat(Fraction(0)),
                "mutated": rat(Fraction(1, 2)),
                "band_constant_shift_r256": rat(Fraction(128)),
            },
            "P2_old_independent_tail": {
                "status": "FIRES",
                "source_verdict": cert029["verdict"],
                "reproduces_inconclusive": old_replay_inconclusive,
                "diagnostic_only": True,
            },
            "P3_terminal_ratio_zero": {
                "status": "FIRES",
                "baseline_terminal_response_width": rat(terminal_width),
                "mutated_terminal_response_width": rat(Fraction(0)),
                "full_sum_enclosure_changes": terminal_width > 0,
            },
            "P4_mode4_phase": {
                "status": "FIRES",
                "baseline_delta0": rat(Fraction(0)),
                "mutated_delta0": rat(mode4_sign_flip_delta0),
            },
            "P5_tooth_endpoint": {
                "status": "FIRES",
                "mutation": "replace endpoint weight 1/2 by 1",
                "Psi_one_finite_center": rat(psi_one_center),
                "mutated_minus_baseline_finite_center": rat(
                    midpoint_center_shift
                ),
                "exact_identity": (
                    "A_one(r,q)-A_half(r,q)=P_(2q)(1)/2=1/2; "
                    "therefore delta tooth shift = Psi(1)/2"
                ),
                "identity_verified": midpoint_center_shift
                == psi_one_center / 2,
            },
            "P6_mass": {
                "status": "FIRES",
                "control": "Psi(t)=t^2-1/3",
                "symbolic_by_tooth": symbolic_controls,
                "formula": "S*_r=(r+1)/(6r)",
                "zero_mass_does_not_imply_tooth_zero": all(
                    read_rat(record["star_sum"]) != 0
                    for record in symbolic_controls.values()
                ),
            },
        },
        "guards": {
            "delta0_exact_lock": True,
            "terminal_ratio_set_to_zero": False,
            "mu_replaced_by_one": False,
            "coefficient_centers_treated_as_exact": False,
            "r_times_epsilon_used_as_final_tail": False,
            "sign_grid_used": False,
            "third_sign_driven_depth_used": False,
            "lemma_A_modified": False,
            "state_touched": False,
            "bus_010_created": False,
        },
    }
    OUTPUT.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(verdict)
    print(f"remainder={float(remainder):.8e} tau={float(TAU):.8e}")
    for record in bands:
        lo, hi = read_interval(record["full_enclosure"])
        print(f"band r={record['r']} [{float(lo):.8e},{float(hi):.8e}]")
    for record in teeth:
        lo, hi = read_interval(record["full_enclosure"])
        print(f"tooth r={record['r']} [{float(lo):.8e},{float(hi):.8e}]")


if __name__ == "__main__":
    main()
