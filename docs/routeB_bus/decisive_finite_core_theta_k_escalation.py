#!/usr/bin/env python3
"""Goal 029: decisive two-cut finite-core theta escalation.

Only the two owner-authorized truncation increases are admissible:
``Delta K = 20`` and, if the first cut is inconclusive, ``Delta K = 40``.
The full modes and certified Theta intervals remain fixed.

The decisive envelopes are

  L = P_center - E_core - tail,
  U = P_center + E_core + tail.

Failure of L is never interpreted as negativity of the full sum.
"""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import arb, ctx, fmpq, fmpq_poly


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
GOAL = HERE / "029_decisive_k_escalation.goal.md"
ADJUDICATION = (
    HERE / "proshka" / "PROSHKA_028_KILL_ADJUDICATION_2026-07-27.md"
)
AUDIT_026 = HERE / "LAMBDA_BRACKET_RESUME_AUDIT.json"
SCRIPT_026 = HERE / "lambda_bracket_resume_audit.py"
ANSWER_025 = HERE / "025_legendre_tail_certificate.answer.md"
PEN = HERE / "proshka" / "PROSHKA_PEN_REDUCTIONS_2026-07-27.md"
BASE_CERT = HERE / "FINITE_CORE_THETA_CERT.json"
BASE_GENERATOR = HERE / "finite_core_theta_certificate.py"
BASE_CHECKER = HERE / "check_finite_core_theta_certificate.py"
GENERATOR = Path(__file__).resolve()
CHECKER = HERE / "check_decisive_finite_core_theta_k_escalation.py"
OUTPUT = HERE / "DECISIVE_FINITE_CORE_THETA_K_ESCALATION.json"

M = 257
DEGREES = (0, 4)
R_VALUES = (256, 255)
AUTHORIZED_EXTRA_K = (20, 40)
COEFFICIENT_DIGITS = 320
OLD_WITNESS = (
    Fraction(65281, 16711680),
    Fraction(32641, 8355840),
)
PASS_CODE = "DUAL_THETA_DOMINANCE_PROVED_PRIORITY_BANDS"
KILL_CODE = "DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL"
INCONCLUSIVE_CODE = "K_ESCALATION_INCONCLUSIVE"

sys.set_int_max_str_digits(200_000)
sys.path.insert(0, str(HERE))
import lambda_bracket_resume_audit as cert026  # noqa: E402
import hlambda_outer_lobe_gate_audit as cert027  # noqa: E402
import finite_core_theta_certificate as base  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def raw_enclosures_to(
    case: dict[str, Any], end_degree: int
) -> tuple[list[dict[str, Any]], list[tuple[int, Fraction, Fraction]]]:
    ctx.dps = cert026.WORKING_DPS[M]
    G = (2 * arb.pi() * M) ** 2
    theta = cert027.theta_ball(case)
    previous = arb(0)
    current = arb(1)
    records = []
    values = []
    for degree in range(0, end_degree + 1, 2):
        lower, upper = base.rational_hull(
            current, COEFFICIENT_DIGITS
        )
        records.append(
            {
                "legendre_degree": degree,
                **base.interval_record(lower, upper),
            }
        )
        values.append((degree, lower, upper))
        following = (
            cert026.d_coeff(degree, G, theta) * current
            - cert026.p_coeff(degree, G) * previous
        ) / cert026.r_coeff(degree, G)
        previous, current = current, following
    return records, values


def prefix(
    rows: list[tuple[int, Fraction, Fraction]], end_degree: int
) -> list[tuple[int, Fraction, Fraction]]:
    result = [row for row in rows if row[0] <= end_degree]
    if not result or result[-1][0] != end_degree:
        raise ArithmeticError("truncation prefix endpoint mismatch")
    return result


def tooth_value(polynomial: fmpq_poly, r: int) -> fmpq:
    sums = base.power_sums(r - 1, polynomial.degree())
    value = fmpq(0)
    for degree in range(polynomial.degree() + 1):
        power_sum = fmpq(sums[degree], r**degree)
        endpoint_weight = fmpq(1, 2)
        value += polynomial[degree] * (power_sum + endpoint_weight)
    return value


def rational_record(value: fmpq) -> dict[str, str]:
    return base.rat(base.fraction_of(value))


def exact_scalar_record(value: fmpq) -> dict[str, Any]:
    return {
        "value": rational_record(value),
        "strictly_negative": value < 0,
        "nonnegative": value >= 0,
    }


def band_record(
    psi: fmpq_poly,
    point_core_error: Fraction,
    epsilon_psi: Fraction,
    r: int,
) -> tuple[dict[str, Any], bool, bool]:
    lower = Fraction(1, r + 1)
    upper = Fraction(1, r)
    center = base.band_polynomial(psi, r)
    band_core_error = r * point_core_error
    band_tail = r * epsilon_psi
    lower_envelope = base.add_constant(
        center, -band_core_error - band_tail
    )
    upper_envelope = base.add_constant(
        center, band_core_error + band_tail
    )
    lower_values = base.bernstein_coefficients(
        lower_envelope, lower, upper
    )
    upper_values = base.bernstein_coefficients(
        upper_envelope, lower, upper
    )
    pass_band = min(lower_values) >= 0
    kill_full_band = max(upper_values) < 0

    witness = None
    kill_witness = False
    if r == 255:
        witness_values = base.bernstein_coefficients(
            upper_envelope, *OLD_WITNESS
        )
        witness_maximum = base.exact_max_record(witness_values)
        kill_witness = bool(witness_maximum["strictly_negative"])
        witness = {
            "exact_domain": base.interval_record(*OLD_WITNESS),
            "U_bernstein_maximum": witness_maximum,
            "true_kill": kill_witness,
        }

    record = {
        "m": M,
        "r": r,
        "exact_domain": base.interval_record(lower, upper),
        "point_core_error": base.rat(point_core_error),
        "band_core_error": base.rat(band_core_error),
        "epsilon_psi_upper": base.rat(epsilon_psi),
        "band_tail_budget": base.rat(band_tail),
        "L_bernstein_minimum": base.exact_min_record(lower_values),
        "U_bernstein_maximum": base.exact_max_record(upper_values),
        "pass_full_band": pass_band,
        "kill_full_band": kill_full_band,
        "old_witness": witness,
    }
    return record, pass_band, kill_full_band or kill_witness


def tooth_record(
    psi: fmpq_poly,
    point_core_error: Fraction,
    epsilon_psi: Fraction,
    r: int,
) -> tuple[dict[str, Any], bool, bool]:
    center = tooth_value(psi, r)
    effective_count = Fraction(2 * r - 1, 2)
    core_error = effective_count * point_core_error
    tail = effective_count * epsilon_psi
    lower = center - base.fq(core_error + tail)
    upper = center + base.fq(core_error + tail)
    pass_tooth = lower >= 0
    kill_tooth = upper < 0
    return (
        {
            "m": M,
            "r": r,
            "z": base.rat(Fraction(1, r)),
            "effective_count": base.rat(effective_count),
            "center": rational_record(center),
            "core_error": base.rat(core_error),
            "tail_budget": base.rat(tail),
            "L": exact_scalar_record(lower),
            "U": exact_scalar_record(upper),
            "pass": pass_tooth,
            "kill": kill_tooth,
        },
        pass_tooth,
        kill_tooth,
    )


def main() -> None:
    sources = (
        GOAL,
        ADJUDICATION,
        AUDIT_026,
        SCRIPT_026,
        ANSWER_025,
        PEN,
        BASE_CERT,
        BASE_GENERATOR,
        BASE_CHECKER,
        GENERATOR,
        CHECKER,
    )
    for path in sources:
        if not path.is_file():
            raise SystemExit(f"missing source: {path}")

    audit = json.loads(AUDIT_026.read_text())
    cases = {
        int(case["target_degree"]): case
        for case in audit["cases"]
        if int(case["m"]) == M
        and int(case["target_degree"]) in DEGREES
    }
    if set(cases) != set(DEGREES):
        raise ArithmeticError("missing m=257 exact-mode case")

    maximum_extra = max(AUTHORIZED_EXTRA_K)
    maximum_end = {
        degree: int(cases[degree]["N0"]) + 2 * maximum_extra
        for degree in DEGREES
    }
    legendre = base.legendre_polynomials(max(maximum_end.values()))
    records_to_max = {}
    enclosures_to_max = {}
    for degree in DEGREES:
        records_to_max[degree], enclosures_to_max[degree] = (
            raw_enclosures_to(cases[degree], maximum_end[degree])
        )

    levels = []
    final_code = INCONCLUSIVE_CODE
    for extra in AUTHORIZED_EXTRA_K:
        mode = {}
        mode_error = {}
        normalization = {}
        epsilon_ratio = {}
        last_degree = {}
        for degree in DEGREES:
            last_degree[degree] = int(cases[degree]["N0"]) + 2 * extra
            rows = prefix(
                enclosures_to_max[degree], last_degree[degree]
            )
            mode[degree], mode_error[degree] = base.center_mode(
                degree, rows, legendre
            )
            normalization[degree] = base.normalization_certificate(
                rows, COEFFICIENT_DIGITS
            )
            ratio = normalization[degree][
                "tail_ratio_upper_after_J_cancellation"
            ]
            epsilon_ratio[degree] = Fraction(
                int(ratio["numerator"]), int(ratio["denominator"])
            )

        psi = (mode[4] - mode[0]) / 2
        point_core_error = (mode_error[0] + mode_error[4]) / 2
        epsilon_psi = sum(epsilon_ratio.values(), Fraction(0))
        bands = []
        teeth = []
        pass_flags = []
        kill_flags = []
        for r in R_VALUES:
            band, pass_band, kill_band = band_record(
                psi, point_core_error, epsilon_psi, r
            )
            tooth, pass_tooth, kill_tooth = tooth_record(
                psi, point_core_error, epsilon_psi, r
            )
            bands.append(band)
            teeth.append(tooth)
            pass_flags.extend((pass_band, pass_tooth))
            kill_flags.extend((kill_band, kill_tooth))

        level_pass = all(pass_flags)
        level_kill = any(kill_flags)
        levels.append(
            {
                "extra_K": extra,
                "last_degree_by_mode": {
                    str(degree): last_degree[degree]
                    for degree in DEGREES
                },
                "normalization_certificates": {
                    str(degree): normalization[degree]
                    for degree in DEGREES
                },
                "epsilon_ratio_upper_by_mode": {
                    str(degree): base.rat(epsilon_ratio[degree])
                    for degree in DEGREES
                },
                "epsilon_psi_upper": base.rat(epsilon_psi),
                "point_core_error": base.rat(point_core_error),
                "bands": bands,
                "teeth": teeth,
                "decisive_pass": level_pass,
                "decisive_kill": level_kill,
            }
        )
        if level_pass:
            final_code = PASS_CODE
            break
        if level_kill:
            final_code = KILL_CODE
            break

    if final_code == INCONCLUSIVE_CODE and len(levels) != 2:
        raise ArithmeticError("inconclusive result before second cut")

    payload = {
        "schema": "route_b_decisive_finite_core_theta_k_escalation.v1",
        "status": "CHALLENGER / NOT_RH",
        "verdict": final_code,
        "scope": {
            "m": M,
            "priority_bands": list(R_VALUES),
            "authorized_extra_K": list(AUTHORIZED_EXTRA_K),
            "same_certified_Theta_intervals": True,
            "same_full_modes": True,
            "not_all_bands_or_teeth": True,
            "not_cofinal_family": True,
        },
        "object_lock": {
            "degree_pair": list(DEGREES),
            "coefficient_decimal_digits": COEFFICIENT_DIGITS,
            "base_K0": {
                str(degree): int(cases[degree]["K0"])
                for degree in DEGREES
            },
            "base_last_degree": {
                str(degree): int(cases[degree]["N0"])
                for degree in DEGREES
            },
            "maximum_last_degree": {
                str(degree): maximum_end[degree]
                for degree in DEGREES
            },
            "theta_intervals": {
                str(degree): cases[degree]["Theta_bracket"]
                for degree in DEGREES
            },
            "live_recessive_boundary": {
                str(degree): {
                    "K0_strict_margin": cases[degree][
                        "K0_strict_margin"
                    ],
                    "terminal_interval": cases[degree][
                        "continued_fraction"
                    ]["terminal_interval"],
                    "live_ratio_interval_before_Krawczyk": cases[degree][
                        "continued_fraction"
                    ]["live_ratio_interval_before_Krawczyk"],
                    "terminal_ratio_zero_used": cases[degree][
                        "continued_fraction"
                    ]["terminal_ratio_zero_used"],
                }
                for degree in DEGREES
            },
            "old_witness": base.interval_record(*OLD_WITNESS),
            "coefficient_enclosures_to_maximum": {
                str(degree): records_to_max[degree]
                for degree in DEGREES
            },
            "source_hashes": [
                {
                    "path": str(path.relative_to(ROOT)),
                    "sha256": sha256(path),
                }
                for path in sources
            ],
        },
        "levels": levels,
        "guards": {
            "L_uses_minus_tail": True,
            "U_uses_plus_tail": True,
            "band_core_error_multiplied_by_term_count": True,
            "normalization_rederived_from_coefficient_boxes": True,
            "live_recessive_continued_fraction_boundary_used": True,
            "stored_J_or_epsilon_trusted_as_primitive": False,
            "terminal_ratio_set_to_zero": False,
            "sign_grid_used": False,
            "coefficient_centers_treated_as_exact": False,
            "third_cut_executed": False,
            "lemma_A_modified": False,
            "state_changed": False,
            "bus_010_created": False,
        },
    }
    OUTPUT.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(final_code)
    for level in levels:
        print(
            f"extra_K={level['extra_K']} "
            f"pass={level['decisive_pass']} "
            f"kill={level['decisive_kill']}"
        )


if __name__ == "__main__":
    main()
