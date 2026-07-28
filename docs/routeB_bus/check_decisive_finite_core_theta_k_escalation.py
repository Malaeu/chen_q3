#!/usr/bin/env python3
"""Independent exact checker for goal 029 decisive K escalation."""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import fmpq, fmpq_poly


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CERTIFICATE = HERE / "DECISIVE_FINITE_CORE_THETA_K_ESCALATION.json"
AUDIT_026 = HERE / "LAMBDA_BRACKET_RESUME_AUDIT.json"
EXPECTED_LEVELS = (20, 40)
R_VALUES = (256, 255)
OLD_WITNESS = (
    Fraction(65281, 16711680),
    Fraction(32641, 8355840),
)
PASS_CODE = "DUAL_THETA_DOMINANCE_PROVED_PRIORITY_BANDS"
KILL_CODE = "DUAL_THETA_DOMINANCE_KILLED_FINITE_CELL"
INCONCLUSIVE_CODE = "K_ESCALATION_INCONCLUSIVE"

sys.set_int_max_str_digits(200_000)
sys.path.insert(0, str(HERE))
import check_finite_core_theta_certificate as base  # noqa: E402


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rat_record(value: Fraction) -> dict[str, str]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
    }


def interval_record(
    lower: Fraction, upper: Fraction
) -> dict[str, dict[str, str]]:
    return {"lower": rat_record(lower), "upper": rat_record(upper)}


def normalization_record(derived: dict[str, Any]) -> dict[str, Any]:
    return {
        "finite_l2_sq": interval_record(*derived["finite_l2_sq"]),
        "tail_l2_sq_upper": rat_record(derived["tail_l2_sq_upper"]),
        "total_l2_sq": interval_record(*derived["total_l2_sq"]),
        "J": interval_record(*derived["J"]),
        "epsilon": interval_record(*derived["epsilon"]),
        "raw_last_abs_lower": rat_record(
            derived["raw_last_abs_lower"]
        ),
        "raw_last_abs_upper": rat_record(
            derived["raw_last_abs_upper"]
        ),
        "tail_ratio_upper_after_J_cancellation": rat_record(
            derived["tail_ratio_upper"]
        ),
    }


def verify_extreme(
    record: dict[str, Any], values: list[fmpq], use_maximum: bool
) -> None:
    extreme = max(values) if use_maximum else min(values)
    require(
        int(record["index"]) == values.index(extreme),
        "extreme index mismatch",
    )
    require(
        base.read_rat(record["value"]) == base.fraction_of(extreme),
        "extreme rational mismatch",
    )
    if "strictly_negative" in record:
        require(
            bool(record["strictly_negative"]) == (extreme < 0),
            "negative sign field mismatch",
        )
    if "strictly_positive" in record:
        require(
            bool(record["strictly_positive"]) == (extreme > 0),
            "positive sign field mismatch",
        )


def tooth_value(polynomial: fmpq_poly, r: int) -> fmpq:
    sums = base.power_sums(r - 1, polynomial.degree())
    value = fmpq(0)
    for degree in range(polynomial.degree() + 1):
        value += polynomial[degree] * (
            fmpq(sums[degree], r**degree) + fmpq(1, 2)
        )
    return value


def verify_scalar(record: dict[str, Any], value: fmpq) -> None:
    require(
        base.read_rat(record["value"]) == base.fraction_of(value),
        "scalar rational mismatch",
    )
    require(
        bool(record["strictly_negative"]) == (value < 0),
        "scalar negative field mismatch",
    )
    require(
        bool(record["nonnegative"]) == (value >= 0),
        "scalar nonnegative field mismatch",
    )


def main() -> None:
    certificate = json.loads(CERTIFICATE.read_text())
    require(
        certificate["schema"]
        == "route_b_decisive_finite_core_theta_k_escalation.v1",
        "wrong schema",
    )
    require(
        certificate["verdict"]
        in (PASS_CODE, KILL_CODE, INCONCLUSIVE_CODE),
        "unknown verdict",
    )
    lock = certificate["object_lock"]
    for source in lock["source_hashes"]:
        path = ROOT / source["path"]
        require(path.is_file(), f"missing source {path}")
        require(sha256(path) == source["sha256"], f"hash drift {path}")
    audit = json.loads(AUDIT_026.read_text())
    cases = {
        int(case["target_degree"]): case
        for case in audit["cases"]
        if int(case["m"]) == 257
        and int(case["target_degree"]) in (0, 4)
    }
    for degree in (0, 4):
        case = cases[degree]
        require(
            lock["theta_intervals"][str(degree)]
            == case["Theta_bracket"],
            "Theta interval source-lock mismatch",
        )
        continued = case["continued_fraction"]
        expected_boundary = {
            "K0_strict_margin": case["K0_strict_margin"],
            "terminal_interval": continued["terminal_interval"],
            "live_ratio_interval_before_Krawczyk": continued[
                "live_ratio_interval_before_Krawczyk"
            ],
            "terminal_ratio_zero_used": continued[
                "terminal_ratio_zero_used"
            ],
        }
        require(
            lock["live_recessive_boundary"][str(degree)]
            == expected_boundary,
            "live recessive boundary source-lock mismatch",
        )
        require(
            expected_boundary["terminal_ratio_zero_used"] is False,
            "source used terminal ratio zero",
        )

    digits = int(lock["coefficient_decimal_digits"])
    records = lock["coefficient_enclosures_to_maximum"]
    maximum_degree = max(
        int(mode_records[-1]["legendre_degree"])
        for mode_records in records.values()
    )
    legendre = base.legendre_polynomials(maximum_degree)

    computed_verdict = INCONCLUSIVE_CODE
    for level_index, level in enumerate(certificate["levels"]):
        extra = int(level["extra_K"])
        require(extra == EXPECTED_LEVELS[level_index], "cut order mismatch")
        modes = {}
        errors = {}
        epsilon_ratio = {}
        for degree in (0, 4):
            end_degree = int(
                level["last_degree_by_mode"][str(degree)]
            )
            base_degree = int(lock["base_last_degree"][str(degree)])
            require(
                end_degree == base_degree + 2 * extra,
                "cut endpoint mismatch",
            )
            mode_records = [
                record
                for record in records[str(degree)]
                if int(record["legendre_degree"]) <= end_degree
            ]
            require(
                int(mode_records[-1]["legendre_degree"]) == end_degree,
                "coefficient prefix mismatch",
            )
            modes[degree], errors[degree] = base.reconstruct_mode(
                degree, mode_records, legendre
            )
            derived = base.derive_normalization(mode_records, digits)
            require(
                level["normalization_certificates"][str(degree)]
                == normalization_record(derived),
                "normalization rederivation mismatch",
            )
            epsilon_ratio[degree] = derived["tail_ratio_upper"]
            require(
                base.read_rat(
                    level["epsilon_ratio_upper_by_mode"][str(degree)]
                )
                == epsilon_ratio[degree],
                "epsilon/J ratio mismatch",
            )

        psi = (modes[4] - modes[0]) / 2
        point_core_error = (errors[0] + errors[4]) / 2
        epsilon_psi = sum(epsilon_ratio.values(), Fraction(0))
        require(
            base.read_rat(level["point_core_error"]) == point_core_error,
            "point core error mismatch",
        )
        require(
            base.read_rat(level["epsilon_psi_upper"]) == epsilon_psi,
            "epsilon Psi mismatch",
        )

        pass_flags = []
        kill_flags = []
        for r, band, tooth in zip(
            R_VALUES, level["bands"], level["teeth"]
        ):
            require((int(band["m"]), int(band["r"])) == (257, r), "band")
            lower, upper = base.read_interval(band["exact_domain"])
            require(
                (lower, upper) == (Fraction(1, r + 1), Fraction(1, r)),
                "band domain mismatch",
            )
            band_core_error = r * point_core_error
            band_tail = r * epsilon_psi
            require(
                base.read_rat(band["band_core_error"]) == band_core_error,
                "band core error count mismatch",
            )
            require(
                base.read_rat(band["band_tail_budget"]) == band_tail,
                "band tail mismatch",
            )
            center = base.band_polynomial(psi, r)
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
            verify_extreme(
                band["L_bernstein_minimum"],
                lower_values,
                use_maximum=False,
            )
            verify_extreme(
                band["U_bernstein_maximum"],
                upper_values,
                use_maximum=True,
            )
            pass_band = min(lower_values) >= 0
            kill_band = max(upper_values) < 0
            require(pass_band == bool(band["pass_full_band"]), "band pass")
            require(kill_band == bool(band["kill_full_band"]), "band kill")

            witness_kill = False
            if r == 255:
                witness = band["old_witness"]
                require(
                    base.read_interval(witness["exact_domain"])
                    == OLD_WITNESS,
                    "old witness mismatch",
                )
                witness_values = base.bernstein_coefficients(
                    upper_envelope, *OLD_WITNESS
                )
                verify_extreme(
                    witness["U_bernstein_maximum"],
                    witness_values,
                    use_maximum=True,
                )
                witness_kill = max(witness_values) < 0
                require(
                    witness_kill == bool(witness["true_kill"]),
                    "witness kill mismatch",
                )
            else:
                require(band["old_witness"] is None, "spurious witness")

            effective_count = Fraction(2 * r - 1, 2)
            tooth_center = tooth_value(psi, r)
            tooth_core_error = effective_count * point_core_error
            tooth_tail = effective_count * epsilon_psi
            tooth_lower = tooth_center - base.fq(
                tooth_core_error + tooth_tail
            )
            tooth_upper = tooth_center + base.fq(
                tooth_core_error + tooth_tail
            )
            require(
                base.read_rat(tooth["effective_count"]) == effective_count,
                "tooth count mismatch",
            )
            require(
                base.read_rat(tooth["center"])
                == base.fraction_of(tooth_center),
                "tooth center mismatch",
            )
            require(
                base.read_rat(tooth["core_error"]) == tooth_core_error,
                "tooth core error mismatch",
            )
            require(
                base.read_rat(tooth["tail_budget"]) == tooth_tail,
                "tooth tail mismatch",
            )
            verify_scalar(tooth["L"], tooth_lower)
            verify_scalar(tooth["U"], tooth_upper)
            pass_tooth = tooth_lower >= 0
            kill_tooth = tooth_upper < 0
            require(pass_tooth == bool(tooth["pass"]), "tooth pass")
            require(kill_tooth == bool(tooth["kill"]), "tooth kill")
            pass_flags.extend((pass_band, pass_tooth))
            kill_flags.extend((kill_band, witness_kill, kill_tooth))

        level_pass = all(pass_flags)
        level_kill = any(kill_flags)
        require(
            level_pass == bool(level["decisive_pass"]),
            "level pass mismatch",
        )
        require(
            level_kill == bool(level["decisive_kill"]),
            "level kill mismatch",
        )
        if level_pass:
            computed_verdict = PASS_CODE
            require(
                level_index + 1 == len(certificate["levels"]),
                "work continued after decisive pass",
            )
            break
        if level_kill:
            computed_verdict = KILL_CODE
            require(
                level_index + 1 == len(certificate["levels"]),
                "work continued after decisive kill",
            )
            break

    if computed_verdict == INCONCLUSIVE_CODE:
        require(len(certificate["levels"]) == 2, "second cut missing")
    require(
        certificate["verdict"] == computed_verdict,
        "final verdict mismatch",
    )

    guards = certificate["guards"]
    require(guards["L_uses_minus_tail"] is True, "L sign guard")
    require(guards["U_uses_plus_tail"] is True, "U sign guard")
    require(
        guards["band_core_error_multiplied_by_term_count"] is True,
        "band error count guard",
    )
    require(
        guards["normalization_rederived_from_coefficient_boxes"] is True,
        "normalization derivation guard",
    )
    require(
        guards["live_recessive_continued_fraction_boundary_used"] is True,
        "live continued-fraction boundary guard",
    )
    require(
        guards["stored_J_or_epsilon_trusted_as_primitive"] is False,
        "normalization primitive guard",
    )
    require(guards["terminal_ratio_set_to_zero"] is False, "ratio guard")
    require(guards["sign_grid_used"] is False, "grid guard")
    require(
        guards["coefficient_centers_treated_as_exact"] is False,
        "coefficient uncertainty guard",
    )
    require(guards["third_cut_executed"] is False, "third cut guard")
    require(guards["lemma_A_modified"] is False, "Lemma A guard")
    require(guards["state_changed"] is False, "STATE guard")
    require(guards["bus_010_created"] is False, "Bus guard")

    print("DECISIVE_FINITE_CORE_THETA_K_ESCALATION_CHECK_OK")
    print(computed_verdict)


if __name__ == "__main__":
    main()
