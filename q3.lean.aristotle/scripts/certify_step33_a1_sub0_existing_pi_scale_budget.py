#!/usr/bin/env python3
"""Exact rational audit for the Step33A.1-A existing-pi scale route.

This is not a Lean proof object.  It records the exact rational arithmetic
behind the fail-closed route decision after the Proshka browser review:
existing endpoint pi bounds imply a scale-error slot much larger than the
current nominal scale-error ledger slot.
"""

from __future__ import annotations

import json
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = (
    ROOT
    / "ACTIVE"
    / "requests"
    / "step33_bootstrap"
    / "step33_a1_sub0_existing_pi_scale_budget_cert.json"
)


def dec(x: Fraction, prec: int = 80) -> str:
    getcontext().prec = prec
    return format(Decimal(x.numerator) / Decimal(x.denominator), "f")


def ceil_to_den(x: Fraction, den: int) -> Fraction:
    return Fraction((x.numerator * den + x.denominator - 1) // x.denominator, den)


def main() -> None:
    pi_lower = Fraction(314159265358979323846262, 10**23)
    pi_upper = Fraction(1570796326794896619231337, 5 * 10**23)
    scale_lower = Fraction(3, 10) / pi_upper
    scale_upper = Fraction(3, 10) / pi_lower
    nominal_scale = Fraction(190985931710274402922660516047, 2 * 10**30)
    current_scale_error = Fraction(1, 2 * 10**30)
    exact_required_error = max(
        abs(scale_lower - nominal_scale),
        abs(scale_upper - nominal_scale),
    )
    certified_required_error = ceil_to_den(exact_required_error, 10**30)

    payload = {
        "schema": "q3_psdpd_step33_a1_sub0_existing_pi_scale_budget_cert.v1",
        "status": "fail_closed_existing_pi_scale_budget_widening_fail",
        "failureCode": "STEP33_A1_SUB0_EXISTING_PI_SCALE_BUDGET_WIDENING_FAIL",
        "proofGrade": "RATIONAL_ARITHMETIC_CERT_NOT_LEAN",
        "source": {
            "piLower": {
                "value": f"{pi_lower.numerator}/{pi_lower.denominator}",
                "decimal": dec(pi_lower),
                "meaning": "Existing endpoint pi lower bound from PSD_CenteredCoeffRawOmegaAEndpointHighOrderLanding.lean",
            },
            "piUpper": {
                "value": f"{pi_upper.numerator}/{pi_upper.denominator}",
                "decimal": dec(pi_upper),
                "meaning": "Existing endpoint pi upper bound from PSD_CenteredCoeffRawOmegaAEndpointHighOrderLanding.lean",
            },
        },
        "derived": {
            "scaleLower": {
                "value": f"{scale_lower.numerator}/{scale_lower.denominator}",
                "decimal": dec(scale_lower),
            },
            "scaleUpper": {
                "value": f"{scale_upper.numerator}/{scale_upper.denominator}",
                "decimal": dec(scale_upper),
            },
            "nominalScale": {
                "value": f"{nominal_scale.numerator}/{nominal_scale.denominator}",
                "decimal": dec(nominal_scale),
            },
            "currentScaleError": {
                "value": f"{current_scale_error.numerator}/{current_scale_error.denominator}",
                "decimal": dec(current_scale_error),
            },
            "exactRequiredScaleError": {
                "value": f"{exact_required_error.numerator}/{exact_required_error.denominator}",
                "decimal": dec(exact_required_error),
            },
            "certifiedRequiredScaleError": {
                "value": f"{certified_required_error.numerator}/{certified_required_error.denominator}",
                "decimal": dec(certified_required_error),
            },
        },
        "checks": {
            "scaleLowerBelowNominal": scale_lower < nominal_scale,
            "scaleUpperAboveNominal": scale_upper > nominal_scale,
            "requiredErrorExceedsCurrentSlot": exact_required_error > current_scale_error,
            "certifiedRequiredErrorExceedsCurrentSlot": certified_required_error
            > current_scale_error,
        },
        "decision": (
            "Existing endpoint pi bounds cannot be spent through the current "
            "NominalScaleErrorAbs slot.  Do not mark generator exact-assembly "
            "fields true from this route; either prove a stronger pi/scale "
            "certificate or introduce a new same-unit product-budget cap."
        ),
    }

    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload["checks"], sort_keys=True))
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
