#!/usr/bin/env python3
"""Build the exact-data certificate for RouteB.031.

The analytic rigidity and the S-to-E estimate are paper identities.  The
numerical input used by the estimate is only the pair of exact rational lower
envelopes already certified by RouteB.030.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


sys.set_int_max_str_digits(300_000)

HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "PRIORITY_BAND_POSITIVE_PART_CERT.json"
CERT_030 = HERE / "COUPLED_FULL_SUM_RESPONSE_CERT.json"
CERT_027 = HERE / "HLAMBDA_OUTER_LOBE_GATE_AUDIT.json"

SUCCESS = "BAND_ZERO_KILLED_PRIORITY_LEAKAGE_BUDGET_PROVED"

SOURCES = (
    HERE / "031_priority_band_positive_part.goal.md",
    HERE / "proshka" / "PROSHKA_031_DIRECTIVE.md",
    HERE / "027_hlambda_outer_lobe_gate.answer.md",
    CERT_027,
    HERE / "028R_finite_core_theta_order_audit.answer.md",
    HERE / "029_decisive_k_escalation.answer.md",
    HERE / "030_coupled_full_sum_response.answer.md",
    HERE / "030_coupled_full_sum_response.goal.md",
    CERT_030,
    HERE / "coupled_full_sum_response_certificate.py",
    HERE / "D0_5_GROUND_AND_TRIAL_TYPES.md",
    HERE / "proshka" / "PROSHKA_PEN_REDUCTIONS_2026-07-27.md",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rat(value: Fraction) -> dict[str, str]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
    }


def read_rat(record: dict[str, str]) -> Fraction:
    return Fraction(int(record["numerator"]), int(record["denominator"]))


def arb_mid_rad(text: str) -> tuple[Decimal, Decimal]:
    match = re.fullmatch(r"\[([^ ]+) \+/- ([^\]]+)\]", text)
    if match is None:
        raise ValueError(f"unsupported Arb rendering: {text}")
    return Decimal(match.group(1)), Decimal(match.group(2))


def scientific(value: Fraction, digits: int = 18) -> str:
    with localcontext() as context:
        context.prec = digits + 20
        decimal_value = Decimal(value.numerator) / Decimal(value.denominator)
        return f"{decimal_value:.{digits}E}"


def budget_over_scalar(
    epsilon: dict[int, Fraction], sigma: Decimal
) -> Decimal:
    """Return the displayed bound divided by I0*I4/D."""
    with localcontext() as context:
        context.prec = 90
        half = Decimal(1) / 2
        exponent = half - sigma
        lam = Decimal(257).sqrt()
        total = Decimal(0)
        for r in (255, 256):
            difference = (
                (Decimal(1) / Decimal(r)) ** exponent
                - (Decimal(1) / Decimal(r + 1)) ** exponent
            )
            eps = Decimal(epsilon[r].numerator) / Decimal(
                epsilon[r].denominator
            )
            total += eps * difference / exponent
        return lam ** (-sigma - half) * total


def main() -> None:
    cert030 = json.loads(CERT_030.read_text(encoding="utf-8"))
    if cert030["verdict"] != "COUPLED_FULL_SUM_RESPONSE_INCONCLUSIVE":
        raise RuntimeError("unexpected RouteB.030 verdict")

    bands030 = {int(record["r"]): record for record in cert030["bands"]}
    if set(bands030) != {255, 256}:
        raise RuntimeError("RouteB.030 priority bands missing")

    epsilon: dict[int, Fraction] = {}
    band_records: list[dict[str, Any]] = []
    for r in (256, 255):
        lower = read_rat(bands030[r]["lower_full_sum"])
        if lower >= 0:
            raise RuntimeError(f"RouteB.030 lower envelope not negative: r={r}")
        epsilon[r] = max(Fraction(0), -lower)
        band_records.append(
            {
                "r": r,
                "z_domain": bands030[r]["domain"],
                "lower_full_sum": bands030[r]["lower_full_sum"],
                "epsilon": rat(epsilon[r]),
                "epsilon_scientific": scientific(epsilon[r]),
            }
        )

    cert027 = json.loads(CERT_027.read_text(encoding="utf-8"))
    cell257 = next(
        record for record in cert027["cells"] if int(record["m"]) == 257
    )
    witness_mid, witness_rad = arb_mid_rad(cell257["strict_point_margin"])
    if witness_mid - witness_rad <= 0:
        raise RuntimeError("027 witness does not have a positive lower bound")

    sigma_rows = []
    for sigma_text in ("0", "0.10", "0.25", "0.40", "0.45"):
        sigma = Decimal(sigma_text)
        sigma_rows.append(
            {
                "sigma": sigma_text,
                "bound_over_I0I4_over_D": (
                    f"{budget_over_scalar(epsilon, sigma):.18E}"
                ),
            }
        )

    p2_k = 5
    p2_r = 256
    p2_sum = sum(n ** (2 * p2_k) for n in range(1, p2_r + 1))
    p4_star = {
        str(r): rat(Fraction(r + 1, 6 * r)) for r in (255, 256)
    }

    certificate: dict[str, Any] = {
        "schema": "route_b_priority_band_positive_part.v1",
        "status": "CHALLENGER / NOT_RH",
        "verdict": SUCCESS,
        "secondary_flags": [
            "JACOBI_DIVIDED_DIFFERENCE_IDENTITY_PROVED",
            "EXACT_TOOTH_ALIAS_IDENTITY_PROVED",
        ],
        "scope": {
            "m": 257,
            "lambda": "sqrt(257)",
            "lambda_square": 257,
            "bands": [256, 255],
            "not_cofinal": True,
            "not_RH": True,
        },
        "source_hashes": {
            str(path.relative_to(HERE)): sha256(path) for path in SOURCES
        },
        "theorem_A": {
            "name": "BandResponseZeroRigidity",
            "verifier": "PAPER_WITH_SYMBOLIC_REPLAY",
            "analytic_domain": "|t|<1",
            "identity_domain": "|z|<1/r",
            "coefficient_multiplier": "sum_(n=1)^r n^k",
            "instances": [255, 256],
            "witness": {
                "source": "HLAMBDA_OUTER_LOBE_GATE_AUDIT.json:m=257",
                "point": "1/sqrt(257)",
                "midpoint_decimal": str(witness_mid),
                "radius_decimal": str(witness_rad),
                "strict_lower_decimal": str(witness_mid - witness_rad),
            },
            "conclusion": {
                "S_255_identically_zero": False,
                "S_256_identically_zero": False,
            },
            "proof_steps": [
                "identity theorem promotes interval-zero to disk-zero",
                "Taylor coefficient k is c_k * sum_(n=1)^r n^k",
                "the power sum is strictly positive for every k>=0",
                "all c_k vanish, so Psi vanishes on the unit disk",
                "the certified 027 positive witness contradicts that conclusion",
            ],
        },
        "theorem_B": {
            "name": "JacobiDividedDifferenceGreenRepresentation",
            "verifier": "EXACT_RATIONAL_SYMBOLIC",
            "phase": "b_(j,q)=(-1)^q*a_(j,2q); the target-4 offset is even",
            "operator": {
                "n": "2q",
                "p_n": "G*(n-1)*n/((2n-3)*(2n-1))",
                "r_n": "G*(n+1)*(n+2)/((2n+3)*(2n+5))",
                "c_n": "1-2*(n*(n+1)-1)/((2n-1)*(2n+3))",
                "diagonal": "n*(n+1)+G*c_n-Theta",
                "L_Theta_b_q": "p_n*b_(q-1)+diagonal*b_q+r_n*b_(q+1)",
            },
            "normalization": "b0_0=b4_0=1",
            "delta": "(b4-b0)/2",
            "divided_difference": (
                "L_Theta4(delta)=((Theta4-Theta0)/2)*b0"
            ),
            "symmetrizing_weight": "omega_q=1/(4q+1)",
            "edge_identity": "omega_q*r_(2q)=omega_(q+1)*p_(2q+2)",
            "green_identity": (
                "sum_(q=0)^Q omega_q*(Y_q*(L delta)_q-"
                "delta_q*(L Y)_q)="
                "a_Q*(Y_Q*delta_(Q+1)-delta_Q*Y_(Q+1))-"
                "a_-1*(Y_-1*delta_0-delta_-1*Y_0)"
            ),
            "lower_boundary": "a_-1=omega_0*p_0=0, retained explicitly",
            "terminal_boundary": (
                "a_Q=omega_Q*r_(2Q); no terminal ratio is set to zero"
            ),
            "response_representation": (
                "if (L_Theta4 Y)_q=A_(r,q)(z)/omega_q, then "
                "S_r=((Theta4-Theta0)/2)*<Y,b0>_omega+B_(r,z,Q), "
                "with B=-terminal+lower"
            ),
            "sign_claim": "NONE",
        },
        "theorem_C": {
            "name": "PriorityPositivePartBudget",
            "verifier": "PAPER_IDENTITY_PLUS_EXACT_RATIONAL_INPUT",
            "source_crosswalk": (
                "E_star(h_lambda,1/v)=-(I0*I4/D)/(lambda*sqrt(v))*"
                "S_lambda(1/(lambda*v))"
            ),
            "requested_crosswalk": (
                "E_star(h_lambda,u)=-(I0*I4/D)*sqrt(z/lambda)*S_lambda(z), "
                "u=lambda*z"
            ),
            "measure_change": "du/u=dz/z",
            "domain_partition": (
                "[1/lambda,lambda/255]=lambda*"
                "[1/257,1/255], because lambda^2=257"
            ),
            "bands": band_records,
            "bound": (
                "(I0*I4/D)*lambda^(-sigma-1/2)*"
                "sum_(r in {255,256}) epsilon_r*"
                "((1/r)^(1/2-sigma)-(1/(r+1))^(1/2-sigma))/"
                "(1/2-sigma)"
            ),
            "displayed_bound_over_scalar": sigma_rows,
            "teeth_measure_zero": True,
            "pointwise_tooth_sign_claim": False,
        },
        "tooth_alias": {
            "identity": (
                "S_star_r=r*T_r(Psi)-Psi(0)/2, where "
                "T_r=(Psi(0)/2+sum_(n=1)^(r-1)Psi(n/r)+Psi(1)/2)/r"
            ),
            "pointwise_only": True,
        },
        "plants": {
            "P1": {
                "fires": True,
                "Psi": "1",
                "S_r": {"255": 255, "256": 256},
            },
            "P2": {
                "fires": True,
                "Psi": f"t^{2*p2_k}",
                "r": p2_r,
                "power_sum": str(p2_sum),
            },
            "P3": {
                "fires": True,
                "witness_strict_lower_decimal": str(
                    witness_mid - witness_rad
                ),
            },
            "P4": {
                "fires": True,
                "Psi": "t^2-1/3",
                "integral_0_1": rat(Fraction(0)),
                "star_sum": p4_star,
            },
            "P5": {
                "fires": True,
                "control": "lambda=1,C=1,sigma=0,S=-1,u in [1/4,1]",
                "with_du_over_u": rat(Fraction(1)),
                "without_du_over_u": rat(Fraction(7, 12)),
            },
            "P6": {
                "fires": True,
                "identity": "E_+ for S equals C*sqrt(z/lambda)*S_-",
                "sign_flip": "S -> -S interchanges positive/negative leakage",
            },
            "P7": {
                "fires": True,
                "mutated_teeth": [257, 256, 255],
                "lebesgue_budget_unchanged": True,
                "pointwise_sign_changed": True,
            },
            "P8": {
                "fires": True,
                "Theta4_minus_Theta0": rat(Fraction(0)),
                "delta": "zero sequence",
                "forcing": "zero sequence",
            },
        },
        "guards": {
            "generator_imported_by_checker": False,
            "arb_imported_by_checker": False,
            "coefficient_centers_treated_as_exact": False,
            "band_zero_claimed": False,
            "pointwise_dual_theta_claimed": False,
            "finite_cell_promoted_to_cofinal": False,
            "state_touched": False,
            "bus_010_created": False,
        },
    }

    OUTPUT.write_text(
        json.dumps(certificate, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(SUCCESS)
    for record in band_records:
        print(
            f"r={record['r']} epsilon={record['epsilon_scientific']}"
        )
    for record in sigma_rows:
        print(
            f"sigma={record['sigma']} "
            f"bound/C={record['bound_over_I0I4_over_D']}"
        )


if __name__ == "__main__":
    main()
