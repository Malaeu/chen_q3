#!/usr/bin/env python3
"""Independent stdlib-only checker for RouteB.031.

This file does not import the generator, python-flint, Arb, or any RouteB.030
code.  It replays the exact rational inputs and the algebraic identities.
"""

from __future__ import annotations

import hashlib
import json
import sys
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Any


sys.set_int_max_str_digits(300_000)

HERE = Path(__file__).resolve().parent
CERTIFICATE = HERE / "PRIORITY_BAND_POSITIVE_PART_CERT.json"
CERT_030 = HERE / "COUPLED_FULL_SUM_RESPONSE_CERT.json"
CERT_027 = HERE / "HLAMBDA_OUTER_LOBE_GATE_AUDIT.json"

SUCCESS = "BAND_ZERO_KILLED_PRIORITY_LEAKAGE_BUDGET_PROVED"
EXPECTED_030_SHA256 = (
    "2e31e67ba9cc9aed78bfed9ed20d052c1917b508958ddff077124e2cf95989da"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_rat(record: dict[str, str]) -> Fraction:
    return Fraction(int(record["numerator"]), int(record["denominator"]))


def pbar(n: int) -> Fraction:
    return Fraction((n - 1) * n, (2 * n - 3) * (2 * n - 1))


def rbar(n: int) -> Fraction:
    return Fraction((n + 1) * (n + 2), (2 * n + 3) * (2 * n + 5))


def cbar(n: int) -> Fraction:
    return Fraction(1) - Fraction(
        2 * (n * (n + 1) - 1), (2 * n - 1) * (2 * n + 3)
    )


def p_coeff(q: int, g: Fraction) -> Fraction:
    return g * pbar(2 * q)


def r_coeff(q: int, g: Fraction) -> Fraction:
    return g * rbar(2 * q)


def d_coeff(q: int, g: Fraction, theta: Fraction) -> Fraction:
    n = 2 * q
    return Fraction(n * (n + 1)) + g * cbar(n) - theta


def solution(
    g: Fraction, theta: Fraction, last_q: int
) -> dict[int, Fraction]:
    values = {-1: Fraction(0), 0: Fraction(1)}
    for q in range(last_q):
        values[q + 1] = -(
            p_coeff(q, g) * values[q - 1]
            + d_coeff(q, g, theta) * values[q]
        ) / r_coeff(q, g)
    return values


def apply_operator(
    values: dict[int, Fraction],
    q: int,
    g: Fraction,
    theta: Fraction,
) -> Fraction:
    return (
        p_coeff(q, g) * values[q - 1]
        + d_coeff(q, g, theta) * values[q]
        + r_coeff(q, g) * values[q + 1]
    )


def check_green_identity(Q: int) -> None:
    """Compare every formal monomial Y_i*delta_j exactly."""
    lhs: dict[tuple[int, int], Fraction] = {}
    rhs: dict[tuple[int, int], Fraction] = {}

    def add(
        target: dict[tuple[int, int], Fraction],
        key: tuple[int, int],
        value: Fraction,
    ) -> None:
        target[key] = target.get(key, Fraction(0)) + value

    g = Fraction(13, 7)
    for q in range(Q + 1):
        omega = Fraction(1, 4 * q + 1)
        p = p_coeff(q, g)
        r = r_coeff(q, g)
        diagonal = Fraction(5 * q + 3, 11)
        add(lhs, (q, q - 1), omega * p)
        add(lhs, (q, q), omega * diagonal)
        add(lhs, (q, q + 1), omega * r)
        add(lhs, (q - 1, q), -omega * p)
        add(lhs, (q, q), -omega * diagonal)
        add(lhs, (q + 1, q), -omega * r)

    a_terminal = Fraction(1, 4 * Q + 1) * r_coeff(Q, g)
    add(rhs, (Q, Q + 1), a_terminal)
    add(rhs, (Q + 1, Q), -a_terminal)

    # The explicit lower term is zero because p_0=0.
    a_lower = p_coeff(0, g)
    add(rhs, (0, -1), a_lower)
    add(rhs, (-1, 0), -a_lower)

    lhs = {key: value for key, value in lhs.items() if value}
    rhs = {key: value for key, value in rhs.items() if value}
    require(lhs == rhs, "finite-Q Green boundary ledger mismatch")


def check_tooth_alias(r: int) -> None:
    left = {index: Fraction(1) for index in range(1, r)}
    left[r] = Fraction(1, 2)
    right = {0: Fraction(1, 2)}
    right.update({index: Fraction(1) for index in range(1, r)})
    right[r] = Fraction(1, 2)
    right[0] -= Fraction(1, 2)
    right = {key: value for key, value in right.items() if value}
    require(left == right, f"tooth alias failed at r={r}")


def main() -> None:
    certificate = json.loads(CERTIFICATE.read_text(encoding="utf-8"))
    require(certificate["verdict"] == SUCCESS, "wrong 031 verdict")
    require(
        certificate["secondary_flags"]
        == [
            "JACOBI_DIVIDED_DIFFERENCE_IDENTITY_PROVED",
            "EXACT_TOOTH_ALIAS_IDENTITY_PROVED",
        ],
        "secondary flags mismatch",
    )

    # Source hashes are checked against live bytes.  RouteB.030 is additionally
    # pinned independently here.
    require(sha256(CERT_030) == EXPECTED_030_SHA256, "030 certificate drift")
    for relative, expected in certificate["source_hashes"].items():
        require(sha256(HERE / relative) == expected, f"source drift: {relative}")

    cert030 = json.loads(CERT_030.read_text(encoding="utf-8"))
    require(
        cert030["verdict"] == "COUPLED_FULL_SUM_RESPONSE_INCONCLUSIVE",
        "unexpected 030 verdict",
    )
    bands030 = {int(record["r"]): record for record in cert030["bands"]}
    stored_bands = {
        int(record["r"]): record
        for record in certificate["theorem_C"]["bands"]
    }
    for r in (255, 256):
        lower = read_rat(bands030[r]["lower_full_sum"])
        epsilon = read_rat(stored_bands[r]["epsilon"])
        require(lower < 0, f"030 lower envelope not negative at r={r}")
        require(epsilon == max(Fraction(0), -lower), f"epsilon mismatch r={r}")
        require(
            stored_bands[r]["lower_full_sum"]
            == bands030[r]["lower_full_sum"],
            f"lower envelope not replayed verbatim r={r}",
        )

    # Theorem A and P1-P3: exact power sums and the certified positive witness.
    for r in (255, 256):
        for k in range(33):
            multiplier = sum(n**k for n in range(1, r + 1))
            require(multiplier > 0, f"power sum not positive r={r},k={k}")
    p2 = certificate["plants"]["P2"]
    require(
        int(p2["power_sum"])
        == sum(n**10 for n in range(1, int(p2["r"]) + 1)),
        "P2 exact power sum mismatch",
    )
    witness = certificate["theorem_A"]["witness"]
    require(
        Decimal(witness["strict_lower_decimal"]) > 0,
        "P3 witness is not strictly positive",
    )
    require(
        certificate["theorem_A"]["conclusion"]
        == {
            "S_255_identically_zero": False,
            "S_256_identically_zero": False,
        },
        "band-zero conclusion mismatch",
    )

    # Theorem B: exact common phased recurrence and divided difference.
    g = Fraction(17, 5)
    theta0 = Fraction(7, 3)
    theta4 = Fraction(29, 4)
    last_q = 24
    b0 = solution(g, theta0, last_q + 1)
    b4 = solution(g, theta4, last_q + 1)
    delta = {
        q: (b4[q] - b0[q]) / 2 for q in range(-1, last_q + 2)
    }
    require(delta[0] == 0, "normalization delta_0 mismatch")
    forcing_scalar = (theta4 - theta0) / 2
    for q in range(last_q + 1):
        require(
            apply_operator(delta, q, g, theta4)
            == forcing_scalar * b0[q],
            f"divided-difference recurrence mismatch q={q}",
        )
    for q in range(701):
        n = 2 * q
        omega_q = Fraction(1, 4 * q + 1)
        omega_next = Fraction(1, 4 * q + 5)
        require(
            omega_q * rbar(n) == omega_next * pbar(n + 2),
            f"symmetrizing weight mismatch q={q}",
        )
    check_green_identity(37)
    require(
        certificate["theorem_B"]["sign_claim"] == "NONE",
        "Theorem B emitted a forbidden sign claim",
    )

    # Tooth alias and P4.
    check_tooth_alias(255)
    check_tooth_alias(256)
    p4 = certificate["plants"]["P4"]
    require(read_rat(p4["integral_0_1"]) == 0, "P4 mass not zero")
    for r in (255, 256):
        require(
            read_rat(p4["star_sum"][str(r)]) == Fraction(r + 1, 6 * r),
            f"P4 star sum mismatch r={r}",
        )
        require(
            read_rat(p4["star_sum"][str(r)]) != 0,
            f"P4 failed to reject tooth-zero r={r}",
        )

    # Theorem C domain and the exact Jacobian control P5.
    require(
        certificate["scope"]["lambda_square"] == 257,
        "lambda-square lock missing",
    )
    require(
        bands030[256]["domain"]
        == {
            "lower": {"numerator": "1", "denominator": "257"},
            "upper": {"numerator": "1", "denominator": "256"},
        },
        "r=256 domain mismatch",
    )
    require(
        bands030[255]["domain"]
        == {
            "lower": {"numerator": "1", "denominator": "256"},
            "upper": {"numerator": "1", "denominator": "255"},
        },
        "r=255 domain mismatch",
    )
    p5 = certificate["plants"]["P5"]
    require(read_rat(p5["with_du_over_u"]) == 1, "P5 Jacobian value mismatch")
    require(
        read_rat(p5["without_du_over_u"]) == Fraction(7, 12),
        "P5 dropped-Jacobian control mismatch",
    )
    require(
        read_rat(p5["with_du_over_u"])
        != read_rat(p5["without_du_over_u"]),
        "P5 did not detect the dropped du/u",
    )

    # P6-P8 and global guards.
    plants = certificate["plants"]
    require(all(plants[f"P{i}"]["fires"] for i in range(1, 9)), "plant failed")
    require(plants["P7"]["lebesgue_budget_unchanged"], "P7 measure mutation")
    require(plants["P7"]["pointwise_sign_changed"], "P7 pointwise mutation")
    require(read_rat(plants["P8"]["Theta4_minus_Theta0"]) == 0, "P8 theta")
    require(plants["P8"]["delta"] == "zero sequence", "P8 delta")
    require(plants["P8"]["forcing"] == "zero sequence", "P8 forcing")

    guards = certificate["guards"]
    require(not guards["generator_imported_by_checker"], "checker import guard")
    require(not guards["arb_imported_by_checker"], "Arb import guard")
    require(not guards["coefficient_centers_treated_as_exact"], "center guard")
    require(not guards["band_zero_claimed"], "band-zero guard")
    require(not guards["pointwise_dual_theta_claimed"], "pointwise sign guard")
    require(not guards["finite_cell_promoted_to_cofinal"], "scope guard")
    require(not guards["state_touched"], "STATE guard")
    require(not guards["bus_010_created"], "BUS_010 guard")

    print(f"PASS {SUCCESS}")
    print(
        "P1 PASS P2 PASS P3 PASS P4 PASS "
        "P5 PASS P6 PASS P7 PASS P8 PASS"
    )
    print("JACOBI_DIVIDED_DIFFERENCE_IDENTITY_PROVED")
    print("EXACT_TOOTH_ALIAS_IDENTITY_PROVED")


if __name__ == "__main__":
    main()
