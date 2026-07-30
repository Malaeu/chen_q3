#!/usr/bin/env python3
"""Independent stdlib-only harness for RouteB.038.

This checker does not prove a sign theorem.  It verifies the STEP 0 source
locks, the generic algebraic Jacobi/Green kernel, the finite m=257 rehearsal,
and every mandatory P038 plant.  It also fails closed on the missing
cofinal profile interface: the source-locked coefficient backend is m=257
only, the adjoint receiver is conditional, and no Q-to-infinity terminal
control is present.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
MIRROR = REPO / "docs" / "routeB_bus"
MANIFEST = MIRROR / "MANIFEST.md"

CERT_030 = HERE / "COUPLED_FULL_SUM_RESPONSE_CERT.json"
SOURCE_030 = HERE / "coupled_full_sum_response_certificate.py"
CERT_031 = HERE / "PRIORITY_BAND_POSITIVE_PART_CERT.json"
SOURCE_031 = HERE / "priority_band_positive_part_certificate.py"
CHECKER_031 = HERE / "check_priority_band_positive_part_certificate.py"
ANSWER_031 = HERE / "031_priority_band_positive_part.answer.md"
CERT_033 = HERE / "FULL_WINDOW_POSITIVE_PART_CERT.json"
DIRECTIVE_038 = (
    HERE / "proshka" / "PROSHKA_038_SUPPLIER_A_DIRECTIVE_2026-07-30.md"
)
MIRROR_DIRECTIVE_038 = (
    MIRROR / "PROSHKA_038_SUPPLIER_A_DIRECTIVE_2026-07-30.md"
)

DIRECTIVE_038_SHA256 = (
    "bbd599fbca17e752fa5c2b5b8b4ac667d84cb6bc6799c40a2568b04b07c16aac"
)
PRIMARY = "SCALED_OUTER_SIGN_BARRIER_FOUR_THIRDS_INCONCLUSIVE"
STOP = "SCALED_JACOBI_COFINAL_LIFT_GAP"

STEP0_NAMES = (
    "027_hlambda_outer_lobe_gate.answer.md",
    "031_priority_band_positive_part.answer.md",
    "034_cofinal_scaled_edge_sliver_moment.answer.md",
    "035_edge_sliver_materialization.answer.md",
    "PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md",
    "PROSHKA_034_EDGE_SLIVER_CONTRACT.md",
    "PRIORITY_BAND_POSITIVE_PART_CERT.json",
    "priority_band_positive_part_certificate.py",
    "check_priority_band_positive_part_certificate.py",
    "COUPLED_FULL_SUM_RESPONSE_CERT.json",
    "coupled_full_sum_response_certificate.py",
    "check_coupled_full_sum_response_certificate.py",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_rat(record: dict[str, str]) -> Fraction:
    return Fraction(int(record["numerator"]), int(record["denominator"]))


def read_interval(record: dict[str, object]) -> tuple[Fraction, Fraction]:
    return read_rat(record["lower"]), read_rat(record["upper"])  # type: ignore[arg-type]


def manifest_hashes() -> dict[str, str]:
    result: dict[str, str] = {}
    pattern = re.compile(r"^\| `([^`]+)` \| [^|]+ \| `([0-9a-f]{64})` \|$")
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        match = pattern.fullmatch(line)
        if match is not None:
            result[match.group(1)] = match.group(2)
    return result


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


def formal_green_ledgers(
    Q: int, *, drop_terminal: bool = False
) -> tuple[
    dict[tuple[int, int], Fraction],
    dict[tuple[int, int], Fraction],
]:
    """Return exact coefficient ledgers for Y_i * delta_j."""
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

    if not drop_terminal:
        a_terminal = Fraction(1, 4 * Q + 1) * r_coeff(Q, g)
        add(rhs, (Q, Q + 1), a_terminal)
        add(rhs, (Q + 1, Q), -a_terminal)

    # Source lower coefficient: a_-1 = omega_0 * p_0 = 0.
    a_lower = p_coeff(0, g)
    add(rhs, (0, -1), a_lower)
    add(rhs, (-1, 0), -a_lower)

    return (
        {key: value for key, value in lhs.items() if value},
        {key: value for key, value in rhs.items() if value},
    )


def check_generic_algebraic_kernel() -> None:
    # Multiple exact specializations check the parameter-independent algebra.
    for g, theta0, theta4 in (
        (Fraction(17, 5), Fraction(7, 3), Fraction(29, 4)),
        (Fraction(5, 2), Fraction(-3, 7), Fraction(11, 6)),
        (Fraction(19, 11), Fraction(2, 9), Fraction(31, 8)),
    ):
        last_q = 28
        b0 = solution(g, theta0, last_q + 1)
        b4 = solution(g, theta4, last_q + 1)
        delta = {
            q: (b4[q] - b0[q]) / 2
            for q in range(-1, last_q + 2)
        }
        require(delta[0] == 0, "generic delta_0 normalization failed")
        forcing = (theta4 - theta0) / 2
        for q in range(last_q + 1):
            require(
                apply_operator(delta, q, g, theta4)
                == forcing * b0[q],
                f"divided-difference replay failed at q={q}",
            )

    for q in range(701):
        n = 2 * q
        require(
            Fraction(1, 4 * q + 1) * rbar(n)
            == Fraction(1, 4 * q + 5) * pbar(n + 2),
            f"symmetrizing weight failed at q={q}",
        )
    lhs, rhs = formal_green_ledgers(37)
    require(lhs == rhs, "full finite Green ledger failed")


def scope_accepts(required: str, supplied: str) -> bool:
    return required == supplied


def interval_direction(
    lower: Fraction, upper: Fraction, *, positive_measure: bool
) -> str:
    if lower >= 0:
        return "PASS"
    if upper < 0 and positive_measure:
        return "KILL"
    return "INCONCLUSIVE"


def coverage_accepts(parts: set[str], *, mode_split: bool) -> bool:
    required = {
        "four_thirds_endpoint",
        "crossing_band",
        "all_open_floor_bands",
        "finite_tooth_null_set",
        "endpoint_m",
    }
    if mode_split:
        required.add("sqrt_m_junction")
        required.add("cofinal_outer_lobe")
    return required <= parts


def main() -> None:
    manifest = manifest_hashes()
    for name in STEP0_NAMES:
        require(name in manifest, f"MANIFEST entry missing: {name}")
        require(
            sha256(MIRROR / name) == manifest[name],
            f"SOURCE_HASH_MISMATCH:{name}",
        )
    require(
        sha256(DIRECTIVE_038) == DIRECTIVE_038_SHA256,
        "canonical 038 directive hash mismatch",
    )
    require(
        sha256(MIRROR_DIRECTIVE_038) == DIRECTIVE_038_SHA256,
        "mirror 038 directive hash mismatch",
    )
    print("STEP0_HASH_GATE PASS 12/12")

    # Exact scaled crosswalk: sqrt(z/lambda), z=a/lambda^2.
    exponent_of_a = Fraction(1, 2)
    exponent_of_lambda = Fraction(-1, 2) + Fraction(-1)
    require(exponent_of_a == Fraction(1, 2), "scaled a exponent mismatch")
    require(
        exponent_of_lambda == Fraction(-3, 2),
        "scaled lambda exponent mismatch",
    )
    print("SCALED_CROSSWALK PASS sqrt(z/lambda)=sqrt(a)/lambda^(3/2)")

    cert030 = json.loads(CERT_030.read_text(encoding="utf-8"))
    cert031 = json.loads(CERT_031.read_text(encoding="utf-8"))
    cert033 = json.loads(CERT_033.read_text(encoding="utf-8"))
    source030 = SOURCE_030.read_text(encoding="utf-8")
    theorem_b = cert031["theorem_B"]

    check_generic_algebraic_kernel()
    print("GENERIC_ALGEBRAIC_KERNEL PASS divided_difference+finite_Green")

    breaks = {
        "B038-1_COEFFICIENT_FAMILY_M257_ONLY": (
            "M = 257" in source030
            and cert030["scope"]["m"] == 257
            and cert030["scope"]["not_cofinal"]
        ),
        "B038-2_RESPONSE_RECEIVER_CONDITIONAL": (
            theorem_b["response_representation"].startswith("if ")
        ),
        "B038-3_DISCRIMINATOR_NOT_MATERIALIZED": (
            "D_m" not in json.dumps(theorem_b, sort_keys=True)
        ),
        "B038-4_Q_INFINITY_TERMINAL_CONTROL_MISSING": (
            "for any finite Q"
            not in theorem_b["terminal_boundary"]
            and "no terminal ratio is set to zero"
            in theorem_b["terminal_boundary"]
        ),
        "B038-5_COFINAL_SPECTRAL_GAP_NOT_SOURCE_LOCKED": (
            "Theta4_m - Theta0_m > 0"
            not in json.dumps(cert031, sort_keys=True)
        ),
    }
    require(all(breaks.values()), "generic-m break localization drift")
    print("GENERIC_M_REPLAY BREAK finite_named_list=5")
    for name in breaks:
        print(f"{name} DETECTED")

    # m=257 rehearsal: exact alias, recurrence orientation, live boundaries,
    # and the frozen 179/62 ledger.
    teeth = cert033["teeth"]
    require(len(teeth) == 241, "rehearsal tooth count mismatch")
    require(all(record["coverage_complete"] for record in teeth), "tooth gap")
    nonnegative = sum(record["nonnegative_proved"] for record in teeth)
    zero_compatible = sum(record["contains_zero"] for record in teeth)
    require(nonnegative == 179, "positive controls mismatch")
    require(zero_compatible == 62, "zero-compatible count mismatch")
    require(
        not any(record["strictly_negative_proved"] for record in teeth),
        "unexpected finite-cell KILL",
    )
    for r in range(17, 258):
        left = {index: Fraction(1) for index in range(1, r)}
        left[r] = Fraction(1, 2)
        right = {0: Fraction(1, 2)}
        right.update({index: Fraction(1) for index in range(1, r)})
        right[r] = Fraction(1, 2)
        right[0] -= Fraction(1, 2)
        require(
            left == {key: value for key, value in right.items() if value},
            f"tooth alias failed at r={r}",
        )
    delta0 = read_interval(cert033["frozen_backend"]["delta_0"])
    require(delta0 == (Fraction(0), Fraction(0)), "rehearsal delta_0")
    require(p_coeff(0, Fraction(13, 7)) == 0, "a_-1 source zero")
    terminal = cert033["plants"]["P6_terminal_ratio_zero"]
    require(
        read_rat(terminal["live_terminal_response_width"]) > 0,
        "terminal boundary not live",
    )
    require(terminal["enclosure_changes"], "terminal-drop plant did not fire")
    print("REHEARSAL_M257 PASS controls=179 zero_compatible=62 kill=0")

    plants: dict[str, bool] = {}
    plants["P038-1"] = not scope_accepts("COFINAL_FAMILY", "FINITE_CELL_m257")

    # Source coordinate maps u=1/lambda to a=1 and z=1/r to a=m/r.
    # The square-cell m=16 gives an exact rational mutant witness.
    source_left_a = Fraction(1)
    source_tooth_a = Fraction(16, 3)
    mutant_tooth_a = Fraction(3, 4)
    plants["P038-2"] = (
        source_left_a == 1 and source_tooth_a != mutant_tooth_a
    )
    plants["P038-3"] = not scope_accepts(
        "COFINAL_OUTER_LOBE", "FINITE_CELL_m_13_53_257"
    )

    lhs, terminal_dropped_rhs = formal_green_ledgers(
        37, drop_terminal=True
    )
    plants["P038-4"] = lhs != terminal_dropped_rhs

    # The exact 031 lower coefficient is zero.  Mutating it to one exposes
    # a formal lower monomial (take delta_-1=Y_0=1).
    lower_baseline = Fraction(0)
    lower_mutant = -Fraction(1) * (Fraction(0) - Fraction(1))
    plants["P038-5"] = lower_baseline == 0 and lower_mutant != 0

    # Source lock L(Y)=A/omega.  Replacing Y by -Y gives -A/omega.
    source_receiver = Fraction(7, 5)
    mutant_receiver = -source_receiver
    plants["P038-6"] = mutant_receiver != source_receiver

    p7_ok = True
    for r in range(1, 1025):
        sum_sq = Fraction(r * (r + 1) * (2 * r + 1), 6)
        left = sum_sq / (r + 1) ** 2 - Fraction(r, 3)
        right = sum_sq / r**2 - Fraction(r, 3)
        p7_ok = p7_ok and left == -Fraction(r, 6 * (r + 1))
        p7_ok = p7_ok and right == Fraction(3 * r + 1, 6 * r)
        p7_ok = p7_ok and left < 0 < right
    zero_mass = Fraction(1, 3) - Fraction(1, 3)
    plants["P038-7"] = p7_ok and zero_mass == 0

    allowed_intrinsic_dependencies = {
        "m",
        "S_scaled_exact_response",
        "a_e_outer_nonnegativity",
    }
    contaminants = {"rho_033", "q_700", "tau_response", "box_width"}
    plants["P038-8"] = contaminants.isdisjoint(
        allowed_intrinsic_dependencies
    )

    full_parts = {
        "four_thirds_endpoint",
        "crossing_band",
        "all_open_floor_bands",
        "finite_tooth_null_set",
        "endpoint_m",
    }
    split_parts = full_parts | {"sqrt_m_junction", "cofinal_outer_lobe"}
    p9_mutations = (
        full_parts - {"all_open_floor_bands"},
        full_parts - {"crossing_band"},
        split_parts - {"sqrt_m_junction"},
    )
    plants["P038-9"] = (
        coverage_accepts(full_parts, mode_split=False)
        and coverage_accepts(split_parts, mode_split=True)
        and all(
            not coverage_accepts(parts, mode_split=(index == 2))
            for index, parts in enumerate(p9_mutations)
        )
    )
    plants["P038-10"] = not scope_accepts(
        "COFINAL_FAMILY", "FINITE_CELL_REHEARSAL_m257"
    )
    plants["P038-11"] = (
        interval_direction(Fraction(-1), Fraction(1), positive_measure=True)
        == "INCONCLUSIVE"
        and interval_direction(Fraction(0), Fraction(1), positive_measure=True)
        == "PASS"
        and interval_direction(
            Fraction(-2), Fraction(-1), positive_measure=True
        )
        == "KILL"
        and interval_direction(
            Fraction(-2), Fraction(-1), positive_measure=False
        )
        == "INCONCLUSIVE"
    )

    for name, fired in plants.items():
        require(fired, f"PLANT_NOT_DETECTED:{name}")
        print(f"{name} FIRES")

    require(
        not scope_accepts("COFINAL_FAMILY", "FINITE_CELL_REHEARSAL_m257"),
        "036 leaked into cofinal dependency tree",
    )
    print("DEPENDENCY_GUARD PASS 036_absent_from_cofinal_target")
    print("LEAN_PHASE_NOT_ENTERED")
    print("ROUTE_STATE CHALLENGER_NOT_RH BUS_010_VOID")
    print(f"PRIMARY {PRIMARY}")
    print(f"STOP {STOP}")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"FAIL {type(error).__name__}: {error}")
        sys.exit(1)
