#!/usr/bin/env python3
"""Independent stdlib-only checker for RouteB.033.

This checker does not import the generator, Arb, python-flint, or the frozen
RouteB.030 implementation.  It validates the proof-carrying exact envelope
records, full-window coverage, source locks, all-sigma formula, outward
C_lambda construction, separate tooth ledger, and plants P1--P11.
"""

from __future__ import annotations

import copy
import csv
import hashlib
import json
import math
import re
import sys
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


sys.set_int_max_str_digits(300_000)

HERE = Path(__file__).resolve().parent
CERTIFICATE = HERE / "FULL_WINDOW_POSITIVE_PART_CERT.json"
BAND_CSV = HERE / "FULL_WINDOW_BAND_PROFILE.csv"
TOOTH_CSV = HERE / "FULL_WINDOW_TOOTH_LEDGER.csv"
CERT_030 = HERE / "COUPLED_FULL_SUM_RESPONSE_CERT.json"
CERT_031 = HERE / "PRIORITY_BAND_POSITIVE_PART_CERT.json"
GENERATOR = HERE / "full_window_positive_part_certificate.py"
DIRECTIVE = HERE / "proshka" / "PROSHKA_033_DIRECTIVE_2026-07-29.md"
STATE = HERE / "STATE.json"
BUS = (
    HERE.parent
    / "routeB_twolevel_spectral_ladder"
    / "bus"
)

M = 257
FULL_BANDS = tuple(range(17, 257))
TEETH = tuple(range(17, 258))
TAU = Fraction(1, 2**512)
PROOF_KIND = "FROZEN_030_EXACT_RATIONAL_BERNSTEIN"
SUCCESS = "FULL_WINDOW_POSITIVE_PART_BUDGET_PROVED"
BACKEND_GAP = "FULL_WINDOW_COUPLED_RESPONSE_BACKEND_GAP"
COVERAGE_GAP = "FULL_WINDOW_COVERAGE_GAP"
ENDPOINT_GAP = "FULL_WINDOW_PARTIAL_ENDPOINT_GAP"
SOURCE_GAP = "FULL_WINDOW_SOURCE_LOCK_MISMATCH"
PRIMARY_CODES = {
    SUCCESS,
    BACKEND_GAP,
    COVERAGE_GAP,
    ENDPOINT_GAP,
    SOURCE_GAP,
}

EXPECTED_GENERATOR_SHA256 = (
    "53da243d64242ebe49390be8a3d66536ebd827cdc98d4587d64326cbabc9c627"
)
EXPECTED_DIRECTIVE_SHA256 = (
    "e1a799bc07579952c47a7f8eb499f8e0d67d8b673741cd0ea6301b919cacacc5"
)
EXPECTED_030_SHA256 = (
    "2e31e67ba9cc9aed78bfed9ed20d052c1917b508958ddff077124e2cf95989da"
)
EXPECTED_031_SHA256 = (
    "86191e9eb8772dd013dbeb7347c1484b910109dbe5a4a2b24562e43211b937c9"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


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


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def proof_digest(
    backend_sha: str, kind: str, r: int, lower: Fraction, upper: Fraction
) -> str:
    return sha256_text(
        "|".join(
            (
                backend_sha,
                PROOF_KIND,
                kind,
                str(r),
                fraction_text(lower),
                fraction_text(upper),
            )
        )
    )


def payload_hash(rows: list[dict[str, Any]]) -> str:
    return sha256_text(
        json.dumps(rows, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    )


def arb_ball_to_interval(text: str) -> tuple[Fraction, Fraction]:
    match = re.fullmatch(r"\[([^ ]+) \+/- ([^\]]+)\]", text)
    require(match is not None, "unsupported Arb source ball")
    midpoint = Fraction(Decimal(match.group(1)))
    radius = Fraction(Decimal(match.group(2)))
    return midpoint - radius, midpoint + radius


def sqrt_fraction_interval(
    value: Fraction, bits: int = 512
) -> tuple[Fraction, Fraction]:
    require(value >= 0, "negative square-root input")
    scale = 1 << bits
    numerator = value.numerator * scale * scale
    denominator = value.denominator
    lower_integer = math.isqrt(numerator // denominator)
    while (
        (lower_integer + 1) * (lower_integer + 1) * denominator
        <= numerator
    ):
        lower_integer += 1
    while lower_integer * lower_integer * denominator > numerator:
        lower_integer -= 1
    lower = Fraction(lower_integer, scale)
    if lower * lower == value:
        return lower, lower
    return lower, Fraction(lower_integer + 1, scale)


def fourth_root_257_interval(bits: int = 256) -> tuple[Fraction, Fraction]:
    scale = 1 << bits
    target = M * scale**4
    lower_integer = math.isqrt(math.isqrt(target))
    while (lower_integer + 1) ** 4 <= target:
        lower_integer += 1
    while lower_integer**4 > target:
        lower_integer -= 1
    return (
        Fraction(lower_integer, scale),
        Fraction(lower_integer + 1, scale),
    )


def validate_endpoint_guard(record: dict[str, Any]) -> bool:
    try:
        if record["kind"] != (
            "rational_outer_endpoint_with_integer_square_proof"
        ):
            return False
        z_plus = read_rat(record["z16_plus"])
        numerator = z_plus.numerator
        denominator = z_plus.denominator
        square_gap = M * numerator * numerator - denominator * denominator
        upper_gap = denominator - 16 * numerator
        return (
            square_gap >= 0
            and upper_gap > 0
            and record["sqrt_guard_integer_gap"] == str(square_gap)
            and record["strict_below_one_sixteenth_integer_gap"]
            == str(upper_gap)
            and record["guard_pass"]
        )
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False


def validate_provenance(
    record: dict[str, Any],
    backend_sha: str,
    kind: str,
    r: int,
    lower: Fraction,
    upper: Fraction,
) -> bool:
    return (
        record.get("proof_kind") == PROOF_KIND
        and record.get("backend_proof_digest")
        == proof_digest(backend_sha, kind, r, lower, upper)
    )


def validate_band_record(
    record: dict[str, Any],
    backend_sha: str,
    global_uncertainty: Fraction,
    global_remainder: Fraction,
) -> bool:
    try:
        r = int(record["r"])
        partial = r == 16
        kind = "partial_r16" if partial else "full_rational_band"
        certified_lower, certified_upper = read_interval(
            record["certified_envelope_domain"]
        )
        if not certified_lower < certified_upper:
            return False
        if partial:
            if certified_lower != Fraction(1, 17):
                return False
        elif (
            certified_lower != Fraction(1, r + 1)
            or certified_upper != Fraction(1, r)
        ):
            return False
        center_lower = read_rat(record["center_bernstein_minimum"]["value"])
        center_upper = read_rat(record["center_bernstein_maximum"]["value"])
        uncertainty = read_rat(
            record["response_weighted_coefficient_uncertainty"]
        )
        remainder = read_rat(record["infinite_response_remainder"])
        radius = read_rat(record["outward_radius"])
        lower = read_rat(record["lower_full_sum"])
        upper = read_rat(record["upper_full_sum"])
        epsilon = read_rat(record["epsilon"])
        return (
            record["band_kind"] == kind
            and 0
            <= int(record["center_bernstein_minimum"]["index"])
            <= 1400
            and 0
            <= int(record["center_bernstein_maximum"]["index"])
            <= 1400
            and center_lower <= center_upper
            and uncertainty == global_uncertainty
            and remainder == global_remainder
            and radius == uncertainty + remainder
            and lower == center_lower - radius
            and upper == center_upper + radius
            and epsilon == max(Fraction(0), -lower)
            and record["contains_zero"] == (lower <= 0 <= upper)
            and record["coverage_complete"]
            and validate_provenance(
                record,
                backend_sha,
                kind,
                r,
                certified_lower,
                certified_upper,
            )
        )
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False


def coverage_ok(bands: list[dict[str, Any]]) -> bool:
    if len(bands) != 241:
        return False
    if [int(record["r"]) for record in bands] != list(
        range(256, 15, -1)
    ):
        return False
    by_r = {int(record["r"]): record for record in bands}
    if set(by_r) != set(range(16, 257)):
        return False
    for r in FULL_BANDS:
        if by_r[r]["integration_domain"] != interval_record(
            Fraction(1, r + 1), Fraction(1, r)
        ):
            return False
    return by_r[16]["integration_domain"] == {
        "lower": rat(Fraction(1, 17)),
        "upper": {
            "kind": "positive_root",
            "relation": "257*z^2=1",
            "name": "1/sqrt(257)",
        },
    }


def validate_tooth_record(
    record: dict[str, Any],
    backend_sha: str,
    global_uncertainty: Fraction,
    global_remainder: Fraction,
) -> bool:
    try:
        r = int(record["r"])
        z = read_rat(record["z"])
        center = read_rat(record["center"])
        uncertainty = read_rat(
            record["response_weighted_coefficient_uncertainty"]
        )
        remainder = read_rat(record["infinite_response_remainder"])
        radius = read_rat(record["outward_radius"])
        lower = read_rat(record["lower_full_sum"])
        upper = read_rat(record["upper_full_sum"])
        return (
            z == Fraction(1, r)
            and uncertainty == global_uncertainty
            and remainder == global_remainder
            and radius == uncertainty + remainder
            and lower == center - radius
            and upper == center + radius
            and record["coverage_complete"]
            and record["nonnegative_proved"] == (lower >= 0)
            and record["strictly_negative_proved"] == (upper < 0)
            and record["contains_zero"] == (lower <= 0 <= upper)
            and validate_provenance(
                record,
                backend_sha,
                "star_tooth",
                r,
                z,
                z,
            )
        )
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False


def recompute_tooth_flag(teeth: list[dict[str, Any]]) -> str:
    if all(record["nonnegative_proved"] for record in teeth):
        return "ALL_WINDOW_TEETH_NONNEGATIVE_PROVED"
    if any(record["strictly_negative_proved"] for record in teeth):
        return "POINTWISE_DUALTHETA_KILLED_AT_TOOTH"
    return "TOOTH_SIGN_INCONCLUSIVE"


def validate_c_lambda(record: dict[str, Any]) -> bool:
    try:
        j0_lower, j0_upper = arb_ball_to_interval(
            record["source_J0_arb_ball"]
        )
        j4_lower, j4_upper = arb_ball_to_interval(
            record["source_J4_arb_ball"]
        )
        if record["source_J0_rational_interval"] != interval_record(
            j0_lower, j0_upper
        ):
            return False
        if record["source_J4_rational_interval"] != interval_record(
            j4_lower, j4_upper
        ):
            return False
        fourth_lower, fourth_upper = fourth_root_257_interval()
        if record["fourth_root_257_rational_interval"] != interval_record(
            fourth_lower, fourth_upper
        ):
            return False
        d_lower, _ = sqrt_fraction_interval(
            j0_lower * j0_lower + j4_lower * j4_lower
        )
        _, d_upper = sqrt_fraction_interval(
            j0_upper * j0_upper + j4_upper * j4_upper
        )
        expected_lower = fourth_lower * j0_lower * j4_lower / d_upper
        expected_upper = fourth_upper * j0_upper * j4_upper / d_lower
        actual_lower, actual_upper = read_interval(record["outward_interval"])
        return (
            actual_lower == expected_lower
            and actual_upper == expected_upper
            and 0 < actual_lower <= actual_upper
            and not record["saved_decimal_C_used_as_exact_input"]
        )
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False


def decimal_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def budget_over_c_decimal(
    epsilon: dict[int, Fraction], sigma: Decimal
) -> Decimal:
    with localcontext() as context:
        context.prec = 120
        half = Decimal(1) / 2
        exponent = sigma - half
        lam = Decimal(M).sqrt()
        bracket = decimal_fraction(epsilon[16]) * (
            lam**exponent - Decimal(17) ** exponent
        )
        for r in FULL_BANDS:
            bracket += decimal_fraction(epsilon[r]) * (
                Decimal(r) ** exponent - Decimal(r + 1) ** exponent
            )
        return lam ** (-sigma - half) * bracket / (half - sigma)


def check_budget_samples(
    theorem: dict[str, Any], epsilon: dict[int, Fraction]
) -> None:
    c_lower, c_upper = read_interval(
        theorem["C_lambda"]["outward_interval"]
    )
    for row in theorem["displayed_outward_samples"]:
        sigma = Decimal(row["sigma"])
        require(Decimal(0) <= sigma < Decimal("0.5"), "sample sigma range")
        over_c = budget_over_c_decimal(epsilon, sigma)
        stored_over_c = row["Delta_full_over_C_lambda"]
        require(
            Decimal(stored_over_c["lower"])
            <= over_c
            <= Decimal(stored_over_c["upper"]),
            f"Delta/C outward sample mismatch sigma={sigma}",
        )
        require(
            Decimal(row["Delta_full"]["lower"])
            <= over_c * decimal_fraction(c_lower),
            f"Delta lower outward sample mismatch sigma={sigma}",
        )
        require(
            over_c * decimal_fraction(c_upper)
            <= Decimal(row["Delta_full"]["upper"]),
            f"Delta upper outward sample mismatch sigma={sigma}",
        )


def read_band_csv() -> list[dict[str, str]]:
    with BAND_CSV.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def read_tooth_csv() -> list[dict[str, str]]:
    with TOOTH_CSV.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def check_band_csv(bands: list[dict[str, Any]]) -> None:
    rows = read_band_csv()
    require(len(rows) == 241, "band CSV row count")
    for sequence, (row, record) in enumerate(zip(rows, bands, strict=True)):
        certified_lower, certified_upper = read_interval(
            record["certified_envelope_domain"]
        )
        lower = read_rat(record["lower_full_sum"])
        upper = read_rat(record["upper_full_sum"])
        epsilon = read_rat(record["epsilon"])
        require(int(row["sequence"]) == sequence, "band CSV sequence")
        require(int(row["r"]) == int(record["r"]), "band CSV r")
        require(row["band_kind"] == record["band_kind"], "band CSV kind")
        require(
            Fraction(
                int(row["certified_lower_num"]),
                int(row["certified_lower_den"]),
            )
            == certified_lower,
            "band CSV certified lower",
        )
        require(
            Fraction(
                int(row["certified_upper_num"]),
                int(row["certified_upper_den"]),
            )
            == certified_upper,
            "band CSV certified upper",
        )
        require(
            Fraction(int(row["lower_full_num"]), int(row["lower_full_den"]))
            == lower,
            "band CSV lower",
        )
        require(
            Fraction(int(row["upper_full_num"]), int(row["upper_full_den"]))
            == upper,
            "band CSV upper",
        )
        require(
            Fraction(int(row["epsilon_num"]), int(row["epsilon_den"]))
            == epsilon,
            "band CSV epsilon",
        )
        require(row["proof_kind"] == PROOF_KIND, "band CSV proof kind")
        require(
            row["backend_proof_digest"] == record["backend_proof_digest"],
            "band CSV proof digest",
        )


def check_tooth_csv(teeth: list[dict[str, Any]]) -> None:
    rows = read_tooth_csv()
    require(len(rows) == 241, "tooth CSV row count")
    for row, record in zip(rows, teeth, strict=True):
        lower = read_rat(record["lower_full_sum"])
        upper = read_rat(record["upper_full_sum"])
        require(int(row["r"]) == int(record["r"]), "tooth CSV r")
        require(
            Fraction(int(row["z_num"]), int(row["z_den"]))
            == Fraction(1, int(record["r"])),
            "tooth CSV z",
        )
        require(
            Fraction(int(row["lower_full_num"]), int(row["lower_full_den"]))
            == lower,
            "tooth CSV lower",
        )
        require(
            Fraction(int(row["upper_full_num"]), int(row["upper_full_den"]))
            == upper,
            "tooth CSV upper",
        )
        require(row["proof_kind"] == PROOF_KIND, "tooth CSV proof kind")
        require(
            row["backend_proof_digest"] == record["backend_proof_digest"],
            "tooth CSV proof digest",
        )


def main() -> None:
    certificate = json.loads(CERTIFICATE.read_text(encoding="utf-8"))
    cert030 = json.loads(CERT_030.read_text(encoding="utf-8"))

    require(
        sha256(GENERATOR) == EXPECTED_GENERATOR_SHA256,
        "033 generator source drift",
    )
    require(
        sha256(DIRECTIVE) == EXPECTED_DIRECTIVE_SHA256,
        "033 directive source drift",
    )
    require(sha256(CERT_030) == EXPECTED_030_SHA256, "030 certificate drift")
    require(sha256(CERT_031) == EXPECTED_031_SHA256, "031 certificate drift")
    require(
        certificate["schema"] == "route_b_full_window_positive_part.v1",
        "wrong schema",
    )
    for relative, expected in certificate["source_locks"].items():
        require(
            sha256(HERE / relative) == expected,
            f"source drift: {relative}",
        )
    require(
        certificate["source_locks"]["STATE.json"] == sha256(STATE),
        "STATE source lock drift",
    )

    primary = certificate["primary_verdict"]
    require(primary in PRIMARY_CODES, "unknown primary verdict")
    require(certificate["primary_code_count"] == 1, "primary code count")
    require(
        sum(
            value == primary
            for key, value in certificate.items()
            if key == "primary_verdict"
        )
        == 1,
        "primary verdict field multiplicity",
    )
    require(
        certificate["status"] == "CHALLENGER / NOT_RH",
        "epistemic status",
    )

    backend = certificate["frozen_backend"]
    backend_sha = backend["certificate_sha256"]
    require(backend_sha == EXPECTED_030_SHA256, "backend source lock")
    require(backend["core_q"] == 440, "core_q lock")
    require(backend["tail_q"] == 700, "tail_q lock")
    require(read_rat(backend["tau_response"]) == TAU, "tau lock")
    require(
        read_interval(backend["terminal_cone"])
        == (Fraction(0), Fraction(1, 2)),
        "terminal cone lock",
    )
    require(backend["canonical_phase"] == "+", "phase lock")
    require(
        read_interval(backend["delta_0"])
        == (Fraction(0), Fraction(0)),
        "delta_0 lock",
    )
    require(
        backend["whole_response_polynomial_degree"] == 1400,
        "whole response degree",
    )
    uncertainty = read_rat(
        backend["response_weighted_coefficient_uncertainty"]
    )
    remainder = read_rat(backend["infinite_response_remainder"])
    require(uncertainty > 0, "coefficient uncertainty vanished")
    require(remainder > 0, "response remainder vanished")
    require(
        backend["backend_below_tau"] == (remainder < TAU),
        "backend tau status",
    )
    require(not backend["old_r_times_epsilon_used"], "old tail used")
    require(not backend["new_depth_used"], "new depth used")
    require(
        not backend["new_precision_ladder_used"],
        "new precision ladder used",
    )

    bands = certificate["bands"]
    require(
        all(
            validate_band_record(
                record, backend_sha, uncertainty, remainder
            )
            for record in bands
        ),
        "band proof-carrying record failed",
    )
    complete = coverage_ok(bands)
    require(complete, "full-window coverage")
    require(validate_endpoint_guard(certificate["partial_endpoint_guard"]),
            "partial endpoint guard")

    by_r = {int(record["r"]): record for record in bands}
    bands030 = {int(record["r"]): record for record in cert030["bands"]}
    priority_regression = True
    for r in (255, 256):
        priority_regression &= (
            by_r[r]["lower_full_sum"] == bands030[r]["lower_full_sum"]
            and by_r[r]["upper_full_sum"] == bands030[r]["upper_full_sum"]
            and read_rat(by_r[r]["epsilon"])
            == max(Fraction(0), -read_rat(bands030[r]["lower_full_sum"]))
        )
    require(priority_regression, "priority regression P1")
    check_band_csv(bands)
    require(
        sha256(BAND_CSV) == certificate["artifacts"]["band_csv_sha256"],
        "band CSV hash",
    )
    require(
        payload_hash(bands)
        == certificate["band_profile_summary"]["band_payload_sha256"],
        "band payload hash",
    )

    epsilon = {
        int(record["r"]): read_rat(record["epsilon"]) for record in bands
    }
    positive_epsilon_bands = sorted(r for r, value in epsilon.items() if value)
    summary = certificate["band_profile_summary"]
    require(summary["coverage_complete"], "band summary coverage")
    require(
        summary["priority_regression_exact"],
        "band summary priority regression",
    )
    require(
        summary["positive_epsilon_bands"] == positive_epsilon_bands,
        "positive epsilon profile",
    )
    require(
        summary["positive_epsilon_band_count"]
        == len(positive_epsilon_bands),
        "positive epsilon count",
    )

    theorem = certificate["positive_part_theorem"]
    require(
        theorem["quantifier"]
        == "for every real sigma with 0 <= sigma < 1/2",
        "all-sigma quantifier",
    )
    require(
        theorem["measure_change"] == "du/u=dz/z",
        "Jacobian statement",
    )
    require(
        theorem["epsilon_definition"] == "epsilon_r=max(0,-L_r)",
        "epsilon theorem",
    )
    require(
        theorem["Delta_full_over_C_lambda_formula"]
        == (
            "lambda^(-sigma-1/2)/(1/2-sigma)*("
            "epsilon_16*(lambda^(sigma-1/2)-17^(sigma-1/2))"
            "+sum_(r=17)^256 epsilon_r*"
            "(r^(sigma-1/2)-(r+1)^(sigma-1/2)))"
        ),
        "Delta/C formula",
    )
    require(
        len(theorem["all_sigma_proof"]) == 5,
        "all-sigma proof ledger",
    )
    require(
        theorem["teeth_excluded_as_measure_zero"],
        "teeth entered Lebesgue budget",
    )
    require(validate_c_lambda(theorem["C_lambda"]), "C_lambda interval")
    check_budget_samples(theorem, epsilon)

    teeth = certificate["teeth"]
    require(
        [int(record["r"]) for record in teeth] == list(range(257, 16, -1)),
        "tooth order/coverage",
    )
    require(
        all(
            validate_tooth_record(
                record, backend_sha, uncertainty, remainder
            )
            for record in teeth
        ),
        "tooth proof-carrying record failed",
    )
    check_tooth_csv(teeth)
    require(
        sha256(TOOTH_CSV) == certificate["artifacts"]["tooth_csv_sha256"],
        "tooth CSV hash",
    )
    require(
        payload_hash(teeth)
        == certificate["tooth_ledger_summary"]["tooth_payload_sha256"],
        "tooth payload hash",
    )
    flag = recompute_tooth_flag(teeth)
    require(certificate["secondary_flags"] == [flag], "secondary flag")
    tooth_summary = certificate["tooth_ledger_summary"]
    require(tooth_summary["secondary_flag"] == flag, "tooth summary flag")
    require(
        tooth_summary["nonnegative_proved"]
        == sum(record["nonnegative_proved"] for record in teeth),
        "tooth nonnegative count",
    )
    require(
        tooth_summary["strictly_negative_proved"]
        == sum(record["strictly_negative_proved"] for record in teeth),
        "tooth negative count",
    )
    require(
        tooth_summary["zero_compatible"]
        == sum(record["contains_zero"] for record in teeth),
        "tooth zero-compatible count",
    )
    require(
        tooth_summary["excluded_from_Lebesgue_budget"],
        "tooth budget separation",
    )

    plants = certificate["plants"]
    require(
        all(plants[f"P{i}_{name}"]["status"] == "FIRES"
            for i, name in (
                (1, "priority_regression"),
                (2, "missing_band"),
                (3, "junction_mutation"),
                (4, "irrational_endpoint"),
                (5, "independent_tail_regression"),
                (6, "terminal_ratio_zero"),
                (7, "phase"),
                (8, "jacobian"),
                (9, "diagnostic_not_proof"),
                (10, "tooth_mutation"),
                (11, "coefficient_centers_as_exact"),
            )),
        "plant status",
    )

    # P1: exact 030/031 priority replay.
    require(
        plants["P1_priority_regression"]["exact_match_r255_r256"],
        "P1 did not fire",
    )

    # P2: remove one immutable band record.
    missing_mutation = bands[1:]
    require(not coverage_ok(missing_mutation), "P2 missing band not detected")

    # P3: mutate a true rational junction to create a gap, then an overlap.
    gap_mutation = copy.deepcopy(bands)
    gap_record = next(record for record in gap_mutation if record["r"] == 100)
    gap_record["integration_domain"]["lower"] = rat(Fraction(1, 100))
    require(not coverage_ok(gap_mutation), "P3 gap not detected")
    overlap_mutation = copy.deepcopy(bands)
    overlap_record = next(
        record for record in overlap_mutation if record["r"] == 100
    )
    overlap_record["integration_domain"]["lower"] = rat(Fraction(1, 102))
    require(not coverage_ok(overlap_mutation), "P3 overlap not detected")

    # P4: 1/16 and a decimal tag are not valid endpoint proofs.
    endpoint_one_sixteenth = copy.deepcopy(
        certificate["partial_endpoint_guard"]
    )
    endpoint_one_sixteenth["z16_plus"] = rat(Fraction(1, 16))
    require(
        not validate_endpoint_guard(endpoint_one_sixteenth),
        "P4 accepted 1/16",
    )
    endpoint_decimal = {"kind": "decimal", "value": "0.062378286"}
    require(
        not validate_endpoint_guard(endpoint_decimal),
        "P4 accepted decimal endpoint",
    )

    # P5: the old independent tail is materially wider and diagnostic only.
    p5 = plants["P5_independent_tail_regression"]
    new_radius = read_rat(p5["new_outward_radius"])
    require(new_radius == uncertainty + remainder, "P5 new radius")
    for r in (255, 256):
        old_radius = read_rat(p5["old_band_tail_budget"][str(r)])
        require(old_radius > new_radius * 10**6, f"P5 did not fire r={r}")
    require(p5["diagnostic_only"], "P5 entered verdict")

    # P6: zeroing the live terminal cone removes a positive component.
    p6 = plants["P6_terminal_ratio_zero"]
    require(
        read_rat(p6["live_terminal_response_width"]) > 0,
        "P6 live terminal width",
    )
    require(
        read_rat(p6["mutated_terminal_response_width"]) == 0,
        "P6 zero mutation",
    )
    require(p6["enclosure_changes"], "P6 enclosure mutation")

    # P7: phase flip breaks delta_0 and priority regression.
    p7 = plants["P7_phase"]
    require(read_rat(p7["baseline_delta_0"]) == 0, "P7 baseline")
    require(read_rat(p7["mutated_delta_0"]) == -1, "P7 mutation")
    require(
        read_rat(p7["priority_constant_shift_r256"]) != 0,
        "P7 priority shift",
    )
    require(p7["priority_regression_breaks"], "P7 regression")

    # P8: both Jacobian and lambda power controls are exact and distinct.
    p8 = plants["P8_jacobian"]
    require(read_rat(p8["with_du_over_u"]) == 1, "P8 Jacobian")
    require(
        read_rat(p8["without_du_over_u"]) == Fraction(7, 12),
        "P8 dropped Jacobian",
    )
    require(
        read_rat(p8["correct_lambda_power"]) == Fraction(1, 2),
        "P8 lambda power",
    )
    require(
        read_rat(p8["dropped_lambda_power"]) == 1,
        "P8 dropped lambda power",
    )

    # P9: a diagnostic string without exact-backend provenance is rejected.
    fake = copy.deepcopy(by_r[100])
    fake["proof_kind"] = "022_DIAGNOSTIC_STRING"
    fake["backend_proof_digest"] = "not-an-exact-envelope"
    require(
        not validate_band_record(fake, backend_sha, uncertainty, remainder),
        "P9 diagnostic accepted as proof",
    )

    # P10: tooth mutation changes only the tooth payload.
    mutated_teeth = copy.deepcopy(teeth)
    mutated_teeth[0]["center"] = rat(
        read_rat(mutated_teeth[0]["center"]) + 1
    )
    require(
        payload_hash(mutated_teeth) != payload_hash(teeth),
        "P10 tooth ledger unchanged",
    )
    require(
        payload_hash(bands)
        == plants["P10_tooth_mutation"]["band_payload_sha256"],
        "P10 band payload changed",
    )
    require(
        plants["P10_tooth_mutation"]["lebesgue_budget_unchanged"],
        "P10 Lebesgue budget changed",
    )

    # P11: deleting coefficient-box uncertainty invalidates every record.
    p11 = plants["P11_coefficient_centers_as_exact"]
    require(read_rat(p11["coefficient_uncertainty"]) > 0, "P11 baseline")
    zero_uncertainty_record = copy.deepcopy(by_r[100])
    zero_uncertainty_record[
        "response_weighted_coefficient_uncertainty"
    ] = rat(Fraction(0))
    require(
        not validate_band_record(
            zero_uncertainty_record, backend_sha, uncertainty, remainder
        ),
        "P11 accepted exact centers",
    )

    guards = certificate["guards"]
    require(not guards["checker_imports_generator"], "generator import guard")
    require(not guards["checker_imports_arb"], "Arb import guard")
    require(not guards["checker_imports_flint"], "flint import guard")
    require(
        not guards["coefficient_centers_treated_as_exact"],
        "coefficient-box guard",
    )
    require(
        not guards["old_independent_tail_used_for_verdict"],
        "old-tail guard",
    )
    require(
        not guards["teeth_included_in_lebesgue_budget"],
        "tooth measure guard",
    )
    require(
        not guards["saved_decimal_C_used_as_exact_input"],
        "C_lambda decimal guard",
    )
    require(not guards["state_touched"], "STATE guard")
    require(not guards["bus_010_created"], "Bus 010 guard")
    require(
        not list(BUS.glob("010_*.goal.md")),
        "physical Bus 010 unexpectedly exists",
    )

    recomputed_primary = (
        SOURCE_GAP
        if not priority_regression
        else ENDPOINT_GAP
        if not validate_endpoint_guard(certificate["partial_endpoint_guard"])
        else COVERAGE_GAP
        if not complete
        else BACKEND_GAP
        if not backend["backend_below_tau"]
        else SUCCESS
    )
    require(primary == recomputed_primary, "primary verdict recomputation")

    print(f"PASS {primary}")
    print(
        "P1 PASS P2 PASS P3 PASS P4 PASS P5 PASS P6 PASS "
        "P7 PASS P8 PASS P9 PASS P10 PASS P11 PASS"
    )
    print(flag)


if __name__ == "__main__":
    main()
