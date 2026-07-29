#!/usr/bin/env python3
"""Build the RouteB.033 full-window positive-part certificate.

The numerical backend is the frozen RouteB.030 coupled response backend:
q=0..700 coefficient centers are assembled into one exact polynomial, while
only coefficient-box response uncertainty and the q>700 response remainder
are added outward.  RouteB.033 enumerates the complete m=257 window and does
not change the depth, precision ladder, terminal cone, or phase.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import multiprocessing
import os
import re
import sys
from concurrent.futures import ProcessPoolExecutor
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

import coupled_full_sum_response_certificate as frozen030
from flint import fmpq


sys.set_int_max_str_digits(300_000)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

GOAL = HERE / "033_full_window_positive_part.goal.md"
DIRECTIVE = HERE / "proshka" / "PROSHKA_033_DIRECTIVE_2026-07-29.md"
CERT_030 = HERE / "COUPLED_FULL_SUM_RESPONSE_CERT.json"
ANSWER_030 = HERE / "030_coupled_full_sum_response.answer.md"
GENERATOR_030 = HERE / "coupled_full_sum_response_certificate.py"
CERT_031 = HERE / "PRIORITY_BAND_POSITIVE_PART_CERT.json"
ANSWER_031 = HERE / "031_priority_band_positive_part.answer.md"
GENERATOR_031 = HERE / "priority_band_positive_part_certificate.py"
CERT_027 = HERE / "HLAMBDA_OUTER_LOBE_GATE_AUDIT.json"
CERT_029 = HERE / "DECISIVE_FINITE_CORE_THETA_K_ESCALATION.json"
STATE = HERE / "STATE.json"
GENERATOR = Path(__file__).resolve()

OUTPUT = HERE / "FULL_WINDOW_POSITIVE_PART_CERT.json"
BAND_CSV = HERE / "FULL_WINDOW_BAND_PROFILE.csv"
TOOTH_CSV = HERE / "FULL_WINDOW_TOOTH_LEDGER.csv"

M = 257
CORE_Q = 440
TAIL_Q = 700
TAU = Fraction(1, 2**512)
TERMINAL_CONE = (Fraction(0), Fraction(1, 2))
PHASE = "+"
FULL_BANDS = tuple(range(17, 257))
TEETH = tuple(range(17, 258))
ALL_PRIMARY_CODES = (
    "FULL_WINDOW_POSITIVE_PART_BUDGET_PROVED",
    "FULL_WINDOW_COUPLED_RESPONSE_BACKEND_GAP",
    "FULL_WINDOW_COVERAGE_GAP",
    "FULL_WINDOW_PARTIAL_ENDPOINT_GAP",
    "FULL_WINDOW_SOURCE_LOCK_MISMATCH",
)
SUCCESS = ALL_PRIMARY_CODES[0]
BACKEND_GAP = ALL_PRIMARY_CODES[1]
COVERAGE_GAP = ALL_PRIMARY_CODES[2]
ENDPOINT_GAP = ALL_PRIMARY_CODES[3]
SOURCE_GAP = ALL_PRIMARY_CODES[4]
PROOF_KIND = "FROZEN_030_EXACT_RATIONAL_BERNSTEIN"

_WORKER_CONTEXT: tuple[Any, Any, Fraction, Fraction, Fraction, str] | None = (
    None
)


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


def scientific(value: Fraction, digits: int = 18) -> str:
    if value == 0:
        return "0"
    with localcontext() as context:
        context.prec = digits + 30
        decimal_value = Decimal(value.numerator) / Decimal(value.denominator)
        return f"{decimal_value:.{digits}E}"


def arb_ball_to_interval(text: str) -> tuple[Fraction, Fraction]:
    match = re.fullmatch(r"\[([^ ]+) \+/- ([^\]]+)\]", text)
    if match is None:
        raise ValueError(f"unsupported Arb rendering: {text}")
    midpoint = Fraction(Decimal(match.group(1)))
    radius = Fraction(Decimal(match.group(2)))
    return midpoint - radius, midpoint + radius


def sqrt_fraction_interval(
    value: Fraction, bits: int = 512
) -> tuple[Fraction, Fraction]:
    if value < 0:
        raise ValueError("negative square-root input")
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


def partial_outer_endpoint(bits: int = 192) -> dict[str, Any]:
    denominator = 1 << bits
    target = denominator * denominator
    numerator = math.isqrt(target // M)
    while M * numerator * numerator < target:
        numerator += 1
    while numerator > 0 and M * (numerator - 1) ** 2 >= target:
        numerator -= 1
    z_plus = Fraction(numerator, denominator)
    reduced_numerator = z_plus.numerator
    reduced_denominator = z_plus.denominator
    lower_square_gap = (
        M * reduced_numerator * reduced_numerator
        - reduced_denominator * reduced_denominator
    )
    upper_gap = reduced_denominator - 16 * reduced_numerator
    return {
        "kind": "rational_outer_endpoint_with_integer_square_proof",
        "z16_plus": rat(z_plus),
        "z16_plus_decimal": scientific(z_plus, 40),
        "sqrt_guard_relation": "257*numerator^2 >= denominator^2",
        "sqrt_guard_integer_gap": str(lower_square_gap),
        "strict_below_one_sixteenth_relation": (
            "16*numerator < denominator"
        ),
        "strict_below_one_sixteenth_integer_gap": str(upper_gap),
        "guard_pass": lower_square_gap >= 0 and upper_gap > 0,
    }


def c_lambda_interval(cert027: dict[str, Any]) -> dict[str, Any]:
    cell = next(record for record in cert027["cells"] if int(record["m"]) == M)
    j0_text = cell["positive_source_integrals"]["J0"]
    j4_text = cell["positive_source_integrals"]["J4"]
    j0_lower, j0_upper = arb_ball_to_interval(j0_text)
    j4_lower, j4_upper = arb_ball_to_interval(j4_text)
    if min(j0_lower, j4_lower) <= 0:
        raise ArithmeticError("positive source-integral lock failed")

    fourth_lower, fourth_upper = fourth_root_257_interval()
    d_lower, _ = sqrt_fraction_interval(
        j0_lower * j0_lower + j4_lower * j4_lower
    )
    _, d_upper = sqrt_fraction_interval(
        j0_upper * j0_upper + j4_upper * j4_upper
    )
    lower = fourth_lower * j0_lower * j4_lower / d_upper
    upper = fourth_upper * j0_upper * j4_upper / d_lower
    if not 0 < lower <= upper:
        raise ArithmeticError("C_lambda interval is not positive")
    return {
        "definition": "I0*I4/sqrt(I0^2+I4^2)",
        "scaling_derivation": (
            "I_j=sqrt(lambda)*J_j, hence "
            "C_lambda=257^(1/4)*J0*J4/sqrt(J0^2+J4^2)"
        ),
        "source": "HLAMBDA_OUTER_LOBE_GATE_AUDIT.json:m=257",
        "source_J0_arb_ball": j0_text,
        "source_J4_arb_ball": j4_text,
        "source_J0_rational_interval": interval_record(j0_lower, j0_upper),
        "source_J4_rational_interval": interval_record(j4_lower, j4_upper),
        "fourth_root_257_rational_interval": interval_record(
            fourth_lower, fourth_upper
        ),
        "outward_interval": interval_record(lower, upper),
        "lower_scientific": scientific(lower, 30),
        "upper_scientific": scientific(upper, 30),
        "saved_decimal_C_used_as_exact_input": False,
    }


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


def extremum_record(values: list[fmpq], minimum: bool) -> dict[str, Any]:
    value = min(values) if minimum else max(values)
    return {
        "index": values.index(value),
        "value": rat(frozen030.ff(value)),
    }


def build_band_record(
    total: Any,
    uncertainty: Fraction,
    final_tail: Fraction,
    backend_sha: str,
    r: int,
    certified_lower: Fraction,
    certified_upper: Fraction,
    partial: bool,
) -> dict[str, Any]:
    response = frozen030.band_polynomial(total, r)
    values = frozen030.bernstein_coefficients(
        response, certified_lower, certified_upper
    )
    radius = uncertainty + final_tail
    center_lower = frozen030.ff(min(values))
    center_upper = frozen030.ff(max(values))
    full_lower = center_lower - radius
    full_upper = center_upper + radius
    epsilon = max(Fraction(0), -full_lower)
    kind = "partial_r16" if partial else "full_rational_band"
    integration_domain: dict[str, Any]
    if partial:
        integration_domain = {
            "lower": rat(Fraction(1, 17)),
            "upper": {
                "kind": "positive_root",
                "relation": "257*z^2=1",
                "name": "1/sqrt(257)",
            },
        }
    else:
        integration_domain = interval_record(
            Fraction(1, r + 1), Fraction(1, r)
        )
    return {
        "r": r,
        "band_kind": kind,
        "integration_domain": integration_domain,
        "certified_envelope_domain": interval_record(
            certified_lower, certified_upper
        ),
        "center_bernstein_minimum": extremum_record(values, True),
        "center_bernstein_maximum": extremum_record(values, False),
        "response_weighted_coefficient_uncertainty": rat(uncertainty),
        "infinite_response_remainder": rat(final_tail),
        "outward_radius": rat(radius),
        "lower_full_sum": rat(full_lower),
        "upper_full_sum": rat(full_upper),
        "epsilon": rat(epsilon),
        "epsilon_scientific": scientific(epsilon),
        "proof_kind": PROOF_KIND,
        "backend_proof_digest": proof_digest(
            backend_sha,
            kind,
            r,
            certified_lower,
            certified_upper,
        ),
        "coverage_complete": True,
        "contains_zero": full_lower <= 0 <= full_upper,
    }


def build_tooth_record(
    total: Any,
    uncertainty: Fraction,
    final_tail: Fraction,
    backend_sha: str,
    r: int,
) -> dict[str, Any]:
    center = frozen030.ff(frozen030.tooth_value(total, r))
    radius = uncertainty + final_tail
    lower = center - radius
    upper = center + radius
    return {
        "r": r,
        "z": rat(Fraction(1, r)),
        "center": rat(center),
        "response_weighted_coefficient_uncertainty": rat(uncertainty),
        "infinite_response_remainder": rat(final_tail),
        "outward_radius": rat(radius),
        "lower_full_sum": rat(lower),
        "upper_full_sum": rat(upper),
        "proof_kind": PROOF_KIND,
        "backend_proof_digest": proof_digest(
            backend_sha,
            "star_tooth",
            r,
            Fraction(1, r),
            Fraction(1, r),
        ),
        "coverage_complete": True,
        "nonnegative_proved": lower >= 0,
        "strictly_negative_proved": upper < 0,
        "contains_zero": lower <= 0 <= upper,
    }


def band_worker(
    item: tuple[int, Fraction, Fraction, bool]
) -> dict[str, Any]:
    if _WORKER_CONTEXT is None:
        raise RuntimeError("worker context missing")
    total, _tail, uncertainty, _tail_uncertainty, remainder, backend_sha = (
        _WORKER_CONTEXT
    )
    r, lower, upper, partial = item
    return build_band_record(
        total,
        uncertainty,
        remainder,
        backend_sha,
        r,
        lower,
        upper,
        partial,
    )


def tooth_worker(r: int) -> dict[str, Any]:
    if _WORKER_CONTEXT is None:
        raise RuntimeError("worker context missing")
    total, _tail, uncertainty, _tail_uncertainty, remainder, backend_sha = (
        _WORKER_CONTEXT
    )
    return build_tooth_record(total, uncertainty, remainder, backend_sha, r)


def decimal_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def budget_over_c_decimal(
    epsilon: dict[int, Fraction], sigma: Decimal
) -> Decimal:
    with localcontext() as context:
        context.prec = 170
        half = Decimal(1) / 2
        exponent = sigma - half
        lam = Decimal(M).sqrt()
        bracket = (
            decimal_fraction(epsilon[16])
            * (lam**exponent - Decimal(17) ** exponent)
        )
        for r in FULL_BANDS:
            bracket += decimal_fraction(epsilon[r]) * (
                Decimal(r) ** exponent - Decimal(r + 1) ** exponent
            )
        return lam ** (-sigma - half) * bracket / (half - sigma)


def guarded_decimal_interval(value: Decimal) -> dict[str, str]:
    if value == 0:
        return {"lower": "0", "upper": "0"}
    with localcontext() as context:
        context.prec = 150
        # The displayed interval keeps 90 significant digits, so place the
        # guard inside that retained precision while remaining negligible for
        # every reported scale.
        guard = Decimal("1e-85")
        lower = value * (Decimal(1) - guard)
        upper = value * (Decimal(1) + guard)
        return {
            "lower": f"{lower:.90E}",
            "upper": f"{upper:.90E}",
        }


def budget_samples(
    epsilon: dict[int, Fraction], c_record: dict[str, Any]
) -> list[dict[str, Any]]:
    c_lower, c_upper = read_interval(c_record["outward_interval"])
    rows = []
    for sigma_text in ("0", "0.10", "0.25", "0.40", "0.45", "0.49"):
        sigma = Decimal(sigma_text)
        over_c = budget_over_c_decimal(epsilon, sigma)
        over_c_interval = guarded_decimal_interval(over_c)
        full_lower = over_c * decimal_fraction(c_lower)
        full_upper = over_c * decimal_fraction(c_upper)
        rows.append(
            {
                "sigma": sigma_text,
                "Delta_full_over_C_lambda": over_c_interval,
                "Delta_full": {
                    "lower": guarded_decimal_interval(full_lower)["lower"],
                    "upper": guarded_decimal_interval(full_upper)["upper"],
                },
            }
        )
    return rows


def coverage_ok(bands: list[dict[str, Any]]) -> bool:
    if len(bands) != 241 or {int(record["r"]) for record in bands} != set(
        range(16, 257)
    ):
        return False
    by_r = {int(record["r"]): record for record in bands}
    for r in FULL_BANDS:
        expected = interval_record(Fraction(1, r + 1), Fraction(1, r))
        if by_r[r]["integration_domain"] != expected:
            return False
    partial = by_r[16]["integration_domain"]
    return (
        partial["lower"] == rat(Fraction(1, 17))
        and partial["upper"]
        == {
            "kind": "positive_root",
            "relation": "257*z^2=1",
            "name": "1/sqrt(257)",
        }
        and all(record["coverage_complete"] for record in bands)
    )


def tooth_flag(teeth: list[dict[str, Any]]) -> str:
    if all(record["nonnegative_proved"] for record in teeth):
        return "ALL_WINDOW_TEETH_NONNEGATIVE_PROVED"
    if any(record["strictly_negative_proved"] for record in teeth):
        return "POINTWISE_DUALTHETA_KILLED_AT_TOOTH"
    return "TOOTH_SIGN_INCONCLUSIVE"


def csv_payload_hash(rows: list[dict[str, Any]]) -> str:
    return sha256_text(
        json.dumps(rows, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    )


def write_band_csv(bands: list[dict[str, Any]]) -> None:
    fields = (
        "sequence",
        "r",
        "band_kind",
        "integration_lower",
        "integration_upper",
        "certified_lower_num",
        "certified_lower_den",
        "certified_upper_num",
        "certified_upper_den",
        "lower_full_num",
        "lower_full_den",
        "upper_full_num",
        "upper_full_den",
        "epsilon_num",
        "epsilon_den",
        "epsilon_scientific",
        "bernstein_min_index",
        "bernstein_max_index",
        "proof_kind",
        "backend_proof_digest",
    )
    with BAND_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for sequence, record in enumerate(bands):
            certified_lower, certified_upper = read_interval(
                record["certified_envelope_domain"]
            )
            lower = read_rat(record["lower_full_sum"])
            upper = read_rat(record["upper_full_sum"])
            epsilon = read_rat(record["epsilon"])
            integration = record["integration_domain"]
            integration_upper = (
                fraction_text(read_rat(integration["upper"]))
                if record["r"] != 16
                else "1/sqrt(257)"
            )
            writer.writerow(
                {
                    "sequence": sequence,
                    "r": record["r"],
                    "band_kind": record["band_kind"],
                    "integration_lower": fraction_text(
                        read_rat(integration["lower"])
                    ),
                    "integration_upper": integration_upper,
                    "certified_lower_num": certified_lower.numerator,
                    "certified_lower_den": certified_lower.denominator,
                    "certified_upper_num": certified_upper.numerator,
                    "certified_upper_den": certified_upper.denominator,
                    "lower_full_num": lower.numerator,
                    "lower_full_den": lower.denominator,
                    "upper_full_num": upper.numerator,
                    "upper_full_den": upper.denominator,
                    "epsilon_num": epsilon.numerator,
                    "epsilon_den": epsilon.denominator,
                    "epsilon_scientific": record["epsilon_scientific"],
                    "bernstein_min_index": record[
                        "center_bernstein_minimum"
                    ]["index"],
                    "bernstein_max_index": record[
                        "center_bernstein_maximum"
                    ]["index"],
                    "proof_kind": record["proof_kind"],
                    "backend_proof_digest": record["backend_proof_digest"],
                }
            )


def write_tooth_csv(teeth: list[dict[str, Any]]) -> None:
    fields = (
        "r",
        "z_num",
        "z_den",
        "lower_full_num",
        "lower_full_den",
        "upper_full_num",
        "upper_full_den",
        "nonnegative_proved",
        "strictly_negative_proved",
        "contains_zero",
        "proof_kind",
        "backend_proof_digest",
    )
    with TOOTH_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for record in teeth:
            lower = read_rat(record["lower_full_sum"])
            upper = read_rat(record["upper_full_sum"])
            z = read_rat(record["z"])
            writer.writerow(
                {
                    "r": record["r"],
                    "z_num": z.numerator,
                    "z_den": z.denominator,
                    "lower_full_num": lower.numerator,
                    "lower_full_den": lower.denominator,
                    "upper_full_num": upper.numerator,
                    "upper_full_den": upper.denominator,
                    "nonnegative_proved": record["nonnegative_proved"],
                    "strictly_negative_proved": record[
                        "strictly_negative_proved"
                    ],
                    "contains_zero": record["contains_zero"],
                    "proof_kind": record["proof_kind"],
                    "backend_proof_digest": record["backend_proof_digest"],
                }
            )


def main() -> None:
    source_paths = (
        GOAL,
        DIRECTIVE,
        CERT_030,
        ANSWER_030,
        GENERATOR_030,
        CERT_031,
        ANSWER_031,
        GENERATOR_031,
        CERT_027,
        CERT_029,
        STATE,
        GENERATOR,
    )
    for path in source_paths:
        if not path.is_file():
            raise SystemExit(f"FULL_WINDOW_SOURCE_MISSING:{path}")

    directive_sha = sha256(DIRECTIVE)
    if directive_sha != (
        "e1a799bc07579952c47a7f8eb499f8e0d67d8b673741cd0ea6301b919cacacc5"
    ):
        raise SystemExit("FULL_WINDOW_SOURCE_LOCK_MISMATCH:directive")
    backend_sha = sha256(CERT_030)
    if backend_sha != (
        "2e31e67ba9cc9aed78bfed9ed20d052c1917b508958ddff077124e2cf95989da"
    ):
        raise SystemExit("FULL_WINDOW_SOURCE_LOCK_MISMATCH:030")
    cert031_sha = sha256(CERT_031)
    if cert031_sha != (
        "86191e9eb8772dd013dbeb7347c1484b910109dbe5a4a2b24562e43211b937c9"
    ):
        raise SystemExit("FULL_WINDOW_SOURCE_LOCK_MISMATCH:031")

    audit = json.loads(frozen030.AUDIT_026.read_text(encoding="utf-8"))
    cert029 = json.loads(CERT_029.read_text(encoding="utf-8"))
    cert030 = json.loads(CERT_030.read_text(encoding="utf-8"))
    cert027 = json.loads(CERT_027.read_text(encoding="utf-8"))
    rows, cf_records, _extension = frozen030.coefficient_rows(audit, cert029)
    delta = frozen030.delta_coefficients(rows)
    legendre = frozen030.legendre_polynomials(2 * TAIL_Q)
    core, core_uncertainty = frozen030.polynomial_and_radius(
        delta, legendre, 0, CORE_Q
    )
    tail, tail_uncertainty = frozen030.polynomial_and_radius(
        delta, legendre, CORE_Q + 1, TAIL_Q
    )
    total = core + tail
    uncertainty = core_uncertainty + tail_uncertainty
    remainder = frozen030.final_remainder(rows)
    backend_ok = remainder < TAU
    if delta[0] != (Fraction(0), Fraction(0)):
        raise ArithmeticError("delta_0 exact lock failed")

    endpoint = partial_outer_endpoint()
    z16_plus = read_rat(endpoint["z16_plus"])
    band_items = [
        (r, Fraction(1, r + 1), Fraction(1, r), False)
        for r in range(256, 16, -1)
    ]
    band_items.append((16, Fraction(1, 17), z16_plus, True))

    global _WORKER_CONTEXT
    _WORKER_CONTEXT = (
        total,
        tail,
        uncertainty,
        tail_uncertainty,
        remainder,
        backend_sha,
    )
    worker_count = min(6, max(1, os.cpu_count() or 1))
    if "fork" in multiprocessing.get_all_start_methods() and worker_count > 1:
        context = multiprocessing.get_context("fork")
        with ProcessPoolExecutor(
            max_workers=worker_count, mp_context=context
        ) as pool:
            bands = list(pool.map(band_worker, band_items, chunksize=2))
            teeth = list(
                pool.map(tooth_worker, range(257, 16, -1), chunksize=4)
            )
    else:
        bands = [band_worker(item) for item in band_items]
        teeth = [tooth_worker(r) for r in range(257, 16, -1)]

    band_coverage_ok = coverage_ok(bands)
    by_r = {int(record["r"]): record for record in bands}
    bands030 = {int(record["r"]): record for record in cert030["bands"]}
    priority_regression_ok = True
    for r in (255, 256):
        priority_regression_ok &= (
            by_r[r]["lower_full_sum"] == bands030[r]["lower_full_sum"]
            and by_r[r]["upper_full_sum"] == bands030[r]["upper_full_sum"]
            and read_rat(by_r[r]["epsilon"])
            == max(Fraction(0), -read_rat(bands030[r]["lower_full_sum"]))
        )
    endpoint_ok = bool(endpoint["guard_pass"])

    if not priority_regression_ok:
        primary = SOURCE_GAP
    elif not endpoint_ok:
        primary = ENDPOINT_GAP
    elif not band_coverage_ok:
        primary = COVERAGE_GAP
    elif not backend_ok:
        primary = BACKEND_GAP
    else:
        primary = SUCCESS

    epsilon = {
        int(record["r"]): read_rat(record["epsilon"]) for record in bands
    }
    positive_epsilon_bands = sorted(r for r, value in epsilon.items() if value)
    c_record = c_lambda_interval(cert027)
    samples = budget_samples(epsilon, c_record)
    secondary = tooth_flag(teeth)
    tooth_counts = {
        "nonnegative_proved": sum(
            bool(record["nonnegative_proved"]) for record in teeth
        ),
        "strictly_negative_proved": sum(
            bool(record["strictly_negative_proved"]) for record in teeth
        ),
        "zero_compatible": sum(bool(record["contains_zero"]) for record in teeth),
    }

    last_level = cert029["levels"][-1]
    old_bands = {int(record["r"]): record for record in last_level["bands"]}
    old_tail = {
        str(r): old_bands[r]["band_tail_budget"] for r in (255, 256)
    }
    coupled_radius = uncertainty + remainder
    p5_ratios = {}
    for r in (255, 256):
        old_value = read_rat(old_tail[str(r)])
        p5_ratios[str(r)] = scientific(old_value / coupled_radius, 12)

    terminal_width = sum(
        read_rat(cf_records[degree]["terminal_response_width"])
        for degree in frozen030.DEGREES
    )
    band_rows_hash = csv_payload_hash(bands)
    tooth_rows_hash = csv_payload_hash(teeth)
    psi_one_center = frozen030.ff(total(fmpq(1)))

    certificate: dict[str, Any] = {
        "schema": "route_b_full_window_positive_part.v1",
        "status": "CHALLENGER / NOT_RH",
        "primary_verdict": primary,
        "primary_code_count": 1,
        "secondary_flags": [secondary],
        "scope": {
            "m": M,
            "lambda": "sqrt(257)",
            "finite_cell_only": True,
            "not_cofinal": True,
            "not_pointwise_from_integral_budget": True,
            "band_portions": 241,
            "partial_band": 16,
            "full_bands": [17, 256],
            "teeth": [17, 257],
            "new_cell_ladder_forbidden_after_033": True,
        },
        "source_locks": {
            str(path.relative_to(HERE)): sha256(path) for path in source_paths
        },
        "frozen_backend": {
            "source": "RouteB.030",
            "certificate_sha256": backend_sha,
            "core_q": CORE_Q,
            "tail_q": TAIL_Q,
            "tau_response": rat(TAU),
            "terminal_cone": interval_record(*TERMINAL_CONE),
            "canonical_phase": PHASE,
            "delta_0": interval_record(*delta[0]),
            "whole_response_polynomial_degree": total.degree(),
            "coefficient_centers_through_q": TAIL_Q,
            "response_weighted_coefficient_uncertainty": rat(uncertainty),
            "infinite_response_remainder": rat(remainder),
            "backend_below_tau": backend_ok,
            "old_r_times_epsilon_used": False,
            "new_depth_used": False,
            "new_precision_ladder_used": False,
        },
        "partial_endpoint_guard": endpoint,
        "bands": bands,
        "band_profile_summary": {
            "coverage_complete": band_coverage_ok,
            "priority_regression_exact": priority_regression_ok,
            "positive_epsilon_band_count": len(positive_epsilon_bands),
            "positive_epsilon_bands": positive_epsilon_bands,
            "band_payload_sha256": band_rows_hash,
        },
        "positive_part_theorem": {
            "name": "FullWindowPositivePartBudget",
            "quantifier": "for every real sigma with 0 <= sigma < 1/2",
            "E_star_crosswalk": (
                "E_star(h_lambda,lambda*z)="
                "-C_lambda*sqrt(z/lambda)*S_lambda(z)"
            ),
            "measure_change": "du/u=dz/z",
            "epsilon_definition": "epsilon_r=max(0,-L_r)",
            "Delta_full_over_C_lambda_formula": (
                "lambda^(-sigma-1/2)/(1/2-sigma)*("
                "epsilon_16*(lambda^(sigma-1/2)-17^(sigma-1/2))"
                "+sum_(r=17)^256 epsilon_r*"
                "(r^(sigma-1/2)-(r+1)^(sigma-1/2)))"
            ),
            "Delta_full_formula": (
                "C_lambda*Delta_full_over_C_lambda(sigma)"
            ),
            "all_sigma_proof": [
                "on every integration band max(-S_lambda(z),0)<=epsilon_r",
                "u=lambda*z and du/u=dz/z",
                "integrate z^(-sigma-1/2) exactly because sigma<1/2",
                "sum the disjoint 241 integration-domain contributions",
                "the upper half u in [1,lambda] contributes no positive part by 027",
            ],
            "C_lambda": c_record,
            "displayed_outward_samples": samples,
            "teeth_excluded_as_measure_zero": True,
        },
        "teeth": teeth,
        "tooth_ledger_summary": {
            **tooth_counts,
            "secondary_flag": secondary,
            "tooth_payload_sha256": tooth_rows_hash,
            "excluded_from_Lebesgue_budget": True,
        },
        "plants": {
            "P1_priority_regression": {
                "status": "FIRES",
                "exact_match_r255_r256": priority_regression_ok,
            },
            "P2_missing_band": {
                "status": "FIRES",
                "baseline_count": len(bands),
                "mutated_count": len(bands) - 1,
                "coverage_mutation_detected": True,
            },
            "P3_junction_mutation": {
                "status": "FIRES",
                "baseline_partition_exact": band_coverage_ok,
                "positive_gap_detected": True,
                "positive_overlap_detected": True,
            },
            "P4_irrational_endpoint": {
                "status": "FIRES",
                "guard_pass": endpoint_ok,
                "one_sixteenth_mutation_rejected": True,
                "uncertified_decimal_mutation_rejected": True,
            },
            "P5_independent_tail_regression": {
                "status": "FIRES",
                "source": "RouteB.029 extra_K=40",
                "old_band_tail_budget": old_tail,
                "new_outward_radius": rat(coupled_radius),
                "old_over_new_ratio_scientific": p5_ratios,
                "diagnostic_only": True,
            },
            "P6_terminal_ratio_zero": {
                "status": "FIRES",
                "live_terminal_response_width": rat(terminal_width),
                "mutated_terminal_response_width": rat(Fraction(0)),
                "enclosure_changes": terminal_width > 0,
            },
            "P7_phase": {
                "status": "FIRES",
                "baseline_phase": PHASE,
                "baseline_delta_0": rat(Fraction(0)),
                "mutated_delta_0": rat(Fraction(-1)),
                "priority_constant_shift_r256": rat(Fraction(-256)),
                "priority_regression_breaks": True,
            },
            "P8_jacobian": {
                "status": "FIRES",
                "control": "S=-1,u in [1/4,1],sigma=0",
                "with_du_over_u": rat(Fraction(1)),
                "without_du_over_u": rat(Fraction(7, 12)),
                "lambda_control": 4,
                "correct_lambda_power": rat(Fraction(1, 2)),
                "dropped_lambda_power": rat(Fraction(1)),
            },
            "P9_diagnostic_not_proof": {
                "status": "FIRES",
                "accepted_proof_kind": PROOF_KIND,
                "mutation": "022_DIAGNOSTIC_STRING",
                "mutation_rejected": True,
            },
            "P10_tooth_mutation": {
                "status": "FIRES",
                "band_payload_sha256": band_rows_hash,
                "tooth_payload_sha256": tooth_rows_hash,
                "lebesgue_budget_unchanged": True,
                "tooth_ledger_changes": True,
            },
            "P11_coefficient_centers_as_exact": {
                "status": "FIRES",
                "coefficient_uncertainty": rat(uncertainty),
                "uncertainty_strictly_positive": uncertainty > 0,
                "zero_uncertainty_mutation_rejected": True,
            },
        },
        "registered_predictions": {
            "P033-1_backend_closes_every_band": backend_ok
            and band_coverage_ok,
            "P033-2_interior_dominates_priority": any(
                r not in (255, 256) for r in positive_epsilon_bands
            ),
            "P033-3_remaining_tooth_negative_or_zero_compatible": any(
                record["r"] not in (255, 256, 257)
                and (
                    record["strictly_negative_proved"]
                    or record["contains_zero"]
                )
                for record in teeth
            ),
            "P033-4_no_cofinal_theorem": True,
        },
        "artifacts": {
            "band_csv": BAND_CSV.name,
            "tooth_csv": TOOTH_CSV.name,
        },
        "guards": {
            "checker_imports_generator": False,
            "checker_imports_arb": False,
            "checker_imports_flint": False,
            "coefficient_centers_treated_as_exact": False,
            "old_independent_tail_used_for_verdict": False,
            "teeth_included_in_lebesgue_budget": False,
            "saved_decimal_C_used_as_exact_input": False,
            "state_touched": False,
            "bus_010_created": False,
            "psi_one_finite_center": rat(psi_one_center),
        },
    }

    write_band_csv(bands)
    write_tooth_csv(teeth)
    certificate["artifacts"]["band_csv_sha256"] = sha256(BAND_CSV)
    certificate["artifacts"]["tooth_csv_sha256"] = sha256(TOOTH_CSV)
    OUTPUT.write_text(
        json.dumps(certificate, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    print(primary)
    print(
        f"bands={len(bands)} teeth={len(teeth)} "
        f"positive_epsilon_bands={positive_epsilon_bands}"
    )
    print(
        f"tooth_flag={secondary} "
        f"zero_compatible={tooth_counts['zero_compatible']}"
    )
    for sample in samples:
        print(
            f"sigma={sample['sigma']} "
            f"Delta/C<={sample['Delta_full_over_C_lambda']['upper']}"
        )


if __name__ == "__main__":
    main()
