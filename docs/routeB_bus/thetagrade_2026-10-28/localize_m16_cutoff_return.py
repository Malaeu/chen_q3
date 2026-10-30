#!/usr/bin/env python3
"""Direct Arb cutoff projection and full same-carrier m=16 Rayleigh gap."""

from __future__ import annotations

import hashlib
import json
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

sys.dont_write_bytecode = True

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
ROOT = Path(__file__).resolve().parents[3]
PHASE5 = ROOT / "docs/routeB_bus/phase5_scripts"
sys.path.insert(0, str(PHASE5))

import edge_ledger_build as edge  # noqa: E402

M = 16
DPS = 100
INITIAL_GRIDS = (8192, 32768)
ONE_REFINEMENT = 131072

GROUND = HERE / "noescape_m16_ground_eigenpair.json"
GROUND_SOURCE = HERE / "noescape_m16_eigenpair.py"
BUILDER_SOURCE = PHASE5 / "edge_ledger_build.py"
VERDICT = ROOT / "docs/routeB_bus/proshka/PROSHKA_VERDICT_LOCALIZE_2026-10-31.md"
OUTPUT = HERE / "localize_m16_cutoff_return.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ball_record(value: arb) -> dict[str, str]:
    value = arb(value)
    return {"ball": str(value), "lower": str(value.lower()), "upper": str(value.upper())}


def fraction_arb(value: Fraction) -> arb:
    denominator = value.denominator
    if denominator & (denominator - 1):
        raise ValueError(f"grid endpoint is not dyadic: {value}")
    return arb(value.numerator) / arb(denominator)


def cell_arb(left: Fraction, right: Fraction) -> arb:
    midpoint = fraction_arb((left + right) / 2)
    radius = fraction_arb((right - left) / 2)
    return arb(midpoint.mid(), (radius + midpoint.rad()).upper())


def interval_from_endpoint_balls(left_value: arb, right_value: arb) -> arb:
    center = (left_value.mid() + right_value.mid()) / 2
    radius = (
        abs(right_value.mid() - left_value.mid()) / 2
        + left_value.rad()
        + right_value.rad()
        + center.rad()
    )
    return arb(center.mid(), radius.upper())


def interval_sign(value: arb) -> str:
    if value.lower() > 0:
        return "POSITIVE"
    if value.upper() < 0:
        return "NEGATIVE"
    return "UNRESOLVED_CONTAINS_ZERO"


def simple_sign_rational(value: arb) -> dict[str, str] | None:
    sign = interval_sign(value)
    magnitude = value if sign == "POSITIVE" else -value if sign == "NEGATIVE" else None
    if magnitude is None:
        return None
    lower = magnitude.lower()
    for digits in range(1, 201):
        denominator = 10**digits
        candidate = arb(f"1/{denominator}")
        if candidate < lower:
            signed = f"1/{denominator}" if sign == "POSITIVE" else f"-1/{denominator}"
            statement = f"value > {signed}" if sign == "POSITIVE" else f"value < {signed}"
            return {"rational": signed, "statement": statement}
    return None


def main() -> None:
    started = time.monotonic()
    ctx.dps = DPS
    ctx.threads = 1

    source = json.loads(GROUND.read_text(encoding="utf-8"))
    ground = source["ground_eigenvector"]
    normalized = ground["interval_normalized"]
    if ground["selected_index_zero_based"] != 0:
        raise ValueError("the cached vector is not the zero-based index-0 ground vector")
    if normalized["map"] != "c_0=xi_0 and c_{+/-j}=xi_j/sqrt(2)":
        raise ValueError("unexpected even-to-phased-Fourier map")
    if normalized["norm_squared_encloses_one"] is not True:
        raise ArithmeticError("cached normalized ground coordinates do not enclose unit norm")
    if sha256(BUILDER_SOURCE) != source["source_sha256"]["edge_ledger_build.py"]:
        raise ValueError("literal CCM builder hash differs from the cached eigenpair provenance")
    if sha256(GROUND_SOURCE) != source["source_sha256"]["this_script"]:
        raise ValueError("ground eigenpair script hash differs from the cached eigenpair provenance")

    xi = [arb(row["ball"]) for row in normalized["even_basis_coordinates"]]
    modes = [arb(row["ball"]) for row in normalized["fourier_modes_minus16_to_plus16"]]
    if len(xi) != M + 1 or len(modes) != 2 * M + 1:
        raise ValueError("unexpected cached m=16 ground coordinate shape")
    xi_norm2 = sum((value * value for value in xi), arb(0))
    if 1 not in xi_norm2:
        raise ArithmeticError("normalized even coordinates do not interval-enclose norm one")

    sqrt2 = arb(2).sqrt()
    max_pair_defect = arb(0)
    for j in range(1, M + 1):
        plus = modes[M + j]
        minus = modes[M - j]
        if 0 not in plus - minus:
            raise ArithmeticError(f"cached phased Fourier pair is not even at mode {j}")
        if 0 not in plus - xi[j] / sqrt2 or 0 not in minus - xi[j] / sqrt2:
            raise ArithmeticError(f"cached Fourier phase map failed at mode {j}")
        defect = abs(plus - minus)
        max_pair_defect = (max_pair_defect + defect + abs(max_pair_defect - defect)) / 2

    L = arb(16).log()
    b = L / 2
    R = arb("1/2")
    pi = arb.pi()
    sqrtL = L.sqrt()
    if not (R < b):
        raise ArithmeticError("cutoff support is not contained in the m=16 carrier window")
    omega = [2 * pi * i / L for i in range(M + 1)]

    def basis_function(i: int, x: arb) -> arb:
        if i == 0:
            return 1 / sqrtL
        return sqrt2 / sqrtL * (omega[i] * (x + b)).cos()

    def ground_function(x: arb) -> arb:
        return sum((xi[i] * basis_function(i, x) for i in range(M + 1)), arb(0))

    def chi_point(x: Fraction) -> arb:
        t = fraction_arb(x)
        if t <= arb("1/4"):
            return arb(1)
        if t >= arb("1/2"):
            return arb(0)
        u = 4 * t - 1
        e_left = (-1 / (1 - u)).exp()
        e_right = (-1 / u).exp()
        return e_left / (e_left + e_right)

    def chi_range(left: Fraction, right: Fraction) -> arb:
        # For u=4x-1, log(e_right/e_left)=(2u-1)/(u(1-u)) is strictly
        # increasing, so chi is decreasing; the endpoint values bound it.
        return interval_from_endpoint_balls(chi_point(right), chi_point(left))

    if chi_point(Fraction(0)) != 1 or chi_point(Fraction(1, 4)) != 1 or chi_point(Fraction(1, 2)) != 0:
        raise ArithmeticError("requested cutoff endpoint values failed")

    builder = edge.CCMArbBuilder(M, M)
    matrix = builder.even_block()
    if matrix.nrows() != M + 1 or matrix.ncols() != M + 1:
        raise ValueError("literal CCM builder returned the wrong even-block size")
    for i in range(M + 1):
        for j in range(i + 1, M + 1):
            if not matrix[i, j].overlaps(matrix[j, i]):
                raise ArithmeticError(f"literal even block is not interval-symmetric at ({i},{j})")

    lam = arb(ground["eigenvalue"]["ball"])

    def coefficient_integrals(base_subdivisions: int) -> tuple[list[arb], int, float]:
        local_started = time.monotonic()
        cuts = {Fraction(i, 2 * base_subdivisions) for i in range(base_subdivisions + 1)}
        cuts.update((Fraction(0), Fraction(1, 4), Fraction(1, 2)))
        ordered = sorted(cuts)
        coefficients = [arb(0) for _ in range(M + 1)]
        for left, right in zip(ordered, ordered[1:]):
            x = cell_arb(left, right)
            width = fraction_arb(right - left)
            chi = chi_range(left, right)
            f = ground_function(x)
            for i in range(M + 1):
                integrand = basis_function(i, x) * chi * f
                coefficients[i] += 2 * width * integrand
        return coefficients, len(ordered) - 1, time.monotonic() - local_started

    def quadratic(coefficients: list[arb]) -> arb:
        return sum(
            (
                coefficients[i] * matrix[i, j] * coefficients[j]
                for i in range(M + 1)
                for j in range(M + 1)
            ),
            arb(0),
        )

    def evaluate_grid(base_subdivisions: int) -> dict[str, Any]:
        coefficients, cell_count, elapsed = coefficient_integrals(base_subdivisions)
        norm2 = sum((value * value for value in coefficients), arb(0))
        if not (norm2.lower() > 0):
            raise ArithmeticError(
                f"cutoff projection norm is not certified positive at {base_subdivisions} cells: {norm2}"
            )
        norm = norm2.sqrt()
        unit_coefficients = [value / norm for value in coefficients]
        unit_norm2 = sum((value * value for value in unit_coefficients), arb(0))
        if 1 not in unit_norm2:
            raise ArithmeticError("interval-normalized cutoff coordinates do not enclose unit norm")

        raw_quadratic = quadratic(coefficients)
        raw_margin = raw_quadratic - lam * norm2
        normalized_quotient = quadratic(unit_coefficients)
        quotient_gap = normalized_quotient - lam
        scaled_gap = norm2 * quotient_gap
        if not raw_margin.overlaps(scaled_gap):
            raise ArithmeticError("raw margin and normalized quotient gap enclosures do not overlap")

        gap_sign = interval_sign(quotient_gap)
        margin_sign = interval_sign(raw_margin)
        if gap_sign != "UNRESOLVED_CONTAINS_ZERO" and margin_sign != gap_sign:
            raise ArithmeticError("raw margin and quotient gap have inconsistent certified signs")
        rational_gap_bound = simple_sign_rational(quotient_gap)
        rational_margin_bound = simple_sign_rational(raw_margin)
        return {
            "base_subdivisions_on_half_interval": base_subdivisions,
            "actual_interval_cells": cell_count,
            "coefficient_integral_seconds": round(elapsed, 3),
            "projection_coefficients_v": [ball_record(value) for value in coefficients],
            "projection_norm_squared": ball_record(norm2),
            "projection_norm_strictly_positive": True,
            "projection_norm": ball_record(norm),
            "unit_cutoff_coefficients": [ball_record(value) for value in unit_coefficients],
            "unit_cutoff_norm_squared": ball_record(unit_norm2),
            "raw_vTA_v": ball_record(raw_quadratic),
            "lambda_cached_times_norm_squared": ball_record(lam * norm2),
            "raw_margin_vTA_v_minus_lambda_norm_squared": ball_record(raw_margin),
            "normalized_rayleigh_quotient": ball_record(normalized_quotient),
            "quotient_gap_minus_lambda_cached": ball_record(quotient_gap),
            "norm_squared_times_quotient_gap": ball_record(scaled_gap),
            "raw_margin_overlaps_norm_squared_times_quotient_gap": True,
            "raw_margin_sign": margin_sign,
            "quotient_gap_sign": gap_sign,
            "quotient_gap_rational_sign_bound": rational_gap_bound,
            "raw_margin_rational_sign_bound": rational_margin_bound,
        }

    results: list[dict[str, Any]] = []
    for count in INITIAL_GRIDS:
        result = evaluate_grid(count)
        results.append(result)
    last = results[-1]
    if (
        last["quotient_gap_sign"] == "UNRESOLVED_CONTAINS_ZERO"
        or last["raw_margin_sign"] == "UNRESOLVED_CONTAINS_ZERO"
    ):
        results.append(evaluate_grid(ONE_REFINEMENT))

    route_criterion = results[-1]["quotient_gap_sign"]
    payload = {
        "status": "DIRECT_M16_CUTOFF_COMPETITOR_INTERVAL_ENCLOSURE",
        "route_status": "CHALLENGER_NOT_RH",
        "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
        "scope": "same-carrier normalized P_16(chi f_16) competitor on the cached literal even m=N=16 index-0 input; finite cell only",
        "cutoff": (
            "even; chi=1 for |x|<=1/4; chi=0 for |x|>=1/2; on 1/4<|x|<1/2, "
            "u=4|x|-1 and chi=exp(-1/(1-u))/(exp(-1/(1-u))+exp(-1/u))"
        ),
        "projection_formula": (
            "v_i=<e_i,chi f>=2*integral_0^(1/2)e_i(x)*chi(x)*f(x)dx; "
            "e_0=1/sqrt(L), e_i=sqrt(2/L)*cos(2*pi*i*(x+b)/L), b=L/2"
        ),
        "integration_method": (
            "direct Arb interval Riemann range sums for the 17 coefficient integrals; each cell contributes exact width "
            "times the interval extension of e_i*chi*f. The half-window factor 2 uses evenness."
        ),
        "ground_input": {
            "path": str(GROUND.relative_to(ROOT)),
            "sha256": sha256(GROUND),
            "status": source["status"],
            "selected_index_zero_based": ground["selected_index_zero_based"],
            "cached_lambda": ball_record(lam),
            "coordinate_source": "ground_eigenvector.interval_normalized.even_basis_coordinates",
            "coordinate_map": normalized["map"],
            "coordinate_norm_squared": ball_record(xi_norm2),
            "maximum_even_pair_absolute_defect_upper": str(max_pair_defect.upper()),
        },
        "operator": {
            "builder": "CCMArbBuilder(16,16).even_block()",
            "source_module": str(BUILDER_SOURCE.relative_to(ROOT)),
            "matrix_dimension": M + 1,
            "basis": "e_0,(e_i+e_-i)/sqrt(2), i=1..16, with phased Fourier cos basis",
            "entry_formula": "CCMArbBuilder.tau_entry = w02 - wr - prime; w02 is the two source pole integrals; wr is the archimedean term including diagonal gamma/beta; prime sums every builder.prime_powers entry",
            "prime_powers": [
                {"n": int(n), "prime": int(p), "coefficient": ball_record(builder.log_prime[p] / arb(n).sqrt())}
                for n, p in builder.prime_powers
            ],
            "matrix_symmetric_interval_check_passed": True,
        },
        "cutoff_competitor": {
            "interpretation": "v=P_16(chi*f); normalized coefficients v/sqrt(sum_i v_i^2)",
            "source_identity_subtraction_used": False,
            "all_operator_terms_preserved_through_builder": True,
            "results": results,
            "final_sign": route_criterion,
        },
        "environment": {
            "python": platform.python_version(),
            "python_flint": getattr(__import__("flint"), "__version__", "unknown"),
            "arb_dps": DPS,
            "arb_threads": 1,
        },
        "input_sha256": {
            "ground_eigenpair_json": sha256(GROUND),
            "ground_eigenpair_source": sha256(GROUND_SOURCE),
            "literal_builder_source": sha256(BUILDER_SOURCE),
            "localize_verdict": sha256(VERDICT),
            "script": sha256(Path(__file__).resolve()),
        },
        "limitations": [
            "Coefficient and matrix interval arithmetic is conditional on the cached coordinate balls and literal builder outputs; the input labels its eigenpair diagnostic, not a proof certificate.",
            "This evaluates one finite same-carrier cutoff competitor only; it is not a cofinal NOESCAPE argument and proves neither T nor RH.",
            "The result is a direct Rayleigh comparison; no energy-identity subtraction is used as an independent computation.",
        ],
        "runtime_seconds_total": round(time.monotonic() - started, 3),
    }
    OUTPUT.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": payload["status"],
        "runtime_seconds_total": payload["runtime_seconds_total"],
        "output": str(OUTPUT),
        "grids": [
            {
                "subdivisions": row["base_subdivisions_on_half_interval"],
                "cells": row["actual_interval_cells"],
                "norm2": row["projection_norm_squared"]["ball"],
                "raw_margin": row["raw_margin_vTA_v_minus_lambda_norm_squared"]["ball"],
                "quotient_gap": row["quotient_gap_minus_lambda_cached"]["ball"],
                "sign": row["quotient_gap_sign"],
                "rational_bound": row["quotient_gap_rational_sign_bound"],
            }
            for row in results
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
