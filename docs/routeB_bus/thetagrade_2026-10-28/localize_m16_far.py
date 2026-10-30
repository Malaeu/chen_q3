#!/usr/bin/env python3
"""Direct Arb enclosure of LOCALIZE (3.2)'s far term on the cached m=16 ground.

The only integration is a one-dimensional interval-Riemann range sum in x.
The continuum's inner a-integral is evaluated by analytic mode primitives.
No energy identity is used to infer this value.
"""

from __future__ import annotations

import hashlib
import json
import platform
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
M = 16
DPS = 120
BASE_SUBDIVISIONS = (512, 2048, 262144)
BREAKPOINT_BITS = 160

GROUND = HERE / "noescape_m16_ground_eigenpair.json"
VERDICT = ROOT / "docs/routeB_bus/proshka/PROSHKA_VERDICT_LOCALIZE_2026-10-31.md"
ALGEBRA = HERE / "localize_proshka_algebra.py"
OUTPUT = HERE / "localize_m16_far.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ball_record(value: arb) -> dict[str, str]:
    value = arb(value)
    return {
        "ball": str(value),
        "lower": str(value.lower()),
        "upper": str(value.upper()),
    }


def fraction_arb(value: Fraction) -> arb:
    """Convert an exact dyadic rational to Arb without a decimal round trip."""
    denominator = value.denominator
    if denominator & (denominator - 1):
        raise ValueError(f"non-dyadic grid rational: {value}")
    return arb(value.numerator) / arb(denominator)


def cell_arb(left: Fraction, right: Fraction) -> arb:
    midpoint = fraction_arb((left + right) / 2)
    radius = fraction_arb((right - left) / 2)
    return arb(midpoint.mid(), (radius + midpoint.rad()).upper())


def interval_from_endpoint_balls(low_value: arb, high_value: arb) -> arb:
    """Enclose the interval between two ordered, interval-valued endpoints."""
    low_value = arb(low_value)
    high_value = arb(high_value)
    center = (low_value.mid() + high_value.mid()) / 2
    radius = (
        abs(high_value.mid() - low_value.mid()) / 2
        + low_value.rad()
        + high_value.rad()
        + center.rad()
    )
    return arb(center.mid(), radius.upper())


def hull_with_zero(value: arb) -> arb:
    """Return a compact Arb ball enclosing value union {0}."""
    value = arb(value)
    if 0 in value:
        return value
    if value > 0:
        upper = value.upper()
        return arb(upper.mid() / 2, upper.mid() / 2 + upper.rad())
    if value < 0:
        return -hull_with_zero(-value)
    raise ArithmeticError(f"could not determine sign for interval hull: {value}")


def prime_for_prime_power(n: int) -> int | None:
    for p in range(2, n + 1):
        if any(p % d == 0 for d in range(2, int(p**0.5) + 1)):
            continue
        q = n
        while q % p == 0:
            q //= p
        if q == 1:
            return p
    return None


def dyadic_bracket(value: arb, bits: int = BREAKPOINT_BITS) -> tuple[Fraction, Fraction]:
    """Return exact dyadic endpoints enclosing a non-dyadic breakpoint ball."""
    left = Fraction(0)
    right = Fraction(1, 2)
    for _ in range(bits):
        middle = (left + right) / 2
        middle_ball = fraction_arb(middle)
        if middle_ball < value:
            left = middle
        elif value < middle_ball:
            right = middle
        else:
            # The Arb breakpoint overlaps this exact dyadic midpoint.  The
            # maintained bracket still contains the whole breakpoint ball.
            return left, right
    return left, right


def classify_le_threshold(left: Fraction, right: Fraction, threshold: arb) -> str:
    """Classify x<=threshold on one partition cell, including a sliver cell."""
    xlo = fraction_arb(left)
    xhi = fraction_arb(right)
    if xhi <= threshold:
        return "active"
    if threshold <= xlo:
        return "inactive"
    return "mixed"


def classify_ge_threshold(left: Fraction, right: Fraction, threshold: arb) -> str:
    """Classify x>=threshold on one partition cell, including a sliver cell."""
    xlo = fraction_arb(left)
    xhi = fraction_arb(right)
    if threshold <= xlo:
        return "active"
    if xhi <= threshold:
        return "inactive"
    return "mixed"


def main() -> None:
    started = time.monotonic()
    ctx.dps = DPS
    ctx.threads = 1

    source = json.loads(GROUND.read_text(encoding="utf-8"))
    ground = source["ground_eigenvector"]
    normalized = ground["interval_normalized"]
    if ground["selected_index_zero_based"] != 0:
        raise ValueError("ground cache is not the zero-based index-0 vector")
    if normalized["map"] != "c_0=xi_0 and c_{+/-j}=xi_j/sqrt(2)":
        raise ValueError("unexpected normalized ground Fourier-coordinate map")
    if normalized["norm_squared_encloses_one"] is not True:
        raise ArithmeticError("stored interval-normalized ground norm does not enclose one")

    xi = [arb(row["ball"]) for row in normalized["even_basis_coordinates"]]
    modes = [arb(row["ball"]) for row in normalized["fourier_modes_minus16_to_plus16"]]
    mode_order = normalized["mode_order"]
    if len(xi) != M + 1 or mode_order != list(range(-M, M + 1)) or len(modes) != 2 * M + 1:
        raise ValueError("unexpected m=16 ground coordinate shape")
    xi_norm2 = sum((coefficient * coefficient for coefficient in xi), arb(0))
    mode_norm2 = sum((coefficient * coefficient for coefficient in modes), arb(0))
    if 1 not in xi_norm2 or 1 not in mode_norm2:
        raise ArithmeticError("normalized ground coordinate balls do not enclose unit norm")

    sqrt2 = arb(2).sqrt()
    pair_differences: list[arb] = []
    pair_map_differences: list[arb] = []
    for j in range(1, M + 1):
        plus = modes[M + j]
        minus = modes[M - j]
        pair_differences.append(plus - minus)
        pair_map_differences.extend((plus - xi[j] / sqrt2, minus - xi[j] / sqrt2))
        if 0 not in (plus - minus):
            raise ArithmeticError(f"stored ground mode pair is not interval-even at j={j}")
        if 0 not in (plus - xi[j] / sqrt2) or 0 not in (minus - xi[j] / sqrt2):
            raise ArithmeticError(f"stored ground mode map failed at j={j}")

    L = arb(16).log()
    b = L / 2
    a0 = arb(3).log()
    radius = arb("1/2")
    pi = arb.pi()
    sqrtL = L.sqrt()
    if not (arb(1) < a0):
        raise ArithmeticError("LOCALIZE requires log(3)>1=2R")
    if not (a0 < b):
        raise ArithmeticError("continuum lower endpoint is not below b=log(4)")
    if not (b + radius < L):
        raise ArithmeticError("continuum translated support reaches the upper integration cap L")

    omega = [2 * pi * j / L for j in range(M + 1)]

    def f_range(x: arb) -> arb:
        value = xi[0]
        for j in range(1, M + 1):
            value += sqrt2 * xi[j] * (omega[j] * (x + b)).cos()
        return value / sqrtL

    def f_from_phased_modes(x: arb) -> arb:
        value = modes[M]
        for j in range(1, M + 1):
            value += (modes[M + j] + modes[M - j]) * (omega[j] * (x + b)).cos()
        return value / sqrtL

    reconstitution_checks: list[dict[str, str]] = []
    for point in (Fraction(0), Fraction(1, 8), Fraction(1, 4), Fraction(1, 2)):
        x = fraction_arb(point)
        defect = f_range(x) - f_from_phased_modes(x)
        if 0 not in defect:
            raise ArithmeticError(f"phased Fourier reconstitution failed at x={point}: {defect}")
        reconstitution_checks.append({"x": str(point), "difference_ball": str(defect)})

    def chi_point(x: Fraction) -> arb:
        t = fraction_arb(x)
        if t <= arb("1/4"):
            return arb(1)
        if t >= arb("1/2"):
            return arb(0)
        u = 4 * t - 1
        left = (-1 / (1 - u)).exp()
        right = (-1 / u).exp()
        return left / (left + right)

    def chi_squared_range(left: Fraction, right: Fraction) -> arb:
        # chi is decreasing on [0,1/2], so endpoint values bound each cell.
        at_left = chi_point(left)
        at_right = chi_point(right)
        return interval_from_endpoint_balls(at_right * at_right, at_left * at_left)

    quarter = Fraction(1, 4)
    half = Fraction(1, 2)
    if chi_point(Fraction(0)) != 1 or chi_point(quarter) != 1 or chi_point(half) != 0:
        raise ArithmeticError("cutoff endpoint definitions do not match the requested plateau/support")

    def primitive(sigma: int, j: int, x: arb, a: arb) -> arb:
        # theta = omega_j * (x+b+sigma*a).  Differentiating gives
        # exp(a/2)*cos(theta), for sigma=+1 and sigma=-1 separately.
        theta = omega[j] * (x + b + sigma * a)
        denominator = arb("1/4") + omega[j] * omega[j]
        numerator = arb("1/2") * theta.cos() + sigma * omega[j] * theta.sin()
        return (a / 2).exp() * numerator / denominator

    def complex_primitive(sigma: int, j: int, x: arb, a: arb) -> arb:
        # Re(exp(i*omega*(x+b))*exp((1/2+i*sigma*omega)*a)
        #    /(1/2+i*sigma*omega)); this independently checks the real signs.
        rate = acb(arb("1/2"), sigma * omega[j])
        phase = acb(0, omega[j] * (x + b))
        return ((phase + rate * a).exp() / rate).real

    primitive_checks: list[dict[str, str]] = []
    for sigma in (1, -1):
        for j in range(M + 1):
            x = arb("1/8")
            a = a0 + arb("1/16")
            real_form = primitive(sigma, j, x, a)
            complex_form = complex_primitive(sigma, j, x, a)
            defect = real_form - complex_form
            if 0 not in defect:
                raise ArithmeticError(
                    f"analytic primitive sign check failed for sigma={sigma}, j={j}: {defect}"
                )
            if j in (0, 1, 16):
                primitive_checks.append(
                    {"sigma": str(sigma), "j": str(j), "difference_ball": str(defect)}
                )

    def continuum_sigma(sigma: int, x: arb) -> arb:
        # The active upper endpoint is b-sigma*x.  The lower endpoint a0
        # remains fixed; all these upper endpoints are below L for |x|<=R.
        upper = b - sigma * x
        total = xi[0] / sqrtL * (primitive(sigma, 0, x, upper) - primitive(sigma, 0, x, a0))
        for j in range(1, M + 1):
            amplitude = sqrt2 * xi[j] / sqrtL
            total += amplitude * (
                primitive(sigma, j, x, upper) - primitive(sigma, j, x, a0)
            )
        return total

    continuum_clip = (arb(4) / arb(3)).log()
    if 0 not in (continuum_clip - (b - a0)):
        raise ArithmeticError("continuum plus-shift clipping threshold failed log(4/3)=b-log(3)")
    continuum_bracket = dyadic_bracket(continuum_clip)
    breakpoint_brackets: dict[str, tuple[Fraction, Fraction]] = {
        "continuum_plus_log_4_over_3": continuum_bracket
    }

    prime_rows: list[dict[str, Any]] = []
    prime_thresholds: dict[int, arb] = {}
    prime_coefficients: dict[int, arb] = {}
    for n in range(4, M + 1):
        p = prime_for_prime_power(n)
        if p is None:
            continue
        coefficient = arb(p).log() / arb(n).sqrt()
        threshold = arb(0) if n == 4 else (arb(n) / 4).log()
        if 0 not in (threshold - (arb(n).log() - b)):
            raise ArithmeticError(f"prime clipping threshold identity failed for n={n}")
        prime_thresholds[n] = threshold
        prime_coefficients[n] = coefficient
        support_empty = radius < threshold
        if not support_empty and n != 4:
            breakpoint_brackets[f"prime_{n}_log_{n}_over_4"] = dyadic_bracket(threshold)
        prime_rows.append(
            {
                "n": n,
                "prime_base": p,
                "von_mangoldt": {"ball": str(arb(p).log())},
                "coefficient_c_n": ball_record(coefficient),
                "minus_shift_threshold_log_n_over_4": ball_record(threshold),
                "support_empty_on_x_0_to_1_over_2": bool(support_empty),
                "plus_shift_support_on_x_positive": "empty except n=4 at the measure-zero endpoint x=0",
            }
        )

    def run_riemann(base_subdivisions: int) -> dict[str, Any]:
        run_started = time.monotonic()
        cuts = {Fraction(i, 2 * base_subdivisions) for i in range(base_subdivisions + 1)}
        cuts.update((Fraction(0), quarter, half))
        for left, right in breakpoint_brackets.values():
            cuts.add(left)
            cuts.add(right)
        ordered_cuts = sorted(cuts)
        by_n = {n: arb(0) for n in prime_thresholds}
        prime_total = arb(0)
        continuum_total = arb(0)
        joint_total = arb(0)
        crossing_cells: list[dict[str, str]] = []

        for left, right in zip(ordered_cuts, ordered_cuts[1:]):
            x = cell_arb(left, right)
            width = fraction_arb(right - left)
            outside = chi_squared_range(left, right) * f_range(x)

            term_by_n: dict[int, arb] = {}
            for n, threshold in prime_thresholds.items():
                if radius < threshold:
                    term_by_n[n] = arb(0)
                    continue
                if n == 4:
                    state = "active"
                else:
                    state = classify_ge_threshold(left, right, threshold)
                if state == "inactive":
                    term_by_n[n] = arb(0)
                else:
                    term = prime_coefficients[n] * f_range(x - arb(n).log())
                    if state == "mixed":
                        term = hull_with_zero(term)
                        crossing_cells.append(
                            {"source": f"prime_n={n}", "left": str(left), "right": str(right)}
                        )
                    term_by_n[n] = term
                    by_n[n] += 2 * width * outside * term

            prime_range = sum(term_by_n.values(), arb(0))
            continuum_plus = continuum_sigma(1, x)
            plus_state = classify_le_threshold(left, right, continuum_clip)
            if plus_state == "inactive":
                continuum_plus = arb(0)
            elif plus_state == "mixed":
                continuum_plus = hull_with_zero(continuum_plus)
                crossing_cells.append(
                    {"source": "continuum_plus", "left": str(left), "right": str(right)}
                )
            continuum_range = continuum_plus + continuum_sigma(-1, x)

            prime_total += 2 * width * outside * prime_range
            continuum_total += 2 * width * outside * continuum_range
            joint_total += 2 * width * outside * (prime_range - continuum_range)

        prime_from_terms = sum(by_n.values(), arb(0))
        separated_joint = prime_from_terms - continuum_total
        joint_overlap = joint_total.overlaps(separated_joint)
        if not joint_overlap:
            raise ArithmeticError("direct and component-difference joint enclosures do not overlap")
        overlap = joint_total.intersection(separated_joint)
        joint_lower = joint_total.lower()
        joint_upper = joint_total.upper()
        if joint_lower > 0:
            joint_sign = "POSITIVE"
        elif joint_upper < 0:
            joint_sign = "NEGATIVE"
        else:
            joint_sign = "UNRESOLVED_CONTAINS_ZERO"
        rational_outer_enclosure = None
        if base_subdivisions == 262144:
            rational_lower_text = "-36014/1000000000"
            rational_upper_text = "-14079/1000000000"
            rational_lower = arb(rational_lower_text)
            rational_upper = arb(rational_upper_text)
            lower_comparison = rational_lower < joint_lower
            upper_comparison = joint_upper < rational_upper
            if not (lower_comparison and upper_comparison):
                raise ArithmeticError(
                    "fine direct F_far interval escaped the asserted rational outer enclosure"
                )
            rational_outer_enclosure = {
                "lower_endpoint_exact_rational": rational_lower_text,
                "upper_endpoint_exact_rational": rational_upper_text,
                "joint_arb_lower_endpoint": str(joint_lower),
                "joint_arb_upper_endpoint": str(joint_upper),
                "lower_comparison_passed": bool(lower_comparison),
                "upper_comparison_passed": bool(upper_comparison),
                "asserted": True,
            }
        return {
            "base_subdivisions_on_half_interval": base_subdivisions,
            "actual_interval_cells": len(ordered_cuts) - 1,
            "x_interval": "[0,1/2] a.e., with factor 2 from exact evenness; the isolated x=0 value is omitted and has measure zero",
            "breakpoint_brackets_dyadic": {
                label: {"left": str(left), "right": str(right), "width": str(right - left)}
                for label, (left, right) in breakpoint_brackets.items()
            },
            "mixed_indicator_cells": crossing_cells,
            "prime_power_integrals": {
                str(n): ball_record(value) for n, value in sorted(by_n.items())
            },
            "raw_prime_sum_from_individual_terms": ball_record(prime_from_terms),
            "raw_prime_sum_direct_cell_ranges": ball_record(prime_total),
            "continuum_integral": ball_record(continuum_total),
            "joint_direct_cell_ranges": ball_record(joint_total),
            "joint_from_separate_components": ball_record(separated_joint),
            "joint_direct_intersects_component_difference": bool(joint_overlap),
            "joint_overlap": ball_record(overlap),
            "joint_sign": joint_sign,
            "rational_outer_enclosure": rational_outer_enclosure,
            "seconds": round(time.monotonic() - run_started, 3),
            "integration_method": (
                "rigorous Arb interval Riemann range a.e.: on each x-cell, the a.e. integrand is enclosed by its interval extension; "
                "multiply by exact cell width and sum. The isolated x=0 value is omitted (measure zero). "
                "Breakpoint slivers enclose both the active formula and zero."
            ),
        }

    result: dict[str, Any] = {
        "status": "RUNNING",
        "route_status": "CHALLENGER_NOT_RH",
        "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
        "scope": "LOCALIZE (3.2) F_far only; cached literal m=N=16 zero-based index-0 ground coordinates; no E, near term, full B, cofinal, T, or RH conclusion",
        "formula": (
            "F_far=integral chi(x)^2 f(x) [sum_{n prime power, 3<n<=16} (Lambda(n)/sqrt(n)) "
            "(f(x+log(n))*1_I(x+log(n))+f(x-log(n))*1_I(x-log(n))) "
            "- integral_{log(3)}^{log(16)} exp(a/2) "
            "(f(x+a)*1_I(x+a)+f(x-a)*1_I(x-a)) da] dx"
        ),
        "conventions": {
            "L": ball_record(L),
            "b=L/2": ball_record(b),
            "I": "[-b,b]",
            "a0": ball_record(a0),
            "R": "1/2",
            "a0_gt_2R": True,
            "prime_powers_strictly_above_3_through_16": [row["n"] for row in prime_rows],
            "prime_power_coefficients": prime_rows,
            "cutoff": (
                "even; chi=1 for |x|<=1/4; chi=0 for |x|>=1/2; for 1/4<|x|<1/2, "
                "u=4|x|-1 and chi=exp(-1/(1-u))/(exp(-1/(1-u))+exp(-1/u))"
            ),
            "cutoff_endpoint_values": {"chi_0": "1", "chi_1_over_4": "1", "chi_1_over_2": "0"},
            "support_geometry": {
                "x_plus_a_inside_I": "a<=b-x; active only for x<=b-log(3)=log(4/3)",
                "x_minus_a_inside_I": "a<=b+x; active on all x in [0,1/2]",
                "continuum_upper_is_below_L": bool(b + radius < L),
                "prime_minus_shift_inside_I": "x>=log(n)-b=log(n/4)",
                "prime_plus_shift_on_x_nonnegative": "only n=4 at the isolated endpoint x=0; omitted from the a.e. range enclosure and contributes zero integral",
                "even_reduction": "the full x integrand is even; compute 2 times x in [0,1/2]",
            },
        },
        "ground_input": {
            "file": str(GROUND.relative_to(ROOT)),
            "sha256": sha256(GROUND),
            "source_status": source["status"],
            "selected_index_zero_based": ground["selected_index_zero_based"],
            "coordinate_source": "ground_eigenvector.interval_normalized.even_basis_coordinates and phased Fourier modes",
            "coordinate_map": normalized["map"],
            "normalized_basis_norm_squared": ball_record(xi_norm2),
            "normalized_fourier_norm_squared": ball_record(mode_norm2),
            "even_pair_difference_contains_zero": True,
            "mode_map_difference_contains_zero": True,
            "pair_difference_max_abs_upper": str(
                max((abs(value).upper() for value in pair_differences), default=arb(0))
            ),
            "sampled_phased_reconstitution": reconstitution_checks,
        },
        "analytic_continuum_primitive": {
            "theta": "theta=omega_j*(x+b+sigma*a), sigma=+1 for x+a, sigma=-1 for x-a",
            "primitive": "G_sigma=exp(a/2)*(1/2*cos(theta)+sigma*omega_j*sin(theta))/(1/4+omega_j^2)",
            "derivative_check": (
                "For sigma=+1: (1/2)*(1/2*cos+omega*sin) + d/da(1/2*cos+omega*sin) "
                "=(1/4+omega^2)*cos(theta). For sigma=-1: (1/2)*(1/2*cos-omega*sin) "
                "+ d/da(1/2*cos-omega*sin)=(1/4+omega^2)*cos(theta). Thus dG_sigma/da=exp(a/2)*cos(theta)."
            ),
            "complex_exponential_crosscheck": primitive_checks,
            "crosscheck_scope": "Arb real primitive and Arb complex-exponential primitive overlap for every mode j=0..16 and both signs at x=1/8, a=log(3)+1/16",
            "inner_integral": "sum over modes of phased coefficient times [G_sigma(x,b-sigma*x)-G_sigma(x,log(3))], with plus-shift clipping at log(4/3)",
        },
        "breakpoint_method": {
            "fixed_breaks": ["0", "1/4", "1/2"],
            "clip_breaks": "exact log breakpoints are enclosed in tiny dyadic brackets; the bracket interval is evaluated with the hull of active range and zero",
            "max_bracket_bits": BREAKPOINT_BITS,
        },
        "environment": {
            "python": platform.python_version(),
            "python_flint": getattr(__import__("flint"), "__version__", "unknown"),
            "arb_dps": DPS,
            "arb_threads": 1,
        },
        "input_sha256": {
            "ground_eigenpair_json": sha256(GROUND),
            "localize_verdict": sha256(VERDICT),
            "localize_algebra_source": sha256(ALGEBRA),
            "script": sha256(Path(__file__).resolve()),
        },
        "formula_validation": {
            "coordinate_map_and_phase": "checked against stored phased +/-j modes at x=0,1/8,1/4,1/2; every Arb difference contains zero",
            "cutoff_endpoint_handling": "exact chi=1 at 0 and 1/4, exact chi=0 at 1/2; no endpoint division by zero",
            "primitive_signs": "plus uses +omega*sin(theta); minus uses -omega*sin(theta); derivative identities written above and Arb complex-form crosschecks pass",
            "integration": "no nested numerical quadrature or mpmath certificate; one-dimensional interval-range Riemann sums enclose the integrand a.e., omitting only the isolated x=0 value, which has measure zero",
        },
        "results": [],
        "limitations": [
            "This is a direct finite-cell enclosure for F_far only. E, near shifts, and the full LOCALIZE expression are not evaluated.",
            "The interval arithmetic encloses the functional of the stored coordinate balls; the input file labels the cached eigenpair diagnostic and does not itself claim a proof certificate.",
            "The separate same-cutoff E bound is not an input to this computation; combining it with the fine F_far enclosure addresses only E+F_far on this finite cell.",
            "Near terms and remaining projection/return pieces are not paid here, so the finite negative E+F_far comparison does not establish energy descent.",
            "A single m=16 value says nothing cofinal about m tending to infinity and proves neither NOESCAPE T nor RH.",
        ],
    }

    for subdivisions in BASE_SUBDIVISIONS:
        result["results"].append(run_riemann(subdivisions))
    result["status"] = "DIRECT_LOCALIZE_FAR_M16_GROUND_INTERVAL_ENCLOSURE"
    result["runtime_seconds_total"] = round(time.monotonic() - started, 3)
    OUTPUT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "runtime_seconds_total": result["runtime_seconds_total"],
        "output": str(OUTPUT),
        "results": [
            {
                "subdivisions": row["base_subdivisions_on_half_interval"],
                "cells": row["actual_interval_cells"],
                "prime": row["raw_prime_sum_from_individual_terms"]["ball"],
                "continuum": row["continuum_integral"]["ball"],
                "joint": row["joint_direct_cell_ranges"]["ball"],
                "sign": row["joint_sign"],
                "seconds": row["seconds"],
            }
            for row in result["results"]
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
