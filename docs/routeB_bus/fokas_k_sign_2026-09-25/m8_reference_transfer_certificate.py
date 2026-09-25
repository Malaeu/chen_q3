#!/usr/bin/env python3
"""Arb reference-transfer certificate for the finite m=8 Robin rectangle.

mpmath supplies endpoint candidates only. Exact rational endpoints are
accepted only after Arb Sturm counts validate them. The selected-source tail
bound is explicitly conditional; this does not certify an actual selected
m=8 row or any cofinal statement.
"""
from __future__ import annotations

import argparse
from decimal import Decimal
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx
import mpmath as mp

import m8_negative_certificate as source
import rectangle_probe as diagnostic

PACKET = Path(__file__).resolve().parent
M = 8
N = 6 * M - 1
MODES = tuple(range(-M, M + 1))
INDEX_BY_MODE = {0: 0, 4: 2}
CANDIDATE_DPS = 160
ENDPOINT_DECIMAL_PLACES = 120
MIN_STURM_DPS = 140
REFERENCE_GROUND_ERROR = "0.05536"
TAIL_INDEX = 5 * M - 1


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def decimal_from_scaled_integer(value: int) -> str:
    scale = 10**ENDPOINT_DECIMAL_PLACES
    sign = "-" if value < 0 else ""
    whole, fractional = divmod(abs(value), scale)
    return f"{sign}{whole}.{fractional:0{ENDPOINT_DECIMAL_PLACES}d}"


def propose_rational_brackets():
    """Round eigsy candidates outward; all four endpoints need Sturm proof."""
    proposals = {}
    with mp.workdps(CANDIDATE_DPS):
        scale = mp.mpf(10) ** ENDPOINT_DECIMAL_PLACES
        candidates = diagnostic.bracket(M)
        for mode in (0, 4):
            lower_candidate, upper_candidate = candidates[mode]
            lower_decimal = decimal_from_scaled_integer(
                int(mp.floor(lower_candidate * scale))
            )
            upper_decimal = decimal_from_scaled_integer(
                int(mp.ceil(upper_candidate * scale))
            )
            lower, upper = Fraction(Decimal(lower_decimal)), Fraction(Decimal(upper_decimal))
            if not lower < upper:
                raise ArithmeticError(f"non-increasing proposed bracket for mode {mode}")
            proposals[mode] = {
                "lower": lower,
                "upper": upper,
                "lower_decimal": lower_decimal,
                "upper_decimal": upper_decimal,
                "mpmath_lower_candidate": mp.nstr(lower_candidate, n=CANDIDATE_DPS),
                "mpmath_upper_candidate": mp.nstr(upper_candidate, n=CANDIDATE_DPS),
            }
    return proposals


def certify_robin_brackets(proposals, sturm_dps: int):
    """Validate exact rational endpoints with H's Arb Sturm recurrence."""
    ctx.dps = sturm_dps
    H = source.H
    H.ctx.dps = sturm_dps
    last_edge = H.up(M, N)
    if not last_edge.upper() < 0:
        raise ArithmeticError(f"Robin endpoint coefficient is not certified negative: {last_edge}")

    checks = []
    for mode, eigenvalue_index in INDEX_BY_MODE.items():
        proposal = proposals[mode]
        lower_count, lower_signs = H.sturm_count_below(
            M, arb("0.5"), H.qball(proposal["lower"])
        )
        upper_count, upper_signs = H.sturm_count_below(
            M, arb(0), H.qball(proposal["upper"])
        )
        if (lower_count, upper_count) != (eigenvalue_index, eigenvalue_index + 1):
            raise ArithmeticError(
                f"Sturm mismatch for mode {mode}: {lower_count}, {upper_count}"
            )
        checks.append({
            "mode": mode,
            "eigenvalue_index_zero_based": eigenvalue_index,
            "lower_t": "1/2",
            "lower_endpoint_exact_decimal_rational": proposal["lower_decimal"],
            "negative_pivots_below_lower": lower_count,
            "lower_pivot_signs": lower_signs,
            "upper_t": "0",
            "upper_endpoint_exact_decimal_rational": proposal["upper_decimal"],
            "negative_pivots_below_upper": upper_count,
            "upper_pivot_signs": upper_signs,
        })
    return {
        "arb_sturm_precision_dps": sturm_dps,
        "negative_last_diagonal_perturbation_coefficient_arb": str(last_edge),
        "robin_parameter_interval": "0 <= t <= 1/2",
        "monotonicity_argument": (
            "J(t)=J(0)+t*up(8,47)*e_47*e_47^T and up(8,47)<0, so each ordered "
            "eigenvalue is nonincreasing in t; the t=1/2 lower endpoint and t=0 "
            "upper endpoint counts enclose the same index throughout the interval."
        ),
        "checks": checks,
    }


def recurrence_and_derivative(energy):
    """Enclose P_k and P'_k on an Arb energy interval, k=0..N."""
    H = source.H
    values, derivatives = [arb(1)], [arb(0)]
    for k in range(N):
        previous = values[k - 1] if k else arb(0)
        previous_derivative = derivatives[k - 1] if k else arb(0)
        diagonal, lower, upper = H.diag(M, k), H.ell(M, k), H.up(M, k)
        values.append(((energy - diagonal) * values[k] - lower * previous) / upper)
        derivatives.append(
            (values[k] + (energy - diagonal) * derivatives[k]
             - lower * previous_derivative) / upper
        )
    return values, derivatives


def vector_norm_upper(values):
    squared = sum((value.abs_upper() ** 2 for value in values), arb(0))
    return squared.sqrt().upper()


def verify_same_k_ground_certificates():
    certificates = {}
    for dps in (100, 140):
        path = PACKET / f"m8_shifted_ground_certificate_dps{dps}.json"
        payload = json.loads(path.read_text())
        if payload.get("status") != "CERTIFIED_FINITE_RATIONAL_REFERENCE_CELL_ONLY":
            raise ArithmeticError(f"unexpected same-K certificate status in {path.name}")
        if payload.get("rigorous_rational_projection_error_upper") != REFERENCE_GROUND_ERROR:
            raise ArithmeticError(f"unexpected ground-error bound in {path.name}")
        enclosure = arb(payload["ground_projection_error_upper_enclosure"])
        if not enclosure.upper() < arb(REFERENCE_GROUND_ERROR):
            raise ArithmeticError(f"ground-error enclosure not below its rational bound in {path.name}")
        # Bind each reused result to the exact inputs recorded by its producer.
        for name, expected in payload["sha256"].items():
            dependency = PACKET / name
            if sha256(dependency) != expected:
                raise ArithmeticError(f"stale dependency hash in {path.name}: {name}")
        certificates[str(dps)] = {
            "file": path.name,
            "sha256": sha256(path),
            "projection_error_enclosure_arb": payload["ground_projection_error_upper_enclosure"],
            "certified_rational_upper": REFERENCE_GROUND_ERROR,
            "strictly_below_rational_upper": True,
        }
    return certificates


def run_certificate(dps: int):
    if dps not in (100, 140):
        raise ValueError("the requested output precisions are 100 and 140 dps")

    proposals = propose_rational_brackets()
    sturm = certify_robin_brackets(proposals, max(dps, MIN_STURM_DPS))

    # The reference center is fixed by m8_negative_certificate.py. Its state
    # gives the same exact rational K, normalized source vector, and z center
    # used by the already certified 0.05536 same-K ground estimate.
    state = source.build_source_state(dps)
    ctx.dps = dps
    H = source.H
    H.ctx.dps = dps
    centers = {
        0: Fraction(Decimal(source.E0_DECIMAL)),
        4: Fraction(Decimal(source.E4_DECIMAL)),
    }
    energy_intervals, radii = {}, {}
    for mode in (0, 4):
        proposal = proposals[mode]
        center = centers[mode]
        if not proposal["lower"] <= center <= proposal["upper"]:
            raise ArithmeticError(f"fixed reference center is outside mode-{mode} bracket")
        energy_intervals[mode] = H.qball(proposal["lower"]).union(H.qball(proposal["upper"]))
        radii[mode] = H.qball(max(
            abs(center - proposal["lower"]), abs(proposal["upper"] - center)
        ))

    recurrence = {mode: recurrence_and_derivative(energy_intervals[mode]) for mode in (0, 4)}
    partial_0, partial_4 = [], []
    for row in state["F"]:
        partial_0.append(sum((
            row[k - 1] * ((-1) ** k) * recurrence[0][1][k]
            for k in range(1, N + 1)
        ), acb(0)))
        partial_4.append(sum((
            -row[k - 1] * ((-1) ** k) * recurrence[4][1][k]
            for k in range(1, N + 1)
        ), acb(0)))

    derivative_norm_0 = vector_norm_upper(partial_0)
    derivative_norm_4 = vector_norm_upper(partial_4)
    energy_error = (
        radii[0] * derivative_norm_0 + radii[4] * derivative_norm_4
    ).upper()

    # This is the requested selected-source tail expression. Its use is
    # conditional on the geometric selected-source hypothesis below threshold.
    p0, p4 = recurrence[0][0], recurrence[4][0]
    tail_factor = (
        arb(M) * (arb(M).sqrt() - 1 / arb(M).sqrt())
    ).sqrt() * arb(2) ** (-M)
    tail_error = (
        tail_factor * (p0[TAIL_INDEX].abs_upper() + p4[TAIL_INDEX].abs_upper())
    ).upper()
    total_error = (energy_error + tail_error).upper()

    z_norm = state["z_norm2"].sqrt().upper()
    z_mode0_lower = state["z"][M].abs_lower().lower()
    denominator_lower = (z_mode0_lower - total_error).lower()
    if not denominator_lower > 0:
        raise ArithmeticError(f"transfer denominator is not positive: {denominator_lower}")
    numerator_upper = (
        z_norm * arb(REFERENCE_GROUND_ERROR) + total_error
    ).upper()
    transfer_upper = (numerator_upper / denominator_lower).upper()

    ground_certificates = verify_same_k_ground_certificates()
    dependency_paths = [
        Path(__file__),
        PACKET / "m8_negative_certificate.py",
        PACKET / "arb_m2_certificate.py",
        PACKET / "rectangle_probe.py",
        PACKET / "m8_shifted_ground_certificate.py",
        PACKET / "m8_shifted_ground_certificate_dps100.json",
        PACKET / "m8_shifted_ground_certificate_dps140.json",
        PACKET / "schur_probe_m8_dps140.json",
    ]

    result = {
        "status": "CERTIFIED_FINITE_M8_REFERENCE_TRANSFER_CONDITIONAL_ON_TAIL_ASSUMPTIONS",
        "m": M,
        "precision_dps": dps,
        "scope": {
            "certified": (
                "rational Robin brackets for eigenvalue indices 0 and 2 over t in [0,1/2], "
                "an Arb uniform bound from the exact m8_negative_certificate reference z center "
                "to every finite prefix z in the product rectangle, and the stated conditional "
                "full-row transfer inequality"
            ),
            "tail_condition": (
                "The geometric selected-source hypothesis required by this tail estimate is not "
                "established at m=8, which is below the applicable source threshold; E_tail is a "
                "conditional number only, not a tail bound asserted for an actual selected m=8 row"
            ),
            "not_claimed": [
                "that m=8 is an actual selected source row or satisfies the selected-source tail hypothesis",
                "any cofinal or source-family conclusion",
                "Goal058 tracking, real-zero convergence, or RH",
            ],
        },
        "candidate_generation": {
            "source": "rectangle_probe.bracket via mpmath eigsy",
            "mpmath_precision_dps": CANDIDATE_DPS,
            "endpoint_rounding": f"outward to {ENDPOINT_DECIMAL_PLACES} decimal places",
            "role": "candidate proposal only; the Arb Sturm counts below validate each exact rational endpoint",
            "candidates": {
                str(mode): {
                    "lower_at_t_half": proposals[mode]["mpmath_lower_candidate"],
                    "upper_at_t_zero": proposals[mode]["mpmath_upper_candidate"],
                } for mode in (0, 4)
            },
        },
        "robin_brackets": sturm,
        "reference_center": {
            "source": "exact rational decimal constants in m8_negative_certificate.py",
            "E0": source.E0_DECIMAL,
            "E4": source.E4_DECIMAL,
            "z_norm_arb_upper": str(z_norm),
            "abs_z_mode0_arb_lower": str(z_mode0_lower),
        },
        "uniform_transfer": {
            "derivative_interval_method": (
                "Arb recurrence for P_k and P'_k on each full rational energy bracket; "
                "coordinatewise derivative vector norms are integrated over the exact "
                "center-to-endpoint radii"
            ),
            "sup_norm_dz_dE0_arb_upper": str(derivative_norm_0),
            "sup_norm_dz_dE4_arb_upper": str(derivative_norm_4),
            "E_energy_arb_upper": str(energy_error),
            "tail_index_5m_minus_1": TAIL_INDEX,
            "tail_formula": (
                "sqrt(m*(sqrt(m)-1/sqrt(m)))*2^(-m)*"
                "(|P0[5m-1]|+|P4[5m-1]|)"
            ),
            "E_tail_arb_upper_conditional": str(tail_error),
            "E_total_arb_upper_conditional": str(total_error),
            "same_K_ground_error_certificates": ground_certificates,
            "transfer_formula": "(||zcenter||*0.05536+E_total)/(|zcenter[mode0]|-E_total)",
            "transfer_denominator_arb_lower": str(denominator_lower),
            "transfer_denominator_strictly_positive": True,
            "transfer_bound_arb_upper_conditional": str(transfer_upper),
            "interpretation": (
                "T2 upper bound for ||(I-P0)b||/|b0|; multiply by |Xi(0)|*8^(H/2) "
                "for normalized transform error; not a unit-row projection-angle bound. "
                "It applies conditionally to full rows whose prefix lies in this rectangle "
                "and whose omitted-tail norm is at most E_tail."
            ),
        },
        "sha256": {path.name: sha256(path) for path in dependency_paths},
    }
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", type=int, choices=(100, 140), default=100)
    args = parser.parse_args()
    result = run_certificate(args.dps)
    output = PACKET / f"m8_reference_transfer_certificate_dps{args.dps}.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print(f"WROTE {output}")


if __name__ == "__main__":
    main()
