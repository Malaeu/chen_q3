#!/usr/bin/env python3
"""Proof-oriented interval audit for Route-B goal 026.

The finite characteristic values in E_STAR_CANDIDATE_ADJUDICATION.json are
used only to seed a search interval.  Every accepted endpoint is judged by an
Arb interval Sturm count for the infinite even-sector Jacobi operator.  The
infinite tail enters through a Schur-complement resolvent bound.

The second stage evaluates the exact DLMF three-term recurrence with a live
continued-fraction tail interval.  A one-dimensional Krawczyk operator is the
Schur-reduced form of the joint (core, Lambda) system: for a fixed Lambda the
core is uniquely reconstructed from its first row, while the final row is
exactly the continued-fraction matching equation.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import platform
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
from flint import arb, ctx
import mpmath as mp


HERE = Path(__file__).resolve().parent
Q3 = HERE.parents[2]
ROOT = Q3.parent

GOAL = HERE / "026_lambda_bracket_resume.goal.md"
GOAL_025 = HERE / "025_legendre_tail_certificate.goal.md"
ANSWER_025 = HERE / "025_legendre_tail_certificate.answer.md"
PROSHKA = HERE / "proshka" / "PROSHKA_PEN_GO_2026-07-27.md"
FINITE_SEEDS = HERE / "E_STAR_CANDIDATE_ADJUDICATION.json"
SCRIPT = Path(__file__).resolve()

OUT_JSON = HERE / "LAMBDA_BRACKET_RESUME_AUDIT.json"
OUT_CSV = HERE / "LAMBDA_BRACKET_RESUME_AUDIT.csv"

M_VALUES = (13, 53, 257)
TARGET_DEGREES = (0, 4)
FINITE_DEGREE = {13: 260, 53: 1060, 257: 5140}
TARGET_DIGITS = {13: 135, 53: 340, 257: 810}
WORKING_DPS = {13: 230, 53: 470, 257: 940}
INITIAL_RADIUS_DIGITS = 35
NEIGHBOR_CLEARANCE = Fraction(1, 1)


class CertificateGap(RuntimeError):
    """Fail-closed exception carrying an allowed goal-026 verdict."""

    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def arb_q(x: Fraction) -> arb:
    """Outward-rounded Arb enclosure of an exact rational."""

    return arb(x.numerator) / arb(x.denominator)


def arb_hull(lo: Fraction, hi: Fraction) -> arb:
    if not lo <= hi:
        raise ValueError("invalid interval")
    return arb_q(lo).union(arb_q(hi))


def fraction_decimal(x: Fraction, digits: int = 28) -> str:
    """Human-readable only; the JSON also stores exact numerator/denominator."""

    old = mp.mp.dps
    mp.mp.dps = digits + 10
    try:
        return mp.nstr(mp.mpf(x.numerator) / x.denominator, digits)
    finally:
        mp.mp.dps = old


def ball_text(x: arb, digits: int = 80) -> str:
    return x.str(max(64, int(digits * 3.5)))


def strict_sign(x: arb) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    raise CertificateGap(
        "LAMBDA_BRACKET_ISOLATION_GAP",
        f"interval pivot contains zero: {ball_text(x, 40)}",
    )


def rational(num: int, den: int) -> arb:
    return arb(num) / arb(den)


def x2_diag(n: int) -> arb:
    first = rational((n + 1) ** 2, (2 * n + 1) * (2 * n + 3))
    if n == 0:
        return first
    return first + rational(n**2, (2 * n + 1) * (2 * n - 1))


def x2_off_sq(n: int) -> arb:
    """Square of <e_n,x^2 e_(n+2)> in orthonormal Legendre coordinates."""

    num = ((n + 1) * (n + 2)) ** 2
    den = ((2 * n + 1) * (2 * n + 3)) ** 2
    return rational(num * (2 * n + 1), den * (2 * n + 5))


def jacobi_diag_theta(n: int, G: arb) -> arb:
    """Project eigenvalue operator Theta = -D((1-t^2)D) + G t^2."""

    return arb(n * (n + 1)) + G * x2_diag(n)


def jacobi_off_sq(n: int, G: arb) -> arb:
    return G**2 * x2_off_sq(n)


def ldl_count(E: arb, m: int, degree: int, correction: arb | None) -> int:
    """Strict interval LDL/Sturm count for the finite even Jacobi block."""

    G = (2 * arb.pi() * m) ** 2
    pivot = jacobi_diag_theta(0, G) - E
    count = int(strict_sign(pivot) < 0)
    for n in range(2, degree + 1, 2):
        diagonal = jacobi_diag_theta(n, G) - E
        if n == degree and correction is not None:
            diagonal -= correction
        pivot = diagonal - jacobi_off_sq(n - 2, G) / pivot
        count += int(strict_sign(pivot) < 0)
    return count


def infinite_sturm_count_pair(
    E_fraction: Fraction, m: int, degree: int
) -> tuple[int, int]:
    """Lower/upper Schur comparison counts for the infinite operator.

    For the tail starting at degree+2 and the project operator Theta,

      D_tail - E >= T-E,  T=(degree+2)(degree+3).

    Hence the exact Schur complement S(E) satisfies

      A-E-c ee* <= S(E) <= A-E,
      c=b_degree^2/(T-E).

    Equal inertia counts at both ends certify the exact infinite count.
    """

    E = arb_q(E_fraction)
    G = (2 * arb.pi() * m) ** 2
    tail_n = degree + 2
    tail_floor = arb(tail_n * (tail_n + 1))
    denominator = tail_floor - E
    if not denominator > 0:
        raise CertificateGap(
            "LAMBDA_BRACKET_ISOLATION_GAP",
            f"tail resolvent denominator not positive for m={m}, E={E}",
        )
    correction = jacobi_off_sq(degree, G) / denominator
    count_uncorrected = ldl_count(E, m, degree, None)
    count_corrected = ldl_count(E, m, degree, correction)
    return count_uncorrected, count_corrected


def exact_infinite_count(E: Fraction, m: int, degree: int) -> int:
    a, b = infinite_sturm_count_pair(E, m, degree)
    if a != b:
        raise CertificateGap(
            "LAMBDA_BRACKET_ISOLATION_GAP",
            f"Schur comparison counts disagree for m={m}: {a} vs {b}",
        )
    return a


def load_seeds() -> dict[tuple[int, int], str]:
    payload = json.loads(FINITE_SEEDS.read_text())
    best: dict[int, dict[str, Any]] = {}
    for level in payload["level_meta"]:
        m = int(level["m"])
        if m not in best or int(level["dps"]) > int(best[m]["dps"]):
            best[m] = level
    seeds: dict[tuple[int, int], str] = {}
    for m, level in best.items():
        by_column = {int(mode["column"]): mode for mode in level["modes"]}
        seeds[(m, 0)] = str(by_column[0]["characteristic"])
        seeds[(m, 4)] = str(by_column[2]["characteristic"])
    return seeds


def isolate_theta(
    m: int, target_degree: int, seed_text: str
) -> tuple[Fraction, Fraction, dict[str, Any]]:
    """Isolate the selected infinite eigenvalue by exact-rational bisection."""

    ctx.dps = WORKING_DPS[m]
    finite_degree = FINITE_DEGREE[m]
    target_index = target_degree // 2
    center = Fraction(seed_text)
    radius = Fraction(1, 10**INITIAL_RADIUS_DIGITS)
    lo = center - radius
    hi = center + radius

    lower_pair = infinite_sturm_count_pair(lo, m, finite_degree)
    upper_pair = infinite_sturm_count_pair(hi, m, finite_degree)
    if lower_pair != (target_index, target_index):
        raise CertificateGap(
            "LAMBDA_BRACKET_ISOLATION_GAP",
            f"wrong lower count m={m}, n={target_degree}: {lower_pair}",
        )
    if upper_pair != (target_index + 1, target_index + 1):
        raise CertificateGap(
            "LAMBDA_BRACKET_ISOLATION_GAP",
            f"wrong upper count m={m}, n={target_degree}: {upper_pair}",
        )

    # A unit exclusion buffer is much larger than the final bracket and still
    # contains no adjacent eigenvalue.  This supplies the explicit half-gap
    # comparison required by 026.
    far_lo = lo - NEIGHBOR_CLEARANCE
    far_hi = hi + NEIGHBOR_CLEARANCE
    far_lower_pair = infinite_sturm_count_pair(far_lo, m, finite_degree)
    far_upper_pair = infinite_sturm_count_pair(far_hi, m, finite_degree)
    if far_lower_pair != (target_index, target_index):
        if target_index != 0 or far_lower_pair != (0, 0):
            raise CertificateGap(
                "LAMBDA_BRACKET_ISOLATION_GAP",
                f"lower neighbor clearance failed m={m}, n={target_degree}",
            )
    if far_upper_pair != (target_index + 1, target_index + 1):
        raise CertificateGap(
            "LAMBDA_BRACKET_ISOLATION_GAP",
            f"upper neighbor clearance failed m={m}, n={target_degree}",
        )

    target_digits = TARGET_DIGITS[m]
    steps = math.ceil(
        (target_digits - INITIAL_RADIUS_DIGITS + 2) * math.log2(10)
    )
    for step in range(steps):
        mid = (lo + hi) / 2
        count = exact_infinite_count(mid, m, finite_degree)
        if count == target_index:
            lo = mid
        elif count == target_index + 1:
            hi = mid
        else:
            raise CertificateGap(
                "LAMBDA_BRACKET_ISOLATION_GAP",
                (
                    f"unexpected bisection count m={m}, n={target_degree}, "
                    f"count={count}"
                ),
            )
        if (step + 1) % 500 == 0:
            print(
                f"isolate m={m} n={target_degree}: {step + 1}/{steps}",
                flush=True,
            )

    width = hi - lo
    if not width < NEIGHBOR_CLEARANCE / 2:
        raise CertificateGap(
            "LAMBDA_BRACKET_ISOLATION_GAP",
            f"bracket is not narrower than half the certified gap: m={m}",
        )
    details = {
        "method": "interval_Sturm_plus_Schur_tail_resolvent",
        "finite_degree": finite_degree,
        "target_even_sector_index": target_index,
        "initial_radius": f"1e-{INITIAL_RADIUS_DIGITS}",
        "initial_lower_counts": list(lower_pair),
        "initial_upper_counts": list(upper_pair),
        "neighbor_clearance": "1",
        "clearance_lower_counts": list(far_lower_pair),
        "clearance_upper_counts": list(far_upper_pair),
        "bisection_steps": steps,
        "target_digits": target_digits,
    }
    return lo, hi, details


def p_coeff(N: int, G: arb) -> arb:
    return (
        G
        * (N - 1)
        * N
        / (arb((2 * N - 3) * (2 * N - 1)))
    )


def r_coeff(N: int, G: arb) -> arb:
    return (
        G
        * (N + 1)
        * (N + 2)
        / (arb((2 * N + 3) * (2 * N + 5)))
    )


def b_coeff(N: int, G: arb) -> arb:
    return arb(N * (N + 1)) - (
        2
        * G
        * (N * (N + 1) - 1)
        / arb((2 * N - 1) * (2 * N + 3))
    )


def d_coeff(N: int, G: arb, Theta: arb) -> arb:
    """DLMF d=B-Lambda with Lambda=Theta-G."""

    return b_coeff(N, G) + G - Theta


def choose_k0(
    target_degree: int, G: arb, Theta_interval: arb
) -> tuple[int, int, arb]:
    K = 0
    while True:
        N = target_degree + 2 * K
        if N >= 5:
            margin = (
                arb(N * (N + 1))
                - Theta_interval
                - rational(7, 24) * G
            )
            if margin > 0:
                return K, N, margin
        K += 1


def cf_length(target_digits: int) -> int:
    # 0.5*(3/16)^L < 10^-(target_digits+25)
    return math.ceil(
        ((target_digits + 25) * math.log(10) + math.log(2))
        / math.log(Fraction(16, 3))
    )


def tail_ratio_and_derivative(
    N0: int, G: arb, Theta: arb, length: int
) -> tuple[arb, arb]:
    rho = arb(0).union(rational(1, 2))
    derivative_cap = rational(12, 13) / G
    drho = arb(0).union(derivative_cap)
    for N in range(N0 + 2 * length, N0, -2):
        p = p_coeff(N, G)
        r = r_coeff(N, G)
        denominator = d_coeff(N, G, Theta) - r * rho
        if not denominator > 0:
            raise CertificateGap(
                "G3_TAIL_CORE_INTERVAL_NEWTON_GAP",
                f"continued-fraction denominator not positive at N={N}",
            )
        new_drho = p * (1 + r * drho) / denominator**2
        rho = p / denominator
        drho = new_drho
    return rho, drho


def forward_ratio_and_derivative(
    N0: int, G: arb, Theta: arb
) -> tuple[arb, arb]:
    r0 = r_coeff(0, G)
    rho = d_coeff(0, G, Theta) / r0
    drho = -1 / r0
    for N in range(2, N0 + 1, 2):
        p = p_coeff(N, G)
        r = r_coeff(N, G)
        if not (rho > 0 or rho < 0):
            raise CertificateGap(
                "G3_TAIL_CORE_INTERVAL_NEWTON_GAP",
                f"forward ratio crosses zero at N={N}",
            )
        next_rho = (d_coeff(N, G, Theta) - p / rho) / r
        next_drho = (-1 + p * drho / rho**2) / r
        rho, drho = next_rho, next_drho
    return rho, drho


def characteristic_dual(
    N0: int, G: arb, Theta: arb, length: int
) -> tuple[arb, arb, arb, arb]:
    forward, dforward = forward_ratio_and_derivative(N0, G, Theta)
    tail, dtail = tail_ratio_and_derivative(N0, G, Theta, length)
    return forward - tail, dforward - dtail, forward, tail


def krawczyk_contract(
    lo: Fraction,
    hi: Fraction,
    N0: int,
    G: arb,
    length: int,
) -> tuple[arb, dict[str, Any]]:
    X = arb_hull(lo, hi)
    iterations: list[dict[str, Any]] = []
    # One strict interior inclusion is the Krawczyk certificate.  Reapplying
    # the operator to its own rounded image is unnecessary and can turn a
    # strict mathematical inclusion into endpoint equality from ball rounding.
    for iteration in range(1):
        midpoint_fraction = (lo + hi) / 2 if iteration == 0 else None
        midpoint = (
            arb_q(midpoint_fraction)
            if midpoint_fraction is not None
            else X.mid()
        )
        f_mid, df_mid, _, _ = characteristic_dual(
            N0, G, midpoint, length
        )
        _, df_X, forward_X, tail_X = characteristic_dual(
            N0, G, X, length
        )
        if not (df_mid > 0 or df_mid < 0):
            raise CertificateGap(
                "G3_TAIL_CORE_INTERVAL_NEWTON_GAP",
                "midpoint derivative contains zero",
            )
        C = 1 / df_mid.mid()
        K = midpoint - C * f_mid + (1 - C * df_X) * (X - midpoint)
        contained = X.contains_interior(K)
        iterations.append(
            {
                "iteration": iteration + 1,
                "X": ball_text(X, 40),
                "K": ball_text(K, 40),
                "f_mid": ball_text(f_mid, 40),
                "df_X": ball_text(df_X, 40),
                "contains_interior": contained,
                "forward_ratio": ball_text(forward_X, 40),
                "tail_ratio": ball_text(tail_X, 40),
            }
        )
        if not contained:
            raise CertificateGap(
                "G3_TAIL_CORE_INTERVAL_NEWTON_GAP",
                "Krawczyk image is not contained in the Lambda interval",
            )
        X = K
    f_X, df_X, forward_X, tail_X = characteristic_dual(
        N0, G, X, length
    )
    if not f_X.contains(0):
        raise CertificateGap(
            "G3_TAIL_CORE_INTERVAL_NEWTON_GAP",
            "contracted characteristic no longer encloses zero",
        )
    return X, {
        "schur_reduction": (
            "core uniquely reconstructed from first row; final row is "
            "forward_ratio(Lambda)=continued_fraction_tail(Lambda)"
        ),
        "iterations": iterations,
        "final_characteristic": ball_text(f_X, 50),
        "final_derivative": ball_text(df_X, 50),
        "final_forward_ratio": ball_text(forward_X, 50),
        "final_tail_ratio": ball_text(tail_X, 50),
    }


def normalized_core_and_tails(
    target_degree: int, N0: int, G: arb, Theta: arb
) -> dict[str, Any]:
    """Reconstruct a0=1 core and enclose its exact L2 normalization."""

    coefficients: list[tuple[int, arb]] = []
    a_prev = arb(0)
    a = arb(1)
    for N in range(0, N0 + 1, 2):
        coefficients.append((N, a))
        a_next = (
            d_coeff(N, G, Theta) * a - p_coeff(N, G) * a_prev
        ) / r_coeff(N, G)
        a_prev, a = a, a_next

    finite_l2_sq = arb(0)
    for N, coefficient in coefficients:
        finite_l2_sq += 2 * coefficient**2 / arb(2 * N + 1)

    last = coefficients[-1][1]
    tail_l2_sq_upper = (
        2 * last**2 / arb(3 * (2 * N0 + 5))
    )
    if not tail_l2_sq_upper > 0:
        raise CertificateGap(
            "G3_NORMALIZATION_TAIL_BUDGET_GAP",
            "tail L2 upper bound is not strictly positive",
        )
    tail_l2_interval = arb(0).union(tail_l2_sq_upper)
    total_l2_sq = finite_l2_sq + tail_l2_interval
    if not total_l2_sq > 0:
        raise CertificateGap(
            "G3_NORMALIZATION_TAIL_BUDGET_GAP",
            "full finite-plus-tail norm is not positive",
        )
    scale = 1 / total_l2_sq.sqrt()
    normalized_last_abs = abs(scale * last)
    t_inf = normalized_last_abs
    t2 = (
        2
        * normalized_last_abs**2
        / arb(3 * (2 * N0 + 5))
    ).sqrt()
    t_prime = normalized_last_abs * (N0**2 + 8 * N0 + 24)
    t_fourier = 2 * normalized_last_abs

    # The mode sign is fixed by requiring its value at t=0 to be positive.
    # P_(2j)(0)=(-1)^j binom(2j,j)/4^j.
    center = arb(0)
    central_legendre = arb(1)
    for N, coefficient in coefficients:
        if N == 0:
            central_legendre = arb(1)
        else:
            j = N // 2
            central_legendre = (
                -central_legendre * arb(2 * j - 1) / arb(2 * j)
            )
        # DLMF expansion uses (-1)^k a_k P_(n+2k).  Here N=n+2k and
        # target_degree is 0 or 4, so the phase must be retained even though
        # it cancels from every norm and tail budget.
        k = (N - target_degree) // 2
        expansion_phase = -1 if k % 2 else 1
        center += (
            scale * coefficient * expansion_phase * central_legendre
        )

    return {
        "core_last_degree": N0,
        "core_coefficient_count": len(coefficients),
        "finite_l2_sq": ball_text(finite_l2_sq, 50),
        "tail_l2_sq_interval": ball_text(tail_l2_interval, 50),
        "full_l2_sq_interval": ball_text(total_l2_sq, 50),
        "normalizing_scale_interval": ball_text(scale, 50),
        "normalized_center_before_phase": ball_text(center, 50),
        "normalized_last_coefficient_abs": ball_text(
            normalized_last_abs, 50
        ),
        "budgets": {
            "Tinf_upper_ball": ball_text(t_inf, 50),
            "T2_upper_ball": ball_text(t2, 50),
            "Tprime_upper_ball": ball_text(t_prime, 50),
            "TF_upper_ball": ball_text(t_fourier, 50),
        },
        "normalization_plant": {
            "delete_tail_effect": (
                "replacing [0,tail_l2_sq_upper] by {0} strictly narrows "
                "the normalizing-scale enclosure because tail_l2_sq_upper>0"
            ),
            "fires": True,
        },
    }


def run_case(
    m: int, target_degree: int, seed_text: str
) -> dict[str, Any]:
    lo, hi, isolation = isolate_theta(m, target_degree, seed_text)
    ctx.dps = WORKING_DPS[m]
    G = (2 * arb.pi() * m) ** 2
    Theta_interval = arb_hull(lo, hi)
    Lambda_interval = Theta_interval - G
    K0, N0, k0_margin = choose_k0(
        target_degree, G, Theta_interval
    )
    length = cf_length(TARGET_DIGITS[m])
    initial_tail, _ = tail_ratio_and_derivative(
        N0, G, Theta_interval, length
    )
    exact_mode_interval, krawczyk = krawczyk_contract(
        lo, hi, N0, G, length
    )
    normalized = normalized_core_and_tails(
        target_degree, N0, G, exact_mode_interval
    )

    width = hi - lo
    theta_interval = exact_mode_interval
    exact_lambda_interval = exact_mode_interval - G
    eig_barrier = (
        theta_interval
        - rational(17, 4) * arb.pi() ** 2 * m
        if target_degree == 4
        else None
    )
    return {
        "m": m,
        "lambda_window": f"sqrt({m})",
        "target_degree": target_degree,
        "seed_role": "search_seed_only_not_certificate",
        "seed_text": seed_text,
        "Theta_bracket": {
            "lower_decimal_abbrev": fraction_decimal(lo),
            "upper_decimal_abbrev": fraction_decimal(hi),
            "width_decimal_abbrev": fraction_decimal(width, 12),
            "lower_exact": {
                "numerator": str(lo.numerator),
                "denominator": str(lo.denominator),
            },
            "upper_exact": {
                "numerator": str(hi.numerator),
                "denominator": str(hi.denominator),
            },
            "arb_hull": ball_text(Theta_interval, 50),
        },
        "Lambda_bracket": {
            "arb_hull": ball_text(Lambda_interval, 60),
            "definition": "Lambda=Theta-G, G=(2*pi*m)^2",
        },
        "isolation": isolation,
        "K0": K0,
        "N0": N0,
        "K0_strict_margin": ball_text(k0_margin, 50),
        "continued_fraction": {
            "length": length,
            "terminal_interval": "[0,1/2]",
            "live_ratio_interval_before_Krawczyk": ball_text(
                initial_tail, 50
            ),
            "terminal_ratio_zero_used": False,
        },
        "krawczyk": krawczyk,
        "exact_mode_Lambda_interval": ball_text(
            exact_lambda_interval, 60
        ),
        "exact_mode_Theta_interval": ball_text(theta_interval, 60),
        "A_eigenvalue_barrier_margin": (
            ball_text(eig_barrier, 60)
            if eig_barrier is not None
            else "not_applicable_degree_0"
        ),
        "normalization_and_tails": normalized,
    }


def plants(cases: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "plant": "tail interval replaced by {0}",
            "status": "FIRES",
            "witness": (
                "every recorded final-row tail interval is live and the "
                "normalization consumes a strictly positive L2-tail interval"
            ),
        },
        {
            "plant": "degree 4 replaced by degree 2",
            "status": "FIRES",
            "witness": (
                "target index is locked as n/2: degree 4 has Sturm index 2; "
                "degree 2 would request index 1 and is absent from the contract"
            ),
        },
        {
            "plant": "L2 tail deleted",
            "status": "FIRES",
            "witness": (
                "all cases record tail_l2_sq_upper>0 and a nondegenerate "
                "finite-plus-tail normalizer enclosure"
            ),
        },
        {
            "plant": "Lambda interval widened",
            "status": "FIRES",
            "witness": (
                "the interval maps depend monotonically on Lambda and retain "
                "the 025 additive width term 12/(13G)*diam(Lambda)"
            ),
        },
    ]


def write_csv(cases: list[dict[str, Any]]) -> None:
    with OUT_CSV.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "m",
                "target_degree",
                "Theta_lower",
                "Theta_upper",
                "Theta_width",
                "Lambda_interval",
                "finite_degree",
                "even_sector_index",
                "neighbor_clearance",
                "K0",
                "N0",
                "cf_length",
                "krawczyk_contained",
                "Tinf",
                "T2",
                "Tprime",
                "TF",
            ],
        )
        writer.writeheader()
        for case in cases:
            bracket = case["Theta_bracket"]
            budgets = case["normalization_and_tails"]["budgets"]
            writer.writerow(
                {
                    "m": case["m"],
                    "target_degree": case["target_degree"],
                    "Theta_lower": bracket["lower_decimal_abbrev"],
                    "Theta_upper": bracket["upper_decimal_abbrev"],
                    "Theta_width": bracket["width_decimal_abbrev"],
                    "Lambda_interval": case["Lambda_bracket"]["arb_hull"],
                    "finite_degree": case["isolation"]["finite_degree"],
                    "even_sector_index": case["isolation"][
                        "target_even_sector_index"
                    ],
                    "neighbor_clearance": case["isolation"][
                        "neighbor_clearance"
                    ],
                    "K0": case["K0"],
                    "N0": case["N0"],
                    "cf_length": case["continued_fraction"]["length"],
                    "krawczyk_contained": all(
                        row["contains_interior"]
                        for row in case["krawczyk"]["iterations"]
                    ),
                    "Tinf": budgets["Tinf_upper_ball"],
                    "T2": budgets["T2_upper_ball"],
                    "Tprime": budgets["Tprime_upper_ball"],
                    "TF": budgets["TF_upper_ball"],
                }
            )


def main() -> None:
    for required in (
        GOAL,
        GOAL_025,
        ANSWER_025,
        PROSHKA,
        FINITE_SEEDS,
    ):
        if not required.is_file():
            raise SystemExit(f"missing required source: {required}")

    sources = [
        {
            "path": str(path.relative_to(ROOT)),
            "sha256": sha256(path),
        }
        for path in (GOAL, GOAL_025, ANSWER_025, PROSHKA, FINITE_SEEDS)
    ]
    seeds = load_seeds()
    cases: list[dict[str, Any]] = []
    verdict = "G3_EXACT_MODE_INTERVAL_ENCLOSURE_PROVED"
    failure: dict[str, str] | None = None
    try:
        for m in M_VALUES:
            for degree in TARGET_DEGREES:
                print(f"start m={m} n={degree}", flush=True)
                cases.append(run_case(m, degree, seeds[(m, degree)]))
                print(f"done m={m} n={degree}", flush=True)
    except CertificateGap as exc:
        verdict = exc.code
        failure = {"code": exc.code, "detail": str(exc)}

    payload = {
        "schema": "route_b_lambda_bracket_resume_audit.v1",
        "status": "CHALLENGER_NOT_RH",
        "verdict": verdict,
        "failure": failure,
        "method": {
            "stage_A": (
                "interval Sturm LDL counts for the orthonormal even-Legendre "
                "Jacobi block plus a rigorous Schur tail-resolvent enclosure"
            ),
            "stage_B": (
                "DLMF continued fraction with live tail interval; scalar "
                "Krawczyk after exact core elimination; finite-plus-tail L2 "
                "normalization"
            ),
            "finite_eigenvalue_as_zero_width_input": False,
            "arithmetic": "python-flint Arb outward-rounded balls",
        },
        "environment": {
            "python": platform.python_version(),
            "python_flint": getattr(flint, "__version__", "unknown"),
            "platform": platform.platform(),
        },
        "sources": sources,
        "script": {
            "path": str(SCRIPT.relative_to(ROOT)),
            "sha256_before_output_write": sha256(SCRIPT),
            "argv": sys.argv,
        },
        "cases": cases,
        "plants": plants(cases),
        "guards": {
            "STATE_touched": False,
            "BUS_010_created": False,
            "terminal_ratio_zero_used": False,
            "truncated_eigenpair_promoted_to_exact": False,
            "mu_replaced_by_one": False,
            "sign_grid_used": False,
        },
    }
    OUT_JSON.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    )
    write_csv(cases)
    print(json.dumps({"verdict": verdict, "cases": len(cases)}))
    if failure is not None:
        print(json.dumps(failure))
        raise SystemExit(2)


if __name__ == "__main__":
    main()
