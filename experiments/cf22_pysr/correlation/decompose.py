#!/usr/bin/env python3
"""Reconstruct the frozen nonunit CF22 panel from saved pair matrices.

This is a finite diagnostic. It reuses the stored raw ``pair_2re`` matrices
and evaluates only the small physical rho sums; it never calls ``raw_sums`` or
the native periodic counter.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib
import json
import platform
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import subprocess
import sys
from typing import Any

from flint import arb, ctx


CORRELATION_DIR = Path(__file__).resolve().parent
EXPERIMENT_DIR = CORRELATION_DIR.parent
NONUNIT_DIR = EXPERIMENT_DIR / "nonunit"
REPO = CORRELATION_DIR.parents[2]
PINNED_COMMIT = "f1993ec6a7933418c38c305a13a3221037b9447a"
PANEL_SCHEMA = "cf22-nonunit-evaluation-v1"
OUTPUT_SCHEMA = "cf22-nonunit-pair-decomposition-v1"

PINNED_INPUT_PATHS = (
    "experiments/cf22_pysr/evaluate.py",
    "experiments/cf22_pysr/nonunit/evaluate_nonunit.py",
    "experiments/cf22_pysr/nonunit/periodic.py",
    "experiments/cf22_pysr/nonunit/periodic_counter.cpp",
    "experiments/cf22_pysr/nonunit/plan.json",
    "experiments/cf22_pysr/nonunit/heldout_freeze.json",
    "experiments/cf22_pysr/nonunit/main.json",
    "experiments/cf22_pysr/nonunit/heldout.json",
)


def _git(args: list[str]) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=REPO, text=True, stderr=subprocess.PIPE
    ).strip()


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git_blob(commit: str, relative_path: str) -> str:
    return _git(["rev-parse", f"{commit}:{relative_path}"])


def verify_pinned_inputs() -> dict[str, dict[str, str]]:
    """Require all mathematical code and frozen panel data to match Git blobs."""
    _git(["cat-file", "-e", f"{PINNED_COMMIT}^{{commit}}"])
    manifest: dict[str, dict[str, str]] = {}
    for relative_path in PINNED_INPUT_PATHS:
        active_path = REPO / relative_path
        if not active_path.is_file():
            raise FileNotFoundError(active_path)
        pinned_bytes = subprocess.check_output(
            ["git", "show", f"{PINNED_COMMIT}:{relative_path}"],
            cwd=REPO,
            stderr=subprocess.PIPE,
        )
        active_bytes = active_path.read_bytes()
        if active_bytes != pinned_bytes:
            raise ValueError(
                f"pinned input differs from {PINNED_COMMIT}:{relative_path}"
            )
        manifest[relative_path] = {
            "git_blob": _git_blob(PINNED_COMMIT, relative_path),
            "sha256": _sha256_bytes(active_bytes),
        }
    return manifest


@lru_cache(maxsize=1)
def _modules() -> tuple[Any, Any]:
    if str(EXPERIMENT_DIR) not in sys.path:
        sys.path.insert(0, str(EXPERIMENT_DIR))
    source = importlib.import_module("evaluate")
    if Path(source.__file__).resolve() != (EXPERIMENT_DIR / "evaluate.py").resolve():
        raise ImportError("evaluate resolved outside the frozen CF22 source")
    if str(NONUNIT_DIR) not in sys.path:
        sys.path.insert(0, str(NONUNIT_DIR))
    evaluator = importlib.import_module("evaluate_nonunit")
    if Path(evaluator.__file__).resolve() != (NONUNIT_DIR / "evaluate_nonunit.py").resolve():
        raise ImportError("evaluate_nonunit resolved outside the frozen source")
    return source, evaluator


def interval_record(source: Any, value: arb) -> dict[str, str]:
    lo, hi, endpoints = source.ball_endpoints(value)
    return {
        "lower": endpoints["lower"],
        "upper": endpoints["upper"],
        "width": source.decimal_fraction(hi - lo),
    }


def interval_from_record(source: Any, value: dict[str, str]) -> arb:
    return arb(value["lower"]).union(arb(value["upper"]))


def interval_contains_zero(source: Any, value: arb) -> bool:
    lo, hi, _ = source.ball_endpoints(value)
    return lo <= 0 <= hi


def _prime_set(factors: tuple[tuple[tuple[int, int], int], ...]) -> frozenset[tuple[int, int]]:
    return frozenset(prime for prime, _exponent in factors)


def pair_category(left_rough: bool, right_rough: bool) -> str:
    if left_rough and right_rough:
        return "rough_rough"
    if left_rough != right_rough:
        return "cross"
    return "affected_affected"


def two_re_character_value(source: Any, left_phase: int, right_phase: int) -> Fraction:
    """Exact 2Re(root^left_phase * conjugate(root^right_phase))."""
    return 2 * source.ROOT_REAL[(left_phase - right_phase) % 6]


def _ideal_record(source: Any, factors: tuple[tuple[tuple[int, int], int], ...]) -> dict[str, Any]:
    return {
        "norm": source.ideal_norm(factors),
        "factors": [
            {
                "prime_generator": [prime[0], prime[1]],
                "prime_ideal_norm": source.norm(prime),
                "exponent": exponent,
            }
            for prime, exponent in factors
        ],
    }


def pair_ideal_metadata(
    source: Any,
    left: tuple[tuple[tuple[int, int], int], ...],
    right: tuple[tuple[tuple[int, int], int], ...],
    orientation: int,
) -> dict[str, Any]:
    """Return Q (full lcm period), primitive quotient conductor, and shared zeros."""
    left_exp = dict(left)
    right_exp = dict(right)
    common = tuple(
        (prime, min(left_exp[prime], right_exp[prime]))
        for prime in sorted(left_exp.keys() & right_exp.keys())
    )
    lcm = tuple(
        (prime, max(left_exp.get(prime, 0), right_exp.get(prime, 0)))
        for prime in sorted(left_exp.keys() | right_exp.keys())
    )
    symmetric_difference = tuple(
        (prime, 1)
        for prime in sorted(left_exp.keys() ^ right_exp.keys())
    )
    if any(exponent != 1 for _prime, exponent in (*left, *right)):
        raise ValueError("the frozen quotient-conductor rule requires squarefree columns")
    conductor_norm = source.ideal_norm(symmetric_difference)
    shared_norm = source.ideal_norm(common)
    full_period_norm = source.ideal_norm(lcm)
    if full_period_norm != conductor_norm * shared_norm:
        raise ArithmeticError("squarefree lcm norm did not split as conductor times shared gcd")
    if conductor_norm <= 1:
        raise ArithmeticError("distinct squarefree columns must have nontrivial quotient conductor")

    local_quotient_factors: list[dict[str, Any]] = []
    for prime, _exponent in left:
        if prime not in right_exp:
            local_quotient_factors.append({
                "prime_generator": [prime[0], prime[1]],
                "prime_ideal_norm": source.norm(prime),
                "quotient_local_exponent": orientation,
                "source_column": "left",
            })
    for prime, _exponent in right:
        if prime not in left_exp:
            local_quotient_factors.append({
                "prime_generator": [prime[0], prime[1]],
                "prime_ideal_norm": source.norm(prime),
                "quotient_local_exponent": -orientation,
                "source_column": "right",
            })
    local_quotient_factors.sort(key=lambda item: tuple(item["prime_generator"]))

    return {
        "full_period_lcm_norm_Q": full_period_norm,
        "full_period_lcm_ideal": _ideal_record(source, lcm),
        "primitive_quotient_conductor": _ideal_record(source, symmetric_difference),
        "primitive_quotient_character": {
            "orientation": orientation,
            "local_factors": local_quotient_factors,
            "description": "left-only primes use +orientation; right-only primes use -orientation",
        },
        "shared_zero_mask_gcd": _ideal_record(source, common),
        "shared_primes_remain_zero_mask": True,
    }


def _support(
    config: dict[str, Any], precision: int, source: Any
) -> dict[str, Any]:
    U = int(config["U"])
    r = Fraction(config["r"])
    ell = Fraction(config["ell"])
    orientation = int(config["orientation"])
    amp_spec = config["P"]
    if orientation not in (-1, 1):
        raise ValueError("orientation must be +1 or -1")
    ctx.prec = precision

    eP = (Fraction(10001, 10000) * r - 1) / 6
    eH = Fraction(10001, 10000) * r
    L = source.rational_exponent(U, ell)
    if amp_spec == "production":
        P = source.rational_exponent(U, eP)
        H = source.rational_exponent(U, eH)
        amp_limit = source.certified_ceil(P)

        def within_P(q: int) -> bool:
            return source.compare_integer_scaled_power(
                q, U, eP, Fraction(1), precision
            ) <= 0
    else:
        if isinstance(amp_spec, bool) or not isinstance(amp_spec, int) or amp_spec < 1:
            raise ValueError(f"invalid integer amplifier cutoff {amp_spec!r}")
        P = arb(amp_spec)
        H = arb(U * amp_spec**6)
        amp_limit = amp_spec

        def within_P(q: int) -> bool:
            return q <= amp_spec

    if not (arb(U) * P**6).overlaps(H):
        raise ArithmeticError("reconstructed H is not U*P^6")

    amp_rows = [
        row for row in source.ideals_up_to(amp_limit)
        if source.good_ideal(row.factors) and within_P(row.q)
    ]
    if not amp_rows:
        raise ArithmeticError("amplifier support unexpectedly empty")

    rho_rows: list[Any] = []
    rho_by_u: list[arb] = []
    for row in source.elements_up_to((3 * U) // 2):
        if not source.sixthfree(row.factors):
            continue
        weight = source.rho_weight(row.q, U, precision)
        if weight > 0:
            rho_rows.append(row)
            rho_by_u.append(weight)
    if not rho_rows:
        raise ArithmeticError("physical sixthfree rho support unexpectedly empty")
    S_rho = sum(rho_by_u, arb(0))

    n_limit = source.certified_ceil(
        source.arb_fraction(Fraction(3, 2)) * L
    )
    n_rows: list[Any] = []
    W_by_n: list[arb] = []
    mu_by_n: list[int] = []
    for row in source.ideals_up_to(n_limit):
        if not source.good_ideal(row.factors):
            continue
        mobius = source.mu(row.factors)
        if mobius == 0:
            continue
        lower_cmp = source.compare_integer_scaled_power(
            row.q, U, ell, Fraction(1, 2), precision
        )
        upper_cmp = source.compare_integer_scaled_power(
            row.q, U, ell, Fraction(3, 2), precision
        )
        if lower_cmp > 0 and upper_cmp < 0:
            n_rows.append(row)
            W_by_n.append(source.W_weight(row.q, U, ell, precision))
            mu_by_n.append(mobius)
    if not n_rows:
        raise ArithmeticError("good squarefree Möbius source support unexpectedly empty")

    return {
        "U": U,
        "r": r,
        "ell": ell,
        "orientation": orientation,
        "P": P,
        "H": H,
        "L": L,
        "within_P": within_P,
        "amp_rows": amp_rows,
        "rho_rows": rho_rows,
        "rho_by_u": rho_by_u,
        "S_rho": S_rho,
        "n_rows": n_rows,
        "W_by_n": W_by_n,
        "mu_by_n": mu_by_n,
    }


def _saved_pair_matrix(row: dict[str, Any], n_count: int) -> list[list[int]]:
    raw = row.get("raw_periodic_sum")
    if not isinstance(raw, dict):
        raise ValueError(f"{row.get('id')}: missing saved raw_periodic_sum")
    matrix = raw.get("pair_2re")
    if not isinstance(matrix, list) or len(matrix) != n_count:
        raise ValueError(f"{row.get('id')}: saved pair matrix does not match n support")
    result: list[list[int]] = []
    for values in matrix:
        if not isinstance(values, list) or len(values) != n_count:
            raise ValueError(f"{row.get('id')}: saved pair matrix is not square")
        converted: list[int] = []
        for value in values:
            if isinstance(value, bool) or not isinstance(value, int):
                raise TypeError(f"{row.get('id')}: pair_2re entries must be JSON integers")
            converted.append(value)
        result.append(converted)
    if any(result[i][j] != result[j][i] for i in range(n_count) for j in range(n_count)):
        raise ArithmeticError(f"{row.get('id')}: saved pair matrix is not symmetric")
    if any(result[i][i] < 0 or result[i][i] % 2 for i in range(n_count)):
        raise ArithmeticError(f"{row.get('id')}: invalid pair_2re diagonal")
    digest = _sha256_bytes(json.dumps(result, separators=(",", ":")).encode("ascii"))
    if digest != raw.get("pair_matrix_sha256"):
        raise ValueError(f"{row.get('id')}: saved pair matrix SHA-256 mismatch")
    if int(raw.get("pair_count", -1)) != n_count * (n_count - 1) // 2:
        raise ValueError(f"{row.get('id')}: saved pair_count mismatch")
    return result


def _squarefree_subsets(
    factors: tuple[tuple[tuple[int, int], int], ...], source: Any
) -> list[tuple[tuple[tuple[tuple[int, int], int], ...], int]]:
    primes = [prime for prime, exponent in factors if exponent == 1]
    if len(primes) != len(factors):
        raise ValueError("inclusion-exclusion requires squarefree source columns")
    terms = []
    for mask in range(1 << len(primes)):
        divisor = tuple(
            (prime, 1) for index, prime in enumerate(primes)
            if mask & (1 << index)
        )
        terms.append((divisor, -1 if len(divisor) % 2 else 1))
    return terms


def _inclusion_exclusion_count(
    amp_rows: list[Any],
    union_factors: tuple[tuple[tuple[int, int], int], ...],
    within_P: Any,
    source: Any,
    after_mask_cache: dict[int, int],
) -> int:
    total = 0
    for divisor, sign in _squarefree_subsets(union_factors, source):
        q_mask = source.ideal_norm(divisor)
        if q_mask not in after_mask_cache:
            after_mask_cache[q_mask] = sum(
                1 for amp in amp_rows if within_P(amp.q * q_mask)
            )
        total += sign * after_mask_cache[q_mask]
    return total


def _ratio_extreme(source: Any, ratios: list[arb], kind: str) -> dict[str, str] | None:
    if not ratios:
        return None
    bounds = [source.ball_endpoints(value)[:2] for value in ratios]
    if kind == "min":
        lo = min(bound[0] for bound in bounds)
        hi = min(bound[1] for bound in bounds)
    elif kind == "max":
        lo = max(bound[0] for bound in bounds)
        hi = max(bound[1] for bound in bounds)
    else:
        raise ValueError(kind)
    return interval_record(source, source.arb_fraction(lo).union(source.arb_fraction(hi)))


def decompose_config(
    config: dict[str, Any],
    saved_row: dict[str, Any],
    plan: dict[str, Any],
    *,
    source: Any | None = None,
    evaluator: Any | None = None,
) -> dict[str, Any]:
    """Decompose one saved panel row; useful for bounded smoke checks."""
    if source is None or evaluator is None:
        loaded_source, loaded_evaluator = _modules()
        source = source or loaded_source
        evaluator = evaluator or loaded_evaluator
    precision = int(plan["precision_bits"])
    tolerance = Fraction(plan["absolute_C_tolerance"])
    if saved_row.get("id") != config.get("id"):
        raise ValueError("plan configuration and saved panel row IDs differ")
    if saved_row.get("precision_bits") != precision:
        raise ValueError(f"{config['id']}: precision differs from frozen plan")
    if saved_row.get("configuration", {}).get("scope") != "OFF_SCHEDULE_MASK_DIAGNOSTIC":
        raise ValueError(f"{config['id']}: saved row has unexpected scope")

    support = _support(config, precision, source)
    U = support["U"]
    ell = support["ell"]
    orientation = support["orientation"]
    n_rows = support["n_rows"]
    W_by_n = support["W_by_n"]
    mu_by_n = support["mu_by_n"]
    rho_rows = support["rho_rows"]
    rho_by_u = support["rho_by_u"]
    S_rho = support["S_rho"]
    amp_rows = support["amp_rows"]
    within_P = support["within_P"]
    A = len(amp_rows)

    recorded_config = saved_row["configuration"]
    expected_config = {
        "U": U,
        "P": config["P"],
        "r": str(Fraction(config["r"])),
        "ell": str(Fraction(config["ell"])),
        "orientation": orientation,
    }
    for key, expected in expected_config.items():
        if recorded_config.get(key) != expected:
            raise ValueError(f"{config['id']}: saved configuration field {key} differs")
    if saved_row.get("counts", {}).get("amp") != A:
        raise ArithmeticError(f"{config['id']}: reconstructed A(P) differs from saved count")
    if saved_row.get("counts", {}).get("physical_u") != len(rho_rows):
        raise ArithmeticError(f"{config['id']}: reconstructed physical u support differs")
    if saved_row.get("counts", {}).get("good_squarefree_mobius_n") != len(n_rows):
        raise ArithmeticError(f"{config['id']}: reconstructed n support count differs")
    saved_S = interval_from_record(source, saved_row["components"]["S_rho"])
    if not S_rho.overlaps(saved_S):
        raise ArithmeticError(f"{config['id']}: reconstructed physical mass S_rho differs")

    amp_records = [evaluator.ideal_record(row.factors) for row in amp_rows]
    if amp_records != [record["ideal"] for record in saved_row["physical_amplifiers"]]:
        raise ArithmeticError(f"{config['id']}: amplifier enumeration/order differs from frozen row")

    matrix = _saved_pair_matrix(saved_row, len(n_rows))
    raw_sum_meta = saved_row["raw_periodic_sum"]
    N = int(raw_sum_meta["N"])
    if N <= 0 or N != int(saved_row["components"]["normalization_N"]):
        raise ArithmeticError(f"{config['id']}: raw normalization differs from saved row")
    if int(saved_row["counts"]["raw_w_N"]) != N:
        raise ArithmeticError(f"{config['id']}: raw disk count differs from saved row")

    n_u_phase = [
        [source.phase_index(n.factors, u.z, orientation) for u in rho_rows]
        for n in n_rows
    ]
    two_re_roots = [
        source.arb_fraction(two_re_character_value(source, phase, 0))
        for phase in range(6)
    ]
    physical_cache: dict[tuple[int, int], arb] = {}
    for i in range(len(n_rows)):
        for j in range(i + 1, len(n_rows)):
            total = arb(0)
            for u_index, weight in enumerate(rho_by_u):
                left_phase = n_u_phase[i][u_index]
                right_phase = n_u_phase[j][u_index]
                if left_phase is None or right_phase is None:
                    continue
                total += weight * two_re_roots[(left_phase - right_phase) % 6]
            physical_cache[(i, j)] = total

    h49_rows = []
    if U == 48 and config["P"] == 49:
        h49_rows = [entry for entry in saved_row["h_masks"] if entry["ideal"]["norm"] == 49]
        if len(h49_rows) != 1:
            raise ArithmeticError(f"{config['id']}: expected one squarefree h49 mask")
    h49_record = h49_rows[0] if h49_rows else None
    h49_factors: tuple[tuple[tuple[int, int], int], ...] = ()
    h49_primes: frozenset[tuple[int, int]] = frozenset()
    h49_pair_sum = arb(0)
    if h49_record is not None:
        h49_factors = tuple(sorted(
            (tuple(factor["prime_generator"]), int(factor["exponent"]))
            for factor in h49_record["ideal"]["factors"]
        ))
        h49_primes = _prime_set(h49_factors)

    category_names = ("rough_rough", "cross", "affected_affected")
    groups: dict[str, dict[str, Any]] = {
        name: {
            "pair_count": 0,
            "C_contribution": arb(0),
            "physical_subtotal": arb(0),
            "raw_subtotal": arb(0),
            "physical_reference_same_A_copies": arb(0),
            "mask_correction": arb(0),
            "absolute_pair_diagnostic_only": arb(0),
            "ratios_H_over_Q": [],
            "max_pair_contribution_width": Fraction(0),
        }
        for name in category_names
    }
    pairs: list[dict[str, Any]] = []
    after_mask_cache: dict[int, int] = {}
    total_ie_checks = 0
    rough_rough_count = 0

    H_record = saved_row["parameters"]["H"]
    H = interval_from_record(source, H_record)
    C_pair_direct = arb(0)
    physical_total_direct = arb(0)
    raw_total_direct = arb(0)
    same_A_total_direct = arb(0)
    absolute_total_direct = arb(0)

    for i, left_row in enumerate(n_rows):
        left_factors = left_row.factors
        left_primes = _prime_set(left_factors)
        left_rough = not any(within_P(source.norm(prime)) for prime in left_primes)
        for j in range(i + 1, len(n_rows)):
            right_row = n_rows[j]
            right_factors = right_row.factors
            right_primes = _prime_set(right_factors)
            right_rough = not any(within_P(source.norm(prime)) for prime in right_primes)
            group = pair_category(left_rough, right_rough)
            union_primes = left_primes | right_primes
            union_factors = tuple((prime, 1) for prime in sorted(union_primes))
            A_P = sum(
                1 for amp in amp_rows
                if source.is_coprime(amp.factors, union_factors)
            )
            inclusion_exclusion = _inclusion_exclusion_count(
                amp_rows, union_factors, within_P, source, after_mask_cache
            )
            total_ie_checks += 1
            if inclusion_exclusion != A_P:
                raise ArithmeticError(
                    f"{config['id']} pair ({i},{j}): inclusion-exclusion {inclusion_exclusion} != A_P {A_P}"
                )
            if group == "rough_rough":
                rough_rough_count += 1
                if A_P != A:
                    raise ArithmeticError(
                        f"{config['id']} pair ({i},{j}): rough columns must have A_P=A"
                    )
            if group == "cross":
                affected_factors = left_factors if not left_rough else right_factors
                affected_only_count = sum(
                    1 for amp in amp_rows
                    if source.is_coprime(amp.factors, affected_factors)
                )
                if A_P != affected_only_count:
                    raise ArithmeticError(
                        f"{config['id']} pair ({i},{j}): cross A_P differs from affected-column count"
                    )

            coefficient_product = (
                mu_by_n[i] * mu_by_n[j] * W_by_n[i] * W_by_n[j]
                / support["L"]
            )
            physical_sum = physical_cache[(i, j)]
            T_physical = physical_sum / S_rho
            raw_pair_sum = matrix[i][j]
            T_raw = arb(raw_pair_sum) / N
            physical_term = coefficient_product * A_P * S_rho * T_physical
            raw_term = coefficient_product * A * S_rho * T_raw
            same_A_reference = coefficient_product * A * physical_sum
            mask_correction = physical_term - same_A_reference
            contribution = physical_term - raw_term

            period_meta = pair_ideal_metadata(
                source, left_factors, right_factors, orientation
            )
            Q = period_meta["full_period_lcm_norm_Q"]
            ratio_H_Q = H / Q
            if h49_record is not None and h49_primes <= union_primes:
                h49_pair_sum += coefficient_product * T_physical

            left_identity = {
                "index": i,
                "ideal": evaluator.ideal_record(left_factors),
                "mu": mu_by_n[i],
                "W": interval_record(source, W_by_n[i]),
                "P_rough": left_rough,
            }
            right_identity = {
                "index": j,
                "ideal": evaluator.ideal_record(right_factors),
                "mu": mu_by_n[j],
                "W": interval_record(source, W_by_n[j]),
                "P_rough": right_rough,
            }
            pair = {
                "i": i,
                "j": j,
                "group": group,
                "left_column": left_identity,
                "right_column": right_identity,
                "coefficient_product_mu_mu_WW_over_L": interval_record(source, coefficient_product),
                "A_P_exact": A_P,
                "A_exact": A,
                "A_P_over_A_exact": str(Fraction(A_P, A)),
                "inclusion_exclusion": {
                    "divisor_count": 1 << len(union_primes),
                    "A_P_from_signed_divisor_sum_exact": inclusion_exclusion,
                    "equals_direct_A_P": True,
                },
                "T_physical_2re": interval_record(source, T_physical),
                "physical_sum_rho_2re": interval_record(source, physical_sum),
                "raw_pair_2re_exact": raw_pair_sum,
                "T_raw_2re": interval_record(source, T_raw),
                "physical_signed_contribution": interval_record(source, physical_term),
                "raw_signed_contribution": interval_record(source, raw_term),
                "physical_reference_same_A_copies": interval_record(source, same_A_reference),
                "mask_correction_vs_same_A_copies": interval_record(source, mask_correction),
                "C_signed_contribution": interval_record(source, contribution),
                "absolute_C_pair_diagnostic_only": interval_record(source, abs(contribution)),
                **period_meta,
                "H_over_Q": interval_record(source, ratio_H_Q),
            }
            pairs.append(pair)
            bucket = groups[group]
            bucket["pair_count"] += 1
            bucket["C_contribution"] += contribution
            bucket["physical_subtotal"] += physical_term
            bucket["raw_subtotal"] += raw_term
            bucket["physical_reference_same_A_copies"] += same_A_reference
            bucket["mask_correction"] += mask_correction
            bucket["absolute_pair_diagnostic_only"] += abs(contribution)
            bucket["ratios_H_over_Q"].append(ratio_H_Q)
            bucket["max_pair_contribution_width"] = max(
                bucket["max_pair_contribution_width"],
                source.interval_width(contribution),
            )
            C_pair_direct += contribution
            physical_total_direct += physical_term
            raw_total_direct += raw_term
            same_A_total_direct += same_A_reference
            absolute_total_direct += abs(contribution)

    group_C = sum((groups[name]["C_contribution"] for name in category_names), arb(0))
    group_physical = sum((groups[name]["physical_subtotal"] for name in category_names), arb(0))
    group_raw = sum((groups[name]["raw_subtotal"] for name in category_names), arb(0))
    group_same_A = sum((groups[name]["physical_reference_same_A_copies"] for name in category_names), arb(0))
    group_mask_correction = sum((groups[name]["mask_correction"] for name in category_names), arb(0))
    group_absolute = sum((groups[name]["absolute_pair_diagnostic_only"] for name in category_names), arb(0))
    for name in category_names:
        bucket = groups[name]
        ratios = bucket.pop("ratios_H_over_Q")
        groups[name] = {
            "pair_count": bucket["pair_count"],
            "C_contribution": interval_record(source, bucket["C_contribution"]),
            "physical_subtotal": interval_record(source, bucket["physical_subtotal"]),
            "raw_subtotal": interval_record(source, bucket["raw_subtotal"]),
            "physical_reference_same_A_copies": interval_record(
                source, bucket["physical_reference_same_A_copies"]
            ),
            "mask_correction": interval_record(source, bucket["mask_correction"]),
            "absolute_pair_diagnostic_only": interval_record(
                source, bucket["absolute_pair_diagnostic_only"]
            ),
            "period_diagnostics": {
                "pair_count": bucket["pair_count"],
                "H_over_Q_min": _ratio_extreme(source, ratios, "min"),
                "H_over_Q_max": _ratio_extreme(source, ratios, "max"),
            },
            "max_pair_contribution_width": source.decimal_fraction(
                bucket["max_pair_contribution_width"]
            ),
        }

    full_C = interval_from_record(source, saved_row["full_C"])
    saved_C = interval_from_record(source, saved_row["C"])
    if not full_C.overlaps(saved_C):
        raise ArithmeticError(f"{config['id']}: saved C and full_C disagree")
    pair_residual = C_pair_direct - full_C
    grouped_residual = group_C - full_C

    old_components = saved_row["components"]
    old_physical = (
        interval_from_record(source, old_components["E_M"])
        - interval_from_record(source, old_components["D_phys"])
    )
    old_raw = (
        interval_from_record(source, old_components["lambda"])
        * interval_from_record(source, old_components["raw_offdiagonal_R_H_minus_D_raw"])
    )
    old_offdiagonal = interval_from_record(
        source, old_components["C_physical_raw_offdiagonal"]
    )
    old_component_C = old_physical - old_raw
    if not physical_total_direct.overlaps(old_physical):
        raise ArithmeticError(f"{config['id']}: pair physical subtotal misses old E_M-D_phys")
    if not raw_total_direct.overlaps(old_raw):
        raise ArithmeticError(f"{config['id']}: pair raw subtotal misses old lambda(R_H-D_raw)")
    if not C_pair_direct.overlaps(full_C) or not C_pair_direct.overlaps(old_offdiagonal):
        raise ArithmeticError(f"{config['id']}: signed pair sum misses old full C/offdiagonal")
    if not group_C.overlaps(C_pair_direct):
        raise ArithmeticError(f"{config['id']}: three signed groups do not reassemble pair sum")
    if not interval_contains_zero(source, pair_residual):
        raise ArithmeticError(f"{config['id']}: pair-vs-full-C interval residual excludes zero")
    if not interval_contains_zero(source, group_C - C_pair_direct):
        raise ArithmeticError(f"{config['id']}: group-vs-pair interval residual excludes zero")

    tolerance_checks = {
        "full_C": source.interval_width(full_C),
        "pair_sum": source.interval_width(C_pair_direct),
        "physical_subtotal": source.interval_width(physical_total_direct),
        "raw_subtotal": source.interval_width(raw_total_direct),
        "same_A_physical_reference": source.interval_width(same_A_total_direct),
        "mask_correction": source.interval_width(physical_total_direct - same_A_total_direct),
        "absolute_pair_diagnostic": source.interval_width(absolute_total_direct),
    }
    for name, width in tolerance_checks.items():
        if width > tolerance:
            raise ArithmeticError(
                f"{config['id']}: {name} interval width {width} exceeds {tolerance}"
            )

    h49_check = None
    if h49_record is not None:
        h49_mu = source.mu(h49_factors)
        h49_pair = h49_mu * h49_pair_sum
        h49_old = interval_from_record(source, h49_record["h"])
        if not h49_pair.overlaps(h49_old):
            raise ArithmeticError(f"{config['id']}: h49 pair formula misses saved h49")
        h49_check = {
            "ideal": h49_record["ideal"],
            "mu": h49_mu,
            "pair_formula": interval_record(source, h49_pair),
            "saved_h49": interval_record(source, h49_old),
            "residual": interval_record(source, h49_pair - h49_old),
            "interval_residual_contains_zero": interval_contains_zero(source, h49_pair - h49_old),
        }

    all_ratios = [
        interval_from_record(source, pair["H_over_Q"]) for pair in pairs
    ]
    rough_column_count = sum(
        1 for n in n_rows
        if not any(within_P(source.norm(prime)) for prime in _prime_set(n.factors))
    )
    max_pair_width = max(
        (source.interval_width(interval_from_record(source, pair["C_signed_contribution"]))
         for pair in pairs),
        default=Fraction(0),
    )
    return {
        "id": config["id"],
        "stage": config["stage"],
        "configuration": {
            "U": U,
            "P": config["P"],
            "r": str(Fraction(config["r"])),
            "ell": str(ell),
            "orientation": orientation,
            "scope": "OFF_SCHEDULE_MASK_DIAGNOSTIC",
        },
        "counts": {
            "A_exact": A,
            "physical_u": len(rho_rows),
            "good_squarefree_mobius_n": len(n_rows),
            "P_rough_columns": rough_column_count,
            "P_affected_columns": len(n_rows) - rough_column_count,
            "pair_count": len(pairs),
            "rough_rough_pair_count": rough_rough_count,
            "inclusion_exclusion_pair_checks": total_ie_checks,
        },
        "parameters": {
            "P": interval_record(source, support["P"]),
            "H": interval_record(source, H),
            "L": interval_record(source, support["L"]),
            "S_rho": interval_record(source, S_rho),
            "N_raw": N,
        },
        "C_pair_sum": interval_record(source, C_pair_direct),
        "full_C": interval_record(source, full_C),
        "pair_minus_full_C_residual": interval_record(source, pair_residual),
        "pair_minus_full_C_residual_contains_zero": interval_contains_zero(source, pair_residual),
        "three_groups_minus_full_C_residual": interval_record(source, grouped_residual),
        "three_groups_minus_full_C_residual_contains_zero": interval_contains_zero(source, grouped_residual),
        "physical_subtotal": interval_record(source, physical_total_direct),
        "old_physical_offdiagonal_E_M_minus_D_phys": interval_record(source, old_physical),
        "physical_subtotal_overlaps_old": physical_total_direct.overlaps(old_physical),
        "raw_subtotal": interval_record(source, raw_total_direct),
        "old_raw_offdiagonal_lambda_R_H_minus_D_raw": interval_record(source, old_raw),
        "raw_subtotal_overlaps_old": raw_total_direct.overlaps(old_raw),
        "old_physical_minus_raw_C": interval_record(source, old_component_C),
        "old_C_physical_raw_offdiagonal": interval_record(source, old_offdiagonal),
        "pair_sum_overlaps_old_C": C_pair_direct.overlaps(old_offdiagonal),
        "same_P_A_copies_physical_reference": interval_record(source, same_A_total_direct),
        "mask_correction_vs_same_P_A_copies": interval_record(source, physical_total_direct - same_A_total_direct),
        "absolute_pair_diagnostic_only": {
            "value": interval_record(source, absolute_total_direct),
            "may_replace_signed_C": False,
        },
        "group_reassembly_checks": {
            "group_C_overlaps_pair_sum": group_C.overlaps(C_pair_direct),
            "group_physical_overlaps_pair_physical": group_physical.overlaps(physical_total_direct),
            "group_raw_overlaps_pair_raw": group_raw.overlaps(raw_total_direct),
            "group_same_A_overlaps_pair_same_A": group_same_A.overlaps(same_A_total_direct),
            "group_mask_correction_overlaps_total": group_mask_correction.overlaps(
                physical_total_direct - same_A_total_direct
            ),
            "group_absolute_diagnostic_overlaps_total": group_absolute.overlaps(absolute_total_direct),
        },
        "interval_width_checks": {
            "limit": str(tolerance),
            "widths": {name: source.decimal_fraction(width) for name, width in tolerance_checks.items()},
            "max_pair_C_contribution_width": source.decimal_fraction(max_pair_width),
            "max_pair_C_contribution_width_within_limit": max_pair_width <= tolerance,
        },
        "period_diagnostics": {
            "pair_count": len(pairs),
            "H_over_Q_min": _ratio_extreme(source, all_ratios, "min"),
            "H_over_Q_max": _ratio_extreme(source, all_ratios, "max"),
            "Q_uses_full_lcm_including_shared_zero_mask": True,
        },
        "groups": groups,
        "h49_pair_formula_check": h49_check,
        "pairs": pairs,
    }


def load_frozen_inputs() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], dict[str, dict[str, str]]]:
    manifest = verify_pinned_inputs()
    source, evaluator = _modules()
    _ = source
    paths = {
        "plan": NONUNIT_DIR / "plan.json",
        "freeze": NONUNIT_DIR / "heldout_freeze.json",
        "main": NONUNIT_DIR / "main.json",
        "heldout": NONUNIT_DIR / "heldout.json",
    }
    loaded = {name: json.loads(path.read_text(encoding="utf-8")) for name, path in paths.items()}
    plan = loaded["plan"]
    evaluator.check_plan(plan)
    if loaded["main"].get("schema") != PANEL_SCHEMA or loaded["heldout"].get("schema") != PANEL_SCHEMA:
        raise ValueError("main/heldout panel schema mismatch")
    if loaded["main"].get("stage") != "main" or loaded["heldout"].get("stage") != "heldout":
        raise ValueError("main/heldout panel stages mismatch")
    for name in ("main", "heldout"):
        if loaded[name].get("scope") != "OFF_SCHEDULE_MASK_DIAGNOSTIC":
            raise ValueError(f"{name} panel has unexpected scope")

    freeze = loaded["freeze"]
    if (freeze.get("status") != "FROZEN_BEFORE_HELDOUT_EXECUTION"
            or freeze.get("baseline_changes_since_plan") is not False
            or freeze.get("fits_executed") != 0):
        raise ValueError("heldout freeze record does not match the frozen diagnostic")
    for frozen_name, relative in {
        "evaluate_nonunit.py": "experiments/cf22_pysr/nonunit/evaluate_nonunit.py",
        "periodic.py": "experiments/cf22_pysr/nonunit/periodic.py",
        "periodic_counter.cpp": "experiments/cf22_pysr/nonunit/periodic_counter.cpp",
        "plan.json": "experiments/cf22_pysr/nonunit/plan.json",
        "main.json": "experiments/cf22_pysr/nonunit/main.json",
    }.items():
        if freeze.get("sha256", {}).get(frozen_name) != manifest[relative]["sha256"]:
            raise ValueError(f"heldout freeze digest mismatch for {frozen_name}")

    for name in ("main", "heldout"):
        provenance = loaded[name].get("provenance", {})
        if provenance.get("plan_sha256") != manifest[
            "experiments/cf22_pysr/nonunit/plan.json"
        ]["sha256"]:
            raise ValueError(f"{name} provenance plan digest mismatch")
        if provenance.get("new_evaluator_sha256") != manifest[
            "experiments/cf22_pysr/nonunit/evaluate_nonunit.py"
        ]["sha256"]:
            raise ValueError(f"{name} provenance evaluator digest mismatch")
        if provenance.get("old_evaluator_sha256") != manifest[
            "experiments/cf22_pysr/evaluate.py"
        ]["sha256"]:
            raise ValueError(f"{name} provenance old evaluator digest mismatch")
        if provenance.get("periodic_python_sha256") != manifest[
            "experiments/cf22_pysr/nonunit/periodic.py"
        ]["sha256"]:
            raise ValueError(f"{name} provenance periodic digest mismatch")

    config_ids = [config["id"] for config in plan["configs"]]
    saved_rows = loaded["main"]["rows"] + loaded["heldout"]["rows"]
    row_by_id = {row["id"]: row for row in saved_rows}
    if len(row_by_id) != len(saved_rows) or set(row_by_id) != set(config_ids) or len(config_ids) != 20:
        raise ValueError("main plus heldout must contain exactly the frozen 20 unique configurations")
    for config in plan["configs"]:
        saved = row_by_id[config["id"]]
        if saved.get("stage") != config.get("stage"):
            raise ValueError(f"{config['id']}: saved stage differs from plan")
    return plan, loaded["main"], loaded["heldout"], freeze, manifest


def _runtime_provenance(
    manifest: dict[str, dict[str, str]], decomposer_sha256: str | None = None
) -> dict[str, Any]:
    import flint

    return {
        "pinned_input_commit": PINNED_COMMIT,
        "execution_head": _git(["rev-parse", "HEAD"]),
        "inputs_exact_pinned_git_blobs": True,
        "input_git_blobs_and_sha256": manifest,
        "decomposer_sha256": decomposer_sha256 or _sha256_bytes(Path(__file__).read_bytes()),
        "python_executable": str(Path(sys.executable).resolve()),
        "python_version": platform.python_version(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "flint_version": getattr(flint, "__version__", None),
        "raw_matrix_source": "saved main.json/heldout.json raw_periodic_sum.pair_2re",
        "raw_sums_called": False,
        "native_periodic_counter_called": False,
    }


def decompose_panel(
    plan: dict[str, Any],
    main: dict[str, Any],
    heldout: dict[str, Any],
    manifest: dict[str, dict[str, str]],
    *,
    decomposer_sha256: str | None = None,
) -> dict[str, Any]:
    source, evaluator = _modules()
    saved_rows = {row["id"]: row for row in main["rows"] + heldout["rows"]}
    results = [
        decompose_config(config, saved_rows[config["id"]], plan, source=source, evaluator=evaluator)
        for config in plan["configs"]
    ]
    panel_checks = {
        "config_count": len(results),
        "exactly_20_configs": len(results) == 20,
        "all_pair_sums_overlap_full_C": all(row["pair_sum_overlaps_old_C"] for row in results),
        "all_physical_subtotals_overlap_old": all(row["physical_subtotal_overlaps_old"] for row in results),
        "all_raw_subtotals_overlap_old": all(row["raw_subtotal_overlaps_old"] for row in results),
        "all_pair_residuals_contain_zero": all(row["pair_minus_full_C_residual_contains_zero"] for row in results),
        "all_group_reassemblies_overlap": all(row["group_reassembly_checks"]["group_C_overlaps_pair_sum"] for row in results),
        "all_group_subtotals_reassemble": all(
            all(row["group_reassembly_checks"].values()) for row in results
        ),
        "all_interval_widths_within_limit": all(
            row["interval_width_checks"]["max_pair_C_contribution_width_within_limit"]
            and all(Fraction(width) <= Fraction(row["interval_width_checks"]["limit"])
                    for width in row["interval_width_checks"]["widths"].values())
            for row in results
        ),
        "all_rough_rough_pairs_have_A_P_equal_A": all(
            pair["A_P_exact"] == pair["A_exact"]
            for row in results for pair in row["pairs"]
            if pair["group"] == "rough_rough"
        ),
        "all_pair_inclusion_exclusion_checks_pass": all(
            pair["inclusion_exclusion"]["equals_direct_A_P"]
            for row in results for pair in row["pairs"]
        ),
    }
    if not all(panel_checks.values()):
        raise ArithmeticError(f"one or more 20-row pair-decomposition checks failed: {panel_checks}")
    return {
        "schema": OUTPUT_SCHEMA,
        "scope": "FINITE_OFF_SCHEDULE_PAIR_DIAGNOSTIC",
        "formula": {
            "pair_C_ij": "(mu_i*mu_j*W_i*W_j/L) * (A_P(n_i*n_j)*S_rho*T_physical_2re - A(P)*S_rho*T_raw_2re)",
            "T_physical_2re": "sum_u rho(q_u/U)*2Re(chi_i(u)*conj(chi_j(u)))/S_rho, preserving zero masks",
            "T_raw_2re": "saved pair_2re[i][j]/N_raw",
            "group_partition": "rough_rough / cross / affected_affected",
            "period_terms": "Q is the full lcm ideal norm; quotient conductor is the squarefree symmetric difference; shared gcd primes remain a zero mask",
        },
        "provenance": _runtime_provenance(manifest, decomposer_sha256),
        "plan_sha256": manifest["experiments/cf22_pysr/nonunit/plan.json"]["sha256"],
        "input_freeze": {
            "status": "FROZEN_BEFORE_HELDOUT_EXECUTION",
            "fits_executed": 0,
            "baseline_changes_since_plan": False,
        },
        "panel_checks": panel_checks,
        "rows": results,
        "limitations": [
            "Finite diagnostic on the frozen 20-configuration panel; no cofinal CF22 estimate is proved.",
            "Absolute pair sums are diagnostics only and never replace the signed pair sum.",
        ],
    }


def write_output(path: Path, payload: dict[str, Any]) -> None:
    encoded = (json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n").encode("utf-8")
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.suffix == ".gz":
        with path.open("xb") as raw_output:
            with gzip.GzipFile(fileobj=raw_output, mode="wb", filename="", mtime=0) as output:
                output.write(encoded)
    else:
        with path.open("xb") as output:
            output.write(encoded)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, help="new JSON or .json.gz output path; existing paths are refused")
    args = parser.parse_args(argv)
    start_decomposer_sha256 = _sha256_bytes(Path(__file__).read_bytes())
    plan, main_data, heldout_data, _freeze, manifest = load_frozen_inputs()
    payload = decompose_panel(
        plan,
        main_data,
        heldout_data,
        manifest,
        decomposer_sha256=start_decomposer_sha256,
    )
    end_decomposer_sha256 = _sha256_bytes(Path(__file__).read_bytes())
    if end_decomposer_sha256 != start_decomposer_sha256:
        raise RuntimeError("decomposer source changed during the panel run")
    if verify_pinned_inputs() != manifest:
        raise RuntimeError("a pinned source/data blob changed during the panel run")
    write_output(Path(args.output).resolve(), payload)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"decompose.py: {type(exc).__name__}: {exc}", file=sys.stderr)
        raise
