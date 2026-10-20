#!/usr/bin/env python3
"""Certified off-schedule mask diagnostic for the finite CF22 source.

This evaluator keeps the original physical profile and complete finite source,
while allowing the amplifier cutoff to be selected independently. It is a
diagnostic experiment only and makes no cofinal or CF22 improvement claim.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import importlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
from types import ModuleType
from typing import Any

from flint import arb, ctx


NONUNIT_DIR = Path(__file__).resolve().parent
EXPERIMENT_DIR = NONUNIT_DIR.parent
REPO = NONUNIT_DIR.parents[2]
SOURCE_EVALUATOR_PATH = EXPERIMENT_DIR / "evaluate.py"
OWNER_REQUEST_PATH = (
    NONUNIT_DIR / "OWNER_REQUEST.txt"
)


def _load_source_evaluator() -> ModuleType:
    if not SOURCE_EVALUATOR_PATH.is_file():
        raise FileNotFoundError(SOURCE_EVALUATOR_PATH)
    if str(EXPERIMENT_DIR) not in sys.path:
        sys.path.insert(0, str(EXPERIMENT_DIR))
    module = importlib.import_module("evaluate")
    if Path(module.__file__).resolve() != SOURCE_EVALUATOR_PATH.resolve():
        raise ImportError("canonical evaluate module resolved to an unexpected file")
    return module


source = _load_source_evaluator()


def _load_periodic() -> ModuleType:
    if str(NONUNIT_DIR) not in sys.path:
        sys.path.insert(0, str(NONUNIT_DIR))
    return importlib.import_module("periodic")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_head() -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO, text=True,
        stderr=subprocess.PIPE,
    ).strip()


def pinned_source_bytes(commit: str, path: Path) -> bytes:
    relative = path.resolve().relative_to(REPO.resolve()).as_posix()
    return subprocess.check_output(
        ["git", "show", f"{commit}:{relative}"], cwd=REPO,
        stderr=subprocess.PIPE,
    )


def pinned_mathematical_source_hashes(commit: str) -> dict[str, str]:
    paths = {
        "full_cusp_pair_q07": REPO / "docs/literature/openai_math_2026-10-07/PROSHKA_VERDICT_FULL_CUSP_PAIR_Q07.md",
        "signed_incidence_q03": REPO / "docs/literature/openai_math_2026-10-07/PROSHKA_VERDICT_SIGNED_INCIDENCE_Q03.md",
    }
    return {
        label: hashlib.sha256(pinned_source_bytes(commit, path)).hexdigest()
        for label, path in paths.items()
    }


def runtime_provenance(periodic: ModuleType) -> dict[str, Any]:
    result: dict[str, Any] = {
        "python_executable": str(Path(sys.executable).resolve()),
        "python_version": platform.python_version(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "flint_version": getattr(sys.modules.get("flint"), "__version__", None),
    }
    compiler = shutil.which("clang++")
    if compiler is not None:
        compiler_path = Path(compiler).resolve()
        result["compiler_path"] = str(compiler_path)
        try:
            version = subprocess.run(
                [compiler, "--version"], check=True, capture_output=True,
                text=True, timeout=10,
            )
            result["compiler_version"] = version.stdout.splitlines()[0]
        except (OSError, subprocess.SubprocessError, IndexError) as exc:
            result["compiler_version_error"] = f"{type(exc).__name__}: {exc}"

    try:
        library = periodic._native_library()
        native_path = Path(library._name).resolve()
        result["native_library_path"] = str(native_path)
        if native_path.is_file():
            result["native_library_sha256"] = sha256(native_path)
        cpp_path = Path(periodic._CPP_FILE).resolve()
        result["native_library_source_sha256"] = sha256(cpp_path)
    except (AttributeError, OSError, RuntimeError) as exc:
        result["native_library_provenance_error"] = f"{type(exc).__name__}: {exc}"
    return result


def fraction_text(value: Fraction) -> str:
    return source.decimal_fraction(value)


def interval_record(value: arb) -> dict[str, str]:
    lo, hi, endpoints = source.ball_endpoints(value)
    width = hi - lo
    return {
        "lower": endpoints["lower"],
        "upper": endpoints["upper"],
        "width": fraction_text(width),
    }


def interval_from_record(value: dict[str, str]) -> arb:
    return arb(value["lower"]).union(arb(value["upper"]))


def ideal_norm(factors: tuple[tuple[tuple[int, int], int], ...]) -> int:
    return source.ideal_norm(factors)


def factors_key(factors: tuple[tuple[tuple[int, int], int], ...]) -> tuple:
    return tuple((tuple(prime), exponent) for prime, exponent in factors)


def radical_factors(
    factors: tuple[tuple[tuple[int, int], int], ...],
) -> tuple[tuple[tuple[int, int], int], ...]:
    return tuple((prime, 1) for prime, _exponent in factors)


def ideal_record(factors: tuple[tuple[tuple[int, int], int], ...]) -> dict[str, Any]:
    return {
        "norm": ideal_norm(factors),
        "factors": [
            {
                "prime_generator": [prime[0], prime[1]],
                "prime_ideal_norm": source.norm(prime),
                "exponent": exponent,
            }
            for prime, exponent in factors
        ],
    }


def squarefree_divisors(
    factors: tuple[tuple[tuple[int, int], int], ...],
) -> list[tuple[tuple[tuple[int, int], int], ...]]:
    primes = [prime for prime, _exponent in factors]
    divisors = [
        tuple((prime, 1) for index, prime in enumerate(primes) if mask & (1 << index))
        for mask in range(1 << len(primes))
    ]
    return sorted(divisors, key=lambda item: (ideal_norm(item), item))


def mobius_divisor_terms(
    factors: tuple[tuple[tuple[int, int], int], ...],
) -> list[tuple[tuple[tuple[tuple[int, int], int], ...], int]]:
    primes = [prime for prime, _exponent in factors]
    terms = []
    for divisor in squarefree_divisors(factors):
        divisor_primes = {prime for prime, _ in divisor}
        complement_size = len(primes) - len(divisor_primes)
        terms.append((divisor, -1 if complement_size % 2 else 1))
    return terms


def check_plan(plan: dict[str, Any]) -> None:
    if plan.get("schema") != "cf22-nonunit-plan-v1":
        raise ValueError("unexpected nonunit plan schema")
    if plan.get("scope") != "OFF_SCHEDULE_MASK_DIAGNOSTIC":
        raise ValueError("plan must be labeled OFF_SCHEDULE_MASK_DIAGNOSTIC")
    if plan.get("status") != "BASELINES_FROZEN_BEFORE_NEW_EVALUATIONS":
        raise ValueError("nonunit baselines are not frozen")
    if plan.get("precision_bits") != 192:
        raise ValueError("this experiment is fixed at the existing 192-bit Arb precision")
    profiles = plan.get("profiles", {})
    if profiles != {
        "rho": "exp(1-1/(1-(2*y-2)^2)) on 1/2<y<3/2, zero elsewhere",
        "W": "same as rho",
        "C_H": 2,
        "S": "prime ideals above 6",
        "nu": "1 on good ideals, zero extension",
    }:
        raise ValueError("plan profile differs from the fixed source specialization")
    if plan.get("no_pysr_fit") is not True:
        raise ValueError("the diagnostic plan must prohibit fitting")
    tolerance = Fraction(plan.get("absolute_C_tolerance", "0"))
    if tolerance <= 0:
        raise ValueError("absolute_C_tolerance must be positive")

    baselines = plan.get("baselines", {})
    zero = baselines.get("zero", {})
    additive = baselines.get("additive", {})
    if zero.get("A_response_prediction") != "0" or zero.get("allowed_error") != "0":
        raise ValueError("the zero-response baseline must be frozen with zero error")
    if (additive.get("mixed_h_prediction")
            != "0 for squarefree d with at least two distinct prime ideal factors"
            or additive.get("allowed_error") != "0"):
        raise ValueError("the additive baseline must freeze all mixed h terms at zero")
    if "Singleton h and F(1),G_H retained exactly" not in additive.get("qualification", ""):
        raise ValueError("the additive baseline must disclose its exact oracle components")

    expected: dict[str, tuple[int, int | str, str, int]] = {}
    for U in (48, 64):
        for P in ("production", 7, 13):
            for orientation in (1, -1):
                expected[f"U{U}_P{P}_o{orientation}"] = (
                    U, P, "main", orientation
                )
    for P in ("production", 7, 13):
        for orientation in (1, -1):
            expected[f"U96_P{P}_o{orientation}"] = (
                96, P, "heldout", orientation
            )
    for orientation in (1, -1):
        expected[f"U48_P49_o{orientation}"] = (
            48, 49, "heldout", orientation
        )

    configs = plan.get("configs")
    if not isinstance(configs, list) or len(configs) != len(expected):
        raise ValueError("plan must contain the frozen 20-configuration panel")
    seen: set[str] = set()
    for config in configs:
        config_id = config.get("id")
        if not isinstance(config_id, str) or config_id in seen or config_id not in expected:
            raise ValueError(f"unexpected or duplicate configuration: {config_id!r}")
        seen.add(config_id)
        U, P, stage, orientation = expected[config_id]
        if (config.get("U"), config.get("P"), config.get("stage")) != (U, P, stage):
            raise ValueError(f"configuration differs from frozen panel: {config_id}")
        if (Fraction(config.get("r", "0")) != Fraction(113, 100)
                or Fraction(config.get("ell", "0")) != Fraction(113, 100)
                or config.get("orientation") != orientation):
            raise ValueError(f"configuration differs from fixed r/ell/orientation: {config_id}")
    if seen != set(expected):
        raise ValueError("plan is missing a frozen configuration")


def floor_production_radius(U: int, exponent: Fraction, scale: Fraction,
                            precision: int) -> int:
    ceiling = source.certified_ceil(
        source.arb_fraction(scale) * source.rational_exponent(U, exponent)
    )
    comparison = source.compare_integer_scaled_power(
        ceiling, U, exponent, scale, precision
    )
    return ceiling if comparison == 0 else ceiling - 1


def _raw_matrix(raw_record: dict[str, Any], n_count: int) -> list[list[int]]:
    matrix = raw_record.get("pair_2re")
    if matrix is None or len(matrix) != n_count:
        raise ValueError("periodic raw_sums returned a missing or incorrectly sized pair matrix")
    result = [[int(value) for value in row] for row in matrix]
    if any(len(row) != n_count for row in result):
        raise ValueError("periodic raw_sums returned a nonsquare pair matrix")
    for index, row in enumerate(result):
        if row[index] < 0 or row[index] % 2:
            raise ArithmeticError("diagonal 2Re pair sum must be twice a nonnegative count")
    return result


def raw_character_components(
    periodic: ModuleType,
    n_rows: list[Any],
    W_by_n: list[arb],
    mu_by_n: list[int],
    L: arb,
    bound: int,
    orientation: int,
) -> tuple[int, arb, arb, arb, dict[str, Any]]:
    raw_results = periodic.raw_sums(n_rows, [bound], orientation=orientation)
    if not isinstance(raw_results, list) or len(raw_results) != 1:
        raise ValueError("periodic.raw_sums must return one record for the requested disk")
    record = raw_results[0]
    if int(record.get("B", -1)) != bound:
        raise ValueError("periodic raw disk boundary differs from the requested exact B")
    matrix = _raw_matrix(record, len(n_rows))
    count = int(record["N"])
    if count <= 0:
        raise ArithmeticError("periodic raw disk must contain nonzero ideal elements")

    diagonal = arb(0)
    off_diagonal = arb(0)
    for i in range(len(n_rows)):
        diagonal_count = matrix[i][i] // 2
        diagonal += diagonal_count * (W_by_n[i] ** 2) / L
        for j in range(i + 1, len(n_rows)):
            off_diagonal += (
                matrix[i][j] * mu_by_n[i] * mu_by_n[j]
                * W_by_n[i] * W_by_n[j] / L
            )
    rh = diagonal + off_diagonal
    return count, rh, diagonal, off_diagonal, {
        "B": str(bound),
        "N": str(count),
        "pair_count": len(n_rows) * (len(n_rows) - 1) // 2,
        "diagonal_count_convention": "pair_2re[i][i] / 2",
        "pair_matrix_shape": [len(matrix), len(matrix)],
        "pair_matrix_sha256": hashlib.sha256(
            json.dumps(matrix, separators=(",", ":")).encode("ascii")
        ).hexdigest(),
        "pair_2re": matrix,
    }


def evaluate_config(config: dict[str, Any], precision: int,
                    absolute_C_tolerance: Fraction,
                    periodic: ModuleType) -> dict[str, Any]:
    U = config["U"]
    r = Fraction(config["r"])
    ell = Fraction(config["ell"])
    orientation = config["orientation"]
    amp_spec = config["P"]
    ctx.prec = precision
    source.BOUNDARY_PRECISIONS.clear()

    production = amp_spec == "production"
    eP = (Fraction(10001, 10000) * r - 1) / 6
    eH = Fraction(10001, 10000) * r
    L = source.rational_exponent(U, ell)
    if production:
        P = source.rational_exponent(U, eP)
        H = source.rational_exponent(U, eH)
        B = floor_production_radius(U, eH, Fraction(2), precision)
        amp_limit = source.certified_ceil(P)

        def within_P(q: int) -> bool:
            return source.compare_integer_scaled_power(q, U, eP, Fraction(1), precision) <= 0
    else:
        P_int = int(amp_spec)
        P = arb(P_int)
        H_int = U * P_int**6
        H = arb(H_int)
        B = 2 * H_int
        amp_limit = P_int

        def within_P(q: int) -> bool:
            return q <= P_int

    if B < 1:
        raise ArithmeticError("raw disk radius must be positive")
    if not (arb(U) * (P ** 6)).overlaps(H):
        raise ArithmeticError("H was not recomputed as U*P^6")

    all_amp = source.ideals_up_to(amp_limit)
    amp_rows = [row for row in all_amp if source.good_ideal(row.factors) and within_P(row.q)]
    if not amp_rows:
        raise ArithmeticError("amplifier ideal set unexpectedly empty")
    expected_amp_counts = {7: 3, 13: 5, 49: 17}
    if not production and P_int in expected_amp_counts and len(amp_rows) != expected_amp_counts[P_int]:
        raise ArithmeticError(
            f"A({P_int})={len(amp_rows)} disagrees with the frozen exact ideal count"
        )

    u_limit = (3 * U) // 2
    u_rows: list[Any] = []
    rho_by_u: list[arb] = []
    for row in source.elements_up_to(u_limit):
        if not source.sixthfree(row.factors):
            continue
        weight = source.rho_weight(row.q, U, precision)
        if weight > 0:
            u_rows.append(row)
            rho_by_u.append(weight)
    if not u_rows:
        raise ArithmeticError("physical sixthfree rho support is empty")
    S_rho = sum(rho_by_u, arb(0))
    if not S_rho > 0:
        raise ArithmeticError("physical profile mass must be positive")

    n_limit = source.certified_ceil(source.arb_fraction(Fraction(3, 2)) * L)
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
        raise ArithmeticError("good squarefree Möbius source support is empty")

    n_u_phase = [
        [source.phase_index(n.factors, u.z, orientation) for u in u_rows]
        for n in n_rows
    ]
    phase_coefficients = [mu_by_n[i] * W_by_n[i] for i in range(len(n_rows))]
    L_inv = 1 / L
    f_cache: dict[tuple, tuple[arb, arb, arb]] = {}

    def measure_mask(mask_factors: tuple) -> tuple[arb, arb, arb]:
        key = factors_key(mask_factors)
        if key in f_cache:
            return f_cache[key]
        compatible = [source.is_coprime(n.factors, mask_factors) for n in n_rows]
        energy = arb(0)
        diagonal = arb(0)
        for u_index, _u in enumerate(u_rows):
            coeffs = [arb(0) for _ in range(6)]
            diag_u = arb(0)
            for i in range(len(n_rows)):
                if not compatible[i]:
                    continue
                phase = n_u_phase[i][u_index]
                if phase is None:
                    continue
                coeffs[phase] += phase_coefficients[i]
                diag_u += W_by_n[i] ** 2 * L_inv
            a = sum((coeffs[k] * source.ROOT[k][0] for k in range(6)), arb(0))
            b = sum((coeffs[k] * source.ROOT[k][1] for k in range(6)), arb(0))
            energy += rho_by_u[u_index] * source.phase_norm((a, b)) * L_inv
            diagonal += rho_by_u[u_index] * diag_u
        F_value = (energy - diagonal) / S_rho
        f_cache[key] = (F_value, energy, diagonal)
        return f_cache[key]

    squarefree_rows = [
        row for row in source.ideals_up_to(amp_limit)
        if source.good_ideal(row.factors) and source.mu(row.factors) != 0
        and within_P(row.q)
    ]
    unit_factors: tuple = ()
    F1, _E1, _D1 = measure_mask(unit_factors)
    for row in squarefree_rows:
        measure_mask(row.factors)

    A = len(amp_rows)
    E_M = arb(0)
    D_phys = arb(0)
    A_response_sum = arb(0)
    amp_records: list[dict[str, Any]] = []
    for amp in amp_rows:
        rad = radical_factors(amp.factors)
        F_mask, E_mask, D_mask = measure_mask(rad)
        E_M += E_mask
        D_phys += D_mask
        A_response_sum += F_mask - F1
        amp_records.append({
            "ideal": ideal_record(amp.factors),
            "radical_mask": ideal_record(rad),
            "F_radical": interval_record(F_mask),
        })
    A_response = A_response_sum / A

    N, R_H, D_raw, raw_off_diagonal, raw_meta = raw_character_components(
        periodic, n_rows, W_by_n, mu_by_n, L, B, orientation
    )
    lam = A * S_rho / N
    G_H = (R_H - D_raw) / N
    D_diag = D_phys - lam * D_raw
    C = E_M - lam * R_H - D_diag
    C_off_diagonal = (E_M - D_phys) - lam * (R_H - D_raw)
    if not C.overlaps(C_off_diagonal):
        raise ArithmeticError("physical/raw off-diagonal reduction does not overlap C")

    h_values: dict[tuple, arb] = {}
    h_records: list[dict[str, Any]] = []
    mobius_checks: list[dict[str, Any]] = []
    for row in squarefree_rows:
        factors = row.factors
        h_value = sum(
            (sign * measure_mask(divisor)[0]
             for divisor, sign in mobius_divisor_terms(factors)),
            arb(0),
        )
        key = factors_key(factors)
        h_values[key] = h_value
        reconstructed = sum(
            (h_values.get(factors_key(divisor), arb(0))
             for divisor in squarefree_divisors(factors)),
            arb(0),
        )
        # h(e) must be available for every proper divisor before checking F(d).
        if not reconstructed.overlaps(measure_mask(factors)[0]):
            # The row order is by norm, so all proper nonunit divisors precede d.
            raise ArithmeticError("finite Mobius inversion does not recover F(d)")
        mobius_checks.append({
            "ideal": ideal_record(factors),
            "reconstructed_F": interval_record(reconstructed),
            "overlaps_F": True,
        })
        h_records.append({
            "ideal": ideal_record(factors),
            "omega": len(factors),
            "F": interval_record(measure_mask(factors)[0]),
            "h": interval_record(h_value),
        })

    def within_amplifier_after_mask(q_product: int) -> bool:
        return within_P(q_product)

    def A_after_mask(q_mask: int) -> int:
        return sum(1 for amp in amp_rows if within_amplifier_after_mask(amp.q * q_mask))

    formula1_sum = sum(
        (measure_mask(radical_factors(amp.factors))[0] for amp in amp_rows), arb(0)
    )
    C1 = S_rho * (formula1_sum - A * G_H)
    C2 = A * S_rho * (F1 - G_H + A_response)

    h_weight_all = arb(0)
    h_weight_singletons = arb(0)
    h_weight_mixed = arb(0)
    singleton_terms: list[dict[str, Any]] = []
    mixed_terms: list[dict[str, Any]] = []
    h_sum = arb(0)
    for row in squarefree_rows:
        if row.q == 1:
            continue
        coefficient = A_after_mask(row.q)
        h_value = h_values[factors_key(row.factors)]
        contribution = coefficient * h_value
        h_sum += contribution
        h_weight_all += contribution
        if len(row.factors) == 1:
            h_weight_singletons += contribution
            singleton_terms.append({
                "ideal": ideal_record(row.factors),
                "A_P_over_q": coefficient,
                "h": interval_record(h_value),
                "weighted_h": interval_record(contribution),
            })
        else:
            h_weight_mixed += contribution
            mixed_terms.append({
                "ideal": ideal_record(row.factors),
                "A_P_over_q": coefficient,
                "h": interval_record(h_value),
                "weighted_h": interval_record(contribution),
            })

    C4 = S_rho * (A * (F1 - G_H) + h_sum)
    C_zero = A * S_rho * (F1 - G_H)
    C_additive = S_rho * (A * (F1 - G_H) + h_weight_singletons)
    zero_residual = C - C_zero
    additive_residual = C - C_additive
    zero_omitted_h = S_rho * h_weight_all
    additive_omitted_h = S_rho * h_weight_mixed
    A_response_from_h = h_weight_all / A

    checks = {
        "C_formula_1_overlaps_direct_C": C1.overlaps(C),
        "C_formula_2_overlaps_direct_C": C2.overlaps(C),
        "C_formula_4_overlaps_direct_C": C4.overlaps(C),
        "physical_raw_offdiagonal_overlaps_direct_C": C_off_diagonal.overlaps(C),
        "A_response_mobius_identity_overlaps": A_response_from_h.overlaps(A_response),
        "zero_baseline_residual_overlaps_weighted_omitted_h": zero_residual.overlaps(zero_omitted_h),
        "additive_baseline_residual_overlaps_weighted_mixed_h": additive_residual.overlaps(additive_omitted_h),
    }
    if not all(checks.values()):
        raise ArithmeticError(f"one or more exact nonunit identities failed: {checks}")
    if source.interval_width(C) > absolute_C_tolerance:
        raise ArithmeticError(
            f"certified C interval width exceeds plan tolerance {absolute_C_tolerance}"
        )
    max_boundary_precision = max(source.BOUNDARY_PRECISIONS, default=precision)

    legacy_comparison = None
    if config["stage"] == "main" and production and U in (48, 64):
        legacy_config = {
            "id": f"legacy_{config['id']}",
            "U": U,
            "r": f"{r.numerator}/{r.denominator}",
            "ell": f"{ell.numerator}/{ell.denominator}",
            "orientation": orientation,
        }
        legacy = source.evaluate_config(legacy_config, precision, Fraction(1, 10**30))
        component_pairs = {
            "E_M": (E_M, legacy["components"]["E_M"]),
            "lambda_R_H": (lam * R_H, legacy["components"]["lambda_R_H"]),
            "D_diag": (D_diag, legacy["components"]["D_diag"]),
            "C": (C, legacy["C"]),
        }
        component_checks = {
            name: current.overlaps(interval_from_record(old))
            for name, (current, old) in component_pairs.items()
        }
        if not all(component_checks.values()):
            raise ArithmeticError(f"new production P0 row disagrees with old evaluator: {component_checks}")
        if int(legacy["counts"]["w"]) != N:
            raise ArithmeticError("periodic raw disk count differs from old finite enumeration")
        legacy_comparison = {
            "old_evaluator_C_overlap_verified": True,
            "component_overlap_checks": component_checks,
            "raw_count_matches_old_enumeration": True,
        }

    factor_f_values = [
        {
            "ideal_mask": ideal_record(row.factors),
            "F": interval_record(measure_mask(row.factors)[0]),
        }
        for row in squarefree_rows
    ]
    P_record = interval_record(P)
    H_record = interval_record(H)
    return {
        "id": config["id"],
        "stage": config["stage"],
        "configuration": {
            "U": U,
            "P": "production" if production else int(amp_spec),
            "r": f"{r.numerator}/{r.denominator}",
            "ell": f"{ell.numerator}/{ell.denominator}",
            "orientation": orientation,
            "scope": "OFF_SCHEDULE_MASK_DIAGNOSTIC",
        },
        "parameters": {
            "P": P_record,
            "H": H_record,
            "L": interval_record(L),
            "raw_disk_B": str(B),
            "raw_disk_N": str(N),
            "C_H": 2,
        },
        "precision_bits": precision,
        "boundary_precision_max_bits": max_boundary_precision,
        "counts": {
            "amp": A,
            "physical_u": len(u_rows),
            "raw_w_N": N,
            "good_squarefree_mobius_n": len(n_rows),
            "squarefree_good_masks": len(squarefree_rows),
            "amp_is_unit_only": A == 1 and amp_rows[0].q == 1,
        },
        "raw_periodic_sum": raw_meta,
        "physical_amplifiers": amp_records,
        "F_masks": factor_f_values,
        "h_masks": h_records,
        "components": {
            "S_rho": interval_record(S_rho),
            "A_response": interval_record(A_response),
            "F_1": interval_record(F1),
            "G_H": interval_record(G_H),
            "E_M": interval_record(E_M),
            "R_H": interval_record(R_H),
            "raw_diagonal_D": interval_record(D_raw),
            "raw_offdiagonal_R_H_minus_D_raw": interval_record(R_H - D_raw),
            "lambda": interval_record(lam),
            "lambda_R_H": interval_record(lam * R_H),
            "D_phys": interval_record(D_phys),
            "D_diag": interval_record(D_diag),
            "normalization_N": N,
            "C_direct": interval_record(C),
            "C_physical_raw_offdiagonal": interval_record(C_off_diagonal),
        },
        "formula_checks": {
            **checks,
            "formula_1_C": interval_record(C1),
            "formula_2_C": interval_record(C2),
            "formula_4_C": interval_record(C4),
            "mobius_inversion": mobius_checks,
        },
        "baselines": {
            "zero_response": {
                "predicted_full_C": interval_record(C_zero),
                "observed_minus_prediction": interval_record(zero_residual),
                "weighted_omitted_h_residual": interval_record(zero_omitted_h),
                "retained_exact_oracle_components": {
                    "F_1": interval_record(F1),
                    "G_H": interval_record(G_H),
                },
                "independent_prediction_of_full_C": False,
                "interpretation": "F(1) and G_H are exact oracle inputs; this is not an independent prediction of full C.",
            },
            "additive_singleton_h": {
                "predicted_full_C": interval_record(C_additive),
                "observed_minus_prediction": interval_record(additive_residual),
                "weighted_omitted_h_residual": interval_record(additive_omitted_h),
                "retained_exact_singleton_h": singleton_terms,
                "omitted_mixed_h": mixed_terms,
                "retained_exact_oracle_components": {
                    "F_1": interval_record(F1),
                    "G_H": interval_record(G_H),
                },
                "independent_prediction_of_full_C": False,
                "interpretation": "Where no mixed squarefree mask is admitted, this is an algebraic identity, not evidence for an interaction law.",
            },
        },
        "C": interval_record(C),
        "full_C": interval_record(C),
        "absolute_C_interval_width": fraction_text(source.interval_width(C)),
        "legacy_P0_comparison": legacy_comparison,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", required=True, help="frozen nonunit plan JSON")
    parser.add_argument("--output", required=True, help="new output JSON path (exclusive)")
    parser.add_argument("--stage", required=True, choices=("main", "heldout"))
    args = parser.parse_args(argv)

    plan_path = Path(args.plan).resolve()
    output_path = Path(args.output).resolve()
    if output_path.exists():
        raise FileExistsError(f"refusing to replace existing output: {output_path}")
    plan_bytes = plan_path.read_bytes()
    plan = json.loads(plan_bytes)
    check_plan(plan)
    precision = plan["precision_bits"]
    tolerance = Fraction(plan["absolute_C_tolerance"])
    if not OWNER_REQUEST_PATH.is_file():
        raise FileNotFoundError(OWNER_REQUEST_PATH)
    if sha256(OWNER_REQUEST_PATH) != plan.get("owner_request_sha256"):
        raise ValueError("source attachment hash differs from the frozen plan")
    source_commit = plan.get("source_commit")
    if not isinstance(source_commit, str) or not source_commit:
        raise ValueError("plan must pin a source commit")
    pinned_evaluator = pinned_source_bytes(source_commit, SOURCE_EVALUATOR_PATH)
    pinned_evaluator_sha256 = hashlib.sha256(pinned_evaluator).hexdigest()
    if sha256(SOURCE_EVALUATOR_PATH) != pinned_evaluator_sha256:
        raise ValueError("working source evaluator differs from the evaluator pinned by the plan")
    pinned_math_hashes = pinned_mathematical_source_hashes(source_commit)
    current_math_hashes = source.source_hashes(REPO)
    if current_math_hashes != pinned_math_hashes:
        raise ValueError("mathematical source files differ from the source commit pinned by the plan")
    execution_head = git_head()

    periodic = _load_periodic()
    if getattr(periodic, "evaluate", None) is not source:
        raise ImportError("periodic and nonunit evaluators must share the canonical evaluate module")
    periodic_path = Path(periodic.__file__).resolve()
    if not periodic_path.is_file():
        raise FileNotFoundError(periodic_path)
    periodic_cpp_path = periodic_path.parent / "periodic_counter.cpp"
    if not periodic_cpp_path.is_file():
        raise FileNotFoundError(periodic_cpp_path)

    input_hashes = {
        "old_evaluator_sha256": sha256(SOURCE_EVALUATOR_PATH),
        "old_evaluator_pinned_sha256": pinned_evaluator_sha256,
        "mathematical_source_sha256": current_math_hashes,
        "new_evaluator_sha256": sha256(Path(__file__).resolve()),
        "periodic_python_sha256": sha256(periodic_path),
        "periodic_cpp_sha256": sha256(periodic_cpp_path),
        "plan_sha256": hashlib.sha256(plan_bytes).hexdigest(),
        "source_attachment_sha256": sha256(OWNER_REQUEST_PATH),
    }
    source.self_checks()
    configs = [config for config in plan["configs"] if config["stage"] == args.stage]
    results = [evaluate_config(config, precision, tolerance, periodic) for config in configs]

    current_hashes = {
        "old_evaluator_sha256": sha256(SOURCE_EVALUATOR_PATH),
        "old_evaluator_pinned_sha256": pinned_evaluator_sha256,
        "mathematical_source_sha256": current_math_hashes,
        "new_evaluator_sha256": sha256(Path(__file__).resolve()),
        "periodic_python_sha256": sha256(periodic_path),
        "periodic_cpp_sha256": sha256(periodic_cpp_path),
        "plan_sha256": sha256(plan_path),
        "source_attachment_sha256": sha256(OWNER_REQUEST_PATH),
    }
    if current_hashes != input_hashes:
        raise RuntimeError("a hashed experiment input changed during evaluation")

    current_source_commit = git_head()
    if current_source_commit != execution_head:
        raise RuntimeError("repository HEAD changed during evaluation")
    payload = {
        "schema": "cf22-nonunit-evaluation-v1",
        "scope": "OFF_SCHEDULE_MASK_DIAGNOSTIC",
        "stage": args.stage,
        "provenance": {
            "source_commit": source_commit,
            "execution_head": execution_head,
            **input_hashes,
            "precision_bits": precision,
            "absolute_C_tolerance": str(tolerance),
            "baseline_status": plan["status"],
            "runtime": runtime_provenance(periodic),
            "source_specialization": {
                "S": "prime ideals above 6",
                "nu": "1 on good ideals, zero extension",
                "rho_W": "exp(1-1/(1-(2*y-2)^2)) on 1/2<y<3/2, zero elsewhere",
                "r_ell": "113/100",
                "C_H": 2,
                "amplifier": "all good ideals including powers, cutoff P as frozen per configuration",
                "raw_sum": "complete disk 0<Norm(w)<=B; exact periodic character-pair sums",
            },
        },
        "baseline_policy": plan["baselines"],
        "rows": results,
        "limitations": [
            "Finite off-schedule diagnostic only; it does not establish a cofinal estimate or improve CF22.",
            "The exact F(1) and G_H values are retained as oracle components in the frozen baselines.",
            "The attachment discloses approximate U48/U64 mask coefficients; those are not blind coefficient holdouts.",
            "Heldout configurations test frozen full-return baselines and receive no fitting or tuning.",
        ],
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("x", encoding="utf-8") as output_file:
        output_file.write(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:  # No partial result is emitted after a failed certificate.
        print(f"evaluate_nonunit.py: {type(exc).__name__}: {exc}", file=sys.stderr)
        raise
