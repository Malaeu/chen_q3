#!/usr/bin/env python3
"""Independently verify saved CF22 rough/affected pair-group contributions.

The physical side is rebuilt directly from the canonical finite source for all
saved configurations. The raw side uses only the integer ``pair_2re`` matrices
saved in the nonunit outputs; this script never calls ``raw_sums``.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib
import json
import platform
from fractions import Fraction
from pathlib import Path
import subprocess
import sys
from typing import Any

from flint import arb, ctx


SCRIPT_PATH = Path(__file__).resolve()
CORRELATION_DIR = SCRIPT_PATH.parent
REPO = SCRIPT_PATH.parents[3]
EXPERIMENT_DIR = REPO / "experiments/cf22_pysr"
SOURCE_EVALUATOR_PATH = EXPERIMENT_DIR / "evaluate.py"
DEFAULT_PLAN = EXPERIMENT_DIR / "nonunit/plan.json"
PLAN_OWNER_REQUEST_PATH = EXPERIMENT_DIR / "nonunit/OWNER_REQUEST.txt"
NEW_OWNER_REQUEST_PATH = CORRELATION_DIR / "OWNER_REQUEST.txt"
DEFAULT_MAIN = EXPERIMENT_DIR / "nonunit/main.json"
DEFAULT_HELDOUT = EXPERIMENT_DIR / "nonunit/heldout.json"
DEFAULT_DECOMPOSITION = CORRELATION_DIR / "decomposition.json.gz"
DEFAULT_OUTPUT = CORRELATION_DIR / "verification.json"
GROUPS = ("rough_rough", "cross", "affected_affected")


def _load_source() -> Any:
    if not SOURCE_EVALUATOR_PATH.is_file():
        raise FileNotFoundError(SOURCE_EVALUATOR_PATH)
    if str(EXPERIMENT_DIR) not in sys.path:
        sys.path.insert(0, str(EXPERIMENT_DIR))
    source = importlib.import_module("evaluate")
    if Path(source.__file__).resolve() != SOURCE_EVALUATOR_PATH.resolve():
        raise ImportError("canonical evaluate module resolved to an unexpected file")
    return source


source = _load_source()


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def git_head() -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO, text=True,
        stderr=subprocess.PIPE,
    ).strip()


def read_json(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    if path.suffix == ".gz":
        with gzip.open(path, "rt", encoding="utf-8") as stream:
            value = json.load(stream)
    else:
        value = json.loads(raw)
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object in {path}")
    return value, raw


def interval_from_record(value: Any) -> arb:
    if not isinstance(value, dict) or "lower" not in value or "upper" not in value:
        raise ValueError(f"expected a certified interval record, got {value!r}")
    return arb(value["lower"]).union(arb(value["upper"]))


def check_nonunit_plan(plan: dict[str, Any]) -> None:
    """Validate the fixed nonunit panel without importing its evaluator."""
    if plan.get("schema") != "cf22-nonunit-plan-v1":
        raise ValueError("unexpected nonunit plan schema")
    if plan.get("scope") != "OFF_SCHEDULE_MASK_DIAGNOSTIC":
        raise ValueError("plan is not the frozen off-schedule diagnostic")
    if plan.get("status") != "BASELINES_FROZEN_BEFORE_NEW_EVALUATIONS":
        raise ValueError("nonunit baselines are not frozen")
    if plan.get("precision_bits") != 192:
        raise ValueError("nonunit panel precision differs from the frozen 192 bits")
    if plan.get("profiles") != {
        "rho": "exp(1-1/(1-(2*y-2)^2)) on 1/2<y<3/2, zero elsewhere",
        "W": "same as rho",
        "C_H": 2,
        "S": "prime ideals above 6",
        "nu": "1 on good ideals, zero extension",
    }:
        raise ValueError("nonunit profile differs from the saved source specialization")
    if plan.get("no_pysr_fit") is not True:
        raise ValueError("nonunit plan must prohibit fitting")
    tolerance = Fraction(plan.get("absolute_C_tolerance", "0"))
    if tolerance <= 0:
        raise ValueError("nonunit absolute_C_tolerance must be positive")
    baselines = plan.get("baselines", {})
    zero = baselines.get("zero", {})
    additive = baselines.get("additive", {})
    if zero.get("A_response_prediction") != "0" or zero.get("allowed_error") != "0":
        raise ValueError("zero-response baseline is not the frozen exact baseline")
    if (additive.get("mixed_h_prediction")
            != "0 for squarefree d with at least two distinct prime ideal factors"
            or additive.get("allowed_error") != "0"
            or "Singleton h and F(1),G_H retained exactly"
            not in additive.get("qualification", "")):
        raise ValueError("additive baseline differs from its frozen exact statement")

    expected: dict[str, tuple[int, int | str, str, int]] = {}
    for U in (48, 64):
        for P in ("production", 7, 13):
            for orientation in (1, -1):
                expected[f"U{U}_P{P}_o{orientation}"] = (U, P, "main", orientation)
    for P in ("production", 7, 13):
        for orientation in (1, -1):
            expected[f"U96_P{P}_o{orientation}"] = (96, P, "heldout", orientation)
    for orientation in (1, -1):
        expected[f"U48_P49_o{orientation}"] = (48, 49, "heldout", orientation)
    configs = plan.get("configs")
    if not isinstance(configs, list) or len(configs) != 20:
        raise ValueError("plan must contain exactly the frozen 20 configurations")
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
        raise ValueError("plan is missing one or more frozen configurations")
    if not isinstance(plan.get("source_commit"), str) or not plan["source_commit"]:
        raise ValueError("nonunit plan does not pin its source commit")
    if not isinstance(plan.get("owner_request_sha256"), str):
        raise ValueError("nonunit plan does not pin the owner request")


def compare_intervals(actual: arb, expected_record: Any,
                      tolerance: Fraction) -> dict[str, Any]:
    expected = interval_from_record(expected_record)
    residual = actual - expected
    contains_zero = residual.overlaps(arb(0))
    width = source.interval_width(residual)
    return {
        "overlaps": actual.overlaps(expected),
        "residual_contains_zero": contains_zero,
        "residual": source.interval_json(residual),
        "residual_width": source.decimal_fraction(width),
        "within_tolerance": width <= tolerance,
    }


def compare_values(actual: arb, expected_record: Any,
                   tolerance: Fraction, label: str) -> dict[str, Any]:
    result = compare_intervals(actual, expected_record, tolerance)
    if not (result["overlaps"] and result["residual_contains_zero"]
            and result["within_tolerance"]):
        raise ArithmeticError(
            f"{label} failed interval comparison: "
            f"overlap={result['overlaps']} zero={result['residual_contains_zero']} "
            f"width={result['residual_width']} tolerance={tolerance}"
        )
    return result


def assert_overlap(actual: arb, expected_record: Any, label: str) -> None:
    expected = interval_from_record(expected_record)
    if not actual.overlaps(expected):
        raise ArithmeticError(f"{label} intervals do not overlap")


def _support_for_config(config: dict[str, Any], saved_row: dict[str, Any],
                        precision: int) -> dict[str, Any]:
    U, r, ell, orientation = source.validate_config(config)
    ctx.prec = precision
    source.BOUNDARY_PRECISIONS.clear()
    eP = (Fraction(10001, 10000) * r - 1) / 6
    eH = Fraction(10001, 10000) * r
    L = source.rational_exponent(U, ell)
    production = config["P"] == "production"

    if production:
        P = source.rational_exponent(U, eP)
        amp_limit = source.certified_ceil(P)

        def within_P(q: int) -> bool:
            return source.compare_integer_scaled_power(
                q, U, eP, Fraction(1), precision
            ) <= 0

        H = source.rational_exponent(U, eH)
        b_ceiling = source.certified_ceil(2 * H)
        b_comparison = source.compare_integer_scaled_power(
            b_ceiling, U, eH, Fraction(2), precision
        )
        raw_bound = b_ceiling if b_comparison == 0 else b_ceiling - 1
        P_description: int | str = "production"
    else:
        P_int = int(config["P"])
        P = arb(P_int)
        H_int = U * P_int**6
        H = arb(H_int)
        amp_limit = P_int
        raw_bound = 2 * H_int
        P_description = P_int

        def within_P(q: int) -> bool:
            return q <= P_int

    if max(amp_limit, (3 * U) // 2) > source.MAX_ENUM_NORM:
        raise RuntimeError("support exceeds the canonical source enumeration bound")

    amp_rows = [
        row for row in source.ideals_up_to(amp_limit)
        if source.good_ideal(row.factors) and within_P(row.q)
    ]
    if not amp_rows:
        raise ArithmeticError("amplifier support is empty")

    u_rows = []
    rho_by_u = []
    for row in source.elements_up_to((3 * U) // 2):
        if not source.sixthfree(row.factors):
            continue
        weight = source.rho_weight(row.q, U, precision)
        if weight > 0:
            u_rows.append(row)
            rho_by_u.append(weight)
    if not u_rows:
        raise ArithmeticError("physical sixthfree rho support is empty")
    S_rho = sum(rho_by_u, arb(0))

    n_limit = source.certified_ceil(
        source.arb_fraction(Fraction(3, 2)) * L
    )
    n_rows = []
    W_by_n = []
    mu_by_n = []
    for row in source.ideals_up_to(n_limit):
        if not source.good_ideal(row.factors):
            continue
        mobius = source.mu(row.factors)
        if mobius == 0:
            continue
        lower = source.compare_integer_scaled_power(
            row.q, U, ell, Fraction(1, 2), precision
        )
        upper = source.compare_integer_scaled_power(
            row.q, U, ell, Fraction(3, 2), precision
        )
        if lower > 0 and upper < 0:
            n_rows.append(row)
            W_by_n.append(source.W_weight(row.q, U, ell, precision))
            mu_by_n.append(mobius)
    if not n_rows:
        raise ArithmeticError("source column support is empty")

    phase_by_n_u = [
        [source.phase_index(n.factors, u.z, orientation) for u in u_rows]
        for n in n_rows
    ]
    masks_by_n_amp = [
        [source.is_coprime(n.factors, a.factors) for a in amp_rows]
        for n in n_rows
    ]
    rough_by_n = [
        all(not within_P(source.norm(prime)) for prime, _exponent in n.factors)
        for n in n_rows
    ]

    raw_record = saved_row.get("raw_periodic_sum", {})
    matrix = raw_record.get("pair_2re")
    if not isinstance(matrix, list) or len(matrix) != len(n_rows):
        raise ValueError("saved raw pair matrix row count differs from reconstructed columns")
    matrix = [[int(value) for value in row] for row in matrix]
    if any(len(row) != len(n_rows) for row in matrix):
        raise ValueError("saved raw pair matrix is not square of reconstructed dimension")
    matrix_hash = sha256_bytes(json.dumps(
        matrix, separators=(",", ":")
    ).encode("ascii"))
    if matrix_hash != raw_record.get("pair_matrix_sha256"):
        raise ValueError("saved raw pair matrix digest mismatch")
    for i, row in enumerate(matrix):
        if row[i] < 0 or row[i] % 2:
            raise ArithmeticError("saved diagonal pair_2re entry violates its convention")
        for j in range(i + 1, len(matrix)):
            if row[j] != matrix[j][i]:
                raise ArithmeticError("saved raw pair matrix is not symmetric")
    if raw_record.get("diagonal_count_convention") != "pair_2re[i][i] / 2":
        raise ValueError("saved raw diagonal convention changed")
    if int(raw_record.get("B", -1)) != raw_bound:
        raise ValueError("saved raw disk radius differs from the reconstructed profile")

    counts = saved_row.get("counts", {})
    if len(amp_rows) != int(counts.get("amp", -1)):
        raise ValueError("amplifier count differs from the saved configuration")
    if len(u_rows) != int(counts.get("physical_u", -1)):
        raise ValueError("physical u count differs from the saved configuration")
    if len(n_rows) != int(counts.get("good_squarefree_mobius_n", -1)):
        raise ValueError("source column count differs from the saved configuration")
    if len(matrix) != int(raw_record.get("pair_matrix_shape", [-1])[0]):
        raise ValueError("saved pair matrix shape metadata mismatch")
    if int(raw_record.get("N", -1)) != int(saved_row["parameters"]["raw_disk_N"]):
        raise ValueError("saved raw matrix N disagrees with saved row parameters")

    squarefree_amp_count = sum(source.mu(row.factors) != 0 for row in amp_rows)
    non_squarefree_amp_count = len(amp_rows) - squarefree_amp_count
    prime_power_amp_count = sum(
        len(row.factors) == 1 and row.factors[0][1] > 1
        for row in amp_rows
    )
    if not production:
        expected_amp_count = {7: 3, 13: 5, 49: 17}.get(int(config["P"]))
        if expected_amp_count is not None and len(amp_rows) != expected_amp_count:
            raise ArithmeticError(
                f"A({config['P']})={len(amp_rows)}, expected {expected_amp_count}"
            )
    if not production and int(config["P"]) == 49:
        if non_squarefree_amp_count == 0 or prime_power_amp_count == 0:
            raise ArithmeticError("P=49 amplifier support did not include prime powers")

    return {
        "U": U,
        "P_description": P_description,
        "P": P,
        "H": H,
        "L": L,
        "orientation": orientation,
        "amp_rows": amp_rows,
        "u_rows": u_rows,
        "rho_by_u": rho_by_u,
        "S_rho": S_rho,
        "n_rows": n_rows,
        "W_by_n": W_by_n,
        "mu_by_n": mu_by_n,
        "phase_by_n_u": phase_by_n_u,
        "masks_by_n_amp": masks_by_n_amp,
        "rough_by_n": rough_by_n,
        "matrix": matrix,
        "raw_N": int(raw_record["N"]),
        "raw_bound": raw_bound,
        "amp_count": len(amp_rows),
        "squarefree_amp_count": squarefree_amp_count,
        "non_squarefree_amp_count": non_squarefree_amp_count,
        "prime_power_amp_count": prime_power_amp_count,
        "pair_counts": {group: 0 for group in GROUPS},
    }


def _root_sum(coefficients: list[arb]) -> tuple[arb, arb]:
    return (
        sum((coefficients[k] * source.ROOT[k][0] for k in range(6)), arb(0)),
        sum((coefficients[k] * source.ROOT[k][1] for k in range(6)), arb(0)),
    )


def _group_for_pair(i: int, j: int, rough_by_n: list[bool]) -> str:
    left, right = rough_by_n[i], rough_by_n[j]
    if left and right:
        return "rough_rough"
    if left != right:
        return "cross"
    return "affected_affected"


def _direct_group_sums(support: dict[str, Any]) -> dict[str, Any]:
    n_rows = support["n_rows"]
    weights = support["W_by_n"]
    mobius = support["mu_by_n"]
    phases = support["phase_by_n_u"]
    masks = support["masks_by_n_amp"]
    rough = support["rough_by_n"]
    u_rows = support["u_rows"]
    rho = support["rho_by_u"]
    L = support["L"]
    amp_rows = support["amp_rows"]
    matrix = support["matrix"]
    n_count = len(n_rows)

    pair_counts = {group: 0 for group in GROUPS}
    for i in range(n_count):
        for j in range(i + 1, n_count):
            pair_counts[_group_for_pair(i, j, rough)] += 1
    if sum(pair_counts.values()) != n_count * (n_count - 1) // 2:
        raise ArithmeticError("rough/affected pair partition is not exhaustive")

    physical = {group: arb(0) for group in GROUPS}
    unmasked_per_amplifier = {group: arb(0) for group in GROUPS}
    raw_unscaled = {group: arb(0) for group in GROUPS}

    # This is the physical source with all amplifier masks removed, for the
    # same P and H. Subtracting A(P) times it gives the exact mask correction.
    for u_index, _u in enumerate(u_rows):
        unmasked_coefficients = {group: [arb(0) for _ in range(6)]
                                 for group in ("rough_rough", "affected_affected")}
        unmasked_diagonal = {group: arb(0) for group in unmasked_coefficients}
        all_coefficients = [arb(0) for _ in range(6)]
        for i in range(n_count):
            phase = phases[i][u_index]
            if phase is None:
                continue
            coefficient = mobius[i] * weights[i]
            all_coefficients[phase] += coefficient
            group = "rough_rough" if rough[i] else "affected_affected"
            unmasked_coefficients[group][phase] += coefficient
            unmasked_diagonal[group] += weights[i] ** 2

        total_norm = source.phase_norm(_root_sum(all_coefficients))
        norm_by_group = {
            group: source.phase_norm(_root_sum(unmasked_coefficients[group]))
            for group in unmasked_coefficients
        }
        weighted = rho[u_index] / L
        unmasked_per_amplifier["rough_rough"] += weighted * (
            norm_by_group["rough_rough"] - unmasked_diagonal["rough_rough"]
        )
        unmasked_per_amplifier["affected_affected"] += weighted * (
            norm_by_group["affected_affected"] - unmasked_diagonal["affected_affected"]
        )
        unmasked_per_amplifier["cross"] += weighted * (
            total_norm - norm_by_group["rough_rough"]
            - norm_by_group["affected_affected"]
        )

        for amp_index, _amp in enumerate(amp_rows):
            coefficients = {group: [arb(0) for _ in range(6)]
                            for group in ("rough_rough", "affected_affected")}
            diagonal = {group: arb(0) for group in coefficients}
            total_coefficients = [arb(0) for _ in range(6)]
            for i in range(n_count):
                if not masks[i][amp_index]:
                    continue
                phase = phases[i][u_index]
                if phase is None:
                    continue
                coefficient = mobius[i] * weights[i]
                total_coefficients[phase] += coefficient
                group = "rough_rough" if rough[i] else "affected_affected"
                coefficients[group][phase] += coefficient
                diagonal[group] += weights[i] ** 2

            total_masked_norm = source.phase_norm(_root_sum(total_coefficients))
            norm_masked = {
                group: source.phase_norm(_root_sum(coefficients[group]))
                for group in coefficients
            }
            physical["rough_rough"] += weighted * (
                norm_masked["rough_rough"] - diagonal["rough_rough"]
            )
            physical["affected_affected"] += weighted * (
                norm_masked["affected_affected"] - diagonal["affected_affected"]
            )
            physical["cross"] += weighted * (
                total_masked_norm - norm_masked["rough_rough"]
                - norm_masked["affected_affected"]
            )

    for i in range(n_count):
        for j in range(i + 1, n_count):
            group = _group_for_pair(i, j, rough)
            # Only saved off-diagonal integer entries are read. Diagonal raw
            # counts are intentionally excluded from every group.
            raw_unscaled[group] += (
                matrix[i][j] * mobius[i] * mobius[j]
                * weights[i] * weights[j] / L
            )

    A = arb(len(amp_rows))
    S_rho = support["S_rho"]
    N_H = support["raw_N"]
    raw_scale = A * S_rho / N_H
    group_results: dict[str, Any] = {}
    for group in GROUPS:
        scaled_raw = raw_scale * raw_unscaled[group]
        correction = physical[group] - A * unmasked_per_amplifier[group]
        contribution = physical[group] - scaled_raw
        group_results[group] = {
            "physical_subtotal": source.interval_json(physical[group]),
            "raw_unscaled_diagnostic": source.interval_json(raw_unscaled[group]),
            "raw_subtotal": source.interval_json(scaled_raw),
            "mask_correction": source.interval_json(correction),
            "C_contribution": source.interval_json(contribution),
            "pair_count": pair_counts[group],
        }
    rough_correction = physical["rough_rough"] - A * unmasked_per_amplifier["rough_rough"]
    rough_correction_check = compare_intervals(
        rough_correction, source.interval_json(arb(0)), Fraction(1, 10**30)
    )
    if not (rough_correction_check["overlaps"]
            and rough_correction_check["residual_contains_zero"]
            and rough_correction_check["within_tolerance"]):
        raise ArithmeticError("P-rough pair mask correction is not zero within tolerance")
    return {
        "groups": group_results,
        "C_pair_sum": sum((physical[g] - raw_scale * raw_unscaled[g]
                            for g in GROUPS), arb(0)),
        "raw_scale": raw_scale,
        "pair_counts": pair_counts,
        "rough_correction_zero_check": rough_correction_check,
    }


def _check_group_output(computed: dict[str, Any], decomp_row: dict[str, Any],
                        tolerance: Fraction) -> dict[str, Any]:
    output_groups = decomp_row.get("groups")
    if not isinstance(output_groups, dict):
        raise ValueError(f"decomposition row {decomp_row.get('id')} lacks groups")
    checks: dict[str, Any] = {}
    for group in GROUPS:
        target = output_groups.get(group)
        if not isinstance(target, dict):
            raise ValueError(f"decomposition row lacks group {group}")
        checks[group] = {}
        for field in ("C_contribution", "physical_subtotal", "raw_subtotal", "mask_correction"):
            actual = interval_from_record(computed["groups"][group][field])
            checks[group][field] = compare_values(
                actual, target.get(field), tolerance,
                f"{decomp_row.get('id')} {group}.{field}",
            )
    return checks


def _runtime() -> dict[str, Any]:
    return {
        "python_executable": str(Path(sys.executable).resolve()),
        "python_version": platform.python_version(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "flint_version": getattr(sys.modules.get("flint"), "__version__", None),
    }


def verify(plan_path: Path, main_path: Path, heldout_path: Path,
           decomposition_path: Path) -> dict[str, Any]:
    input_paths = {
        "plan": plan_path,
        "plan_owner_request": PLAN_OWNER_REQUEST_PATH,
        "pair_decomposition_request": NEW_OWNER_REQUEST_PATH,
        "saved_main": main_path,
        "saved_heldout": heldout_path,
        "decomposition": decomposition_path,
        "source_evaluator": SOURCE_EVALUATOR_PATH,
        "verifier": SCRIPT_PATH,
    }
    input_hashes_before = {key: sha256_file(path) for key, path in input_paths.items()}
    execution_head = git_head()

    plan, _plan_bytes = read_json(plan_path)
    main, _main_bytes = read_json(main_path)
    heldout, _heldout_bytes = read_json(heldout_path)
    decomposition, _decomposition_bytes = read_json(decomposition_path)
    check_nonunit_plan(plan)
    if sha256_file(PLAN_OWNER_REQUEST_PATH) != plan["owner_request_sha256"]:
        raise ValueError("nonunit owner request differs from the hash pinned in its plan")
    pinned_source = subprocess.check_output(
        ["git", "show", f"{plan['source_commit']}:experiments/cf22_pysr/evaluate.py"],
        cwd=REPO, stderr=subprocess.PIPE,
    )
    if sha256_bytes(pinned_source) != input_hashes_before["source_evaluator"]:
        raise ValueError("working source evaluator differs from the evaluator pinned by the plan")
    precision = int(plan["precision_bits"])
    tolerance = Fraction(plan["absolute_C_tolerance"])
    source.self_checks()

    saved_rows: dict[str, dict[str, Any]] = {}
    for dataset in (main, heldout):
        if not isinstance(dataset.get("rows"), list):
            raise ValueError("saved nonunit dataset has no rows list")
        for row in dataset["rows"]:
            row_id = row.get("id")
            if not isinstance(row_id, str) or row_id in saved_rows:
                raise ValueError(f"duplicate or invalid saved row id: {row_id!r}")
            saved_rows[row_id] = row

    decomposition_rows = decomposition.get("rows")
    if not isinstance(decomposition_rows, list):
        raise ValueError("decomposition output has no rows list")
    decomposed_by_id: dict[str, dict[str, Any]] = {}
    for row in decomposition_rows:
        row_id = row.get("id")
        if not isinstance(row_id, str) or row_id in decomposed_by_id:
            raise ValueError(f"duplicate or invalid decomposition row id: {row_id!r}")
        decomposed_by_id[row_id] = row

    expected_ids = {config["id"] for config in plan["configs"]}
    if len(expected_ids) != 20 or set(saved_rows) != expected_ids:
        raise ValueError("saved main/heldout rows do not match the frozen 20-config panel")
    if set(decomposed_by_id) != expected_ids:
        raise ValueError("decomposition rows do not match the frozen 20-config panel")

    for dataset in (main, heldout):
        provenance = dataset.get("provenance", {})
        if provenance.get("precision_bits") != precision:
            raise ValueError("saved evaluation precision differs from the frozen plan")
        if provenance.get("absolute_C_tolerance") != str(tolerance):
            raise ValueError("saved evaluation tolerance differs from the frozen plan")
        if provenance.get("old_evaluator_sha256") != input_hashes_before["source_evaluator"]:
            raise ValueError("saved panel was produced by a different source evaluator")

    results: dict[str, Any] = {}
    for config in plan["configs"]:
        row_id = config["id"]
        saved_row = saved_rows[row_id]
        decomp_row = decomposed_by_id[row_id]
        if saved_row.get("stage") != config["stage"]:
            raise ValueError(f"saved stage differs from plan for {row_id}")
        support = _support_for_config(config, saved_row, precision)
        assert_overlap(support["L"], saved_row["parameters"]["L"], f"{row_id} L")
        assert_overlap(support["S_rho"], saved_row["components"]["S_rho"], f"{row_id} S_rho")
        if support["amp_count"] != (
                support["squarefree_amp_count"] + support["non_squarefree_amp_count"]):
            raise ArithmeticError("amplifier squarefree/power partition failed")
        if any(value not in (-1, 1) for value in support["mu_by_n"]):
            raise ArithmeticError("source column Möbius signs are not squarefree +/-1 values")
        computed = _direct_group_sums(support)
        field_checks = _check_group_output(computed, decomp_row, tolerance)

        group_sum = computed["C_pair_sum"]
        saved_full_checks = {
            "saved_C": compare_values(group_sum, saved_row["C"], tolerance, f"{row_id} saved C"),
            "saved_full_C": compare_values(group_sum, saved_row["full_C"], tolerance, f"{row_id} saved full_C"),
            "decomposition_full_C": compare_values(group_sum, decomp_row["full_C"], tolerance,
                                                     f"{row_id} decomposition full_C"),
            "decomposition_C_pair_sum": compare_values(group_sum, decomp_row["C_pair_sum"], tolerance,
                                                        f"{row_id} decomposition C_pair_sum"),
        }
        results[row_id] = {
            "id": row_id,
            "configuration": {
                "U": support["U"],
                "P": support["P_description"],
                "orientation": support["orientation"],
            },
            "counts": {
                "columns": len(support["n_rows"]),
                "amplifiers": support["amp_count"],
                "amplifier_squarefree": support["squarefree_amp_count"],
                "amplifier_non_squarefree": support["non_squarefree_amp_count"],
                "amplifier_prime_powers": support["prime_power_amp_count"],
                "physical_u": len(support["u_rows"]),
                "raw_N_H": support["raw_N"],
                "raw_B": support["raw_bound"],
                "unordered_pairs": sum(computed["pair_counts"].values()),
                "pairs_by_group": computed["pair_counts"],
            },
            "raw_saved_matrix": {
                "sha256": saved_row["raw_periodic_sum"]["pair_matrix_sha256"],
                "dimensions": [len(support["matrix"]), len(support["matrix"])],
                "diagonal_used": False,
                "raw_scale_A_times_S_over_N": source.interval_json(computed["raw_scale"]),
            },
            "groups": computed["groups"],
            "group_interval_checks": field_checks,
            "full_interval_checks": saved_full_checks,
            "rough_rough_mask_correction_zero": computed["rough_correction_zero_check"],
        }

    # Conjugating every sixth-root character (orientation +/-) preserves each
    # real energy and the real saved pair kernel.
    orientation_checks: dict[str, Any] = {}
    config_by_id = {config["id"]: config for config in plan["configs"]}
    for row_id, row_result in results.items():
        config = config_by_id[row_id]
        opposite_id = row_id.rsplit("_o", 1)[0] + ("_o-1" if config["orientation"] == 1 else "_o1")
        if opposite_id not in results or row_id > opposite_id:
            continue
        opposite = results[opposite_id]
        for group in GROUPS:
            for field in ("C_contribution", "physical_subtotal", "raw_subtotal", "mask_correction"):
                left = interval_from_record(row_result["groups"][group][field])
                right = interval_from_record(opposite["groups"][group][field])
                comparison = compare_intervals(left, source.interval_json(right), tolerance)
                if not (comparison["overlaps"] and comparison["residual_contains_zero"]
                        and comparison["within_tolerance"]):
                    raise ArithmeticError(
                        f"orientation conjugation control failed for {row_id}/{opposite_id} "
                        f"{group}.{field}"
                    )
                orientation_checks.setdefault(row_id.rsplit("_o", 1)[0], {})[
                    f"{group}.{field}"
                ] = comparison

    input_hashes_after = {key: sha256_file(path) for key, path in input_paths.items()}
    if input_hashes_after != input_hashes_before:
        raise RuntimeError("an input or verifier changed during independent verification")
    if git_head() != execution_head:
        raise RuntimeError("repository HEAD changed during independent verification")

    return {
        "schema": "cf22-pair-groups-independent-verification-v1",
        "status": "PASS",
        "scope": "DIRECT_GROUP_ENERGY_CHECK_SAVED_20_CONFIGURATIONS",
        "source_commit": plan["source_commit"],
        "execution_head": execution_head,
        "provenance": {
            "input_sha256": input_hashes_before,
            "precision_bits": precision,
            "absolute_C_tolerance": str(tolerance),
            "runtime": _runtime(),
            "verifier_sha256": input_hashes_before["verifier"],
            "raw_sums_called": False,
            "raw_source": "saved nonunit raw_periodic_sum.pair_2re integer matrix",
            "physical_source": "canonical evaluate.py support, roots, residue symbols, and profiles",
        },
        "controls": {
            "frozen_20_configuration_panel": len(results) == 20,
            "orientation_conjugation": orientation_checks,
            "raw_diagonals_omitted": True,
            "all_amplifier_ideals_including_prime_powers": True,
            "group_partition": "rough_rough + cross + affected_affected exhausts unordered off-diagonal pairs",
        },
        "rows": [results[config["id"]] for config in plan["configs"]],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, default=DEFAULT_PLAN)
    parser.add_argument("--saved-main", type=Path, default=DEFAULT_MAIN)
    parser.add_argument("--saved-heldout", type=Path, default=DEFAULT_HELDOUT)
    parser.add_argument("--decomposition", type=Path, default=DEFAULT_DECOMPOSITION)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)

    output_path = args.output.resolve()
    if output_path.exists():
        raise FileExistsError(f"refusing to replace existing verification JSON: {output_path}")
    payload = verify(
        args.plan.resolve(), args.saved_main.resolve(), args.saved_heldout.resolve(),
        args.decomposition.resolve(),
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"verify_groups.py: {type(exc).__name__}: {exc}", file=sys.stderr)
        raise
