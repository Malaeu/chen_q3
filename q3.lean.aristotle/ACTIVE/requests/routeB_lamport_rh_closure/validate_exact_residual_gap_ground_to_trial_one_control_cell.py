#!/usr/bin/env python3
"""Independent fail-closed validation of the Goal 058 M1B control cell."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from flint import arb, ctx
import mpmath as mp


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
TWOLEVEL = HERE.parent / "routeB_twolevel_spectral_ladder"
OUT = TWOLEVEL / "out"
TRIAL = OUT / "portable_k_coeffs_lambda_sq_13_N_120.json"
GROUND = OUT / "nconv_anchor_lambda_sq_13_N_120.json"
BLOCK_CACHE = OUT / "nconv_anchor_block_cache_lambda_sq_13_N_120.json"
PILOT = TWOLEVEL / "routeb_ladder_pilot.py"
LEAN_N1 = REPO / "q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean"
LEAN_FINITE = REPO / "q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean"
DIRECTIVE = REPO / "docs/routeB_bus/proshka/PROSHKA_NEXT_AFTER_8C3AEC96_GOAL058_2026-08-12.md"
GENERATOR = HERE / "exact_residual_gap_ground_to_trial_one_control_cell.py"
RESULT = HERE / "EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_DATA_2026-08-12.json"
REPORT = HERE / "EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_REPORT_2026-08-12.md"

MODE_ORDER = list(range(-120, 121))
SOURCE_HASHES = {
    "trial": "0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88",
    "ground": "cbc556ef7c73c9aefa9f177bb59aeca5867ed6628e3f1cca6edb270bfc13e7f0",
    "block_cache": "17bf89f62dd5c512f0e75a283809f09ad703edd6dd54d127e9f371e0f4231928",
    "pilot": "b1b609da86456425200190c17bf2be7573f27f2135c4cc061915b9067b9868c5",
    "lean_n1": "f2f9d248a6f2ad703428c624ccbaf5a75b340655e4b4ebbbe3f1d77355523815",
    "lean_finite": "282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89",
    "directive": "48d10524b400ea0aa1e0050dd5fa3b3fd03fed451045f21207516c4da5b96aeb",
}
SOURCE_PATHS = {
    "trial": TRIAL,
    "ground": GROUND,
    "block_cache": BLOCK_CACHE,
    "pilot": PILOT,
    "lean_n1": LEAN_N1,
    "lean_finite": LEAN_FINITE,
    "directive": DIRECTIVE,
}
PLANTS = {
    "posthoc_q": "M1_SOURCE_TRIAL_PRECOMMIT_VIOLATION",
    "mode_order": "M1_SOURCE_MFIN_MODE_ORDER_MISMATCH",
    "parity_denominator": "M1_TRACKING_GAP_PARITY_UNJUSTIFIED",
    "interval_direction": "M1_RESIDUAL_GAP_ENVELOPE_DIRECTION_ERROR",
    "ground_oracle": "M1_MATVEC_GROUND_ORACLE_SURROGATE",
}


def fail(message: str) -> None:
    raise SystemExit(f"VALIDATE_M1_EXACT_RESIDUAL_GAP_CONTROL_CELL: FAIL: {message}")


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_pilot() -> Any:
    spec = importlib.util.spec_from_file_location("routeb_ladder_pilot_m1b_validator", PILOT)
    require(spec is not None and spec.loader is not None, "pilot import spec missing")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def mp_norm(vector: mp.matrix) -> mp.mpf:
    return mp.sqrt(sum(abs(vector[i]) ** 2 for i in range(vector.rows)))


def normalized_vector(rows: list[dict[str, Any]]) -> mp.matrix:
    require([int(row["n"]) for row in rows] == MODE_ORDER, "mode order drift")
    vector = mp.matrix([mp.mpc(str(row["re"]), str(row["im"])) for row in rows])
    return vector / mp_norm(vector)


def midpoint(text: str) -> mp.mpf:
    stripped = text.strip()
    if stripped.startswith("[") and " +/- " in stripped:
        stripped = stripped[1:].split(" +/- ", 1)[0]
    return mp.mpf(stripped)


def close_absolute(label: str, actual: mp.mpf, recorded_ball: str, tolerance: str) -> None:
    target = midpoint(recorded_ball)
    if abs(actual - target) > mp.mpf(tolerance):
        fail(f"{label} mismatch: actual={mp.nstr(actual, 80)} target={mp.nstr(target, 80)}")


def interval_from_record(record: dict[str, Any]) -> arb:
    return arb(record["lower"]).union(arb(record["upper"]))


def arb_close_relative(actual: arb, recorded: arb, tolerance: str = "1e-80") -> bool:
    scale = max(arb(1), abs(actual.mid()), abs(recorded.mid()))
    return abs(actual.mid() - recorded.mid()) <= arb(tolerance) * scale


def validate_structure(result: dict[str, Any], report: str) -> None:
    require(result.get("schema") == "exact_residual_gap_ground_to_trial_one_control_cell/v1", "schema drift")
    require(result.get("target") == "G3_M1B_EXACT_RESIDUAL_GAP_CONTROL_CELL", "target drift")
    require(result.get("cell") == {"m": 13, "N": 120, "coordinate_count": 241}, "cell drift")
    require(result.get("evidence_class") == ["FINITE_CELL", "CONDITIONAL"], "evidence class drift")
    require(result.get("classification") == "WEAK", "classification drift")
    require(result.get("outcome") == "M1_EXACT_RESIDUAL_GAP_CONTROL_CELL_CLASSIFIED", "outcome drift")
    require(result.get("pin") == {
        "head": "8c3aec968066eca3cb27cfb1d1d293601c30eaa2",
        "origin_rh_clean": "8c3aec968066eca3cb27cfb1d1d293601c30eaa2",
        "strict_startup": "P9_STRICT_PASS",
        "routeb_status": "CHECK_OK",
    }, "pin drift")
    require(result.get("arsenal_used") == ["C04", "C07", "C09", "C10"], "arsenal receipt drift")
    require(result.get("non_claims") == [
        "not a theorem",
        "not G1 closure",
        "not G3 closure",
        "not a cofinal estimate",
        "not Route B promotion",
        "not an RH claim",
    ], "non-claim boundary drift")
    require("**WEAK**" in report, "report classification missing")
    require("[FINITE_CELL][CONDITIONAL]" in report, "report evidence boundary missing")
    require(report.rstrip().endswith("`M1_EXACT_RESIDUAL_GAP_CONTROL_CELL_CLASSIFIED`"), "report outcome footer missing")


def validate_sources(result: dict[str, Any]) -> None:
    for name, path in SOURCE_PATHS.items():
        actual = sha256(path)
        require(actual == SOURCE_HASHES[name], f"{name} source SHA drift")
        recorded = result["source_lock"][name]
        require(recorded["sha256"] == actual and recorded["match"] is True, f"{name} recorded lock drift")
    require(result["source_identity"]["mode_order"] == MODE_ORDER, "persisted mode order drift")
    require(result["source_identity"]["K"] == "ccmWeilMatFinite 13 120 = W02 - WR - Prime", "matrix source identity drift")


def validate_spectrum_and_bounds(result: dict[str, Any], ground: dict[str, Any]) -> None:
    spectrum = result["certified_spectrum"]
    expected = {
        "epsilon0_even": (0, 1, 0),
        "epsilon0_odd": (0, 1, 1),
        "epsilon1_even": (1, 2, 2),
    }
    cache = ground["xi_m_y_cache"]
    intervals: dict[str, arb] = {}
    for label, (lower_count, upper_count, cache_index) in expected.items():
        record = spectrum[label]
        require(record["negative_count_at_lower"] == lower_count, f"{label} lower inertia drift")
        require(record["negative_count_at_upper"] == upper_count, f"{label} upper inertia drift")
        require(record["certificate"] == "OUTWARD_ROUNDED_ARB_VALIDATED_BALL_INVERSE_PLUS_MIDPOINT_LDL_STURM", f"{label} certificate drift")
        interval = interval_from_record(record)
        seed = arb(str(cache[cache_index]["mu"]))
        require(interval.contains(seed), f"{label} cached eigenvalue outside certified bracket")
        intervals[label] = interval
    require(intervals["epsilon0_even"] < intervals["epsilon0_odd"], "even/odd ground ordering not certified")
    require(intervals["epsilon0_odd"] < intervals["epsilon1_even"], "odd/even1 ordering not certified")

    a = arb(result["theorem_facing"]["a"])
    nu = arb(result["theorem_facing"]["nu"])
    delta_iso = intervals["epsilon0_odd"] - intervals["epsilon0_even"]
    alpha = a - intervals["epsilon0_even"]
    separation = intervals["epsilon0_odd"] - a
    require(delta_iso > 0 and alpha > 0 and separation > 0, "positive gap/alpha/separation not certified")
    rayleigh = alpha.upper() / delta_iso.lower()
    residual = (nu.upper() / separation.lower()) ** 2
    require(arb_close_relative(rayleigh, arb(result["bounds"]["U_rayleigh_upper"])), "Rayleigh envelope direction/value drift")
    require(arb_close_relative(residual, arb(result["bounds"]["U_residual_upper"])), "residual envelope direction/value drift")
    selected_sqrt = arb(result["bounds"]["selected_sqrt_upper"])
    require(selected_sqrt > arb("1e-3") and selected_sqrt < arb("1e-1"), "WEAK threshold replay failed")
    require(result["bounds"]["selected"] == "RAYLEIGH", "selected bound drift")


def validate_independent_dense_replay(result: dict[str, Any], trial: dict[str, Any], ground: dict[str, Any]) -> None:
    mp.mp.dps = 145
    pilot = load_pilot()
    matrix = pilot.build_tau_matrix(mp.sqrt(mp.mpf(13)), 120, 145)
    q = normalized_vector(trial["coefficients"])
    kq = matrix * q
    a_complex = sum(mp.conj(q[i]) * kq[i] for i in range(q.rows))
    residual = kq - mp.re(a_complex) * q
    nu = mp_norm(residual)
    close_absolute("independent a", mp.re(a_complex), result["theorem_facing"]["a"], "1e-100")
    close_absolute("independent nu", nu, result["theorem_facing"]["nu"], "1e-100")

    reflected = mp.matrix([q[240 - i] for i in range(241)])
    parity_defect = mp_norm(q - reflected)
    require(parity_defect > 0, "literal q unexpectedly became exactly even")
    close_absolute("independent q parity defect", parity_defect, result["parity"]["q"]["norm_q_minus_Jq"], "1e-100")
    require(result["parity"]["q"]["Jq_eq_q_literal_persisted_decimal_vector"] is False, "literal q parity guard drift")
    require(result["parity"]["K"]["source_ball_replay_all_entry_differences_contain_zero"] is True, "matrix parity replay drift")

    # Independent eigenpair-residual smoke validation of the three persisted
    # cache eigenpairs.  Their coordinates are persisted only at ordinary
    # decimal precision, so this detects a gross source/order mismatch but is
    # explicitly not eigenvalue authority at the 1e-59 scale.  The generator's
    # validated Arb inertia brackets remain the authority.
    residuals: list[mp.mpf] = []
    for cached in ground["xi_m_y_cache"][:3]:
        vector = normalized_vector(cached["xi_vector"])
        mu = mp.mpf(str(cached["mu"]))
        eigen_residual = mp_norm(matrix * vector - mu * vector)
        residuals.append(eigen_residual)
    require(max(residuals) < mp.mpf("1e-14"), f"cached eigenpair residual exceeds persistence floor: {mp.nstr(max(residuals), 50)}")
    print("independent_cached_eigenpair_residual_max=" + mp.nstr(max(residuals), 80))


def validate_plants(result: dict[str, Any]) -> None:
    for name, expected_code in PLANTS.items():
        completed = subprocess.run(
            [sys.executable, str(GENERATOR), "--plant", name],
            cwd=REPO,
            text=True,
            capture_output=True,
            check=False,
        )
        require(completed.returncode == 2, f"plant {name} exit code {completed.returncode}, expected 2")
        require(completed.stdout.strip() == expected_code, f"plant {name} emitted wrong stop code")
        require(result["plants"][name] == {
            "expected_code": expected_code,
            "observed_code": expected_code,
            "pass": True,
        }, f"plant {name} receipt drift")


def main() -> int:
    ctx.prec = 512
    require(RESULT.is_file(), "result missing")
    require(REPORT.is_file(), "report missing")
    result = json.loads(RESULT.read_text(encoding="utf-8"))
    report = REPORT.read_text(encoding="utf-8")
    trial = json.loads(TRIAL.read_text(encoding="utf-8"))
    ground = json.loads(GROUND.read_text(encoding="utf-8"))
    validate_structure(result, report)
    validate_sources(result)
    validate_spectrum_and_bounds(result, ground)
    validate_independent_dense_replay(result, trial, ground)
    validate_plants(result)
    print("classification=WEAK")
    print("scope=[FINITE_CELL][CONDITIONAL]")
    print("VALIDATE_M1_EXACT_RESIDUAL_GAP_CONTROL_CELL: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
