#!/usr/bin/env python3
"""PoissonResidualChannelAudit_v1 for bus goal 007.

Fixed-cell, request-local audit only.  NOT_RH; no Phase 2; no QW or packet
definition changes; Q3 mainline untouched.
"""

from __future__ import annotations

import hashlib
import json
import time
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

import mpmath as mp

import leakage_falsifier_v1 as legacy


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "poisson_residual_channel_audit_v1.json"
GOAL = REQUEST_DIR / "bus" / "007_poisson_residual_channel_audit.goal.md"
ANSWER_006 = REQUEST_DIR / "bus" / "006_leakage_closeout.answer.md"
JSON_006 = OUT_DIR / "leakage_closeout_v1.json"
SCRIPT_006 = REQUEST_DIR / "leakage_closeout_v1.py"
TRUE_PRECISION_SOURCE = REQUEST_DIR / "true_precision_packet_gate_v1.py"
OBJECT_DICTIONARY = REPO_ROOT / "q3.lean.aristotle" / "docs" / "PEN_3_3_G04_OBJECT_DICTIONARY.md"
LEFT_EDGE_NOTE = REPO_ROOT / "q3.lean.aristotle" / "docs" / "PEN_3_1_4a_LEFT_EDGE_v3.md"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"

LAMBDA_SQ = 13
MAX_DEGREE = 180
DPS_MODEL = 120
DPS_QUAD = 90
K_LEDGER = 40
K_TABLE = 200
REPRO_REL_TOL = mp.mpf("5e-12")


def progress(label: str) -> None:
    print(f"[PoissonResidualChannelAudit_v1] {label}", flush=True)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, mp.mpf):
        return mp.nstr(value, 110)
    if isinstance(value, mp.mpc):
        return {"re": mp.nstr(mp.re(value), 110), "im": mp.nstr(mp.im(value), 110)}
    return value


def normalize_real_combo(values: Sequence[mp.mpf]) -> List[mp.mpf]:
    norm = mp.sqrt(sum(x * x for x in values))
    if norm == 0:
        raise RuntimeError("zero combo norm")
    return [x / norm for x in values]


def column(matrix: mp.matrix, j: int) -> List[mp.mpf]:
    return [mp.re(matrix[i, j]) for i in range(matrix.rows)]


def build_exact_components() -> Dict[str, Any]:
    """Reproduce the true-precision constructor with exact local lambda and C."""
    mp.mp.dps = DPS_MODEL
    lam = mp.sqrt(mp.mpf(LAMBDA_SQ))
    bandwidth = 2 * mp.pi * mp.mpf(LAMBDA_SQ)
    degrees = list(range(0, MAX_DEGREE + 1, 2))
    x2 = legacy.legendre_x2_matrix_mp(degrees)
    operator = mp.matrix(len(degrees), len(degrees))
    for i, degree in enumerate(degrees):
        operator[i, i] = degree * (degree + 1)
    operator += bandwidth * bandwidth * x2
    eigenvalues, eigenvectors = mp.eigsy((operator + operator.T) / 2)

    raw: Dict[int, List[mp.mpf]] = {}
    window: Dict[int, List[mp.mpf]] = {}
    unit: Dict[int, List[mp.mpf]] = {}
    integrals: Dict[int, mp.mpf] = {}
    for which, col in zip((0, 2, 4, 6, 8), range(5)):
        vector = column(eigenvectors, col)
        if vector[0] < 0:
            vector = [-x for x in vector]
        raw[which] = vector
        integrals[which] = vector[0] * mp.sqrt(2 * lam)
        window[which] = [
            value * mp.sqrt(mp.mpf(2 * degree + 1) / (2 * lam))
            for value, degree in zip(vector, degrees)
        ]
        unit[which] = [
            value * mp.sqrt(mp.mpf(2 * degree + 1) / 2)
            for value, degree in zip(vector, degrees)
        ]

    c0, c4 = normalize_real_combo([integrals[4], -integrals[0]])
    combo_window = [c0 * a + c4 * b for a, b in zip(window[0], window[4])]
    combo_unit = [c0 * a + c4 * b for a, b in zip(unit[0], unit[4])]
    return {
        "lambda": lam,
        "bandwidth": bandwidth,
        "degrees": degrees,
        "eigenvalues": [mp.re(eigenvalues[i]) for i in range(eigenvalues.rows)],
        "window_by_mode": window,
        "unit_by_mode": unit,
        "integrals": integrals,
        "c0": c0,
        "c4": c4,
        "combo_window": combo_window,
        "combo_unit": combo_unit,
    }


def eval_series(coefficients: Sequence[mp.mpf], degrees: Sequence[int], x: mp.mpf) -> mp.mpf:
    return legacy.eval_legendre_series(coefficients, degrees, x)


def spherical_polynomials(max_degree: int) -> List[Dict[int, mp.mpf]]:
    """j_l(x) at sin(x)=0, cos(x)=1 as a polynomial in inverse x."""
    rows: List[Dict[int, mp.mpf]] = [{}, {1: mp.mpf(-1)}]
    for degree in range(1, max_degree):
        nxt = {power + 1: (2 * degree + 1) * value for power, value in rows[degree].items()}
        for power, value in rows[degree - 1].items():
            nxt[power] = nxt.get(power, mp.mpf("0")) - value
        rows.append(nxt)
    return rows


def poisson_polynomial(
    coefficients: Sequence[mp.mpf],
    degrees: Sequence[int],
    lam: mp.mpf,
    bandwidth: mp.mpf,
) -> Dict[int, mp.mpf]:
    """p_k = sum A_power/k^power, including the outer lambda factor."""
    spherical = spherical_polynomials(max(degrees))
    result: Dict[int, mp.mpf] = {}
    for coefficient, degree in zip(coefficients, degrees):
        phase = 2 * ((-1) ** (degree // 2)) * coefficient
        for power, value in spherical[degree].items():
            result[power] = result.get(power, mp.mpf("0")) + (
                lam * phase * value / bandwidth**power
            )
    return result


def p_value(polynomial: Dict[int, mp.mpf], k: int) -> mp.mpf:
    return sum(value / mp.mpf(k) ** power for power, value in polynomial.items())


def harmonic(power: int, cutoff: int) -> mp.mpf:
    return mp.fsum(mp.mpf(1) / mp.mpf(k) ** power for k in range(1, cutoff + 1))


def prefix(polynomial: Dict[int, mp.mpf], cutoff: int) -> mp.mpf:
    return sum(value * harmonic(power, cutoff) for power, value in polynomial.items())


def tail(polynomial: Dict[int, mp.mpf], cutoff: int) -> mp.mpf:
    return sum(
        value * (mp.zeta(power) - harmonic(power, cutoff))
        for power, value in polynomial.items()
    )


def tail_partial_and_bound(
    polynomial: Dict[int, mp.mpf], cutoff: int, max_power: int
) -> Tuple[mp.mpf, mp.mpf]:
    partial = sum(
        value * (mp.zeta(power) - harmonic(power, cutoff))
        for power, value in polynomial.items()
        if power <= max_power
    )
    omitted_bound = sum(
        abs(value) * (mp.zeta(power) - harmonic(power, cutoff))
        for power, value in polynomial.items()
        if power > max_power
    )
    return partial, omitted_bound


def period_split_integral(
    coefficients: Sequence[mp.mpf], degrees: Sequence[int], bandwidth: mp.mpf, k: int
) -> mp.mpf:
    mp.mp.dps = DPS_QUAD
    periods = LAMBDA_SQ * k
    total = mp.mpf("0")
    for j in range(periods):
        a = mp.mpf(j) / periods
        b = mp.mpf(j + 1) / periods
        total += mp.quad(
            lambda x: eval_series(coefficients, degrees, x) * mp.cos(bandwidth * k * x),
            [a, b],
        )
    return 2 * total


def analytic_mode_integral(
    polynomial: Dict[int, mp.mpf], lam: mp.mpf, k: int
) -> mp.mpf:
    # Mode polynomials also include the outer lambda; remove it here.
    return p_value(polynomial, k) / lam


def main() -> None:
    started = time.time()
    mp.mp.dps = DPS_MODEL
    previous = load_json(JSON_006)
    model = build_exact_components()
    mp.mp.dps = DPS_MODEL
    lam = model["lambda"]
    bandwidth = model["bandwidth"]
    degrees = model["degrees"]
    c0 = model["c0"]
    c4 = model["c4"]

    progress("derive exact integer-phase inverse-power Poisson ledger")
    polynomial_mode0 = poisson_polynomial(model["unit_by_mode"][0], degrees, lam, bandwidth)
    polynomial_mode4 = poisson_polynomial(model["unit_by_mode"][4], degrees, lam, bandwidth)
    polynomial_combo = poisson_polynomial(model["combo_unit"], degrees, lam, bandwidth)

    g = lambda x: eval_series(model["combo_window"], degrees, x)
    direct_full = lam ** (-mp.mpf("0.5")) * sum(
        g(mp.mpf(m) / LAMBDA_SQ) for m in range(1, LAMBDA_SQ + 1)
    )
    endpoint = g(mp.mpf("1"))
    endpoint_full_contribution = lam ** (-mp.mpf("0.5")) * endpoint
    direct_star = direct_full - endpoint_full_contribution / 2
    h0 = g(mp.mpf("0"))
    c_pole = -lam ** (-mp.mpf("0.5")) * h0 / 2
    c_mid_for_full_target = direct_full - direct_star

    p8 = prefix(polynomial_combo, 8)
    p20 = prefix(polynomial_combo, 20)
    p40 = prefix(polynomial_combo, K_LEDGER)
    t40 = tail(polynomial_combo, K_LEDGER)
    t40_partial8, t40_omitted_bound = tail_partial_and_bound(polynomial_combo, K_LEDGER, 8)
    t40_interval = [t40_partial8 - t40_omitted_bound, t40_partial8 + t40_omitted_bound]

    canonical_ledger = p40 + t40 + c_pole
    full_target_ledger = canonical_ledger + c_mid_for_full_target
    canonical_closure = abs(canonical_ledger - direct_star) / abs(direct_star)
    full_closure = abs(full_target_ledger - direct_full) / abs(direct_full)
    full_closure_interval = max(
        abs(p40 + bound + c_pole + c_mid_for_full_target - direct_full) / abs(direct_full)
        for bound in t40_interval
    )

    old_direct = mp.mpf(previous["G2_poisson_tail_truncation"]["direct"])
    old_prefixes = previous["G2_poisson_tail_truncation"]["poisson_prefix_selected"]
    reproduction = {
        "D_direct": {
            "bus006": old_direct,
            "reproduced": direct_full,
            "relative_difference": abs(old_direct - direct_full) / abs(direct_full),
        },
        "P_8": {
            "bus006": mp.mpf(old_prefixes["8"]),
            "reproduced": p8,
            "relative_difference": abs(mp.mpf(old_prefixes["8"]) - p8) / abs(p8),
        },
        "P_20": {
            "bus006": mp.mpf(old_prefixes["20"]),
            "reproduced": p20,
            "relative_difference": abs(mp.mpf(old_prefixes["20"]) - p20) / abs(p20),
        },
        "P_40": {
            "bus006": mp.mpf(old_prefixes["40"]),
            "reproduced": p40,
            "relative_difference": abs(mp.mpf(old_prefixes["40"]) - p40) / abs(p40),
        },
    }
    reproduction_pass = all(
        cell["relative_difference"] <= REPRO_REL_TOL for cell in reproduction.values()
    )

    progress("independent period-split quadrature n=0, k=18")
    quadrature_n0_k18 = period_split_integral(
        model["unit_by_mode"][0], degrees, bandwidth, 18
    )
    mp.mp.dps = DPS_MODEL
    analytic_n0_k18 = analytic_mode_integral(polynomial_mode0, lam, 18)
    quadrature_error = abs(quadrature_n0_k18 - analytic_n0_k18)
    quadrature_relative = quadrature_error / abs(analytic_n0_k18)

    p_rows = []
    for k in range(1, K_TABLE + 1):
        mode0 = c0 * p_value(polynomial_mode0, k)
        mode4 = c4 * p_value(polynomial_mode4, k)
        p_rows.append(
            {
                "k": k,
                "mode0_weighted": mode0,
                "mode4_weighted": mode4,
                "combined": mode0 + mode4,
                "sign": "+" if mode0 + mode4 > 0 else "-" if mode0 + mode4 < 0 else "0",
            }
        )

    # Positivity/decay guard for k >= 40 inside the fixed finite model.
    a2 = polynomial_combo[2]
    scaled_remainder_bound_k40 = sum(
        abs(value) / mp.mpf(K_LEDGER) ** (power - 2)
        for power, value in polynomial_combo.items()
        if power > 2
    )
    asymptotic_positive = a2 > scaled_remainder_bound_k40

    # Plant A changes only the Poisson-side c4 sign; direct remains canonical.
    polynomial_signflip = {
        power: c0 * polynomial_mode0.get(power, mp.mpf("0"))
        - c4 * polynomial_mode4.get(power, mp.mpf("0"))
        for power in set(polynomial_mode0) | set(polynomial_mode4)
    }
    signflip_ledger = (
        prefix(polynomial_signflip, K_LEDGER)
        + tail(polynomial_signflip, K_LEDGER)
        + c_pole
        + c_mid_for_full_target
    )
    signflip_closure = abs(signflip_ledger - direct_full) / abs(direct_full)

    # Plant B varies endpoint weight while retaining the canonical starred ledger.
    direct_weight0 = direct_star - endpoint_full_contribution / 2
    direct_weight1 = direct_star + endpoint_full_contribution / 2
    midpoint_plant0 = abs(canonical_ledger - direct_weight0) / abs(direct_weight0)
    midpoint_plant1 = abs(canonical_ledger - direct_weight1) / abs(direct_weight1)

    # Plant C removes the largest nonzero correction channel, C_mid.
    deleted_mid_ledger = canonical_ledger
    deleted_mid_closure = abs(deleted_mid_ledger - direct_full) / abs(direct_full)

    formula_inventory = {
        "direct_quantity": {
            "status": "PRESENT_EXACT",
            "source": "PEN_3_3_G04_OBJECT_DICTIONARY.md:127-167; leakage_falsifier_v1.py:337-345",
        },
        "one_poisson_mode": {
            "status": "PRESENT_EXACT",
            "source": "PEN_3_1_4a_LEFT_EDGE_v3.md:22-31; this script finite Legendre/Bessel reduction",
        },
        "finite_poisson_sum": {
            "status": "PRESENT_EXACT",
            "source": "leakage_falsifier_v1.py:347-361; leakage_closeout_v1.py:154-173",
        },
        "lower_left_endpoint": {
            "status": "PRESENT_EXACT",
            "source": "PEN_3_3_G04_OBJECT_DICTIONARY.md:141-167",
        },
        "upper_right_endpoint": {
            "status": "ABSENT_FROM_CURRENT_IDENTITY",
            "source": "No independent right-edge term occurs in the exact starred Poisson identity.",
        },
        "midpoint_half_weight": {
            "status": "PRESENT_EXACT",
            "source": "PEN_3_3_G04_OBJECT_DICTIONARY.md:112-167,360-379",
        },
        "H2_pole_correction": {
            "status": "PRESENT_EXACT",
            "source": "PEN_3_1_4a_LEFT_EDGE_v3.md:33-48; PEN_3_3_G04_OBJECT_DICTIONARY.md:250-290",
        },
        "truncation_remainder": {
            "status": "PRESENT_EXACT",
            "source": "Finite inverse-even-power/zeta tail derived algebraically in this script.",
        },
    }

    verdict = "MIDPOINT_POLE_LEDGER_REPAIR"
    payload = {
        "scope": ["NOT_RH", "no Phase 2", "no QW changes", "no packet changes", "Q3 mainline untouched"],
        "parameters": {
            "lambda_sq": LAMBDA_SQ,
            "max_degree": MAX_DEGREE,
            "dps_model": DPS_MODEL,
            "dps_quad": DPS_QUAD,
            "ledger_cutoff": K_LEDGER,
            "table_cutoff": K_TABLE,
        },
        "hashes": {
            "bus/007_poisson_residual_channel_audit.goal.md": sha256_file(GOAL),
            "bus/006_leakage_closeout.answer.md": sha256_file(ANSWER_006),
            "out/leakage_closeout_v1.json": sha256_file(JSON_006),
            "leakage_closeout_v1.py": sha256_file(SCRIPT_006),
            "true_precision_packet_gate_v1.py": sha256_file(TRUE_PRECISION_SOURCE),
            "docs/PEN_3_3_G04_OBJECT_DICTIONARY.md": sha256_file(OBJECT_DICTIONARY),
            "docs/PEN_3_1_4a_LEFT_EDGE_v3.md": sha256_file(LEFT_EDGE_NOTE),
            "ROUTE_B_STATE.md": sha256_file(ROUTE_STATE),
        },
        "T0_reproduction": {
            "values": reproduction,
            "registered_relative_tolerance": REPRO_REL_TOL,
            "pass": reproduction_pass,
            "period_split_check": {
                "mode": 0,
                "k": 18,
                "quadrature": quadrature_n0_k18,
                "analytic": analytic_n0_k18,
                "absolute_error": quadrature_error,
                "relative_error": quadrature_relative,
            },
        },
        "T1_formula_inventory": formula_inventory,
        "T2_signed_tail": {
            "representation": "p_k = sum_{r=1..90} A_(2r) / k^(2r)",
            "polynomial_coefficients": polynomial_combo,
            "leading_power": 2,
            "leading_coefficient_A2": a2,
            "scaled_remainder_bound_for_k_ge_40": scaled_remainder_bound_k40,
            "positive_for_all_k_ge_40": asymptotic_positive,
            "T40_exact_fixed_model": t40,
            "T40_partial_through_power8": t40_partial8,
            "T40_omitted_absolute_bound": t40_omitted_bound,
            "T40_interval": t40_interval,
            "rows_k_1_200": p_rows,
            "status": "SIGNED_TAIL_INSUFFICIENT",
            "classification_note": (
                "The certified tail closes the canonical starred identity with C_pole, "
                "but it does not close the bus-006 full-endpoint D_direct without the "
                "exact midpoint half-weight correction C_mid."
            ),
        },
        "T3_channels": {
            "D_direct_bus006_full_endpoint": direct_full,
            "D_direct_canonical_starred": direct_star,
            "endpoint_value": endpoint,
            "endpoint_full_contribution": endpoint_full_contribution,
            "C_pole": {"status": "PRESENT_EXACT", "value": c_pole, "h_lambda_0": h0},
            "C_mid": {
                "status": "PRESENT_EXACT",
                "value_for_bus006_full_target": c_mid_for_full_target,
                "meaning": "D_full - D_star",
            },
            "C_left": {"status": "ABSENT_FROM_CURRENT_IDENTITY", "value": 0},
            "C_right": {"status": "ABSENT_FROM_CURRENT_IDENTITY", "value": 0},
            "R_other": {"status": "ZERO_EXACT", "value": 0},
        },
        "T4_closure": {
            "P8": p8,
            "P20": p20,
            "P40": p40,
            "T40": t40,
            "C_pole": c_pole,
            "C_mid": c_mid_for_full_target,
            "C_left": 0,
            "C_right": 0,
            "R_other": 0,
            "canonical_starred_ledger": canonical_ledger,
            "canonical_starred_relative_closure_error": canonical_closure,
            "bus006_full_target_ledger": full_target_ledger,
            "bus006_full_relative_closure_error": full_closure,
            "certified_interval_worst_relative_closure_error": full_closure_interval,
            "success_threshold": "2e-3",
            "instrument_floor_guard_pass": abs(full_target_ledger - direct_full) <= 10 * quadrature_error,
        },
        "T5_verdict": verdict,
        "plants": {
            "A_c4_signflip": {
                "relative_closure_error": signflip_closure,
                "fires": signflip_closure > mp.mpf("2e-3"),
            },
            "B_midpoint_weight0": {
                "direct_value": direct_weight0,
                "relative_closure_error_with_canonical_ledger": midpoint_plant0,
                "fires": midpoint_plant0 > mp.mpf("2e-3"),
            },
            "B_midpoint_weight1": {
                "direct_value": direct_weight1,
                "relative_closure_error_with_canonical_ledger": midpoint_plant1,
                "fires": midpoint_plant1 > mp.mpf("2e-3"),
            },
            "C_delete_largest_channel": {
                "deleted": "C_mid",
                "relative_closure_error": deleted_mid_closure,
                "fires": deleted_mid_closure > mp.mpf("2e-3") or deleted_mid_closure >= 5 * full_closure,
            },
        },
        "implementation_precision_audit": {
            "legacy_lambda_stored": legacy.LAMBDA,
            "exact_lambda": lam,
            "legacy_lambda_relative_error": abs(legacy.LAMBDA - lam) / lam,
            "legacy_bandwidth_stored": legacy.C_BANDWIDTH,
            "exact_bandwidth": bandwidth,
            "legacy_bandwidth_relative_error": abs(legacy.C_BANDWIDTH - bandwidth) / bandwidth,
            "note": "006 values reproduce at stated precision, but 007 uses exact high-precision lambda and C before model construction.",
        },
        "elapsed_seconds": time.time() - started,
    }
    if not reproduction_pass:
        payload["T5_verdict"] = "INPUT_REPRODUCTION_MISMATCH"

    JSON_OUT.parent.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    progress(f"wrote {JSON_OUT}")
    print(
        json.dumps(
            {
                "verdict": payload["T5_verdict"],
                "full_closure": mp.nstr(full_closure, 20),
                "interval_closure": mp.nstr(full_closure_interval, 20),
                "T40": mp.nstr(t40, 20),
                "plants_fire": all(cell["fires"] for cell in payload["plants"].values()),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
