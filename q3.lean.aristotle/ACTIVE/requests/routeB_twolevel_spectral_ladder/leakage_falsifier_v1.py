#!/usr/bin/env python3
"""
LeakageFalsifier_v1 for Route B / Route Z E5.

Diagnostic only:
- NOT_RH
- no Phase 2
- no QW formula changes
- no packet-definition changes
- no Q3 mainline changes
"""

from __future__ import annotations

import hashlib
import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import mpmath as mp


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "leakage_falsifier_v1.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"
PEN_NOTE = REPO_ROOT / "q3.lean.aristotle" / "docs" / "PEN_3_1_4_SMOOTH_REMAINDER_v1.md"
GOAL_FILE = REQUEST_DIR / "bus" / "003_leakage_falsifier.goal.md"
COEFF_CACHE = OUT_DIR / "portable_k_coeffs_lambda_sq_13_N_120.json"

LAMBDA_SQ = 13
LAMBDA = mp.sqrt(LAMBDA_SQ)
C_BANDWIDTH = 2 * mp.pi * LAMBDA_SQ
MAX_DEGREE = 180
DPS_MODEL = 90
DPS_QUAD = 70
F1_NS = [0, 2, 4]
F1_KS = list(range(1, 9))


@dataclass
class ProlateModel:
    degrees: List[int]
    eigenvalues: Dict[int, mp.mpf]
    unit_coeffs: Dict[int, List[mp.mpf]]
    window_coeffs: Dict[int, List[mp.mpf]]
    unit_integrals: Dict[int, mp.mpf]
    window_integrals: Dict[int, mp.mpf]
    g04_combo_by_h: Dict[int, mp.mpf]


def progress(label: str) -> None:
    print(f"[LeakageFalsifier_v1] {label}", flush=True)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def rel(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REQUEST_DIR))
    except ValueError:
        try:
            return str(path.resolve().relative_to(REPO_ROOT))
        except ValueError:
            return str(path.resolve())


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, mp.mpf):
        return mp.nstr(value, 90)
    if isinstance(value, mp.mpc):
        return {"re": mp.nstr(mp.re(value), 90), "im": mp.nstr(mp.im(value), 90)}
    return value


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def normalize_real_combo(coefs: Sequence[mp.mpf]) -> List[mp.mpf]:
    nrm = mp.sqrt(sum(c * c for c in coefs))
    if nrm == 0:
        raise RuntimeError("zero prolate combo norm")
    return [c / nrm for c in coefs]


def legendre_x2_matrix_mp(degrees: Sequence[int]) -> mp.matrix:
    idx = {k: i for i, k in enumerate(degrees)}
    M = mp.matrix(len(degrees), len(degrees))
    for l in degrees:
        a = mp.mpf(l + 1) / (2 * l + 1)
        b = mp.mpf(l) / (2 * l + 1) if l > 0 else mp.mpf("0")
        terms: List[Tuple[int, mp.mpf]] = []
        lp = l + 1
        terms.append((lp + 1, a * mp.mpf(lp + 1) / (2 * lp + 1)))
        terms.append((lp - 1, a * mp.mpf(lp) / (2 * lp + 1)))
        if l > 0:
            lm = l - 1
            terms.append((lm + 1, b * mp.mpf(lm + 1) / (2 * lm + 1)))
            if lm > 0:
                terms.append((lm - 1, b * mp.mpf(lm) / (2 * lm + 1)))
        for k, coef in terms:
            if k in idx:
                M[idx[k], idx[l]] += coef * mp.sqrt(mp.mpf(2 * l + 1) / (2 * k + 1))
    return M


def column(vecs: mp.matrix, j: int) -> List[mp.mpf]:
    return [mp.re(vecs[i, j]) for i in range(vecs.rows)]


def build_prolate_model() -> ProlateModel:
    mp.mp.dps = DPS_MODEL
    degrees = list(range(0, MAX_DEGREE + 1, 2))
    X2 = legendre_x2_matrix_mp(degrees)
    A = mp.matrix(len(degrees), len(degrees))
    for i, k in enumerate(degrees):
        A[i, i] = k * (k + 1)
    A += C_BANDWIDTH * C_BANDWIDTH * X2
    vals, vecs = mp.eigsy((A + A.T) / 2)

    unit_coeffs: Dict[int, List[mp.mpf]] = {}
    window_coeffs: Dict[int, List[mp.mpf]] = {}
    unit_integrals: Dict[int, mp.mpf] = {}
    window_integrals: Dict[int, mp.mpf] = {}
    eigenvalues: Dict[int, mp.mpf] = {}
    raw_vectors: Dict[int, List[mp.mpf]] = {}
    for which, col in zip((0, 2, 4, 6, 8), range(5)):
        v = column(vecs, col)
        if v[0] < 0:
            v = [-x for x in v]
        raw_vectors[which] = v
        eigenvalues[which] = mp.re(vals[col])
        unit_coeffs[which] = [vi * mp.sqrt(mp.mpf(2 * deg + 1) / 2) for vi, deg in zip(v, degrees)]
        window_coeffs[which] = [vi * mp.sqrt(mp.mpf(2 * deg + 1) / (2 * LAMBDA)) for vi, deg in zip(v, degrees)]
        unit_integrals[which] = v[0] * mp.sqrt(2)
        window_integrals[which] = v[0] * mp.sqrt(2 * LAMBDA)

    g04_c = normalize_real_combo([window_integrals[4], -window_integrals[0]])
    return ProlateModel(
        degrees=degrees,
        eigenvalues=eigenvalues,
        unit_coeffs=unit_coeffs,
        window_coeffs=window_coeffs,
        unit_integrals=unit_integrals,
        window_integrals=window_integrals,
        g04_combo_by_h={0: g04_c[0], 4: g04_c[1]},
    )


def eval_legendre_series(coeffs: Sequence[mp.mpf], degrees: Sequence[int], t: mp.mpf) -> mp.mpf:
    max_degree = degrees[-1]
    out = coeffs[0]
    if max_degree == 0:
        return out
    p_prev = mp.mpf("1")
    p_curr = t
    degree_index = 1
    for k in range(1, max_degree):
        p_next = ((2 * k + 1) * t * p_curr - k * p_prev) / (k + 1)
        p_prev, p_curr = p_curr, p_next
        deg = k + 1
        if deg % 2 == 0:
            out += coeffs[degree_index] * p_curr
            degree_index += 1
    return out


def psi_unit(model: ProlateModel, n: int, t: mp.mpf) -> mp.mpf:
    return eval_legendre_series(model.unit_coeffs[n], model.degrees, t)


def psi_window(model: ProlateModel, n: int, t: mp.mpf) -> mp.mpf:
    return eval_legendre_series(model.window_coeffs[n], model.degrees, t)


def g04_window(model: ProlateModel, t: mp.mpf) -> mp.mpf:
    return sum(coef * psi_window(model, n, t) for n, coef in model.g04_combo_by_h.items())


def g04_unit(model: ProlateModel, t: mp.mpf) -> mp.mpf:
    return sum(coef * psi_unit(model, n, t) for n, coef in model.g04_combo_by_h.items())


def oscillatory_integral(model: ProlateModel, n: int, k: int) -> mp.mpf:
    mp.mp.dps = DPS_QUAD
    if k == 0:
        return model.unit_integrals[n]
    periods = LAMBDA_SQ * k
    total = mp.mpf("0")
    for j in range(periods):
        a = mp.mpf(j) / periods
        b = mp.mpf(j + 1) / periods
        total += mp.quad(lambda x: psi_unit(model, n, x) * mp.cos(C_BANDWIDTH * k * x), [a, b])
    return 2 * total


def linfit_power(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    xs = [mp.log(mp.mpf(row["k"])) for row in rows]
    ys = [mp.log(abs(mp.mpf(row["psi_ext"]))) for row in rows if mp.mpf(row["psi_ext"]) != 0]
    if len(xs) != len(ys) or len(xs) < 2:
        return {"status": "INSUFFICIENT", "p": None}
    xm = sum(xs) / len(xs)
    ym = sum(ys) / len(ys)
    slope = sum((x - xm) * (y - ym) for x, y in zip(xs, ys)) / sum((x - xm) ** 2 for x in xs)
    return {"status": "OK", "slope": slope, "p": -slope}


def sign_label(x: mp.mpf) -> str:
    if x > 0:
        return "+"
    if x < 0:
        return "-"
    return "0"


def f0_h2(model: ProlateModel, scale: mp.mpf) -> Dict[str, Any]:
    g0 = g04_window(model, mp.mpf("0"))
    ratio = abs(g0) / scale if scale else mp.inf
    holds = ratio <= mp.mpf("1e-8")
    return {
        "g04_0": g0,
        "abs_g04_0": abs(g0),
        "window_scale_norm_E_g04": scale,
        "abs_over_scale": ratio,
        "registered_threshold": "1e-8 * scale",
        "code": "H2_HOLDS" if holds else "REPAIR_H2_POLE_CANCEL",
        "H2_holds": holds,
    }


def f1_integer_samples(model: ProlateModel) -> Dict[str, Any]:
    rows: Dict[int, List[Dict[str, Any]]] = {}
    mu_rows: Dict[int, Dict[str, Any]] = {}
    all_ratio_pass = True
    all_sign_pass = True
    for n in F1_NS:
        progress(f"F1 oscillatory integrals n={n}")
        mu = model.unit_integrals[n] / psi_unit(model, n, mp.mpf("0"))
        phase = 1 if n % 4 == 0 else -1
        mu_rows[n] = {
            "i_power_n": phase,
            "mu_signed": mu,
            "mu_abs": abs(mu),
            "mu_source": "integral_0 / psi_n(0), with i^n phase book",
        }
        n_rows: List[Dict[str, Any]] = []
        psi1: Optional[mp.mpf] = None
        for k in F1_KS:
            integ = oscillatory_integral(model, n, k)
            psi_ext = integ / mu
            if k == 1:
                psi1 = psi_ext
            ratio = None
            if psi1 is not None and psi1 != 0:
                ratio = abs(psi_ext) * (k**2) / (LAMBDA * abs(psi1))
            n_rows.append(
                {
                    "n": n,
                    "k": k,
                    "integral_mu_psi": integ,
                    "psi_ext": psi_ext,
                    "sign": sign_label(mp.re(psi_ext)),
                    "ratio_abs_psi_k_k2_over_lambda_abs_psi1": ratio,
                }
            )
        checked = [row for row in n_rows if row["k"] in (2, 3, 4)]
        ratio_pass = all(
            row["ratio_abs_psi_k_k2_over_lambda_abs_psi1"] is not None
            and mp.mpf("0.5") <= row["ratio_abs_psi_k_k2_over_lambda_abs_psi1"] <= mp.mpf("1.5")
            for row in checked
        )
        nonzero_signs = [row["sign"] for row in n_rows if row["sign"] != "0"]
        sign_pass = bool(nonzero_signs) and len(set(nonzero_signs)) == 1
        power_fit = linfit_power(n_rows[1:])
        rows[n] = n_rows
        mu_rows[n]["ratio_pass_k_2_3_4"] = ratio_pass
        mu_rows[n]["constant_sign_k_1_8"] = sign_pass
        mu_rows[n]["power_fit_abs_psi_vs_k_k_2_8"] = power_fit
        all_ratio_pass = all_ratio_pass and ratio_pass
        all_sign_pass = all_sign_pass and sign_pass
    return {
        "mu": mu_rows,
        "samples": rows,
        "all_ratio_pass_k_2_3_4": all_ratio_pass,
        "all_constant_sign_pass": all_sign_pass,
        "code": "INTEGER_SAMPLING_CONFIRMED" if all_ratio_pass and all_sign_pass else "SIN_VANISHING_REFUTED",
    }


def combo_integral(model: ProlateModel, integrals_by_n: Dict[int, Dict[int, mp.mpf]], k: int) -> mp.mpf:
    return sum(coef * integrals_by_n[n][k] for n, coef in model.g04_combo_by_h.items())


def combo_integral_phase_forced(
    model: ProlateModel,
    integrals_by_n: Dict[int, Dict[int, mp.mpf]],
    mu_by_n: Dict[int, mp.mpf],
    k: int,
) -> mp.mpf:
    total = mp.mpf("0")
    for n, coef in model.g04_combo_by_h.items():
        mu = mu_by_n[n]
        if mu == 0:
            total += coef * integrals_by_n[n][k]
        else:
            total += coef * (abs(mu) / mu) * integrals_by_n[n][k]
    return total


def f2_left_edge(
    model: ProlateModel,
    scale: mp.mpf,
    f0: Dict[str, Any],
    f1: Dict[str, Any],
) -> Dict[str, Any]:
    g0 = mp.mpf(f0["g04_0"])
    direct_terms = [
        {
            "m": m,
            "t_eval": mp.mpf(m) / LAMBDA_SQ,
            "g04_value": g04_window(model, mp.mpf(m) / LAMBDA_SQ),
        }
        for m in range(1, LAMBDA_SQ + 1)
    ]
    direct = LAMBDA ** (-mp.mpf("0.5")) * sum(row["g04_value"] for row in direct_terms)

    integrals_by_n: Dict[int, Dict[int, mp.mpf]] = {n: {} for n in model.g04_combo_by_h}
    for n in model.g04_combo_by_h:
        for k in range(1, 9):
            cached = None
            for row in f1["samples"].get(n, []):
                if row["k"] == k:
                    cached = mp.mpf(row["integral_mu_psi"])
                    break
            integrals_by_n[n][k] = cached if cached is not None else oscillatory_integral(model, n, k)

    mu_by_n = {int(n): mp.mpf(cell["mu_signed"]) for n, cell in f1["mu"].items()}
    poisson_terms = [{"k": k, "combo_integral": combo_integral(model, integrals_by_n, k)} for k in range(1, 9)]
    poisson_uncorrected = LAMBDA * sum(row["combo_integral"] for row in poisson_terms)
    correction = LAMBDA ** (-mp.mpf("0.5")) * g0 / 2 if not f0["H2_holds"] else mp.mpf("0")
    poisson = poisson_uncorrected - correction

    planted_terms = [
        {
            "k": k,
            "combo_integral_phase_forced_plus_one": combo_integral_phase_forced(model, integrals_by_n, mu_by_n, k),
        }
        for k in range(1, 9)
    ]
    planted_uncorrected = LAMBDA * sum(row["combo_integral_phase_forced_plus_one"] for row in planted_terms)
    planted = planted_uncorrected - correction

    rel = abs(direct - poisson) / max(abs(direct), mp.mpf("1e-300"))
    planted_rel = abs(direct - planted) / max(abs(direct), mp.mpf("1e-300"))
    planted_delta_vs_normal = abs(planted - poisson) / max(abs(poisson), mp.mpf("1e-300"))
    magnitude_ratio = abs(direct) / scale if scale else mp.inf
    left_match = rel <= mp.mpf("1e-3")
    magnitude_pass = mp.mpf("1.7e-29") <= magnitude_ratio <= mp.mpf("4.2e-28")
    planted_breaks = planted_rel > mp.mpf("1e-2") and planted_delta_vs_normal > mp.mpf("1e-2")
    phase_factors = {str(n): (1 if n % 4 == 0 else -1) for n in model.g04_combo_by_h}
    planted_informative = len(set(phase_factors.values())) > 1
    return {
        "direct_E_g04_left_edge": direct,
        "direct_terms": direct_terms,
        "poisson_k_1_8": poisson,
        "poisson_uncorrected_k_1_8": poisson_uncorrected,
        "h2_correction_subtracted": correction,
        "poisson_terms": poisson_terms,
        "relative_agreement": rel,
        "relative_agreement_pass_1e_minus_3": left_match,
        "magnitude_abs_direct_over_norm_E_g04": magnitude_ratio,
        "magnitude_registered_band": ["1.7e-29", "4.2e-28"],
        "magnitude_registered_pass": magnitude_pass,
        "planted_phase_forced_plus_one": {
            "value": planted,
            "relative_agreement": planted_rel,
            "delta_vs_normal_poisson": planted_delta_vs_normal,
            "breaks_agreement": planted_breaks,
            "informative_for_current_g04": planted_informative,
            "phase_factors_in_current_g04": phase_factors,
            "note": "Current project g04 is the h0/h4 zero-integral packet; i^0 and i^4 are both +1, so this plant is expected to be inert unless the packet includes an i^2 branch.",
        },
        "code": "LEFT_EDGE_MATCH" if left_match and magnitude_pass and planted_breaks else "LEFT_EDGE_MISMATCH",
    }


def main() -> None:
    started = time.time()
    mp.mp.dps = DPS_MODEL
    coeff_cache = load_json(COEFF_CACHE)
    scale = mp.mpf(str(coeff_cache["raw_norm_g04"]))
    progress("build mpmath prolate model")
    model = build_prolate_model()
    f0 = f0_h2(model, scale)
    progress("F1 integer samples")
    f1 = f1_integer_samples(model)
    progress("F2 left edge")
    f2 = f2_left_edge(model, scale, f0, f1)
    codes = [f0["code"], f1["code"], f2["code"]]
    payload = {
        "goal": "LeakageFalsifier_v1",
        "diagnostic_scope": {
            "NOT_RH": True,
            "phase2_run": False,
            "qW_formula_changed": False,
            "packet_definition_changed": False,
            "q3_mainline_touched": False,
        },
        "inputs": {
            "goal_file": {"path": rel(GOAL_FILE), "sha256": sha256_file(GOAL_FILE)},
            "pen_note_read_only": {"path": rel(PEN_NOTE), "sha256": sha256_file(PEN_NOTE)},
            "coefficient_cache_for_scale": {"path": rel(COEFF_CACHE), "sha256": sha256_file(COEFF_CACHE)},
            "true_precision_constructor_reference": {
                "path": rel(REQUEST_DIR / "true_precision_packet_gate_v1.py"),
                "sha256": sha256_file(REQUEST_DIR / "true_precision_packet_gate_v1.py"),
                "note": "formula copied locally to avoid importing routeb_ladder_pilot/scipy",
            },
        },
        "parameters": {
            "lambda_sq": LAMBDA_SQ,
            "lambda": LAMBDA,
            "c": C_BANDWIDTH,
            "max_degree": MAX_DEGREE,
            "dps_model": DPS_MODEL,
            "dps_quad": DPS_QUAD,
            "g04_combo_by_h": model.g04_combo_by_h,
            "normalization": "h_n L2-normalized on [-lambda,lambda] for time-side g04; F1 uses unit [-1,1] psi ratios where scale cancels",
        },
        "sanity": {
            "g04_endpoint_t_eq_1_recomputed": g04_window(model, mp.mpf("1")),
            "g04_endpoint_cache": coeff_cache.get("g04_endpoint_t_eq_1"),
            "raw_norm_g04_cache": scale,
            "pN_norm_g04_cache": coeff_cache.get("pN_norm_g04"),
        },
        "F0_H2_fork": f0,
        "F1_integer_samples": f1,
        "F2_left_edge_crosscheck": f2,
        "codes": codes,
        "elapsed_seconds": time.time() - started,
    }
    write_json(JSON_OUT, payload)
    progress(f"wrote {rel(JSON_OUT)}")


if __name__ == "__main__":
    main()
