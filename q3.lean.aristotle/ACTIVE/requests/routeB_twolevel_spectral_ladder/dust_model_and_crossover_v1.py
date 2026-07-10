#!/usr/bin/env python3
"""
DustModelAndCrossover_v1 for Route B / Route Z E5.

Diagnostic only:
- not RH
- no Phase 2
- no QW formula changes
- no packet-definition changes
- no Q3 mainline changes

Uses dumped per-j data from ZeroSumProfile_v2 for D1-D3 and fresh cheap
J=200 K-profiles from the existing true-precision packet constructor for D4.
"""

from __future__ import annotations

import cmath
import json
import math
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import mpmath as mp

import routeb_ladder_pilot as pilot
import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
PROFILE_JSON = OUT_DIR / "zero_sum_profile_v2.json"
ADDENDUM_JSON = OUT_DIR / "zero_sum_profile_v2_addendum.json"
PHASE_LEDGER_JSON = OUT_DIR / "phase_trace_and_ledger_filter_v1.json"
JSON_OUT = OUT_DIR / "dust_model_and_crossover_v1.json"
REPORT = REQUEST_DIR / "dust_model_and_crossover_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"

LAMBDA_SQ = 13
N = 120
REGISTERED_D = mp.mpf("8.6e-33")
ZERO_CONSISTENT_FACTOR = mp.mpf("10")
MAIN_DPS = 80
D4_PACKET_DPS = 90
D4_QUAD_ORDER = 192
D4_J = 200
DYADIC_BLOCKS = [
    (mp.mpf("14"), mp.mpf("28")),
    (mp.mpf("28"), mp.mpf("56")),
    (mp.mpf("56"), mp.mpf("112")),
    (mp.mpf("112"), mp.mpf("224")),
    (mp.mpf("224"), mp.mpf("448")),
    (mp.mpf("448"), mp.mpf("896")),
]


def progress(label: str) -> None:
    print(f"[DustModelAndCrossover_v1] {label}", flush=True)


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, (mp.mpf, mp.mpc)):
        return mp.nstr(value, 90)
    return value


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fmt(value: Any, digits: int = 12) -> str:
    if value is None:
        return "UNKNOWN"
    if isinstance(value, str):
        try:
            return mp.nstr(mp.mpf(value), digits)
        except Exception:
            return value
    return mp.nstr(value, digits)


def parse_complex_text(value: Any) -> complex:
    text = str(value).strip().strip("()").replace(" ", "")
    if text.endswith("j"):
        body = text[:-1]
        split_at = None
        for idx in range(1, len(body)):
            if body[idx] in "+-" and body[idx - 1] not in "eE":
                split_at = idx
        if split_at is None:
            return complex(0.0, float(body))
        return complex(float(body[:split_at]), float(body[split_at:]))
    return complex(float(text), 0.0)


def normalize_rows(raw_rows: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows = []
    for row in raw_rows:
        k = parse_complex_text(row["K"])
        rows.append(
            {
                "j": int(row["j"]),
                "gamma": mp.mpf(str(row["gamma"])),
                "K": k,
                "abs_K": mp.mpf(str(row["abs_K"])),
                "Re_K": mp.mpf(str(row["Re_K"])),
                "Im_K": mp.mpf(str(row["Im_K"])),
                "S_J_over_denom": mp.mpf(str(row["S_J_over_denom"])),
                "term": mp.mpf(str(row["term"])),
            }
        )
    return rows


def median(values: Sequence[mp.mpf]) -> mp.mpf:
    vals = sorted(values)
    n = len(vals)
    if n == 0:
        return mp.nan
    if n % 2:
        return vals[n // 2]
    return (vals[n // 2 - 1] + vals[n // 2]) / 2


def average_ranks(values: Sequence[mp.mpf]) -> List[mp.mpf]:
    indexed = sorted((val, idx) for idx, val in enumerate(values))
    ranks = [mp.mpf("0") for _ in values]
    i = 0
    while i < len(indexed):
        j = i + 1
        while j < len(indexed) and indexed[j][0] == indexed[i][0]:
            j += 1
        avg = (mp.mpf(i + 1) + mp.mpf(j)) / 2
        for _, idx in indexed[i:j]:
            ranks[idx] = avg
        i = j
    return ranks


def pearson(xs: Sequence[mp.mpf], ys: Sequence[mp.mpf]) -> Optional[mp.mpf]:
    if len(xs) < 2:
        return None
    xm = sum(xs) / len(xs)
    ym = sum(ys) / len(ys)
    cov = sum((x - xm) * (y - ym) for x, y in zip(xs, ys))
    vx = sum((x - xm) ** 2 for x in xs)
    vy = sum((y - ym) ** 2 for y in ys)
    if vx == 0 or vy == 0:
        return None
    return cov / mp.sqrt(vx * vy)


def spearman(xs: Sequence[mp.mpf], ys: Sequence[mp.mpf]) -> Optional[mp.mpf]:
    if len(xs) != len(ys) or len(xs) < 2:
        return None
    return pearson(average_ranks(xs), average_ranks(ys))


def wrap_pi_float(x: float) -> float:
    return ((x + math.pi / 2) % math.pi) - math.pi / 2


def phase_fit(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    if not rows:
        return {
            "point_count": 0,
            "phi0": None,
            "circular_MAD": None,
            "median_im_over_re_corrected": None,
        }
    phases = [math.atan2(row["K"].imag, row["K"].real) for row in rows]
    mean = sum(cmath.exp(2j * phase) for phase in phases) / len(phases)
    phi = 0.5 * math.atan2(mean.imag, mean.real)
    residuals = [abs(wrap_pi_float(phase - phi)) for phase in phases]
    corrected = [row["K"] * cmath.exp(-1j * phi) for row in rows]
    med_im = median([mp.mpf(str(abs(z.imag))) for z in corrected])
    med_re = median([mp.mpf(str(abs(z.real))) for z in corrected])
    return {
        "point_count": len(rows),
        "phi0": mp.mpf(str(phi)),
        "circular_MAD": median([mp.mpf(str(r)) for r in residuals]),
        "median_abs_Im_corrected": med_im,
        "median_abs_Re_corrected": med_re,
        "median_im_over_re_corrected": med_im / max(med_re, mp.mpf("1e-300")),
    }


def D1_additivity(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    block_rows = []
    for lo, hi in DYADIC_BLOCKS:
        block = [row for row in rows if lo <= row["gamma"] < hi]
        im_vals = [abs(row["Im_K"]) for row in block]
        abs_vals = [row["abs_K"] for row in block]
        med_im = median(im_vals)
        med_abs = median(abs_vals)
        rel_to_d = abs(med_im - REGISTERED_D) / REGISTERED_D if block else mp.nan
        block_rows.append(
            {
                "gamma_range": [lo, hi],
                "count": len(block),
                "median_abs_Im_K": med_im,
                "median_abs_K": med_abs,
                "registered_d": REGISTERED_D,
                "relative_deviation_from_d": rel_to_d,
                "registered_pm50_pass": rel_to_d <= mp.mpf("0.5"),
                "physical_crossover_in_block": lo <= 4 * mp.pi * LAMBDA_SQ < hi,
            }
        )
    med_ims = [row["median_abs_Im_K"] for row in block_rows if row["count"]]
    med_abss = [row["median_abs_K"] for row in block_rows if row["count"]]
    all_block_pass = all(row["registered_pm50_pass"] for row in block_rows if row["count"])
    corr = spearman(med_ims, med_abss)
    dust_zone_blocks = [
        row
        for row in block_rows
        if row["count"] and row["median_abs_K"] <= ZERO_CONSISTENT_FACTOR * REGISTERED_D
    ]
    dust_zone_pass = bool(dust_zone_blocks) and all(row["registered_pm50_pass"] for row in dust_zone_blocks)
    return {
        "definition": "raw dyadic block medians of |Im K_j| from dumped K_j rows",
        "registered_d": REGISTERED_D,
        "zero_consistent_threshold_absK": ZERO_CONSISTENT_FACTOR * REGISTERED_D,
        "dyadic_blocks": block_rows,
        "raw_all_blocks_registered_pm50_pass": all_block_pass,
        "block_median_absIm_vs_block_median_absK_spearman": corr,
        "dust_zone_block_count": len(dust_zone_blocks),
        "dust_zone_blocks_pm50_pass": dust_zone_pass,
        "interpretation": (
            "early dust-zone blocks match d, but the literal all-block raw median check is not satisfied"
            if not all_block_pass
            else "literal all-block raw median check satisfies registered d window"
        ),
        "code": "DUST_ADDITIVE_CONFIRMED" if all_block_pass else "DUST_ADDITIVE_REFUTED",
    }


def D2_zoned_judge(rows: Sequence[Dict[str, Any]], d1: Dict[str, Any]) -> Dict[str, Any]:
    threshold = ZERO_CONSISTENT_FACTOR * REGISTERED_D
    judged = [row for row in rows if row["abs_K"] >= threshold]
    fit = phase_fit(judged)
    first100 = [row for row in rows if row["j"] <= 100]
    zero_consistent = [row for row in first100 if row["abs_K"] < threshold]
    frac = mp.mpf(len(zero_consistent)) / max(len(first100), 1)
    realness_pass = (
        fit["point_count"] > 0
        and fit["circular_MAD"] <= mp.mpf("0.05")
        and fit["median_im_over_re_corrected"] <= mp.mpf("0.05")
    )
    frac_pass = mp.mpf("0.5") <= frac <= mp.mpf("0.85")
    return {
        "threshold_absK_ge_10d": threshold,
        "judged_point_count": len(judged),
        "zero_consistent_definition": "|K_j| < 10*d in the j<=100 early zone",
        "j_le_100_zero_consistent_count": len(zero_consistent),
        "j_le_100_total": len(first100),
        "j_le_100_zero_consistent_fraction": frac,
        "zero_consistent_fraction_registered_pass": frac_pass,
        "realness_on_absK_ge_10d": fit,
        "realness_registered_pass": realness_pass,
        "pass": realness_pass and frac_pass,
        "code": "ZONED_JUDGE_PASS" if realness_pass and frac_pass else "ZONED_JUDGE_FAIL",
        "D1_code_seen": d1["code"],
    }


def D3_early_zone(rows: Sequence[Dict[str, Any]], profile: Dict[str, Any]) -> Dict[str, Any]:
    early = [row for row in rows if row["j"] <= 30]
    selected_js = {1, 2, 3, 5, 10, 20, 30}
    selected = [
        {"j": row["j"], "gamma": row["gamma"], "abs_K": row["abs_K"]}
        for row in early
        if row["j"] in selected_js
    ]
    first_share = mp.mpf(str(profile.get("P1", {}).get("first_zero_share", rows[0]["term"] / mp.mpf(str(profile["a1_raw"])))))
    max_abs = max((row["abs_K"] for row in early), default=mp.mpf("0"))
    med_abs = median([row["abs_K"] for row in early])
    return {
        "j_range": "j<=30",
        "max_abs_K_j_le_30": max_abs,
        "median_abs_K_j_le_30": med_abs,
        "selected_upper_bounds": selected,
        "first_zero_share_original": first_share,
        "first_zero_share_relabel": "<= 3.5e-6 (ZC)",
        "first_zero_share_ZC_pass": first_share <= mp.mpf("3.5e-6"),
    }


def with_tp_context(lambda_sq: int, n_bound: int):
    class Context:
        def __enter__(self):
            self.old_lambda_sq = tp.LAMBDA_SQ
            self.old_n = tp.N
            tp.LAMBDA_SQ = lambda_sq
            tp.N = n_bound

        def __exit__(self, exc_type, exc, tb):
            tp.LAMBDA_SQ = self.old_lambda_sq
            tp.N = self.old_n

    return Context()


def coeff_norm(coeffs: Sequence[mp.mpc]) -> mp.mpf:
    return mp.sqrt(sum(abs(z) ** 2 for z in coeffs))


def normalize_coeffs(coeffs: Sequence[mp.mpc]) -> Tuple[List[mp.mpc], mp.mpf]:
    nrm = coeff_norm(coeffs)
    if nrm == 0:
        raise RuntimeError("zero coefficient norm")
    return [z / nrm for z in coeffs], nrm


def vector_from_coeffs(coeffs: Sequence[mp.mpc]) -> mp.matrix:
    v = mp.matrix(len(coeffs), 1)
    for i, coeff in enumerate(coeffs):
        v[i] = coeff
    return v


def K_from_coeffs(lambda_sq: int, n_bound: int, t: mp.mpf, coeffs: Sequence[mp.mpc]) -> mp.mpc:
    L = mp.log(lambda_sq)
    lam = mp.sqrt(lambda_sq)
    total = mp.mpc(0)
    n0 = -n_bound
    for idx, coeff in enumerate(coeffs):
        n = n0 + idx
        alpha = 2 * mp.pi * n / L - t
        z = 1j * alpha * L
        if abs(z) < mp.mpf("1e-40"):
            integral = L
        else:
            integral = L * mp.expm1(z) / z
        total += coeff * integral
    return (lam ** (1j * t)) * total / mp.sqrt(L)


def packet_for_anchor(lambda_sq: int, n_bound: int) -> Dict[str, Any]:
    with with_tp_context(lambda_sq, n_bound):
        mp.mp.dps = D4_PACKET_DPS
        model = tp.build_prolate_model(D4_PACKET_DPS)
        n_values = list(range(-n_bound, n_bound + 1))
        low = tp.integrate_coefficients(
            model,
            dps=D4_PACKET_DPS,
            quad_order=D4_QUAD_ORDER // 2,
            n_values=n_values,
            names=["g04"],
        )
        high = tp.integrate_coefficients(
            model,
            dps=D4_PACKET_DPS,
            quad_order=D4_QUAD_ORDER,
            n_values=n_values,
            names=["g04"],
        )
        coeff_diff = max(abs(a - b) for a, b in zip(low.coeffs["g04"], high.coeffs["g04"]))
        coeffs, pN_norm = normalize_coeffs(high.coeffs["g04"])
        g04_endpoint = tp.eval_all_g(model, mp.mpf("1"))["g04"]
    lam = mp.sqrt(lambda_sq)
    k_edge = mp.sqrt(lam) * g04_endpoint / high.raw_norms["g04"]
    return {
        "coeffs_normalized": coeffs,
        "pN_norm_g04": pN_norm,
        "raw_norm_g04": high.raw_norms["g04"],
        "coeff_max_abs_diff_vs_half_q": coeff_diff,
        "g04_endpoint_t_eq_1": g04_endpoint,
        "k_edge": k_edge,
        "k_edge_abs": abs(k_edge),
    }


def anchor_profile(lambda_sq: int, n_bound: int, gammas: Sequence[mp.mpf]) -> Dict[str, Any]:
    started = time.time()
    progress(f"D4 packet/profile lambda_sq={lambda_sq} N={n_bound}")
    packet = packet_for_anchor(lambda_sq, n_bound)
    coeffs = packet["coeffs_normalized"]
    mp.mp.dps = MAIN_DPS
    T = pilot.build_tau_matrix(mp.sqrt(lambda_sq), n_bound, MAIN_DPS)
    v = vector_from_coeffs(coeffs)
    Tv = T * v
    a1_raw = mp.re(pilot.inner(v, Tv))
    rows = []
    partial = mp.mpf("0")
    for j, gamma in enumerate(gammas, start=1):
        kval = K_from_coeffs(lambda_sq, n_bound, gamma, coeffs)
        abs_k = abs(kval)
        term = 2 * abs_k**2
        partial += term
        rows.append(
            {
                "j": j,
                "gamma": gamma,
                "K": kval,
                "abs_K": abs_k,
                "term": term,
                "S_J_over_a1": partial / a1_raw,
            }
        )
    peak = max(rows, key=lambda row: row["abs_K"])
    expected = 4 * mp.pi * lambda_sq
    peak_rel_error = abs(peak["gamma"] - expected) / expected
    c_table = []
    for J in (100, 150, 200):
        row = rows[J - 1]
        residual = a1_raw * (1 - row["S_J_over_a1"])
        denom = mp.log(row["gamma"] / (2 * mp.pi)) + 1
        c_val = mp.sqrt(residual * mp.pi * row["gamma"] / denom) if residual > 0 else None
        c_table.append(
            {
                "J": J,
                "Gamma": row["gamma"],
                "S_J_over_a1": row["S_J_over_a1"],
                "R_J_over_a1": 1 - row["S_J_over_a1"],
                "C": c_val,
            }
        )
    return {
        "lambda_sq": lambda_sq,
        "N": n_bound,
        "J": len(rows),
        "dps": MAIN_DPS,
        "packet_dps": D4_PACKET_DPS,
        "quad_order": D4_QUAD_ORDER,
        "a1_raw": a1_raw,
        "packet": {
            "raw_norm_g04": packet["raw_norm_g04"],
            "pN_norm_g04": packet["pN_norm_g04"],
            "coeff_max_abs_diff_vs_half_q": packet["coeff_max_abs_diff_vs_half_q"],
        },
        "peak": {
            "j": peak["j"],
            "gamma": peak["gamma"],
            "abs_K": peak["abs_K"],
            "expected_4pi_lambda_sq": expected,
            "relative_error_vs_expected": peak_rel_error,
            "within_8pct_registered_pass": peak_rel_error <= mp.mpf("0.08"),
        },
        "ledger_C_fit": c_table,
        "k_edge": packet["k_edge"],
        "k_edge_abs": packet["k_edge_abs"],
        "elapsed_s": time.time() - started,
    }


def fit_slope_xy(xs: Sequence[mp.mpf], ys: Sequence[mp.mpf]) -> Optional[mp.mpf]:
    if len(xs) < 2:
        return None
    xm = sum(xs) / len(xs)
    ym = sum(ys) / len(ys)
    cov = sum((x - xm) * (y - ym) for x, y in zip(xs, ys))
    var = sum((x - xm) ** 2 for x in xs)
    if var == 0:
        return None
    return cov / var


def D4_crossover(rows_13_120: Sequence[Dict[str, Any]], addendum: Dict[str, Any]) -> Dict[str, Any]:
    mp.mp.dps = MAIN_DPS
    gammas = [row["gamma"] for row in rows_13_120[:D4_J]]
    profiles = {
        "lambda_sq_12_N_120": anchor_profile(12, 120, gammas),
        "lambda_sq_14_N_120": anchor_profile(14, 120, gammas),
        "lambda_sq_13_N_90": anchor_profile(13, 90, gammas),
    }
    peak13_row = max(rows_13_120[:D4_J], key=lambda row: row["abs_K"])
    expected13 = 4 * mp.pi * 13
    profile13 = {
        "lambda_sq": 13,
        "N": 120,
        "peak": {
            "j": peak13_row["j"],
            "gamma": peak13_row["gamma"],
            "abs_K": peak13_row["abs_K"],
            "expected_4pi_lambda_sq": expected13,
            "relative_error_vs_expected": abs(peak13_row["gamma"] - expected13) / expected13,
            "within_8pct_registered_pass": abs(peak13_row["gamma"] - expected13) / expected13 <= mp.mpf("0.08"),
        },
        "k_edge_abs": mp.mpf(str(addendum.get("A3_edge", {}).get("k_edge_abs", "nan"))),
    }
    profiles["lambda_sq_13_N_120_source_v2"] = profile13
    peak12_pass = profiles["lambda_sq_12_N_120"]["peak"]["within_8pct_registered_pass"]
    peak14_pass = profiles["lambda_sq_14_N_120"]["peak"]["within_8pct_registered_pass"]
    peak90 = profiles["lambda_sq_13_N_90"]["peak"]["gamma"]
    n_control_physical = abs(peak90 - mp.mpf("167")) <= mp.mpf("10")
    n_control_nyquist = abs(peak90 - mp.mpf("125")) <= mp.mpf("10")

    slope_rows = []
    saved_scalars = {}
    for lam_sq in (12, 13, 14):
        scalar_path = OUT_DIR / f"lambda_sq_{lam_sq}_N_120.json"
        if scalar_path.exists():
            saved = load_json(scalar_path)
            E = mp.e ** (-4 * mp.pi * lam_sq)
            saved_scalars[str(lam_sq)] = {
                "source": scalar_path.name,
                "E": E,
                "mu1_over_E": saved.get("mu1_over_E"),
                "Delta_over_E": saved.get("Delta_over_E"),
            }
        else:
            E = mp.e ** (-4 * mp.pi * lam_sq)
        if lam_sq == 12:
            k_edge_abs = profiles["lambda_sq_12_N_120"]["k_edge_abs"]
        elif lam_sq == 13:
            k_edge_abs = profile13["k_edge_abs"]
        else:
            k_edge_abs = profiles["lambda_sq_14_N_120"]["k_edge_abs"]
        slope_rows.append(
            {
                "lambda_sq": lam_sq,
                "lambda": mp.sqrt(lam_sq),
                "E": E,
                "k_edge_abs": k_edge_abs,
                "k_edge_sq_over_E": k_edge_abs**2 / E,
                "log_lambda": mp.log(mp.sqrt(lam_sq)),
                "log_k_edge_sq_over_E": mp.log(k_edge_abs**2 / E),
            }
        )
    slope = fit_slope_xy(
        [row["log_lambda"] for row in slope_rows],
        [row["log_k_edge_sq_over_E"] for row in slope_rows],
    )
    slope_pass = slope is not None and mp.mpf("7") <= slope <= mp.mpf("11")
    if n_control_nyquist:
        code = "CROSSOVER_IS_NYQUIST"
    elif peak12_pass and peak14_pass and n_control_physical and slope_pass:
        code = "CROSSOVER_LAW_CONFIRMED"
    else:
        code = "CROSSOVER_LAW_REFUTED"
    return {
        "profiles": profiles,
        "registered_peak_12_pass": peak12_pass,
        "registered_peak_14_pass": peak14_pass,
        "N_control_peak_13_90": peak90,
        "N_control_physical_pass": n_control_physical,
        "N_control_nyquist_signature": n_control_nyquist,
        "slope_rows": slope_rows,
        "slope_log_k_edge_sq_over_E_vs_log_lambda": slope,
        "slope_registered_9_pm2_pass": slope_pass,
        "saved_scalar_sources": saved_scalars,
        "code": code,
    }


def D5_tail(d1: Dict[str, Any], d2: Dict[str, Any]) -> Dict[str, Any]:
    if d1["code"] != "DUST_ADDITIVE_CONFIRMED" or not d2["pass"]:
        return {
            "status": "NOT_RUN",
            "reason": "D5 objective says run only if D1-D2 pass; literal D1/D2 gate did not pass",
            "S_2000_over_a1": None,
            "tail_code": None,
        }
    return {
        "status": "NOT_RUN_IMPLEMENTATION_GUARD",
        "reason": "D1-D2 passed unexpectedly; J=2000 tail extension is guarded to avoid silent heavy run without review",
        "S_2000_over_a1": None,
        "tail_code": "BOOKKEEPING_HOLE",
    }


def load_history() -> List[str]:
    if not ROUTE_STATE.exists():
        return []
    old = ROUTE_STATE.read_text(encoding="utf-8")
    if "## History" not in old:
        return []
    return [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]


def compute() -> Dict[str, Any]:
    started = time.time()
    profile = load_json(PROFILE_JSON)
    addendum = load_json(ADDENDUM_JSON) if ADDENDUM_JSON.exists() else {}
    phase_ledger = load_json(PHASE_LEDGER_JSON) if PHASE_LEDGER_JSON.exists() else {}
    rows = normalize_rows(profile["rows"])
    progress("D1-D3 from dumped zero_sum_profile_v2 rows")
    d1 = D1_additivity(rows)
    d2 = D2_zoned_judge(rows, d1)
    d3 = D3_early_zone(rows, profile)
    progress("D4 crossover profiles")
    d4 = D4_crossover(rows, addendum)
    d5 = D5_tail(d1, d2)
    codes = [d1["code"], d4["code"]]
    if d5.get("tail_code"):
        codes.append(d5["tail_code"])
    payload = {
        "gate": "DustModelAndCrossover_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "point": {"lambda_sq": LAMBDA_SQ, "N": N},
        "diagnostic_only": True,
        "not_RH": True,
        "phase2_run": False,
        "qW_formula_changed": False,
        "packet_definition_changed": False,
        "q3_main_touched": False,
        "source_profile_json": "out/zero_sum_profile_v2.json",
        "source_addendum_json": "out/zero_sum_profile_v2_addendum.json",
        "source_phase_ledger_json": "out/phase_trace_and_ledger_filter_v1.json",
        "status": codes[0],
        "codes": codes,
        "previous_phase_ledger_codes": phase_ledger.get("codes", []),
        "D1_additivity": d1,
        "D2_zoned_judge": d2,
        "D3_early_zone_relabel": d3,
        "D4_crossover_law": d4,
        "D5_tail": d5,
        "elapsed_s": time.time() - started,
    }
    return payload


def write_report(payload: Dict[str, Any]) -> None:
    d1 = payload["D1_additivity"]
    d2 = payload["D2_zoned_judge"]
    d3 = payload["D3_early_zone_relabel"]
    d4 = payload["D4_crossover_law"]
    d5 = payload["D5_tail"]
    lines = [
        "# DustModelAndCrossover_v1",
        "",
        "## Headlines",
        "",
        f"1. Dust additive floor confirmed? {'YES' if d1['code'] == 'DUST_ADDITIVE_CONFIRMED' else 'NO'}",
        f"2. Zoned judge passes? {'YES' if d2['pass'] else 'NO'}",
        f"3. Early-zone first-zero relabel passes? {'YES' if d3['first_zero_share_ZC_pass'] else 'NO'}",
        f"4. Crossover law status: `{d4['code']}`",
        f"5. D5/J=2000: `{d5['status']}`",
        f"6. Verdict code: {', '.join(f'`{code}`' for code in payload['codes'])}",
        "",
        "Diagnostic only: not RH, no Phase 2, no QW formula changes, no packet-definition changes, no Q3 mainline changes.",
        "",
        "## D1 Additivity",
        "",
        f"- registered dust floor `d={fmt(d1['registered_d'], 12)}`; zero-consistent threshold `10d={fmt(d1['zero_consistent_threshold_absK'], 12)}`.",
        f"- raw all-block registered +-50% pass: `{d1['raw_all_blocks_registered_pm50_pass']}`.",
        f"- dust-zone block count `{d1['dust_zone_block_count']}`; dust-zone blocks +-50% pass `{d1['dust_zone_blocks_pm50_pass']}`.",
        f"- block median |Im K| vs block median |K| Spearman `{fmt(d1['block_median_absIm_vs_block_median_absK_spearman'], 12)}`.",
        f"- code: `{d1['code']}`.",
        "",
        "| gamma block | count | median |Im K| | median |K| | +-50% d pass | physical crossover? |",
        "| --- | ---: | ---: | ---: | --- | --- |",
    ]
    for row in d1["dyadic_blocks"]:
        lines.append(
            f"| [{fmt(row['gamma_range'][0], 8)}, {fmt(row['gamma_range'][1], 8)}) | {row['count']} | "
            f"`{fmt(row['median_abs_Im_K'], 12)}` | `{fmt(row['median_abs_K'], 12)}` | "
            f"`{row['registered_pm50_pass']}` | `{row['physical_crossover_in_block']}` |"
        )
    lines.extend(
        [
            "",
            "## D2 Zoned Judge",
            "",
            f"- judged subset: `|K_j| >= 10d`, count `{d2['judged_point_count']}`.",
            f"- realness circular MAD `{fmt(d2['realness_on_absK_ge_10d']['circular_MAD'], 12)}`.",
            f"- realness median `|Im/Re|` after phase fit `{fmt(d2['realness_on_absK_ge_10d']['median_im_over_re_corrected'], 12)}`.",
            f"- realness registered pass `{d2['realness_registered_pass']}`.",
            f"- j<=100 ZERO_CONSISTENT fraction `{fmt(d2['j_le_100_zero_consistent_fraction'], 12)}` ({d2['j_le_100_zero_consistent_count']}/{d2['j_le_100_total']}); registered pass `{d2['zero_consistent_fraction_registered_pass']}`.",
            f"- code: `{d2['code']}`.",
            "",
            "## D3 Early-Zone Relabel",
            "",
            f"- j<=30 max `|K|={fmt(d3['max_abs_K_j_le_30'], 12)}`; median `|K|={fmt(d3['median_abs_K_j_le_30'], 12)}`.",
            f"- first-zero share `{fmt(d3['first_zero_share_original'], 12)}` relabeled `{d3['first_zero_share_relabel']}`; pass `{d3['first_zero_share_ZC_pass']}`.",
            "",
            "| j | gamma | |K_j| upper bound |",
            "| ---: | ---: | ---: |",
        ]
    )
    for row in d3["selected_upper_bounds"]:
        lines.append(f"| {row['j']} | `{fmt(row['gamma'], 12)}` | `{fmt(row['abs_K'], 12)}` |")
    lines.extend(
        [
            "",
            "## D4 Crossover Law",
            "",
            f"- code: `{d4['code']}`.",
            f"- peak(12,120) pass `{d4['registered_peak_12_pass']}`; peak(14,120) pass `{d4['registered_peak_14_pass']}`.",
            f"- N-control peak(13,90) `{fmt(d4['N_control_peak_13_90'], 12)}`; physical pass `{d4['N_control_physical_pass']}`; nyquist signature `{d4['N_control_nyquist_signature']}`.",
            f"- slope log(k_edge^2/E) vs log(lambda) `{fmt(d4['slope_log_k_edge_sq_over_E_vs_log_lambda'], 12)}`; registered 9+-2 pass `{d4['slope_registered_9_pm2_pass']}`.",
            "",
            "| anchor | peak gamma | expected 4pi lambda_sq | rel err | k_edge | C(J=200) |",
            "| --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for key in ("lambda_sq_12_N_120", "lambda_sq_13_N_120_source_v2", "lambda_sq_14_N_120", "lambda_sq_13_N_90"):
        prof = d4["profiles"][key]
        peak = prof["peak"]
        c200 = "UNKNOWN"
        if "ledger_C_fit" in prof:
            c200_val = prof["ledger_C_fit"][-1]["C"]
            c200 = "NEGATIVE_RESIDUAL" if c200_val is None else fmt(c200_val, 12)
        rel = peak.get("relative_error_vs_expected")
        lines.append(
            f"| `{key}` | `{fmt(peak['gamma'], 12)}` | `{fmt(peak['expected_4pi_lambda_sq'], 12)}` | "
            f"`{fmt(rel, 8)}` | `{fmt(prof.get('k_edge_abs'), 12)}` | `{c200}` |"
        )
    for key in ("lambda_sq_12_N_120", "lambda_sq_14_N_120"):
        prof = d4["profiles"][key]
        c200 = prof["ledger_C_fit"][-1]
        lines.append(
            f"- `{key}` ledger C(J=200): `{'NEGATIVE_RESIDUAL' if c200['C'] is None else fmt(c200['C'], 12)}`; "
            f"`R_J/a1={fmt(c200['R_J_over_a1'], 12)}`."
        )
    lines.extend(
        [
            "",
            "## D5 Tail",
            "",
            f"- status: `{d5['status']}`.",
            f"- reason: {d5['reason']}.",
            "",
            "## State Policy",
            "",
            "- Do not promote DISPLACED_PROFILE from this gate unless D1/D2 and D5 pass.",
            "- The previous edge+ledger far-tail evidence remains diagnostic support, not RH closure.",
        ]
    )
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "DUST_MODEL_AND_CROSSOVER_V1_COMPLETE",
            "last_verdict": payload["status"],
            "last_codes": payload["codes"],
            "last_report": "dust_model_and_crossover_v1.md",
            "last_json": "out/dust_model_and_crossover_v1.json",
            "dust_model_D1_code": payload["D1_additivity"]["code"],
            "dust_model_D2_code": payload["D2_zoned_judge"]["code"],
            "dust_model_D2_zero_consistent_fraction_j100": payload["D2_zoned_judge"]["j_le_100_zero_consistent_fraction"],
            "dust_model_D3_first_zero_share_ZC_pass": payload["D3_early_zone_relabel"]["first_zero_share_ZC_pass"],
            "dust_model_D4_code": payload["D4_crossover_law"]["code"],
            "dust_model_D5_status": payload["D5_tail"]["status"],
            "phase2_run": False,
            "qW_formula_changed": False,
            "packet_definition_changed": False,
            "q3_main_touched": False,
            "next_gate": "STOP_AFTER_DUST_MODEL_AND_CROSSOVER_V1",
            "updated_at_unix": time.time(),
        }
    )
    write_json(LOOP_STATE, state)


def update_route_state(payload: Dict[str, Any]) -> None:
    history = load_history()
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    d1 = payload["D1_additivity"]
    d2 = payload["D2_zoned_judge"]
    d4 = payload["D4_crossover_law"]
    d5 = payload["D5_tail"]
    history.append(
        f"- {now}: DustModelAndCrossover_v1 -> {', '.join(payload['codes'])}; "
        f"D1={d1['code']}; D2={d2['code']} zc_frac={fmt(d2['j_le_100_zero_consistent_fraction'], 6)}; "
        f"D4={d4['code']}; D5={d5['status']}."
    )
    lines = [
        "# ROUTE_B_STATE",
        "",
        "## DOOR",
        "",
        f"`DustModelAndCrossover_v1: {', '.join(payload['codes'])}`",
        "",
        "## PEN-CLOSED / LOCAL DIAGNOSTIC SUPPORT",
        "",
        "- alpha-Gate Equivalence (a-bound assumed; RH-EQUIVALENT GATE)",
        "- RayleighLadderTracking",
        "- PoissonParityLadder (Hermite exact / PSWF with measured defect)",
        "- MidWindowMassBound absorbed by RayleighLadderTracking",
        "- AlphaDetector",
        "- ZEO_v2",
        "- E5/Z1-Z3 pen bookkeeping opened by zero-sum calibration (K7: no RH inference)",
        "- E5 far-tail diagnostic support: edge+ledger remains stable near C~8e-29 with contrast ~1.2 from the previous gate",
        "",
        "## OPEN",
        "",
        "- G3: RayleighExcessBound `alpha <= poly(lambda)*E`, not raw eta",
        "- G3a: reduced to TraceCompressionBound; not closed",
        "- E5 near half: HumpMassBound/window error around heights <=2c remains open",
        "- E5 dust model: literal raw all-block additive floor is not promoted unless D1 passes",
        "- E5 profile: DISPLACED_PROFILE not promoted by this gate because D5 was not run/passed",
        "- G4': CONDITIONAL(RH-regime) theorem candidate; UNCONDITIONAL detector component using `mu3-mu1`",
        "- alpha-Gate: RH core; only measure and monitor `W_prime`",
        "- finite-N to continuum double limit remains explicit",
        "",
        "## DUST MODEL AND CROSSOVER V1",
        "",
        f"- D1 `{d1['code']}`: raw all-block +-50% pass `{d1['raw_all_blocks_registered_pm50_pass']}`; dust-zone pass `{d1['dust_zone_blocks_pm50_pass']}`.",
        f"- D2 `{d2['code']}`: realness pass `{d2['realness_registered_pass']}`; j<=100 ZERO_CONSISTENT fraction `{fmt(d2['j_le_100_zero_consistent_fraction'], 8)}`.",
        f"- D3 first-zero share ZC pass `{payload['D3_early_zone_relabel']['first_zero_share_ZC_pass']}`.",
        f"- D4 `{d4['code']}`: peak12 pass `{d4['registered_peak_12_pass']}`, peak14 pass `{d4['registered_peak_14_pass']}`, N90 physical `{d4['N_control_physical_pass']}`, slope pass `{d4['slope_registered_9_pm2_pass']}`.",
        f"- D5 `{d5['status']}`: {d5['reason']}.",
        "",
        "## NEXT STEP",
        "",
        "STOP: handoff DustModelAndCrossover_v1; ask reviewer whether D1 should be literal all-block raw medians or dust-zone-only.",
        "",
        "## CURRENT_CODES",
        "",
        ", ".join(f"`{code}`" for code in payload["codes"]),
        "",
        "## History",
        "",
        *history,
    ]
    ROUTE_STATE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    d1 = payload["D1_additivity"]
    d2 = payload["D2_zoned_judge"]
    d3 = payload["D3_early_zone_relabel"]
    d4 = payload["D4_crossover_law"]
    d5 = payload["D5_tail"]
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "DustModelAndCrossover_v1 / Route B / Route Z E5",
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. No Phase 2. No QW formula changes. No packet-definition changes. Q3 mainline not touched.",
        "",
        "Codes:",
        ", ".join(payload["codes"]),
        "",
        "D1 additivity:",
        f"- registered d = {fmt(d1['registered_d'], 12)}; threshold 10d = {fmt(d1['zero_consistent_threshold_absK'], 12)}",
        f"- raw all-block +-50% pass = {d1['raw_all_blocks_registered_pm50_pass']} -> code {d1['code']}",
        f"- dust-zone blocks +-50% pass = {d1['dust_zone_blocks_pm50_pass']}",
        "- important: early dust-zone blocks match d, but literal all-block raw medians are contaminated by the physical hump block.",
        "",
        "D2 zoned judge:",
        f"- |K|>=10d count = {d2['judged_point_count']}",
        f"- circ-MAD = {fmt(d2['realness_on_absK_ge_10d']['circular_MAD'], 12)}",
        f"- median |Im/Re| after phase fit = {fmt(d2['realness_on_absK_ge_10d']['median_im_over_re_corrected'], 12)}",
        f"- j<=100 ZERO_CONSISTENT fraction = {fmt(d2['j_le_100_zero_consistent_fraction'], 12)} ({d2['j_le_100_zero_consistent_count']}/{d2['j_le_100_total']})",
        f"- code = {d2['code']}",
        "",
        "D3 early zone:",
        f"- max |K| j<=30 = {fmt(d3['max_abs_K_j_le_30'], 12)}",
        f"- first-zero share = {fmt(d3['first_zero_share_original'], 12)} relabeled <=3.5e-6 (ZC), pass={d3['first_zero_share_ZC_pass']}",
        "",
        "D4 crossover:",
        f"- code = {d4['code']}",
        f"- peak(12,120) = {fmt(d4['profiles']['lambda_sq_12_N_120']['peak']['gamma'], 12)} vs 150.8 registered",
        f"- peak(14,120) = {fmt(d4['profiles']['lambda_sq_14_N_120']['peak']['gamma'], 12)} vs 175.9 registered",
        f"- peak(13,90) = {fmt(d4['N_control_peak_13_90'], 12)}; physical={d4['N_control_physical_pass']}; nyquist={d4['N_control_nyquist_signature']}",
        f"- slope log(k_edge^2/E) vs log(lambda) = {fmt(d4['slope_log_k_edge_sq_over_E_vs_log_lambda'], 12)}; pass={d4['slope_registered_9_pm2_pass']}",
        f"- C(12,J=200) = {'NEGATIVE_RESIDUAL' if d4['profiles']['lambda_sq_12_N_120']['ledger_C_fit'][-1]['C'] is None else fmt(d4['profiles']['lambda_sq_12_N_120']['ledger_C_fit'][-1]['C'], 12)}, R/a1={fmt(d4['profiles']['lambda_sq_12_N_120']['ledger_C_fit'][-1]['R_J_over_a1'], 12)}",
        f"- C(14,J=200) = {'NEGATIVE_RESIDUAL' if d4['profiles']['lambda_sq_14_N_120']['ledger_C_fit'][-1]['C'] is None else fmt(d4['profiles']['lambda_sq_14_N_120']['ledger_C_fit'][-1]['C'], 12)}, R/a1={fmt(d4['profiles']['lambda_sq_14_N_120']['ledger_C_fit'][-1]['R_J_over_a1'], 12)}",
        "",
        "D5:",
        f"- {d5['status']}: {d5['reason']}",
        "",
        "State:",
        "ROUTE_B_STATE.md keeps edge+ledger far-tail support, keeps HumpMassBound/window-error open, and does not promote DISPLACED_PROFILE.",
        "",
        "Reviewer question:",
        "Should D1 be interpreted literally as all dyadic raw medians, or should the physical crossover block be excluded and the dust-zone pass used for the additive-floor model?",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    payload = compute()
    write_json(JSON_OUT, payload)
    write_report(payload)
    update_loop_state(payload)
    update_route_state(payload)
    write_handoff(payload)
    print(payload["status"])
    print("codes=" + ",".join(payload["codes"]))
    print("D2=" + payload["D2_zoned_judge"]["code"])
    print("D4=" + payload["D4_crossover_law"]["code"])
    print("D5=" + payload["D5_tail"]["status"])


if __name__ == "__main__":
    main()
