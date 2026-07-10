#!/usr/bin/env python3
"""
ZeroSumProfile_v2 for Route B / Route Z E5.

Diagnostic only:
- not RH
- no Phase 2
- no QW formula changes
- one point: (lambda_sq, N) = (13, 120)

Channel B is the primary finite-object zero-side profile. Channel C is only a
secondary continuum E-integral gap check at selected points.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import mpmath as mp

import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "zero_sum_profile_v2.json"
REPORT = REQUEST_DIR / "zero_sum_profile_v2.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"
PREVIOUS_JSON = OUT_DIR / "zero_sum_crosscheck_v1.json"

LAMBDA_SQ = 13
N = 120
MAIN_DPS = 80
ZERO_COUNT = 500
SELFTEST_DPS_LOW = 40
SELFTEST_DPS_HIGH = 80
SELFTEST_T = mp.mpf("1")
QUAD_ORDER = 192

DYADIC_BLOCKS = [
    (mp.mpf("14"), mp.mpf("28")),
    (mp.mpf("28"), mp.mpf("56")),
    (mp.mpf("56"), mp.mpf("112")),
    (mp.mpf("112"), mp.mpf("224")),
    (mp.mpf("224"), mp.mpf("448")),
    (mp.mpf("448"), mp.mpf("896")),
]


IDENTITY_LOCK = {
    "object": "channel B primary: k1_N=sum_{n=-120}^{120} c_n V_n; K_N(gamma)=sum c_n Vhat_n(gamma)",
    "transform": "Vhat_n(gamma)=lambda^{i gamma} L^{-1/2}*(exp(i(2pi n/L-gamma)L)-1)/(i(2pi n/L-gamma))",
    "stable_form": "use expm1(z)/z with z=i(2pi n/L-gamma)L; exact limit L when denominator is small",
    "partial_sum": "S_J=2*sum_{j<=J}|K_N(gamma_j)|^2",
    "denominator": "denom=a1_raw=<T k1_N,k1_N>",
    "expected_full_identity": "S_full/denom=1 for the same finite object and full zero-side identity",
    "boundary_poles": "W02/poles already inside tau/T; do not subtract pole or boundary terms in ZeroSumProfile",
    "channel_C": "continuum E-integral secondary only; N-truncation gap reported separately",
    "zero_input": "mpmath.zetazero(j), K7 calibration only, no RH inference",
}


def progress(label: str) -> None:
    print(f"[ZeroSumProfile_v2] {label}", flush=True)


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
        return "MISSING"
    return mp.nstr(value, digits)


def parse_mpc_text(value: Any) -> mp.mpc:
    if isinstance(value, (mp.mpf, mp.mpc)):
        return mp.mpc(value)
    text = str(value).strip()
    text = text.strip("()").replace(" ", "")
    if text.endswith("j"):
        body = text[:-1]
        split_at = None
        for idx in range(1, len(body)):
            if body[idx] in "+-" and body[idx - 1] not in "eE":
                split_at = idx
        if split_at is None:
            return mp.mpc(0, mp.mpf(body))
        return mp.mpc(mp.mpf(body[:split_at]), mp.mpf(body[split_at:]))
    return mp.mpc(mp.mpf(text), mp.mpf("0"))


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


def target_a1_raw() -> Tuple[mp.mpf, str]:
    packet_truth = OUT_DIR / "packet_truth_pull_v1.json"
    if packet_truth.exists():
        data = load_json(packet_truth)
        return mp.mpf(str(data["T0_T2_main"]["a1_raw"])), "out/packet_truth_pull_v1.json:T0_T2_main.a1_raw"
    prev = PREVIOUS_JSON
    if prev.exists():
        data = load_json(prev)
        return mp.mpf(str(data["a1_raw"])), "out/zero_sum_crosscheck_v1.json:a1_raw"
    raise RuntimeError("a1_raw source missing")


def coeff_norm(coeffs: Sequence[mp.mpc]) -> mp.mpf:
    return mp.sqrt(sum(abs(z) ** 2 for z in coeffs))


def normalize_coeffs(coeffs: Sequence[mp.mpc]) -> Tuple[List[mp.mpc], mp.mpf]:
    nrm = coeff_norm(coeffs)
    if nrm == 0:
        raise RuntimeError("zero coefficient norm")
    return [z / nrm for z in coeffs], nrm


def fixed_packet_coeffs(dps: int, quad_order: int) -> Dict[str, Any]:
    with with_tp_context(LAMBDA_SQ, N):
        mp.mp.dps = dps
        model = tp.build_prolate_model(dps)
        n_values = list(range(-N, N + 1))
        low = tp.integrate_coefficients(model, dps=dps, quad_order=quad_order // 2, n_values=n_values, names=["g04"])
        high = tp.integrate_coefficients(model, dps=dps, quad_order=quad_order, n_values=n_values, names=["g04"])
    diff = max(abs(a - b) for a, b in zip(low.coeffs["g04"], high.coeffs["g04"]))
    coeffs, pN_norm = normalize_coeffs(high.coeffs["g04"])
    return {
        "dps": dps,
        "quad_order": quad_order,
        "compare_quad_order": quad_order // 2,
        "coeff_max_abs_diff_vs_half_q": diff,
        "coeffs_normalized": coeffs,
        "pN_norm_g04": pN_norm,
        "raw_norm_g04": high.raw_norms["g04"],
        "breakpoint_intervals": high.intervals,
    }


def tol_b_packet_coeffs() -> Dict[str, Any]:
    started = time.time()
    run = fixed_packet_coeffs(dps=110, quad_order=192)
    return {
        "source": "fixed g04-only tol_B constructor: dps=110, quad 96/192",
        "dps": 110,
        "quad_order": 192,
        "compare_quad_order": 96,
        "coeff_max_abs_diff_vs_half_q": run["coeff_max_abs_diff_vs_half_q"],
        "coeffs_normalized": [mp.mpc(z) for z in run["coeffs_normalized"]],
        "pN_norm_g04": run["pN_norm_g04"],
        "raw_norm_g04": run["raw_norm_g04"],
        "breakpoint_intervals": run["breakpoint_intervals"],
        "elapsed_s": time.time() - started,
    }


def K_from_coeffs(t: mp.mpf, coeffs: Sequence[mp.mpc]) -> mp.mpc:
    L = mp.log(LAMBDA_SQ)
    lam = mp.sqrt(LAMBDA_SQ)
    total = mp.mpc(0)
    n0 = -N
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


def relative_digits(a: mp.mpc, b: mp.mpc) -> mp.mpf:
    diff = abs(a - b)
    denom = max(abs(a), abs(b), mp.mpf("1e-300"))
    rel = diff / denom
    if rel == 0:
        return mp.inf
    return -mp.log10(rel)


def load_or_run_selftest() -> Dict[str, Any]:
    if PREVIOUS_JSON.exists():
        prev = load_json(PREVIOUS_JSON)
        st = prev.get("Z1_selftest", {})
        if st and mp.mpf(str(st.get("relative_digits", "0"))) >= 25 and st.get("pass") is True:
            return {
                "source": "reused out/zero_sum_crosscheck_v1.json:Z1_selftest",
                "t": mp.mpf(str(st["t"])),
                "dps_low": int(st["dps_low"]),
                "dps_high": int(st["dps_high"]),
                "quad_order": int(st["quad_order"]),
                "K_low": parse_mpc_text(st["K_low"]),
                "K_high": parse_mpc_text(st["K_high"]),
                "abs_diff": mp.mpf(str(st["abs_diff"])),
                "relative_digits": mp.mpf(str(st["relative_digits"])),
                "pass": True,
            }

    progress("self-test: rebuild dps40 coefficients")
    low = fixed_packet_coeffs(SELFTEST_DPS_LOW, QUAD_ORDER)
    mp.mp.dps = SELFTEST_DPS_LOW
    k_low = K_from_coeffs(SELFTEST_T, low["coeffs_normalized"])

    progress("self-test: rebuild dps80 coefficients")
    high = fixed_packet_coeffs(SELFTEST_DPS_HIGH, QUAD_ORDER)
    mp.mp.dps = SELFTEST_DPS_HIGH
    k_high = K_from_coeffs(SELFTEST_T, high["coeffs_normalized"])
    digits = relative_digits(k_low, k_high)
    return {
        "source": "fresh ZeroSumProfile_v2 selftest",
        "t": SELFTEST_T,
        "dps_low": SELFTEST_DPS_LOW,
        "dps_high": SELFTEST_DPS_HIGH,
        "quad_order": QUAD_ORDER,
        "K_low": k_low,
        "K_high": k_high,
        "abs_diff": abs(k_low - k_high),
        "relative_digits": digits,
        "pass": digits >= 25,
    }


def median(values: Sequence[mp.mpf]) -> mp.mpf:
    vals = sorted(values)
    n = len(vals)
    if n == 0:
        return mp.mpf("nan")
    if n % 2:
        return vals[n // 2]
    return (vals[n // 2 - 1] + vals[n // 2]) / 2


def fit_power(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    usable = [row for row in rows if row["abs_K"] > 0]
    if len(usable) < 2:
        return {"status": "INSUFFICIENT_POINTS", "p": None, "slope": None}
    xs = [mp.log(row["gamma"]) for row in usable]
    ys = [mp.log(row["abs_K"]) for row in usable]
    xm = sum(xs) / len(xs)
    ym = sum(ys) / len(ys)
    cov = sum((x - xm) * (y - ym) for x, y in zip(xs, ys))
    var = sum((x - xm) ** 2 for x in xs)
    slope = cov / var
    return {"status": "OK", "slope": slope, "p": -slope, "point_count": len(usable)}


def von_mangoldt(k: int) -> mp.mpf:
    if k <= 1:
        return mp.mpf("0")
    for p in range(2, k + 1):
        if k % p != 0:
            continue
        power = p
        while power < k:
            power *= p
        if power == k:
            return mp.log(p)
    return mp.mpf("0")


def comb_values(gamma: mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
    t_sum = mp.mpc(0)
    l_sum = mp.mpc(0)
    for m in range(1, LAMBDA_SQ + 1):
        term = mp.power(m, mp.mpc("-0.5", gamma))
        t_sum += term
        l_sum += von_mangoldt(m) * term
    return abs(t_sum), abs(l_sum)


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
    return pearson(average_ranks(xs), average_ranks(ys))


def dyadic_block_summary(rows: Sequence[Dict[str, Any]], denom: mp.mpf) -> List[Dict[str, Any]]:
    out = []
    for lo, hi in DYADIC_BLOCKS:
        block_rows = [row for row in rows if lo <= row["gamma"] < hi]
        block_sum = sum((row["term"] for row in block_rows), mp.mpf("0"))
        out.append(
            {
                "gamma_range": [lo, hi],
                "count": len(block_rows),
                "sum_2_absK_sq": block_sum,
                "sum_over_denom": block_sum / denom,
                "max_abs_K": max((row["abs_K"] for row in block_rows), default=mp.mpf("0")),
                "argmax_j": max(block_rows, key=lambda row: row["abs_K"])["j"] if block_rows else None,
            }
        )
    return out


def compute_rows(coeffs: Sequence[mp.mpc], denom: mp.mpf) -> Tuple[List[Dict[str, Any]], Dict[str, Any]]:
    mp.mp.dps = MAIN_DPS
    rows: List[Dict[str, Any]] = []
    partial = mp.mpf("0")
    for j in range(1, ZERO_COUNT + 1):
        zero = mp.zetazero(j)
        gamma = mp.im(zero)
        kval = K_from_coeffs(gamma, coeffs)
        abs_k = abs(kval)
        term = 2 * abs_k**2
        partial += term
        t_comb, l_comb = comb_values(gamma)
        rows.append(
            {
                "j": j,
                "zero": zero,
                "gamma": gamma,
                "K": kval,
                "Re_K": mp.re(kval),
                "Im_K": mp.im(kval),
                "abs_K": abs_k,
                "term": term,
                "S_J": partial,
                "S_J_over_denom": partial / denom,
                "T_comb": t_comb,
                "L_comb": l_comb,
                "T_comb_over_gamma": t_comb / gamma,
                "L_comb_over_gamma": l_comb / gamma,
            }
        )
    summary = {
        "S_J_over_denom": {str(j): rows[j - 1]["S_J_over_denom"] for j in (100, 200, 300, 400, 500)},
        "S_500_over_denom": rows[-1]["S_J_over_denom"],
        "S_500": rows[-1]["S_J"],
        "monotone": all(rows[i]["S_J"] >= rows[i - 1]["S_J"] for i in range(1, len(rows))),
        "max_S_J_over_denom": max(row["S_J_over_denom"] for row in rows),
    }
    return rows, summary


def p1_profile(rows: Sequence[Dict[str, Any]], denom: mp.mpf) -> Dict[str, Any]:
    first100 = list(rows[:100])
    peak = max(first100, key=lambda row: row["abs_K"])
    med_im = median([abs(row["Im_K"]) for row in first100])
    med_re = median([abs(row["Re_K"]) for row in first100])
    ratio = med_im / max(med_re, mp.mpf("1e-300"))
    first_share = first100[0]["term"] / denom
    return {
        "rows_j_le_100": first100,
        "argmax_j": peak["j"],
        "argmax_gamma": peak["gamma"],
        "peak_abs_K": peak["abs_K"],
        "peak_registered_pass": mp.mpf("1e-31") <= peak["abs_K"] <= mp.mpf("1e-30") and mp.mpf("25") <= peak["gamma"] <= mp.mpf("120"),
        "first_zero_share": first_share,
        "first_zero_share_registered": "3.5e-6",
        "median_abs_Im_K": med_im,
        "median_abs_Re_K": med_re,
        "median_im_over_re": ratio,
        "im_dust_pass": ratio <= mp.mpf("0.1"),
        "dyadic_blocks": dyadic_block_summary(first100, denom)[:4],
    }


def p2_classify(rows: Sequence[Dict[str, Any]], p2_summary: Dict[str, Any], blocks: Sequence[Dict[str, Any]]) -> str:
    s500 = p2_summary["S_500_over_denom"]
    if s500 >= mp.mpf("0.85"):
        return "DISPLACED_PROFILE_CONFIRMED"
    if mp.mpf("0.50") <= s500 < mp.mpf("0.85"):
        return "PARTIAL_DISPLACED_PROFILE"
    last_block = blocks[-1]["sum_over_denom"] if blocks else mp.mpf("0")
    prev_block = blocks[-2]["sum_over_denom"] if len(blocks) >= 2 else mp.mpf("0")
    if s500 <= mp.mpf("0.50") and last_block > prev_block:
        return "TAIL_BEYOND_500"
    return "BOOKKEEPING_HOLE_OR_NORMALIZATION_FACTOR_SUSPECT"


def comb_correlation(rows: Sequence[Dict[str, Any]], argmax_j: int) -> Dict[str, Any]:
    def corr_for(subrows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
        abs_k = [row["abs_K"] for row in subrows]
        t_vals = [row["T_comb_over_gamma"] for row in subrows]
        l_vals = [row["L_comb_over_gamma"] for row in subrows]
        return {
            "count": len(subrows),
            "corr_T_over_gamma": spearman(abs_k, t_vals),
            "corr_L_over_gamma": spearman(abs_k, l_vals),
        }

    all_corr = corr_for(rows)
    post = [row for row in rows if row["j"] > argmax_j]
    post_corr = corr_for(post)
    post_t = post_corr["corr_T_over_gamma"]
    post_l = post_corr["corr_L_over_gamma"]
    supported = False
    if post_t is not None and post_t >= mp.mpf("0.6"):
        supported = True
    if post_l is not None and post_l >= mp.mpf("0.6"):
        supported = True
    expected_order = post_t is not None and post_l is not None and post_t > post_l
    return {
        "all_j_1_500": all_corr,
        "post_peak_j_gt_argmax": post_corr,
        "expected_corr_T_gt_corr_L": expected_order,
        "code": "COMB_MECHANISM_SUPPORTED" if supported else "COMB_MECHANISM_REFUTED",
    }


def channel_c_K(t: mp.mpf, pN_norm: mp.mpf) -> mp.mpc:
    with with_tp_context(LAMBDA_SQ, N):
        mp.mp.dps = MAIN_DPS
        model = tp.build_prolate_model(MAIN_DPS)
        intervals = tp.split_intervals()
        nodes, weights = tp.gauss_rule(QUAD_ORDER)
    lam = mp.sqrt(LAMBDA_SQ)
    total = mp.mpc(0)
    for interval in intervals:
        a = interval["a"]
        b = interval["b"]
        mmax = int(interval["mmax"])
        center = (a + b) / 2
        half = (b - a) / 2
        for node, weight in zip(nodes, weights):
            x = center + half * node
            w = half * weight
            exp_x = mp.e**x
            u = exp_x / lam
            s = mp.mpf("0")
            for m in range(1, mmax + 1):
                s += tp.eval_all_g(model, mp.mpf(m) * exp_x / LAMBDA_SQ)["g04"]
            e_val = mp.sqrt(u) * s / pN_norm
            total += w * e_val * mp.e ** (-1j * t * mp.log(u))
    return total


def channel_c_gap(rows: Sequence[Dict[str, Any]], pN_norm: mp.mpf) -> List[Dict[str, Any]]:
    first = rows[0]
    peak = max(rows[:100], key=lambda row: row["abs_K"])
    selected: Dict[int, Dict[str, Any]] = {first["j"]: first, peak["j"]: peak}
    out = []
    for row in selected.values():
        progress(f"channel C continuum gap at j={row['j']}")
        k_c = channel_c_K(row["gamma"], pN_norm)
        gap = abs(k_c - row["K"])
        out.append(
            {
                "j": row["j"],
                "gamma": row["gamma"],
                "K_B": row["K"],
                "K_C": k_c,
                "abs_gap": gap,
                "relative_gap_vs_K_B": gap / max(row["abs_K"], mp.mpf("1e-300")),
            }
        )
    return out


def compute() -> Dict[str, Any]:
    started = time.time()
    a1_raw, a1_source = target_a1_raw()

    if not IDENTITY_LOCK:
        return {"gate": "ZeroSumProfile_v2", "status": "ZERO_SIDE_IDENTITY_UNSPECIFIED"}

    progress("P0 identity lock accepted")
    selftest = load_or_run_selftest()
    if not selftest["pass"]:
        return {
            "gate": "ZeroSumProfile_v2",
            "status": "TRANSFORM_SELFTEST_FAILS",
            "identity_lock": IDENTITY_LOCK,
            "Z1_selftest": selftest,
        }

    progress("rebuild tol_B channel B coefficients")
    packet = tol_b_packet_coeffs()
    mp.mp.dps = MAIN_DPS

    progress("P1/P2 compute 500 zero profile")
    rows, p2_summary = compute_rows(packet["coeffs_normalized"], a1_raw)
    blocks = dyadic_block_summary(rows, a1_raw)
    p1 = p1_profile(rows, a1_raw)
    p2_code = p2_classify(rows, p2_summary, blocks)
    p2_summary.update(
        {
            "dyadic_blocks": blocks,
            "code": p2_code,
            "strictly_rising_past_0_40": p2_summary["S_J_over_denom"]["500"] > p2_summary["S_J_over_denom"]["400"],
        }
    )

    progress("P3 comb correlations")
    p3 = comb_correlation(rows, int(p1["argmax_j"]))

    progress("P4 post-peak profile fit")
    post_rows = [row for row in rows if row["j"] >= int(p1["argmax_j"])]
    p4 = fit_power(post_rows)
    p4["fit_label"] = "FIT_NOT_LAW"
    p4["registered_pass"] = p4["p"] is not None and mp.mpf("1.7") <= p4["p"] <= mp.mpf("2.5")
    p4["code"] = None if p4["registered_pass"] else "PROFILE_FIT_OUT_OF_RANGE"

    progress("channel C secondary truncation-gap check")
    c_gap = channel_c_gap(rows, packet["pN_norm_g04"])

    codes = [p2_code, p3["code"]]
    if not p1["im_dust_pass"]:
        codes.insert(0, "CHANNEL_DUST_FLOOR")
    if p4["code"]:
        codes.append(p4["code"])
    primary_status = codes[0]

    payload = {
        "gate": "ZeroSumProfile_v2",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": primary_status,
        "codes": codes,
        "lambda_sq": LAMBDA_SQ,
        "N": N,
        "main_dps": MAIN_DPS,
        "zero_count": ZERO_COUNT,
        "not_RH": True,
        "phase2_run": False,
        "q3_main_touched": False,
        "qW_formula_changed": False,
        "identity_lock": IDENTITY_LOCK,
        "a1_raw": a1_raw,
        "a1_raw_source": a1_source,
        "packet": {
            "source": packet["source"],
            "dps": packet["dps"],
            "quad_order": packet["quad_order"],
            "compare_quad_order": packet["compare_quad_order"],
            "coeff_max_abs_diff_vs_half_q": packet["coeff_max_abs_diff_vs_half_q"],
            "pN_norm_g04": packet["pN_norm_g04"],
            "raw_norm_g04": packet["raw_norm_g04"],
            "elapsed_s": packet["elapsed_s"],
            "coefficients_persisted": False,
            "coefficients_note": "c_n arrays are reconstructed deterministically because prior JSONs did not persist them",
        },
        "Z1_selftest": selftest,
        "P1": p1,
        "P2": p2_summary,
        "P3": p3,
        "P4": p4,
        "channel_C_secondary": {
            "description": "continuum E-integral gap; not the denominator identity channel",
            "gap_rows": c_gap,
        },
        "rows": rows,
        "state_update_policy": {
            "if_p2_confirmed_or_partial": "replace SLOW_TAIL by DISPLACED_PROFILE and keep E5=StripTailZeroSumBound",
            "if_tail_beyond_500": "record DISPLACED_PROFILE_INCOMPLETE_RANGE; extend range required",
            "if_normalization_suspect": "do not overwrite state with DISPLACED_PROFILE",
        },
        "elapsed_s": time.time() - started,
    }
    return payload


def selected_rows(rows: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    wanted = {1, 2, 5, 10, 20, 50, 100, 200, 300, 400, 500}
    return [row for row in rows if row["j"] in wanted]


def write_report(payload: Dict[str, Any]) -> None:
    if payload["status"] in {"ZERO_SIDE_IDENTITY_UNSPECIFIED", "TRANSFORM_SELFTEST_FAILS"}:
        REPORT.write_text(json.dumps(json_safe(payload), indent=2) + "\n", encoding="utf-8")
        return

    p1 = payload["P1"]
    p2 = payload["P2"]
    p3 = payload["P3"]
    p4 = payload["P4"]
    rows = payload["rows"]
    lines = [
        "# ZeroSumProfile_v2",
        "",
        "## Verdict",
        "",
        ", ".join(f"`{code}`" for code in payload["codes"]),
        "",
        "Diagnostic only: not RH, no Phase 2, no QW formula changes.",
        "",
        "## P0 Identity Lock",
        "",
        "- Object: channel B primary `k1_N=sum c_n V_n`; `K_N(gamma)=sum c_n Vhat_n(gamma)`.",
        "- Transform: `Vhat_n(gamma)=lambda^{i gamma} L^{-1/2} * (exp(i(2pi n/L-gamma)L)-1)/(i(2pi n/L-gamma))`.",
        "- Stable form: `expm1(z)/z`, exact limit `L` when denominator is small.",
        "- Partial sum: `S_J=2*sum_{j<=J}|K_N(gamma_j)|^2`.",
        f"- Denominator: `a1_raw=<T k1_N,k1_N>={fmt(payload['a1_raw'], 18)}` from `{payload['a1_raw_source']}`.",
        "- Boundary/poles: already inside `tau/T`; no pole or boundary subtraction here.",
        "- Channel C: secondary continuum E-integral gap only.",
        "- Zero input: `mpmath.zetazero(j)`; K7 calibration only; no RH inference.",
        "",
        "## P1 Profile j<=100",
        "",
        f"- argmax j: `{p1['argmax_j']}`, gamma `{fmt(p1['argmax_gamma'], 14)}`.",
        f"- peak `|K|={fmt(p1['peak_abs_K'], 12)}`; registered peak window pass `{p1['peak_registered_pass']}`.",
        f"- first-zero share `2|K(g1)|^2/a1={fmt(p1['first_zero_share'], 12)}`; registered `3.5e-6`.",
        f"- median `|Im K|={fmt(p1['median_abs_Im_K'], 12)}`.",
        f"- median `|Re K|={fmt(p1['median_abs_Re_K'], 12)}`.",
        f"- median `|Im|/|Re|={fmt(p1['median_im_over_re'], 12)}`; dust pass `{p1['im_dust_pass']}`.",
        "",
        "| gamma block | count | block sum / denom | max |K| | argmax j |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for block in p1["dyadic_blocks"]:
        lo, hi = block["gamma_range"]
        lines.append(
            f"| `[{fmt(lo, 5)},{fmt(hi, 5)})` | {block['count']} | `{fmt(block['sum_over_denom'], 12)}` | `{fmt(block['max_abs_K'], 12)}` | {block['argmax_j']} |"
        )
    lines.extend(
        [
            "",
            "## P2 Extended Profile",
            "",
            "| J | S_J/denom |",
            "| ---: | ---: |",
        ]
    )
    for j in (100, 200, 300, 400, 500):
        lines.append(f"| {j} | `{fmt(p2['S_J_over_denom'][str(j)], 12)}` |")
    lines.extend(
        [
            "",
            "| gamma block | count | block sum / denom | max |K| | argmax j |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for block in p2["dyadic_blocks"]:
        lo, hi = block["gamma_range"]
        lines.append(
            f"| `[{fmt(lo, 5)},{fmt(hi, 5)})` | {block['count']} | `{fmt(block['sum_over_denom'], 12)}` | `{fmt(block['max_abs_K'], 12)}` | {block['argmax_j']} |"
        )
    lines.extend(
        [
            "",
            f"- P2 code: `{p2['code']}`.",
            f"- S_500/denom: `{fmt(p2['S_500_over_denom'], 12)}`.",
            f"- strictly rising 400->500: `{p2['strictly_rising_past_0_40']}`.",
            "",
            "## P3 Comb Correlation",
            "",
            f"- all j corr `|K|` vs `T/gamma`: `{fmt(p3['all_j_1_500']['corr_T_over_gamma'], 12)}`.",
            f"- all j corr `|K|` vs `L/gamma`: `{fmt(p3['all_j_1_500']['corr_L_over_gamma'], 12)}`.",
            f"- post-peak corr `T/gamma`: `{fmt(p3['post_peak_j_gt_argmax']['corr_T_over_gamma'], 12)}`.",
            f"- post-peak corr `L/gamma`: `{fmt(p3['post_peak_j_gt_argmax']['corr_L_over_gamma'], 12)}`.",
            f"- expected `corr(T)>corr(L)`: `{p3['expected_corr_T_gt_corr_L']}`.",
            f"- comb code: `{p3['code']}`.",
            "",
            "## P4 Fit",
            "",
            f"- post-peak fit p: `{fmt(p4['p'], 12)}`.",
            f"- registered `[1.7,2.5]`: `{p4['registered_pass']}`.",
            "- label: `FIT_NOT_LAW`.",
            "",
            "## Channel C Gap",
            "",
            "| j | gamma | |K_B| | |K_C-K_B|/|K_B| |",
            "| ---: | ---: | ---: | ---: |",
        ]
    )
    for row in payload["channel_C_secondary"]["gap_rows"]:
        lines.append(
            f"| {row['j']} | `{fmt(row['gamma'], 14)}` | `{fmt(abs(row['K_B']), 12)}` | `{fmt(row['relative_gap_vs_K_B'], 12)}` |"
        )
    lines.extend(
        [
            "",
            "## Selected Rows",
            "",
            "| J | gamma_J | |K_N(gamma_J)| | S_J/denom |",
            "| ---: | ---: | ---: | ---: |",
        ]
    )
    for row in selected_rows(rows):
        lines.append(
            f"| {row['j']} | `{fmt(row['gamma'], 14)}` | `{fmt(row['abs_K'], 12)}` | `{fmt(row['S_J_over_denom'], 12)}` |"
        )
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def load_history() -> List[str]:
    if not ROUTE_STATE.exists():
        return []
    old = ROUTE_STATE.read_text(encoding="utf-8")
    if "## History" not in old:
        return []
    return [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]


def state_route_line(payload: Dict[str, Any]) -> Tuple[str, List[str], str]:
    p2_code = payload["P2"]["code"]
    p3_code = payload["P3"]["code"]
    p4_code = payload["P4"]["code"]
    codes = payload["codes"]
    if "CHANNEL_DUST_FLOOR" in codes:
        open_line = "- E5: channel dust floor; do not overwrite with DISPLACED_PROFILE until Im/Re structure is explained"
        status_line = f"- ZeroSumProfile_v2: `{p2_code}` numerically, but `CHANNEL_DUST_FLOOR` blocks state promotion."
        next_step = "STOP: inspect channel-B phase/dust convention before profile promotion."
    elif p2_code in {"DISPLACED_PROFILE_CONFIRMED", "PARTIAL_DISPLACED_PROFILE"}:
        open_line = "- E5 = StripTailZeroSumBound; mechanism: truncated-zeta/log-derivative comb + cancellation depth"
        status_line = f"- ZeroSumProfile_v2: replaces `SLOW_TAIL` by `DISPLACED_PROFILE` ({p2_code}); comb `{p3_code}`."
        next_step = "STOP: handoff ZeroSumProfile_v2; next E5 target remains `StripTailZeroSumBound`."
    elif p2_code == "TAIL_BEYOND_500":
        open_line = "- E5: DISPLACED_PROFILE_INCOMPLETE_RANGE; extend zero range required before mechanism verdict"
        status_line = f"- ZeroSumProfile_v2: `{p2_code}`; do not replace `SLOW_TAIL` yet."
        next_step = "STOP: extend range beyond 500 before mechanism verdict."
    else:
        open_line = "- E5: bookkeeping/normalization suspect; do not overwrite with DISPLACED_PROFILE"
        status_line = f"- ZeroSumProfile_v2: `{p2_code}`; state not promoted."
        next_step = "STOP: inspect zero-side identity/normalization before profile promotion."
    if p4_code:
        status_line += f" Fit code `{p4_code}`."
    return open_line, [status_line], next_step


def update_route_state(payload: Dict[str, Any]) -> None:
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    p1 = payload["P1"]
    p2 = payload["P2"]
    p3 = payload["P3"]
    p4 = payload["P4"]
    history = load_history()
    history.append(
        f"- {now}: ZeroSumProfile_v2 -> {', '.join(payload['codes'])}; "
        f"S500/a1={fmt(p2['S_500_over_denom'], 8)}; "
        f"peak_j={p1['argmax_j']}; "
        f"im_ratio={fmt(p1['median_im_over_re'], 8)}; "
        f"post_corr_T={fmt(p3['post_peak_j_gt_argmax']['corr_T_over_gamma'], 8)}; "
        f"p={fmt(p4['p'], 8)}."
    )
    e5_open_line, status_lines, next_step = state_route_line(payload)
    door = (
        "ZeroSumProfile_v2 numbers: "
        f"codes={'+'.join(payload['codes'])}; "
        f"S500/a1={fmt(p2['S_500_over_denom'], 12)}; "
        f"peak_j={p1['argmax_j']}; "
        f"medianIm/Re={fmt(p1['median_im_over_re'], 12)}"
    )
    lines = [
        "# ROUTE_B_STATE",
        "",
        "## ДВЕРЬ",
        "",
        f"`{door}`",
        "",
        "## ДОКАЗАНО ПЕРОМ",
        "",
        "- alpha-Gate Equivalence (a-bound assumed; RH-EQUIVALENT GATE)",
        "- RayleighLadderTracking",
        "- PoissonParityLadder (Hermite exact / PSWF with measured defect)",
        "- MidWindowMassBound absorbed by RayleighLadderTracking",
        "- AlphaDetector",
        "- ZEO_v2",
        "- E5/Z1-Z3 pen bookkeeping opened by zero-sum calibration (K7: no RH inference)",
        "",
        "## ОТКРЫТО",
        "",
        "- G3: RayleighExcessBound `alpha <= poly(lambda)*E`, not raw eta",
        "- G3a: сведён к TraceCompressionBound (безусловная trace-compression bound; не закрыто)",
        e5_open_line,
        "- G4': CONDITIONAL(RH-regime) theorem candidate; UNCONDITIONAL detector component using `mu3-mu1`",
        "- alpha-Gate: RH-ядро; только мерить и мониторить `W_prime`",
        "- finite-N to continuum double limit remains explicit",
        "",
        "## ZERO SUM PROFILE V2",
        "",
        *status_lines,
        f"- P2 S_100/S_200/S_300/S_400/S_500 = `{fmt(p2['S_J_over_denom']['100'], 8)}`, `{fmt(p2['S_J_over_denom']['200'], 8)}`, `{fmt(p2['S_J_over_denom']['300'], 8)}`, `{fmt(p2['S_J_over_denom']['400'], 8)}`, `{fmt(p2['S_J_over_denom']['500'], 8)}`.",
        f"- P1 peak `|K|={fmt(p1['peak_abs_K'], 8)}` at j `{p1['argmax_j']}`, gamma `{fmt(p1['argmax_gamma'], 10)}`.",
        f"- P1 median `|Im|/|Re|={fmt(p1['median_im_over_re'], 8)}`.",
        f"- P3 comb code `{p3['code']}`; post-peak corr T `{fmt(p3['post_peak_j_gt_argmax']['corr_T_over_gamma'], 8)}`, L `{fmt(p3['post_peak_j_gt_argmax']['corr_L_over_gamma'], 8)}`.",
        f"- P4 post-peak p `{fmt(p4['p'], 8)}` (`FIT_NOT_LAW`).",
        "",
        "## SYMBOL DIAGONAL RECLASSIFICATION",
        "",
        "- `SymbolDiagonalCrossCheck_v1`: `SYMBOL_MATCH -> TAUTOLOGICAL_CHANNEL`.",
        "- reason: same `tau` contraction; `rel_diff=2.3763e-91` is the fingerprint.",
        "",
        "## СЛЕДУЮЩИЙ ШАГ",
        "",
        next_step,
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


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "ZERO_SUM_PROFILE_V2_COMPLETE",
            "last_verdict": payload["status"],
            "last_codes": payload["codes"],
            "last_report": "zero_sum_profile_v2.md",
            "last_json": "out/zero_sum_profile_v2.json",
            "zero_sum_profile_v2_status": payload["status"],
            "zero_sum_profile_v2_codes": payload["codes"],
            "zero_sum_profile_v2_S500_over_a1": mp.nstr(payload["P2"]["S_500_over_denom"], 40),
            "zero_sum_profile_v2_peak_j": payload["P1"]["argmax_j"],
            "zero_sum_profile_v2_median_im_over_re": mp.nstr(payload["P1"]["median_im_over_re"], 40),
            "zero_sum_profile_v2_comb_code": payload["P3"]["code"],
            "zero_sum_profile_v2_fit_p": mp.nstr(payload["P4"]["p"], 40),
            "route_status": "NOT_RH_DIAGNOSTIC_ONLY",
            "phase2_run": False,
            "q3_main_touched": False,
            "next_gate": "STOP_AFTER_ZERO_SUM_PROFILE_V2",
            "updated_at_unix": time.time(),
        }
    )
    write_json(LOOP_STATE, state)


def write_handoff(payload: Dict[str, Any]) -> None:
    p1 = payload["P1"]
    p2 = payload["P2"]
    p3 = payload["P3"]
    p4 = payload["P4"]
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "ZeroSumProfile_v2 / Route B / Route Z E5",
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. No Phase 2. No QW formula changes. Q3 mainline not touched.",
        "",
        "Codes:",
        ", ".join(payload["codes"]),
        "",
        "P0 identity:",
        "Channel B primary finite object: k1_N=sum c_n V_n, K_N=sum c_n Vhat_n. S_J=2 sum |K_N(gamma_j)|^2, denom=a1_raw=<T k1_N,k1_N>. W02/poles already inside tau/T; no pole subtraction in this profile. Zeros are K7 calibration only.",
        "",
        "P1:",
        f"- argmax j={p1['argmax_j']}, gamma={fmt(p1['argmax_gamma'], 14)}, peak |K|={fmt(p1['peak_abs_K'], 12)}",
        f"- first-zero share={fmt(p1['first_zero_share'], 12)}",
        f"- median |Im|/|Re|={fmt(p1['median_im_over_re'], 12)} (dust pass={p1['im_dust_pass']})",
        "",
        "P2:",
        f"- S100={fmt(p2['S_J_over_denom']['100'], 12)}",
        f"- S200={fmt(p2['S_J_over_denom']['200'], 12)}",
        f"- S300={fmt(p2['S_J_over_denom']['300'], 12)}",
        f"- S400={fmt(p2['S_J_over_denom']['400'], 12)}",
        f"- S500={fmt(p2['S_J_over_denom']['500'], 12)}",
        f"- P2 code={p2['code']}",
        "",
        "P3:",
        f"- comb code={p3['code']}",
        f"- post-peak corr T/gamma={fmt(p3['post_peak_j_gt_argmax']['corr_T_over_gamma'], 12)}",
        f"- post-peak corr L/gamma={fmt(p3['post_peak_j_gt_argmax']['corr_L_over_gamma'], 12)}",
        f"- corr(T)>corr(L)={p3['expected_corr_T_gt_corr_L']}",
        "",
        "P4:",
        f"- post-peak p={fmt(p4['p'], 12)} FIT_NOT_LAW; registered pass={p4['registered_pass']}",
        "",
        "State:",
        (
            "ROUTE_B_STATE.md does NOT promote to DISPLACED_PROFILE: P2 is PARTIAL_DISPLACED_PROFILE, "
            "but CHANNEL_DUST_FLOOR blocks state promotion until the channel-B phase/dust convention is explained."
            if "CHANNEL_DUST_FLOOR" in payload["codes"]
            else "ROUTE_B_STATE.md updated according to P5."
        ),
        "",
        "Question:",
        "Accept this v2 profile as the profile/mechanism gate for E5, or require range extension before using the comb mechanism in the pen write-up?",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    payload = compute()
    write_json(JSON_OUT, payload)
    write_report(payload)
    if payload["status"] not in {"ZERO_SIDE_IDENTITY_UNSPECIFIED", "TRANSFORM_SELFTEST_FAILS"}:
        update_route_state(payload)
        update_loop_state(payload)
        write_handoff(payload)
    print(payload["status"])
    if "P2" in payload:
        print(f"codes={','.join(payload['codes'])}")
        print(f"S500/a1={fmt(payload['P2']['S_500_over_denom'], 18)}")
        print(f"peak_j={payload['P1']['argmax_j']} peak={fmt(payload['P1']['peak_abs_K'], 18)}")
        print(f"comb={payload['P3']['code']} p={fmt(payload['P4']['p'], 18)}")


if __name__ == "__main__":
    main()
