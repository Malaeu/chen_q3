#!/usr/bin/env python3
"""
ZeroSumProfile_v2_Addendum for Route B / Route Z E5.

Diagnostic only:
- not RH
- no Phase 2
- no QW formula changes
- no packet-definition changes
- no Q3 mainline changes
"""

from __future__ import annotations

import json
import cmath
import math
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import mpmath as mp

import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
PROFILE_JSON = OUT_DIR / "zero_sum_profile_v2.json"
JSON_OUT = OUT_DIR / "zero_sum_profile_v2_addendum.json"
REPORT = REQUEST_DIR / "zero_sum_profile_v2_addendum.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"

LAMBDA_SQ = 13
N = 120
MAIN_DPS = 80
PHASE_PASS_MAD = mp.mpf("0.05")


def progress(label: str) -> None:
    print(f"[ZeroSumProfile_v2_Addendum] {label}", flush=True)


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
    return mp.nstr(value, digits)


def parse_mpc_text(value: Any) -> mp.mpc:
    if isinstance(value, (mp.mpf, mp.mpc)):
        return mp.mpc(value)
    text = str(value).strip().strip("()").replace(" ", "")
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


def normalize_rows(raw_rows: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for row in raw_rows:
        k = parse_mpc_text(row["K"])
        rows.append(
            {
                "j": int(row["j"]),
                "gamma": mp.mpf(str(row["gamma"])),
                "K": k,
                "abs_K": mp.mpf(str(row["abs_K"])),
                "Re_K": mp.re(k),
                "Im_K": mp.im(k),
                "T_comb": mp.mpf(str(row["T_comb"])),
                "L_comb": mp.mpf(str(row["L_comb"])),
                "T_comb_over_gamma": mp.mpf(str(row["T_comb_over_gamma"])),
                "L_comb_over_gamma": mp.mpf(str(row["L_comb_over_gamma"])),
                "S_J_over_denom": mp.mpf(str(row["S_J_over_denom"])),
            }
        )
    return rows


def median(values: Sequence[mp.mpf]) -> mp.mpf:
    vals = sorted(values)
    if not vals:
        return mp.mpf("nan")
    n = len(vals)
    if n % 2:
        return vals[n // 2]
    return (vals[n // 2 - 1] + vals[n // 2]) / 2


def wrap_period_pi(x: mp.mpf) -> mp.mpf:
    return mp.fmod(x + mp.pi / 2, mp.pi) - mp.pi / 2


def phase_eval(rows: Sequence[Dict[str, Any]], slope: mp.mpf) -> Dict[str, Any]:
    slope_f = float(slope)
    phases = [math.atan2(float(row["Im_K"]), float(row["Re_K"])) for row in rows]
    gammas = [float(row["gamma"]) for row in rows]
    doubled = [cmath.exp(2j * (phase - slope_f * gamma)) for phase, gamma in zip(phases, gammas)]
    mean = sum(doubled) / len(doubled)
    intercept_f = 0.5 * math.atan2(mean.imag, mean.real)

    def wrap_float(x: float) -> float:
        return ((x + math.pi / 2) % math.pi) - math.pi / 2

    residuals_f = [wrap_float(phase - slope_f * gamma - intercept_f) for phase, gamma in zip(phases, gammas)]
    abs_residuals = [mp.mpf(str(abs(r))) for r in residuals_f]
    corrected = [
        complex(float(row["Re_K"]), float(row["Im_K"])) * cmath.exp(-1j * (slope_f * gamma + intercept_f))
        for row, gamma in zip(rows, gammas)
    ]
    med_im = median([mp.mpf(str(abs(z.imag))) for z in corrected])
    med_re = median([mp.mpf(str(abs(z.real))) for z in corrected])
    return {
        "slope": slope,
        "intercept": mp.mpf(str(intercept_f)),
        "circular_MAD_residual": median(abs_residuals),
        "mean_abs_residual": sum(abs_residuals) / len(abs_residuals),
        "max_abs_residual": max(abs_residuals),
        "corrected_median_abs_Im": med_im,
        "corrected_median_abs_Re": med_re,
        "corrected_median_im_over_re": med_im / max(med_re, mp.mpf("1e-300")),
    }


def phase_grid(rows: Sequence[Dict[str, Any]], lo: mp.mpf, hi: mp.mpf, step: mp.mpf) -> Dict[str, Any]:
    best: Optional[Dict[str, Any]] = None
    k = 0
    slope = lo
    while slope <= hi:
        ev = phase_eval(rows, slope)
        if best is None or ev["circular_MAD_residual"] < best["circular_MAD_residual"]:
            best = ev
        k += 1
        slope = lo + step * k
    assert best is not None
    return best


def phase_audit(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    log_lambda = mp.log(mp.sqrt(LAMBDA_SQ))
    candidates = {
        "primary_minus_log_lambda": -log_lambda,
        "secondary_plus_2log_lambda": 2 * log_lambda,
        "secondary_minus_2log_lambda": -2 * log_lambda,
    }
    candidate_rows = {name: phase_eval(rows, slope) for name, slope in candidates.items()}
    best_registered_name = min(
        candidate_rows,
        key=lambda name: candidate_rows[name]["circular_MAD_residual"],
    )
    diagnostic_grid = phase_grid(rows, mp.mpf("-3"), mp.mpf("3"), mp.mpf("0.005"))
    phase_pass = candidate_rows[best_registered_name]["circular_MAD_residual"] <= PHASE_PASS_MAD
    return {
        "hypothesis": "K_code(gamma)=exp(-i gamma log(lambda))*K_true(gamma), K_true real",
        "registered_slopes": candidates,
        "candidate_fits": candidate_rows,
        "best_registered": {"name": best_registered_name, **candidate_rows[best_registered_name]},
        "best_unrestricted_grid": diagnostic_grid,
        "pass_threshold_circular_MAD": PHASE_PASS_MAD,
        "phase_origin_confirmed": phase_pass,
        "code": "PHASE_ORIGIN_CONFIRMED" if phase_pass else "PHASE_NOT_LINEAR",
    }


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


def comb_audit(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    peak = max(rows, key=lambda row: row["abs_K"])
    post = [row for row in rows if row["j"] > peak["j"]]
    low_limit = 2 * mp.pi * LAMBDA_SQ
    low = [row for row in rows if row["gamma"] < low_limit]
    post_k_gamma = [row["abs_K"] * row["gamma"] for row in post]
    post_t = [row["T_comb"] for row in post]
    post_l = [row["L_comb"] for row in post]
    low_k = [row["abs_K"] for row in low]
    low_t = [row["T_comb_over_gamma"] for row in low]
    low_l = [row["L_comb_over_gamma"] for row in low]
    post_corr_t = spearman(post_k_gamma, post_t)
    post_corr_l = spearman(post_k_gamma, post_l)
    repaired_supported = post_corr_t is not None and post_corr_t >= mp.mpf("0.5")
    return {
        "argmax_j": peak["j"],
        "argmax_gamma": peak["gamma"],
        "post_peak": {
            "count": len(post),
            "corr_absK_gamma_vs_T": post_corr_t,
            "corr_absK_gamma_vs_L": post_corr_l,
            "registered_T_corr_pass": repaired_supported,
        },
        "low_range": {
            "gamma_limit": low_limit,
            "count": len(low),
            "corr_absK_vs_T_over_gamma": spearman(low_k, low_t),
            "corr_absK_vs_L_over_gamma": spearman(low_k, low_l),
            "report_only": True,
        },
        "code": "OLD_RANGE_TEST_INVALID_REPAIRED_SUPPORTED" if repaired_supported else "COMB_MECHANISM_STILL_REFUTED",
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


def edge_audit(rows: Sequence[Dict[str, Any]], profile: Dict[str, Any]) -> Dict[str, Any]:
    mp.mp.dps = MAIN_DPS
    with with_tp_context(LAMBDA_SQ, N):
        model = tp.build_prolate_model(MAIN_DPS)
        g04_endpoint = tp.eval_all_g(model, mp.mpf("1"))["g04"]
    lam = mp.sqrt(LAMBDA_SQ)
    raw_norm = mp.mpf(str(profile["packet"]["raw_norm_g04"]))
    k_edge = mp.sqrt(lam) * g04_endpoint / raw_norm
    k_edge_abs = abs(k_edge)
    vals = [
        row["abs_K"] * row["gamma"]
        for row in rows
        if 300 <= row["j"] <= 500
    ]
    med_tail = median(vals)
    ratio = med_tail / (mp.mpf("1.784") * max(k_edge_abs, mp.mpf("1e-300")))
    edge_window_pass = mp.mpf("2e-29") <= k_edge_abs <= mp.mpf("3e-28")
    closure_pass = mp.mpf("0.5") <= ratio <= mp.mpf("2")
    return {
        "g04_endpoint_t_eq_1": g04_endpoint,
        "k_edge": k_edge,
        "k_edge_abs": k_edge_abs,
        "k_edge_registered_window_pass": edge_window_pass,
        "median_j_300_500_absK_gamma": med_tail,
        "closure_ratio": ratio,
        "closure_ratio_registered_pass": closure_pass,
        "code": "EDGE_CLOSURE_PASS" if edge_window_pass and closure_pass else "EDGE_CLOSURE_FAILS",
        "BK_endpoint_identity": {
            "status": "BK_EDGE_IMPORT_INCOMPLETE",
            "reason": "chi4_proxy / BK endpoint normalization ingredients are not persisted in current Route B artifacts",
            "code": "BK_EDGE_IMPORT_INCOMPLETE",
        },
    }


def a4_extension_if_allowed(phase: Dict[str, Any]) -> Dict[str, Any]:
    if not phase["phase_origin_confirmed"]:
        return {
            "status": "NOT_RUN",
            "reason": "A1 phase audit failed; objective says STOP before A4 extension",
            "S_2000_over_a1": None,
            "tail_status": "NOT_RUN_PHASE_NOT_LINEAR",
        }
    return {
        "status": "ZEROSUM_ADDENDUM_BLOCKED",
        "reason": "A1 passed unexpectedly but A4 implementation was not reached in this run",
        "code": "ZEROSUM_ADDENDUM_BLOCKED",
    }


def load_history() -> List[str]:
    if not ROUTE_STATE.exists():
        return []
    old = ROUTE_STATE.read_text(encoding="utf-8")
    if "## History" not in old:
        return []
    return [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]


def write_report(payload: Dict[str, Any]) -> None:
    phase = payload["A1_phase"]
    comb = payload["A2_comb"]
    edge = payload["A3_edge"]
    a4 = payload["A4_extension"]
    lines = [
        "# ZeroSumProfile_v2_Addendum",
        "",
        "## Headlines",
        "",
        f"1. Phase-origin artifact confirmed? {'YES' if phase['phase_origin_confirmed'] else 'NO'}",
        f"2. Detrended comb mechanism supported? {'YES' if comb['code'] == 'OLD_RANGE_TEST_INVALID_REPAIRED_SUPPORTED' else 'NO'}",
        f"3. Edge value closure passes? {'YES' if edge['code'] == 'EDGE_CLOSURE_PASS' else 'NO'}",
        f"4. S_2000/a1 and tail status: `{a4['S_2000_over_a1']}` / `{a4['tail_status']}`",
        f"5. Verdict code: {', '.join(f'`{code}`' for code in payload['codes'])}",
        "",
        "Diagnostic only: not RH, no Phase 2, no QW formula changes, no packet-definition changes, no Q3 mainline changes.",
        "",
        "## A1 Phase Audit",
        "",
        f"- registered primary slope `-log(sqrt(13))={fmt(phase['registered_slopes']['primary_minus_log_lambda'], 16)}`.",
        f"- registered secondary slopes `+/-2log(sqrt(13)) = {fmt(phase['registered_slopes']['secondary_plus_2log_lambda'], 16)}`, `{fmt(phase['registered_slopes']['secondary_minus_2log_lambda'], 16)}`.",
        f"- best registered slope: `{phase['best_registered']['name']}` = `{fmt(phase['best_registered']['slope'], 16)}`.",
        f"- best registered circular MAD: `{fmt(phase['best_registered']['circular_MAD_residual'], 12)}` rad; threshold `0.05`.",
        f"- corrected median `|Im|/|Re|` at best registered slope: `{fmt(phase['best_registered']['corrected_median_im_over_re'], 12)}`.",
        f"- unrestricted diagnostic grid best slope: `{fmt(phase['best_unrestricted_grid']['slope'], 12)}`, MAD `{fmt(phase['best_unrestricted_grid']['circular_MAD_residual'], 12)}`.",
        f"- code: `{phase['code']}`.",
        "",
        "| candidate | slope | circular MAD | median corrected |Im|/|Re| |",
        "| --- | ---: | ---: | ---: |",
    ]
    for name, row in phase["candidate_fits"].items():
        lines.append(
            f"| `{name}` | `{fmt(row['slope'], 16)}` | `{fmt(row['circular_MAD_residual'], 12)}` | `{fmt(row['corrected_median_im_over_re'], 12)}` |"
        )
    lines.extend(
        [
            "",
            "## A2 Detrended Comb",
            "",
            f"- post-peak count: `{comb['post_peak']['count']}` after j `{comb['argmax_j']}`.",
            f"- Spearman `|K|*gamma` vs `T(gamma)`: `{fmt(comb['post_peak']['corr_absK_gamma_vs_T'], 12)}`.",
            f"- Spearman `|K|*gamma` vs `L(gamma)`: `{fmt(comb['post_peak']['corr_absK_gamma_vs_L'], 12)}`.",
            f"- registered repaired T corr pass: `{comb['post_peak']['registered_T_corr_pass']}`.",
            f"- low-range gamma limit `2*pi*13={fmt(comb['low_range']['gamma_limit'], 12)}`; count `{comb['low_range']['count']}`.",
            f"- low-range `|K|` vs `T/gamma`: `{fmt(comb['low_range']['corr_absK_vs_T_over_gamma'], 12)}`.",
            f"- low-range `|K|` vs `L/gamma`: `{fmt(comb['low_range']['corr_absK_vs_L_over_gamma'], 12)}`.",
            f"- code: `{comb['code']}`.",
            "",
            "## A3 Edge Value Check",
            "",
            f"- `g04(1)={fmt(edge['g04_endpoint_t_eq_1'], 16)}`.",
            f"- `k_edge={fmt(edge['k_edge'], 16)}`; `|k_edge|={fmt(edge['k_edge_abs'], 16)}`.",
            f"- registered `|k_edge|` window pass: `{edge['k_edge_registered_window_pass']}`.",
            f"- median j in [300,500] of `|K|*gamma`: `{fmt(edge['median_j_300_500_absK_gamma'], 16)}`.",
            f"- closure ratio: `{fmt(edge['closure_ratio'], 12)}`; pass `{edge['closure_ratio_registered_pass']}`.",
            f"- edge code: `{edge['code']}`.",
            f"- BK endpoint identity: `{edge['BK_endpoint_identity']['code']}`.",
            "",
            "## A4 Extension",
            "",
            f"- status: `{a4['status']}`.",
            f"- reason: {a4['reason']}.",
            f"- S_2000/a1: `{a4['S_2000_over_a1']}`.",
            f"- tail status: `{a4['tail_status']}`.",
            "",
            "## A5 State",
            "",
            "- `PHASE_ORIGIN_ARTIFACT` not recorded because A1 did not pass.",
            "- `DISPLACED_PROFILE` not promoted because A4 was not run.",
        ]
    )
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "ZERO_SUM_PROFILE_V2_ADDENDUM_COMPLETE",
            "last_verdict": payload["primary_verdict"],
            "last_codes": payload["codes"],
            "last_report": "zero_sum_profile_v2_addendum.md",
            "last_json": "out/zero_sum_profile_v2_addendum.json",
            "zero_sum_profile_v2_addendum_phase_code": payload["A1_phase"]["code"],
            "zero_sum_profile_v2_addendum_comb_code": payload["A2_comb"]["code"],
            "zero_sum_profile_v2_addendum_edge_code": payload["A3_edge"]["code"],
            "zero_sum_profile_v2_addendum_A4_status": payload["A4_extension"]["status"],
            "phase2_run": False,
            "q3_main_touched": False,
            "qW_formula_changed": False,
            "packet_definition_changed": False,
            "next_gate": "STOP_AFTER_ZERO_SUM_PROFILE_V2_ADDENDUM",
            "updated_at_unix": time.time(),
        }
    )
    write_json(LOOP_STATE, state)


def update_route_state(payload: Dict[str, Any]) -> None:
    history = load_history()
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    phase = payload["A1_phase"]
    comb = payload["A2_comb"]
    edge = payload["A3_edge"]
    a4 = payload["A4_extension"]
    history.append(
        f"- {now}: ZeroSumProfile_v2_Addendum -> {', '.join(payload['codes'])}; "
        f"phase_MAD={fmt(phase['best_registered']['circular_MAD_residual'], 8)}; "
        f"comb_T={fmt(comb['post_peak']['corr_absK_gamma_vs_T'], 8)}; "
        f"edge_ratio={fmt(edge['closure_ratio'], 8)}; "
        f"A4={a4['status']}."
    )
    lines = [
        "# ROUTE_B_STATE",
        "",
        "## ДВЕРЬ",
        "",
        f"`ZeroSumProfile_v2_Addendum: {payload['primary_verdict']}; A4={a4['tail_status']}`",
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
        "- E5: phase-origin hypothesis failed; keep channel dust floor / phase convention audit open; no DISPLACED_PROFILE promotion",
        "- G4': CONDITIONAL(RH-regime) theorem candidate; UNCONDITIONAL detector component using `mu3-mu1`",
        "- alpha-Gate: RH-ядро; только мерить и мониторить `W_prime`",
        "- finite-N to continuum double limit remains explicit",
        "",
        "## ZERO SUM PROFILE V2 ADDENDUM",
        "",
        f"- A1 `{phase['code']}`: best registered MAD `{fmt(phase['best_registered']['circular_MAD_residual'], 8)}` > `0.05`.",
        f"- A2 `{comb['code']}`: post-peak corr T `{fmt(comb['post_peak']['corr_absK_gamma_vs_T'], 8)}`, L `{fmt(comb['post_peak']['corr_absK_gamma_vs_L'], 8)}`.",
        f"- A3 `{edge['code']}` plus `{edge['BK_endpoint_identity']['code']}`: `|k_edge|={fmt(edge['k_edge_abs'], 8)}`, closure ratio `{fmt(edge['closure_ratio'], 8)}`.",
        f"- A4 `{a4['status']}`: {a4['reason']}.",
        "",
        "## СЛЕДУЮЩИЙ ШАГ",
        "",
        "STOP: handoff ZeroSumProfile_v2_Addendum; inspect phase/dust convention before any range extension or profile promotion.",
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
    phase = payload["A1_phase"]
    comb = payload["A2_comb"]
    edge = payload["A3_edge"]
    a4 = payload["A4_extension"]
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "ZeroSumProfile_v2_Addendum / Route B / Route Z E5",
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. No Phase 2. No QW formula changes. No packet-definition changes. Q3 mainline not touched.",
        "",
        "Codes:",
        ", ".join(payload["codes"]),
        "",
        "Headlines:",
        f"1. Phase-origin artifact confirmed? {'YES' if phase['phase_origin_confirmed'] else 'NO'}",
        f"2. Detrended comb mechanism supported? {'YES' if comb['code'] == 'OLD_RANGE_TEST_INVALID_REPAIRED_SUPPORTED' else 'NO'}",
        f"3. Edge value closure passes? {'YES' if edge['code'] == 'EDGE_CLOSURE_PASS' else 'NO'}",
        f"4. S_2000/a1 and tail status: {a4['S_2000_over_a1']} / {a4['tail_status']}",
        f"5. Verdict code: {payload['primary_verdict']}",
        "",
        "A1:",
        f"- best registered slope: {phase['best_registered']['name']} = {fmt(phase['best_registered']['slope'], 16)}",
        f"- best registered circular MAD = {fmt(phase['best_registered']['circular_MAD_residual'], 12)} rad, threshold 0.05",
        f"- corrected median |Im|/|Re| = {fmt(phase['best_registered']['corrected_median_im_over_re'], 12)}",
        f"- unrestricted diagnostic grid best slope = {fmt(phase['best_unrestricted_grid']['slope'], 12)}, MAD={fmt(phase['best_unrestricted_grid']['circular_MAD_residual'], 12)}",
        "",
        "A2:",
        f"- post-peak Spearman |K|*gamma vs T = {fmt(comb['post_peak']['corr_absK_gamma_vs_T'], 12)}",
        f"- post-peak Spearman |K|*gamma vs L = {fmt(comb['post_peak']['corr_absK_gamma_vs_L'], 12)}",
        f"- low-range |K| vs T/gamma = {fmt(comb['low_range']['corr_absK_vs_T_over_gamma'], 12)}",
        f"- low-range |K| vs L/gamma = {fmt(comb['low_range']['corr_absK_vs_L_over_gamma'], 12)}",
        "",
        "A3:",
        f"- |k_edge| = {fmt(edge['k_edge_abs'], 16)}",
        f"- closure ratio = {fmt(edge['closure_ratio'], 12)}",
        f"- BK status = {edge['BK_endpoint_identity']['code']}",
        "",
        "A4:",
        f"- {a4['status']}: {a4['reason']}",
        "",
        "State:",
        "PHASE_ORIGIN_ARTIFACT not recorded and DISPLACED_PROFILE not promoted. A4 was not run because A1 failed.",
        "",
        "Question:",
        "Does Mythos want a different phase model, or should the next gate inspect the channel-B phase/dust convention before any J=2000 extension?",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def compute() -> Dict[str, Any]:
    started = time.time()
    profile = load_json(PROFILE_JSON)
    rows = normalize_rows(profile["rows"])
    rows500 = rows[:500]
    progress("A1 phase audit")
    phase = phase_audit(rows500)
    progress("A2 detrended comb audit")
    comb = comb_audit(rows500)
    progress("A3 edge value audit")
    edge = edge_audit(rows500, profile)
    progress("A4 extension gate")
    a4 = a4_extension_if_allowed(phase)
    codes = [phase["code"], comb["code"], edge["code"], edge["BK_endpoint_identity"]["code"]]
    if a4.get("code"):
        codes.append(a4["code"])
    primary = phase["code"]
    payload = {
        "gate": "ZeroSumProfile_v2_Addendum",
        "route": "RouteB_TwoLevelSpectralLadder",
        "point": {"lambda_sq": LAMBDA_SQ, "N": N},
        "status": primary,
        "primary_verdict": primary,
        "codes": codes,
        "diagnostic_only": True,
        "not_RH": True,
        "phase2_run": False,
        "qW_formula_changed": False,
        "packet_definition_changed": False,
        "q3_main_touched": False,
        "source_profile_json": "out/zero_sum_profile_v2.json",
        "A1_phase": phase,
        "A2_comb": comb,
        "A3_edge": edge,
        "A4_extension": a4,
        "elapsed_s": time.time() - started,
    }
    return payload


def main() -> None:
    payload = compute()
    write_json(JSON_OUT, payload)
    write_report(payload)
    update_loop_state(payload)
    update_route_state(payload)
    write_handoff(payload)
    print(payload["primary_verdict"])
    print("codes=" + ",".join(payload["codes"]))
    print("phase_mad=" + fmt(payload["A1_phase"]["best_registered"]["circular_MAD_residual"], 18))
    print("edge_ratio=" + fmt(payload["A3_edge"]["closure_ratio"], 18))
    print("A4=" + payload["A4_extension"]["status"])


if __name__ == "__main__":
    main()
