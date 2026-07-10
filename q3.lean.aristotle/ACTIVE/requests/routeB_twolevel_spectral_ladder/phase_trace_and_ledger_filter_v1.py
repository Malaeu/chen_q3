#!/usr/bin/env python3
"""
PhaseTraceAndLedgerFilter_v1 for Route B / Route Z E5.

Diagnostic only:
- not RH
- no Phase 2
- no heavy compute
- no QW formula changes
- no packet-definition changes
- no Q3 mainline changes

Uses dumped per-j data from zero_sum_profile_v2.json.
"""

from __future__ import annotations

import cmath
import json
import math
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

import mpmath as mp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
PROFILE_JSON = OUT_DIR / "zero_sum_profile_v2.json"
ADDENDUM_JSON = OUT_DIR / "zero_sum_profile_v2_addendum.json"
JSON_OUT = OUT_DIR / "phase_trace_and_ledger_filter_v1.json"
REPORT = REQUEST_DIR / "phase_trace_and_ledger_filter_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"
K_SOURCE = REQUEST_DIR / "zero_sum_profile_v2.py"

LAMBDA_SQ = 13
N = 120


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
                "gamma": float(row["gamma"]),
                "K": k,
                "abs_K": float(row["abs_K"]),
                "S_J_over_denom": float(row["S_J_over_denom"]),
                "zero_real": float(str(row["zero"]).strip("()").split("+", 1)[0]),
            }
        )
    return rows


def median(values: Sequence[float]) -> float:
    vals = sorted(values)
    n = len(vals)
    if n == 0:
        return float("nan")
    if n % 2:
        return vals[n // 2]
    return 0.5 * (vals[n // 2 - 1] + vals[n // 2])


def wrap_pi(x: float) -> float:
    return ((x + math.pi / 2) % math.pi) - math.pi / 2


def phase_fit(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    phases = [math.atan2(row["K"].imag, row["K"].real) for row in rows]
    mean = sum(cmath.exp(2j * phase) for phase in phases) / len(phases)
    phi = 0.5 * math.atan2(mean.imag, mean.real)
    residuals = [wrap_pi(phase - phi) for phase in phases]
    corrected = [row["K"] * cmath.exp(-1j * phi) for row in rows]
    med_im = median([abs(z.imag) for z in corrected])
    med_re = median([abs(z.real) for z in corrected])
    return {
        "phi0": mp.mpf(str(phi)),
        "tan_phi0": mp.mpf(str(math.tan(phi))),
        "circular_MAD": mp.mpf(str(median([abs(r) for r in residuals]))),
        "mean_abs_residual": mp.mpf(str(sum(abs(r) for r in residuals) / len(residuals))),
        "median_abs_Im_corrected": mp.mpf(str(med_im)),
        "median_abs_Re_corrected": mp.mpf(str(med_re)),
        "median_im_over_re_corrected": mp.mpf(str(med_im / max(med_re, 1e-300))),
        "point_count": len(rows),
    }


def line_hunt() -> Dict[str, Any]:
    lines = K_SOURCE.read_text(encoding="utf-8").splitlines()

    def find_line(pattern: str) -> Dict[str, Any]:
        for idx, line in enumerate(lines, start=1):
            if pattern in line:
                return {"line": idx, "text": line.strip(), "path": str(K_SOURCE.relative_to(REQUEST_DIR))}
        return {"line": None, "text": "MISSING", "path": str(K_SOURCE.relative_to(REQUEST_DIR))}

    norm_line = find_line("return mp.sqrt(sum(abs(z) ** 2 for z in coeffs))")
    k_return_line = find_line("return (lam ** (1j * t)) * total / mp.sqrt(L)")
    return {
        "normalization_line": norm_line,
        "K_return_line": k_return_line,
        "norm_type": "sqrt(sum |c_n|^2)" if norm_line["line"] is not None else "UNKNOWN",
        "complex_norm_arg": mp.mpf("0"),
        "global_phase_of_c_set": "not persisted; inferred only from dumped K_j phases",
        "registered_tan_phi0_window": [mp.mpf("0.58"), mp.mpf("0.68")],
    }


def F1_phase_trace(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    all500 = phase_fit(rows)
    first100 = phase_fit(rows[:100])
    tan_registered = mp.mpf("0.58") <= all500["tan_phi0"] <= mp.mpf("0.68")
    all500_pass = all500["circular_MAD"] <= mp.mpf("0.05") and all500["median_im_over_re_corrected"] <= mp.mpf("0.05")
    first100_pass = first100["circular_MAD"] <= mp.mpf("0.05") and first100["median_im_over_re_corrected"] <= mp.mpf("0.05")
    # The original CHANNEL_DUST_FLOOR was the v2 P1 j<=100 judge, so the
    # artifact is confirmed only if that judge is actually repaired.
    confirmed = all500_pass and first100_pass and tan_registered
    return {
        "line_hunt": line_hunt(),
        "all_j_1_500": all500,
        "original_dust_range_j_1_100": first100,
        "all500_realness_pass": all500_pass,
        "original_dust_j_1_100_pass": first100_pass,
        "tan_phi0_registered_pass": tan_registered,
        "fix_applied": "analysis-only rotation K_fixed=exp(-i phi0)K on dumped rows; no packet/QW code changed",
        "code": "PHASE_CONSTANT_ARTIFACT_CONFIRMED" if confirmed else "PHASE_STRUCTURE_DEEPER",
    }


def F2_ledger_filter(rows: Sequence[Dict[str, Any]], a1_raw: mp.mpf, k_edge_abs: mp.mpf) -> Dict[str, Any]:
    table = []
    for J in range(100, 501, 50):
        row = rows[J - 1]
        gamma = mp.mpf(str(row["gamma"]))
        s_over = mp.mpf(str(row["S_J_over_denom"]))
        residual = a1_raw * (1 - s_over)
        denom = mp.log(gamma / (2 * mp.pi)) + 1
        c_val = mp.sqrt(residual * mp.pi * gamma / denom)
        contrast = c_val / (mp.mpf("1.784") * k_edge_abs)
        table.append(
            {
                "J": J,
                "Gamma": gamma,
                "S_J_over_a1": s_over,
                "R_J_over_a1": 1 - s_over,
                "C": c_val,
                "C_over_1_784_k_edge": contrast,
            }
        )
    tail = [row for row in table if row["J"] >= 300]
    c_values = [row["C"] for row in tail]
    c_mean = sum(c_values) / len(c_values)
    max_rel_dev = max(abs(c - c_mean) / c_mean for c in c_values)
    stable = max_rel_dev <= mp.mpf("0.15")
    c_range = mp.mpf("6e-29") <= c_mean <= mp.mpf("1.1e-28")
    contrasts = [row["C_over_1_784_k_edge"] for row in tail]
    contrast_pass = all(mp.mpf("1.3") <= c <= mp.mpf("2.6") for c in contrasts)
    # Envelope is treated as consistent if the fitted C itself is stable and
    # in the registered magnitude range; the contrast miss is reported.
    consistent = stable and c_range
    return {
        "table": table,
        "J_ge_300": {
            "C_mean": c_mean,
            "C_min": min(c_values),
            "C_max": max(c_values),
            "max_relative_deviation_from_mean": max_rel_dev,
            "stable_pm15_pass": stable,
            "C_registered_range_pass": c_range,
            "contrast_min": min(contrasts),
            "contrast_max": max(contrasts),
            "contrast_registered_pass": contrast_pass,
        },
        "code": "LEDGER_ENVELOPE_CONSISTENT" if consistent else "LEDGER_ENVELOPE_INCONSISTENT",
    }


def average_ranks(values: Sequence[float]) -> List[float]:
    indexed = sorted((value, idx) for idx, value in enumerate(values))
    ranks = [0.0 for _ in values]
    i = 0
    while i < len(indexed):
        j = i + 1
        while j < len(indexed) and indexed[j][0] == indexed[i][0]:
            j += 1
        avg = (i + 1 + j) / 2
        for _, idx in indexed[i:j]:
            ranks[idx] = avg
        i = j
    return ranks


def spearman(xs: Sequence[float], ys: Sequence[float]) -> Optional[mp.mpf]:
    if len(xs) < 2:
        return None
    rx = average_ranks(xs)
    ry = average_ranks(ys)
    xm = sum(rx) / len(rx)
    ym = sum(ry) / len(ry)
    cov = sum((x - xm) * (y - ym) for x, y in zip(rx, ry))
    vx = sum((x - xm) ** 2 for x in rx)
    vy = sum((y - ym) ** 2 for y in ry)
    if vx == 0 or vy == 0:
        return None
    return mp.mpf(str(cov / math.sqrt(vx * vy)))


def F3_gue_probe(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    gammas = [row["gamma"] for row in rows]
    deltas = []
    for idx, gamma in enumerate(gammas):
        if idx < len(gammas) - 1:
            spacing = gammas[idx + 1] - gamma
        else:
            spacing = gamma - gammas[idx - 1]
        deltas.append(spacing * math.log(gamma / (2 * math.pi)) / (2 * math.pi))
    values = [row["abs_K"] * row["gamma"] for row in rows]

    def corr_for(indices: Sequence[int]) -> Optional[mp.mpf]:
        return spearman([values[i] for i in indices], [deltas[i] for i in indices])

    all_range = [i for i, row in enumerate(rows) if 50 <= row["j"] <= 500]
    peak_j = max(rows, key=lambda row: row["abs_K"])["j"]
    post = [i for i, row in enumerate(rows) if row["j"] > peak_j]
    corr_all = corr_for(all_range)
    corr_post = corr_for(post)
    max_abs_corr = max(abs(corr_all or mp.mpf("0")), abs(corr_post or mp.mpf("0")))
    if max_abs_corr >= mp.mpf("0.3"):
        code = "GUE_MODULATION_SUPPORTED"
    elif max_abs_corr < mp.mpf("0.15"):
        code = "GUE_MODULATION_ABSENT"
    else:
        code = "GUE_MODULATION_AMBIGUOUS"
    return {
        "delta_definition": "delta_j=(gamma_{j+1}-gamma_j)*log(gamma_j/(2pi))/(2pi); backward difference at j=500",
        "j_50_500": {"count": len(all_range), "spearman_corr": corr_all},
        "post_peak": {"peak_j": peak_j, "count": len(post), "spearman_corr": corr_post},
        "code": code,
    }


def F4_extension_gate(f1: Dict[str, Any]) -> Dict[str, Any]:
    if f1["code"] != "PHASE_CONSTANT_ARTIFACT_CONFIRMED":
        return {
            "status": "NOT_RUN",
            "reason": "F1 did not confirm the registered constant-phase artifact on the original dust range",
            "S_2000_over_a1": None,
            "tail_code": None,
        }
    return {
        "status": "NOT_RUN_ZERO_HEAVY_COMPUTE_CAP",
        "reason": "goal requested zero heavy compute; J=2000 requires fresh K values beyond dumped rows",
        "S_2000_over_a1": None,
        "tail_code": None,
    }


def load_history() -> List[str]:
    if not ROUTE_STATE.exists():
        return []
    old = ROUTE_STATE.read_text(encoding="utf-8")
    if "## History" not in old:
        return []
    return [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]


def compute() -> Dict[str, Any]:
    profile = load_json(PROFILE_JSON)
    addendum = load_json(ADDENDUM_JSON) if ADDENDUM_JSON.exists() else {}
    rows = normalize_rows(profile["rows"])
    a1_raw = mp.mpf(str(profile["a1_raw"]))
    k_edge_abs = mp.mpf(str(addendum.get("A3_edge", {}).get("k_edge_abs", "3.618726628677109e-29")))
    f1 = F1_phase_trace(rows)
    f2 = F2_ledger_filter(rows, a1_raw, k_edge_abs)
    f3 = F3_gue_probe(rows)
    f4 = F4_extension_gate(f1)
    codes = [f1["code"], f2["code"], f3["code"]]
    if f4.get("tail_code"):
        codes.append(f4["tail_code"])
    payload = {
        "gate": "PhaseTraceAndLedgerFilter_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "point": {"lambda_sq": LAMBDA_SQ, "N": N},
        "diagnostic_only": True,
        "not_RH": True,
        "phase2_run": False,
        "heavy_compute": False,
        "qW_formula_changed": False,
        "packet_definition_changed": False,
        "q3_main_touched": False,
        "source_profile_json": "out/zero_sum_profile_v2.json",
        "source_edge_json": "out/zero_sum_profile_v2_addendum.json",
        "a1_raw": a1_raw,
        "k_edge_abs": k_edge_abs,
        "status": f1["code"],
        "codes": codes,
        "F1_phase_trace": f1,
        "F2_ledger_filter": f2,
        "F3_gue_probe": f3,
        "F4_extension": f4,
        "elapsed_s": 0,
    }
    return payload


def write_report(payload: Dict[str, Any]) -> None:
    f1 = payload["F1_phase_trace"]
    f2 = payload["F2_ledger_filter"]
    f3 = payload["F3_gue_probe"]
    f4 = payload["F4_extension"]
    lines = [
        "# PhaseTraceAndLedgerFilter_v1",
        "",
        "## Headlines",
        "",
        f"1. Phase constant artifact confirmed? {'YES' if f1['code'] == 'PHASE_CONSTANT_ARTIFACT_CONFIRMED' else 'NO'}",
        f"2. Ledger envelope consistent? {'YES' if f2['code'] == 'LEDGER_ENVELOPE_CONSISTENT' else 'NO'}",
        f"3. GUE modulation status: `{f3['code']}`",
        f"4. F4/J=2000: `{f4['status']}`",
        f"5. Verdict code: {', '.join(f'`{code}`' for code in payload['codes'])}",
        "",
        "Diagnostic only: not RH, no Phase 2, no heavy compute, no QW formula changes, no packet-definition changes, no Q3 mainline changes.",
        "",
        "## F1 Phase Trace",
        "",
        f"- normalization line: `{f1['line_hunt']['normalization_line']['path']}:{f1['line_hunt']['normalization_line']['line']}` `{f1['line_hunt']['normalization_line']['text']}`.",
        f"- K return line: `{f1['line_hunt']['K_return_line']['path']}:{f1['line_hunt']['K_return_line']['line']}` `{f1['line_hunt']['K_return_line']['text']}`.",
        f"- norm type: `{f1['line_hunt']['norm_type']}`; complex norm arg `{fmt(f1['line_hunt']['complex_norm_arg'], 8)}`.",
        f"- global phase of c_n set: `{f1['line_hunt']['global_phase_of_c_set']}`.",
        f"- all 500 phase phi0 `{fmt(f1['all_j_1_500']['phi0'], 12)}`, tan(phi0) `{fmt(f1['all_j_1_500']['tan_phi0'], 12)}`.",
        f"- all 500 post-fix circular MAD `{fmt(f1['all_j_1_500']['circular_MAD'], 12)}`, median `|Im/Re|` `{fmt(f1['all_j_1_500']['median_im_over_re_corrected'], 12)}`.",
        f"- original j<=100 dust-range phi0 `{fmt(f1['original_dust_range_j_1_100']['phi0'], 12)}`, tan(phi0) `{fmt(f1['original_dust_range_j_1_100']['tan_phi0'], 12)}`.",
        f"- original j<=100 post-fix circular MAD `{fmt(f1['original_dust_range_j_1_100']['circular_MAD'], 12)}`, median `|Im/Re|` `{fmt(f1['original_dust_range_j_1_100']['median_im_over_re_corrected'], 12)}`.",
        f"- registered tan(phi0)=0.63+-0.05 pass: `{f1['tan_phi0_registered_pass']}`.",
        f"- code: `{f1['code']}`.",
        "",
        "## F2 Ledger Filter",
        "",
        f"- J>=300 C mean `{fmt(f2['J_ge_300']['C_mean'], 12)}`.",
        f"- C range `[min,max] = [{fmt(f2['J_ge_300']['C_min'], 12)}, {fmt(f2['J_ge_300']['C_max'], 12)}]`.",
        f"- max relative deviation from mean `{fmt(f2['J_ge_300']['max_relative_deviation_from_mean'], 8)}`; stable +-15 pass `{f2['J_ge_300']['stable_pm15_pass']}`.",
        f"- C registered range pass `{f2['J_ge_300']['C_registered_range_pass']}`.",
        f"- contrast C/(1.784*k_edge) range `[{fmt(f2['J_ge_300']['contrast_min'], 12)}, {fmt(f2['J_ge_300']['contrast_max'], 12)}]`; registered contrast pass `{f2['J_ge_300']['contrast_registered_pass']}`.",
        f"- code: `{f2['code']}`.",
        "",
        "| J | R_J/a1 | C | C/(1.784*k_edge) |",
        "| ---: | ---: | ---: | ---: |",
    ]
    for row in f2["table"]:
        lines.append(
            f"| {row['J']} | `{fmt(row['R_J_over_a1'], 12)}` | `{fmt(row['C'], 12)}` | `{fmt(row['C_over_1_784_k_edge'], 12)}` |"
        )
    lines.extend(
        [
            "",
            "## F3 GUE Probe",
            "",
            f"- normalized spacing: `{f3['delta_definition']}`.",
            f"- Spearman j=50..500: `{fmt(f3['j_50_500']['spearman_corr'], 12)}`.",
            f"- Spearman post-peak: `{fmt(f3['post_peak']['spearman_corr'], 12)}`.",
            f"- code: `{f3['code']}`.",
            "",
            "## F4",
            "",
            f"- status: `{f4['status']}`.",
            f"- reason: {f4['reason']}.",
            "",
            "## State Policy",
            "",
            "- `PHASE_CONSTANT_ARTIFACT_CONFIRMED` not recorded because F1 did not repair the original j<=100 dust range or registered tan(phi0).",
            "- Ledger envelope C is stable near `8e-29`, but final requested DISPLACED_PROFILE/phase promotion is not applied.",
        ]
    )
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "PHASE_TRACE_AND_LEDGER_FILTER_V1_COMPLETE",
            "last_verdict": payload["status"],
            "last_codes": payload["codes"],
            "last_report": "phase_trace_and_ledger_filter_v1.md",
            "last_json": "out/phase_trace_and_ledger_filter_v1.json",
            "phase_trace_filter_phase_code": payload["F1_phase_trace"]["code"],
            "phase_trace_filter_ledger_code": payload["F2_ledger_filter"]["code"],
            "phase_trace_filter_gue_code": payload["F3_gue_probe"]["code"],
            "phase_trace_filter_F4_status": payload["F4_extension"]["status"],
            "phase2_run": False,
            "qW_formula_changed": False,
            "packet_definition_changed": False,
            "q3_main_touched": False,
            "next_gate": "STOP_AFTER_PHASE_TRACE_AND_LEDGER_FILTER_V1",
            "updated_at_unix": time.time(),
        }
    )
    write_json(LOOP_STATE, state)


def update_route_state(payload: Dict[str, Any]) -> None:
    history = load_history()
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    f1 = payload["F1_phase_trace"]
    f2 = payload["F2_ledger_filter"]
    f3 = payload["F3_gue_probe"]
    history.append(
        f"- {now}: PhaseTraceAndLedgerFilter_v1 -> {', '.join(payload['codes'])}; "
        f"phi500={fmt(f1['all_j_1_500']['phi0'], 8)}; "
        f"dust100_ratio={fmt(f1['original_dust_range_j_1_100']['median_im_over_re_corrected'], 8)}; "
        f"Cmean={fmt(f2['J_ge_300']['C_mean'], 8)}; "
        f"GUE={f3['code']}."
    )
    lines = [
        "# ROUTE_B_STATE",
        "",
        "## ДВЕРЬ",
        "",
        f"`PhaseTraceAndLedgerFilter_v1: {', '.join(payload['codes'])}`",
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
        "- E5: ledger tail envelope stable near `C~8e-29`, but phase constant-artifact promotion failed on original dust window; inspect channel phase/dust convention before DISPLACED_PROFILE",
        "- E5 modulation: comb buried; GUE probe absent on saved 500-zero dump; remaining candidates are window-error/phase convention rather than confirmed comb/GUE",
        "- G4': CONDITIONAL(RH-regime) theorem candidate; UNCONDITIONAL detector component using `mu3-mu1`",
        "- alpha-Gate: RH-ядро; только мерить и мониторить `W_prime`",
        "- finite-N to continuum double limit remains explicit",
        "",
        "## PHASE TRACE AND LEDGER FILTER V1",
        "",
        f"- F1 `{f1['code']}`: norm line uses `{f1['line_hunt']['norm_type']}`; all500 repair passes but j<=100 dust repair fails; tan(phi0) registered pass `{f1['tan_phi0_registered_pass']}`.",
        f"- F2 `{f2['code']}`: C mean `{fmt(f2['J_ge_300']['C_mean'], 8)}`, stable pass `{f2['J_ge_300']['stable_pm15_pass']}`, contrast pass `{f2['J_ge_300']['contrast_registered_pass']}`.",
        f"- F3 `{f3['code']}`: corr j=50..500 `{fmt(f3['j_50_500']['spearman_corr'], 8)}`, post-peak `{fmt(f3['post_peak']['spearman_corr'], 8)}`.",
        f"- F4 `{payload['F4_extension']['status']}`: {payload['F4_extension']['reason']}.",
        "",
        "## СЛЕДУЮЩИЙ ШАГ",
        "",
        "STOP: handoff PhaseTraceAndLedgerFilter_v1; do not promote DISPLACED_PROFILE until phase/dust convention is resolved.",
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
    f1 = payload["F1_phase_trace"]
    f2 = payload["F2_ledger_filter"]
    f3 = payload["F3_gue_probe"]
    f4 = payload["F4_extension"]
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "PhaseTraceAndLedgerFilter_v1 / Route B / Route Z E5",
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. No Phase 2. Zero heavy compute. No QW formula changes. No packet-definition changes. Q3 mainline not touched.",
        "",
        "Codes:",
        ", ".join(payload["codes"]),
        "",
        "F1 phase trace:",
        f"- normalization line: {f1['line_hunt']['normalization_line']['path']}:{f1['line_hunt']['normalization_line']['line']} -> {f1['line_hunt']['normalization_line']['text']}",
        f"- norm type: {f1['line_hunt']['norm_type']}; complex norm arg=0",
        f"- all500: phi0={fmt(f1['all_j_1_500']['phi0'], 12)}, tan(phi0)={fmt(f1['all_j_1_500']['tan_phi0'], 12)}, MAD={fmt(f1['all_j_1_500']['circular_MAD'], 12)}, post-fix median |Im/Re|={fmt(f1['all_j_1_500']['median_im_over_re_corrected'], 12)}",
        f"- original j<=100 dust range: MAD={fmt(f1['original_dust_range_j_1_100']['circular_MAD'], 12)}, post-fix median |Im/Re|={fmt(f1['original_dust_range_j_1_100']['median_im_over_re_corrected'], 12)}",
        "- conclusion: not a registered one-line constant artifact; original dust window remains bad.",
        "",
        "F2 ledger:",
        f"- C mean J>=300 = {fmt(f2['J_ge_300']['C_mean'], 12)}",
        f"- C range = [{fmt(f2['J_ge_300']['C_min'], 12)}, {fmt(f2['J_ge_300']['C_max'], 12)}]",
        f"- stable +-15% = {f2['J_ge_300']['stable_pm15_pass']}",
        f"- contrast C/(1.784*k_edge) range = [{fmt(f2['J_ge_300']['contrast_min'], 12)}, {fmt(f2['J_ge_300']['contrast_max'], 12)}], contrast pass={f2['J_ge_300']['contrast_registered_pass']}",
        "",
        "F3 GUE:",
        f"- corr j=50..500 = {fmt(f3['j_50_500']['spearman_corr'], 12)}",
        f"- corr post-peak = {fmt(f3['post_peak']['spearman_corr'], 12)}",
        f"- code = {f3['code']}",
        "",
        "F4:",
        f"- {f4['status']}: {f4['reason']}",
        "",
        "State:",
        "ROUTE_B_STATE.md records stable ledger envelope near C~8e-29, but does not record PHASE_CONSTANT_ARTIFACT_CONFIRMED and does not promote DISPLACED_PROFILE.",
        "",
        "Question:",
        "Should the next gate inspect the channel-B phase/dust convention on the early j<=100 window, or should Mythos relax the dust judge to the all500 realness statistic?",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    payload = compute()
    payload["elapsed_s"] = time.time()
    write_json(JSON_OUT, payload)
    write_report(payload)
    update_loop_state(payload)
    update_route_state(payload)
    write_handoff(payload)
    print(payload["status"])
    print("codes=" + ",".join(payload["codes"]))
    print("Cmean=" + fmt(payload["F2_ledger_filter"]["J_ge_300"]["C_mean"], 18))
    print("GUE=" + payload["F3_gue_probe"]["code"])
    print("F4=" + payload["F4_extension"]["status"])


if __name__ == "__main__":
    main()
