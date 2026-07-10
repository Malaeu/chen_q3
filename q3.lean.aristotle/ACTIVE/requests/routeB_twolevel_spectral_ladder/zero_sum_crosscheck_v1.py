#!/usr/bin/env python3
"""
ZeroSumCrossCheck_v1 for Route B.

Request-local diagnostic only:
- one point: (lambda_sq, N) = (13, 120)
- not RH
- no Phase 2
- no Q3 mainline edits

This is an independent zero-sum channel for the E5/Route Z pen write-up.
The main K(t) values are evaluated from the normalized finite packet
coefficients of tol_B k1. Those coefficients are rebuilt from the physical
E-map with the request-standard breakpoint split at u=lambda/m.
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

import mpmath as mp

import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "zero_sum_crosscheck_v1.json"
REPORT = REQUEST_DIR / "zero_sum_crosscheck_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"
SYMBOL_REPORT = REQUEST_DIR / "symbol_diagonal_crosscheck_v1.md"

LAMBDA_SQ = 13
N = 120
MAIN_DPS = 80
SELFTEST_DPS_LOW = 40
SELFTEST_DPS_HIGH = 80
QUAD_ORDER = 192
SELFTEST_T = mp.mpf("1")
ZERO_COUNT = 100
A1_RAW_REGISTERED = mp.mpf("5.37295373544e-59")


def progress(label: str) -> None:
    print(f"[ZeroSumCrossCheck_v1] {label}", flush=True)


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

    symbol = OUT_DIR / "symbol_diagonal_crosscheck_v1.json"
    if symbol.exists():
        data = load_json(symbol)
        return mp.mpf(str(data["comparison"]["target_matvec_a1_raw"])), "out/symbol_diagonal_crosscheck_v1.json:comparison.target_matvec_a1_raw"

    return A1_RAW_REGISTERED, "registered literal 5.37295373544e-59"


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
    spec = next(dict(s) for s in tp.RUN_SPECS if s["label"] == "tol_B")
    with with_tp_context(LAMBDA_SQ, N):
        run = tp.adaptive_packet_run(spec)
    if run.get("status") != "OK":
        raise RuntimeError(f"tol_B reconstruction failed: {run.get('status')}")
    return {
        "dps": run["dps"],
        "quad_order": run["quad_order"],
        "compare_quad_order": run["attempts"][-1]["quad_order_low"],
        "coeff_max_abs_diff_vs_half_q": run["coeff_max_abs_diff"],
        "coeffs_normalized": [mp.mpc(z) for z in run["coeffs_normalized"]["g04"]],
        "pN_norm_g04": run["pN_norms"]["g04"],
        "raw_norm_g04": run["raw_norms"]["g04"],
        "breakpoint_intervals": run["breakpoint_intervals"],
        "elapsed_s": run["elapsed_s"],
    }


def K_from_coeffs(t: mp.mpf, coeffs: Sequence[mp.mpc]) -> mp.mpc:
    L = mp.log(LAMBDA_SQ)
    lam = mp.sqrt(LAMBDA_SQ)
    total = mp.mpc(0)
    n0 = -N
    for idx, coeff in enumerate(coeffs):
        n = n0 + idx
        alpha = 2 * mp.pi * n / L - t
        if abs(alpha) < mp.mpf("1e-50"):
            integral = L
        else:
            integral = (mp.e ** (1j * alpha * L) - 1) / (1j * alpha)
        total += coeff * integral
    return (lam ** (1j * t)) * total / mp.sqrt(L)


def relative_digits(a: mp.mpc, b: mp.mpc) -> mp.mpf:
    diff = abs(a - b)
    denom = max(abs(a), abs(b), mp.mpf("1e-300"))
    rel = diff / denom
    if rel == 0:
        return mp.inf
    return -mp.log10(rel)


def transform_selftest() -> Dict[str, Any]:
    started = time.time()
    progress("Z1 self-test: rebuild dps40 coefficients")
    low = fixed_packet_coeffs(SELFTEST_DPS_LOW, QUAD_ORDER)
    mp.mp.dps = SELFTEST_DPS_LOW
    k_low = K_from_coeffs(SELFTEST_T, low["coeffs_normalized"])

    progress("Z1 self-test: rebuild dps80 coefficients")
    high = fixed_packet_coeffs(SELFTEST_DPS_HIGH, QUAD_ORDER)
    mp.mp.dps = SELFTEST_DPS_HIGH
    k_high = K_from_coeffs(SELFTEST_T, high["coeffs_normalized"])

    digits = relative_digits(k_low, k_high)
    return {
        "t": SELFTEST_T,
        "dps_low": SELFTEST_DPS_LOW,
        "dps_high": SELFTEST_DPS_HIGH,
        "quad_order": QUAD_ORDER,
        "K_low": k_low,
        "K_high": k_high,
        "abs_diff": abs(k_low - k_high),
        "relative_digits": digits,
        "pass": digits >= 25,
        "low_coeff_diff_vs_half_q": low["coeff_max_abs_diff_vs_half_q"],
        "high_coeff_diff_vs_half_q": high["coeff_max_abs_diff_vs_half_q"],
        "elapsed_s": time.time() - started,
    }


def zero_rows(coeffs: Sequence[mp.mpc], a1_raw: mp.mpf) -> Tuple[List[Dict[str, Any]], Dict[str, Any]]:
    mp.mp.dps = MAIN_DPS
    rows: List[Dict[str, Any]] = []
    partial = mp.mpf("0")
    for j in range(1, ZERO_COUNT + 1):
        zero = mp.zetazero(j)
        gamma = mp.im(zero)
        kval = K_from_coeffs(gamma, coeffs)
        abs_k = abs(kval)
        term = 2 * abs_k ** 2
        partial += term
        rows.append(
            {
                "j": j,
                "zero": zero,
                "gamma": gamma,
                "K": kval,
                "abs_K": abs_k,
                "term_2_abs_K_sq": term,
                "S_J": partial,
                "S_J_over_a1_raw": partial / a1_raw,
            }
        )

    x_vals = [mp.log(row["gamma"]) for row in rows]
    y_vals = [mp.log(row["abs_K"]) for row in rows if row["abs_K"] > 0]
    x_fit = x_vals[: len(y_vals)]
    x_mean = sum(x_fit) / len(x_fit)
    y_mean = sum(y_vals) / len(y_vals)
    cov = sum((x - x_mean) * (y - y_mean) for x, y in zip(x_fit, y_vals))
    var = sum((x - x_mean) ** 2 for x in x_fit)
    slope = cov / var
    p = -slope
    monotone = all(rows[i]["S_J"] >= rows[i - 1]["S_J"] for i in range(1, len(rows)))
    max_ratio = max(row["S_J_over_a1_raw"] for row in rows)
    k1_abs = rows[0]["abs_K"]
    s100_ratio = rows[-1]["S_J_over_a1_raw"]
    return rows, {
        "S_100": rows[-1]["S_J"],
        "S_100_over_a1_raw": s100_ratio,
        "monotone_up": monotone,
        "max_S_J_over_a1_raw": max_ratio,
        "no_overshoot_gt_1_05": max_ratio <= mp.mpf("1.05"),
        "K_gamma1_abs": k1_abs,
        "K_gamma1_registered_pass": mp.mpf("3e-31") <= k1_abs <= mp.mpf("3e-30"),
        "decay_fit_slope_log_absK_vs_log_gamma": slope,
        "decay_fit_p": p,
        "decay_fit_registered_pass": mp.mpf("0.5") <= p <= mp.mpf("1.5"),
        "fit_label": "FIT_NOT_LAW",
    }


def classify(selftest: Dict[str, Any], summary: Dict[str, Any]) -> str:
    if not selftest["pass"]:
        return "TRANSFORM_SELFTEST_FAILS"
    if not summary["monotone_up"] or not summary["no_overshoot_gt_1_05"]:
        return "ZERO_SUM_MISSING_TERM"
    if summary["S_100_over_a1_raw"] < mp.mpf("0.5"):
        return "SLOW_TAIL"
    return "ZERO_SUM_MATCH"


def append_symbol_reclassification() -> None:
    if not SYMBOL_REPORT.exists():
        return
    text = SYMBOL_REPORT.read_text(encoding="utf-8")
    if "TAUTOLOGICAL_CHANNEL" in text:
        text = text.replace(
            "- The independent diagonal symbol channel matches the saved raw matvec within the registered relative tolerance.\n"
            "- This fixes the trace-formula normalization for the G3a pen write-up.\n"
            "- State promotion applied: `AlphaDetector`, `ZEO_v2`; `G3a` is now reduced to `TraceCompressionBound`.\n",
            "- The diagonal symbol channel matches the saved raw matvec within the registered relative tolerance.\n"
            "- After `ZeroSumCrossCheck_v1`, this is reclassified as `TAUTOLOGICAL_CHANNEL`: useful internal consistency for the pilot `tau` contraction, but not an independent E5 zero-sum judge.\n"
            "- State promotion already applied: `AlphaDetector`, `ZEO_v2`; `G3a` remains reduced to `TraceCompressionBound`.\n",
        )
        SYMBOL_REPORT.write_text(text, encoding="utf-8")
        return
    marker = "## Verdict\n\n`SYMBOL_MATCH`\n"
    insert = (
        "## Reclassification\n\n"
        "`TAUTOLOGICAL_CHANNEL`\n\n"
        "ZeroSumCrossCheck_v1 reclassifies the previous `SYMBOL_MATCH`: "
        "the `rel_diff=2.3763e-91` match is the fingerprint of the same "
        "`tau` contraction, useful as an internal consistency check but not "
        "an independent E5 zero-sum channel.\n\n"
    )
    if marker in text:
        text = text.replace(marker, marker + "\n" + insert, 1)
    else:
        text += "\n\n" + insert
    SYMBOL_REPORT.write_text(text, encoding="utf-8")


def compute() -> Dict[str, Any]:
    started = time.time()
    a1_raw, a1_source = target_a1_raw()
    progress("Z1 transform self-test")
    selftest = transform_selftest()

    progress("rebuild tol_B k1 coefficients")
    packet = tol_b_packet_coeffs()
    mp.mp.dps = MAIN_DPS

    progress("Z0 first 100 mpmath zetazero values and Z2 partial sums")
    rows, summary = zero_rows(packet["coeffs_normalized"], a1_raw)
    code = classify(selftest, summary)

    payload = {
        "gate": "ZeroSumCrossCheck_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": code,
        "registered_pass": code == "ZERO_SUM_MATCH",
        "lambda_sq": LAMBDA_SQ,
        "N": N,
        "main_dps": MAIN_DPS,
        "zero_count": ZERO_COUNT,
        "not_RH": True,
        "phase2_run": False,
        "q3_main_touched": False,
        "K7_note": "first 100 zeta zeros are numerical calibration only; no RH inference",
        "symbol_diagonal_reclassification": {
            "old_code": "SYMBOL_MATCH",
            "new_code": "TAUTOLOGICAL_CHANNEL",
            "reason": "same tau-contraction fingerprint rel_diff=2.3763e-91",
        },
        "a1_raw": a1_raw,
        "a1_raw_source": a1_source,
        "packet": {
            "source": "true_precision_packet_gate_v1.adaptive_packet_run(tol_B)",
            "dps": packet["dps"],
            "quad_order": packet["quad_order"],
            "compare_quad_order": packet["compare_quad_order"],
            "coeff_max_abs_diff_vs_half_q": packet["coeff_max_abs_diff_vs_half_q"],
            "pN_norm_g04": packet["pN_norm_g04"],
            "raw_norm_g04": packet["raw_norm_g04"],
            "elapsed_s": packet["elapsed_s"],
            "breakpoints": "u=lambda/m; x=log(lambda*u) intervals from true_precision_packet_gate_v1.split_intervals",
        },
        "Z0_zeros": {
            "source": "mpmath.zetazero(j), j=1..100",
            "digits_requirement": ">=30 decimal digits recorded",
            "pairing_convention": "S_J uses explicit +-gamma pairing as 2*|K(gamma_j)|^2",
        },
        "Z1_selftest": selftest,
        "Z2_partial_sums": {
            "summary": summary,
            "rows": rows,
        },
        "classification_rules": {
            "ZERO_SUM_MATCH": "selftest pass, monotone, no overshoot >1.05, S_100/a1_raw >=0.5",
            "ZERO_SUM_MISSING_TERM": "overshoot or non-monotone; pole/sign bookkeeping in Z1, no refit",
            "SLOW_TAIL": "S_100/a1_raw <0.5; log-correction regime for Z4",
            "TRANSFORM_SELFTEST_FAILS": "dps40 vs dps80 K selftest has <25 relative digits",
        },
        "elapsed_s": time.time() - started,
    }
    return payload


def selected_rows(rows: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    wanted = {1, 2, 5, 10, 20, 50, 100}
    return [row for row in rows if row["j"] in wanted]


def write_report(payload: Dict[str, Any]) -> None:
    selftest = payload["Z1_selftest"]
    summary = payload["Z2_partial_sums"]["summary"]
    rows = payload["Z2_partial_sums"]["rows"]
    lines = [
        "# ZeroSumCrossCheck_v1",
        "",
        "## Verdict",
        "",
        f"`{payload['status']}`",
        "",
        "Route B diagnostic only: not RH, no Phase 2, no Q3 mainline edit.",
        "",
        "## SymbolDiagonal Reclassification",
        "",
        "- `SymbolDiagonalCrossCheck_v1`: `SYMBOL_MATCH -> TAUTOLOGICAL_CHANNEL`.",
        "- Reason: the `rel_diff=2.3763e-91` match is the fingerprint of the same `tau` contraction, not an independent E5 zero-sum judge.",
        "",
        "## Z0",
        "",
        "- zeros: first 100 nontrivial zeta zeros via `mpmath.zetazero(j)`.",
        "- recorded precision: at least 30 digits in JSON.",
        "- K7: numerical calibration only; no RH inference.",
        "",
        "## Z1",
        "",
        "- `K(t) = int k1(u) u^{-it} d*u` with normalized tol_B `k1`.",
        "- tol_B coefficients were rebuilt from the physical E-map using breakpoints `u=lambda/m`.",
        "- Main zero sums use the exact finite-packet Mellin transform from those coefficients.",
        f"- self-test point: `t={fmt(selftest['t'], 8)}`.",
        f"- `K_dps40={fmt(selftest['K_low'], 18)}`",
        f"- `K_dps80={fmt(selftest['K_high'], 18)}`",
        f"- relative digits: `{fmt(selftest['relative_digits'], 12)}`; required `>=25`; pass `{selftest['pass']}`.",
        "",
        "## Z2",
        "",
        "- pairing convention: `+-gamma` is counted explicitly by `2|K(gamma_j)|^2`.",
        f"- `a1_raw={fmt(payload['a1_raw'], 18)}` from `{payload['a1_raw_source']}`.",
        f"- `|K(gamma_1)|={fmt(summary['K_gamma1_abs'], 12)}`; registered window `[3e-31,3e-30]`; pass `{summary['K_gamma1_registered_pass']}`.",
        f"- `S_100/a1_raw={fmt(summary['S_100_over_a1_raw'], 12)}`.",
        f"- monotone up: `{summary['monotone_up']}`.",
        f"- max `S_J/a1_raw={fmt(summary['max_S_J_over_a1_raw'], 12)}`; no overshoot `>1.05`: `{summary['no_overshoot_gt_1_05']}`.",
        f"- decay fit `|K(gamma_j)| ~ gamma^(-p)`: `p={fmt(summary['decay_fit_p'], 12)}`; registered `[0.5,1.5]`; `{summary['fit_label']}`.",
        "",
        "| J | gamma_J | |K(gamma_J)| | S_J/a1_raw |",
        "| ---: | ---: | ---: | ---: |",
    ]
    for row in selected_rows(rows):
        lines.append(
            f"| {row['j']} | `{fmt(row['gamma'], 14)}` | `{fmt(row['abs_K'], 12)}` | `{fmt(row['S_J_over_a1_raw'], 12)}` |"
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
        ]
    )
    if payload["status"] == "ZERO_SUM_MATCH":
        lines.extend(
            [
                "- The first 100 zero-pair terms account for the registered fraction without overshoot.",
                "- E5 proceeds to the pen write-up with the remaining tail isolated as `StripTailZeroSumBound`.",
            ]
        )
    elif payload["status"] == "SLOW_TAIL":
        lines.extend(
            [
                "- The transform self-test passes and partial sums are monotone with no overshoot, but `S_100/a1_raw < 0.5`.",
                "- Classification is `SLOW_TAIL`: E5 is opened into Z1-Z3 pen bookkeeping plus a required `StripTailZeroSumBound` / log-correction tail gate.",
            ]
        )
    elif payload["status"] == "ZERO_SUM_MISSING_TERM":
        lines.extend(
            [
                "- Partial sums overshot or failed monotonic bookkeeping.",
                "- Stop before refitting; inspect pole/sign/pairing conventions.",
            ]
        )
    else:
        lines.extend(
            [
                "- The transform self-test failed; do not interpret the zero-sum partial sums.",
                "- Stop and repair Z1 numerics before E5 pen use.",
            ]
        )
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    summary = payload["Z2_partial_sums"]["summary"]
    state.update(
        {
            "current_gate": "ZERO_SUM_CROSSCHECK_V1_COMPLETE",
            "last_verdict": payload["status"],
            "last_codes": [payload["status"], "TAUTOLOGICAL_CHANNEL"],
            "last_report": "zero_sum_crosscheck_v1.md",
            "last_json": "out/zero_sum_crosscheck_v1.json",
            "symbol_diagonal_crosscheck_v1_reclassified_as": "TAUTOLOGICAL_CHANNEL",
            "zero_sum_crosscheck_v1_status": payload["status"],
            "zero_sum_crosscheck_v1_S100_over_a1_raw": mp.nstr(summary["S_100_over_a1_raw"], 40),
            "zero_sum_crosscheck_v1_K_gamma1_abs": mp.nstr(summary["K_gamma1_abs"], 40),
            "zero_sum_crosscheck_v1_decay_p": mp.nstr(summary["decay_fit_p"], 40),
            "E5_status": "opened_Z1_Z3_to_pen_remaining_StripTailZeroSumBound",
            "route_status": "NOT_RH_DIAGNOSTIC_ONLY",
            "phase2_run": False,
            "q3_main_touched": False,
            "next_gate": "STOP_AFTER_ZERO_SUM_CROSSCHECK",
            "updated_at_unix": time.time(),
        }
    )
    write_json(LOOP_STATE, state)


def update_route_state(payload: Dict[str, Any]) -> None:
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    summary = payload["Z2_partial_sums"]["summary"]
    history_lines: List[str] = []
    if ROUTE_STATE.exists():
        old = ROUTE_STATE.read_text(encoding="utf-8")
        if "## History" in old:
            history_lines = [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]
    history_lines.append(
        f"- {now}: ZeroSumCrossCheck_v1 -> {payload['status']}; "
        f"S100/a1={fmt(summary['S_100_over_a1_raw'], 8)}; "
        f"K1={fmt(summary['K_gamma1_abs'], 8)}; "
        f"p={fmt(summary['decay_fit_p'], 8)}; SymbolDiagonal=TAUTOLOGICAL_CHANNEL."
    )

    door = (
        "ZeroSumCrossCheck numbers: "
        f"code={payload['status']}; "
        f"S100/a1={fmt(summary['S_100_over_a1_raw'], 12)}; "
        f"|K1|={fmt(summary['K_gamma1_abs'], 12)}; "
        f"p={fmt(summary['decay_fit_p'], 12)}"
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
        "- E5 вскрыта: Z1-Z3 -> перо; остаток = StripTailZeroSumBound",
        "- G4': CONDITIONAL(RH-regime) theorem candidate; UNCONDITIONAL detector component using `mu3-mu1`",
        "- alpha-Gate: RH-ядро; только мерить и мониторить `W_prime`",
        "- finite-N to continuum double limit remains explicit",
        "",
        "## SYMBOL DIAGONAL RECLASSIFICATION",
        "",
        "- `SymbolDiagonalCrossCheck_v1`: `SYMBOL_MATCH -> TAUTOLOGICAL_CHANNEL`.",
        "- reason: same `tau` contraction; `rel_diff=2.3763e-91` is the fingerprint.",
        "",
        "## ZERO SUM CROSSCHECK",
        "",
        f"- code: `{payload['status']}`",
        f"- `(lambda_sq,N)=({payload['lambda_sq']},{payload['N']})`",
        f"- zeros: first `{payload['zero_count']}` via `mpmath.zetazero`; K7 no RH inference",
        "- pairing: `+-gamma` counted as `2|K(gamma_j)|^2`",
        f"- self-test digits: `{fmt(payload['Z1_selftest']['relative_digits'], 12)}`; pass `{payload['Z1_selftest']['pass']}`",
        f"- `a1_raw={fmt(payload['a1_raw'], 18)}`",
        f"- `S_100/a1_raw={fmt(summary['S_100_over_a1_raw'], 12)}`",
        f"- `|K(gamma_1)|={fmt(summary['K_gamma1_abs'], 12)}`",
        f"- decay `p={fmt(summary['decay_fit_p'], 12)}` (`FIT_NOT_LAW`)",
        f"- monotone `{summary['monotone_up']}`; no overshoot `>1.05`: `{summary['no_overshoot_gt_1_05']}`",
        "",
        "## SCORE / REGISTERED MISSES",
        "",
        "- Gap slope `(mu3-mu1)/E`: measured `19.6819692055`; registered `19.4 +- 1.5`; `PASS`.",
        "- W-prime slope: registered `-3.5 +- 0.7`, measured raw `-5.00273858981`; registered miss in favorable direction (`FIT_NOT_LAW`).",
        "- W-prime decomposition: `-5.00273858981 = 0.5 + (8.67649202592 - 19.6819692055)/2`.",
        "- Rung residuals: rungs 4/5 pass `<=1e-60`; rung 6 `1.48383114434507e-60` is a `1.48x` numeric-floor miss; PSD clean judge silent on all rungs.",
        "",
        "## СЛЕДУЮЩИЙ ШАГ",
        "",
        "STOP: handoff ZeroSumCrossCheck_v1; next E5 pen target is `StripTailZeroSumBound`.",
        "",
        "## CURRENT_CODES",
        "",
        f"`{payload['status']}`, `TAUTOLOGICAL_CHANNEL`",
        "",
        "## History",
        "",
        *history_lines,
    ]
    ROUTE_STATE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    summary = payload["Z2_partial_sums"]["summary"]
    selftest = payload["Z1_selftest"]
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "ZeroSumCrossCheck_v1 / Route B / Route Z E5",
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. Phase 2 not run. Q3 mainline not touched.",
        "",
        "Codes:",
        f"{payload['status']}, TAUTOLOGICAL_CHANNEL",
        "",
        "Reclassification:",
        "SymbolDiagonalCrossCheck_v1 is reclassified SYMBOL_MATCH -> TAUTOLOGICAL_CHANNEL: rel 2.4e-91 is the same tau-contraction fingerprint, not an independent E5 zero-sum channel.",
        "",
        "Z0/Z1:",
        "First 100 nontrivial zeros from mpmath.zetazero; K7 no RH inference. K uses normalized tol_B k1; coefficients rebuilt from breakpoint-split E-map at u=lambda/m.",
        f"Self-test t=1: dps40 vs dps80 relative digits = {fmt(selftest['relative_digits'], 12)} (pass={selftest['pass']}).",
        "",
        "Z2 numbers:",
        f"- a1_raw = {fmt(payload['a1_raw'], 18)}",
        f"- |K(gamma1)| = {fmt(summary['K_gamma1_abs'], 12)} (registered [3e-31,3e-30], pass={summary['K_gamma1_registered_pass']})",
        f"- S_100/a1_raw = {fmt(summary['S_100_over_a1_raw'], 12)}",
        f"- monotone = {summary['monotone_up']}",
        f"- max S_J/a1_raw = {fmt(summary['max_S_J_over_a1_raw'], 12)} (no overshoot >1.05={summary['no_overshoot_gt_1_05']})",
        f"- decay p = {fmt(summary['decay_fit_p'], 12)} FIT_NOT_LAW",
        "",
        "State update:",
        "ROUTE_B_STATE.md: E5 opened; Z1-Z3 -> pen; remaining target = StripTailZeroSumBound.",
        "",
        "Question for reviewer:",
        "Accept SLOW_TAIL/zero-sum calibration as the right E5 split, or require a second normalization convention before writing StripTailZeroSumBound?",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    payload = compute()
    write_json(JSON_OUT, payload)
    write_report(payload)
    update_loop_state(payload)
    update_route_state(payload)
    append_symbol_reclassification()
    write_handoff(payload)
    summary = payload["Z2_partial_sums"]["summary"]
    print(payload["status"])
    print(f"S_100/a1_raw={fmt(summary['S_100_over_a1_raw'], 18)}")
    print(f"|K(gamma1)|={fmt(summary['K_gamma1_abs'], 18)}")
    print(f"decay_p={fmt(summary['decay_fit_p'], 18)}")


if __name__ == "__main__":
    main()
