#!/usr/bin/env python3
"""
SymbolDiagonalCrossCheck_v1 for Route B TwoLevelSpectralLadder.

Request-local diagnostic only:
- one point: (lambda_sq, N) = (13, 120)
- no Phase 2
- no Q3 mainline edits
- no new matrix/lattice/eigensolve ladder

The check evaluates the diagonal symbol channel induced by the pilot q_nm
normalization and compares it to the saved raw matvec value for tol_B k1.
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

import mpmath as mp

import routeb_ladder_pilot as pilot
import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "symbol_diagonal_crosscheck_v1.json"
REPORT = REQUEST_DIR / "symbol_diagonal_crosscheck_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"

LAMBDA_SQ = 13
N = 120
REL_TOL = mp.mpf("1e-6")


def progress(label: str) -> None:
    print(f"[SymbolDiagonalCrossCheck_v1] {label}", flush=True)


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


def target_a1_raw() -> Tuple[mp.mpf, str]:
    packet_truth = OUT_DIR / "packet_truth_pull_v1.json"
    if packet_truth.exists():
        data = load_json(packet_truth)
        return mp.mpf(str(data["T0_T2_main"]["a1_raw"])), "out/packet_truth_pull_v1.json:T0_T2_main.a1_raw"

    rotation = OUT_DIR / "rotation_trend_vector_recert_v1.json"
    if rotation.exists():
        data = load_json(rotation)
        row = data["points"]["13"]["raw_triple"]["a1_raw"]
        return mp.mpf(str(row)), "out/rotation_trend_vector_recert_v1.json:points.13.raw_triple.a1_raw"

    ladder = OUT_DIR / "ladder_law_v1.json"
    data = load_json(ladder)
    row = data["T1_rayleigh_table"]["rows"]["13"]["a1_raw"]
    return mp.mpf(str(row)), "out/ladder_law_v1.json:T1_rayleigh_table.rows.13.a1_raw"


def pilot_dps() -> Tuple[int, str]:
    cell = OUT_DIR / f"lambda_sq_{LAMBDA_SQ}_N_{N}.json"
    data = load_json(cell)
    return int(data["dps"]), f"out/lambda_sq_{LAMBDA_SQ}_N_{N}.json:dps"


def tol_b_spec() -> Dict[str, Any]:
    for spec in tp.RUN_SPECS:
        if spec["label"] == "tol_B":
            return dict(spec)
    raise RuntimeError("tol_B spec missing in true_precision_packet_gate_v1.RUN_SPECS")


def rebuild_tol_b_k1() -> Dict[str, Any]:
    old_lambda_sq = tp.LAMBDA_SQ
    old_n = tp.N
    tp.LAMBDA_SQ = LAMBDA_SQ
    tp.N = N
    try:
        run = tp.adaptive_packet_run(tol_b_spec())
    finally:
        tp.LAMBDA_SQ = old_lambda_sq
        tp.N = old_n
    if run.get("status") != "OK":
        raise RuntimeError(f"tol_B packet reconstruction failed: {run.get('status')}")
    return run


def precompute_q_evaluator(n_values: Sequence[int], coeffs: Sequence[mp.mpc], L: mp.mpf):
    weights = [abs(z) ** 2 for z in coeffs]
    a_weights: List[mp.mpc] = []
    b_weights: List[mp.mpc] = []
    for j, m in enumerate(n_values):
        total = mp.mpc(0)
        for i, n in enumerate(n_values):
            if i == j:
                continue
            total += mp.conj(coeffs[i]) / (mp.pi * (n - m))
        a_weights.append(total)
    for i, n in enumerate(n_values):
        total = mp.mpc(0)
        for j, m in enumerate(n_values):
            if i == j:
                continue
            total += coeffs[j] / (mp.pi * (n - m))
        b_weights.append(total)

    def q_value(y: mp.mpf) -> mp.mpc:
        theta = 2 * mp.pi * y / L
        cos_theta = mp.cos(theta)
        sin_theta = mp.sin(theta)
        cos_pos = [mp.mpf("1")]
        sin_pos = [mp.mpf("0")]
        for _ in range(N):
            c_prev = cos_pos[-1]
            s_prev = sin_pos[-1]
            cos_pos.append(c_prev * cos_theta - s_prev * sin_theta)
            sin_pos.append(s_prev * cos_theta + c_prev * sin_theta)

        diag = mp.mpf("0")
        off_left = mp.mpc(0)
        off_right = mp.mpc(0)
        one_minus = 1 - y / L
        for idx, n in enumerate(n_values):
            abs_n = abs(n)
            s = sin_pos[abs_n] if n >= 0 else -sin_pos[abs_n]
            c = cos_pos[abs_n]
            diag += weights[idx] * 2 * one_minus * c
            off_left += coeffs[idx] * s * a_weights[idx]
            off_right += mp.conj(coeffs[idx]) * s * b_weights[idx]
        return diag + off_left - off_right

    return q_value


def quadratic_form_from_kernel(
    n_values: Sequence[int],
    coeffs: Sequence[mp.mpc],
    kernel,
    L: mp.mpf,
) -> mp.mpc:
    total = mp.mpc(0)
    for i, n in enumerate(n_values):
        ci = mp.conj(coeffs[i])
        for j, m in enumerate(n_values):
            total += ci * coeffs[j] * kernel(n, m, L)
    return total


def prime_symbol(q_value, L: mp.mpf) -> Tuple[mp.mpc, List[Dict[str, Any]]]:
    total = mp.mpc(0)
    rows: List[Dict[str, Any]] = []
    for k, mangoldt in pilot.prime_powers_up_to(mp.e**L):
        coeff = mangoldt * k ** mp.mpf("-0.5")
        qk = q_value(mp.log(k))
        contribution = coeff * qk
        total += contribution
        rows.append(
            {
                "k": k,
                "Lambda_k": mangoldt,
                "coefficient": coeff,
                "Q_log_k": qk,
                "contribution": contribution,
            }
        )
    return total, rows


def wr_symbol_direct(q_value, L: mp.mpf) -> Tuple[mp.mpc, Dict[str, Any]]:
    q0 = q_value(mp.mpf("0"))
    const_factor = mp.mpf("0.5") * (mp.euler + mp.log(4 * mp.pi * (mp.e**L - 1) / (mp.e**L + 1)))
    const = q0 * const_factor

    def integrand(x: mp.mpf) -> mp.mpc:
        if abs(x) < mp.mpf("1e-40"):
            return mp.mpf("0")
        return (mp.e ** (x / 2) * q_value(x) - q0) / (mp.e**x - mp.e ** (-x))

    pieces = [0, L / 8, L / 4, 3 * L / 8, L / 2, 5 * L / 8, 3 * L / 4, 7 * L / 8, L]
    integral = mp.quad(integrand, pieces, method="gauss-legendre")
    return const + integral, {
        "Q0": q0,
        "const_factor": const_factor,
        "const": const,
        "integral": integral,
        "pieces": pieces,
    }


def compute_crosscheck() -> Dict[str, Any]:
    started = time.time()
    dps, dps_source = pilot_dps()
    mp.mp.dps = dps
    L = 2 * mp.log(mp.sqrt(LAMBDA_SQ))
    target, target_source = target_a1_raw()

    progress("rebuild tol_B k1 packet")
    packet_started = time.time()
    packet_run = rebuild_tol_b_k1()
    packet_elapsed = time.time() - packet_started
    mp.mp.dps = dps

    progress("precompute q_nm diagonal evaluator")
    coeffs = [mp.mpc(z) for z in packet_run["coeffs_normalized"]["g04"]]
    n_values = list(range(-N, N + 1))
    q_value = precompute_q_evaluator(n_values, coeffs, L)

    progress("compute W02_Q")
    w02_q = quadratic_form_from_kernel(n_values, coeffs, pilot.w02, L)
    progress("compute WP_Q prime symbol")
    wp_q, prime_rows = prime_symbol(q_value, L)
    progress("compute WR_direct_Q")
    wr_q, wr_details = wr_symbol_direct(q_value, L)
    omega_q = w02_q - wr_q
    a_sym = omega_q - wp_q
    a_sym_real = mp.re(a_sym)
    imag_abs = abs(mp.im(a_sym))
    abs_diff = abs(a_sym_real - target)
    rel_diff = abs_diff / max(abs(target), mp.mpf("1e-300"))
    code = "SYMBOL_MATCH" if rel_diff <= REL_TOL else "SYMBOL_NORMALIZATION_MISMATCH"

    attempts = packet_run.get("attempts", [])
    last_attempt = attempts[-1] if attempts else {}
    payload = {
        "gate": "SymbolDiagonalCrossCheck_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": code,
        "registered_pass": code == "SYMBOL_MATCH",
        "lambda_sq": LAMBDA_SQ,
        "N": N,
        "dps": dps,
        "dps_source": dps_source,
        "L": L,
        "method": {
            "description": "direct diagonal symbol channel in pilot q_nm normalization",
            "formula": "a_sym = (W02_Q - WR_direct_Q) - WP_Q",
            "normalization_note": "the external (1/2pi) trace-formula normalization is represented by the pilot q_nm convention used here",
            "matrix_build": False,
            "phase2_run": False,
            "q3_main_touched": False,
        },
        "packet": {
            "source": "true_precision_packet_gate_v1.adaptive_packet_run(tol_B)",
            "label": packet_run["label"],
            "tol": packet_run["tol"],
            "dps": packet_run["dps"],
            "quad_order": packet_run["quad_order"],
            "last_compare": last_attempt,
            "coeff_max_abs_diff": packet_run.get("coeff_max_abs_diff"),
            "pN_norm_g04": packet_run["pN_norms"]["g04"],
            "raw_norm_g04": packet_run["raw_norms"]["g04"],
            "elapsed_s": packet_elapsed,
        },
        "components": {
            "W02_Q": w02_q,
            "WR_direct_Q": wr_q,
            "Omega_Q_W02_minus_WR": omega_q,
            "WP_Q_prime_symbol": wp_q,
            "a_sym": a_sym,
            "a_sym_real": a_sym_real,
            "a_sym_imag_abs": imag_abs,
            "prime_rows": prime_rows,
            "wr_direct_details": wr_details,
        },
        "comparison": {
            "target_matvec_a1_raw": target,
            "target_source": target_source,
            "abs_diff": abs_diff,
            "rel_diff": rel_diff,
            "rel_tolerance": REL_TOL,
            "registered_target": "5.3730e-59",
            "registered_requirement": "relative error <= 1e-6",
        },
        "updates": {
            "ROUTE_B_STATE": "AlphaDetector and ZEO_v2 added iff SYMBOL_MATCH; G3a reduced to TraceCompressionBound",
            "loop_state": "current gate and symbol code recorded",
            "handoff": "compact reviewer report overwritten",
        },
        "elapsed_s": time.time() - started,
    }
    return payload


def write_report(payload: Dict[str, Any]) -> None:
    c = payload["comparison"]
    p = payload["packet"]
    comp = payload["components"]
    lines = [
        "# SymbolDiagonalCrossCheck_v1",
        "",
        "## Verdict",
        "",
        f"`{payload['status']}`",
        "",
        "This is a Route B diagnostic only: no RH claim, no Phase 2, no Q3 mainline edit.",
        "",
        "## Point",
        "",
        f"- `(lambda_sq,N)=({payload['lambda_sq']},{payload['N']})`",
        f"- pilot dps: `{payload['dps']}` from `{payload['dps_source']}`",
        f"- packet: `tol_B`, constructor dps `{p['dps']}`, quad order `{p['quad_order']}`",
        f"- coefficient max diff vs previous quadrature: `{fmt(p['coeff_max_abs_diff'], 12)}`",
        "",
        "## Method",
        "",
        "- `K` is the Fourier packet vector from true-precision `k1 = g04` (`tol_B`).",
        "- `Omega_Q = W02_Q - WR_direct_Q` using the pilot `wr_direct` integral lifted to the diagonal quadratic form.",
        "- `p_R_Q = WP_Q` over prime powers `k <= exp(L) = 13`.",
        "- `a_sym = Omega_Q - p_R_Q`; the `(1/2pi)` trace normalization is the pilot `q_nm` normalization in this channel.",
        "- No `T` matrix was built for this gate.",
        "",
        "## Numbers",
        "",
        f"- `W02_Q = {fmt(comp['W02_Q'], 18)}`",
        f"- `WR_direct_Q = {fmt(comp['WR_direct_Q'], 18)}`",
        f"- `Omega_Q = {fmt(comp['Omega_Q_W02_minus_WR'], 18)}`",
        f"- `WP_Q = {fmt(comp['WP_Q_prime_symbol'], 18)}`",
        f"- `a_sym = {fmt(comp['a_sym_real'], 18)}`",
        f"- `|Im(a_sym)| = {fmt(comp['a_sym_imag_abs'], 8)}`",
        f"- matvec target `a1_raw = {fmt(c['target_matvec_a1_raw'], 18)}` from `{c['target_source']}`",
        f"- `abs_diff = {fmt(c['abs_diff'], 12)}`",
        f"- `rel_diff = {fmt(c['rel_diff'], 12)}`",
        f"- registered tolerance: `{fmt(c['rel_tolerance'], 4)}`",
        "",
        "## Interpretation",
        "",
    ]
    if payload["status"] == "SYMBOL_MATCH":
        lines.extend(
            [
                "- The independent diagonal symbol channel matches the saved raw matvec within the registered relative tolerance.",
                "- This fixes the trace-formula normalization for the G3a pen write-up.",
                "- State promotion applied: `AlphaDetector`, `ZEO_v2`; `G3a` is now reduced to `TraceCompressionBound`.",
            ]
        )
    else:
        lines.extend(
            [
                "- The independent diagonal symbol channel does not match the saved raw matvec at registered tolerance.",
                "- Stop before using the G3a normalization downstream.",
                "- State promotion is not justified until this is resolved.",
            ]
        )
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "SYMBOL_DIAGONAL_CROSSCHECK_V1_COMPLETE",
            "last_verdict": payload["status"],
            "last_codes": [payload["status"]],
            "last_report": "symbol_diagonal_crosscheck_v1.md",
            "last_json": "out/symbol_diagonal_crosscheck_v1.json",
            "symbol_diagonal_crosscheck_v1_status": payload["status"],
            "symbol_diagonal_crosscheck_v1_rel_diff": mp.nstr(payload["comparison"]["rel_diff"], 40),
            "symbol_diagonal_crosscheck_v1_a_sym": mp.nstr(payload["components"]["a_sym_real"], 40),
            "symbol_diagonal_crosscheck_v1_target": mp.nstr(payload["comparison"]["target_matvec_a1_raw"], 40),
            "G3a_open": "reduced to TraceCompressionBound" if payload["registered_pass"] else "symbol normalization mismatch blocks TraceCompressionBound reduction",
            "AlphaDetector": "REGISTERED" if payload["registered_pass"] else "NOT_REGISTERED",
            "ZEO_v2": "REGISTERED" if payload["registered_pass"] else "NOT_REGISTERED",
            "route_status": "NOT_RH_DIAGNOSTIC_ONLY",
            "phase2_run": False,
            "q3_main_touched": False,
            "next_gate": "STOP_AFTER_SYMBOL_DIAGONAL_CROSSCHECK",
            "updated_at_unix": time.time(),
        }
    )
    write_json(LOOP_STATE, state)


def update_route_state(payload: Dict[str, Any]) -> None:
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    history_lines: List[str] = []
    if ROUTE_STATE.exists():
        old = ROUTE_STATE.read_text(encoding="utf-8")
        if "## History" in old:
            history_lines = [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]
    history_lines.append(
        f"- {now}: SymbolDiagonalCrossCheck_v1 -> {payload['status']}; "
        f"a_sym={fmt(payload['components']['a_sym_real'], 12)}; "
        f"rel_diff={fmt(payload['comparison']['rel_diff'], 8)}; "
        "G3a=TraceCompressionBound." if payload["registered_pass"] else "G3a=blocked_by_symbol_normalization."
    )

    proved = [
        "- alpha-Gate Equivalence (a-bound assumed; RH-EQUIVALENT GATE)",
        "- RayleighLadderTracking",
        "- PoissonParityLadder (Hermite exact / PSWF with measured defect)",
        "- MidWindowMassBound absorbed by RayleighLadderTracking",
    ]
    if payload["registered_pass"]:
        proved.extend(["- AlphaDetector", "- ZEO_v2"])

    g3a_line = (
        "- G3a: сведён к TraceCompressionBound (безусловная trace-compression bound; не закрыто)"
        if payload["registered_pass"]
        else "- G3a: blocked until SymbolDiagonalCrossCheck_v1 normalization mismatch is resolved"
    )
    door = "SYMBOL_MATCH_TRACE_NORMALIZATION_CONFIRMED" if payload["registered_pass"] else "SYMBOL_NORMALIZATION_MISMATCH"
    next_step = (
        "STOP: use `symbol_diagonal_crosscheck_v1.md` for reviewer/pen handoff; next proof target is `TraceCompressionBound`."
        if payload["registered_pass"]
        else "STOP: fix symbol normalization before any G3a pen write-up."
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
        *proved,
        "",
        "## ОТКРЫТО",
        "",
        "- G3: RayleighExcessBound `alpha <= poly(lambda)*E`, not raw eta",
        g3a_line,
        "- G4': CONDITIONAL(RH-regime) theorem candidate; UNCONDITIONAL detector component using `mu3-mu1`",
        "- alpha-Gate: RH-ядро; только мерить и мониторить `W_prime`",
        "- finite-N to continuum double limit remains explicit",
        "",
        "## SYMBOL DIAGONAL CROSSCHECK",
        "",
        f"- code: `{payload['status']}`",
        f"- `(lambda_sq,N)=({payload['lambda_sq']},{payload['N']})`",
        f"- `a_sym={fmt(payload['components']['a_sym_real'], 18)}`",
        f"- target raw matvec `a1_raw={fmt(payload['comparison']['target_matvec_a1_raw'], 18)}`",
        f"- `rel_diff={fmt(payload['comparison']['rel_diff'], 12)}`; registered tolerance `<=1e-6`",
        "- normalization: pilot `q_nm` diagonal symbol channel for `(1/2pi) int (Omega-p_R)|K|^2`",
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
        next_step,
        "",
        "## CURRENT_CODES",
        "",
        f"`{payload['status']}`",
        "",
        "## History",
        "",
        *history_lines,
    ]
    ROUTE_STATE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    c = payload["comparison"]
    comp = payload["components"]
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "SymbolDiagonalCrossCheck_v1 / Route B TwoLevelSpectralLadder",
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. Phase 2 not run. Q3 mainline not touched.",
        "",
        "Code:",
        payload["status"],
        "",
        "Point:",
        f"(lambda_sq,N)=({payload['lambda_sq']},{payload['N']}), pilot dps={payload['dps']}, packet=tol_B k1.",
        "",
        "Normalization channel:",
        "a_sym = (W02_Q - WR_direct_Q) - WP_Q, where Q is the pilot q_nm diagonal quadratic form for k1.",
        "This is the request-local version of (1/2pi) int (Omega(t)-p_R(t)) |K(t)|^2 dt.",
        "",
        "Key numbers:",
        f"- a_sym = {fmt(comp['a_sym_real'], 18)}",
        f"- target raw matvec a1_raw = {fmt(c['target_matvec_a1_raw'], 18)}",
        f"- abs_diff = {fmt(c['abs_diff'], 12)}",
        f"- rel_diff = {fmt(c['rel_diff'], 12)}",
        f"- tolerance = {fmt(c['rel_tolerance'], 4)}",
        f"- |Im(a_sym)| = {fmt(comp['a_sym_imag_abs'], 8)}",
        "",
        "State update:",
        (
            "ROUTE_B_STATE.md now records AlphaDetector and ZEO_v2 under ДОКАЗАНО ПЕРОМ; "
            "G3a is reduced to TraceCompressionBound."
            if payload["registered_pass"]
            else "ROUTE_B_STATE.md records the symbol normalization mismatch; G3a is not reduced."
        ),
        "",
        "Question for reviewer:",
        "Accept this as fixing the trace-formula normalization for the G3a pen write-up, or require a second independent symbolic normalization audit before writing TraceCompressionBound?",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    payload = compute_crosscheck()
    write_json(JSON_OUT, payload)
    write_report(payload)
    update_loop_state(payload)
    update_route_state(payload)
    write_handoff(payload)
    print(payload["status"])
    print(f"a_sym={fmt(payload['components']['a_sym_real'], 18)}")
    print(f"target={fmt(payload['comparison']['target_matvec_a1_raw'], 18)}")
    print(f"rel_diff={fmt(payload['comparison']['rel_diff'], 12)}")


if __name__ == "__main__":
    main()
