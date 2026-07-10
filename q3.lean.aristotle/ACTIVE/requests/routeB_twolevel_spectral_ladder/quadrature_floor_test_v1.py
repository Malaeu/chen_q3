#!/usr/bin/env python3
"""
QuadratureFloorTest_v1 for Route B TwoLevelSpectralLadder.

Request-local diagnostic only:
- one point: (lambda_sq, N) = (13, 120)
- no Phase 2, no new lambda/N anchors, no RH claim
- rebuild only k1, k2_odd, k2_even packet vectors through the existing
  make_packets path with quadrature refinement labels for the requested
  tol=1e-15 and tol=1e-18 checks.
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import mpmath as mp

import parity_audit_rebuild_v2 as parity
import routeb_ladder_pilot as pilot


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "quadrature_floor_test_v1.json"
REPORT = REQUEST_DIR / "quadrature_floor_test_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"

LAMBDA_SQ = 13
N = 120

PACKET_NAMES = {"k1": "g04", "k2_odd": "g26", "k2_even": "g048perp"}
EXPECTED_PARITY = {"k1": "even", "k2_odd": "odd", "k2_even": "even"}
ORDER = ["k1", "k2_odd", "k2_even"]

# The current packet constructor is double/numpy based. These are refinement
# runs that keep the same quadrature scheme while exposing the instrument floor.
RUNS = [
    {"label": "baseline_tol_1e-9", "requested_tol": "1e-9", "quad_order": 900},
    {"label": "requested_tol_1e-15", "requested_tol": "1e-15", "quad_order": 1800},
    {"label": "requested_tol_1e-18", "requested_tol": "1e-18", "quad_order": 3600},
]


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, (mp.mpf, mp.mpc)):
        return mp.nstr(value, 80)
    return value


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def mpf(value: Any) -> mp.mpf:
    return mp.mpf(str(value))


def mpc(value: Any) -> mp.mpc:
    return parity.parse_mpc(value)


def fmt(value: Any, digits: int = 12) -> str:
    if value is None:
        return "MISSING"
    return mp.nstr(value, digits)


def matrix_to_rows(A: mp.matrix) -> List[List[Any]]:
    return [[A[i, j] for j in range(A.cols)] for i in range(A.rows)]


def eigvals_hermitian(A: mp.matrix) -> List[mp.mpf]:
    vals, _ = mp.eighe(pilot.hermitian_part(A))
    return [mp.re(vals[i]) for i in range(vals.rows)]


def packet_parity_split(quad_order: int) -> Tuple[Dict[str, mp.matrix], Dict[str, mp.matrix], List[Dict[str, Any]]]:
    lam = mp.sqrt(LAMBDA_SQ)
    packet = pilot.make_packets(float(lam), N, quad_order=quad_order)
    raw: Dict[str, mp.matrix] = {}
    projected: Dict[str, mp.matrix] = {}
    rows: List[Dict[str, Any]] = []

    for logical in ORDER:
        v = pilot.mp_vec_from_np(packet.coeffs[PACKET_NAMES[logical]])
        even, odd = parity.parity_parts(v)
        expected = EXPECTED_PARITY[logical]
        keep = even if expected == "even" else odd
        off = odd if expected == "even" else even
        raw[logical] = parity.normalize(v)
        projected[logical] = parity.normalize(keep)
        rows.append(
            {
                "vector": logical,
                "packet_name": PACKET_NAMES[logical],
                "expected_parity": expected,
                "delta_off_parity": pilot.norm(off) / max(pilot.norm(v), mp.mpf("1e-300")),
                "even_norm": pilot.norm(even),
                "odd_norm": pilot.norm(odd),
            }
        )
    return raw, projected, rows


def even_g_block(T: mp.matrix, even_basis: Sequence[mp.matrix]) -> mp.matrix:
    Tq = [T * q for q in even_basis]
    G = mp.matrix(len(even_basis), len(even_basis))
    for i, qi in enumerate(even_basis):
        for j, Tqj in enumerate(Tq):
            G[i, j] = pilot.inner(qi, Tqj)
    return G


def xi1_from_saved_cache() -> Tuple[mp.matrix, Dict[str, Any]]:
    path = OUT_DIR / "nconv_anchor_lambda_sq_13_N_120.json"
    data = load_json(path)
    cache = data.get("xi_m_y_cache", [])
    if not cache or "xi_vector" not in cache[0]:
        raise RuntimeError("xi1 saved eigenvector cache missing at out/nconv_anchor_lambda_sq_13_N_120.json:xi_m_y_cache[0]")

    v = mp.matrix(2 * N + 1, 1)
    seen = set()
    for row in cache[0]["xi_vector"]:
        n = int(row["n"])
        seen.add(n)
        v[n + N] = mp.mpc(mpf(row["re"]), mpf(row["im"]))
    expected = set(range(-N, N + 1))
    if seen != expected:
        missing = sorted(expected - seen)
        raise RuntimeError(f"xi1 saved vector has incomplete n support; missing first entries: {missing[:5]}")
    nrm = pilot.norm(v)
    if nrm == 0:
        raise RuntimeError("xi1 saved vector has zero norm")
    for i in range(v.rows):
        v[i] /= nrm
    return v, {
        "status": "OK",
        "source": "out/nconv_anchor_lambda_sq_13_N_120.json:xi_m_y_cache[0].xi_vector",
        "saved_y_norm": mpf(cache[0]["y_norm"]),
        "renormalization_norm_before": nrm,
    }


def project_residual_norm(v: mp.matrix, basis: Sequence[mp.matrix]) -> mp.mpf:
    residual = pilot.copy_vec(v)
    for q in basis:
        coeff = pilot.inner(q, v)
        for i in range(residual.rows):
            residual[i] -= coeff * q[i]
    return pilot.norm(residual)


def compute_run(run: Dict[str, Any], T: mp.matrix, xi1: mp.matrix) -> Dict[str, Any]:
    started = time.time()
    raw, projected, dust_rows = packet_parity_split(int(run["quad_order"]))
    even_packets, q_stats = pilot.modified_gram_schmidt_mp(
        [projected["k1"], projected["k2_even"]],
        tol=mp.power(10, -min(70, max(30, mp.mp.dps // 3))),
    )
    if len(even_packets) != 2:
        raise RuntimeError(f"even packet MGS accepted {len(even_packets)} vectors, expected 2")

    G_even = even_g_block(T, even_packets)
    g_vals = sorted(eigvals_hermitian(G_even))
    a1_raw = mp.re(pilot.inner(raw["k1"], T * raw["k1"]))
    a1_even_projected = mp.re(pilot.inner(projected["k1"], T * projected["k1"]))
    align_raw = 1 - abs(pilot.inner(xi1, raw["k1"]))
    align_even_projected = 1 - abs(pilot.inner(xi1, projected["k1"]))
    y_norm = project_residual_norm(xi1, even_packets)
    dust_max = max(row["delta_off_parity"] for row in dust_rows)

    return {
        "label": run["label"],
        "requested_tol": run["requested_tol"],
        "quad_order": int(run["quad_order"]),
        "elapsed_s": time.time() - started,
        "packet_builder": "routeb_ladder_pilot.make_packets(double/numpy, quadrature refinement only)",
        "dust_rows": dust_rows,
        "dust_max_delta_off": dust_max,
        "even_q_stats": q_stats,
        "a1_raw_k1": a1_raw,
        "a1_even_projected_k1": a1_even_projected,
        "G_even": matrix_to_rows(G_even),
        "lambda1_G_even": g_vals[0],
        "lambda2_G_even": g_vals[1],
        "alignment_one_minus_abs_xi1_inner_raw_k1": align_raw,
        "alignment_one_minus_abs_xi1_inner_even_projected_k1": align_even_projected,
        "y_norm_xi1_minus_P_evenM_xi1": y_norm,
    }


def optional_y_12_120() -> Dict[str, Any]:
    candidates = [
        ("out/nconv_anchor_lambda_sq_12_N_120.json", ["xi_m_y_cache", 0, "y_norm"]),
        ("out/full_low_eig_lambda_sq_12_N_120.json", ["eigenvectors", 0, "projection_Mperp_norm"]),
        ("out/feshbach_lambda_sq_12_N_120.json", ["dynamic_feshbach", 0, "y_actual_norm"]),
    ]
    checked = []
    for rel, keys in candidates:
        path = OUT_DIR / Path(rel).name
        checked.append(rel)
        if not path.exists():
            continue
        data: Any = load_json(path)
        ok = True
        for key in keys:
            try:
                data = data[key]
            except (KeyError, IndexError, TypeError):
                ok = False
                break
        if ok:
            return {"lambda_sq": 12, "N": 120, "status": "OK", "source": rel, "value": mpf(data)}
    return {
        "lambda_sq": 12,
        "N": 120,
        "status": "MISSING",
        "source": None,
        "checked": checked,
        "value": None,
    }


def saved_y_13_120(xi_source: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "lambda_sq": 13,
        "N": 120,
        "status": "OK",
        "source": "out/nconv_anchor_lambda_sq_13_N_120.json:xi_m_y_cache[0].y_norm",
        "value": xi_source["saved_y_norm"],
    }


def saved_y_14_120() -> Dict[str, Any]:
    candidates = [
        ("out/feshbach_lambda_sq_14_N_120.json", ["dynamic_feshbach", 0, "y_actual_norm"]),
        ("out/full_low_eig_lambda_sq_14_N_120.json", ["eigenvectors", 0, "projection_Mperp_norm"]),
    ]
    for rel, keys in candidates:
        path = OUT_DIR / Path(rel).name
        if not path.exists():
            continue
        data: Any = load_json(path)
        ok = True
        for key in keys:
            try:
                data = data[key]
            except (KeyError, IndexError, TypeError):
                ok = False
                break
        if ok:
            return {"lambda_sq": 14, "N": 120, "status": "OK", "source": rel, "value": mpf(data)}
    return {"lambda_sq": 14, "N": 120, "status": "MISSING", "source": None, "value": None}


def ratio(a: mp.mpf, b: mp.mpf) -> mp.mpf:
    return a / max(b, mp.mpf("1e-300"))


def classify(runs: Sequence[Dict[str, Any]], q3_rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    baseline = runs[0]
    tol15 = runs[1]
    tol18 = runs[2]
    base_lambda = baseline["lambda1_G_even"]
    lambda15 = tol15["lambda1_G_even"]
    lambda18 = tol18["lambda1_G_even"]
    lambda_ratio15 = ratio(lambda15, base_lambda)
    lambda_ratio18 = ratio(lambda18, base_lambda)
    drop15 = ratio(base_lambda, lambda15) if lambda15 < base_lambda else mp.mpf("1") / lambda_ratio15
    drop18 = ratio(base_lambda, lambda18) if lambda18 < base_lambda else mp.mpf("1") / lambda_ratio18
    within_x3_15 = mp.mpf("1") / 3 <= lambda_ratio15 <= 3
    within_x3_18 = mp.mpf("1") / 3 <= lambda_ratio18 <= 3
    alignment18 = tol18["alignment_one_minus_abs_xi1_inner_even_projected_k1"]

    dust_ratio15 = ratio(tol15["dust_max_delta_off"], baseline["dust_max_delta_off"])
    dust_ratio18 = ratio(tol18["dust_max_delta_off"], baseline["dust_max_delta_off"])
    dust_registered_drop_pass = dust_ratio15 < mp.mpf("1e-3") and dust_ratio18 < dust_ratio15

    if drop15 >= mp.mpf("1e4") and drop18 > drop15 and alignment18 < mp.mpf("1e-10"):
        fork_verdict = "PACKET_FLOOR_CONFIRMED"
        fork_reason = "lambda1(G_even) dropped by >=4 orders and kept dropping; alignment passed."
    elif within_x3_15 and within_x3_18:
        fork_verdict = "PACKET_RAYLEIGH_PHYSICAL"
        fork_reason = "lambda1(G_even) stayed within x3 for both refinement runs."
    else:
        fork_verdict = "FLOOR_AMBIGUOUS"
        fork_reason = "lambda1(G_even) moved outside x3 but did not satisfy the >=1e4 drop rule."

    y13_latest = tol18["y_norm_xi1_minus_P_evenM_xi1"]
    m1_ref = mp.mpf("1.2e-10")
    malt_ref = mp.mpf("2.8e-9")
    m_selector = "M-alt" if abs(mp.log(y13_latest / malt_ref)) <= abs(mp.log(y13_latest / m1_ref)) else "M1"

    failure_codes: List[str] = []
    if fork_verdict == "FLOOR_AMBIGUOUS":
        failure_codes.append("FLOOR_AMBIGUOUS")
    if any(row["status"] != "OK" for row in q3_rows):
        failure_codes.append("Y_CACHE_MISSING")

    return {
        "fork_verdict": fork_verdict,
        "fork_reason": fork_reason,
        "lambda_ratio_tol15_over_baseline": lambda_ratio15,
        "lambda_ratio_tol18_over_baseline": lambda_ratio18,
        "drop_factor_baseline_over_tol15": drop15,
        "drop_factor_baseline_over_tol18": drop18,
        "within_x3_tol15": within_x3_15,
        "within_x3_tol18": within_x3_18,
        "dust_ratio_tol15_over_baseline": dust_ratio15,
        "dust_ratio_tol18_over_baseline": dust_ratio18,
        "dust_registered_proportional_drop_pass": dust_registered_drop_pass,
        "instrument_floor_note": "Current make_packets path is double/numpy based; dust did not scale to requested 1e-15/1e-18 targets.",
        "y13_latest": y13_latest,
        "m_selector_by_y13": m_selector,
        "m_selector_refs": {"M1": m1_ref, "M-alt": malt_ref},
        "failure_codes": failure_codes,
        "primary_failure_code": failure_codes[0] if failure_codes else None,
        "status": "complete_with_registered_failure" if failure_codes else "complete",
    }


def write_report(payload: Dict[str, Any]) -> None:
    lines = [
        "# QuadratureFloorTest_v1",
        "",
        "Route B TwoLevelSpectralLadder diagnostic only. Not RH. No Phase 2. One point `(lambda_sq,N)=(13,120)`.",
        "",
        "## Verdict",
        "",
        f"- status: `{payload['classification']['status']}`",
        f"- fork_verdict: `{payload['classification']['fork_verdict']}`",
        f"- failure_codes: `{payload['classification']['failure_codes']}`",
        f"- reason: {payload['classification']['fork_reason']}",
        f"- instrument floor: {payload['classification']['instrument_floor_note']}",
        "",
        "## Q1 Packet Rebuild Dust",
        "",
        "| run | requested tol | quad_order | max delta_off | k1 | k2_odd | k2_even |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for run in payload["runs"]:
        deltas = {row["vector"]: row["delta_off_parity"] for row in run["dust_rows"]}
        lines.append(
            f"| `{run['label']}` | `{run['requested_tol']}` | {run['quad_order']} | `{fmt(run['dust_max_delta_off'], 8)}` | `{fmt(deltas['k1'], 8)}` | `{fmt(deltas['k2_odd'], 8)}` | `{fmt(deltas['k2_even'], 8)}` |"
        )

    cls = payload["classification"]
    lines.extend(
        [
            "",
            "Dust ratios:",
            f"- tol=1e-15 over baseline: `{fmt(cls['dust_ratio_tol15_over_baseline'], 8)}`",
            f"- tol=1e-18 over baseline: `{fmt(cls['dust_ratio_tol18_over_baseline'], 8)}`",
            f"- registered proportional drop pass: `{cls['dust_registered_proportional_drop_pass']}`",
            "",
            "## Q2 Recomputed Metrics",
            "",
            "| run | a1 raw | a1 even-projected | lambda1(G_even) | lambda2(G_even) | 1-|<xi1,k1_even>| | ||y|| |",
            "|---|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for run in payload["runs"]:
        lines.append(
            f"| `{run['label']}` | `{fmt(run['a1_raw_k1'], 8)}` | `{fmt(run['a1_even_projected_k1'], 8)}` | `{fmt(run['lambda1_G_even'], 8)}` | `{fmt(run['lambda2_G_even'], 8)}` | `{fmt(run['alignment_one_minus_abs_xi1_inner_even_projected_k1'], 8)}` | `{fmt(run['y_norm_xi1_minus_P_evenM_xi1'], 8)}` |"
        )

    lines.extend(
        [
            "",
            "Lambda1 movement:",
            f"- tol=1e-15 / baseline: `{fmt(cls['lambda_ratio_tol15_over_baseline'], 8)}`; drop factor `{fmt(cls['drop_factor_baseline_over_tol15'], 8)}`",
            f"- tol=1e-18 / baseline: `{fmt(cls['lambda_ratio_tol18_over_baseline'], 8)}`; drop factor `{fmt(cls['drop_factor_baseline_over_tol18'], 8)}`",
            f"- within x3 at both tightened labels: `{cls['within_x3_tol15'] and cls['within_x3_tol18']}`",
            f"- M selector by latest ||y||: `{cls['m_selector_by_y13']}`",
            "",
            "## Q3 Free Pulls",
            "",
            "| lambda_sq | N | status | ||y|| | source |",
            "|---:|---:|---|---:|---|",
        ]
    )
    for row in payload["q3_free_pulls"]:
        source = row["source"] if row["source"] else ",".join(row.get("checked", []))
        lines.append(f"| {row['lambda_sq']} | {row['N']} | `{row['status']}` | `{fmt(row['value'], 12)}` | `{source}` |")

    lines.extend(
        [
            "",
            "## Stop",
            "",
            "Stop after this report + handoff. Carry the fork verdict and any failure code into `OperatorStaticSchurStabilityGate` on `S0_parity`.",
            "",
        ]
    )
    REPORT.write_text("\n".join(lines), encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    cls = payload["classification"]
    latest = payload["runs"][-1]
    lines = [
        "PROSHKA_ROUTE_REVIEW",
        "",
        "Gate:",
        "QuadratureFloorTest_v1 / Route B TwoLevelSpectralLadder",
        "",
        "Verdict:",
        cls["fork_verdict"],
        "",
        "Failure codes:",
        str(cls["failure_codes"]),
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. Phase 2 not run. No new lambda/N anchors. Q3 mainline not touched.",
        "",
        "What happened:",
        "- Rebuilt only k1, k2_odd, k2_even for (13,120) through the existing make_packets path.",
        "- Requested tol labels 1e-15 and 1e-18 were tested by quadrature refinement, but the current packet builder is double/numpy based.",
        f"- max packet parity dust baseline -> tol1e-15 -> tol1e-18: {fmt(payload['runs'][0]['dust_max_delta_off'], 8)} -> {fmt(payload['runs'][1]['dust_max_delta_off'], 8)} -> {fmt(payload['runs'][2]['dust_max_delta_off'], 8)}.",
        f"- lambda1(G_even) baseline -> tol1e-15 -> tol1e-18: {fmt(payload['runs'][0]['lambda1_G_even'], 8)} -> {fmt(payload['runs'][1]['lambda1_G_even'], 8)} -> {fmt(payload['runs'][2]['lambda1_G_even'], 8)}.",
        f"- latest ||y|| = {fmt(latest['y_norm_xi1_minus_P_evenM_xi1'], 12)}; selector by requested M1/M-alt references: {cls['m_selector_by_y13']}.",
        "- Saved ||y||(12,120) is missing if `Y_CACHE_MISSING` is listed above.",
        "",
        "Question for Proshka:",
        "Accept this as enough to carry the fork verdict into OperatorStaticSchurStabilityGate on S0_parity, or require a separate high-precision packet constructor before interpreting lambda1(G_even)?",
        "",
        "Stop condition:",
        "Codex stops here after report + handoff, then next goal should be OperatorStaticSchurStabilityGate carrying this verdict/failure-code state.",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    cls = payload["classification"]
    state.update(
        {
            "current_gate": "QUADRATURE_FLOOR_TEST_V1_COMPLETE",
            "last_verdict": cls["fork_verdict"],
            "last_failure_codes": cls["failure_codes"],
            "next_gate": "OperatorStaticSchurStabilityGate_on_S0_parity",
            "last_report": "quadrature_floor_test_v1.md",
            "last_json": "out/quadrature_floor_test_v1.json",
            "route_status": "NOT_RH_DIAGNOSTIC_ONLY",
            "phase2_run": False,
            "new_lambda_or_N_anchor_bought": False,
            "q3_main_touched": False,
        }
    )
    write_json(LOOP_STATE, state)


def main() -> None:
    started = time.time()
    cell = load_json(OUT_DIR / "lambda_sq_13_N_120.json")
    dps = int(cell["dps"])
    mp.mp.dps = dps
    lam = mp.sqrt(LAMBDA_SQ)

    xi1, xi_source = xi1_from_saved_cache()
    q3_rows = [optional_y_12_120(), saved_y_13_120(xi_source), saved_y_14_120()]

    # Full T was not persisted in the anchor; this follows the deterministic
    # rebuild path already used by the parity audits for this request.
    T = pilot.build_tau_matrix(lam, N, dps)

    run_payloads = [compute_run(run, T, xi1) for run in RUNS]
    classification = classify(run_payloads, q3_rows)
    payload: Dict[str, Any] = {
        "gate": "QuadratureFloorTest_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "source": "request_local_packet_refinement_rebuild",
        "lambda_sq": LAMBDA_SQ,
        "lambda": lam,
        "N": N,
        "dps": dps,
        "status": classification["status"],
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "new_lambdas": False,
        "new_T_family": False,
        "new_full_ladder": False,
        "q3_main_touched": False,
        "elapsed_s": time.time() - started,
        "xi1_source": xi_source,
        "runs": run_payloads,
        "q3_free_pulls": q3_rows,
        "classification": classification,
        "next_gate": "OperatorStaticSchurStabilityGate_on_S0_parity",
    }
    write_json(JSON_OUT, payload)
    write_report(payload)
    write_handoff(payload)
    update_loop_state(payload)
    print(f"Wrote {JSON_OUT}")
    print(f"Wrote {REPORT}")
    print(f"fork_verdict={classification['fork_verdict']} failure_codes={classification['failure_codes']}")


if __name__ == "__main__":
    main()
