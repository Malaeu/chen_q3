#!/usr/bin/env python3
"""
RotationTrend_and_VectorRecert_v1 for Route B TwoLevelSpectralLadder.

Request-local diagnostic only:
- true-precision packet rotation trend at (12,120), (13,120), (14,120)
- fresh dps>=250 inverse-iteration recert at (13,120)
- no RH claim, no Phase 2, no new lambda/N anchors.
"""

from __future__ import annotations

import json
import random
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import mpmath as mp

import parity_audit_rebuild_v2 as parity
import routeb_ladder_pilot as pilot
import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "rotation_trend_vector_recert_v1.json"
REPORT = REQUEST_DIR / "rotation_trend_vector_recert_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"

N = 120
PACKET_NAMES = tp.PACKET_NAMES
LOGICAL_BY_PACKET = tp.LOGICAL_BY_PACKET
EXPECTED_PARITY = tp.EXPECTED_PARITY
DPS_PACKET = 110
QUAD_ORDER = 192
DPS_RECERT = 250


@contextmanager
def tp_lambda(lambda_sq: int):
    old_lambda_sq = tp.LAMBDA_SQ
    old_N = tp.N
    tp.LAMBDA_SQ = lambda_sq
    tp.N = N
    try:
        yield
    finally:
        tp.LAMBDA_SQ = old_lambda_sq
        tp.N = old_N


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


def mpf(value: Any) -> mp.mpf:
    return mp.mpf(str(value))


def fmt(value: Any, digits: int = 12) -> str:
    if value is None:
        return "MISSING"
    return mp.nstr(value, digits)


def matrix_to_rows(A: mp.matrix) -> List[List[Any]]:
    return [[A[i, j] for j in range(A.cols)] for i in range(A.rows)]


def vector_from_coeffs(coeffs: Sequence[mp.mpc]) -> mp.matrix:
    v = mp.matrix(len(coeffs), 1)
    for i, z in enumerate(coeffs):
        v[i] = z
    return v


def coeff_norm(coeffs: Sequence[mp.mpc]) -> mp.mpf:
    return mp.sqrt(sum(abs(z) ** 2 for z in coeffs))


def normalize_coeffs(coeffs: Sequence[mp.mpc]) -> Tuple[List[mp.mpc], mp.mpf]:
    nrm = coeff_norm(coeffs)
    if nrm == 0:
        raise RuntimeError("zero packet coefficient norm")
    return [z / nrm for z in coeffs], nrm


def normalize_vec(v: mp.matrix) -> mp.matrix:
    out = pilot.copy_vec(v)
    nrm = pilot.norm(out)
    if nrm == 0:
        raise RuntimeError("zero vector")
    for i in range(out.rows):
        out[i] /= nrm
    return out


def subtract_projection(v: mp.matrix, q: mp.matrix) -> None:
    coeff = pilot.inner(q, v)
    for i in range(v.rows):
        v[i] -= coeff * q[i]


def orthogonalize(v: mp.matrix, basis: Sequence[mp.matrix]) -> mp.matrix:
    out = pilot.copy_vec(v)
    for _ in range(2):
        for q in basis:
            subtract_projection(out, q)
    return normalize_vec(out)


def eigvals_vecs_hermitian(A: mp.matrix) -> Tuple[List[mp.mpf], mp.matrix]:
    vals, vecs = mp.eighe(pilot.hermitian_part(A))
    return [mp.re(vals[i]) for i in range(vals.rows)], vecs


def high_precision_packet_run(lambda_sq: int, target_N: int = N) -> Dict[str, Any]:
    started = time.time()
    with tp_lambda(lambda_sq):
        mp.mp.dps = DPS_PACKET
        model = tp.build_prolate_model(DPS_PACKET)
        n_values = list(range(-target_N, target_N + 1))
        low = tp.integrate_coefficients(model, dps=DPS_PACKET, quad_order=QUAD_ORDER // 2, n_values=n_values, names=PACKET_NAMES)
        high = tp.integrate_coefficients(model, dps=DPS_PACKET, quad_order=QUAD_ORDER, n_values=n_values, names=PACKET_NAMES)
        diff = tp.max_coeff_diff(low, high, PACKET_NAMES)
    normalized: Dict[str, List[mp.mpc]] = {}
    pN_norms: Dict[str, mp.mpf] = {}
    for name in PACKET_NAMES:
        normalized[name], pN_norms[name] = normalize_coeffs(high.coeffs[name])
    return {
        "lambda_sq": lambda_sq,
        "N": target_N,
        "dps": DPS_PACKET,
        "quad_order": QUAD_ORDER,
        "compare_quad_order": QUAD_ORDER // 2,
        "coeff_max_abs_diff_vs_half_q": diff,
        "coeffs_normalized": normalized,
        "raw_norms": high.raw_norms,
        "pN_norms": pN_norms,
        "elapsed_s": time.time() - started,
    }


def packet_vectors(packet_run: Dict[str, Any]) -> Dict[str, mp.matrix]:
    return {
        LOGICAL_BY_PACKET[name]: vector_from_coeffs(packet_run["coeffs_normalized"][name])
        for name in PACKET_NAMES
    }


def parity_project(vectors: Dict[str, mp.matrix]) -> Tuple[Dict[str, mp.matrix], List[Dict[str, Any]]]:
    projected: Dict[str, mp.matrix] = {}
    rows: List[Dict[str, Any]] = []
    for logical in ("k1", "k2_odd", "k2_even"):
        v = vectors[logical]
        even, odd = parity.parity_parts(v)
        expected = EXPECTED_PARITY[logical]
        keep = even if expected == "even" else odd
        off = odd if expected == "even" else even
        projected[logical] = normalize_vec(keep)
        rows.append(
            {
                "vector": logical,
                "expected_parity": expected,
                "delta_off_parity": pilot.norm(off) / max(pilot.norm(v), mp.mpf("1e-300")),
                "even_norm": pilot.norm(even),
                "odd_norm": pilot.norm(odd),
            }
        )
    return projected, rows


def block_from_basis(T: mp.matrix, basis: Sequence[mp.matrix]) -> mp.matrix:
    Tq = [T * q for q in basis]
    G = mp.matrix(len(basis), len(basis))
    for i, qi in enumerate(basis):
        for j, Tqj in enumerate(Tq):
            G[i, j] = pilot.inner(qi, Tqj)
    return G


def build_T(lambda_sq: int, dps_override: Optional[int] = None) -> Tuple[mp.matrix, int]:
    cell = load_json(OUT_DIR / f"lambda_sq_{lambda_sq}_N_{N}.json")
    dps = int(dps_override if dps_override is not None else cell["dps"])
    mp.mp.dps = dps
    return pilot.build_tau_matrix(mp.sqrt(lambda_sq), N, dps), dps


def raw_2x2_ground(a1: mp.mpf, a2: mp.mpf, g12: mp.mpc) -> Tuple[List[mp.mpf], mp.matrix]:
    G = mp.matrix([[a1, g12], [mp.conj(g12), a2]])
    return eigvals_vecs_hermitian(G)


def parse_mpc(value: Any) -> mp.mpc:
    return parity.parse_mpc(value)


def rotation_point(lambda_sq: int, packet_run: Dict[str, Any], T: mp.matrix, dps_T: int) -> Dict[str, Any]:
    vectors = packet_vectors(packet_run)
    projected, dust_rows = parity_project(vectors)
    k1_raw = vectors["k1"]
    k2e_raw = vectors["k2_even"]
    gamma = pilot.inner(k1_raw, k2e_raw)
    a1_raw = mp.re(pilot.inner(k1_raw, T * k1_raw))
    a2_raw = mp.re(pilot.inner(k2e_raw, T * k2e_raw))
    g12_raw = pilot.inner(k1_raw, T * k2e_raw)
    raw_vals, raw_vecs = raw_2x2_ground(a1_raw, a2_raw, g12_raw)

    q1 = projected["k1"]
    q2 = orthogonalize(projected["k2_even"], [q1])
    G = block_from_basis(T, [q1, q2])
    vals, vecs = eigvals_vecs_hermitian(G)
    a1 = mp.re(G[0, 0])
    a2 = mp.re(G[1, 1])
    g12 = G[0, 1]
    denom = a2 - a1
    theta_ratio = abs(g12) / max(abs(denom), mp.mpf("1e-300"))
    ground_vec = [vecs[i, 0] for i in range(vecs.rows)]
    theta_angle = mp.acos(min(mp.mpf("1"), abs(ground_vec[0])))
    return {
        "lambda_sq": lambda_sq,
        "N": N,
        "dps_T": dps_T,
        "packet_constructor": {
            "dps": packet_run["dps"],
            "quad_order": packet_run["quad_order"],
            "compare_quad_order": packet_run["compare_quad_order"],
            "coeff_max_abs_diff_vs_half_q": packet_run["coeff_max_abs_diff_vs_half_q"],
        },
        "dust_rows": dust_rows,
        "dust_max_delta_off": max(row["delta_off_parity"] for row in dust_rows),
        "raw_triple": {
            "a1_raw": a1_raw,
            "a2_raw": a2_raw,
            "g12_raw": g12_raw,
            "gram_gamma_raw": gamma,
            "ordinary_raw_2x2_eigenvalues": raw_vals,
            "ordinary_raw_2x2_ground": raw_vals[0],
            "ordinary_raw_2x2_ground_vector": [raw_vecs[i, 0] for i in range(raw_vecs.rows)],
        },
        "gram_orthonormal": {
            "G_even": matrix_to_rows(G),
            "a1": a1,
            "a2_orth": a2,
            "g12_orth": g12,
            "lambda1": vals[0],
            "lambda2": vals[1],
            "denominator_a2_minus_a1": denom,
            "theta_ratio_abs_g12_over_gap": theta_ratio,
            "theta_ground_angle": theta_angle,
            "ground_vector": ground_vec,
        },
    }


def classify_rotation(points: Dict[int, Dict[str, Any]]) -> Dict[str, Any]:
    theta12 = points[12]["gram_orthonormal"]["theta_ground_angle"]
    theta13 = points[13]["gram_orthonormal"]["theta_ground_angle"]
    theta14 = points[14]["gram_orthonormal"]["theta_ground_angle"]
    targets = {
        "slope_-2": {12: mp.mpf("7.5e-5"), 13: mp.mpf("6.41e-5"), 14: mp.mpf("5.5e-5")},
        "slope_-3.5": {12: mp.mpf("8.5e-5"), 13: mp.mpf("6.41e-5"), 14: mp.mpf("4.9e-5")},
        "slope_-4": {12: mp.mpf("8.8e-5"), 13: mp.mpf("6.41e-5"), 14: mp.mpf("4.8e-5")},
    }
    observed = {12: theta12, 13: theta13, 14: theta14}
    errors: Dict[str, mp.mpf] = {}
    for label, rows in targets.items():
        errors[label] = mp.sqrt(sum((mp.log(observed[k] / rows[k])) ** 2 for k in (12, 13, 14)) / 3)
    best = min(errors, key=errors.get)
    decaying = theta12 > theta13 > theta14
    if decaying:
        code = f"ROTATION_DECAYING({best})"
    else:
        code = "ROTATION_PERSISTENT"
    return {
        "theta_observed": observed,
        "target_errors_log_rms": errors,
        "best_slope": best,
        "decaying_order_12_gt_13_gt_14": decaying,
        "code": code,
    }


def load_saved_xi_vectors() -> List[mp.matrix]:
    data = load_json(OUT_DIR / "nconv_anchor_lambda_sq_13_N_120.json")
    cache = data.get("xi_m_y_cache", [])
    if len(cache) < 3:
        raise RuntimeError("saved xi cache requires three vectors")
    out: List[mp.matrix] = []
    for idx in range(3):
        v = mp.matrix(2 * N + 1, 1)
        for row in cache[idx]["xi_vector"]:
            v[int(row["n"]) + N] = mp.mpc(mpf(row["re"]), mpf(row["im"]))
        out.append(normalize_vec(v))
    return out


def inverse_iteration_eigenpairs(T: mp.matrix, starts: Sequence[mp.matrix], iterations: int = 2) -> List[Dict[str, Any]]:
    pairs: List[Dict[str, Any]] = []
    basis: List[mp.matrix] = []
    for idx, start in enumerate(starts, start=1):
        q = orthogonalize(start, basis)
        iteration_rows = []
        for it in range(iterations):
            y = mp.lu_solve(T, q)
            q = orthogonalize(y, basis)
            mu = mp.re(pilot.inner(q, T * q))
            residual_vec = T * q
            for i in range(residual_vec.rows):
                residual_vec[i] -= mu * q[i]
            iteration_rows.append({"iteration": it + 1, "mu": mu, "residual_norm": pilot.norm(residual_vec)})
        mu = mp.re(pilot.inner(q, T * q))
        residual_vec = T * q
        for i in range(residual_vec.rows):
            residual_vec[i] -= mu * q[i]
        residual = pilot.norm(residual_vec)
        basis.append(q)
        pairs.append({"index": idx, "mu": mu, "xi": q, "residual_norm": residual, "iterations": iteration_rows})
    return pairs


def project_residual(v: mp.matrix, basis: Sequence[mp.matrix]) -> mp.matrix:
    residual = pilot.copy_vec(v)
    for q in basis:
        coeff = pilot.inner(q, v)
        for i in range(residual.rows):
            residual[i] -= coeff * q[i]
    return residual


def deterministic_random_vec(size: int, seed: int = 20260704) -> mp.matrix:
    rng = random.Random(seed)
    v = mp.matrix(size, 1)
    for i in range(size):
        v[i] = mp.mpf(str(rng.uniform(-0.5, 0.5)))
    return normalize_vec(v)


def psd_judge(T: mp.matrix, xi: mp.matrix, packet_basis: Sequence[mp.matrix], threshold: mp.mpf) -> Dict[str, Any]:
    y = project_residual(xi, packet_basis)
    y_norm = pilot.norm(y)
    E_tail = mp.re(pilot.inner(y, T * y))
    c_star = E_tail / max(y_norm ** 2, mp.mpf("1e-300"))
    return {
        "y_norm": y_norm,
        "E_tail": E_tail,
        "c_star": c_star,
        "threshold": threshold,
        "pass": E_tail <= threshold,
    }


def vector_recert(T: mp.matrix, packet13: Dict[str, Any], rotation13: Dict[str, Any]) -> Dict[str, Any]:
    started = time.time()
    mp.mp.dps = DPS_RECERT
    saved_starts = load_saved_xi_vectors()
    pairs = inverse_iteration_eigenpairs(T, saved_starts, iterations=2)
    vectors = packet_vectors(packet13)
    projected, _dust_rows = parity_project(vectors)
    packet_basis, packet_q_stats = pilot.modified_gram_schmidt_mp(
        [projected["k1"], projected["k2_odd"], projected["k2_even"]],
        tol=mp.power(10, -min(70, max(30, mp.mp.dps // 3))),
    )
    G3 = block_from_basis(T, packet_basis)
    G3_vals, _ = eigvals_vecs_hermitian(G3)
    mu1 = pairs[0]["mu"]
    lambda3_G = G3_vals[-1]
    threshold = (mp.sqrt(max(mu1, mp.mpf("0"))) + mp.sqrt(max(lambda3_G, mp.mpf("0")))) ** 2
    fresh_judge = psd_judge(T, pairs[0]["xi"], packet_basis, threshold)

    planted = pairs[0]["xi"] + mp.mpf("1e-9") * deterministic_random_vec(pairs[0]["xi"].rows)
    planted = normalize_vec(planted)
    planted_judge = psd_judge(T, planted, packet_basis, threshold)
    planted_fires = not planted_judge["pass"]

    if not planted_fires:
        code = "PSD_JUDGE_SILENT_ON_PLANT"
        door = "JUDGE_BROKEN_STOP"
        pass_recert = False
    elif not fresh_judge["pass"]:
        code = "VECTOR_RECERT_FAILS"
        door = "PSD_JUDGE_FAILS_ON_FRESH_VECTOR"
        pass_recert = False
    else:
        code = "VECTOR_RECERT_PASS"
        pass_recert = True
        if fresh_judge["y_norm"] <= mp.mpf("1e-12"):
            door = "rotation_only"
        elif fresh_judge["y_norm"] < mp.mpf("2.6e-9") and fresh_judge["c_star"] <= threshold / max(fresh_judge["y_norm"] ** 2, mp.mpf("1e-300")):
            door = "extend_packet_next"
        else:
            door = "outside_registered_vector_fork"
    return {
        "dps": DPS_RECERT,
        "method": "inverse_iteration_with_saved_xi_starts_and_T_solve",
        "iterations_per_pair": 2,
        "eigenpairs": [
            {
                "index": p["index"],
                "mu": p["mu"],
                "residual_norm": p["residual_norm"],
                "iterations": p["iterations"],
            }
            for p in pairs
        ],
        "packet_basis_q_stats": packet_q_stats,
        "G3_eigenvalues": G3_vals,
        "lambda3_G": lambda3_G,
        "psd_threshold": threshold,
        "fresh_judge": fresh_judge,
        "planted_judge": planted_judge,
        "planted_fires": planted_fires,
        "code": code,
        "pass": pass_recert,
        "door": door,
        "elapsed_s": time.time() - started,
    }


def write_report(payload: Dict[str, Any]) -> None:
    trend = payload["PART_A_rotation_trend"]
    recert = payload["PART_B_vector_recert"]
    conv = payload["lambda1_convention_gap"]
    lines = [
        "# RotationTrend_and_VectorRecert_v1",
        "",
        "Route B diagnostic only. Not RH. No Phase 2.",
        "",
        "## Verdict",
        "",
        f"- status: `{payload['status']}`",
        f"- codes: `{payload['codes']}`",
        f"- door: `{payload['door']}`",
        "",
        "## Part A Rotation Trend",
        "",
        "| lambda_sq | theta | a1_raw | a2_raw | g12_raw | gamma | ground(raw 2x2) |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for lam in (12, 13, 14):
        row = payload["PART_A_points"][str(lam)]
        raw = row["raw_triple"]
        lines.append(
            f"| {lam} | `{fmt(row['gram_orthonormal']['theta_ground_angle'], 10)}` | `{fmt(raw['a1_raw'], 8)}` | `{fmt(raw['a2_raw'], 8)}` | `{fmt(raw['g12_raw'], 8)}` | `{fmt(raw['gram_gamma_raw'], 8)}` | `{fmt(raw['ordinary_raw_2x2_ground'], 8)}` |"
        )
    lines.extend(
        [
            "",
            f"- trend code: `{trend['code']}`",
            f"- best slope target: `{trend['best_slope']}`",
            f"- decaying order theta12 > theta13 > theta14: `{trend['decaying_order_12_gt_13_gt_14']}`",
            "",
            "## Lambda1 Convention Gap",
            "",
            f"- literal raw ordinary 2x2 ground at 13: `{fmt(conv['literal_raw_ordinary_2x2_ground_13'], 12)}`",
            f"- hybrid PacketTruth `a1_raw` with orthogonal `g12/a2` ground at 13: `{fmt(conv['hybrid_packettruth_a1raw_with_orth_g12_a2_ground_13'], 12)}`",
            f"- TPPG value: `{fmt(conv['TPPG_gram_orthonormal_parity_projected_lambda1'], 12)}`",
            f"- resolution: {conv['resolution']}",
            "",
            "## Part B Vector Recert",
            "",
            f"- method: `{recert['method']}`, dps `{recert['dps']}`",
            f"- code: `{recert['code']}`",
            f"- PSD threshold: `{fmt(recert['psd_threshold'], 8)}`",
            f"- fresh y: `{fmt(recert['fresh_judge']['y_norm'], 12)}`",
            f"- fresh E_tail: `{fmt(recert['fresh_judge']['E_tail'], 8)}`",
            f"- fresh c*_y: `{fmt(recert['fresh_judge']['c_star'], 8)}`",
            f"- fresh PSD pass: `{recert['fresh_judge']['pass']}`",
            f"- planted PSD fires: `{recert['planted_fires']}`",
            "",
            "| i | mu | residual |",
            "|---:|---:|---:|",
        ]
    )
    for p in recert["eigenpairs"]:
        lines.append(f"| {p['index']} | `{fmt(p['mu'], 12)}` | `{fmt(p['residual_norm'], 8)}` |")
    lines.extend(["", "## Stop", "", "Stop after report + handoff.", ""])
    REPORT.write_text("\n".join(lines), encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    trend = payload["PART_A_rotation_trend"]
    recert = payload["PART_B_vector_recert"]
    conv = payload["lambda1_convention_gap"]
    points = payload["PART_A_points"]
    lines = [
        "PROSHKA_ROUTE_REVIEW",
        "",
        "Gate:",
        "RotationTrend_and_VectorRecert_v1 / Route B TwoLevelSpectralLadder",
        "",
        "Codes:",
        str(payload["codes"]),
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. Phase 2 not run. No new lambda/N anchors. Q3 mainline not touched.",
        "",
        "Part A:",
        f"- theta12={fmt(points['12']['gram_orthonormal']['theta_ground_angle'], 10)}, theta13={fmt(points['13']['gram_orthonormal']['theta_ground_angle'], 10)}, theta14={fmt(points['14']['gram_orthonormal']['theta_ground_angle'], 10)}.",
        f"- trend={trend['code']} best={trend['best_slope']}.",
        f"- lambda1 convention resolved: literal raw ground={fmt(conv['literal_raw_ordinary_2x2_ground_13'], 8)}, hybrid expected ground={fmt(conv['hybrid_packettruth_a1raw_with_orth_g12_a2_ground_13'], 8)}, TPPG={fmt(conv['TPPG_gram_orthonormal_parity_projected_lambda1'], 8)}.",
        "",
        "Part B:",
        f"- recert code={recert['code']}; door={recert['door']}.",
        f"- fresh y={fmt(recert['fresh_judge']['y_norm'], 12)}, E_tail={fmt(recert['fresh_judge']['E_tail'], 8)}, c*_y={fmt(recert['fresh_judge']['c_star'], 8)}.",
        f"- PSD threshold={fmt(recert['psd_threshold'], 8)}, fresh pass={recert['fresh_judge']['pass']}, planted fires={recert['planted_fires']}.",
        "",
        "Question for Proshka:",
        "Accept this as recertifying the door state, or require a stricter shifted inverse iteration / full eigensolve before acting on the vector fork?",
        "",
        "Stop condition:",
        "Codex stops here after ROUTE_B_STATE.md update + handoff.",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "ROTATION_TREND_AND_VECTOR_RECERT_V1_COMPLETE",
            "last_verdict": payload["door"],
            "last_codes": payload["codes"],
            "next_gate": payload["next_gate"],
            "last_report": "rotation_trend_vector_recert_v1.md",
            "last_json": "out/rotation_trend_vector_recert_v1.json",
            "route_status": "NOT_RH_DIAGNOSTIC_ONLY",
            "phase2_run": False,
            "new_lambda_or_N_anchor_bought": False,
            "q3_main_touched": False,
        }
    )
    write_json(LOOP_STATE, state)


def update_route_state(payload: Dict[str, Any]) -> None:
    trend = payload["PART_A_rotation_trend"]
    recert = payload["PART_B_vector_recert"]
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    if ROUTE_STATE.exists():
        old = ROUTE_STATE.read_text(encoding="utf-8")
    else:
        old = "# ROUTE_B_STATE\n\n## History\n"
    history_line = (
        f"- {now}: RotationTrend_and_VectorRecert_v1 -> "
        f"{', '.join(payload['codes'])}; door={payload['door']}; "
        f"theta_trend={trend['code']}; vector={recert['code']}."
    )
    body = [
        "# ROUTE_B_STATE",
        "",
        "## ДВЕРЬ",
        "",
        f"`{payload['door']}`",
        "",
        "## СЛЕДУЮЩИЙ ШАГ",
        "",
        payload["next_step_text"],
        "",
        "## CURRENT_CODES",
        "",
        ", ".join(f"`{code}`" for code in payload["codes"]),
        "",
        "## History",
        "",
    ]
    old_history = []
    if "## History" in old:
        old_history = [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]
    body.extend(old_history)
    body.append(history_line)
    ROUTE_STATE.write_text("\n".join(body) + "\n", encoding="utf-8")


def main() -> None:
    started = time.time()
    packets: Dict[int, Dict[str, Any]] = {}
    points: Dict[int, Dict[str, Any]] = {}
    for lam_sq in (12, 13, 14):
        packets[lam_sq] = high_precision_packet_run(lam_sq, N)
        T, dps_T = build_T(lam_sq)
        points[lam_sq] = rotation_point(lam_sq, packets[lam_sq], T, dps_T)

    trend = classify_rotation(points)
    packet_truth = load_json(OUT_DIR / "packet_truth_pull_v1.json")
    conv = {
        "literal_raw_ordinary_2x2_ground_13": points[13]["raw_triple"]["ordinary_raw_2x2_ground"],
        "hybrid_packettruth_a1raw_with_orth_g12_a2_ground_13": raw_2x2_ground(
            points[13]["raw_triple"]["a1_raw"],
            mp.re(parse_mpc(packet_truth["T0_T2_main"]["G_even_internals"]["g22"])),
            parse_mpc(packet_truth["T0_T2_main"]["G_even_internals"]["g12"]),
        )[0][0],
        "TPPG_gram_orthonormal_parity_projected_lambda1": mpf(packet_truth["T0_T2_main"]["G_even_internals"]["lambda1"]),
        "resolution": "literal raw ordinary 2x2 uses raw k1/k2e/gamma-free entries; the earlier expected ~4.545e-59 is the hybrid a1_raw with PacketTruth orthogonal g12/a2 convention; TPPG 3.8922e-59 is the fully Gram-orthonormal parity-projected G_even ground.",
    }
    T250, _ = build_T(13, dps_override=DPS_RECERT)
    recert = vector_recert(T250, packets[13], points[13])

    codes = [trend["code"], "LAMBDA1_CONVENTION_RESOLVED", recert["code"]]
    if recert["code"] == "PSD_JUDGE_SILENT_ON_PLANT":
        status = "complete_with_registered_failure"
        door = "JUDGE_BROKEN_STOP"
        next_step = "Stop: PSD judge did not fire on planted vector corruption."
        next_gate = "WAIT_FOR_REVIEW"
    elif recert["code"] != "VECTOR_RECERT_PASS":
        status = "complete_with_registered_failure"
        door = recert["door"]
        next_step = "Review vector recert failure before extending packets or running operator-static Schur."
        next_gate = "WAIT_FOR_PROSHKA_REVIEW"
    elif recert["door"] == "rotation_only":
        status = "complete"
        door = "ROTATION_ONLY"
        next_step = "Proceed to rotation model / eps-lambda trend; old Y codes retired."
        next_gate = "RotationModel_next"
    elif recert["door"] == "extend_packet_next":
        status = "complete"
        door = "EXTEND_PACKET_NEXT"
        next_step = "Extend packet model next; old Y codes retired."
        next_gate = "ExtendPacketModel_next"
    else:
        status = "complete_with_registered_failure"
        door = recert["door"]
        next_step = "Vector fork landed outside registered bands; ask Proshka before continuing."
        next_gate = "WAIT_FOR_PROSHKA_REVIEW"

    payload: Dict[str, Any] = {
        "gate": "RotationTrend_and_VectorRecert_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": status,
        "codes": codes,
        "door": door,
        "next_step_text": next_step,
        "next_gate": next_gate,
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "new_lambdas": False,
        "q3_main_touched": False,
        "elapsed_s": time.time() - started,
        "PART_A_points": {str(k): v for k, v in points.items()},
        "PART_A_rotation_trend": trend,
        "lambda1_convention_gap": conv,
        "PART_B_vector_recert": recert,
    }
    write_json(JSON_OUT, payload)
    write_report(payload)
    write_handoff(payload)
    update_loop_state(payload)
    update_route_state(payload)
    print(f"Wrote {JSON_OUT}")
    print(f"Wrote {REPORT}")
    print(f"codes={codes} door={door}")


if __name__ == "__main__":
    main()
