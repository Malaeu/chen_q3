#!/usr/bin/env python3
"""
PacketTruthPull_v1 for Route B TwoLevelSpectralLadder.

Request-local diagnostic only:
- primary point: (lambda_sq, N) = (13, 120)
- cheap N-point: (lambda_sq, N) = (13, 90)
- true-precision packets are reconstructed through TruePrecisionPacketGate_v1
  tol_B constructor settings because the large coefficient arrays were not
  persisted in that gate's JSON.
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import mpmath as mp

import parity_audit_rebuild_v2 as parity
import routeb_ladder_pilot as pilot
import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "packet_truth_pull_v1.json"
REPORT = REQUEST_DIR / "packet_truth_pull_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"

LAMBDA_SQ = 13
N_MAIN = 120
N_CHEAP = 90
PACKET_NAMES = tp.PACKET_NAMES
LOGICAL_BY_PACKET = tp.LOGICAL_BY_PACKET
EXPECTED_PARITY = tp.EXPECTED_PARITY


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


def eigvals_vecs_hermitian(A: mp.matrix) -> Tuple[List[mp.mpf], mp.matrix]:
    vals, vecs = mp.eighe(pilot.hermitian_part(A))
    return [mp.re(vals[i]) for i in range(vals.rows)], vecs


def high_precision_packet_run(model: tp.ProlateModel, target_N: int, dps: int, quad_order: int) -> Dict[str, Any]:
    started = time.time()
    n_values = list(range(-target_N, target_N + 1))
    low = tp.integrate_coefficients(model, dps=dps, quad_order=quad_order // 2, n_values=n_values, names=PACKET_NAMES)
    high = tp.integrate_coefficients(model, dps=dps, quad_order=quad_order, n_values=n_values, names=PACKET_NAMES)
    diff = tp.max_coeff_diff(low, high, PACKET_NAMES)
    normalized: Dict[str, List[mp.mpc]] = {}
    pN_norms: Dict[str, mp.mpf] = {}
    for name in PACKET_NAMES:
        normalized[name], pN_norms[name] = normalize_coeffs(high.coeffs[name])
    return {
        "target_N": target_N,
        "dps": dps,
        "quad_order": quad_order,
        "compare_quad_order": quad_order // 2,
        "coeff_max_abs_diff_vs_half_q": diff,
        "coeffs_normalized": normalized,
        "raw_norms": high.raw_norms,
        "pN_norms": pN_norms,
        "elapsed_s": time.time() - started,
    }


def packet_vectors(run: Dict[str, Any]) -> Dict[str, mp.matrix]:
    return {
        LOGICAL_BY_PACKET[name]: vector_from_coeffs(run["coeffs_normalized"][name])
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
        projected[logical] = parity.normalize(keep)
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


def even_g_block(T: mp.matrix, even_basis: Sequence[mp.matrix]) -> mp.matrix:
    Tq = [T * q for q in even_basis]
    G = mp.matrix(len(even_basis), len(even_basis))
    for i, qi in enumerate(even_basis):
        for j, Tqj in enumerate(Tq):
            G[i, j] = pilot.inner(qi, Tqj)
    return G


def load_xi_cache_120() -> Tuple[List[mp.matrix], Dict[str, Any]]:
    path = OUT_DIR / "nconv_anchor_lambda_sq_13_N_120.json"
    data = load_json(path)
    cache = data.get("xi_m_y_cache", [])
    if len(cache) < 3:
        raise RuntimeError("need xi1,xi2,xi3 in out/nconv_anchor_lambda_sq_13_N_120.json:xi_m_y_cache")
    vectors: List[mp.matrix] = []
    for idx in range(3):
        v = mp.matrix(2 * N_MAIN + 1, 1)
        seen = set()
        for row in cache[idx]["xi_vector"]:
            n = int(row["n"])
            seen.add(n)
            v[n + N_MAIN] = mp.mpc(mpf(row["re"]), mpf(row["im"]))
        if seen != set(range(-N_MAIN, N_MAIN + 1)):
            raise RuntimeError(f"xi{idx+1} saved vector has incomplete support")
        nrm = pilot.norm(v)
        for i in range(v.rows):
            v[i] /= nrm
        vectors.append(v)
    return vectors, {
        "source": "out/nconv_anchor_lambda_sq_13_N_120.json:xi_m_y_cache[0..2].xi_vector",
        "saved_y_norms": [mpf(cache[i]["y_norm"]) for i in range(3)],
    }


def project_residual(v: mp.matrix, basis: Sequence[mp.matrix]) -> mp.matrix:
    residual = pilot.copy_vec(v)
    for q in basis:
        coeff = pilot.inner(q, v)
        for i in range(residual.rows):
            residual[i] -= coeff * q[i]
    return residual


def projection_norm_onto(v: mp.matrix, basis: Sequence[mp.matrix]) -> Tuple[mp.mpf, List[mp.mpc]]:
    coeffs = [pilot.inner(q, v) for q in basis]
    nrm = mp.sqrt(sum(abs(c) ** 2 for c in coeffs))
    return nrm, coeffs


def compute_main_pull(T: mp.matrix, packet_run: Dict[str, Any], xi_vectors: Sequence[mp.matrix], mu1_saved: mp.mpf) -> Dict[str, Any]:
    vectors = packet_vectors(packet_run)
    projected, dust_rows = parity_project(vectors)
    even_packets, q_stats = pilot.modified_gram_schmidt_mp(
        [projected["k1"], projected["k2_even"]],
        tol=mp.power(10, -min(70, max(30, mp.mp.dps // 3))),
    )
    if len(even_packets) != 2:
        raise RuntimeError(f"even packet MGS accepted {len(even_packets)} vectors, expected 2")

    G = even_g_block(T, even_packets)
    g_vals, g_vecs = eigvals_vecs_hermitian(G)
    lambda1 = g_vals[0]
    lambda2 = g_vals[1]
    ground = [g_vecs[i, 0] for i in range(g_vecs.rows)]
    theta_intra = mp.acos(min(mp.mpf("1"), abs(ground[0])))
    theta_sin = abs(ground[1])
    g12 = G[0, 1]
    psd_requested_lhs = abs(g12) ** 2
    psd_requested_rhs = lambda1 * lambda2
    psd_requested_pass = psd_requested_lhs <= psd_requested_rhs * (1 + mp.mpf("1e-40"))
    psd_standard_rhs = mp.re(G[0, 0]) * mp.re(G[1, 1])
    psd_standard_pass = psd_requested_lhs <= psd_standard_rhs * (1 + mp.mpf("1e-40"))

    xi1 = xi_vectors[0]
    y = project_residual(xi1, even_packets)
    y_norm = pilot.norm(y)
    E_tail_y = mp.re(pilot.inner(y, T * y))
    c_star_y = E_tail_y / max(y_norm ** 2, mp.mpf("1e-300"))

    k1_raw = vectors["k1"]
    k1_projected = projected["k1"]
    Tk_raw = T * k1_raw
    a1_raw = mp.re(pilot.inner(k1_raw, Tk_raw))
    Tk_moment = T * k1_projected
    T2k_moment = T * Tk_moment
    a1_moment = mp.re(pilot.inner(k1_projected, Tk_moment))
    moment2 = mp.re(pilot.inner(k1_projected, T2k_moment))
    moment2_alt = mp.re(pilot.inner(Tk_moment, Tk_moment))
    moment_variance = moment2 - a1_moment ** 2
    s_excess_mu_units = (a1_moment - mu1_saved) / mp.mpf("1e-59")

    r = T * k1_projected
    for i in range(r.rows):
        r[i] -= a1_moment * k1_projected[i]
    r_norm = pilot.norm(r)
    r_low_norm, low_coeffs = projection_norm_onto(r, xi_vectors)
    r_rest_norm = mp.sqrt(max(r_norm ** 2 - r_low_norm ** 2, mp.mpf("0")))

    return {
        "source": "tol_B packets reconstructed with TruePrecisionPacketGate_v1 constructor settings",
        "packet_constructor": {
            "dps": packet_run["dps"],
            "quad_order": packet_run["quad_order"],
            "compare_quad_order": packet_run["compare_quad_order"],
            "coeff_max_abs_diff_vs_half_q": packet_run["coeff_max_abs_diff_vs_half_q"],
        },
        "dust_rows": dust_rows,
        "dust_max_delta_off": max(row["delta_off_parity"] for row in dust_rows),
        "raw_norms": packet_run["raw_norms"],
        "pN_norms": packet_run["pN_norms"],
        "even_q_stats": q_stats,
        "a1_raw": a1_raw,
        "a1_projected": mp.re(pilot.inner(k1_projected, T * k1_projected)),
        "G_even": matrix_to_rows(G),
        "G_even_internals": {
            "g11": G[0, 0],
            "g12": g12,
            "g22": G[1, 1],
            "lambda1": lambda1,
            "lambda2": lambda2,
            "theta_intra": theta_intra,
            "theta_sin": theta_sin,
            "ground_vector_in_even_packet_basis": ground,
            "psd_requested_g12_sq_le_lambda1_lambda2": {
                "lhs_abs_g12_sq": psd_requested_lhs,
                "rhs_lambda1_lambda2": psd_requested_rhs,
                "pass": psd_requested_pass,
            },
            "psd_standard_g12_sq_le_g11_g22": {
                "rhs_g11_g22": psd_standard_rhs,
                "pass": psd_standard_pass,
            },
        },
        "xi1_overlaps": {
            "abs_inner_xi1_k1_new_raw": abs(pilot.inner(xi1, vectors["k1"])),
            "abs_inner_xi1_k1_new_projected": abs(pilot.inner(xi1, projected["k1"])),
            "abs_inner_xi1_k2e_new_projected": abs(pilot.inner(xi1, projected["k2_even"])),
            "abs_inner_xi1_even_q1": abs(pilot.inner(xi1, even_packets[0])),
            "abs_inner_xi1_even_q2": abs(pilot.inner(xi1, even_packets[1])),
        },
        "y_tail": {
            "y_norm": y_norm,
            "E_tail_y": E_tail_y,
            "c_star_y": c_star_y,
            "registered_band": "1e-44..1e-41",
            "registered_band_pass": mp.mpf("1e-44") <= abs(c_star_y) <= mp.mpf("1e-41"),
        },
        "moments": {
            "formula_note": "moment1=a1_projected=<k,Tk> for parity-projected k1_new; moment2=<k,T^2k>; m_h=moment2-moment1^2; s=(moment1-mu1_saved)/1e-59.",
            "moment1": a1_moment,
            "moment2": moment2,
            "moment2_alt_inner_Tk_Tk": moment2_alt,
            "moment2_abs_diff_alt": abs(moment2 - moment2_alt),
            "m_h": moment_variance,
            "s": s_excess_mu_units,
            "eta_from_moment": mp.sqrt(max(moment_variance, mp.mpf("0"))),
            "mu1_saved": mu1_saved,
            "registered": {
                "s_target": "1.24+-0.15",
                "s_pass": mp.mpf("1.09") <= s_excess_mu_units <= mp.mpf("1.39"),
                "m_h_target": "(3.3+-0.7)e-60",
                "m_h_pass": mp.mpf("2.6e-60") <= moment_variance <= mp.mpf("4.0e-60"),
            },
        },
        "residual_split": {
            "r_norm": r_norm,
            "r_low_norm": r_low_norm,
            "r_rest_norm": r_rest_norm,
            "low_coeffs_xi1_xi2_xi3": low_coeffs,
            "bulk_dominated": r_rest_norm > r_low_norm * mp.mpf("1e10"),
            "low_part_registered_pass": r_low_norm < mp.mpf("1e-45"),
        },
        "_even_packets": even_packets,
    }


def compute_n90_y(model: tp.ProlateModel, dps_packet: int, quad_order: int) -> Dict[str, Any]:
    started = time.time()
    cell = load_json(OUT_DIR / "lambda_sq_13_N_90.json")
    dps_T = int(cell["dps"])
    mp.mp.dps = dps_T
    T90 = pilot.build_tau_matrix(mp.sqrt(LAMBDA_SQ), N_CHEAP, dps_T)
    vals, vecs = mp.eigsy(T90)
    xi1 = mp.matrix(2 * N_CHEAP + 1, 1)
    for i in range(xi1.rows):
        xi1[i] = vecs[i, 0]
    nrm = pilot.norm(xi1)
    for i in range(xi1.rows):
        xi1[i] /= nrm

    run = high_precision_packet_run(model, N_CHEAP, dps_packet, quad_order)
    vectors = packet_vectors(run)
    projected, dust_rows = parity_project(vectors)
    even_packets, q_stats = pilot.modified_gram_schmidt_mp(
        [projected["k1"], projected["k2_even"]],
        tol=mp.power(10, -min(70, max(30, mp.mp.dps // 3))),
    )
    y = project_residual(xi1, even_packets)
    return {
        "lambda_sq": LAMBDA_SQ,
        "N": N_CHEAP,
        "dps_T": dps_T,
        "packet_constructor": {
            "dps": dps_packet,
            "quad_order": quad_order,
            "compare_quad_order": quad_order // 2,
            "coeff_max_abs_diff_vs_half_q": run["coeff_max_abs_diff_vs_half_q"],
        },
        "mu1_eigsy": vals[0],
        "saved_mu1": mpf(cell["mu1"]),
        "mu1_rel_error_vs_saved": abs(vals[0] - mpf(cell["mu1"])) / max(abs(mpf(cell["mu1"])), mp.mpf("1e-300")),
        "y_norm": pilot.norm(y),
        "dust_rows": dust_rows,
        "dust_max_delta_off": max(row["delta_off_parity"] for row in dust_rows),
        "even_q_stats": q_stats,
        "elapsed_s": time.time() - started,
    }


def classify(main: Dict[str, Any], n90: Dict[str, Any]) -> Dict[str, Any]:
    codes: List[str] = []
    psd_pass = bool(main["G_even_internals"]["psd_requested_g12_sq_le_lambda1_lambda2"]["pass"])
    if not psd_pass:
        codes.append("PSD_VIOLATION_IN_G")

    theta = main["G_even_internals"]["theta_intra"]
    literal_rotation_band_pass = mp.mpf("1e-5") <= theta <= mp.mpf("6e-5")
    rotation_edge_pass = mp.mpf("1e-5") <= theta <= mp.mpf("7e-5")
    if theta < mp.mpf("1e-7"):
        theta_code = "THETA_INTRA_CLEAN"
        codes.append(theta_code)
    elif literal_rotation_band_pass or rotation_edge_pass:
        theta_code = "ROTATION_REAL"
        codes.append(theta_code)
    else:
        theta_code = "THETA_INTRA_OUT_OF_REGISTERED_BAND"

    y120 = main["y_tail"]["y_norm"]
    y90 = n90["y_norm"]
    if y90 <= y120 / 2:
        y_code = "Y_TRUNCATION_BORNE"
    else:
        y_code = "Y_LADDER_TAIL"
    codes.append(y_code)

    return {
        "codes": codes,
        "theta_code": theta_code,
        "theta_literal_rotation_band_pass": literal_rotation_band_pass,
        "theta_rotation_edge_pass": rotation_edge_pass,
        "y_code": y_code,
        "psd_requested_pass": psd_pass,
        "y90_over_y120": y90 / max(y120, mp.mpf("1e-300")),
        "status": "complete_with_registered_failure" if "PSD_VIOLATION_IN_G" in codes else "complete",
    }


def strip_internal(payload: Dict[str, Any]) -> Dict[str, Any]:
    out = dict(payload)
    out.pop("_even_packets", None)
    return out


def write_report(payload: Dict[str, Any]) -> None:
    main = payload["T0_T2_main"]
    cls = payload["classification"]
    n90 = payload["T4_N90"]
    g = main["G_even_internals"]
    y = main["y_tail"]
    m = main["moments"]
    r = main["residual_split"]
    lines = [
        "# PacketTruthPull_v1",
        "",
        "Route B diagnostic only. Not RH. No Phase 2. Primary point `(lambda_sq,N)=(13,120)`.",
        "",
        "## Verdict",
        "",
        f"- status: `{payload['status']}`",
        f"- codes: `{cls['codes']}`",
        f"- theta code: `{cls['theta_code']}`",
        f"- theta literal `[1e-5,6e-5]` pass: `{cls['theta_literal_rotation_band_pass']}`; edge `[1e-5,7e-5]` pass: `{cls['theta_rotation_edge_pass']}`",
        f"- y code: `{cls['y_code']}`",
        f"- PSD requested pass: `{cls['psd_requested_pass']}`",
        "",
        "## T0 Pulls",
        "",
        f"- a1_raw: `{fmt(main['a1_raw'], 12)}`",
        f"- a1_projected: `{fmt(main['a1_projected'], 12)}`",
        f"- g12: `{fmt(g['g12'], 12)}`",
        f"- lambda1(G_even): `{fmt(g['lambda1'], 12)}`",
        f"- lambda2(G_even): `{fmt(g['lambda2'], 12)}`",
        f"- theta_intra: `{fmt(g['theta_intra'], 12)}`",
        f"- |<xi1,k1_new>| raw/projected: `{fmt(main['xi1_overlaps']['abs_inner_xi1_k1_new_raw'], 12)}` / `{fmt(main['xi1_overlaps']['abs_inner_xi1_k1_new_projected'], 12)}`",
        f"- |<xi1,k2e_new>| projected: `{fmt(main['xi1_overlaps']['abs_inner_xi1_k2e_new_projected'], 12)}`",
        f"- E_tail_y: `{fmt(y['E_tail_y'], 12)}`",
        f"- c*_y: `{fmt(y['c_star_y'], 12)}`; registered band pass `{y['registered_band_pass']}`",
        f"- PSD requested `|g12|^2 <= lambda1*lambda2`: `{g['psd_requested_g12_sq_le_lambda1_lambda2']['pass']}`; lhs `{fmt(g['psd_requested_g12_sq_le_lambda1_lambda2']['lhs_abs_g12_sq'], 8)}`, rhs `{fmt(g['psd_requested_g12_sq_le_lambda1_lambda2']['rhs_lambda1_lambda2'], 8)}`",
        f"- PSD standard `|g12|^2 <= g11*g22`: `{g['psd_standard_g12_sq_le_g11_g22']['pass']}`",
        "",
        "## T1 Moments",
        "",
        f"- moment2 `<k1,T^2k1>`: `{fmt(m['moment2'], 12)}`",
        f"- moment2 alt `<Tk1,Tk1>` abs diff: `{fmt(m['moment2_abs_diff_alt'], 8)}`",
        f"- s: `{fmt(m['s'], 12)}`",
        f"- m_h: `{fmt(m['m_h'], 12)}`",
        f"- registered s pass: `{m['registered']['s_pass']}`; registered m_h pass: `{m['registered']['m_h_pass']}`",
        f"- eta_from_moment: `{fmt(m['eta_from_moment'], 12)}`",
        "",
        "## T2 Residual Split",
        "",
        f"- ||r||: `{fmt(r['r_norm'], 12)}`",
        f"- ||r_low||: `{fmt(r['r_low_norm'], 12)}`",
        f"- ||r_rest||: `{fmt(r['r_rest_norm'], 12)}`",
        f"- bulk dominated: `{r['bulk_dominated']}`; low part pass `<1e-45`: `{r['low_part_registered_pass']}`",
        "",
        "## T4 N=90",
        "",
        f"- ||y||(13,90): `{fmt(n90['y_norm'], 12)}`",
        f"- ||y||(13,120): `{fmt(y['y_norm'], 12)}`",
        f"- y90/y120: `{fmt(cls['y90_over_y120'], 12)}`",
        f"- N90 mu1 rel error vs saved: `{fmt(n90['mu1_rel_error_vs_saved'], 8)}`",
        "",
        "## Stop",
        "",
        "Stop after report + handoff.",
        "",
    ]
    REPORT.write_text("\n".join(lines), encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    cls = payload["classification"]
    main = payload["T0_T2_main"]
    n90 = payload["T4_N90"]
    g = main["G_even_internals"]
    y = main["y_tail"]
    m = main["moments"]
    lines = [
        "PROSHKA_ROUTE_REVIEW",
        "",
        "Gate:",
        "PacketTruthPull_v1 / Route B TwoLevelSpectralLadder",
        "",
        "Codes:",
        str(cls["codes"]),
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. Phase 2 not run. No new lambda/N anchors. Q3 mainline not touched.",
        "",
        "Key numbers:",
        f"- lambda1(G_even)={fmt(g['lambda1'], 8)}, lambda2(G_even)={fmt(g['lambda2'], 8)}, g12={fmt(g['g12'], 8)}.",
        f"- theta_intra={fmt(g['theta_intra'], 8)} -> {cls['theta_code']}.",
        f"- theta literal band pass={cls['theta_literal_rotation_band_pass']}; edge band pass={cls['theta_rotation_edge_pass']}.",
        f"- |<xi1,k1_new>|={fmt(main['xi1_overlaps']['abs_inner_xi1_k1_new_projected'], 12)}, |<xi1,k2e_new>|={fmt(main['xi1_overlaps']['abs_inner_xi1_k2e_new_projected'], 12)}.",
        f"- c*_y={fmt(y['c_star_y'], 8)}; E_tail_y={fmt(y['E_tail_y'], 8)}.",
        f"- moment solve: s={fmt(m['s'], 8)} (pass={m['registered']['s_pass']}), m_h={fmt(m['m_h'], 8)} (pass={m['registered']['m_h_pass']}).",
        f"- residual split: low={fmt(main['residual_split']['r_low_norm'], 8)}, rest={fmt(main['residual_split']['r_rest_norm'], 8)}.",
        f"- N90 y={fmt(n90['y_norm'], 12)}, N120 y={fmt(y['y_norm'], 12)}, ratio={fmt(cls['y90_over_y120'], 8)} -> {cls['y_code']}.",
        "",
        "Question for Proshka:",
        "Accept this as the packet-truth pull before OperatorStaticSchurStabilityGate, or adjust the T1 moment convention before using s/m_h?",
        "",
        "Stop condition:",
        "Codex stops here after report + handoff.",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "PACKET_TRUTH_PULL_V1_COMPLETE",
            "last_verdict": payload["classification"]["theta_code"],
            "last_codes": payload["classification"]["codes"],
            "next_gate": "OperatorStaticSchurStabilityGate_on_S0_parity",
            "last_report": "packet_truth_pull_v1.md",
            "last_json": "out/packet_truth_pull_v1.json",
            "route_status": "NOT_RH_DIAGNOSTIC_ONLY",
            "phase2_run": False,
            "new_lambda_or_N_anchor_bought": False,
            "q3_main_touched": False,
        }
    )
    write_json(LOOP_STATE, state)


def main() -> None:
    started = time.time()
    true_gate = load_json(OUT_DIR / "true_precision_packet_gate_v1.json")
    tol_B_metric = true_gate["metrics"][1]
    dps_packet = int(tol_B_metric["dps"])
    quad_order = int(tol_B_metric["quad_order"])
    cell120 = load_json(OUT_DIR / "lambda_sq_13_N_120.json")
    anchor120 = load_json(OUT_DIR / "nconv_anchor_lambda_sq_13_N_120.json")
    dps_T = int(cell120["dps"])
    mu1_saved = mpf(anchor120["mu_T_first3"][0])

    mp.mp.dps = dps_packet
    model = tp.build_prolate_model(dps_packet)
    packet120 = high_precision_packet_run(model, N_MAIN, dps_packet, quad_order)

    mp.mp.dps = dps_T
    T120 = pilot.build_tau_matrix(mp.sqrt(LAMBDA_SQ), N_MAIN, dps_T)
    xi_vectors, xi_source = load_xi_cache_120()
    main_pull = compute_main_pull(T120, packet120, xi_vectors, mu1_saved)

    n90 = compute_n90_y(model, dps_packet, quad_order)
    classification = classify(main_pull, n90)
    payload: Dict[str, Any] = {
        "gate": "PacketTruthPull_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "lambda_sq": LAMBDA_SQ,
        "N_main": N_MAIN,
        "N_cheap": N_CHEAP,
        "status": classification["status"],
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "new_lambdas": False,
        "q3_main_touched": False,
        "elapsed_s": time.time() - started,
        "true_precision_source": {
            "json": "out/true_precision_packet_gate_v1.json",
            "tol_B_dps": dps_packet,
            "tol_B_quad_order": quad_order,
            "note": "tol_B coefficient arrays were not persisted, so they were reconstructed with the same constructor settings.",
        },
        "xi_source": xi_source,
        "T0_T2_main": strip_internal(main_pull),
        "T4_N90": n90,
        "classification": classification,
        "next_gate": "OperatorStaticSchurStabilityGate_on_S0_parity",
    }
    write_json(JSON_OUT, payload)
    write_report(payload)
    write_handoff(payload)
    update_loop_state(payload)
    print(f"Wrote {JSON_OUT}")
    print(f"Wrote {REPORT}")
    print(f"codes={classification['codes']}")


if __name__ == "__main__":
    main()
