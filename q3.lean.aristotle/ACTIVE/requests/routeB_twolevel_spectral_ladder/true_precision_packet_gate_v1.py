#!/usr/bin/env python3
"""
TruePrecisionPacketGate_v1 for Route B TwoLevelSpectralLadder.

Request-local diagnostic only:
- one point: (lambda_sq, N) = (13, 120)
- no Phase 2, no new lambda/N anchors, no RH claim
- T is rebuilt through the same deterministic routeb_ladder_pilot path
- packet coefficients <E(f), V_n> are rebuilt in mpmath with breakpoint
  splitting at u=lambda/m.
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import mpmath as mp

import parity_audit_rebuild_v2 as parity
import routeb_ladder_pilot as pilot


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "true_precision_packet_gate_v1.json"
REPORT = REQUEST_DIR / "true_precision_packet_gate_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"

LAMBDA_SQ = 13
N = 120
MAX_DEGREE = 180
TOL_A = mp.mpf("1e-24")
TOL_B = mp.mpf("1e-30")
TOL_A_LABEL = "1e-24"
TOL_B_LABEL = "1e-30"
RUN_SPECS = [
    {"label": "tol_A", "tol": TOL_A, "tol_label": TOL_A_LABEL, "dps": 80, "q_start": 64, "q_max": 384},
    {"label": "tol_B", "tol": TOL_B, "tol_label": TOL_B_LABEL, "dps": 110, "q_start": 96, "q_max": 512},
]
PACKET_NAMES = ["g04", "g26", "g048perp"]
LOGICAL_BY_PACKET = {"g04": "k1", "g26": "k2_odd", "g048perp": "k2_even"}
EXPECTED_PARITY = {"k1": "even", "k2_odd": "odd", "k2_even": "even"}


@dataclass
class ProlateModel:
    dps: int
    lam: mp.mpf
    degrees: List[int]
    eigenvalues: List[mp.mpf]
    scaled_coeffs: Dict[str, List[mp.mpf]]
    integrals: Dict[int, mp.mpf]
    combo_coeffs: Dict[str, List[mp.mpf]]


@dataclass
class IntegralResult:
    dps: int
    quad_order: int
    coeffs: Dict[str, List[mp.mpc]]
    raw_norms: Dict[str, mp.mpf]
    intervals: List[Dict[str, Any]]
    planted_observed_contribution: Optional[mp.mpf] = None


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


def eigvals_hermitian(A: mp.matrix) -> List[mp.mpf]:
    vals, _ = mp.eighe(pilot.hermitian_part(A))
    return [mp.re(vals[i]) for i in range(vals.rows)]


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


def normalize_real_combo(coefs: Sequence[mp.mpf]) -> List[mp.mpf]:
    nrm = mp.sqrt(sum(c * c for c in coefs))
    if nrm == 0:
        raise RuntimeError("zero prolate combo norm")
    return [c / nrm for c in coefs]


def cross3(a: Sequence[mp.mpf], b: Sequence[mp.mpf]) -> List[mp.mpf]:
    return [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    ]


def build_prolate_model(dps: int) -> ProlateModel:
    mp.mp.dps = dps
    lam = mp.sqrt(LAMBDA_SQ)
    degrees = list(range(0, MAX_DEGREE + 1, 2))
    c = 2 * mp.pi * LAMBDA_SQ
    X2 = legendre_x2_matrix_mp(degrees)
    A = mp.matrix(len(degrees), len(degrees))
    for i, k in enumerate(degrees):
        A[i, i] = k * (k + 1)
    A += c * c * X2
    vals, vecs = mp.eigsy((A + A.T) / 2)

    h: Dict[int, List[mp.mpf]] = {}
    integrals: Dict[int, mp.mpf] = {}
    for which, col in zip((0, 2, 4, 6, 8), range(5)):
        v = column(vecs, col)
        # Fix arbitrary eigenvector sign for cross-dps stability.
        if v[0] < 0:
            v = [-x for x in v]
        h[which] = v
        integrals[which] = v[0] * mp.sqrt(2 * lam)

    g04_c = normalize_real_combo([integrals[4], -integrals[0]])
    g26_c = normalize_real_combo([integrals[6], -integrals[2]])
    g048_c = normalize_real_combo(cross3([integrals[0], integrals[4], integrals[8]], [g04_c[0], g04_c[1], mp.mpf("0")]))

    combo_coeffs_by_h = {
        "g04": {0: g04_c[0], 4: g04_c[1]},
        "g26": {2: g26_c[0], 6: g26_c[1]},
        "g048perp": {0: g048_c[0], 4: g048_c[1], 8: g048_c[2]},
    }

    scaled_coeffs: Dict[str, List[mp.mpf]] = {}
    combo_coeffs: Dict[str, List[mp.mpf]] = {}
    for name, h_combo in combo_coeffs_by_h.items():
        leg = [mp.mpf("0") for _ in degrees]
        for which, scale in h_combo.items():
            for i, val in enumerate(h[which]):
                leg[i] += scale * val
        combo_coeffs[name] = leg
        scaled_coeffs[name] = [
            leg_i * mp.sqrt(mp.mpf(2 * deg + 1) / (2 * lam))
            for leg_i, deg in zip(leg, degrees)
        ]

    return ProlateModel(
        dps=dps,
        lam=lam,
        degrees=degrees,
        eigenvalues=[mp.re(vals[i]) for i in range(vals.rows)],
        scaled_coeffs=scaled_coeffs,
        integrals=integrals,
        combo_coeffs={
            "g04": g04_c,
            "g26": g26_c,
            "g048perp": g048_c,
        },
    )


def eval_all_g(model: ProlateModel, t: mp.mpf) -> Dict[str, mp.mpf]:
    max_degree = model.degrees[-1]
    out = {name: mp.mpf("0") for name in PACKET_NAMES}
    p_prev = mp.mpf("1")
    for name in PACKET_NAMES:
        out[name] += model.scaled_coeffs[name][0] * p_prev
    if max_degree == 0:
        return out
    p_curr = t
    degree_index = 1
    for k in range(1, max_degree):
        p_next = ((2 * k + 1) * t * p_curr - k * p_prev) / (k + 1)
        p_prev, p_curr = p_curr, p_next
        deg = k + 1
        if deg % 2 == 0:
            for name in PACKET_NAMES:
                out[name] += model.scaled_coeffs[name][degree_index] * p_curr
            degree_index += 1
    return out


def split_intervals() -> List[Dict[str, Any]]:
    L = mp.log(LAMBDA_SQ)
    points = [mp.log(mp.mpf(LAMBDA_SQ) / m) for m in range(LAMBDA_SQ, 0, -1)]
    intervals: List[Dict[str, Any]] = []
    for a, b in zip(points, points[1:]):
        if b <= a:
            continue
        mid = (a + b) / 2
        mmax = int(mp.floor(mp.mpf(LAMBDA_SQ) / mp.e**mid))
        intervals.append({"a": a, "b": b, "mmax": mmax})
    if not intervals or abs(intervals[0]["a"]) > mp.mpf("1e-60") or abs(intervals[-1]["b"] - L) > mp.mpf("1e-60"):
        raise RuntimeError("breakpoint split did not cover [0,L]")
    return intervals


def gauss_rule(quad_order: int) -> Tuple[List[mp.mpf], List[mp.mpf]]:
    nodes, weights = mp.gauss_quadrature(quad_order, "legendre")
    return [nodes[i] for i in range(len(nodes))], [weights[i] for i in range(len(weights))]


def integrate_coefficients(
    model: ProlateModel,
    *,
    dps: int,
    quad_order: int,
    n_values: Sequence[int],
    names: Sequence[str],
    plant_node_error: Optional[mp.mpf] = None,
) -> IntegralResult:
    mp.mp.dps = dps
    lam = mp.sqrt(LAMBDA_SQ)
    L = mp.log(LAMBDA_SQ)
    sqrt_L = mp.sqrt(L)
    intervals = split_intervals()
    nodes, weights = gauss_rule(quad_order)
    coeffs: Dict[str, List[mp.mpc]] = {name: [mp.mpc(0) for _ in n_values] for name in names}
    raw_sq: Dict[str, mp.mpf] = {name: mp.mpf("0") for name in names}
    planted_done = False
    planted_observed: Optional[mp.mpf] = None

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
            sums = {name: mp.mpf("0") for name in names}
            for m in range(1, mmax + 1):
                t = mp.mpf(m) * exp_x / LAMBDA_SQ
                vals = eval_all_g(model, t)
                for name in names:
                    sums[name] += vals[name]
            e_vals = {name: mp.sqrt(u) * sums[name] for name in names}

            for name in names:
                raw_sq[name] += w * e_vals[name] * e_vals[name]

            factor = w / sqrt_L
            if len(n_values) == 1:
                n = n_values[0]
                phase = mp.e ** (-2j * mp.pi * n * x / L)
                for name in names:
                    coeffs[name][0] += factor * e_vals[name] * phase
                if plant_node_error is not None and not planted_done and "g04" in names:
                    # Plant the error into one quadrature-node contribution,
                    # not into the raw integrand value where the weight can
                    # dilute it below the requested judge threshold.
                    coeffs["g04"][0] += plant_node_error
                    planted_observed = abs(plant_node_error)
                    planted_done = True
            else:
                z = mp.e ** (-2j * mp.pi * x / L)
                phase = mp.e ** (-2j * mp.pi * n_values[0] * x / L)
                for idx, _ in enumerate(n_values):
                    for name in names:
                        coeffs[name][idx] += factor * e_vals[name] * phase
                    phase *= z

    raw_norms = {name: mp.sqrt(max(raw_sq[name], mp.mpf("0"))) for name in names}
    interval_rows = [{"a": row["a"], "b": row["b"], "mmax": row["mmax"]} for row in intervals]
    return IntegralResult(
        dps=dps,
        quad_order=quad_order,
        coeffs=coeffs,
        raw_norms=raw_norms,
        intervals=interval_rows,
        planted_observed_contribution=planted_observed,
    )


def max_coeff_diff(left: IntegralResult, right: IntegralResult, names: Sequence[str]) -> mp.mpf:
    err = mp.mpf("0")
    for name in names:
        for a, b in zip(left.coeffs[name], right.coeffs[name]):
            err = max(err, abs(a - b))
    return err


def adaptive_packet_run(spec: Dict[str, Any]) -> Dict[str, Any]:
    dps = int(spec["dps"])
    tol = mp.mpf(spec["tol"])
    mp.mp.dps = dps
    started = time.time()
    model = build_prolate_model(dps)
    n_values = list(range(-N, N + 1))
    q = int(spec["q_start"])
    low: Optional[IntegralResult] = None
    attempts: List[Dict[str, Any]] = []

    while q <= int(spec["q_max"]):
        if low is None or low.quad_order != q:
            low = integrate_coefficients(model, dps=dps, quad_order=q, n_values=n_values, names=PACKET_NAMES)
        high = integrate_coefficients(model, dps=dps, quad_order=2 * q, n_values=n_values, names=PACKET_NAMES)
        diff = max_coeff_diff(low, high, PACKET_NAMES)
        attempts.append({"quad_order_low": q, "quad_order_high": 2 * q, "max_abs_coeff_diff": diff})
        if diff <= tol:
            normalized: Dict[str, List[mp.mpc]] = {}
            pN_norms: Dict[str, mp.mpf] = {}
            for name in PACKET_NAMES:
                normalized[name], pN_norms[name] = normalize_coeffs(high.coeffs[name])
            return {
                "status": "OK",
                "label": spec["label"],
                "tol": tol,
                "tol_label": spec["tol_label"],
                "dps": dps,
                "quad_order": 2 * q,
                "attempts": attempts,
                "coeff_max_abs_diff": diff,
                "coeffs_normalized": normalized,
                "raw_norms": high.raw_norms,
                "pN_norms": pN_norms,
                "breakpoint_intervals": high.intervals,
                "prolate_eigenvalues_0_4": [model.eigenvalues[i] for i in range(5)],
                "prolate_integrals": model.integrals,
                "combo_coeffs": model.combo_coeffs,
                "elapsed_s": time.time() - started,
            }
        low = high
        q *= 2

    return {
        "status": "CONSTRUCTOR_TOL_NOT_REACHED",
        "label": spec["label"],
        "tol": tol,
        "tol_label": spec["tol_label"],
        "dps": dps,
        "attempts": attempts,
        "coeff_max_abs_diff": attempts[-1]["max_abs_coeff_diff"] if attempts else None,
        "elapsed_s": time.time() - started,
    }


def single_coeff(model: ProlateModel, dps: int, quad_order: int, plant: Optional[mp.mpf] = None) -> mp.mpc:
    res = integrate_coefficients(model, dps=dps, quad_order=quad_order, n_values=[0], names=["g04"], plant_node_error=plant)
    return res.coeffs["g04"][0]


def constructor_selftests() -> Dict[str, Any]:
    started = time.time()
    model40 = build_prolate_model(40)
    c40 = single_coeff(model40, 40, 192)
    model80 = build_prolate_model(80)
    c80 = single_coeff(model80, 80, 384)
    diff = abs(c40 - c80)

    clean_low = single_coeff(model80, 80, 96)
    clean_high = single_coeff(model80, 80, 192)
    planted = single_coeff(model80, 80, 96, plant=mp.mpf("1e-20"))
    planted_diff = abs(planted - clean_high)
    clean_diff = abs(clean_low - clean_high)

    k1_pass = diff <= TOL_A
    planted_pass = clean_diff <= TOL_A and planted_diff > TOL_A
    return {
        "elapsed_s": time.time() - started,
        "K1_dps40_vs_dps80": {
            "coefficient": "g04,n=0",
            "dps40_quad_order": 192,
            "dps80_quad_order": 384,
            "abs_diff": diff,
            "tol": TOL_A,
            "pass": k1_pass,
        },
        "K1_planted_node_error": {
            "coefficient": "g04,n=0",
            "clean_low_quad_order": 96,
            "clean_high_quad_order": 192,
            "planted_error_in_one_node": "1e-20",
            "clean_abs_diff": clean_diff,
            "planted_abs_diff_vs_clean_high": planted_diff,
            "tol": TOL_A,
            "pass": planted_pass,
        },
        "pass": k1_pass and planted_pass,
    }


def packet_vectors(run: Dict[str, Any]) -> Dict[str, mp.matrix]:
    return {
        LOGICAL_BY_PACKET[name]: vector_from_coeffs(run["coeffs_normalized"][name])
        for name in PACKET_NAMES
    }


def parity_rows(vectors: Dict[str, mp.matrix]) -> Tuple[Dict[str, mp.matrix], List[Dict[str, Any]]]:
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
        raise RuntimeError("xi1 saved vector has incomplete n support")
    nrm = pilot.norm(v)
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


def compute_metrics(run: Dict[str, Any], T: mp.matrix, xi1: mp.matrix) -> Dict[str, Any]:
    vectors = packet_vectors(run)
    projected, dust_rows = parity_rows(vectors)
    even_packets, q_stats = pilot.modified_gram_schmidt_mp(
        [projected["k1"], projected["k2_even"]],
        tol=mp.power(10, -min(70, max(30, mp.mp.dps // 3))),
    )
    if len(even_packets) != 2:
        raise RuntimeError(f"even packet MGS accepted {len(even_packets)} vectors, expected 2")
    G_even = even_g_block(T, even_packets)
    g_vals = sorted(eigvals_hermitian(G_even))
    k1 = projected["k1"]
    a1 = mp.re(pilot.inner(k1, T * k1))
    align = 1 - abs(pilot.inner(xi1, k1))
    y_norm = project_residual_norm(xi1, even_packets)
    return {
        "label": run["label"],
        "tol_label": run["tol_label"],
        "dps": run["dps"],
        "quad_order": run["quad_order"],
        "coeff_max_abs_diff": run["coeff_max_abs_diff"],
        "dust_rows": dust_rows,
        "dust_max_delta_off": max(row["delta_off_parity"] for row in dust_rows),
        "raw_norms": run["raw_norms"],
        "pN_norms": run["pN_norms"],
        "even_q_stats": q_stats,
        "G_even": matrix_to_rows(G_even),
        "lambda1_G_even": g_vals[0],
        "lambda2_G_even": g_vals[1],
        "a1": a1,
        "alignment_one_minus_abs_xi1_inner_k1": align,
        "y_norm_xi1_minus_P_evenM_xi1": y_norm,
        "k1_projected": k1,
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
    return {"lambda_sq": 12, "N": 120, "status": "MISSING", "source": None, "checked": checked, "value": None}


def classify(metrics: Sequence[Dict[str, Any]], T: mp.matrix) -> Dict[str, Any]:
    A = metrics[0]
    B = metrics[1]
    lam_ratio = A["lambda1_G_even"] / max(B["lambda1_G_even"], mp.mpf("1e-300"))
    y_ratio = A["y_norm_xi1_minus_P_evenM_xi1"] / max(B["y_norm_xi1_minus_P_evenM_xi1"], mp.mpf("1e-300"))
    codes: List[str] = []
    landed_at_mu1 = B["lambda1_G_even"] <= mp.mpf("1e-56")
    if lam_ratio >= mp.mpf("1e8") or landed_at_mu1:
        eps_code = "EPS_SQUARE_LAW_CONFIRMED"
        codes.append(eps_code)
        if landed_at_mu1:
            codes.append("LANDS_AT_MU1")
    else:
        eps_code = "EPS_SQUARE_LAW_FAILS"
        codes.append(eps_code)

    if y_ratio >= mp.mpf("1e10"):
        y_code = "Y_TRACKS_TOL"
    else:
        y_code = "Y_PHYSICAL"
    codes.append(y_code)

    eta: Optional[mp.mpf] = None
    eta_class: Optional[Dict[str, Any]] = None
    if eps_code == "EPS_SQUARE_LAW_CONFIRMED":
        k1 = B["k1_projected"]
        a1 = B["a1"]
        residual = T * k1
        for i in range(residual.rows):
            residual[i] -= a1 * k1[i]
        eta = pilot.norm(residual)
        refs = {"E^(1/4)": mp.mpf("1e-18"), "E^(1/2)": mp.mpf("1e-36"), "E": mp.mpf("1e-71")}
        best = min(refs.items(), key=lambda kv: abs(mp.log10(max(eta, mp.mpf("1e-300"))) - mp.log10(kv[1])))
        eta_class = {"label": "FIT_NOT_LAW", "eta_true": eta, "closest_class": best[0], "class_refs": refs}
        codes.append("ETA_TRUE_MEASURED")

    return {
        "codes": codes,
        "eps_code": eps_code,
        "lambda1_A_over_B": lam_ratio,
        "expected_square_ratio": "1e12",
        "y_code": y_code,
        "y_A_over_B": y_ratio,
        "eta_true": eta,
        "eta_classification": eta_class,
        "status": "complete",
    }


def strip_vectors_for_json(metrics: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows = []
    for row in metrics:
        clean = dict(row)
        clean.pop("k1_projected", None)
        rows.append(clean)
    return rows


def write_report(payload: Dict[str, Any]) -> None:
    cls = payload["classification"]
    lines = [
        "# TruePrecisionPacketGate_v1",
        "",
        "Route B TwoLevelSpectralLadder diagnostic only. Not RH. No Phase 2. One point `(lambda_sq,N)=(13,120)`.",
        "",
        "## Verdict",
        "",
        f"- status: `{payload['status']}`",
        f"- codes: `{cls['codes']}`",
        f"- eps code: `{cls['eps_code']}`",
        f"- y code: `{cls['y_code']}`",
        f"- lambda1(A)/lambda1(B): `{fmt(cls['lambda1_A_over_B'], 12)}`",
        f"- y(A)/y(B): `{fmt(cls['y_A_over_B'], 12)}`",
        "",
        "## P0 Constructor Self-Test",
        "",
        f"- K1 dps40 vs dps80 pass: `{payload['selftests']['K1_dps40_vs_dps80']['pass']}`; diff `{fmt(payload['selftests']['K1_dps40_vs_dps80']['abs_diff'], 8)}`",
        f"- planted node error caught: `{payload['selftests']['K1_planted_node_error']['pass']}`; clean diff `{fmt(payload['selftests']['K1_planted_node_error']['clean_abs_diff'], 8)}`, planted diff `{fmt(payload['selftests']['K1_planted_node_error']['planted_abs_diff_vs_clean_high'], 8)}`",
        "",
        "## P1-P3 Runs",
        "",
        "| run | tol | dps | q | coeff maxdiff | max dust | lambda1(G_even) | lambda2(G_even) | 1-|<xi1,k1>| | ||y|| |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["metrics"]:
        lines.append(
            f"| `{row['label']}` | `{row['tol_label']}` | {row['dps']} | {row['quad_order']} | `{fmt(row['coeff_max_abs_diff'], 8)}` | `{fmt(row['dust_max_delta_off'], 8)}` | `{fmt(row['lambda1_G_even'], 8)}` | `{fmt(row['lambda2_G_even'], 8)}` | `{fmt(row['alignment_one_minus_abs_xi1_inner_k1'], 8)}` | `{fmt(row['y_norm_xi1_minus_P_evenM_xi1'], 8)}` |"
        )
    lines.extend(["", "Dust rows:"])
    for row in payload["metrics"]:
        parts = ", ".join(f"{dust['vector']}={fmt(dust['delta_off_parity'], 8)}" for dust in row["dust_rows"])
        lines.append(f"- `{row['label']}`: {parts}")

    lines.extend(
        [
            "",
            "## P4 Eta",
            "",
        ]
    )
    if cls["eta_true"] is None:
        lines.append("- skipped: P2 did not confirm EPS square law.")
    else:
        eta_class = cls["eta_classification"]
        lines.append(f"- eta_true: `{fmt(eta_class['eta_true'], 12)}`")
        lines.append(f"- closest class: `{eta_class['closest_class']}` (`FIT_NOT_LAW`, one point only)")

    y12 = payload["P5_y_12_120"]
    source = y12["source"] if y12["source"] else ",".join(y12.get("checked", []))
    lines.extend(
        [
            "",
            "## P5 Free Pull",
            "",
            f"- ||y||(12,120): `{fmt(y12['value'], 12)}`; status `{y12['status']}`; source `{source}`",
            "",
            "## Stop",
            "",
            "Stop after this report + handoff. Carry the verdict into `OperatorStaticSchurStabilityGate` on `S0_parity`.",
            "",
        ]
    )
    REPORT.write_text("\n".join(lines), encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    cls = payload["classification"]
    A, B = payload["metrics"]
    lines = [
        "PROSHKA_ROUTE_REVIEW",
        "",
        "Gate:",
        "TruePrecisionPacketGate_v1 / Route B TwoLevelSpectralLadder",
        "",
        "Codes:",
        str(cls["codes"]),
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. Phase 2 not run. No new lambda/N anchors. Q3 mainline not touched.",
        "",
        "What happened:",
        "- Rebuilt E-map coefficients <E(f),V_n> in mpmath with breakpoint splitting at u=lambda/m for lambda^2=13.",
        f"- Constructor selftest pass: {payload['selftests']['pass']}.",
        f"- lambda1(G_even) tol_A -> tol_B: {fmt(A['lambda1_G_even'], 8)} -> {fmt(B['lambda1_G_even'], 8)}; ratio A/B={fmt(cls['lambda1_A_over_B'], 12)}.",
        f"- max dust tol_A -> tol_B: {fmt(A['dust_max_delta_off'], 8)} -> {fmt(B['dust_max_delta_off'], 8)}.",
        f"- ||y|| tol_A -> tol_B: {fmt(A['y_norm_xi1_minus_P_evenM_xi1'], 12)} -> {fmt(B['y_norm_xi1_minus_P_evenM_xi1'], 12)}; ratio A/B={fmt(cls['y_A_over_B'], 12)}.",
        f"- P5 ||y||(12,120) status: {payload['P5_y_12_120']['status']}.",
        "",
        "Question for Proshka:",
        "Accept these codes as the packet-precision verdict to carry into OperatorStaticSchurStabilityGate on S0_parity, or request another constructor audit before interpreting S0?",
        "",
        "Stop condition:",
        "Codex stops here after report + handoff; next gate is OperatorStaticSchurStabilityGate carrying these codes.",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "TRUE_PRECISION_PACKET_GATE_V1_COMPLETE",
            "last_verdict": payload["classification"]["eps_code"],
            "last_codes": payload["classification"]["codes"],
            "next_gate": "OperatorStaticSchurStabilityGate_on_S0_parity",
            "last_report": "true_precision_packet_gate_v1.md",
            "last_json": "out/true_precision_packet_gate_v1.json",
            "route_status": "NOT_RH_DIAGNOSTIC_ONLY",
            "phase2_run": False,
            "new_lambda_or_N_anchor_bought": False,
            "q3_main_touched": False,
        }
    )
    write_json(LOOP_STATE, state)


def write_selftest_failure(selftests: Dict[str, Any]) -> None:
    payload = {
        "gate": "TruePrecisionPacketGate_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": "CONSTRUCTOR_SELFTEST_FAILS",
        "codes": ["CONSTRUCTOR_SELFTEST_FAILS"],
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "q3_main_touched": False,
        "selftests": selftests,
    }
    write_json(JSON_OUT, payload)
    REPORT.write_text(
        "# TruePrecisionPacketGate_v1\n\n"
        "Status: `CONSTRUCTOR_SELFTEST_FAILS`.\n\n"
        f"K1 dps40/dps80 pass: `{selftests['K1_dps40_vs_dps80']['pass']}`.\n"
        f"Planted node error pass: `{selftests['K1_planted_node_error']['pass']}`.\n",
        encoding="utf-8",
    )
    HANDOFF.write_text(
        "PROSHKA_ROUTE_REVIEW\n\n"
        "Gate:\nTruePrecisionPacketGate_v1\n\n"
        "Codes:\n['CONSTRUCTOR_SELFTEST_FAILS']\n\n"
        "Stop condition:\nConstructor self-test failed; do not interpret packet drift.\n",
        encoding="utf-8",
    )
    update_loop_state({"classification": {"eps_code": "CONSTRUCTOR_SELFTEST_FAILS", "codes": ["CONSTRUCTOR_SELFTEST_FAILS"]}})


def main() -> None:
    started = time.time()
    mp.mp.dps = 80
    selftests = constructor_selftests()
    if not selftests["pass"]:
        write_selftest_failure(selftests)
        print("CONSTRUCTOR_SELFTEST_FAILS")
        return

    run_payloads = [adaptive_packet_run(spec) for spec in RUN_SPECS]
    failures = [row for row in run_payloads if row.get("status") != "OK"]
    if failures:
        payload = {
            "gate": "TruePrecisionPacketGate_v1",
            "route": "RouteB_TwoLevelSpectralLadder",
            "status": "CONSTRUCTOR_TOL_NOT_REACHED",
            "codes": ["CONSTRUCTOR_SELFTEST_FAILS"],
            "selftests": selftests,
            "runs": run_payloads,
            "phase2_run": False,
            "new_lambda_or_N_anchor_bought": False,
            "q3_main_touched": False,
        }
        write_json(JSON_OUT, payload)
        REPORT.write_text("# TruePrecisionPacketGate_v1\n\nStatus: `CONSTRUCTOR_TOL_NOT_REACHED`.\n", encoding="utf-8")
        write_handoff(
            {
                "classification": {"codes": ["CONSTRUCTOR_SELFTEST_FAILS"], "lambda1_A_over_B": mp.nan, "y_A_over_B": mp.nan},
                "selftests": selftests,
                "metrics": [
                    {"lambda1_G_even": mp.nan, "dust_max_delta_off": mp.nan, "y_norm_xi1_minus_P_evenM_xi1": mp.nan},
                    {"lambda1_G_even": mp.nan, "dust_max_delta_off": mp.nan, "y_norm_xi1_minus_P_evenM_xi1": mp.nan},
                ],
                "P5_y_12_120": {"status": "NOT_RUN"},
            }
        )
        print("CONSTRUCTOR_TOL_NOT_REACHED")
        return

    cell = load_json(OUT_DIR / "lambda_sq_13_N_120.json")
    dps_T = int(cell["dps"])
    mp.mp.dps = dps_T
    T = pilot.build_tau_matrix(mp.sqrt(LAMBDA_SQ), N, dps_T)
    xi1, xi_source = xi1_from_saved_cache()
    metrics = [compute_metrics(row, T, xi1) for row in run_payloads]
    classification = classify(metrics, T)
    y12 = optional_y_12_120()
    payload: Dict[str, Any] = {
        "gate": "TruePrecisionPacketGate_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "source": "mpmath_E_map_breakpoint_split_constructor",
        "lambda_sq": LAMBDA_SQ,
        "lambda": mp.sqrt(LAMBDA_SQ),
        "N": N,
        "dps_T": dps_T,
        "status": classification["status"],
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "new_lambdas": False,
        "q3_main_touched": False,
        "elapsed_s": time.time() - started,
        "selftests": selftests,
        "constructor_runs": [
            {k: v for k, v in row.items() if k not in {"coeffs_normalized"}}
            for row in run_payloads
        ],
        "metrics": strip_vectors_for_json(metrics),
        "xi1_source": xi_source,
        "P5_y_12_120": y12,
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
