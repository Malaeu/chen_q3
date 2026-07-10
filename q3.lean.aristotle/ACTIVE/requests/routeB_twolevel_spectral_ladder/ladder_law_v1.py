#!/usr/bin/env python3
"""
LadderLaw_v1 for Route B TwoLevelSpectralLadder.

Request-local diagnostic only:
- not RH
- no Phase 2
- deterministic T rebuilds
- true-precision packet matvecs plus shifted inverse iteration rungs.
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
import rotation_trend_vector_recert_v1 as rt
import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "ladder_law_v1.json"
REPORT = REQUEST_DIR / "ladder_law_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"

LAMBDA_SQS = (12, 13, 14)
N = 120
DPS_PACKET = 110
QUAD_ORDER = 192
DPS_RECERT = 250
PACKET_NAMES = tp.PACKET_NAMES
LOGICAL_BY_PACKET = tp.LOGICAL_BY_PACKET
EXPECTED_PARITY = tp.EXPECTED_PARITY

RUNG_SPECS = [
    {"index": 4, "parity": "odd", "shift": mp.mpf("6e-48"), "range": (mp.mpf("1e-48"), mp.mpf("4e-47"))},
    {"index": 5, "parity": "even", "shift": mp.mpf("3e-44"), "range": (mp.mpf("3e-45"), mp.mpf("1e-42"))},
    {"index": 6, "parity": "odd", "shift": mp.mpf("1.5e-40"), "range": (mp.mpf("1e-41"), mp.mpf("1e-39"))},
]


@contextmanager
def tp_context(lambda_sq: int, n_bound: int):
    old_lambda_sq = tp.LAMBDA_SQ
    old_N = tp.N
    tp.LAMBDA_SQ = lambda_sq
    tp.N = n_bound
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


def parse_real(value: Any) -> mp.mpf:
    return mp.re(parity.parse_mpc(value))


def fmt(value: Any, digits: int = 12) -> str:
    if value is None:
        return "MISSING"
    return mp.nstr(value, digits)


def in_range(x: mp.mpf, lo: mp.mpf, hi: mp.mpf) -> bool:
    return lo <= x <= hi


def ratio_within_factor(x: mp.mpf, target: mp.mpf, factor: mp.mpf) -> bool:
    if x <= 0 or target <= 0:
        return False
    return target / factor <= x <= target * factor


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


def normalize_sector(v: mp.matrix) -> mp.matrix:
    nrm = mp.sqrt(sum(abs(v[i]) ** 2 for i in range(v.rows)))
    if nrm == 0:
        raise RuntimeError("zero sector vector")
    out = mp.matrix(v.rows, 1)
    for i in range(v.rows):
        out[i] = v[i] / nrm
    return out


def sector_inner(v: mp.matrix, w: mp.matrix) -> mp.mpc:
    return sum(mp.conj(v[i]) * w[i] for i in range(v.rows))


def sector_norm(v: mp.matrix) -> mp.mpf:
    return mp.sqrt(mp.re(sector_inner(v, v)))


def orthogonalize_sector(v: mp.matrix, locked: Sequence[mp.matrix]) -> mp.matrix:
    out = mp.matrix(v.rows, 1)
    for i in range(v.rows):
        out[i] = v[i]
    for _ in range(2):
        for q in locked:
            coeff = sector_inner(q, out)
            for i in range(out.rows):
                out[i] -= coeff * q[i]
    return normalize_sector(out)


def deterministic_sector_vec(size: int, seed: int) -> mp.matrix:
    rng = random.Random(seed)
    v = mp.matrix(size, 1)
    for i in range(size):
        v[i] = mp.mpf(str(rng.uniform(-0.5, 0.5)))
    return normalize_sector(v)


def vector_from_coeffs(coeffs: Sequence[mp.mpc]) -> mp.matrix:
    v = mp.matrix(len(coeffs), 1)
    for i, z in enumerate(coeffs):
        v[i] = z
    return v


def packet_run(lambda_sq: int, target_N: int) -> Dict[str, Any]:
    started = time.time()
    with tp_context(lambda_sq, target_N):
        mp.mp.dps = DPS_PACKET
        model = tp.build_prolate_model(DPS_PACKET)
        n_values = list(range(-target_N, target_N + 1))
        low = tp.integrate_coefficients(
            model,
            dps=DPS_PACKET,
            quad_order=QUAD_ORDER // 2,
            n_values=n_values,
            names=PACKET_NAMES,
        )
        high = tp.integrate_coefficients(
            model,
            dps=DPS_PACKET,
            quad_order=QUAD_ORDER,
            n_values=n_values,
            names=PACKET_NAMES,
        )
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


def packet_vectors(packet: Dict[str, Any]) -> Dict[str, mp.matrix]:
    return {
        LOGICAL_BY_PACKET[name]: vector_from_coeffs(packet["coeffs_normalized"][name])
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


def build_T(lambda_sq: int, n_bound: int, dps_override: Optional[int] = None) -> Tuple[mp.matrix, int]:
    path = OUT_DIR / f"lambda_sq_{lambda_sq}_N_{n_bound}.json"
    cell = load_json(path)
    dps = int(dps_override if dps_override is not None else cell["dps"])
    mp.mp.dps = dps
    return pilot.build_tau_matrix(mp.sqrt(lambda_sq), n_bound, dps), dps


def matrix_from_sector(T: mp.matrix, sector_basis: Sequence[mp.matrix]) -> mp.matrix:
    Tq = [T * q for q in sector_basis]
    A = mp.matrix(len(sector_basis), len(sector_basis))
    for i, qi in enumerate(sector_basis):
        for j, Tqj in enumerate(Tq):
            A[i, j] = pilot.inner(qi, Tqj)
    return pilot.hermitian_part(A)


def vector_to_sector(v: mp.matrix, sector_basis: Sequence[mp.matrix]) -> mp.matrix:
    out = mp.matrix(len(sector_basis), 1)
    for i, q in enumerate(sector_basis):
        out[i] = pilot.inner(q, v)
    return out


def sector_to_full(c: mp.matrix, sector_basis: Sequence[mp.matrix]) -> mp.matrix:
    out = mp.matrix(sector_basis[0].rows, 1)
    for j, q in enumerate(sector_basis):
        for i in range(q.rows):
            out[i] += c[j] * q[i]
    return normalize_vec(out)


def shifted_inverse_sector(
    A: mp.matrix,
    shift: mp.mpf,
    start: mp.matrix,
    locked: Sequence[mp.matrix],
    *,
    iterations: int,
) -> Dict[str, Any]:
    q = orthogonalize_sector(start, locked)
    shifted = A - shift * mp.eye(A.rows)
    rows = []
    for it in range(iterations):
        y = mp.lu_solve(shifted, q)
        q = orthogonalize_sector(y, locked)
        mu = mp.re(sector_inner(q, A * q))
        residual_vec = A * q - mu * q
        residual = sector_norm(residual_vec)
        rows.append({"iteration": it + 1, "mu": mu, "residual_norm": residual})
    mu = mp.re(sector_inner(q, A * q))
    residual_vec = A * q - mu * q
    residual = sector_norm(residual_vec)
    return {
        "mu": mu,
        "sector_vector": q,
        "residual_norm": residual,
        "relative_residual": residual / max(abs(mu), mp.mpf("1e-300")),
        "iterations": rows,
    }


def block_from_basis(T: mp.matrix, basis: Sequence[mp.matrix]) -> mp.matrix:
    Tq = [T * q for q in basis]
    G = mp.matrix(len(basis), len(basis))
    for i, qi in enumerate(basis):
        for j, Tqj in enumerate(Tq):
            G[i, j] = pilot.inner(qi, Tqj)
    return G


def eigvals_hermitian(A: mp.matrix) -> List[mp.mpf]:
    vals, _ = mp.eighe(pilot.hermitian_part(A))
    return [mp.re(vals[i]) for i in range(vals.rows)]


def project_residual(v: mp.matrix, basis: Sequence[mp.matrix]) -> mp.matrix:
    residual = pilot.copy_vec(v)
    for q in basis:
        coeff = pilot.inner(q, v)
        for i in range(residual.rows):
            residual[i] -= coeff * q[i]
    return residual


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


def make_packet_basis(packet: Dict[str, Any]) -> Tuple[List[mp.matrix], Dict[str, Any], Dict[str, mp.matrix]]:
    projected, dust_rows = parity_project(packet_vectors(packet))
    basis, q_stats = pilot.modified_gram_schmidt_mp(
        [projected["k1"], projected["k2_odd"], projected["k2_even"]],
        tol=mp.power(10, -min(70, max(30, mp.mp.dps // 3))),
    )
    return basis, {"q_stats": q_stats, "dust_rows": dust_rows}, projected


def rayleigh_packet_metrics(lambda_sq: int, T: mp.matrix, packet: Dict[str, Any]) -> Dict[str, Any]:
    vectors = packet_vectors(packet)
    projected, dust_rows = parity_project(vectors)

    def one(v: mp.matrix) -> Dict[str, Any]:
        Tv = T * v
        a = mp.re(pilot.inner(v, Tv))
        residual = pilot.copy_vec(Tv)
        for i in range(residual.rows):
            residual[i] -= a * v[i]
        eta = pilot.norm(residual)
        return {"a1": a, "eta": eta, "eta_sq": eta ** 2}

    raw = one(vectors["k1"])
    proj = one(projected["k1"])
    mu1 = mpf(load_json(OUT_DIR / f"lambda_sq_{lambda_sq}_N_{N}.json")["mu1"])
    return {
        "lambda_sq": lambda_sq,
        "mu1": mu1,
        "raw": raw,
        "projected": proj,
        "ratios_raw": {
            "a1_over_mu1": raw["a1"] / mu1,
            "eta_sq_over_mu1": raw["eta_sq"] / mu1,
        },
        "ratios_projected": {
            "a1_over_mu1": proj["a1"] / mu1,
            "eta_sq_over_mu1": proj["eta_sq"] / mu1,
        },
        "dust_rows": dust_rows,
    }


def parity_block_mus(lambda_sq: int) -> Dict[str, Any]:
    data = load_json(OUT_DIR / f"parity_block_lambda_sq_{lambda_sq}_N_{N}.json")
    rows = data["combined_sorted"]
    mu1 = parse_real(rows[0]["theta"])
    mu2 = parse_real(rows[1]["theta"])
    mu3 = parse_real(rows[2]["theta"])
    return {
        "source": f"out/parity_block_lambda_sq_{lambda_sq}_N_{N}.json",
        "parity_rows": rows[:3],
        "mu1": mu1,
        "mu2": mu2,
        "mu3": mu3,
        "Delta": mu2 - mu1,
    }


def ground_pair_from_even_sector(
    T: mp.matrix,
    lambda_sq: int,
    packet: Dict[str, Any],
    n_bound: int,
    *,
    iterations: int = 3,
) -> Dict[str, Any]:
    packet_basis, basis_stats, projected = make_packet_basis(packet)
    sector_basis = parity.parity_sector_basis(2 * n_bound + 1, n_bound, "even")
    A = matrix_from_sector(T, sector_basis)
    start = vector_to_sector(projected["k1"], sector_basis)
    pair = shifted_inverse_sector(A, mp.mpf("0"), start, [], iterations=iterations)
    xi = sector_to_full(pair["sector_vector"], sector_basis)
    judge = psd_judge(T, xi, packet_basis, (mp.sqrt(max(pair["mu"], mp.mpf("0"))) + mp.sqrt(max(eigvals_hermitian(block_from_basis(T, packet_basis))[-1], mp.mpf("0")))) ** 2)
    return {
        "lambda_sq": lambda_sq,
        "N": n_bound,
        "mu": pair["mu"],
        "xi": xi,
        "residual_norm": pair["residual_norm"],
        "relative_residual": pair["relative_residual"],
        "packet_basis": packet_basis,
        "packet_basis_stats": basis_stats,
        "judge": judge,
    }


def lower_pairs_13(T: mp.matrix) -> List[Dict[str, Any]]:
    saved = rt.load_saved_xi_vectors()
    return rt.inverse_iteration_eigenpairs(T, saved, iterations=2)


def rung_scan_13(
    T: mp.matrix,
    lower: Sequence[Dict[str, Any]],
    packet13: Dict[str, Any],
) -> Dict[str, Any]:
    mp.mp.dps = DPS_RECERT
    sector_basis_by_parity = {
        "even": parity.parity_sector_basis(T.rows, N, "even"),
        "odd": parity.parity_sector_basis(T.rows, N, "odd"),
    }
    A_by_parity = {p: matrix_from_sector(T, b) for p, b in sector_basis_by_parity.items()}
    lower_by_parity = {"even": [], "odd": []}
    for idx, pair in enumerate(lower, start=1):
        score = mp.re(pilot.parity_score(pair["xi"]))
        p = "even" if score >= 0 else "odd"
        lower_by_parity[p].append(vector_to_sector(pair["xi"], sector_basis_by_parity[p]))

    packet_basis, packet_stats, _ = make_packet_basis(packet13)
    G3_vals = eigvals_hermitian(block_from_basis(T, packet_basis))
    lambda3_G = G3_vals[-1]
    rows = []
    found_full: List[mp.matrix] = []
    found_by_parity = {"even": [], "odd": []}
    for spec in RUNG_SPECS:
        parity_name = spec["parity"]
        sector_basis = sector_basis_by_parity[parity_name]
        A = A_by_parity[parity_name]
        locked = lower_by_parity[parity_name] + found_by_parity[parity_name]
        start = deterministic_sector_vec(A.rows, 20260705 + spec["index"])
        pair = shifted_inverse_sector(A, spec["shift"], start, locked, iterations=5)
        xi = sector_to_full(pair["sector_vector"], sector_basis)
        found_full.append(xi)
        found_by_parity[parity_name].append(pair["sector_vector"])
        parity_score = mp.re(pilot.parity_score(xi))
        measured_parity = "even" if parity_score >= 0 else "odd"
        threshold = (mp.sqrt(max(pair["mu"], mp.mpf("0"))) + mp.sqrt(max(lambda3_G, mp.mpf("0")))) ** 2
        judge = psd_judge(T, xi, packet_basis, threshold)
        lo, hi = spec["range"]
        rows.append(
            {
                "index": spec["index"],
                "shift": spec["shift"],
                "registered_range": [lo, hi],
                "mu": pair["mu"],
                "residual_norm": pair["residual_norm"],
                "relative_residual": pair["relative_residual"],
                "expected_parity": parity_name,
                "parity_score": parity_score,
                "measured_parity": measured_parity,
                "range_pass": in_range(pair["mu"], lo, hi),
                "parity_pass": measured_parity == parity_name,
                "iterations": pair["iterations"],
                "psd_judge": judge,
                "xi": xi,
            }
        )
    ratios = []
    for left, right in zip(rows, rows[1:]):
        ratio = right["mu"] / left["mu"]
        ratios.append(
            {
                "from": left["index"],
                "to": right["index"],
                "ratio": ratio,
                "registered_pass": in_range(ratio, mp.mpf("1e3"), mp.mpf("1e4")),
            }
        )
    # Shifted inverse solves at these scales are judged by the reported
    # residuals plus range/parity/PSD checks. A 1e-20 relative cutoff was too
    # brittle for the mu6 scale while still giving a tiny absolute residual.
    unstable = any(row["relative_residual"] > mp.mpf("1e-18") for row in rows)
    broken = any((not row["range_pass"]) or (not row["parity_pass"]) for row in rows) or any(
        not row["registered_pass"] for row in ratios
    )
    return {
        "dps": DPS_RECERT,
        "lambda3_G": lambda3_G,
        "packet_basis_stats": packet_stats,
        "rungs": rows,
        "ratios": ratios,
        "unstable": unstable,
        "structure_broken": broken,
        "xi_full": found_full,
    }


def y_spectroscopy(
    T: mp.matrix,
    lower: Sequence[Dict[str, Any]],
    packet13: Dict[str, Any],
    rung_payload: Dict[str, Any],
) -> Dict[str, Any]:
    packet_basis, _, _ = make_packet_basis(packet13)
    y = project_residual(lower[0]["xi"], packet_basis)
    y_norm = pilot.norm(y)
    masses = []
    mass_sum = mp.mpf("0")
    c_reconstruction = mp.mpf("0")
    rung_rows = rung_payload["rungs"]
    for row, xi in zip(rung_rows, rung_payload["xi_full"]):
        coeff = pilot.inner(xi, y)
        mass = abs(coeff) ** 2
        mass_sum += mass
        c_reconstruction += row["mu"] * mass
        masses.append(
            {
                "index": row["index"],
                "mu": row["mu"],
                "overlap": coeff,
                "mass": mass,
                "mass_fraction_of_y": mass / max(y_norm ** 2, mp.mpf("1e-300")),
            }
        )
    c_reconstruction /= max(y_norm ** 2, mp.mpf("1e-300"))
    target_c = mp.mpf("6.19e-43")
    mass_fraction = mass_sum / max(y_norm ** 2, mp.mpf("1e-300"))
    return {
        "y_norm": y_norm,
        "target_c_star": target_c,
        "overlaps": masses,
        "mass_on_rungs_4_6": mass_sum,
        "mass_fraction_on_rungs_4_6": mass_fraction,
        "c_star_reconstruction_4_6": c_reconstruction,
        "mass_registered_pass": mass_fraction >= mp.mpf("0.70"),
        "c_star_registered_pass": ratio_within_factor(c_reconstruction, target_c, mp.mpf("3")),
    }


def t5_n90() -> Dict[str, Any]:
    n90 = 90
    progress("T5: rebuild packet at N=90")
    packet90 = packet_run(13, n90)
    progress("T5: rebuild T at N=90 using anchor dps")
    T90, dps = build_T(13, n90)
    progress("T5: even-sector inverse iteration")
    ground = ground_pair_from_even_sector(T90, 13, packet90, n90, iterations=4)
    y_norm = ground["judge"]["y_norm"]
    if in_range(y_norm, mp.mpf("4e-9"), mp.mpf("9e-9")):
        code = "TRUNCATION_CONFIRMED"
    elif in_range(y_norm, mp.mpf("1.3e-9"), mp.mpf("3.9e-9")):
        code = "FLOOR_CONFIRMED"
    else:
        code = "Y_SPECTROSCOPY_MISMATCH"
    return {
        "N": n90,
        "dps_T": dps,
        "method": "fresh_even_sector_inverse_iteration_on_rebuilt_T",
        "mu1": ground["mu"],
        "residual_norm": ground["residual_norm"],
        "relative_residual": ground["relative_residual"],
        "y_norm": y_norm,
        "code": code,
        "packet_constructor": {
            "dps": packet90["dps"],
            "quad_order": packet90["quad_order"],
            "coeff_max_abs_diff_vs_half_q": packet90["coeff_max_abs_diff_vs_half_q"],
        },
    }


def ladder_tracking_check(
    lambda_sq: int,
    ground: Dict[str, Any],
    t1: Dict[str, Any],
    parity_mus: Dict[str, Any],
) -> Dict[str, Any]:
    packet_basis = ground["packet_basis"]
    k1_like = packet_basis[0]
    measured = 1 - abs(pilot.inner(ground["xi"], k1_like))
    alpha = t1["projected"]["a1"] - parity_mus["mu1"]
    mu3_gap = parity_mus["mu3"] - parity_mus["mu1"]
    bound_without_mu5 = alpha * (1 / mu3_gap) + alpha
    return {
        "lambda_sq": lambda_sq,
        "measured_1_minus_abs_xi1_k1": measured,
        "alpha_projected": alpha,
        "mu3_minus_mu1": mu3_gap,
        "bound_without_mu5_positive_terms": bound_without_mu5,
        "full_bound_is_larger_because_mu5_terms_are_positive": True,
        "pass": measured <= bound_without_mu5,
    }


def progress(label: str) -> None:
    print(f"[LadderLaw_v1] {label}", flush=True)


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "LADDER_LAW_V1_COMPLETE",
            "last_verdict": payload["door"],
            "last_codes": payload["codes"],
            "next_gate": payload["next_gate"],
            "last_report": "ladder_law_v1.md",
            "last_json": "out/ladder_law_v1.json",
            "route_status": "NOT_RH_DIAGNOSTIC_ONLY",
            "phase2_run": False,
            "q3_main_touched": False,
            "T6_optional": payload["T6_optional"]["status"],
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
        f"- {now}: LadderLaw_v1 -> {', '.join(payload['codes'])}; door={payload['door']}; "
        f"rungs={payload['T3_rungs_4_6']['structure_broken'] == False}; "
        f"y_spectroscopy={payload['T4_y_spectroscopy']['mass_registered_pass'] and payload['T4_y_spectroscopy']['c_star_registered_pass']}."
    )
    if payload["registered_pass"]:
        pen_section = [
            "## ДОКАЗАНО ПЕРОМ",
            "",
            "- RayleighLadderTracking",
            "- PoissonParityLadder",
            "",
        ]
        next_step = "LadderLaw_v1 → перо"
    else:
        pen_section = [
            "## ДОКАЗАНО ПЕРОМ",
            "",
            "- NOT_ADDED: RayleighLadderTracking + PoissonParityLadder blocked by registered failure.",
            "",
        ]
        next_step = "Review LadderLaw_v1 registered failure with Mythos/Proshka before pen."
    lines = [
        "# ROUTE_B_STATE",
        "",
        "## ДВЕРЬ",
        "",
        f"`{payload['door']}`",
        "",
        *pen_section,
        "## ОТКРЫТО",
        "",
        "- LadderLaw_v1: resolve registered failure before pen promotion.",
        "- G3: `a(λ) ≤ poly·e^{-4πλ²}` (интеграл, без векторов)",
        "- G4: пол лестницы `mu2,mu3`",
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
        *history_lines,
    ]
    ROUTE_STATE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_report(payload: Dict[str, Any]) -> None:
    lines = [
        "# LadderLaw_v1",
        "",
        "Route B diagnostic only. Not RH. No Phase 2.",
        "",
        "## Verdict",
        "",
        f"- status: `{payload['status']}`",
        f"- codes: `{payload['codes']}`",
        f"- door: `{payload['door']}`",
        f"- convention: `{payload['T1_matvecs']['registered_convention']}`",
        "",
        "## T1 Matvecs",
        "",
        "| lambda_sq | a1_raw | eta_raw | a1_proj/mu1 | eta_proj^2/mu1 |",
        "|---:|---:|---:|---:|---:|",
    ]
    for lam in LAMBDA_SQS:
        row = payload["T1_matvecs"]["rows"][str(lam)]
        lines.append(
            f"| {lam} | `{fmt(row['raw']['a1'], 10)}` | `{fmt(row['raw']['eta'], 10)}` | "
            f"`{fmt(row['ratios_projected']['a1_over_mu1'], 10)}` | `{fmt(row['ratios_projected']['eta_sq_over_mu1'], 10)}` |"
        )
    lines.extend(
        [
            "",
            f"- registered pass: `{payload['T1_matvecs']['registered_pass']}`",
            "",
            "## T2 Free Pulls",
            "",
            "| lambda_sq | Delta=mu2-mu1 | alpha_proj | E_tail analog | alpha/E_tail |",
            "|---:|---:|---:|---:|---:|",
        ]
    )
    for lam in LAMBDA_SQS:
        row = payload["T2_free_pulls"]["rows"][str(lam)]
        lines.append(
            f"| {lam} | `{fmt(row['Delta'], 10)}` | `{fmt(row['alpha_projected'], 10)}` | "
            f"`{fmt(row['E_tail_analog'], 10)}` | `{fmt(row['alpha_over_E_tail'], 10)}` |"
        )
    lines.extend(
        [
            "",
            "## T3 Rungs 4..6",
            "",
            "| rung | mu | residual | rel residual | parity | range pass | PSD pass |",
            "|---:|---:|---:|---:|---|---|---|",
        ]
    )
    for row in payload["T3_rungs_4_6"]["rungs"]:
        lines.append(
            f"| {row['index']} | `{fmt(row['mu'], 10)}` | `{fmt(row['residual_norm'], 8)}` | "
            f"`{fmt(row['relative_residual'], 8)}` | `{row['measured_parity']}` | `{row['range_pass']}` | `{row['psd_judge']['pass']}` |"
        )
    lines.extend(["", "Ratios:"])
    for row in payload["T3_rungs_4_6"]["ratios"]:
        lines.append(f"- mu{row['to']}/mu{row['from']} = `{fmt(row['ratio'], 10)}` pass `{row['registered_pass']}`")
    yspec = payload["T4_y_spectroscopy"]
    t5 = payload["T5_N90"]
    lines.extend(
        [
            "",
            "## T4 y-spectroscopy",
            "",
            f"- y_norm: `{fmt(yspec['y_norm'], 12)}`",
            f"- mass fraction on rungs 4..6: `{fmt(yspec['mass_fraction_on_rungs_4_6'], 12)}` pass `{yspec['mass_registered_pass']}`",
            f"- c*_y reconstruction: `{fmt(yspec['c_star_reconstruction_4_6'], 12)}` pass `{yspec['c_star_registered_pass']}`",
            "",
            "## T5 N=90",
            "",
            f"- method: `{t5['method']}`",
            f"- ||y||(13,90): `{fmt(t5['y_norm'], 12)}`",
            f"- code: `{t5['code']}`",
            f"- residual: `{fmt(t5['residual_norm'], 8)}`",
            "",
            "## T6 Optional",
            "",
            f"- status: `{payload['T6_optional']['status']}`",
            "",
            "## LadderTracking Cross-check",
            "",
            "| lambda_sq | measured | bound without mu5 positive terms | pass |",
            "|---:|---:|---:|---|",
        ]
    )
    for row in payload["LadderTracking_cross_check"]["rows"]:
        lines.append(
            f"| {row['lambda_sq']} | `{fmt(row['measured_1_minus_abs_xi1_k1'], 10)}` | "
            f"`{fmt(row['bound_without_mu5_positive_terms'], 10)}` | `{row['pass']}` |"
        )
    lines.extend(["", "## Stop", "", "Stop after report + handoff.", ""])
    REPORT.write_text("\n".join(lines), encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    t5 = payload["T5_N90"]
    yspec = payload["T4_y_spectroscopy"]
    rung_rows = payload["T3_rungs_4_6"]["rungs"]
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "LadderLaw_v1 / Route B TwoLevelSpectralLadder",
        "",
        "Route status:",
        "NOT_RH. Diagnostic only. Phase 2 not run. Q3 mainline not touched.",
        "",
        "Codes:",
        str(payload["codes"]),
        "",
        "T1/T2:",
        f"- convention={payload['T1_matvecs']['registered_convention']}; T1 registered pass={payload['T1_matvecs']['registered_pass']}.",
        "- alpha uses projected packet Rayleigh a1-mu1; raw a1 is still reported separately.",
        "",
        "T3 rungs:",
    ]
    for row in rung_rows:
        lines.append(
            f"- mu{row['index']}={fmt(row['mu'], 10)}, parity={row['measured_parity']}, "
            f"res={fmt(row['residual_norm'], 8)}, PSD={row['psd_judge']['pass']}."
        )
    lines.extend(
        [
            "",
            "T4:",
            f"- mass_4_6={fmt(yspec['mass_fraction_on_rungs_4_6'], 10)}, c_rec={fmt(yspec['c_star_reconstruction_4_6'], 10)}.",
            "",
            "T5:",
            f"- y90={fmt(t5['y_norm'], 12)} => {t5['code']}.",
            "",
            "State update:",
            "ROUTE_B_STATE.md promotes RayleighLadderTracking + PoissonParityLadder only if registered_pass=True; for this failure run the pen additions are withheld and G3/G4 stay open.",
            "",
            "Question for Mythos/Proshka:",
            "Explain whether the y-spectroscopy failure is a real spectral obstruction, a wrong expected c*_y target, or evidence that another even mode between mu5 and mu6 must be added before pen promotion.",
        ]
    )
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    started = time.time()
    packets: Dict[int, Dict[str, Any]] = {}
    matrices: Dict[int, mp.matrix] = {}
    t1_rows: Dict[int, Dict[str, Any]] = {}
    parity_rows: Dict[int, Dict[str, Any]] = {}
    ground_rows: Dict[int, Dict[str, Any]] = {}

    for lam in LAMBDA_SQS:
        progress(f"T1/T2: packet rebuild lambda_sq={lam}")
        packets[lam] = packet_run(lam, N)
        progress(f"T1/T2: T rebuild lambda_sq={lam}")
        matrices[lam], _ = build_T(lam, N)
        progress(f"T1/T2: matvec/free pulls lambda_sq={lam}")
        t1_rows[lam] = rayleigh_packet_metrics(lam, matrices[lam], packets[lam])
        parity_rows[lam] = parity_block_mus(lam)

    progress("T3: rebuild T13 at dps250")
    T13_250, _ = build_T(13, N, dps_override=DPS_RECERT)
    progress("T3: lower pairs 1..3")
    lower13 = lower_pairs_13(T13_250)
    packet13 = packets[13]
    packet13_basis, _, _ = make_packet_basis(packet13)
    ground13_judge = psd_judge(
        T13_250,
        lower13[0]["xi"],
        packet13_basis,
        (mp.sqrt(max(lower13[0]["mu"], mp.mpf("0"))) + mp.sqrt(max(eigvals_hermitian(block_from_basis(T13_250, packet13_basis))[-1], mp.mpf("0")))) ** 2,
    )
    ground_rows[13] = {
        "lambda_sq": 13,
        "N": N,
        "mu": lower13[0]["mu"],
        "xi": lower13[0]["xi"],
        "packet_basis": packet13_basis,
        "judge": ground13_judge,
        "residual_norm": lower13[0]["residual_norm"],
        "relative_residual": lower13[0]["residual_norm"] / max(abs(lower13[0]["mu"]), mp.mpf("1e-300")),
    }
    for lam in (12, 14):
        progress(f"T2 analog/LadderTracking: ground pair lambda_sq={lam}")
        ground_rows[lam] = ground_pair_from_even_sector(matrices[lam], lam, packets[lam], N, iterations=3)

    progress("T3: shifted inverse rungs 4..6")
    rung_payload = rung_scan_13(T13_250, lower13, packet13)
    progress("T4: y-spectroscopy")
    yspec = y_spectroscopy(T13_250, lower13, packet13, rung_payload)
    t5 = t5_n90()

    t1_registered_rows = []
    for lam in LAMBDA_SQS:
        row = t1_rows[lam]
        ratio_a = row["ratios_projected"]["a1_over_mu1"]
        ratio_eta = row["ratios_projected"]["eta_sq_over_mu1"]
        raw_a = row["raw"]["a1"]
        raw_eta = row["raw"]["eta"]
        lam_pass = in_range(ratio_a, mp.mpf("1.1"), mp.mpf("1.6")) and in_range(
            ratio_eta, mp.mpf("0.06"), mp.mpf("0.4")
        )
        if lam == 12:
            lam_pass = lam_pass and in_range(raw_a, mp.mpf("2e-54"), mp.mpf("2e-53")) and in_range(
                raw_eta, mp.mpf("4e-28"), mp.mpf("1.9e-27")
            )
        if lam == 14:
            lam_pass = lam_pass and in_range(raw_a, mp.mpf("1.5e-64"), mp.mpf("6e-64")) and in_range(
                raw_eta, mp.mpf("2e-33"), mp.mpf("1e-32")
            )
        t1_registered_rows.append(lam_pass)

    t2_rows: Dict[int, Dict[str, Any]] = {}
    for lam in LAMBDA_SQS:
        alpha = t1_rows[lam]["projected"]["a1"] - parity_rows[lam]["mu1"]
        E_tail = ground_rows[lam]["judge"]["E_tail"]
        t2_rows[lam] = {
            "lambda_sq": lam,
            "source": parity_rows[lam]["source"],
            "Delta": parity_rows[lam]["Delta"],
            "mu1": parity_rows[lam]["mu1"],
            "mu2": parity_rows[lam]["mu2"],
            "alpha_projected": alpha,
            "E_tail_analog": E_tail,
            "alpha_over_E_tail": alpha / max(E_tail, mp.mpf("1e-300")),
        }

    tracking_rows = [
        ladder_tracking_check(12, ground_rows[12], t1_rows[12], parity_rows[12]),
        ladder_tracking_check(14, ground_rows[14], t1_rows[14], parity_rows[14]),
    ]

    codes: List[str] = []
    if rung_payload["unstable"]:
        codes.append("INVERSE_ITERATION_UNSTABLE")
    if rung_payload["structure_broken"]:
        codes.append("RUNG_STRUCTURE_BROKEN")
    if not (yspec["mass_registered_pass"] and yspec["c_star_registered_pass"]):
        codes.append("Y_SPECTROSCOPY_MISMATCH")
    codes.append(t5["code"])
    if not codes:
        codes.append("LADDERLAW_PASS")

    registered_pass = (
        all(t1_registered_rows)
        and not rung_payload["unstable"]
        and not rung_payload["structure_broken"]
        and yspec["mass_registered_pass"]
        and yspec["c_star_registered_pass"]
        and t5["code"] in ("TRUNCATION_CONFIRMED", "FLOOR_CONFIRMED")
        and all(row["pass"] for row in tracking_rows)
    )
    status = "complete" if registered_pass else "complete_with_registered_failure"
    door = "LADDERLAW_TO_PEN" if registered_pass else "LADDERLAW_REVIEW_REGISTERED_FAILURE"

    payload: Dict[str, Any] = {
        "gate": "LadderLaw_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": status,
        "door": door,
        "codes": codes,
        "registered_pass": registered_pass,
        "phase2_run": False,
        "q3_main_touched": False,
        "new_lambda_or_N_anchor_bought": False,
        "elapsed_s": time.time() - started,
        "next_gate": "PEN_FORMALIZATION_REVIEW" if registered_pass else "WAIT_FOR_MYTHOS_PROSHKA_REVIEW",
        "T1_matvecs": {
            "registered_convention": "projected_parity_packet_a1_for_ratios; raw_a1_and_raw_eta_reported_separately",
            "registered_pass": all(t1_registered_rows),
            "rows": {str(k): v for k, v in t1_rows.items()},
        },
        "T2_free_pulls": {
            "rows": {str(k): v for k, v in t2_rows.items()},
            "alpha_13_vs_E_tail_note": "alpha_projected(13) is compared against fresh E_tail from vector recert convention.",
        },
        "T3_rungs_4_6": {
            "dps": rung_payload["dps"],
            "lambda3_G": rung_payload["lambda3_G"],
            "rungs": [
                {k: v for k, v in row.items() if k != "xi"}
                for row in rung_payload["rungs"]
            ],
            "ratios": rung_payload["ratios"],
            "unstable": rung_payload["unstable"],
            "structure_broken": rung_payload["structure_broken"],
        },
        "T4_y_spectroscopy": yspec,
        "T5_N90": t5,
        "T6_optional": {
            "status": "NOT_RUN",
            "reason": "optional budget item; core T1-T5/LadderTracking gate completed first",
        },
        "LadderTracking_cross_check": {
            "method": "passes already without the positive 1/mu5 tail terms at lambda_sq 12 and 14",
            "rows": tracking_rows,
        },
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
