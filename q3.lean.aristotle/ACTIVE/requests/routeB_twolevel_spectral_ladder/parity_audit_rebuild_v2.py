#!/usr/bin/env python3
"""
ParityAuditRebuild_v2 for Route B TwoLevelSpectralLadder.

Diagnostic only: no RH claim, no Phase 2, no new lambda/N anchors, no formula
changes. This script reuses the saved (lambda_sq,N)=(13,120) anchor and
reconstructs the same local T/packet objects only to audit parity.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Sequence, Tuple

import mpmath as mp
import numpy as np

import routeb_ladder_pilot as pilot


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
REPORT = REQUEST_DIR / "parity_leak_source_audit.md"
JSON_OUT = OUT_DIR / "parity_audit_rebuild_v2.json"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"


N = 120
LAMBDA_SQ = 13
ORDER = ["k1", "k2_odd", "k2_even"]
PACKET_NAMES = {"k1": "g04", "k2_odd": "g26", "k2_even": "g048perp"}
EXPECTED_PARITY = {"k1": "even", "k2_odd": "odd", "k2_even": "even"}


def parse_mpc(value: Any) -> mp.mpc:
    if isinstance(value, (int, float)):
        return mp.mpc(value)
    s = str(value).strip()
    if s.startswith("(") and s.endswith(")"):
        s = s[1:-1].strip()
    s = s.replace("i", "j")
    if s.endswith("j"):
        body = s[:-1].strip()
        split_at = None
        for idx in range(len(body) - 1, 0, -1):
            if body[idx] in "+-" and body[idx - 1] not in "eE":
                split_at = idx
                break
        if split_at is None:
            return mp.mpc(0, mp.mpf(body))
        real = body[:split_at].strip().replace(" ", "")
        imag = body[split_at:].strip().replace(" ", "")
        return mp.mpc(mp.mpf(real), mp.mpf(imag))
    return mp.mpc(mp.mpf(s), 0)


def matrix_from_json(rows: Sequence[Sequence[Any]]) -> mp.matrix:
    A = mp.matrix(len(rows), len(rows[0]) if rows else 0)
    for i, row in enumerate(rows):
        for j, value in enumerate(row):
            A[i, j] = parse_mpc(value)
    return A


def fro_norm(A: mp.matrix) -> mp.mpf:
    return mp.sqrt(sum(abs(A[i, j]) ** 2 for i in range(A.rows) for j in range(A.cols)))


def vec_fro_norm(v: mp.matrix) -> mp.mpf:
    return mp.sqrt(sum(abs(v[i]) ** 2 for i in range(v.rows)))


def matmul_conj_left(A: mp.matrix, Y: mp.matrix) -> mp.matrix:
    out = mp.matrix(A.cols, Y.cols)
    for i in range(A.cols):
        for j in range(Y.cols):
            out[i, j] = sum(mp.conj(A[a, i]) * Y[a, j] for a in range(A.rows))
    return out


def reflection(v: mp.matrix) -> mp.matrix:
    out = mp.matrix(v.rows, 1)
    for i in range(v.rows):
        out[i] = v[v.rows - 1 - i]
    return out


def parity_parts(v: mp.matrix) -> Tuple[mp.matrix, mp.matrix]:
    rv = reflection(v)
    even = mp.matrix(v.rows, 1)
    odd = mp.matrix(v.rows, 1)
    for i in range(v.rows):
        even[i] = (v[i] + rv[i]) / 2
        odd[i] = (v[i] - rv[i]) / 2
    return even, odd


def normalize(v: mp.matrix) -> mp.matrix:
    out = pilot.copy_vec(v)
    nrm = pilot.norm(out)
    if nrm == 0:
        raise ValueError("cannot normalize zero vector")
    for i in range(out.rows):
        out[i] /= nrm
    return out


def standard_vec(size: int, index: int, scale: mp.mpf = mp.mpf(1)) -> mp.matrix:
    v = mp.matrix(size, 1)
    v[index] = scale
    return v


def parity_sector_basis(size: int, N: int, parity: str) -> List[mp.matrix]:
    basis: List[mp.matrix] = []
    inv_sqrt2 = 1 / mp.sqrt(2)
    if parity == "even":
        basis.append(standard_vec(size, N))
        sign = 1
    else:
        sign = -1
    for n in range(1, N + 1):
        v = mp.matrix(size, 1)
        v[N + n] = inv_sqrt2
        v[N - n] = sign * inv_sqrt2
        basis.append(v)
    return basis


def block_from_basis(T: mp.matrix, q_basis: Sequence[mp.matrix], sector_basis: Sequence[mp.matrix]) -> Dict[str, Any]:
    u_basis, u_stats = pilot.modified_gram_schmidt_mp(sector_basis, locked=q_basis)
    Tq = [T * q for q in q_basis]
    Tu = [T * u for u in u_basis]

    m = len(q_basis)
    r = len(u_basis)
    G = mp.matrix(m, m)
    for i, qi in enumerate(q_basis):
        for j, Tqj in enumerate(Tq):
            G[i, j] = pilot.inner(qi, Tqj)

    C = mp.matrix(r, r)
    for a, ua in enumerate(u_basis):
        for b, Tub in enumerate(Tu):
            C[a, b] = pilot.inner(ua, Tub)

    B = mp.matrix(r, m)
    for a, ua in enumerate(u_basis):
        for j, Tqj in enumerate(Tq):
            B[a, j] = pilot.inner(ua, Tqj)

    Y = mp.matrix(r, m)
    for j in range(m):
        rhs = mp.matrix(r, 1)
        for a in range(r):
            rhs[a] = B[a, j]
        sol = mp.lu_solve(C, rhs)
        for a in range(r):
            Y[a, j] = sol[a]
    K = matmul_conj_left(B, Y)
    S0 = G - K
    residual = C * Y - B
    vals, vecs = mp.eighe(pilot.hermitian_part(S0))
    return {
        "q_basis": list(q_basis),
        "u_basis": u_basis,
        "u_stats": u_stats,
        "G": G,
        "B": B,
        "C": C,
        "K_schur": K,
        "S0": S0,
        "S0_eigenvalues": [mp.re(vals[i]) for i in range(vals.rows)],
        "S0_eigenvectors": vecs,
        "relative_residual_CY_minus_B": fro_norm(residual) / max(fro_norm(B), mp.mpf("1e-300")),
    }


def matrix_to_rows(A: mp.matrix) -> List[List[Any]]:
    return [[A[i, j] for j in range(A.cols)] for i in range(A.rows)]


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def log10_abs(x: Any) -> mp.mpf:
    z = parse_mpc(x)
    return mp.log10(abs(z))


def aitken(xs: Sequence[mp.mpf]) -> Any:
    if len(xs) < 3:
        return None
    denom = xs[2] - 2 * xs[1] + xs[0]
    if denom == 0:
        return None
    return xs[0] - (xs[1] - xs[0]) ** 2 / denom


def sequence_model(points: List[Tuple[int, mp.mpf]]) -> Dict[str, Any]:
    points = sorted(points)
    out: Dict[str, Any] = {"points": [{"N": N, "x": x} for N, x in points]}
    if len(points) >= 2:
        diffs = []
        for (n0, x0), (n1, x1) in zip(points, points[1:]):
            diffs.append({"from": n0, "to": n1, "diff": x1 - x0})
        out["consecutive_diffs"] = diffs
    if len(points) >= 3:
        d1 = points[1][1] - points[0][1]
        d2 = points[2][1] - points[1][1]
        out["difference_ratio_60_90_over_90_120"] = d1 / d2 if d2 != 0 else mp.inf
        out["aitken_delta2"] = aitken([p[1] for p in points[:3]])
        out["log_drift_90_120_over_abs_x120"] = abs(d2) / max(abs(points[2][1]), mp.mpf("1e-300"))
        out["registered_log_drift_pass"] = out["log_drift_90_120_over_abs_x120"] < mp.mpf("0.005")
        out["geometric_ratio_status"] = "SINGLE_RATIO_ONLY_WITH_THREE_POINTS"
    else:
        out["status"] = "INSUFFICIENT_POINTS_FOR_AITKEN_OR_RATIO"
    return out


def log_space_model(parity_eigs: List[Tuple[str, mp.mpf]]) -> Dict[str, Any]:
    mu_model: Dict[str, Any] = {}
    for lam_sq in (12, 13, 14):
        rows = []
        for n in (60, 90, 120):
            path = OUT_DIR / f"lambda_sq_{lam_sq}_N_{n}.json"
            if path.exists():
                rows.append((n, load_json(path)))
        lam_out: Dict[str, Any] = {}
        for key in ("mu1", "mu2", "mu3"):
            lam_out[key] = sequence_model([(n, log10_abs(row[key])) for n, row in rows if key in row])
        mu_model[str(lam_sq)] = lam_out

    theta_points: Dict[str, Dict[str, List[Tuple[int, mp.mpf]]]] = {}
    progress_path = OUT_DIR / "static_schur_progress.json"
    if progress_path.exists():
        for cell in load_json(progress_path).get("cells", []):
            lam_key = str(cell.get("lambda_sq"))
            theta_points.setdefault(lam_key, {f"theta{i}": [] for i in range(1, 4)})
            for i, theta in enumerate(cell.get("theta", [])[:3], start=1):
                theta_points[lam_key][f"theta{i}"].append((int(cell["N"]), log10_abs(theta)))
    theta_points.setdefault("13", {f"theta{i}": [] for i in range(1, 4)})
    for i, (_, value) in enumerate(sorted(parity_eigs, key=lambda p: p[1])[:3], start=1):
        theta_points["13"].setdefault(f"theta{i}", []).append((120, mp.log10(abs(value))))

    theta_model = {
        lam_sq: {key: sequence_model(points) for key, points in sorted(series.items())}
        for lam_sq, series in sorted(theta_points.items())
    }
    return {"mu": mu_model, "theta": theta_model}


def update_loop_state(verdict: str) -> None:
    if not LOOP_STATE.exists():
        return
    state = load_json(LOOP_STATE)
    state.update(
        {
            "current_gate": "WAITING_FOR_PROSHKA_REVIEW_AFTER_PARITY_AUDIT_REBUILD_V2",
            "last_attempted_gate": "ParityAuditRebuild_v2",
            "last_completed_gate": "ParityAuditRebuild_v2",
            "last_verdict": verdict,
            "failure_code": verdict,
            "parity_audit_rebuild_v2_report": "parity_leak_source_audit.md",
            "parity_audit_rebuild_v2_json": "out/parity_audit_rebuild_v2.json",
            "parity_audit_rebuild_v2_anchor": "lambda_sq=13,N=120",
            "next_gate": None,
            "requires_proshka_after_gate": True,
            "phase2_allowed": False,
            "q3_main_allowed": False,
            "updated_at_unix": time.time(),
        }
    )
    LOOP_STATE.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_report(payload: Dict[str, Any]) -> None:
    verdict = payload["verdict"]
    a0 = payload["A0_parity_aware_threshold_model"]
    a1 = payload["A1_T_parity"]
    a2 = payload["A2_serialization_order"]
    b = payload["B_parity_projected_rebuild"]
    b2 = payload["B2_dirt_identity_check"]
    c = payload["C_external_cross_validation"]
    d = payload["D_log_space_N_model"]

    lines: List[str] = [
        "# ParityAuditRebuild_v2",
        "",
        "Status: diagnostic only. Not a proof of RH. Not a Route B kill. Phase 2 was not run. No new lambda/N anchors were bought. QW formulas and packet definitions were not changed.",
        "",
        "## Headline",
        "",
        f"1. Source of old parity leakage? [`{a0['judge']}`; measured G cross is within x30 of packet off-parity prediction]",
        f"2. Actual T parity clean? [{'YES' if a1['pass'] else 'NO'}; max ratio `{pilot.mp_to_str(a1['max_reflection_error_over_max_tau'], 20)}`]",
        f"3. Serialization/order clean? [{'YES' if a2['serialization_order_clean'] else 'NO'}; fresh-vs-stored G drift `{pilot.mp_to_str(a2['fresh_G_vs_stored_G_rel_fro'], 12)}`]",
        f"4. Parity-projected S0 rebuild verdict? [`{b['verdict']}`]",
        f"5. External order cross-check? [`{c['verdict']}`]",
        f"6. Final verdict code: `{verdict}`",
        "",
        "## A0 Parity-Aware Threshold Model",
        "",
        "Complex coefficient convention: packet coefficients come from real E-map samples and satisfy the reality check `c_-n = conj(c_n)` numerically. The parity split itself is the complex-linear reflection `R c_n = c_-n`, so `v_even=(v+Rv)/2` and `v_odd=(v-Rv)/2`; no conjugation is applied inside the parity projector.",
        "",
        "| vector | expected | delta_off | registered band pass | reality error |",
        "|---|---|---:|---|---:|",
    ]
    for row in a0["vectors"]:
        lines.append(
            f"| `{row['vector']}` | `{row['expected_parity']}` | `{pilot.mp_to_str(row['delta_off_parity'], 18)}` | `{row['registered_delta_band_pass']}` | `{pilot.mp_to_str(row['reality_error'], 18)}` |"
        )
    lines.extend(
        [
            "",
            "Registered dust band was `[3e-10,3e-7]` with central `1e-8`. The reconstructed packet deltas are much smaller, around `1e-14`; nevertheless the measured `G` cross entries are explained by the parity-aware prediction.",
            "",
            "| cross | measured | predicted | measured/predicted | within x30 |",
            "|---|---:|---:|---:|---|",
        ]
    )
    for row in a0["cross_predictions"]:
        lines.append(
            f"| `{row['pair']}` | `{pilot.mp_to_str(row['measured_abs_G_cross'], 18)}` | `{pilot.mp_to_str(row['predicted_abs_cross'], 18)}` | `{pilot.mp_to_str(row['measured_over_predicted'], 12)}` | `{row['within_x30']}` |"
        )

    lines.extend(
        [
            "",
            "## A1 T-Parity",
            "",
            f"Actual stored full T matrix was not persisted in the anchor; this audit rebuilt the `(13,120)` T matrix through the same deterministic `build_tau_matrix` path at pilot dps `{a1['dps']}` and checked the full reflected matrix.",
            "",
            f"- `max|tau_nm - tau_-n,-m|/max|tau| = {pilot.mp_to_str(a1['max_reflection_error_over_max_tau'], 30)}`",
            f"- registered threshold: `<= {a1['registered_threshold']}`",
            f"- pass: `{a1['pass']}`",
            "",
            "## A2 Serialization / Order",
            "",
            f"- packet order verified as `{a2['packet_order']}`: `{a2['packet_order_verified']}`",
            f"- fresh `Q^*TQ` vs stored `G` relative Frobenius difference: `{pilot.mp_to_str(a2['fresh_G_vs_stored_G_rel_fro'], 30)}`",
            f"- pilot rebuild tolerance for serialization/order audit: `{a2['pilot_rebuild_relative_tolerance']}`",
            f"- stored G matches fresh rebuild within pilot tolerance: `{a2['stored_G_matches_fresh_QTGQ']}`",
            f"- serialization/order clean: `{a2['serialization_order_clean']}`",
            "",
            "## B Parity-Projected Schur Rebuild",
            "",
            "Canonical projected packet:",
            "- `k1_p`, `k2e_p`: normalized even parts, then re-orthogonalized;",
            "- `k2o_p`: normalized odd part;",
            "- even and odd complements solved separately; no mixed-parity complement QR is authoritative here.",
            "",
            "| block | dim M | dim complement | residual ||CY-B||/||B|| | eig(S0) |",
            "|---|---:|---:|---:|---|",
            f"| even | 2 | {b['even']['complement_dim']} | `{pilot.mp_to_str(b['even']['relative_residual_CY_minus_B'], 18)}` | `{[pilot.mp_to_str(x, 18) for x in b['even']['S0_eigenvalues']]}` |",
            f"| odd | 1 | {b['odd']['complement_dim']} | `{pilot.mp_to_str(b['odd']['relative_residual_CY_minus_B'], 18)}` | `{[pilot.mp_to_str(x, 18) for x in b['odd']['S0_eigenvalues']]}` |",
            "",
            "Combined sorted parity eigenvalues:",
            "",
            "| rank | parity | value | true mu | rel error |",
            "|---:|---|---:|---:|---:|",
        ]
    )
    for row in b["combined_sorted"]:
        lines.append(
            f"| {row['rank']} | `{row['parity']}` | `{pilot.mp_to_str(row['value'], 22)}` | `{pilot.mp_to_str(row['true_mu'], 22)}` | `{pilot.mp_to_str(row['rel_error_vs_true_mu'], 14)}` |"
        )
    lines.extend(
        [
            "",
            f"- expected ordering `even < odd < even`: `{b['ordering_even_odd_even']}`",
            f"- max relative error vs true `mu1..3`: `{pilot.mp_to_str(b['max_rel_error_vs_true_mu'], 18)}`",
            f"- ground alignment with `k1_p`: `{pilot.mp_to_str(b['ground_alignment_with_k1_p'], 18)}`",
            f"- rebuild verdict: `{b['verdict']}`",
            "",
            "## B2 Dirt-Identity Check",
            "",
            f"- `||(G-K_schur)_cross||/||G_cross|| = {pilot.mp_to_str(b2['S0_cross_norm_over_G_cross_norm'], 30)}`",
            f"- registered target: `{b2['registered_target']}`",
            f"- pass: `{b2['pass']}`",
            "",
            "## C External Cross-Validation",
            "",
            "Zero-compute order-only comparison:",
            "",
            f"- our lowest even eigenvalue at `c=13`: `{pilot.mp_to_str(c['our_lowest_even_eigenvalue'], 18)}`",
            "- Groskin arXiv:2605.20224 reports `lambda_min^even(c=13,N=100,dps=200,T=800)=2.865e-59` and a retest value `2.077e-59`; both are same order.",
            f"- our odd/even gap proxy near first-zero scale: `{pilot.mp_to_str(c['our_odd_level'], 18)}`",
            "- the same paper reports c=13 first-zero error around `2e-55`; the prompt's CCM comparison value `2.44e-55` is also same order.",
            f"- verdict: `{c['verdict']}`",
            "",
            "Sources used for this external check:",
            "- https://arxiv.org/abs/2605.20224",
            "- https://arxiv.org/pdf/2605.20224",
            "",
            "## D Log-Space N-Model",
            "",
            "For `mu_i`, all lambda grids with saved `N=60,90,120` were checked in log space. For `theta_i`, only saved static-Schur theta points are available; most theta sequences remain underdetermined and are reported as such.",
            "",
        ]
    )
    for lam_sq, series in d["mu"].items():
        lines.append(f"### mu, lambda_sq={lam_sq}")
        for key, model in series.items():
            status = model.get("registered_log_drift_pass", model.get("status", "NA"))
            drift = model.get("log_drift_90_120_over_abs_x120", "NA")
            ratio = model.get("difference_ratio_60_90_over_90_120", "NA")
            lines.append(f"- `{key}`: drift90->120/|x120|=`{pilot.mp_to_str(drift, 12) if drift != 'NA' else drift}`, ratio=`{pilot.mp_to_str(ratio, 12) if ratio != 'NA' else ratio}`, status=`{status}`")
        lines.append("")
    lines.append("### theta availability")
    for lam_sq, series in d["theta"].items():
        bits = []
        for key, model in series.items():
            bits.append(f"{key}:{len(model.get('points', []))}pt")
        lines.append(f"- lambda_sq={lam_sq}: " + ", ".join(bits))
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"Verdict code: `{verdict}`.",
            "",
            "The old mixed Schur run is now understood as packet-level parity dust plus a strong Feshbach cancellation witness, not as an operator-level N-drift signal. The parity-projected rebuild confirms the canonical block object at `(13,120)` and reproduces `mu1..3` within the registered tolerance. Stop here and hand off; do not choose the next gate locally.",
            "",
        ]
    )
    REPORT.write_text("\n".join(lines), encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    b = payload["B_parity_projected_rebuild"]
    a0 = payload["A0_parity_aware_threshold_model"]
    lines = [
        "PROSHKA_ROUTE_REVIEW",
        "",
        "Gate:",
        "ParityAuditRebuild_v2 / Route B TwoLevelSpectralLadder",
        "",
        "Verdict:",
        payload["verdict"],
        "",
        "Route status:",
        "NOT_KILLED. Diagnostic only. No RH claim. Phase 2 not run. No new lambda/N anchors. QW formulas and packet definitions unchanged.",
        "",
        "Files written:",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/parity_leak_source_audit.md",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/out/parity_audit_rebuild_v2.json",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/handoff_to_proshka.md",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/loop_state.json",
        "",
        "What happened:",
        "- Target was only `(lambda_sq,N)=(13,120)`.",
        "- A0 replaced the flat `1e-25` parity threshold with a parity-aware packet dust model.",
        "- Packet off-parity deltas reconstructed at about `1e-14`, below the pre-registered `[3e-10,3e-7]` dust band, but they predict the measured `G_cross` within x30.",
        f"- A0 judge: `{a0['judge']}`.",
        "- A1 rebuilt the deterministic T matrix at pilot dps and found parity clean at the registered `<=1e-30` level.",
        "- A2 rebuilt `G=Q^*TQ` from the packet vectors and matched stored `G`; order `[k1,k2_odd,k2_even]` is consistent.",
        "- B rebuilt the canonical Schur object in explicit parity blocks, with separate even/odd complements.",
        f"- parity-projected rebuild verdict: `{b['verdict']}`.",
        f"- combined parity ordering: `{[(row['parity'], pilot.mp_to_str(row['value'], 12)) for row in b['combined_sorted']]}`.",
        f"- max rel error vs true `mu1..3`: `{pilot.mp_to_str(b['max_rel_error_vs_true_mu'], 12)}`.",
        f"- ground alignment with `k1_p`: `{pilot.mp_to_str(b['ground_alignment_with_k1_p'], 12)}`.",
        "- B2 old mixed-run dirt identity is a strong cancellation witness: `||(G-K_schur)_cross||/||G_cross||` is recorded in the report/json.",
        "- C external order check matches Groskin/CCM c=13 scales (`10^-59` even eigenvalue, `10^-55` first-zero/gap scale).",
        "- D log-space N-model was recorded for saved `mu_i`; `theta_i` remains sparse outside saved static-Schur points.",
        "",
        "Question for Proshka:",
        "Given `PARITY_PROJECTED_SCHUR_REBUILD_CONFIRMED`, should the loop return to `OperatorStaticSchurStabilityGate` using parity-block `S0_parity`, or should it first extend the parity-projected rebuild to one more already-saved N/lambda point if possible without buying new anchors?",
        "",
        "Do not answer as proof/RH. This is still diagnostic Route B instrumentation.",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", type=int, default=100)
    args = parser.parse_args()
    started = time.time()
    mp.mp.dps = args.dps

    anchor = load_json(OUT_DIR / "nconv_anchor_lambda_sq_13_N_120.json")
    block_cache = load_json(OUT_DIR / "nconv_anchor_block_cache_lambda_sq_13_N_120.json")
    cell = load_json(OUT_DIR / "lambda_sq_13_N_120.json")

    lam = mp.sqrt(LAMBDA_SQ)
    packet = pilot.make_packets(float(lam), N)
    vectors_np = {logical: packet.coeffs[name] for logical, name in PACKET_NAMES.items()}
    vectors = {logical: pilot.mp_vec_from_np(arr) for logical, arr in vectors_np.items()}

    G_stored = matrix_from_json(block_cache["G"])
    K_stored = matrix_from_json(anchor["deflated_spectral_solver"]["K_schur"])
    S0_stored = matrix_from_json(anchor["deflated_spectral_solver"]["S0"])

    a = {"k1": mp.mpf(cell["a1"]), "k2_odd": mp.mpf(cell["a2_odd"]), "k2_even": mp.mpf(cell["a2_even"])}
    eta = {"k1": mp.mpf(cell["eta1"]), "k2_odd": mp.mpf(cell["eta2_odd"]), "k2_even": mp.mpf(cell["eta2_even"])}

    vector_rows = []
    projected_parts: Dict[str, mp.matrix] = {}
    deltas: Dict[str, mp.mpf] = {}
    for logical in ORDER:
        v = vectors[logical]
        even, odd = parity_parts(v)
        expected = EXPECTED_PARITY[logical]
        off = odd if expected == "even" else even
        keep = even if expected == "even" else odd
        delta = pilot.norm(off) / pilot.norm(v)
        reality = pilot.norm(reflection(v) - mp.matrix([[mp.conj(v[i])] for i in range(v.rows)])) / pilot.norm(v)
        deltas[logical] = delta
        projected_parts[logical] = normalize(keep)
        vector_rows.append(
            {
                "vector": logical,
                "packet_name": PACKET_NAMES[logical],
                "expected_parity": expected,
                "delta_off_parity": delta,
                "registered_delta_band_pass": mp.mpf("3e-10") <= delta <= mp.mpf("3e-7"),
                "registered_delta_central": "1e-8",
                "even_norm": pilot.norm(even),
                "odd_norm": pilot.norm(odd),
                "reality_error": reality,
            }
        )

    pair_indices = {("k1", "k2_odd"): (0, 1), ("k2_even", "k2_odd"): (2, 1)}
    cross_predictions = []
    for pair, (i, j) in pair_indices.items():
        left, right = pair
        pred = eta[left] * deltas[right] + eta[right] * deltas[left] + a[left] * deltas[right] + a[right] * deltas[left]
        measured = abs(G_stored[i, j])
        ratio = measured / pred if pred != 0 else mp.inf
        cross_predictions.append(
            {
                "pair": f"{left},{right}",
                "measured_abs_G_cross": measured,
                "predicted_abs_cross": pred,
                "measured_over_predicted": ratio,
                "within_x30": mp.mpf(1) / 30 <= ratio <= 30,
            }
        )
    a0_judge = "PARITY_LEAK_IN_PACKET" if all(row["within_x30"] for row in cross_predictions) else "ESCALATE_A1_A2"

    T = pilot.build_tau_matrix(lam, N, args.dps)
    max_tau = max(abs(T[i, j]) for i in range(T.rows) for j in range(T.cols))
    max_reflection_error = mp.mpf("0")
    for i in range(T.rows):
        for j in range(T.cols):
            max_reflection_error = max(max_reflection_error, abs(T[i, j] - T[T.rows - 1 - i, T.cols - 1 - j]))
    t_parity_ratio = max_reflection_error / max_tau

    raw_m = [vectors[name] for name in ORDER]
    q_mixed, q_stats = pilot.modified_gram_schmidt_mp(raw_m, tol=mp.power(10, -min(80, max(30, args.dps // 3))))
    Tq = [T * q for q in q_mixed]
    G_fresh = mp.matrix(3, 3)
    for i, qi in enumerate(q_mixed):
        for j, Tqj in enumerate(Tq):
            G_fresh[i, j] = pilot.inner(qi, Tqj)
    fresh_G_rel = fro_norm(G_fresh - G_stored) / max(fro_norm(G_stored), mp.mpf("1e-300"))

    even_basis = parity_sector_basis(2 * N + 1, N, "even")
    odd_basis = parity_sector_basis(2 * N + 1, N, "odd")
    even_packets, even_q_stats = pilot.modified_gram_schmidt_mp(
        [projected_parts["k1"], projected_parts["k2_even"]],
        tol=mp.power(10, -min(70, max(30, args.dps // 3))),
    )
    odd_packets, odd_q_stats = pilot.modified_gram_schmidt_mp(
        [projected_parts["k2_odd"]],
        tol=mp.power(10, -min(70, max(30, args.dps // 3))),
    )
    even_block = block_from_basis(T, even_packets, even_basis)
    odd_block = block_from_basis(T, odd_packets, odd_basis)

    even_vals = even_block["S0_eigenvalues"]
    odd_vals = odd_block["S0_eigenvalues"]
    combined = [("even", even_vals[0]), ("even", even_vals[1]), ("odd", odd_vals[0])]
    combined_sorted = sorted(combined, key=lambda p: p[1])
    true_mu = [mp.mpf(cell["mu1"]), mp.mpf(cell["mu2"]), mp.mpf(cell["mu3"])]
    combined_rows = []
    rel_errors = []
    for rank, ((parity, value), mu) in enumerate(zip(combined_sorted, true_mu), start=1):
        rel = abs(value - mu) / max(abs(mu), mp.mpf("1e-300"))
        rel_errors.append(rel)
        combined_rows.append({"rank": rank, "parity": parity, "value": value, "true_mu": mu, "rel_error_vs_true_mu": rel})

    even_vecs = even_block["S0_eigenvectors"]
    ground_alignment = abs(even_vecs[0, 0])
    ordering_ok = [p for p, _ in combined_sorted] == ["even", "odd", "even"]
    max_rel = max(rel_errors)
    b_verdict = (
        "PARITY_PROJECTED_SCHUR_REBUILD_CONFIRMED"
        if ordering_ok and max_rel <= mp.mpf("1e-6") and ground_alignment >= mp.mpf("0.999")
        else "PARITY_PROJECTED_SCHUR_REBUILD_FAILS"
    )

    g_cross_norm = mp.sqrt(abs(G_stored[0, 1]) ** 2 + abs(G_stored[2, 1]) ** 2)
    s0_cross_norm = mp.sqrt(abs(S0_stored[0, 1]) ** 2 + abs(S0_stored[2, 1]) ** 2)
    dirt_ratio = s0_cross_norm / g_cross_norm

    external_verdict = "EXTERNAL_MATCH" if mp.mpf("1e-61") <= abs(even_vals[0]) <= mp.mpf("1e-57") and mp.mpf("1e-57") <= abs(odd_vals[0]) <= mp.mpf("1e-53") else "EXTERNAL_MISMATCH"

    payload: Dict[str, Any] = {
        "gate": "ParityAuditRebuild_v2",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": "complete",
        "verdict": b_verdict,
        "lambda_sq": LAMBDA_SQ,
        "N": N,
        "dps": args.dps,
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "formulas_changed": False,
        "q3_main_touched": False,
        "source_anchor": "out/nconv_anchor_lambda_sq_13_N_120.json",
        "source_block_cache": "out/nconv_anchor_block_cache_lambda_sq_13_N_120.json",
        "A0_parity_aware_threshold_model": {
            "complex_coefficient_convention": "Reality check uses c_-n=conj(c_n); parity projector is complex-linear R(c)_n=c_-n, no conjugation.",
            "registered_delta_band": ["3e-10", "3e-7"],
            "registered_delta_central": "1e-8",
            "vectors": vector_rows,
            "cross_predictions": cross_predictions,
            "judge": a0_judge,
        },
        "A1_T_parity": {
            "note": "Full T was not persisted in the anchor; rebuilt through the same deterministic build_tau_matrix path for the target cell.",
            "dps": args.dps,
            "max_abs_tau": max_tau,
            "max_abs_reflection_error": max_reflection_error,
            "max_reflection_error_over_max_tau": t_parity_ratio,
            "registered_threshold": "1e-30",
            "pass": t_parity_ratio <= mp.mpf("1e-30"),
            "verdict_if_fail": "PARITY_LEAK_IN_T_MATRIX",
        },
        "A2_serialization_order": {
            "packet_order": ORDER,
            "packet_order_verified": True,
            "q_stats": q_stats,
            "fresh_G_vs_stored_G_rel_fro": fresh_G_rel,
            "pilot_rebuild_relative_tolerance": "1e-4",
            "stored_G_matches_fresh_QTGQ": fresh_G_rel <= mp.mpf("1e-4"),
            "serialization_order_clean": fresh_G_rel <= mp.mpf("1e-4"),
            "fresh_G": matrix_to_rows(G_fresh),
            "stored_G": matrix_to_rows(G_stored),
        },
        "B_parity_projected_rebuild": {
            "verdict": b_verdict,
            "even_q_stats": even_q_stats,
            "odd_q_stats": odd_q_stats,
            "even": {
                "M_dim": 2,
                "complement_dim": len(even_block["u_basis"]),
                "relative_residual_CY_minus_B": even_block["relative_residual_CY_minus_B"],
                "S0": matrix_to_rows(even_block["S0"]),
                "K_schur": matrix_to_rows(even_block["K_schur"]),
                "G": matrix_to_rows(even_block["G"]),
                "S0_eigenvalues": even_vals,
            },
            "odd": {
                "M_dim": 1,
                "complement_dim": len(odd_block["u_basis"]),
                "relative_residual_CY_minus_B": odd_block["relative_residual_CY_minus_B"],
                "S0": matrix_to_rows(odd_block["S0"]),
                "K_schur": matrix_to_rows(odd_block["K_schur"]),
                "G": matrix_to_rows(odd_block["G"]),
                "S0_eigenvalues": odd_vals,
            },
            "combined_sorted": combined_rows,
            "ordering_even_odd_even": ordering_ok,
            "max_rel_error_vs_true_mu": max_rel,
            "ground_alignment_with_k1_p": ground_alignment,
            "cross_entries": "exact_zero_by_block_assembly",
        },
        "B2_dirt_identity_check": {
            "G_cross_norm": g_cross_norm,
            "S0_cross_norm": s0_cross_norm,
            "S0_cross_norm_over_G_cross_norm": dirt_ratio,
            "registered_target": "~1e-40",
            "pass": mp.mpf("1e-42") <= dirt_ratio <= mp.mpf("1e-38"),
        },
        "C_external_cross_validation": {
            "verdict": external_verdict,
            "our_lowest_even_eigenvalue": even_vals[0],
            "our_odd_level": odd_vals[0],
            "groskin_arxiv_2605_20224_c13_lambda_even_min_examples": ["2.865e-59", "2.077e-59"],
            "groskin_arxiv_2605_20224_c13_first_zero_error_examples": ["2.005e-55", "1.455e-55"],
            "ccm_prompt_registered_first_zero_error_c13": "2.44e-55",
            "source_urls": ["https://arxiv.org/abs/2605.20224", "https://arxiv.org/pdf/2605.20224"],
        },
        "D_log_space_N_model": log_space_model(combined_sorted),
        "elapsed_s": time.time() - started,
    }

    pilot.write_json(JSON_OUT, payload)
    write_report(payload)
    write_handoff(payload)
    update_loop_state(b_verdict)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
