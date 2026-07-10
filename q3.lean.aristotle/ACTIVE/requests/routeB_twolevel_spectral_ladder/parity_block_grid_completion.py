#!/usr/bin/env python3
"""
ParityBlockGridCompletion for Route B TwoLevelSpectralLadder.

Request-local numerical diagnostic only: no RH claim, no Phase 2, no new
lambda/N anchors. The runner rebuilds canonical parity-block Schur objects for
the saved grid and imports the already persisted (13,120) parity rebuild as the
lambda13 N=120 anchor.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import mpmath as mp

import parity_audit_rebuild_v2 as parity
import routeb_ladder_pilot as pilot


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
REPORT = REQUEST_DIR / "parity_block_grid_completion.md"
JSON_OUT = OUT_DIR / "parity_block_grid_completion.json"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"

POINT_ORDER: List[Tuple[str, int, int]] = [
    ("T1", 13, 60),
    ("T1", 13, 90),
    ("T2", 12, 60),
    ("T2", 12, 90),
    ("T2", 14, 60),
    ("T2", 14, 90),
    ("T3", 12, 120),
    ("T3", 14, 120),
]
SEED_POINT = (13, 120)
PACKET_NAMES = parity.PACKET_NAMES
ORDER = parity.ORDER
EXPECTED_PARITY = parity.EXPECTED_PARITY

RESIDUAL_TARGET = mp.mpf("1e-150")
DUST_TARGET = mp.mpf("1e-12")
THETA_LOG_DRIFT_TARGET = mp.mpf("0.005")
MU2_ODD_12_BAND = (mp.mpf("3e-50"), mp.mpf("3e-49"))
R1_13_BAND = (mp.mpf("1e-36"), mp.mpf("1e-32"))

GROSKIN_FIRST_ZERO_ERRORS = {
    13: {
        "first_zero_error": mp.mpf("2.005e-55"),
        "lambda_even_min": mp.mpf("2.865e-59"),
        "source": "Groskin arXiv:2605.20224, Table 3, c=13, N=100, T=800",
    },
    14: {
        "first_zero_error": mp.mpf("3.541e-61"),
        "lambda_even_min": mp.mpf("4.835e-65"),
        "source": "Groskin arXiv:2605.20224, Table 3, c=14, N=100, T=800",
    },
}


def point_path(lambda_sq: int, N: int) -> Path:
    return OUT_DIR / f"parity_block_lambda_sq_{lambda_sq}_N_{N}.json"


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def mpf(value: Any) -> mp.mpf:
    return mp.mpf(str(value))


def mpc(value: Any) -> mp.mpc:
    return parity.parse_mpc(value)


def eigvals_hermitian(A: mp.matrix) -> List[mp.mpf]:
    vals, _ = mp.eighe(pilot.hermitian_part(A))
    return [mp.re(vals[i]) for i in range(vals.rows)]


def positive_lambda1(vals: Sequence[mp.mpf]) -> Tuple[mp.mpf, str]:
    positives = [v for v in vals if v > 0]
    if positives:
        return min(positives), "smallest_positive"
    return min(vals, key=lambda x: abs(x)), "min_abs_no_positive"


def max_reflection_ratio(T: mp.matrix) -> Dict[str, Any]:
    max_tau = max(abs(T[i, j]) for i in range(T.rows) for j in range(T.cols))
    max_reflection_error = mp.mpf("0")
    for i in range(T.rows):
        for j in range(T.cols):
            max_reflection_error = max(
                max_reflection_error,
                abs(T[i, j] - T[T.rows - 1 - i, T.cols - 1 - j]),
            )
    return {
        "max_abs_tau": max_tau,
        "max_abs_reflection_error": max_reflection_error,
        "ratio": max_reflection_error / max(max_tau, mp.mpf("1e-300")),
    }


def matrix_to_rows(A: mp.matrix) -> List[List[Any]]:
    return [[A[i, j] for j in range(A.cols)] for i in range(A.rows)]


def log10_abs(value: Any) -> mp.mpf:
    return mp.log10(abs(mpc(value)))


def sequence_fit(points: Sequence[Tuple[int, mp.mpf]]) -> Dict[str, Any]:
    rows = sorted(points)
    out: Dict[str, Any] = {
        "label": "FIT_NOT_LAW",
        "points": [{"N": N, "log10_abs": x} for N, x in rows],
    }
    if len(rows) < 2:
        out["status"] = "INSUFFICIENT_POINTS"
        return out
    diffs = []
    for (n0, x0), (n1, x1) in zip(rows, rows[1:]):
        diffs.append({"from": n0, "to": n1, "drift": x1 - x0})
    out["consecutive_drifts"] = diffs
    if len(rows) >= 3:
        (_, x0), (_, x1), (_, x2) = rows[:3]
        d1 = x1 - x0
        d2 = x2 - x1
        out["rho_drift_60_90_over_90_120"] = d1 / d2 if d2 != 0 else mp.inf
        denom = x2 - 2 * x1 + x0
        out["aitken_delta2"] = None if denom == 0 else x0 - ((x1 - x0) ** 2) / denom
        out["geometric_extrapolation"] = None
        if d2 != 0:
            rho = abs(d1 / d2)
            if rho > 1:
                out["geometric_extrapolation"] = x2 + d2 / (rho - 1)
        out["drift_90_120_over_abs_x120"] = abs(d2) / max(abs(x2), mp.mpf("1e-300"))
    return out


def write_payload(path: Path, payload: Dict[str, Any]) -> None:
    pilot.write_json(path, payload)


def packet_parity_split(lambda_sq: int, N: int) -> Tuple[Dict[str, mp.matrix], List[Dict[str, Any]]]:
    lam = mp.sqrt(lambda_sq)
    packet = pilot.make_packets(float(lam), N)
    projected: Dict[str, mp.matrix] = {}
    rows: List[Dict[str, Any]] = []
    for logical in ORDER:
        v = pilot.mp_vec_from_np(packet.coeffs[PACKET_NAMES[logical]])
        even, odd = parity.parity_parts(v)
        expected = EXPECTED_PARITY[logical]
        keep = even if expected == "even" else odd
        off = odd if expected == "even" else even
        delta = pilot.norm(off) / max(pilot.norm(v), mp.mpf("1e-300"))
        reflected_conj = mp.matrix([[mp.conj(v[i])] for i in range(v.rows)])
        reality_error = pilot.norm(parity.reflection(v) - reflected_conj) / max(pilot.norm(v), mp.mpf("1e-300"))
        projected[logical] = parity.normalize(keep)
        rows.append(
            {
                "vector": logical,
                "packet_name": PACKET_NAMES[logical],
                "expected_parity": expected,
                "delta_off_parity": delta,
                "dust_registered_pass": delta <= DUST_TARGET,
                "even_norm": pilot.norm(even),
                "odd_norm": pilot.norm(odd),
                "reality_error": reality_error,
            }
        )
    return projected, rows


def combined_rows(
    even_vals: Sequence[mp.mpf],
    odd_vals: Sequence[mp.mpf],
    cell: Dict[str, Any],
) -> Tuple[List[Dict[str, Any]], List[Tuple[str, mp.mpf]]]:
    combined = [("even", even_vals[0]), ("even", even_vals[1]), ("odd", odd_vals[0])]
    combined_sorted = sorted(combined, key=lambda p: p[1])
    true_mu = [mpf(cell["mu1"]), mpf(cell["mu2"]), mpf(cell["mu3"])]
    rows = []
    for rank, ((parity_label, value), mu) in enumerate(zip(combined_sorted, true_mu), start=1):
        rows.append(
            {
                "rank": rank,
                "parity": parity_label,
                "theta": value,
                "saved_mu": mu,
                "rel_error_vs_saved_mu": abs(value - mu) / max(abs(mu), mp.mpf("1e-300")),
            }
        )
    return rows, combined_sorted


def compute_point(tier: str, lambda_sq: int, N: int) -> Dict[str, Any]:
    started = time.time()
    cell = load_json(OUT_DIR / f"lambda_sq_{lambda_sq}_N_{N}.json")
    dps = int(cell["dps"])
    mp.mp.dps = dps
    lam = mp.sqrt(lambda_sq)

    T = pilot.build_tau_matrix(lam, N, dps)
    t_parity = max_reflection_ratio(T)
    projected, dust_rows = packet_parity_split(lambda_sq, N)

    even_packets, even_q_stats = pilot.modified_gram_schmidt_mp(
        [projected["k1"], projected["k2_even"]],
        tol=mp.power(10, -min(70, max(30, dps // 3))),
    )
    odd_packets, odd_q_stats = pilot.modified_gram_schmidt_mp(
        [projected["k2_odd"]],
        tol=mp.power(10, -min(70, max(30, dps // 3))),
    )
    even_block = parity.block_from_basis(T, even_packets, parity.parity_sector_basis(2 * N + 1, N, "even"))
    odd_block = parity.block_from_basis(T, odd_packets, parity.parity_sector_basis(2 * N + 1, N, "odd"))

    even_vals = even_block["S0_eigenvalues"]
    odd_vals = odd_block["S0_eigenvalues"]
    rows, combined_sorted = combined_rows(even_vals, odd_vals, cell)
    ordering_ok = [p for p, _ in combined_sorted] == ["even", "odd", "even"]
    residual_max = max(even_block["relative_residual_CY_minus_B"], odd_block["relative_residual_CY_minus_B"])
    dust_max = max(row["delta_off_parity"] for row in dust_rows)

    even_G = eigvals_hermitian(even_block["G"])
    lambda1_G, lambda1_G_selection = positive_lambda1(even_G)
    theta1 = combined_sorted[0][1]
    r1 = theta1 / lambda1_G

    ground_alignment = abs(even_block["S0_eigenvectors"][0, 0])
    payload: Dict[str, Any] = {
        "gate": "ParityBlockGridCompletion",
        "route": "RouteB_TwoLevelSpectralLadder",
        "source": "fresh_rebuild_from_saved_scalar_anchor",
        "tier": tier,
        "lambda_sq": lambda_sq,
        "lambda": lam,
        "N": N,
        "dps": dps,
        "status": "complete",
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "q3_main_touched": False,
        "elapsed_s": time.time() - started,
        "T_parity": t_parity,
        "A0_packet_dust": {
            "rows": dust_rows,
            "max_delta_off_parity": dust_max,
            "registered_threshold": DUST_TARGET,
            "registered_pass": dust_max <= DUST_TARGET,
        },
        "even": {
            "M_dim": 2,
            "complement_dim": len(even_block["u_basis"]),
            "q_stats": even_q_stats,
            "G_eigenvalues": even_G,
            "lambda1_G": lambda1_G,
            "lambda1_G_selection": lambda1_G_selection,
            "relative_residual_CY_minus_B": even_block["relative_residual_CY_minus_B"],
            "S0": matrix_to_rows(even_block["S0"]),
            "S0_eigenvalues": even_vals,
        },
        "odd": {
            "M_dim": 1,
            "complement_dim": len(odd_block["u_basis"]),
            "q_stats": odd_q_stats,
            "G_eigenvalues": eigvals_hermitian(odd_block["G"]),
            "relative_residual_CY_minus_B": odd_block["relative_residual_CY_minus_B"],
            "S0": matrix_to_rows(odd_block["S0"]),
            "S0_eigenvalues": odd_vals,
        },
        "combined_sorted": rows,
        "ordering_even_odd_even": ordering_ok,
        "max_rel_error_vs_saved_mu": max(row["rel_error_vs_saved_mu"] for row in rows),
        "ground_alignment_with_k1_p": ground_alignment,
        "theta": [row["theta"] for row in rows],
        "mu2_odd": odd_vals[0],
        "r1_theta1_over_lambda1_G_even": r1,
        "registered": {
            "ordering_even_odd_even_pass": ordering_ok,
            "solver_residual_target": RESIDUAL_TARGET,
            "solver_residual_max": residual_max,
            "solver_residual_pass": residual_max <= RESIDUAL_TARGET,
            "dust_delta_target": DUST_TARGET,
            "dust_delta_pass": dust_max <= DUST_TARGET,
        },
    }
    write_payload(point_path(lambda_sq, N), payload)
    return payload


def seed_from_existing_parity_audit() -> Dict[str, Any]:
    source = load_json(OUT_DIR / "parity_audit_rebuild_v2.json")
    cell = load_json(OUT_DIR / "lambda_sq_13_N_120.json")
    b = source["B_parity_projected_rebuild"]
    mp.mp.dps = int(source["dps"])

    even_G = parity.matrix_from_json(b["even"]["G"])
    even_G_vals = eigvals_hermitian(even_G)
    lambda1_G, lambda1_G_selection = positive_lambda1(even_G_vals)
    rows = []
    for row in b["combined_sorted"]:
        rows.append(
            {
                "rank": int(row["rank"]),
                "parity": row["parity"],
                "theta": mpc(row["value"]),
                "saved_mu": mpc(row["true_mu"]),
                "rel_error_vs_saved_mu": mpf(row["rel_error_vs_true_mu"]),
            }
        )
    dust_rows = source["A0_parity_aware_threshold_model"]["vectors"]
    dust_max = max(mpf(row["delta_off_parity"]) for row in dust_rows)
    residual_max = max(
        mpf(b["even"]["relative_residual_CY_minus_B"]),
        mpf(b["odd"]["relative_residual_CY_minus_B"]),
    )
    theta1 = mpc(rows[0]["theta"])
    payload: Dict[str, Any] = {
        "gate": "ParityBlockGridCompletion",
        "route": "RouteB_TwoLevelSpectralLadder",
        "source": "imported_from_parity_audit_rebuild_v2",
        "source_json": "out/parity_audit_rebuild_v2.json",
        "tier": "SEED",
        "lambda_sq": 13,
        "lambda": mp.sqrt(13),
        "N": 120,
        "dps": int(source["dps"]),
        "status": "complete",
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "q3_main_touched": False,
        "elapsed_s": 0,
        "T_parity": source["A1_T_parity"],
        "A0_packet_dust": {
            "rows": dust_rows,
            "max_delta_off_parity": dust_max,
            "registered_threshold": DUST_TARGET,
            "registered_pass": dust_max <= DUST_TARGET,
        },
        "even": {
            "M_dim": 2,
            "complement_dim": b["even"]["complement_dim"],
            "G_eigenvalues": even_G_vals,
            "lambda1_G": lambda1_G,
            "lambda1_G_selection": lambda1_G_selection,
            "relative_residual_CY_minus_B": mpf(b["even"]["relative_residual_CY_minus_B"]),
            "S0": b["even"]["S0"],
            "S0_eigenvalues": [mpc(x) for x in b["even"]["S0_eigenvalues"]],
        },
        "odd": {
            "M_dim": 1,
            "complement_dim": b["odd"]["complement_dim"],
            "relative_residual_CY_minus_B": mpf(b["odd"]["relative_residual_CY_minus_B"]),
            "S0": b["odd"]["S0"],
            "S0_eigenvalues": [mpc(x) for x in b["odd"]["S0_eigenvalues"]],
        },
        "combined_sorted": rows,
        "ordering_even_odd_even": b["ordering_even_odd_even"],
        "max_rel_error_vs_saved_mu": mpf(b["max_rel_error_vs_true_mu"]),
        "ground_alignment_with_k1_p": mpf(b["ground_alignment_with_k1_p"]),
        "theta": [row["theta"] for row in rows],
        "mu2_odd": mpc(b["odd"]["S0_eigenvalues"][0]),
        "r1_theta1_over_lambda1_G_even": theta1 / lambda1_G,
        "registered": {
            "ordering_even_odd_even_pass": b["ordering_even_odd_even"],
            "solver_residual_target": RESIDUAL_TARGET,
            "solver_residual_max": residual_max,
            "solver_residual_pass": residual_max <= RESIDUAL_TARGET,
            "dust_delta_target": DUST_TARGET,
            "dust_delta_pass": dust_max <= DUST_TARGET,
        },
        "saved_scalar_anchor": {
            "mu1": cell["mu1"],
            "mu2": cell["mu2"],
            "mu3": cell["mu3"],
        },
    }
    write_payload(point_path(13, 120), payload)
    return payload


def best_point(points: Sequence[Dict[str, Any]], lambda_sq: int, N: int) -> Dict[str, Any]:
    for point in points:
        if int(point["lambda_sq"]) == lambda_sq and int(point["N"]) == N:
            return point
    raise KeyError((lambda_sq, N))


def aggregate(points: Sequence[Dict[str, Any]], skipped: Sequence[Tuple[str, int, int]]) -> Dict[str, Any]:
    by_lam: Dict[int, List[Dict[str, Any]]] = {}
    for point in points:
        by_lam.setdefault(int(point["lambda_sq"]), []).append(point)
    for rows in by_lam.values():
        rows.sort(key=lambda p: int(p["N"]))

    theta_fits: Dict[str, Dict[str, Any]] = {}
    for lambda_sq, rows in sorted(by_lam.items()):
        theta_fits[str(lambda_sq)] = {}
        for rank in range(3):
            theta_fits[str(lambda_sq)][f"theta{rank + 1}"] = sequence_fit(
                [(int(p["N"]), log10_abs(p["theta"][rank])) for p in rows if len(p["theta"]) > rank]
            )

    lambda13_drift = {}
    for rank in range(3):
        fit = theta_fits["13"][f"theta{rank + 1}"]
        lambda13_drift[f"theta{rank + 1}"] = {
            "drift_90_120_over_abs_x120": fit.get("drift_90_120_over_abs_x120"),
            "pass": fit.get("drift_90_120_over_abs_x120", mp.inf) < THETA_LOG_DRIFT_TARGET,
        }

    mu2_odd_12_rows = []
    for point in by_lam.get(12, []):
        value = mpc(point["mu2_odd"])
        mu2_odd_12_rows.append(
            {
                "N": int(point["N"]),
                "mu2_odd": value,
                "pass": MU2_ODD_12_BAND[0] <= abs(value) <= MU2_ODD_12_BAND[1],
            }
        )

    r1_13_rows = []
    for point in by_lam.get(13, []):
        value = mpc(point["r1_theta1_over_lambda1_G_even"])
        r1_13_rows.append(
            {
                "N": int(point["N"]),
                "r1": value,
                "pass": R1_13_BAND[0] <= abs(value) <= R1_13_BAND[1],
            }
        )

    external_rows = []
    for lambda_sq, source in GROSKIN_FIRST_ZERO_ERRORS.items():
        point = best_point(points, lambda_sq, 120)
        ours = abs(mpc(point["mu2_odd"]))
        theirs = source["first_zero_error"]
        factor = max(ours / theirs, theirs / ours)
        external_rows.append(
            {
                "lambda_sq": lambda_sq,
                "N": 120,
                "our_mu2_odd": ours,
                "groskin_first_zero_error": theirs,
                "groskin_lambda_even_min": source["lambda_even_min"],
                "factor_max": factor,
                "log10_abs_delta": abs(mp.log10(ours) - mp.log10(theirs)),
                "support_order_law": factor <= 10,
                "source": source["source"],
            }
        )

    registered = {
        "ordering_even_odd_even_every_point": all(p["registered"]["ordering_even_odd_even_pass"] for p in points),
        "solver_residual_every_point": all(p["registered"]["solver_residual_pass"] for p in points),
        "dust_delta_every_point": all(p["registered"]["dust_delta_pass"] for p in points),
        "theta_log_drift_lambda13": lambda13_drift,
        "theta_log_drift_lambda13_pass": all(row["pass"] for row in lambda13_drift.values()),
        "mu2_odd_12_band": {
            "band": [MU2_ODD_12_BAND[0], MU2_ODD_12_BAND[1]],
            "rows": mu2_odd_12_rows,
            "pass": bool(mu2_odd_12_rows) and all(row["pass"] for row in mu2_odd_12_rows),
        },
        "r1_13_band": {
            "band": [R1_13_BAND[0], R1_13_BAND[1]],
            "rows": r1_13_rows,
            "pass": bool(r1_13_rows) and all(row["pass"] for row in r1_13_rows),
        },
        "external_ZERO_ERR_EQUALS_ODD_LEVEL": {
            "rows": external_rows,
            "verdict": "SUPPORTED_ORDER_ONLY" if all(row["support_order_law"] for row in external_rows) else "REFUTED",
        },
        "skipped": [{"tier": t, "lambda_sq": c, "N": N} for t, c, N in skipped],
    }

    failure_code: Optional[str] = None
    if skipped:
        failure_code = "SKIPPED_BY_BUDGET"
    elif not registered["solver_residual_every_point"]:
        failure_code = "SOLVER_RESIDUAL_DEGRADED"
    elif not registered["ordering_even_odd_even_every_point"]:
        failure_code = "PARITY_ORDERING_BROKEN"
    elif not registered["theta_log_drift_lambda13_pass"]:
        failure_code = "THETA_LOG_N_UNSTABLE"
    elif not registered["mu2_odd_12_band"]["pass"] or not registered["r1_13_band"]["pass"]:
        failure_code = "E_CLASS_SCALING_VIOLATED"
    elif not registered["dust_delta_every_point"]:
        failure_code = "SOLVER_RESIDUAL_DEGRADED"

    return {
        "fits": {"theta_log10_abs": theta_fits, "label": "FIT_NOT_LAW"},
        "registered": registered,
        "failure_code": failure_code,
        "verdict": failure_code or "PARITY_BLOCK_GRID_COMPLETION_CONFIRMED",
    }


def update_loop_state(verdict: str, failure_code: Optional[str]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "WAITING_FOR_PROSHKA_REVIEW_AFTER_PARITY_BLOCK_GRID_COMPLETION",
            "last_attempted_gate": "ParityBlockGridCompletion",
            "last_completed_gate": "ParityBlockGridCompletion",
            "last_completed_gate_status": "COMPLETED_WITH_REGISTERED_FAILURE" if failure_code else "COMPLETED_PASS",
            "last_verdict": verdict,
            "failure_code": failure_code or verdict,
            "parity_block_grid_completion_report": "parity_block_grid_completion.md",
            "parity_block_grid_completion_json": "out/parity_block_grid_completion.json",
            "next_gate": None,
            "requires_proshka_after_gate": True,
            "phase2_allowed": False,
            "q3_main_allowed": False,
            "updated_at_unix": time.time(),
        }
    )
    LOOP_STATE.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def short(x: Any, digits: int = 12) -> str:
    return pilot.mp_to_str(x, digits)


def write_report(payload: Dict[str, Any]) -> None:
    agg = payload["aggregate"]
    lines = [
        "# ParityBlockGridCompletion",
        "",
        "Status: diagnostic only. Not a proof of RH. Not a Route B kill. Phase 2 was not run. No new lambda/N anchors were bought. Q3 mainline files were not touched.",
        "",
        "## Verdict",
        "",
        f"- verdict: `{agg['verdict']}`",
        f"- failure_code: `{agg['failure_code']}`",
        "- canonical object: `S0 = (2x2 even) direct_sum (1x1 odd)`",
        "- `(13,120)` was imported from the already persisted `ParityAuditRebuild_v2`; every other listed point was rebuilt fresh from saved scalar anchors.",
        "",
        "## Point Table",
        "",
        "| tier | lambda_sq | N | source | ordering | max residual | max dust | mu2_odd | r1=theta1/lambda1(G_even) | max rel err vs saved mu |",
        "|---|---:|---:|---|---|---:|---:|---:|---:|---:|",
    ]
    for p in sorted(payload["points"], key=lambda r: (int(r["lambda_sq"]), int(r["N"]))):
        lines.append(
            "| {tier} | {lam} | {N} | `{source}` | `{ordering}` | `{resid}` | `{dust}` | `{mu2}` | `{r1}` | `{rel}` |".format(
                tier=p["tier"],
                lam=p["lambda_sq"],
                N=p["N"],
                source=p["source"],
                ordering=p["ordering_even_odd_even"],
                resid=short(p["registered"]["solver_residual_max"], 10),
                dust=short(p["A0_packet_dust"]["max_delta_off_parity"], 10),
                mu2=short(p["mu2_odd"], 10),
                r1=short(p["r1_theta1_over_lambda1_G_even"], 10),
                rel=short(p["max_rel_error_vs_saved_mu"], 10),
            )
        )

    reg = agg["registered"]
    lines.extend(
        [
            "",
            "## Registered Checks",
            "",
            f"- ordering `even<odd<even` every point: `{reg['ordering_even_odd_even_every_point']}`",
            f"- solver residual `<=1e-150` every point: `{reg['solver_residual_every_point']}`",
            f"- dust delta `<=1e-12` every point: `{reg['dust_delta_every_point']}`",
            f"- lambda13 theta log-drift `<0.5%`: `{reg['theta_log_drift_lambda13_pass']}`",
            f"- `mu2_odd(12)` in `[3e-50,3e-49]`: `{reg['mu2_odd_12_band']['pass']}`",
            f"- `r1(13)` in `[1e-36,1e-32]`: `{reg['r1_13_band']['pass']}`",
            f"- external `ZERO_ERR_EQUALS_ODD_LEVEL`: `{reg['external_ZERO_ERR_EQUALS_ODD_LEVEL']['verdict']}`",
            "",
            "### Lambda13 Theta Drift",
            "",
            "| theta | drift90->120 / abs(x120) | pass |",
            "|---|---:|---|",
        ]
    )
    for key, row in reg["theta_log_drift_lambda13"].items():
        lines.append(f"| `{key}` | `{short(row['drift_90_120_over_abs_x120'], 12)}` | `{row['pass']}` |")

    lines.extend(
        [
            "",
            "### mu2_odd(12)",
            "",
            "| N | mu2_odd | pass |",
            "|---:|---:|---|",
        ]
    )
    for row in reg["mu2_odd_12_band"]["rows"]:
        lines.append(f"| {row['N']} | `{short(row['mu2_odd'], 12)}` | `{row['pass']}` |")

    lines.extend(
        [
            "",
            "### r1(13)",
            "",
            "| N | r1 | pass |",
            "|---:|---:|---|",
        ]
    )
    for row in reg["r1_13_band"]["rows"]:
        lines.append(f"| {row['N']} | `{short(row['r1'], 12)}` | `{row['pass']}` |")

    lines.extend(
        [
            "",
            "## FIT_NOT_LAW Log Fits",
            "",
            "All fits below are finite-grid diagnostics only. Aitken and geometric extrapolations are reported on log10(abs(theta)) when three N-points exist; no law is claimed.",
            "",
            "| lambda_sq | theta | rho drift60->90 / drift90->120 | Aitken log10 | drift90->120/abs(x120) |",
            "|---:|---|---:|---:|---:|",
        ]
    )
    for lam, series in agg["fits"]["theta_log10_abs"].items():
        for key, fit in series.items():
            lines.append(
                f"| {lam} | `{key}` | `{short(fit.get('rho_drift_60_90_over_90_120', 'NA'), 10)}` | `{short(fit.get('aitken_delta2', 'NA'), 10)}` | `{short(fit.get('drift_90_120_over_abs_x120', 'NA'), 10)}` |"
            )

    lines.extend(
        [
            "",
            "## External Zero-Compute Check",
            "",
            "Comparison source: Groskin, arXiv:2605.20224, Table 3 and c=13/c=14 discussion. This is order-only numerical context, not proof input.",
            "",
            "| c=lambda_sq | our mu2_odd N=120 | Groskin first-zero error | factor max | verdict |",
            "|---:|---:|---:|---:|---|",
        ]
    )
    for row in reg["external_ZERO_ERR_EQUALS_ODD_LEVEL"]["rows"]:
        lines.append(
            f"| {row['lambda_sq']} | `{short(row['our_mu2_odd'], 12)}` | `{short(row['groskin_first_zero_error'], 12)}` | `{short(row['factor_max'], 8)}` | `{'support' if row['support_order_law'] else 'refute'}` |"
        )
    lines.extend(
        [
            "",
            "Sources:",
            "- https://arxiv.org/abs/2605.20224",
            "- https://arxiv.org/pdf/2605.20224",
            "",
            "## Stop",
            "",
            "Stop after this report and handoff. Do not pick the next gate locally.",
            "",
        ]
    )
    REPORT.write_text("\n".join(lines), encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    agg = payload["aggregate"]
    reg = agg["registered"]
    lines = [
        "PROSHKA_ROUTE_REVIEW",
        "",
        "Gate:",
        "ParityBlockGridCompletion / Route B TwoLevelSpectralLadder",
        "",
        "Verdict:",
        agg["verdict"],
        "",
        "Route status:",
        "NOT_KILLED. Diagnostic only. No RH claim. Phase 2 not run. No new lambda/N anchors. Q3 mainline untouched.",
        "",
        "Files written:",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/parity_block_grid_completion.py",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/parity_block_grid_completion.md",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/out/parity_block_grid_completion.json",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/out/parity_block_lambda_sq_*_N_*.json",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/handoff_to_proshka.md",
        "- ACTIVE/requests/routeB_twolevel_spectral_ladder/loop_state.json",
        "",
        "What happened:",
        "- Canonical parity-block Schur was evaluated across the saved grid only.",
        "- `(13,120)` was imported from the already saved ParityAuditRebuild_v2; all requested T1/T2/T3 points were rebuilt fresh.",
        f"- ordering even<odd<even every point: `{reg['ordering_even_odd_even_every_point']}`.",
        f"- solver residual <=1e-150 every point: `{reg['solver_residual_every_point']}`.",
        f"- dust delta <=1e-12 every point: `{reg['dust_delta_every_point']}`.",
        f"- lambda13 theta log-drift <0.5%: `{reg['theta_log_drift_lambda13_pass']}`.",
        f"- mu2_odd(12) registered band pass: `{reg['mu2_odd_12_band']['pass']}`.",
        f"- r1(13) registered band pass: `{reg['r1_13_band']['pass']}`.",
        f"- ZERO_ERR_EQUALS_ODD_LEVEL external order law: `{reg['external_ZERO_ERR_EQUALS_ODD_LEVEL']['verdict']}`.",
        "",
        "Question for Proshka:",
        "Given this parity-block grid completion, which next gate should be chosen? Do not answer as RH proof/kill. If accepted, should we return to OperatorStaticSchurStabilityGate using only parity-block S0_parity, or should another source/packet audit precede it?",
        "",
        "Stop condition:",
        "Codex stops here after report + handoff and does not pick the next gate locally.",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def maybe_load_existing(lambda_sq: int, N: int) -> Optional[Dict[str, Any]]:
    path = point_path(lambda_sq, N)
    if not path.exists():
        return None
    payload = load_json(path)
    if payload.get("gate") == "ParityBlockGridCompletion" and payload.get("status") == "complete":
        return payload
    return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--resume", action="store_true", help="reuse already persisted parity_block point JSONs")
    parser.add_argument("--skip-t3", action="store_true", help="budget stop before optional T3 points")
    args = parser.parse_args()
    started = time.time()

    points: List[Dict[str, Any]] = [seed_from_existing_parity_audit()]
    skipped: List[Tuple[str, int, int]] = []
    for tier, lambda_sq, N in POINT_ORDER:
        if args.skip_t3 and tier == "T3":
            skipped.append((tier, lambda_sq, N))
            continue
        existing = maybe_load_existing(lambda_sq, N) if args.resume else None
        point = existing if existing is not None else compute_point(tier, lambda_sq, N)
        points.append(point)

        if not point["registered"]["solver_residual_pass"]:
            break
        if not point["registered"]["ordering_even_odd_even_pass"]:
            break

    agg = aggregate(points, skipped)
    payload = {
        "gate": "ParityBlockGridCompletion",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": "complete" if agg["failure_code"] is None else "stopped",
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "q3_main_touched": False,
        "point_order": [{"tier": t, "lambda_sq": c, "N": N} for t, c, N in POINT_ORDER],
        "seed_point": {"lambda_sq": SEED_POINT[0], "N": SEED_POINT[1], "source": "out/parity_audit_rebuild_v2.json"},
        "points": points,
        "aggregate": agg,
        "elapsed_s": time.time() - started,
    }
    write_payload(JSON_OUT, payload)
    write_report(payload)
    write_handoff(payload)
    update_loop_state(agg["verdict"], agg["failure_code"])
    return 0 if agg["failure_code"] is None else 3


if __name__ == "__main__":
    raise SystemExit(main())
