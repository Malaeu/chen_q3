#!/usr/bin/env python3
"""
AnchorLockedKChannel_v1 for Route B / Route Z E5.

Diagnostic only:
- not RH
- no Phase 2
- no QW formula changes
- no packet-definition changes
- no Q3 mainline changes
"""

from __future__ import annotations

import hashlib
import json
import math
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import mpmath as mp
import numpy as np

import routeb_ladder_pilot as pilot


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
OUT_DIR = REQUEST_DIR / "out"

JSON_OUT = OUT_DIR / "anchor_locked_k_channel_v1.json"
REPORT = REQUEST_DIR / "anchor_locked_k_channel_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
ACTIONS_LOG = REQUEST_DIR / "anchor_locked_k_channel_v1_actions_log.md"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"

ZERO_PROFILE_JSON = OUT_DIR / "zero_sum_profile_v2.json"

POINTS = [(13, 120), (12, 120), (14, 120), (13, 90)]
ANCHOR_POINT = (13, 120)
A1_J = 10
A4_J = 200
A5_J = 2000
MP_DPS = 100
PLANCHEREL_TOL = mp.mpf("1e-4")
ANCHOR_TOL = mp.mpf("1e-6")
CEILING = mp.mpf("1.05")


def progress(label: str) -> None:
    print(f"[AnchorLockedKChannel_v1] {label}", flush=True)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def rel(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REQUEST_DIR))
    except ValueError:
        try:
            return str(path.resolve().relative_to(REPO_ROOT))
        except ValueError:
            return str(path.resolve())


def file_record(path: Path, role: str) -> Dict[str, Any]:
    return {
        "role": role,
        "path": rel(path),
        "sha256": sha256_file(path) if path.exists() else None,
        "exists": path.exists(),
    }


def git_diff_stat() -> str:
    proc = subprocess.run(
        ["git", "diff", "--stat", "--", str(REQUEST_DIR.relative_to(REPO_ROOT))],
        cwd=str(REPO_ROOT),
        text=True,
        capture_output=True,
        check=False,
    )
    return proc.stdout.strip() or "(empty)"


def git_status_short() -> str:
    proc = subprocess.run(
        ["git", "status", "--short", "--", str(REQUEST_DIR.relative_to(REPO_ROOT))],
        cwd=str(REPO_ROOT),
        text=True,
        capture_output=True,
        check=False,
    )
    return proc.stdout.strip() or "(empty)"


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, (mp.mpf, mp.mpc)):
        return mp.nstr(value, 90)
    if isinstance(value, complex):
        return {"re": repr(value.real), "im": repr(value.imag)}
    if isinstance(value, np.generic):
        return value.item()
    return value


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fmt(value: Any, digits: int = 12) -> str:
    if value is None:
        return "UNKNOWN"
    if isinstance(value, str):
        try:
            return mp.nstr(mp.mpf(value), digits)
        except Exception:
            return value
    return mp.nstr(value, digits)


def coeff_cache_path(lambda_sq: int, n_bound: int) -> Path:
    return OUT_DIR / f"portable_k_coeffs_lambda_sq_{lambda_sq}_N_{n_bound}.json"


def anchor_zeros_path(count: int) -> Path:
    return OUT_DIR / f"anchor_locked_zeros_first_{count}.json"


def parse_coeff_rows(rows: Sequence[Dict[str, Any]]) -> List[mp.mpc]:
    return [mp.mpc(mp.mpf(str(row["re"])), mp.mpf(str(row["im"]))) for row in rows]


def coeff_norm_sq(coeffs: Sequence[mp.mpc]) -> mp.mpf:
    return sum(abs(z) ** 2 for z in coeffs)


def load_coeff_cache(lambda_sq: int, n_bound: int) -> Dict[str, Any]:
    path = coeff_cache_path(lambda_sq, n_bound)
    data = load_json(path)
    data["_path"] = path
    data["_sha256"] = sha256_file(path)
    return data


def load_coeffs_mp(cache: Dict[str, Any]) -> List[mp.mpc]:
    return parse_coeff_rows(cache["coefficients"])


def first_coeffs(cache: Dict[str, Any], count: int = 3) -> List[Dict[str, Any]]:
    return cache["coefficients"][:count]


def provenance_lock(cache: Dict[str, Any]) -> Dict[str, Any]:
    coeffs = load_coeffs_mp(cache)
    expected = {
        "source": "true_precision_packet_gate_v1.integrate_coefficients",
        "packet_name": "g04",
        "logical_vector": "k1",
        "dps": 110,
        "quad_order": 192,
    }
    fields_ok = (
        cache.get("source") == expected["source"]
        and cache.get("packet_name") == expected["packet_name"]
        and cache.get("logical_vector") == expected["logical_vector"]
        and int(cache.get("dps")) == expected["dps"]
        and int(cache.get("quad_order")) == expected["quad_order"]
    )
    norm_sq = coeff_norm_sq(coeffs)
    return {
        "point": {"lambda_sq": cache["lambda_sq"], "N": cache["N"]},
        "coefficient_file": rel(cache["_path"]),
        "coefficient_file_sha256": cache["_sha256"],
        "first_3_coefficients": first_coeffs(cache),
        "sum_abs_c_n_sq": norm_sq,
        "abs_sum_abs_c_n_sq_minus_1": abs(norm_sq - 1),
        "provenance_fields_ok": fields_ok,
        "provenance_line": (
            "tol_B true-precision normalized packet by construction: "
            "g04/k1 coefficients loaded from true_precision_packet_gate_v1.integrate_coefficients, "
            "dps=110, quad_order=192 with 96/192 refinement, then l2-normalized."
        ),
    }


def K_mp(lambda_sq: int, n_bound: int, gamma: mp.mpf, coeffs: Sequence[mp.mpc]) -> mp.mpc:
    L = mp.log(lambda_sq)
    lam = mp.sqrt(lambda_sq)
    total = mp.mpc(0)
    n0 = -n_bound
    for idx, coeff in enumerate(coeffs):
        n = n0 + idx
        alpha = 2 * mp.pi * n / L - gamma
        z = 1j * alpha * L
        if abs(z) < mp.mpf("1e-50"):
            integral = L
        else:
            integral = L * mp.expm1(z) / z
        total += coeff * integral
    return (lam ** (1j * gamma)) * total / mp.sqrt(L)


def K_numpy_grid(
    lambda_sq: int,
    n_bound: int,
    coeffs: np.ndarray,
    t_grid: np.ndarray,
    plant_index: Optional[int] = None,
    plant_rel: float = 0.0,
) -> np.ndarray:
    L = math.log(lambda_sq)
    lam = math.sqrt(lambda_sq)
    n = np.arange(-n_bound, n_bound + 1, dtype=np.float64)
    out = np.empty_like(t_grid, dtype=np.complex128)
    for start in range(0, len(t_grid), 20000):
        t = t_grid[start : start + 20000]
        alpha = 2.0 * math.pi * n[:, None] / L - t[None, :]
        z = 1j * alpha * L
        integral = np.empty_like(z, dtype=np.complex128)
        small = np.abs(z) < 1e-12
        integral[small] = L
        integral[~small] = L * np.expm1(z[~small]) / z[~small]
        vhat = (lam ** (1j * t))[None, :] * integral / math.sqrt(L)
        if plant_index is not None:
            vhat[plant_index, :] *= 1.0 + plant_rel
        out[start : start + 20000] = (coeffs[:, None] * vhat).sum(axis=0)
    return out


def real_plancherel(lambda_sq: int, n_bound: int, cache: Dict[str, Any]) -> Dict[str, Any]:
    coeffs_np = np.array(
        [complex(float(row["re"]), float(row["im"])) for row in cache["coefficients"]],
        dtype=np.complex128,
    )
    refinements = [(250.0, 0.1), (500.0, 0.1), (500.0, 0.05), (1000.0, 0.05)]
    rows: List[Dict[str, Any]] = []
    prev = None
    for T, h in refinements:
        grid = np.arange(-T, T + h / 2.0, h, dtype=np.float64)
        vals = K_numpy_grid(lambda_sq, n_bound, coeffs_np, grid)
        P = float(np.trapezoid(np.abs(vals) ** 2, grid) / (2.0 * math.pi))
        rows.append(
            {
                "T": T,
                "h": h,
                "grid_points": int(len(grid)),
                "P": P,
                "abs_P_minus_1": abs(P - 1.0),
                "delta_from_previous": None if prev is None else abs(P - prev),
            }
        )
        prev = P
    final = rows[-1]
    max_conv_delta = max(row["delta_from_previous"] or 0.0 for row in rows[1:])
    max_idx = int(np.argmax(np.abs(coeffs_np)))
    T = final["T"]
    h = final["h"]
    grid = np.arange(-T, T + h / 2.0, h, dtype=np.float64)
    clean_vals = K_numpy_grid(lambda_sq, n_bound, coeffs_np, grid)
    planted_vals = K_numpy_grid(lambda_sq, n_bound, coeffs_np, grid, plant_index=max_idx, plant_rel=1e-6)
    P_clean = float(np.trapezoid(np.abs(clean_vals) ** 2, grid) / (2.0 * math.pi))
    P_planted = float(np.trapezoid(np.abs(planted_vals) ** 2, grid) / (2.0 * math.pi))
    plant_delta = abs(P_planted - P_clean)
    plant_threshold = max(1e-8, 100.0 * max_conv_delta)
    return {
        "method": "real t-quadrature: composite trapezoid on symmetric finite t-ranges with T/h refinement",
        "unitarity_identity_not_used_for_verdict": True,
        "coefficient_side_plant_used_for_verdict": False,
        "refinements": rows,
        "P": P_clean,
        "abs_P_minus_1": abs(P_clean - 1.0),
        "registered_tolerance": PLANCHEREL_TOL,
        "convergence_max_delta": max_conv_delta,
        "code": "PLANCHEREL_REAL_PASS" if abs(P_clean - 1.0) <= float(PLANCHEREL_TOL) else "PLANCHEREL_REAL_FAILS",
        "transform_planted_violation": {
            "operation": "multiply one Vhat_n(t) transform evaluation stream by 1+1e-6; coefficients unchanged",
            "n": int(cache["coefficients"][max_idx]["n"]),
            "plant_rel": "1e-6",
            "P_clean_same_grid": P_clean,
            "P_planted": P_planted,
            "delta_from_clean": plant_delta,
            "judge_threshold": plant_threshold,
            "judge_fires": plant_delta > plant_threshold,
        },
    }


def anchor_reproduction(cache: Dict[str, Any], zero_profile: Dict[str, Any]) -> Dict[str, Any]:
    coeffs = load_coeffs_mp(cache)
    rows = []
    max_rel = mp.mpf("0")
    for archived in zero_profile["rows"][:A1_J]:
        gamma = mp.mpf(str(archived["gamma"]))
        kval = K_mp(13, 120, gamma, coeffs)
        got = abs(kval)
        expected = mp.mpf(str(archived["abs_K"]))
        rel_diff = abs(got - expected) / max(expected, mp.mpf("1e-300"))
        max_rel = max(max_rel, rel_diff)
        rows.append(
            {
                "j": int(archived["j"]),
                "gamma": gamma,
                "archived_abs_K": expected,
                "computed_abs_K": got,
                "relative_diff": rel_diff,
                "pass": rel_diff <= ANCHOR_TOL,
            }
        )
    passed = all(row["pass"] for row in rows)
    factor = "none"
    if not passed:
        ratios = [
            row["computed_abs_K"] / row["archived_abs_K"]
            for row in rows
            if row["archived_abs_K"] != 0
        ]
        factor = fmt(sum(ratios) / len(ratios), 16) if ratios else "undefined"
    return {
        "anchor_artifact": rel(ZERO_PROFILE_JSON),
        "anchor_artifact_sha256": sha256_file(ZERO_PROFILE_JSON),
        "registered_tolerance": ANCHOR_TOL,
        "rows": rows,
        "max_relative_diff": max_rel,
        "pass": passed,
        "code": "ANCHOR_REPRODUCED" if passed else f"ANCHOR_MISMATCH({factor})",
        "side_by_side_if_failed": None
        if passed
        else {
            "archived_identity_lock": zero_profile.get("identity_lock"),
            "anchor_locked_window_map": "u in [0,L], L=log(lambda_sq), Vhat_n integral over [0,L]",
            "anchor_locked_phase_book": "lambda^(i gamma) outside the finite-window Fourier transform",
            "anchor_locked_measure": "(1/2pi) integral |K(t)|^2 dt",
            "localized_factor": factor,
        },
    }


def high_precision_zeros(count: int, zero_profile: Dict[str, Any]) -> Tuple[List[mp.mpf], Dict[str, Any]]:
    path = anchor_zeros_path(count)
    if path.exists():
        data = load_json(path)
        vals = [mp.mpf(str(row["gamma"])) for row in data.get("zeros", [])]
        if len(vals) >= count:
            return vals[:count], {
                "source": rel(path),
                "sha256": sha256_file(path),
                "loaded_from_cache": True,
                "count": count,
            }

    vals: List[mp.mpf] = []
    for row in zero_profile.get("rows", []):
        if len(vals) >= min(500, count):
            break
        vals.append(mp.mpf(str(row["gamma"])))
    start = len(vals) + 1
    if start <= count:
        progress(f"compute high-precision zeta zeros {start}..{count}")
    for j in range(start, count + 1):
        if j == start or j % 100 == 0 or j == count:
            progress(f"zetazero {j}/{count}")
        vals.append(mp.im(mp.zetazero(j)))
    payload = {
        "count": len(vals),
        "mp_dps": MP_DPS,
        "source": "zero_sum_profile_v2 rows for first 500 when available; mpmath.zetazero for the rest",
        "zeros": [{"j": i + 1, "gamma": vals[i]} for i in range(len(vals))],
    }
    write_json(path, payload)
    return vals[:count], {
        "source": rel(path),
        "sha256": sha256_file(path),
        "loaded_from_cache": False,
        "count": count,
    }


def vector_from_coeffs(coeffs: Sequence[mp.mpc]) -> mp.matrix:
    v = mp.matrix(len(coeffs), 1)
    for i, z in enumerate(coeffs):
        v[i] = z
    return v


def denominator_a1(lambda_sq: int, n_bound: int, cache: Dict[str, Any], zero_profile: Dict[str, Any]) -> Dict[str, Any]:
    if (lambda_sq, n_bound) == ANCHOR_POINT:
        return {
            "a1_raw": mp.mpf(str(zero_profile["a1_raw"])),
            "source": "out/zero_sum_profile_v2.json:a1_raw",
            "rebuilt_tau": False,
        }
    progress(f"build tau denominator lambda_sq={lambda_sq} N={n_bound}")
    T = pilot.build_tau_matrix(mp.sqrt(lambda_sq), n_bound, 80)
    v = vector_from_coeffs(load_coeffs_mp(cache))
    Tv = T * v
    return {
        "a1_raw": mp.re(pilot.inner(v, Tv)),
        "source": "fresh pilot.build_tau_matrix with anchor-loaded coefficients",
        "rebuilt_tau": True,
    }


def profile_rows(
    lambda_sq: int,
    n_bound: int,
    cache: Dict[str, Any],
    gammas: Sequence[mp.mpf],
    count: int,
) -> List[Dict[str, Any]]:
    coeffs = load_coeffs_mp(cache)
    rows = []
    partial = mp.mpf("0")
    for j, gamma in enumerate(gammas[:count], start=1):
        kval = K_mp(lambda_sq, n_bound, gamma, coeffs)
        abs_k = abs(kval)
        partial += 2 * abs_k**2
        rows.append({"j": j, "gamma": gamma, "K": kval, "abs_K": abs_k, "S_J": partial})
    return rows


def ceiling_judge(rows: Sequence[Dict[str, Any]], a1: mp.mpf) -> Dict[str, Any]:
    max_row = max(rows, key=lambda row: row["S_J"] / a1)
    max_ratio = max_row["S_J"] / a1
    violation = max_ratio > CEILING
    first = None
    if violation:
        for row in rows:
            ratio = row["S_J"] / a1
            if ratio > CEILING:
                first = {"j": row["j"], "gamma": row["gamma"], "S_J_over_a1": ratio}
                break
    return {
        "ceiling": CEILING,
        "max_j": max_row["j"],
        "max_gamma": max_row["gamma"],
        "max_S_J_over_a1": max_ratio,
        "violation": violation,
        "first_violation": first,
        "code": "CHANNEL_OBJECT_MISMATCH" if violation else None,
    }


def C_from_residual(a1: mp.mpf, gamma: mp.mpf, s_over_a1: mp.mpf) -> Optional[mp.mpf]:
    residual = a1 * (1 - s_over_a1)
    if residual <= 0:
        return None
    denom = mp.log(gamma / (2 * mp.pi)) + 1
    return mp.sqrt(residual * mp.pi * gamma / denom)


def fit_power(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    usable = [row for row in rows if row["abs_K"] > 0]
    if len(usable) < 3:
        return {"status": "INSUFFICIENT", "p": None, "count": len(usable)}
    xs = [mp.log(row["gamma"]) for row in usable]
    ys = [mp.log(row["abs_K"]) for row in usable]
    xm = sum(xs) / len(xs)
    ym = sum(ys) / len(ys)
    slope = sum((x - xm) * (y - ym) for x, y in zip(xs, ys)) / sum((x - xm) ** 2 for x in xs)
    return {"status": "OK", "slope": slope, "p": -slope, "count": len(usable)}


def crossover_retest(
    caches: Dict[Tuple[int, int], Dict[str, Any]],
    zero_profile: Dict[str, Any],
    gammas: Sequence[mp.mpf],
) -> Dict[str, Any]:
    anchors = [(12, 120), (14, 120), (13, 90)]
    out: Dict[str, Any] = {}
    for lambda_sq, n_bound in anchors:
        cache = caches[(lambda_sq, n_bound)]
        denom = denominator_a1(lambda_sq, n_bound, cache, zero_profile)
        rows = profile_rows(lambda_sq, n_bound, cache, gammas, A4_J)
        a1 = denom["a1_raw"]
        ceiling = ceiling_judge(rows, a1)
        if ceiling["violation"]:
            return {
                "status": "STOPPED_BY_A3",
                "code": "CHANNEL_OBJECT_MISMATCH",
                "point": {"lambda_sq": lambda_sq, "N": n_bound},
                "denominator": denom,
                "ceiling": ceiling,
                "peaks_reported": False,
            }
        peak = max(rows, key=lambda row: row["abs_K"])
        checkpoints = []
        for J in (100, 150, 200):
            row = rows[J - 1]
            s_over = row["S_J"] / a1
            c_val = C_from_residual(a1, row["gamma"], s_over)
            checkpoints.append(
                {
                    "J": J,
                    "gamma": row["gamma"],
                    "S_J_over_a1": s_over,
                    "R_J_over_a1": 1 - s_over,
                    "C": c_val,
                    "negative_residual": c_val is None,
                }
            )
        out[f"lambda_sq_{lambda_sq}_N_{n_bound}"] = {
            "lambda_sq": lambda_sq,
            "N": n_bound,
            "denominator": denom,
            "ceiling": ceiling,
            "peak": {"j": peak["j"], "gamma": peak["gamma"], "abs_K": peak["abs_K"]},
            "checkpoints": checkpoints,
            "S_200_over_a1": checkpoints[-1]["S_J_over_a1"],
            "S_rising_100_150_200": checkpoints[0]["S_J_over_a1"] < checkpoints[1]["S_J_over_a1"] < checkpoints[2]["S_J_over_a1"],
            "no_negative_residuals": all(not row["negative_residual"] for row in checkpoints),
        }
    peak12 = out["lambda_sq_12_N_120"]["peak"]["gamma"]
    peak14 = out["lambda_sq_14_N_120"]["peak"]["gamma"]
    peak90 = out["lambda_sq_13_N_90"]["peak"]["gamma"]
    peak12_pass = abs(peak12 - mp.mpf("150.8")) <= mp.mpf("12")
    peak14_pass = abs(peak14 - mp.mpf("175.9")) <= mp.mpf("12")
    n_physical = abs(peak90 - mp.mpf("167")) <= mp.mpf("10")
    n_nyquist = abs(peak90 - mp.mpf("125")) <= mp.mpf("10")
    s_pass = all(mp.mpf("0.3") <= cell["S_200_over_a1"] <= mp.mpf("0.9") for cell in out.values())
    rising = all(cell["S_rising_100_150_200"] for cell in out.values())
    no_negative = all(cell["no_negative_residuals"] for cell in out.values())
    if n_nyquist:
        code = "CROSSOVER_IS_NYQUIST"
    elif peak12_pass and peak14_pass and n_physical and s_pass and rising and no_negative:
        code = "CROSSOVER_CONFIRMED"
    else:
        code = "CROSSOVER_REFUTED"
    return {
        "status": "RUN",
        "profiles": out,
        "peak12_registered_pass": peak12_pass,
        "peak14_registered_pass": peak14_pass,
        "N_control_physical_pass": n_physical,
        "N_control_nyquist_signature": n_nyquist,
        "S_200_registered_pass": s_pass,
        "S_rising_registered_pass": rising,
        "no_negative_residuals_registered_pass": no_negative,
        "code": code,
    }


def tail_13_120(
    cache: Dict[str, Any],
    zero_profile: Dict[str, Any],
    gammas: Sequence[mp.mpf],
) -> Dict[str, Any]:
    denom = denominator_a1(13, 120, cache, zero_profile)
    rows = profile_rows(13, 120, cache, gammas, A5_J)
    a1 = denom["a1_raw"]
    ceiling = ceiling_judge(rows, a1)
    if ceiling["violation"]:
        return {
            "status": "STOPPED_BY_A3",
            "code": "CHANNEL_OBJECT_MISMATCH",
            "denominator": denom,
            "ceiling": ceiling,
            "tail_code": None,
        }
    checkpoints = []
    for J in (500, 750, 1000, 1500, 2000):
        row = rows[J - 1]
        s_over = row["S_J"] / a1
        checkpoints.append(
            {
                "J": J,
                "gamma": row["gamma"],
                "S_J_over_a1": s_over,
                "R_J_over_a1": 1 - s_over,
                "C": C_from_residual(a1, row["gamma"], s_over),
            }
        )
    fit_rows = [row for row in rows if mp.mpf("1200") <= row["gamma"] <= mp.mpf("2500")]
    pfit = fit_power(fit_rows)
    c_vals = [row["C"] for row in checkpoints if row["C"] is not None and row["J"] >= 500]
    c_refit = sum(c_vals) / len(c_vals) if c_vals else None
    c_ref = mp.mpf("7.9e-29")
    c_pass = c_refit is not None and abs(c_refit - c_ref) / c_ref <= mp.mpf("0.20")
    s2000 = checkpoints[-1]["S_J_over_a1"]
    rising = all(checkpoints[i]["S_J_over_a1"] < checkpoints[i + 1]["S_J_over_a1"] for i in range(len(checkpoints) - 1))
    p_pass = pfit["p"] is not None and abs(pfit["p"] - 1) <= mp.mpf("0.15")
    s_pass = mp.mpf("0.82") <= s2000 <= mp.mpf("0.95")
    if s_pass and rising and p_pass and c_pass:
        tail_code = "TAIL_FLATTENING_CONFIRMED"
    else:
        tail_code = "TAIL_FLATTENING_REFUTED"
    return {
        "status": "RUN",
        "denominator": denom,
        "ceiling": ceiling,
        "checkpoints": checkpoints,
        "S_2000_over_a1": s2000,
        "S_2000_registered_pass": s_pass,
        "rising": rising,
        "local_p_fit_gamma_1200_2500": pfit,
        "local_p_registered_pass": p_pass,
        "C_refit": c_refit,
        "C_refit_reference": c_ref,
        "C_refit_pm20_pass": c_pass,
        "tail_code": tail_code,
    }


def load_history() -> List[str]:
    if not ROUTE_STATE.exists():
        return []
    old = ROUTE_STATE.read_text(encoding="utf-8")
    if "## History" not in old:
        return []
    return [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]


def compute() -> Dict[str, Any]:
    started = time.time()
    mp.mp.dps = MP_DPS
    zero_profile = load_json(ZERO_PROFILE_JSON)
    caches = {(lambda_sq, n_bound): load_coeff_cache(lambda_sq, n_bound) for lambda_sq, n_bound in POINTS}
    provenance = {f"lambda_sq_{a}_N_{b}": provenance_lock(caches[(a, b)]) for a, b in POINTS}
    a1 = anchor_reproduction(caches[ANCHOR_POINT], zero_profile)

    a2: Dict[str, Any] = {"status": "NOT_RUN", "reason": "A1 did not pass", "all_points_pass": False}
    a3: Dict[str, Any] = {"status": "NOT_RUN"}
    a4: Dict[str, Any] = {"status": "NOT_RUN", "code": "CROSSOVER_UNTESTED"}
    a5: Dict[str, Any] = {"status": "NOT_RUN", "tail_code": None}
    zeros_meta: Dict[str, Any] = {"status": "NOT_RUN"}

    codes = [a1["code"]]
    if a1["pass"]:
        progress("A2 real Plancherel")
        a2_points = {}
        for point in POINTS:
            key = f"lambda_sq_{point[0]}_N_{point[1]}"
            a2_points[key] = real_plancherel(point[0], point[1], caches[point])
        a2_all = all(
            row["code"] == "PLANCHEREL_REAL_PASS" and row["transform_planted_violation"]["judge_fires"]
            for row in a2_points.values()
        )
        a2 = {"status": "RUN", "points": a2_points, "all_points_pass": a2_all}
        codes.append("PLANCHEREL_REAL_PASS" if a2_all else "PLANCHEREL_REAL_FAILS")
        if a2_all:
            gammas_200, zeros_meta_200 = high_precision_zeros(A4_J, zero_profile)
            progress("A4 crossover retest")
            a4 = crossover_retest(caches, zero_profile, gammas_200)
            if a4.get("code") == "CHANNEL_OBJECT_MISMATCH":
                a3 = {"status": "FAIL", "source": "A4", "ceiling": a4["ceiling"]}
                codes.append("CHANNEL_OBJECT_MISMATCH")
            else:
                codes.append(a4.get("code") or "CROSSOVER_UNTESTED")
                progress("A5 tail")
                gammas_2000, zeros_meta = high_precision_zeros(A5_J, zero_profile)
                zeros_meta["a4_zero_source"] = zeros_meta_200
                a5 = tail_13_120(caches[ANCHOR_POINT], zero_profile, gammas_2000)
                if a5.get("code") == "CHANNEL_OBJECT_MISMATCH":
                    a3 = {"status": "FAIL", "source": "A5", "ceiling": a5["ceiling"]}
                    codes.append("CHANNEL_OBJECT_MISMATCH")
                else:
                    a3 = {"status": "PASS", "source": "A4+A5"}
                    if a5.get("tail_code"):
                        codes.append(a5["tail_code"])

    if any(code == "CHANNEL_OBJECT_MISMATCH" for code in codes):
        status = "CHANNEL_OBJECT_MISMATCH"
    elif not a1["pass"]:
        status = a1["code"]
    elif a2.get("all_points_pass") is False:
        status = "PLANCHEREL_REAL_FAILS"
    else:
        status = codes[-1]

    input_files = [
        file_record(Path(__file__), "script"),
        file_record(ZERO_PROFILE_JSON, "anchor_artifact_dataset"),
        *[file_record(coeff_cache_path(a, b), f"coefficient_dataset_lambda_sq_{a}_N_{b}") for a, b in POINTS],
        file_record(ROUTE_STATE, "state_before_update"),
        file_record(LOOP_STATE, "loop_state_before_update"),
        file_record(REQUEST_DIR / "routeb_ladder_pilot.py", "imported_script"),
    ]
    payload = {
        "gate": "AnchorLockedKChannel_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "not_RH": True,
        "phase2_run": False,
        "qW_formula_changed": False,
        "packet_definition_changed": False,
        "q3_main_touched": False,
        "status": status,
        "codes": codes,
        "rollback": {
            "previous_plancherel_entry": "VOID_TAUTOLOGICAL_JUDGE",
            "previous_crossover": "UNTESTED",
            "reason": "PortableKChannel_v1 used coefficient-side Plancherel identity and float/complex128 zero-profile path; AnchorLockedKChannel_v1 is the replacement gate.",
        },
        "A0_provenance_lock": provenance,
        "A1_anchor_reproduction": a1,
        "A2_real_plancherel": a2,
        "A3_standing_ceiling": a3,
        "A4_crossover_retest": a4,
        "A5_tail_13_120": a5,
        "high_precision_zeros": zeros_meta,
        "action_log_inputs": {
            "scripts_and_args": [{"python": sys.executable, "script": rel(Path(__file__)), "args": sys.argv[1:]}],
            "files_and_sha256": input_files,
            "datasets_loaded_sha256": [row for row in input_files if "dataset" in row["role"] or "state" in row["role"]],
            "git_diff_stat_before_outputs": git_diff_stat(),
            "git_status_short_before_outputs": git_status_short(),
        },
        "elapsed_s": time.time() - started,
    }
    return payload


def write_report(payload: Dict[str, Any]) -> None:
    a1 = payload["A1_anchor_reproduction"]
    a2 = payload["A2_real_plancherel"]
    a4 = payload["A4_crossover_retest"]
    a5 = payload["A5_tail_13_120"]
    lines = [
        "# AnchorLockedKChannel_v1",
        "",
        "## Headlines",
        "",
        f"1. Anchor reproduced? `{'YES' if a1['pass'] else 'NO'}`",
        f"2. Real Plancherel pass? `{'YES' if a2.get('all_points_pass') else 'NO'}`",
        f"3. Standing ceiling: `{payload['A3_standing_ceiling'].get('status')}`",
        f"4. Crossover: `{a4.get('code') or a4.get('status')}`",
        f"5. Tail: `{a5.get('tail_code') or a5.get('status')}`",
        f"6. Verdict codes: {', '.join(f'`{code}`' for code in payload['codes'])}",
        "",
        "Diagnostic only: not RH, no Phase 2, no QW formula changes, no packet-definition changes, no Q3 mainline changes.",
        "",
        "## Rollback",
        "",
        "- Previous portable Plancherel entry: `VOID_TAUTOLOGICAL_JUDGE`.",
        "- Previous crossover entry: `UNTESTED`.",
        "",
        "## A0 Provenance Lock",
        "",
        "| point | coeff file | sha256 | Sum |c|^2 | fields ok |",
        "| --- | --- | --- | ---: | --- |",
    ]
    for key, row in payload["A0_provenance_lock"].items():
        lines.append(
            f"| `{key}` | `{row['coefficient_file']}` | `{row['coefficient_file_sha256']}` | `{fmt(row['sum_abs_c_n_sq'], 14)}` | `{row['provenance_fields_ok']}` |"
        )
    lines.extend(
        [
            "",
            "## A1 Anchor Reproduction",
            "",
            f"- anchor artifact: `{a1['anchor_artifact']}` sha256 `{a1['anchor_artifact_sha256']}`.",
            f"- max relative diff j<=10: `{fmt(a1['max_relative_diff'], 12)}`; tolerance `1e-6`; code `{a1['code']}`.",
            "",
            "| j | gamma | archived | computed | rel diff |",
            "| ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for row in a1["rows"]:
        lines.append(
            f"| {row['j']} | `{fmt(row['gamma'], 14)}` | `{fmt(row['archived_abs_K'], 12)}` | `{fmt(row['computed_abs_K'], 12)}` | `{fmt(row['relative_diff'], 8)}` |"
        )
    lines.extend(["", "## A2 Real Plancherel", ""])
    if a2.get("status") == "RUN":
        lines.extend(["| point | P | |P-1| | code | plant fires |", "| --- | ---: | ---: | --- | --- |"])
        for key, row in a2["points"].items():
            plant = row["transform_planted_violation"]
            lines.append(
                f"| `{key}` | `{fmt(row['P'], 12)}` | `{fmt(row['abs_P_minus_1'], 8)}` | `{row['code']}` | `{plant['judge_fires']}` |"
            )
        lines.append("")
        lines.append("- Method: real t-quadrature on symmetric t-ranges; coefficient identity not used for verdict.")
        lines.append("- Planted violation perturbs one `Vhat_n(t)` stream by `1e-6`; coefficient-side plants do not count.")
    else:
        lines.append(f"- status: `{a2.get('status')}`; reason: {a2.get('reason')}.")
    lines.extend(["", "## A4 Crossover", ""])
    if a4.get("status") == "RUN":
        lines.extend(["| point | peak gamma | S200/a1 | R200/a1 |", "| --- | ---: | ---: | ---: |"])
        for key, cell in a4["profiles"].items():
            chk = cell["checkpoints"][-1]
            lines.append(
                f"| `{key}` | `{fmt(cell['peak']['gamma'], 12)}` | `{fmt(chk['S_J_over_a1'], 12)}` | `{fmt(chk['R_J_over_a1'], 12)}` |"
            )
        lines.append(f"- code: `{a4['code']}`.")
    else:
        lines.append(f"- status: `{a4.get('status')}`; code `{a4.get('code')}`.")
        if a4.get("ceiling"):
            lines.append(f"- ceiling violation: `{fmt(a4['ceiling']['max_S_J_over_a1'], 12)}`.")
    lines.extend(["", "## A5 Tail", ""])
    if a5.get("status") == "RUN":
        lines.extend(["| J | S_J/a1 | R_J/a1 | C |", "| ---: | ---: | ---: | ---: |"])
        for row in a5["checkpoints"]:
            lines.append(
                f"| {row['J']} | `{fmt(row['S_J_over_a1'], 12)}` | `{fmt(row['R_J_over_a1'], 12)}` | `{fmt(row['C'], 12)}` |"
            )
        lines.append(f"- local p: `{fmt(a5['local_p_fit_gamma_1200_2500'].get('p'), 12)}`; pass `{a5['local_p_registered_pass']}`.")
        lines.append(f"- C_refit: `{fmt(a5['C_refit'], 12)}`; pass `{a5['C_refit_pm20_pass']}`.")
        lines.append(f"- tail code: `{a5['tail_code']}`.")
    else:
        lines.append(f"- status: `{a5.get('status')}`; code `{a5.get('code')}`.")
        if a5.get("ceiling"):
            lines.append(f"- ceiling violation: `{fmt(a5['ceiling']['max_S_J_over_a1'], 12)}`.")
    lines.extend(
        [
            "",
            "## Actions Log",
            "",
            f"- Required actions log: `{rel(ACTIONS_LOG)}`.",
        ]
    )
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_route_state(payload: Dict[str, Any]) -> None:
    history = load_history()
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    history.append(
        f"- {now}: AnchorLockedKChannel_v1 -> {', '.join(payload['codes'])}; "
        f"A1={payload['A1_anchor_reproduction']['pass']}; "
        f"A2={payload['A2_real_plancherel'].get('all_points_pass')}; "
        f"A4={payload['A4_crossover_retest'].get('code')}; "
        f"A5={payload['A5_tail_13_120'].get('tail_code') or payload['A5_tail_13_120'].get('status')}."
    )
    a1 = payload["A1_anchor_reproduction"]
    a2 = payload["A2_real_plancherel"]
    a3 = payload["A3_standing_ceiling"]
    a4 = payload["A4_crossover_retest"]
    a5 = payload["A5_tail_13_120"]
    lines = [
        "# ROUTE_B_STATE",
        "",
        "## DOOR",
        "",
        f"`AnchorLockedKChannel_v1: {', '.join(payload['codes'])}`",
        "",
        "## LOCAL DIAGNOSTIC SUPPORT",
        "",
        "- Previous PortableKChannel_v1 Plancherel is voided as `VOID_TAUTOLOGICAL_JUDGE`.",
        "- Previous PortableKChannel_v1 crossover is reset to `UNTESTED`.",
        f"- Anchor reproduction j<=10: `{a1['code']}` with max relative diff `{fmt(a1['max_relative_diff'], 8)}`.",
        f"- Real t-quadrature Plancherel all points pass `{a2.get('all_points_pass')}`.",
        "",
        "## OPEN",
        "",
        "- No RH inference; alpha-Gate remains RH-equivalent core.",
        "- DISPLACED_PROFILE remains unpromoted unless anchor, real Plancherel, crossover, and tail gates all pass.",
        "",
        "## ANCHOR LOCKED K CHANNEL V1",
        "",
        f"- A0 provenance points: `{len(payload['A0_provenance_lock'])}`.",
        f"- A1 anchor code `{a1['code']}`.",
        f"- A2 status `{a2.get('status')}`; all pass `{a2.get('all_points_pass')}`.",
        f"- A3 standing ceiling `{a3.get('status')}`.",
        f"- A4 crossover `{a4.get('code') or a4.get('status')}`.",
        f"- A5 tail `{a5.get('tail_code') or a5.get('status')}`.",
        f"- Actions log `{rel(ACTIONS_LOG)}`.",
        "",
        "## NEXT STEP",
        "",
        "STOP: hand off AnchorLockedKChannel_v1 result to reviewer before promoting any Route B state.",
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


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "ANCHOR_LOCKED_K_CHANNEL_V1_COMPLETE",
            "last_verdict": payload["status"],
            "last_codes": payload["codes"],
            "last_report": "anchor_locked_k_channel_v1.md",
            "last_json": "out/anchor_locked_k_channel_v1.json",
            "anchor_locked_A1_code": payload["A1_anchor_reproduction"]["code"],
            "anchor_locked_A2_all_points_pass": payload["A2_real_plancherel"].get("all_points_pass"),
            "anchor_locked_A3_status": payload["A3_standing_ceiling"].get("status"),
            "anchor_locked_A4_code": payload["A4_crossover_retest"].get("code"),
            "anchor_locked_A5_tail_code": payload["A5_tail_13_120"].get("tail_code"),
            "portable_k_plancherel_status": "VOID_TAUTOLOGICAL_JUDGE",
            "portable_k_crossover_code": "UNTESTED",
            "phase2_run": False,
            "qW_formula_changed": False,
            "packet_definition_changed": False,
            "q3_main_touched": False,
            "next_gate": "STOP_AFTER_ANCHOR_LOCKED_K_CHANNEL_V1",
            "updated_at_unix": time.time(),
        }
    )
    write_json(LOOP_STATE, state)


def write_handoff(payload: Dict[str, Any]) -> None:
    a1 = payload["A1_anchor_reproduction"]
    a2 = payload["A2_real_plancherel"]
    a4 = payload["A4_crossover_retest"]
    a5 = payload["A5_tail_13_120"]
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "AnchorLockedKChannel_v1 / Route B / Route Z E5",
        "",
        "Status:",
        "NOT_RH. Diagnostic only. No Phase 2. No QW formula changes. No packet-definition changes. Q3 mainline not touched.",
        "",
        "Mandatory rollback:",
        "- old PortableKChannel Plancherel = VOID_TAUTOLOGICAL_JUDGE",
        "- old crossover = UNTESTED",
        "",
        "Codes:",
        ", ".join(payload["codes"]),
        "",
        "A0 provenance:",
        f"- coefficient files locked for {len(payload['A0_provenance_lock'])} points; sha256 recorded in actions log.",
        "",
        "A1 anchor reproduction:",
        f"- code = {a1['code']}",
        f"- max rel diff j<=10 = {fmt(a1['max_relative_diff'], 12)}",
        f"- anchor sha256 = {a1['anchor_artifact_sha256']}",
        "",
        "A2 real Plancherel:",
        f"- all points pass = {a2.get('all_points_pass')}",
        "- method = real t-quadrature, not coefficient identity",
        "- transform-side planted Vhat perturbation fires at every passing point",
        "",
        "A4 crossover:",
        f"- status/code = {a4.get('code') or a4.get('status')}",
    ]
    if a4.get("status") == "RUN":
        for key, cell in a4["profiles"].items():
            chk = cell["checkpoints"][-1]
            lines.append(f"- {key}: peak={fmt(cell['peak']['gamma'], 12)}, S200/a1={fmt(chk['S_J_over_a1'], 12)}")
    elif a4.get("ceiling"):
        lines.append(f"- stopped by ceiling at S/a1={fmt(a4['ceiling']['max_S_J_over_a1'], 12)}")
    lines.extend(["", "A5 tail:", f"- status/code = {a5.get('tail_code') or a5.get('status')}"])
    if a5.get("status") == "RUN":
        lines.append(f"- S2000/a1 = {fmt(a5['S_2000_over_a1'], 12)}")
        lines.append(f"- local p = {fmt(a5['local_p_fit_gamma_1200_2500'].get('p'), 12)}")
        lines.append(f"- C_refit = {fmt(a5['C_refit'], 12)}")
    elif a5.get("ceiling"):
        lines.append(f"- stopped by ceiling at S/a1={fmt(a5['ceiling']['max_S_J_over_a1'], 12)}")
    lines.extend(
        [
            "",
            "Actions log:",
            rel(ACTIONS_LOG),
            "",
            "Reviewer question:",
            "Can we accept the anchored real-Plancherel K object for downstream E5 diagnostics, or does the crossover/tail result still show a channel-object mismatch?",
        ]
    )
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_actions_log(payload: Dict[str, Any]) -> None:
    output_files = [
        file_record(JSON_OUT, "output_json"),
        file_record(REPORT, "output_report"),
        file_record(HANDOFF, "output_handoff"),
        file_record(ROUTE_STATE, "updated_state"),
        file_record(LOOP_STATE, "updated_loop_state"),
        file_record(anchor_zeros_path(A4_J), "generated_or_loaded_high_precision_zero_dataset_J200"),
        file_record(anchor_zeros_path(A5_J), "generated_or_loaded_high_precision_zero_dataset_J2000"),
    ]
    lines = [
        "# AnchorLockedKChannel_v1 Actions Log",
        "",
        "## Scripts And Args",
        "",
    ]
    for row in payload["action_log_inputs"]["scripts_and_args"]:
        lines.append(f"- python: `{row['python']}`; script: `{row['script']}`; args: `{row['args']}`")
    lines.extend(["", "## Files And SHA256", ""])
    for row in payload["action_log_inputs"]["files_and_sha256"] + output_files:
        lines.append(f"- `{row['role']}` `{row['path']}` sha256 `{row['sha256']}` exists `{row['exists']}`")
    lines.extend(["", "## Datasets Loaded And SHA256", ""])
    for row in payload["action_log_inputs"]["datasets_loaded_sha256"]:
        lines.append(f"- `{row['role']}` `{row['path']}` sha256 `{row['sha256']}`")
    lines.extend(["", "## Git Diff Stat", "", "```text", git_diff_stat(), "```", ""])
    lines.extend(["", "## Git Status Short", "", "```text", git_status_short(), "```", ""])
    ACTIONS_LOG.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    payload = compute()
    write_json(JSON_OUT, payload)
    write_report(payload)
    update_route_state(payload)
    update_loop_state(payload)
    write_handoff(payload)
    write_actions_log(payload)
    print(payload["status"])
    print("codes=" + ",".join(payload["codes"]))
    print("A1=" + payload["A1_anchor_reproduction"]["code"])
    print("A2=" + str(payload["A2_real_plancherel"].get("all_points_pass")))
    print("A4=" + str(payload["A4_crossover_retest"].get("code") or payload["A4_crossover_retest"].get("status")))
    print("A5=" + str(payload["A5_tail_13_120"].get("tail_code") or payload["A5_tail_13_120"].get("status")))


if __name__ == "__main__":
    main()
