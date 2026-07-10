#!/usr/bin/env python3
"""
TailReturnProbe_v1 for Route B / Route Z E5.

Diagnostic only:
- NOT_RH
- no Phase 2
- no QW formula changes
- no packet-definition changes
- no Q3 mainline changes
"""

from __future__ import annotations

import json
import hashlib
import math
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import mpmath as mp

import anchor_locked_extraction_v1 as extraction


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "tail_return_probe_v1.json"
ZEROS_2000 = OUT_DIR / "anchor_locked_zeros_first_2000.json"
ZEROS_5000 = OUT_DIR / "anchor_locked_zeros_first_5000.json"
ZERO_PROFILE_JSON = OUT_DIR / "zero_sum_profile_v2.json"

PINNED_ZEROS_2000_SHA = "60dba843b9dca732b232d1bf4f3a133b174ca403fd9929d99d49122a38303356"
PINNED_COEFF_SHA = "0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88"
LAMBDA_SQ = 13
N_BOUND = 120
COUNT = 5000
MP_DPS = 100
mp.mp.dps = MP_DPS
CEILING = mp.mpf("1.05")
REF_C = mp.mpf("7.9e-29")


def progress(label: str) -> None:
    print(f"[TailReturnProbe_v1] {label}", flush=True)


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


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, mp.mpf):
        return mp.nstr(value, 90)
    if isinstance(value, mp.mpc):
        return {"re": mp.nstr(mp.re(value), 90), "im": mp.nstr(mp.im(value), 90)}
    return value


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def coeff_cache_path(lambda_sq: int, n_bound: int) -> Path:
    return OUT_DIR / f"portable_k_coeffs_lambda_sq_{lambda_sq}_N_{n_bound}.json"


def parse_coeff_rows(rows: Sequence[Dict[str, Any]]) -> List[mp.mpc]:
    return [mp.mpc(mp.mpf(str(row["re"])), mp.mpf(str(row["im"]))) for row in rows]


def load_coeff_cache(lambda_sq: int, n_bound: int) -> Dict[str, Any]:
    path = coeff_cache_path(lambda_sq, n_bound)
    data = load_json(path)
    data["_path"] = path
    data["_sha256"] = sha256_file(path)
    return data


def load_coeffs_mp(cache: Dict[str, Any]) -> List[mp.mpc]:
    return parse_coeff_rows(cache["coefficients"])


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


def C_from_residual(a1: mp.mpf, gamma: mp.mpf, s_over_a1: mp.mpf) -> Optional[mp.mpf]:
    residual = a1 * (1 - s_over_a1)
    if residual <= 0:
        return None
    denom = mp.log(gamma / (2 * mp.pi)) + 1
    return mp.sqrt(residual * mp.pi * gamma / denom)


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


def load_zero_cache_2000() -> List[mp.mpf]:
    actual = sha256_file(ZEROS_2000)
    if actual != PINNED_ZEROS_2000_SHA:
        raise RuntimeError(f"pinned 2000-zero cache sha mismatch: {actual}")
    data = load_json(ZEROS_2000)
    rows = data.get("zeros", [])
    if len(rows) < 2000:
        raise RuntimeError(f"2000-zero cache has only {len(rows)} rows")
    vals = [mp.mpf(str(row["gamma"])) for row in rows[:2000]]
    for idx, row in enumerate(rows[:2000], start=1):
        if int(row["j"]) != idx:
            raise RuntimeError(f"2000-zero cache j mismatch at row {idx}: {row['j']}")
    return vals


def extend_zeros_to_5000(parent: Sequence[mp.mpf]) -> Tuple[List[mp.mpf], Dict[str, Any]]:
    if ZEROS_5000.exists():
        data = load_json(ZEROS_5000)
        rows = data.get("zeros", [])
        if len(rows) >= COUNT:
            vals = [mp.mpf(str(row["gamma"])) for row in rows[:COUNT]]
            if vals[:2000] == list(parent):
                return vals, {
                    "source": rel(ZEROS_5000),
                    "sha256": sha256_file(ZEROS_5000),
                    "loaded_from_cache": True,
                    "parent_cache_verified": True,
                    "count": COUNT,
                }
            progress("existing 5000-zero cache ignored: first 2000 rows do not match pinned parent")

    vals = list(parent)
    progress("extend zeros 2001..5000 using mpmath.zetazero")
    for j in range(2001, COUNT + 1):
        vals.append(mp.im(mp.zetazero(j)))
        if j % 500 == 0 or j == COUNT:
            progress(f"zetazero {j}/{COUNT}")

    payload = {
        "count": len(vals),
        "mp_dps": MP_DPS,
        "source": "anchor_locked_zeros_first_2000.json for j<=2000; mpmath.zetazero for j=2001..5000",
        "parent_cache": {
            "path": rel(ZEROS_2000),
            "sha256": PINNED_ZEROS_2000_SHA,
        },
        "zeros": [{"j": i + 1, "gamma": vals[i]} for i in range(len(vals))],
    }
    write_json(ZEROS_5000, payload)
    return vals, {
        "source": rel(ZEROS_5000),
        "sha256": sha256_file(ZEROS_5000),
        "loaded_from_cache": False,
        "parent_cache_verified": True,
        "count": COUNT,
    }


def f_tail(gamma: mp.mpf) -> mp.mpf:
    return (mp.log(gamma / (2 * mp.pi)) + 1) / gamma


def c_eff_from_window(delta_s_abs: mp.mpf, g_lo: mp.mpf, g_hi: mp.mpf) -> Optional[mp.mpf]:
    denom = f_tail(g_lo) - f_tail(g_hi)
    if delta_s_abs <= 0 or denom <= 0:
        return None
    return mp.sqrt(delta_s_abs * mp.pi / denom)


def median(vals: Sequence[mp.mpf]) -> Optional[mp.mpf]:
    if not vals:
        return None
    ordered = sorted(vals)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return (ordered[mid - 1] + ordered[mid]) / 2


def c_refit(rows: Sequence[Dict[str, Any]], a1: mp.mpf) -> Dict[str, Any]:
    all_cs: List[mp.mpf] = []
    grid_cs: List[mp.mpf] = []
    checkpoint_js = [500, 750, 1000, 1500, 2000, 2500, 3000, 4000, 5000]
    checkpoint_cs: List[Dict[str, Any]] = []
    for row in rows[499:COUNT]:
        s_over_a1 = row["S_J"] / a1
        c = C_from_residual(a1, row["gamma"], s_over_a1)
        if c is not None:
            all_cs.append(c)
            if row["j"] % 100 == 0:
                grid_cs.append(c)
        if row["j"] in checkpoint_js:
            checkpoint_cs.append({"j": row["j"], "gamma": row["gamma"], "C_from_residual": c})
    med = median(all_cs)
    grid_med = median(grid_cs)
    checkpoint_vals = [row["C_from_residual"] for row in checkpoint_cs if row["C_from_residual"] is not None]
    checkpoint_mean = sum(checkpoint_vals) / len(checkpoint_vals) if checkpoint_vals else None
    rel_miss_checkpoint = abs(checkpoint_mean - REF_C) / REF_C if checkpoint_mean is not None else None
    rel_miss_all = abs(med - REF_C) / REF_C if med is not None else None
    return {
        "reference_C": REF_C,
        "all_J_500_5000_count": len(all_cs),
        "median_all_J_500_5000": med,
        "relative_miss_all_J_median_vs_7p9e_minus_29": rel_miss_all,
        "grid_step_100_count": len(grid_cs),
        "median_grid_step_100": grid_med,
        "checkpoint_mean": checkpoint_mean,
        "checkpoint_values": checkpoint_cs,
        "relative_miss_vs_7p9e_minus_29": rel_miss_checkpoint,
        "pass_pm15": bool(rel_miss_checkpoint is not None and rel_miss_checkpoint <= mp.mpf("0.15")),
        "primary_rule": "AnchorLocked-compatible checkpoint mean over J=500,750,1000,1500,2000,2500,3000,4000,5000",
    }


def checkpoint(rows: Sequence[Dict[str, Any]], a1: mp.mpf, j: int) -> Dict[str, Any]:
    row = rows[j - 1]
    return {
        "j": j,
        "gamma": row["gamma"],
        "S_J": row["S_J"],
        "S_J_over_a1": row["S_J"] / a1,
        "C_from_residual": C_from_residual(a1, row["gamma"], row["S_J"] / a1),
    }


def window_row(rows: Sequence[Dict[str, Any]], a1: mp.mpf, name: str, j_lo: int, j_hi: int) -> Dict[str, Any]:
    left = rows[j_lo - 1]
    right = rows[j_hi - 1]
    delta_s = right["S_J"] - left["S_J"]
    c_eff = c_eff_from_window(delta_s, left["gamma"], right["gamma"])
    return {
        "name": name,
        "j_lo": j_lo,
        "j_hi": j_hi,
        "gamma_lo": left["gamma"],
        "gamma_hi": right["gamma"],
        "DeltaS": delta_s,
        "DeltaS_over_a1": delta_s / a1,
        "C_eff": c_eff,
    }


def p_mass_row(left: Dict[str, Any], right: Dict[str, Any]) -> Dict[str, Any]:
    target = float(left["DeltaS"] / right["DeltaS"])
    solve = extraction.solve_p_for_ratio(
        float(left["gamma_lo"]),
        float(left["gamma_hi"]),
        float(right["gamma_hi"]),
        target,
    )
    return {
        "adjacent_pair": f"{left['name']}/{right['name']}",
        "DeltaS_ratio": target,
        "solve": solve,
    }


def zoned_realness(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    zones = [(2000, 2500), (2500, 3000), (3000, 4000), (4000, 5000)]
    out = []
    for j_lo, j_hi in zones:
        max_imag_leak = mp.mpf("0")
        max_nonfinite = 0
        for row in rows[j_lo - 1 : j_hi]:
            kval = row["K"]
            mass = kval * mp.conj(kval)
            max_imag_leak = max(max_imag_leak, abs(mp.im(mass)))
            if not (mp.isfinite(mp.re(kval)) and mp.isfinite(mp.im(kval)) and mp.isfinite(row["abs_K"])):
                max_nonfinite += 1
        out.append(
            {
                "j_lo": j_lo,
                "j_hi": j_hi,
                "max_imaginary_part_of_K_conjK": max_imag_leak,
                "nonfinite_entries": max_nonfinite,
                "pass": max_nonfinite == 0,
            }
        )
    return {"zones": out, "pass": all(row["pass"] for row in out)}


def main() -> None:
    started = time.time()
    mp.mp.dps = MP_DPS
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    parent_zeros = load_zero_cache_2000()
    gammas, zeros_info = extend_zeros_to_5000(parent_zeros)

    zero_profile = load_json(ZERO_PROFILE_JSON)
    coeff_cache = load_coeff_cache(LAMBDA_SQ, N_BOUND)
    coeff_sha_ok = coeff_cache["_sha256"] == PINNED_COEFF_SHA
    if not coeff_sha_ok:
        raise RuntimeError(f"coefficient cache sha mismatch: {coeff_cache['_sha256']}")
    a1_info = {
        "a1_raw": mp.mpf(str(zero_profile["a1_raw"])),
        "source": "out/zero_sum_profile_v2.json:a1_raw",
        "rebuilt_tau": False,
    }
    a1 = mp.mpf(a1_info["a1_raw"])

    coeffs = load_coeffs_mp(coeff_cache)
    rows: List[Dict[str, Any]] = []
    partial = mp.mpf("0")
    progress("profile anchored portable K at (13,120)")
    for j, gamma in enumerate(gammas, start=1):
        kval = K_mp(LAMBDA_SQ, N_BOUND, gamma, coeffs)
        abs_k = abs(kval)
        partial += 2 * abs_k**2
        rows.append({"j": j, "gamma": gamma, "K": kval, "abs_K": abs_k, "S_J": partial})
        if j % 500 == 0 or j == COUNT:
            progress(f"profile {j}/{COUNT}")

    checkpoints = [checkpoint(rows, a1, j) for j in [2500, 3000, 4000, 5000]]
    windows = [
        window_row(rows, a1, "W5", 2000, 2500),
        window_row(rows, a1, "W6", 2500, 3000),
        window_row(rows, a1, "W7", 3000, 4000),
        window_row(rows, a1, "W8", 4000, 5000),
    ]
    p_rows = [p_mass_row(windows[1], windows[2]), p_mass_row(windows[2], windows[3])]
    ceiling = ceiling_judge(rows, a1)
    refit = c_refit(rows, a1)
    realness = zoned_realness(rows)

    s_ratios = [row["S_J_over_a1"] for row in checkpoints]
    strictly_rising = all(b > a for a, b in zip(s_ratios, s_ratios[1:]))
    c_w8 = windows[-1]["C_eff"]
    r1_pass = bool(c_w8 is not None and mp.mpf("6e-29") <= c_w8 <= mp.mpf("1.1e-28"))
    trough_extended = all(row["C_eff"] is not None and row["C_eff"] < mp.mpf("4e-29") for row in windows)
    s5000 = checkpoints[-1]["S_J_over_a1"]
    r2_pass = mp.mpf("0.90") <= s5000 <= mp.mpf("0.96") and strictly_rising
    p_w7_w8 = p_rows[-1]["solve"].get("p")
    r4_pass = isinstance(p_w7_w8, float) and 0.7 <= p_w7_w8 <= 1.5
    ledger_code = "LEDGER_CONSISTENT" if refit["pass_pm15"] else "LEDGER_INCONSISTENT"
    mass_code = "MASS_P_CONFIRMED" if r4_pass else "MASS_P_OUT_OF_RANGE"

    if ceiling["violation"]:
        code = "CHANNEL_OBJECT_MISMATCH"
    elif r1_pass and r2_pass and refit["pass_pm15"] and r4_pass and realness["pass"]:
        code = "TAIL_RETURN_CONFIRMED"
    elif trough_extended:
        code = "TROUGH_EXTENDED"
    else:
        code = "AMBIGUOUS"

    payload: Dict[str, Any] = {
        "goal": "TailReturnProbe_v1",
        "diagnostic_scope": {
            "NOT_RH": True,
            "phase2_changed": False,
            "qw_or_packet_definition_changed": False,
            "q3_mainline_changed": False,
        },
            "parameters": {"lambda_sq": LAMBDA_SQ, "N": N_BOUND, "mp_dps": MP_DPS, "count": COUNT},
        "inputs": {
            "zeros_2000": {
                "path": rel(ZEROS_2000),
                "sha256": sha256_file(ZEROS_2000),
                "pinned_sha256": PINNED_ZEROS_2000_SHA,
            },
            "zeros_5000": zeros_info,
            "coefficient_cache": {
                "path": rel(coeff_cache["_path"]),
                "sha256": coeff_cache["_sha256"],
                "pinned_sha256": PINNED_COEFF_SHA,
            },
            "zero_profile": {
                "path": rel(ZERO_PROFILE_JSON),
                "sha256": sha256_file(ZERO_PROFILE_JSON),
            },
            "a1_info": a1_info,
        },
        "tail_profile": {
            "checkpoints": checkpoints,
            "windows": windows,
            "p_mass_rows": p_rows,
            "c_refit": refit,
            "ceiling_judge": ceiling,
            "zoned_realness_judge": realness,
        },
        "registered": {
            "R1_trough_exit_C_eff_W8_band": {"pass": r1_pass, "measured": c_w8, "band": ["6e-29", "1.1e-28"]},
            "R1_fork_trough_extended": {"pass": trough_extended, "condition": "all W5..W8 C_eff < 4e-29"},
            "R2_S5000_band_and_rising": {
                "pass": r2_pass,
                "S5000_over_a1": s5000,
                "band": ["0.90", "0.96"],
                "strictly_rising": strictly_rising,
            },
            "R3_ledger_C_refit_pm15": {"pass": refit["pass_pm15"], "relative_miss": refit["relative_miss_vs_7p9e_minus_29"]},
            "R4_p_mass_W7_W8_band": {"pass": r4_pass, "measured": p_w7_w8, "band": ["0.7", "1.5"]},
            "ceiling_never_fires": {"pass": not ceiling["violation"], "max_S_J_over_a1": ceiling["max_S_J_over_a1"]},
            "zoned_realness": {"pass": realness["pass"]},
        },
        "codes": [code, ledger_code, mass_code],
        "elapsed_seconds": time.time() - started,
    }
    write_json(JSON_OUT, payload)
    progress(f"wrote {rel(JSON_OUT)}")


if __name__ == "__main__":
    main()
