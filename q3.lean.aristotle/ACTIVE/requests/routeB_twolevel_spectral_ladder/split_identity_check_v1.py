#!/usr/bin/env python3
"""
SplitIdentityCheck_v1 for Route B / Route Z E5.

Diagnostic only:
- NOT_RH
- no Phase 2
- no QW formula changes
- no packet-definition changes
- no Q3 mainline changes
"""

from __future__ import annotations

import hashlib
import json
import time
from pathlib import Path
from typing import Any, Dict, List, Sequence

import mpmath as mp

import leakage_falsifier_v1 as leakage
import tail_return_probe_v1 as tail


REQUEST_DIR = Path(__file__).resolve().parent
REPO_ROOT = REQUEST_DIR.parents[3]
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "split_identity_check_v1.json"
GOAL_FILE = REQUEST_DIR / "bus" / "004_split_identity_check.goal.md"
PEN_NOTE = REPO_ROOT / "q3.lean.aristotle" / "docs" / "PEN_3_1_3_LG_INCOHERENCE_v2.md"
ZEROS_5000 = OUT_DIR / "anchor_locked_zeros_first_5000.json"
LEAKAGE_JSON = OUT_DIR / "leakage_falsifier_v1.json"

LAMBDA_SQ = 13
N_BOUND = 120
M_EDGE = LAMBDA_SQ
MP_DPS = 90
PINNED_COEFF_SHA = "0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88"


def progress(label: str) -> None:
    print(f"[SplitIdentityCheck_v1] {label}", flush=True)


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


def complex_cell(z: mp.mpc) -> Dict[str, Any]:
    return {
        "re": mp.re(z),
        "im": mp.im(z),
        "abs": abs(z),
        "phase_rad": mp.arg(z),
        "real_sign": "+" if mp.re(z) > 0 else "-" if mp.re(z) < 0 else "0",
        "imag_sign": "+" if mp.im(z) > 0 else "-" if mp.im(z) < 0 else "0",
    }


def d_sum(gamma: mp.mpf, upper: int) -> mp.mpc:
    return sum(mp.power(mp.mpf(m), -mp.mpf("0.5") + 1j * gamma) for m in range(1, upper + 1))


def direct_left_edge_from_model() -> Dict[str, Any]:
    progress("build prolate model for direct left-edge atom")
    model = leakage.build_prolate_model()
    terms = [
        {
            "m": m,
            "t_eval": mp.mpf(m) / LAMBDA_SQ,
            "g04_value": leakage.g04_window(model, mp.mpf(m) / LAMBDA_SQ),
        }
        for m in range(1, LAMBDA_SQ + 1)
    ]
    direct = mp.sqrt(LAMBDA_SQ) ** (-mp.mpf("0.5")) * sum(row["g04_value"] for row in terms)
    return {"direct_E_g04_left_edge": direct, "direct_terms": terms}


def load_zeros() -> List[mp.mpf]:
    data = load_json(ZEROS_5000)
    rows = data.get("zeros", [])
    if len(rows) < 500:
        raise RuntimeError(f"zero cache has only {len(rows)} rows; need at least 500")
    vals = [mp.mpf(str(row["gamma"])) for row in rows]
    for idx, row in enumerate(rows[:500], start=1):
        if int(row["j"]) != idx:
            raise RuntimeError(f"zero cache j mismatch at row {idx}: {row['j']}")
    return vals


def split_components(
    gamma: mp.mpf,
    coeffs: Sequence[mp.mpc],
    lam: mp.mpf,
    g04_lambda_norm: mp.mpf,
    e_left_norm: mp.mpf,
    include_edge_tooth: bool,
) -> Dict[str, Any]:
    upper = M_EDGE if include_edge_tooth else M_EDGE - 1
    full = tail.K_mp(LAMBDA_SQ, N_BOUND, gamma, coeffs)
    d_val = d_sum(gamma, upper)
    comb = (
        g04_lambda_norm
        * mp.power(lam, mp.mpf("0.5") - 1j * gamma)
        * d_val
        / (1j * gamma)
    )
    boundary = e_left_norm * mp.power(lam, 1j * gamma) / (1j * gamma)
    smooth = full - comb - boundary
    return {
        "D_upper": upper,
        "D": d_val,
        "K_full": full,
        "K_comb": comb,
        "B_L": boundary,
        "K_smooth": smooth,
        "smooth_over_comb_abs": abs(smooth) / abs(comb),
        "smooth_subdominant_bound": mp.mpf("0.5"),
        "smooth_subdominant_pass": abs(smooth) <= mp.mpf("0.5") * abs(comb),
    }


def main() -> None:
    started = time.time()
    mp.mp.dps = MP_DPS
    progress("load pinned caches")

    coeff_cache = tail.load_coeff_cache(LAMBDA_SQ, N_BOUND)
    if coeff_cache["_sha256"] != PINNED_COEFF_SHA:
        raise RuntimeError(f"coefficient cache sha mismatch: {coeff_cache['_sha256']}")
    coeffs = tail.load_coeffs_mp(coeff_cache)
    zeros = load_zeros()
    leakage_data = load_json(LEAKAGE_JSON)

    left_edge = direct_left_edge_from_model()
    mp.mp.dps = MP_DPS

    stored_left_edge = mp.mpf(str(leakage_data["F2_left_edge_crosscheck"]["direct_E_g04_left_edge"]))
    direct_left_edge = mp.mpf(left_edge["direct_E_g04_left_edge"])
    direct_vs_stored_abs = abs(direct_left_edge - stored_left_edge)
    direct_vs_stored_rel = direct_vs_stored_abs / max(abs(direct_left_edge), mp.mpf("1e-300"))

    lam = mp.sqrt(LAMBDA_SQ)
    pnorm = mp.mpf(str(coeff_cache["pN_norm_g04"]))
    g04_lambda_raw = mp.mpf(str(coeff_cache["g04_endpoint_t_eq_1"]))
    g04_lambda_norm = g04_lambda_raw / pnorm
    e_left_norm = direct_left_edge / pnorm

    gamma_points = {
        "gamma_1": zeros[0],
        "gamma_62": zeros[61],
        "gamma_500": zeros[499],
        "midpoint_gamma_62_63": (zeros[61] + zeros[62]) / 2,
    }

    progress("evaluate split at four points")
    point_rows: Dict[str, Any] = {}
    for label, gamma in gamma_points.items():
        half = split_components(gamma, coeffs, lam, g04_lambda_norm, e_left_norm, include_edge_tooth=False)
        planted = split_components(gamma, coeffs, lam, g04_lambda_norm, e_left_norm, include_edge_tooth=True)
        jump = planted["K_smooth"] - half["K_smooth"]
        tooth = (
            -g04_lambda_norm
            * mp.power(lam, mp.mpf("0.5") - 1j * gamma)
            * mp.power(mp.mpf(M_EDGE), -mp.mpf("0.5") + 1j * gamma)
            / (1j * gamma)
        )
        point_rows[label] = {
            "gamma": gamma,
            "half_open": {
                "K_full": complex_cell(half["K_full"]),
                "K_comb": complex_cell(half["K_comb"]),
                "B_L": complex_cell(half["B_L"]),
                "K_smooth": complex_cell(half["K_smooth"]),
                "smooth_over_comb_abs": half["smooth_over_comb_abs"],
                "smooth_subdominant_pass": half["smooth_subdominant_pass"],
            },
            "planted_edge_tooth": {
                "K_comb_planted": complex_cell(planted["K_comb"]),
                "K_smooth_planted": complex_cell(planted["K_smooth"]),
                "jump": complex_cell(jump),
                "expected_tooth": complex_cell(tooth),
                "jump_abs_over_expected_abs": abs(jump) / abs(tooth),
                "jump_abs_rel_error": abs(abs(jump) - abs(tooth)) / abs(tooth),
            },
        }

    far_labels = ["gamma_500", "midpoint_gamma_62_63"]
    s1_pass = all(point_rows[label]["half_open"]["smooth_subdominant_pass"] for label in far_labels)

    planted_g500 = point_rows["gamma_500"]["planted_edge_tooth"]
    planted_rel_error = mp.mpf(planted_g500["jump_abs_rel_error"])
    planted_fires = planted_rel_error <= mp.mpf("0.05")

    progress("compute report-only D12 mean for j<=62")
    d12_vals = [d_sum(gamma, M_EDGE - 1) for gamma in zeros[:62]]
    mean_abs_d12_sq = sum(abs(z) ** 2 for z in d12_vals) / len(d12_vals)

    if s1_pass:
        final_code = "SPLIT_IDENTITY_PASS"
    else:
        final_code = "SMOOTH_NOT_SUBDOMINANT"

    codes = [final_code]
    if planted_fires:
        codes.append("K_SPLIT_EDGE_ACCOUNTING_GAP")
    else:
        codes.append("PLANTED_EDGE_JUDGE_MISSED")

    payload = {
        "goal": "SplitIdentityCheck_v1",
        "diagnostic_scope": {
            "NOT_RH": True,
            "phase2_changed": False,
            "q3_mainline_changed": False,
            "qw_or_packet_definition_changed": False,
        },
        "inputs": {
            "goal_file": rel(GOAL_FILE),
            "pen_note": rel(PEN_NOTE),
            "coeff_cache": {
                "path": rel(coeff_cache["_path"]),
                "sha256": coeff_cache["_sha256"],
            },
            "zeros_cache": {
                "path": rel(ZEROS_5000),
                "sha256": sha256_file(ZEROS_5000),
                "count": len(zeros),
            },
            "leakage_json_sanity_source": {
                "path": rel(LEAKAGE_JSON),
                "sha256": sha256_file(LEAKAGE_JSON),
            },
        },
        "parameters": {
            "lambda_sq": LAMBDA_SQ,
            "lambda": lam,
            "N_bound": N_BOUND,
            "mp_dps": MP_DPS,
            "M_edge": M_EDGE,
            "split_convention": "half-open comb m<=12 plus one left boundary atom at m=13 edge",
            "normalization": "Full anchored K uses coefficients normalized by pN_norm_g04; split atoms are divided by the same pN_norm_g04.",
            "pN_norm_g04": pnorm,
            "g04_lambda_raw": g04_lambda_raw,
            "g04_lambda_normalized": g04_lambda_norm,
            "direct_E_g04_left_edge_raw": direct_left_edge,
            "direct_E_g04_left_edge_normalized": e_left_norm,
            "direct_left_edge_vs_leakage_json": {
                "stored": stored_left_edge,
                "abs_diff": direct_vs_stored_abs,
                "rel_diff": direct_vs_stored_rel,
            },
        },
        "S1_split_identity": {
            "registered_bound": "|K_smooth| <= 0.5*|K_comb| at gamma_500 and midpoint",
            "registered_pass": s1_pass,
            "code": None if s1_pass else "SMOOTH_NOT_SUBDOMINANT",
            "points": point_rows,
        },
        "S2_planted_double_count": {
            "registered": "gamma_500 residual jump equals planted m=13 tooth magnitude within 5 percent",
            "registered_pass": planted_fires,
            "branch_code": "K_SPLIT_EDGE_ACCOUNTING_GAP" if planted_fires else "PLANTED_EDGE_JUDGE_MISSED",
            "half_open_double_count_code": None,
            "gamma_500_jump_abs_rel_error": planted_rel_error,
            "gamma_500_jump_abs_over_expected_abs": planted_g500["jump_abs_over_expected_abs"],
        },
        "S3_report_only": {
            "mean_j_le_62_abs_D12_sq": mean_abs_d12_sq,
            "count": 62,
        },
        "codes": codes,
        "elapsed_seconds": time.time() - started,
    }
    write_json(JSON_OUT, payload)
    progress(f"wrote {rel(JSON_OUT)}")


if __name__ == "__main__":
    main()
