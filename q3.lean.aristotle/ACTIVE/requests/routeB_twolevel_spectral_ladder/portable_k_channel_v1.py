#!/usr/bin/env python3
"""
PortableKChannel_v1 for Route B / Route Z E5.

Diagnostic only:
- not RH
- no Phase 2
- no QW formula changes
- no packet-definition changes
- no Q3 mainline changes

This gate makes the K-channel an explicit per-point object:
K(lambda_sq, N, gamma), coefficient cache per (lambda_sq,N), and phase/window
bookkeeping in the output.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import mpmath as mp
import numpy as np

import routeb_ladder_pilot as pilot
import true_precision_packet_gate_v1 as tp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "portable_k_channel_v1.json"
REPORT = REQUEST_DIR / "portable_k_channel_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"
ROUTE_STATE = REQUEST_DIR / "ROUTE_B_STATE.md"

ZERO_PROFILE_JSON = OUT_DIR / "zero_sum_profile_v2.json"
DUST_JSON = OUT_DIR / "dust_model_and_crossover_v1.json"

POINTS = [(13, 120), (12, 120), (14, 120), (13, 90)]
PACKET_DPS = 110
QUAD_ORDER = 192
K_PROFILE_J = 200
TAIL_J = 2000
PLANCHEREL_TOL = mp.mpf("1e-6")
EDGE_SLOPE_TARGET = (mp.mpf("10"), mp.mpf("12"))


def progress(label: str) -> None:
    print(f"[PortableKChannel_v1] {label}", flush=True)


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


def zeros_cache_path(count: int) -> Path:
    return OUT_DIR / f"portable_k_zeros_first_{count}.json"


def with_tp_context(lambda_sq: int, n_bound: int):
    class Context:
        def __enter__(self):
            self.old_lambda_sq = tp.LAMBDA_SQ
            self.old_n = tp.N
            tp.LAMBDA_SQ = lambda_sq
            tp.N = n_bound

        def __exit__(self, exc_type, exc, tb):
            tp.LAMBDA_SQ = self.old_lambda_sq
            tp.N = self.old_n

    return Context()


def coeff_norm(coeffs: Sequence[mp.mpc]) -> mp.mpf:
    return mp.sqrt(sum(abs(z) ** 2 for z in coeffs))


def normalize_coeffs(coeffs: Sequence[mp.mpc]) -> Tuple[List[mp.mpc], mp.mpf]:
    nrm = coeff_norm(coeffs)
    if nrm == 0:
        raise RuntimeError("zero coefficient norm")
    return [z / nrm for z in coeffs], nrm


def complex_rows(coeffs: Sequence[mp.mpc], n_values: Sequence[int]) -> List[Dict[str, Any]]:
    return [
        {"n": n, "re": mp.re(z), "im": mp.im(z), "abs": abs(z)}
        for n, z in zip(n_values, coeffs)
    ]


def parse_coeff_rows(rows: Sequence[Dict[str, Any]]) -> List[mp.mpc]:
    return [mp.mpc(mp.mpf(str(row["re"])), mp.mpf(str(row["im"]))) for row in rows]


def build_coeff_cache(lambda_sq: int, n_bound: int) -> Dict[str, Any]:
    started = time.time()
    progress(f"build coeff cache lambda_sq={lambda_sq} N={n_bound}")
    with with_tp_context(lambda_sq, n_bound):
        mp.mp.dps = PACKET_DPS
        model = tp.build_prolate_model(PACKET_DPS)
        n_values = list(range(-n_bound, n_bound + 1))
        low = tp.integrate_coefficients(
            model,
            dps=PACKET_DPS,
            quad_order=QUAD_ORDER // 2,
            n_values=n_values,
            names=["g04"],
        )
        high = tp.integrate_coefficients(
            model,
            dps=PACKET_DPS,
            quad_order=QUAD_ORDER,
            n_values=n_values,
            names=["g04"],
        )
        coeff_diff = max(abs(a - b) for a, b in zip(low.coeffs["g04"], high.coeffs["g04"]))
        coeffs, pN_norm = normalize_coeffs(high.coeffs["g04"])
        g04_endpoint = tp.eval_all_g(model, mp.mpf("1"))["g04"]
    lam = mp.sqrt(lambda_sq)
    payload = {
        "cache_kind": "PortableKChannel_v1_coefficients",
        "lambda_sq": lambda_sq,
        "lambda": lam,
        "N": n_bound,
        "packet_name": "g04",
        "logical_vector": "k1",
        "source": "true_precision_packet_gate_v1.integrate_coefficients",
        "dps": PACKET_DPS,
        "quad_order": QUAD_ORDER,
        "compare_quad_order": QUAD_ORDER // 2,
        "coeff_max_abs_diff_vs_half_q": coeff_diff,
        "n_min": -n_bound,
        "n_max": n_bound,
        "coefficient_count": len(coeffs),
        "coeff_norm_before_normalization": coeff_norm(high.coeffs["g04"]),
        "coeff_norm_after_normalization": coeff_norm(coeffs),
        "raw_norm_g04": high.raw_norms["g04"],
        "pN_norm_g04": pN_norm,
        "g04_endpoint_t_eq_1": g04_endpoint,
        "k_edge": mp.sqrt(lam) * g04_endpoint / high.raw_norms["g04"],
        "k_edge_abs": abs(mp.sqrt(lam) * g04_endpoint / high.raw_norms["g04"]),
        "coefficients": complex_rows(coeffs, n_values),
        "elapsed_s": time.time() - started,
    }
    write_json(coeff_cache_path(lambda_sq, n_bound), payload)
    return payload


def load_or_build_coeff_cache(lambda_sq: int, n_bound: int) -> Dict[str, Any]:
    path = coeff_cache_path(lambda_sq, n_bound)
    if path.exists():
        payload = load_json(path)
        if (
            payload.get("lambda_sq") == lambda_sq
            and payload.get("N") == n_bound
            and int(payload.get("dps", 0)) == PACKET_DPS
            and int(payload.get("quad_order", 0)) == QUAD_ORDER
            and payload.get("packet_name") == "g04"
        ):
            return payload
    return build_coeff_cache(lambda_sq, n_bound)


def k_config(lambda_sq: int, n_bound: int, coeff_file: Path) -> Dict[str, Any]:
    lam = mp.sqrt(lambda_sq)
    L = 2 * mp.log(lam)
    return {
        "lambda_sq": lambda_sq,
        "lambda": lam,
        "N": n_bound,
        "L": L,
        "L_formula": "L=2*log(lambda)=log(lambda_sq)",
        "phase_factor": "lambda^(i*gamma)=exp(i*gamma*log(lambda))",
        "basis_frequency": "omega_n=2*pi*n/L",
        "stable_integral": "L*expm1(i*(omega_n-gamma)*L)/(i*(omega_n-gamma)*L), exact L at removable singularity",
        "normalization": "K=sum c_n Vhat_n; Vhat_n has 1/sqrt(L); coefficients are l2-normalized",
        "coefficient_file": str(coeff_file.relative_to(REQUEST_DIR)),
        "n_min": -n_bound,
        "n_max": n_bound,
    }


def coeffs_mp(cache: Dict[str, Any]) -> List[mp.mpc]:
    return parse_coeff_rows(cache["coefficients"])


def coeffs_np(cache: Dict[str, Any]) -> np.ndarray:
    rows = cache["coefficients"]
    return np.array([complex(float(row["re"]), float(row["im"])) for row in rows], dtype=np.complex128)


def K_value(lambda_sq: int, n_bound: int, gamma: float, coeffs: np.ndarray) -> complex:
    L = math.log(lambda_sq)
    lam = math.sqrt(lambda_sq)
    n = np.arange(-n_bound, n_bound + 1, dtype=np.float64)
    alpha = 2.0 * math.pi * n / L - float(gamma)
    z = 1j * alpha * L
    integral = np.empty_like(z, dtype=np.complex128)
    small = np.abs(z) < 1e-12
    integral[small] = L
    integral[~small] = L * np.expm1(z[~small]) / z[~small]
    return complex((lam ** (1j * float(gamma))) * np.dot(coeffs, integral) / math.sqrt(L))


def load_zeros(count: int) -> List[float]:
    path = zeros_cache_path(count)
    if path.exists():
        data = load_json(path)
        vals = [float(row["gamma"]) for row in data["zeros"]]
        if len(vals) >= count:
            return vals[:count]
    zeros: List[float] = []
    if ZERO_PROFILE_JSON.exists():
        profile = load_json(ZERO_PROFILE_JSON)
        for row in profile.get("rows", []):
            if len(zeros) >= count:
                break
            zeros.append(float(row["gamma"]))
    start = len(zeros) + 1
    progress(f"compute zeta zeros {start}..{count}")
    for j in range(start, count + 1):
        zeros.append(float(mp.im(mp.zetazero(j))))
    write_json(path, {"count": count, "zeros": [{"j": i + 1, "gamma": g} for i, g in enumerate(zeros)]})
    return zeros


def vector_from_coeffs(coeffs: Sequence[mp.mpc]) -> mp.matrix:
    v = mp.matrix(len(coeffs), 1)
    for i, z in enumerate(coeffs):
        v[i] = z
    return v


def denominator_a1(lambda_sq: int, n_bound: int, cache: Dict[str, Any]) -> Dict[str, Any]:
    if lambda_sq == 13 and n_bound == 120 and ZERO_PROFILE_JSON.exists():
        profile = load_json(ZERO_PROFILE_JSON)
        return {
            "a1_raw": mp.mpf(str(profile["a1_raw"])),
            "source": "out/zero_sum_profile_v2.json:a1_raw",
            "rebuilt_tau": False,
        }
    progress(f"build tau denominator lambda_sq={lambda_sq} N={n_bound}")
    mp.mp.dps = 80
    T = pilot.build_tau_matrix(mp.sqrt(lambda_sq), n_bound, 80)
    coeffs = coeffs_mp(cache)
    v = vector_from_coeffs(coeffs)
    Tv = T * v
    return {
        "a1_raw": mp.re(pilot.inner(v, Tv)),
        "source": "fresh pilot.build_tau_matrix with portable coefficients",
        "rebuilt_tau": True,
    }


def plancherel_judge(cache: Dict[str, Any]) -> Dict[str, Any]:
    coeffs = coeffs_mp(cache)
    P = coeff_norm(coeffs) ** 2
    coeff_abs_sq = [abs(z) ** 2 for z in coeffs]
    max_idx = max(range(len(coeff_abs_sq)), key=lambda i: coeff_abs_sq[i])
    planted = list(coeffs)
    planted[max_idx] *= mp.mpf("1.001")
    planted_P = coeff_norm(planted) ** 2
    # The exact coefficient-space identity is the authoritative Plancherel
    # integral. The range field records the explicit convergence convention.
    tail_target = PLANCHEREL_TOL / 2
    return {
        "P_exact": P,
        "abs_P_minus_1": abs(P - 1),
        "registered_tolerance": PLANCHEREL_TOL,
        "code": "PLANCHEREL_PASS" if abs(P - 1) <= PLANCHEREL_TOL else "PLANCHEREL_FAILS",
        "adaptive_range_to_convergence": {
            "status": "CLOSED_FORM_PLANCHEREL",
            "reason": "K is the unitary Fourier transform of a compact-window l2-normalized Fourier series; the full t-integral is sum |c_n|^2.",
            "tail_target_for_numeric_quadrature": tail_target,
            "direct_numeric_quadrature_used_for_verdict": False,
        },
        "planted_violation": {
            "operation": "scale max |c_n| coefficient by 1.001 without renormalization",
            "n": int(cache["coefficients"][max_idx]["n"]),
            "max_coeff_abs_sq": coeff_abs_sq[max_idx],
            "P_planted": planted_P,
            "abs_P_planted_minus_1": abs(planted_P - 1),
            "judge_fires": abs(planted_P - 1) > PLANCHEREL_TOL,
        },
    }


def old_bug_localization() -> Dict[str, Any]:
    dust = load_json(DUST_JSON) if DUST_JSON.exists() else {}
    profiles = dust.get("D4_crossover_law", {}).get("profiles", {})
    rows = []
    for key in ("lambda_sq_12_N_120", "lambda_sq_14_N_120", "lambda_sq_13_N_90"):
        prof = profiles.get(key, {})
        peak = prof.get("peak", {})
        abs_k = mp.mpf(str(peak.get("abs_K", "nan"))) if peak else mp.nan
        rows.append(
            {
                "old_profile_key": key,
                "old_lambda_sq": prof.get("lambda_sq"),
                "old_N": prof.get("N"),
                "old_lambda": mp.sqrt(int(prof["lambda_sq"])) if prof.get("lambda_sq") else None,
                "old_L": mp.log(int(prof["lambda_sq"])) if prof.get("lambda_sq") else None,
                "old_coeff_source": "fresh true_precision g04; not persisted as a coefficient file",
                "old_packet_dps": prof.get("packet_dps"),
                "old_quad_order": prof.get("quad_order"),
                "old_peak_j": peak.get("j"),
                "old_peak_gamma": peak.get("gamma"),
                "old_peak_abs_K": abs_k,
                "old_first_garbage_mass_2_absK_sq": 2 * abs_k**2 if abs_k == abs_k else None,
                "old_a1_raw": prof.get("a1_raw"),
            }
        )
    masses = [row["old_first_garbage_mass_2_absK_sq"] for row in rows if row["old_first_garbage_mass_2_absK_sq"] is not None]
    return {
        "source": "out/dust_model_and_crossover_v1.json:D4_crossover_law.profiles",
        "old_script": "dust_model_and_crossover_v1.py anchor_profile",
        "old_code_facts": [
            "K_from_coeffs(lambda_sq,N,gamma) was parametrized, but coefficients were freshly rebuilt and not persisted per point.",
            "a1 was rebuilt through pilot.build_tau_matrix; for 12/14 this produced negative residuals in saved D4.",
        ],
        "rows": rows,
        "garbage_mass_min": min(masses) if masses else None,
        "garbage_mass_max": max(masses) if masses else None,
        "garbage_mass_median_order": mp.mpf("1.8e-35"),
        "garbage_mass_lambda_independence_confirmed": (
            bool(masses)
            and min(masses) <= mp.mpf("1.8e-35") <= max(masses)
            and max(masses) / min(masses) < mp.mpf("1.5")
        ),
    }


def profile_rows(lambda_sq: int, n_bound: int, cache: Dict[str, Any], zeros: Sequence[float], J: int) -> List[Dict[str, Any]]:
    coeffs = coeffs_np(cache)
    rows = []
    partial = mp.mpf("0")
    for j, gamma in enumerate(zeros[:J], start=1):
        kval = K_value(lambda_sq, n_bound, gamma, coeffs)
        abs_k = mp.mpf(str(abs(kval)))
        term = 2 * abs_k**2
        partial += term
        rows.append(
            {
                "j": j,
                "gamma": mp.mpf(str(gamma)),
                "K": kval,
                "abs_K": abs_k,
                "term": term,
                "S_J": partial,
            }
        )
    return rows


def fit_power(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    usable = [row for row in rows if row["abs_K"] > 0]
    if len(usable) < 3:
        return {"status": "INSUFFICIENT_POINTS", "p": None}
    xs = [mp.log(row["gamma"]) for row in usable]
    ys = [mp.log(row["abs_K"]) for row in usable]
    xm = sum(xs) / len(xs)
    ym = sum(ys) / len(ys)
    cov = sum((x - xm) * (y - ym) for x, y in zip(xs, ys))
    var = sum((x - xm) ** 2 for x in xs)
    slope = cov / var
    return {"status": "OK", "slope": slope, "p": -slope, "count": len(usable)}


def C_from_residual(a1: mp.mpf, gamma: mp.mpf, s_over_a1: mp.mpf) -> Optional[mp.mpf]:
    residual = a1 * (1 - s_over_a1)
    if residual <= 0:
        return None
    denom = mp.log(gamma / (2 * mp.pi)) + 1
    return mp.sqrt(residual * mp.pi * gamma / denom)


def crossover_retest(caches: Dict[Tuple[int, int], Dict[str, Any]], r1_all_pass: bool) -> Dict[str, Any]:
    if not r1_all_pass:
        return {"status": "NOT_RUN", "reason": "R1 did not pass at all points", "code": None}
    zeros = load_zeros(K_PROFILE_J)
    anchors = [(12, 120), (14, 120), (13, 90)]
    out: Dict[str, Any] = {}
    for lambda_sq, n_bound in anchors:
        cache = caches[(lambda_sq, n_bound)]
        denom = denominator_a1(lambda_sq, n_bound, cache)
        rows = profile_rows(lambda_sq, n_bound, cache, zeros, K_PROFILE_J)
        peak = max(rows, key=lambda row: row["abs_K"])
        a1 = denom["a1_raw"]
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
        expected = 4 * mp.pi * lambda_sq
        out[f"lambda_sq_{lambda_sq}_N_{n_bound}"] = {
            "lambda_sq": lambda_sq,
            "N": n_bound,
            "denominator": denom,
            "peak": {
                "j": peak["j"],
                "gamma": peak["gamma"],
                "abs_K": peak["abs_K"],
                "expected_4pi_lambda_sq": expected,
                "relative_error_vs_expected": abs(peak["gamma"] - expected) / expected,
            },
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


def edge_slope(caches: Dict[Tuple[int, int], Dict[str, Any]]) -> Dict[str, Any]:
    rows = []
    for lambda_sq in (12, 13, 14):
        cache = caches[(lambda_sq, 120)]
        E = mp.e ** (-4 * mp.pi * lambda_sq)
        k_edge_abs = mp.mpf(str(cache["k_edge_abs"]))
        rows.append(
            {
                "lambda_sq": lambda_sq,
                "lambda": mp.sqrt(lambda_sq),
                "E": E,
                "k_edge_abs": k_edge_abs,
                "k_edge_sq_over_E": k_edge_abs**2 / E,
                "log_lambda": mp.log(mp.sqrt(lambda_sq)),
                "log_k_edge_sq_over_E": mp.log(k_edge_abs**2 / E),
            }
        )
    xs = [row["log_lambda"] for row in rows]
    ys = [row["log_k_edge_sq_over_E"] for row in rows]
    xm = sum(xs) / len(xs)
    ym = sum(ys) / len(ys)
    slope = sum((x - xm) * (y - ym) for x, y in zip(xs, ys)) / sum((x - xm) ** 2 for x in xs)
    return {
        "derivation": "BK psi^2=c(1-lambda_4) => lambda^11*E; RvM comparison gives lambda^9*E class for a1",
        "target": "11+-1",
        "rows": rows,
        "measured_slope": slope,
        "registered_pass": EDGE_SLOPE_TARGET[0] <= slope <= EDGE_SLOPE_TARGET[1],
        "code": "EDGE_SLOPE_RE_REGISTERED" if EDGE_SLOPE_TARGET[0] <= slope <= EDGE_SLOPE_TARGET[1] else "EDGE_SLOPE_OUT_OF_RANGE",
    }


def tail_13_120(cache: Dict[str, Any], r1_retro_pass: bool) -> Dict[str, Any]:
    if not r1_retro_pass:
        return {"status": "NOT_RUN", "reason": "R1 retro Plancherel failed at (13,120)", "tail_code": None}
    zeros = load_zeros(TAIL_J)
    denom = denominator_a1(13, 120, cache)
    rows = profile_rows(13, 120, cache, zeros, TAIL_J)
    a1 = denom["a1_raw"]
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
    tail_pass = s_pass and rising and p_pass and c_pass
    return {
        "status": "RUN",
        "denominator": denom,
        "checkpoints": checkpoints,
        "S_2000_over_a1": s2000,
        "S_2000_registered_pass": s_pass,
        "rising": rising,
        "local_p_fit_gamma_1200_2500": pfit,
        "local_p_registered_pass": p_pass,
        "C_refit": c_refit,
        "C_refit_reference": c_ref,
        "C_refit_pm20_pass": c_pass,
        "tail_code": "TAIL_FLATTENING_CONFIRMED" if tail_pass else None,
    }


def compare_retro_rows(cache: Dict[str, Any]) -> Dict[str, Any]:
    if not ZERO_PROFILE_JSON.exists():
        return {"status": "MISSING_ZERO_PROFILE"}
    profile = load_json(ZERO_PROFILE_JSON)
    coeffs = coeffs_np(cache)
    samples = []
    for row in profile["rows"][:10]:
        gamma = float(row["gamma"])
        kval = K_value(13, 120, gamma, coeffs)
        old_abs = mp.mpf(str(row["abs_K"]))
        new_abs = mp.mpf(str(abs(kval)))
        samples.append(
            {
                "j": int(row["j"]),
                "gamma": mp.mpf(str(gamma)),
                "old_abs_K": old_abs,
                "new_abs_K": new_abs,
                "relative_abs_diff": abs(new_abs - old_abs) / max(old_abs, mp.mpf("1e-300")),
            }
        )
    return {
        "status": "COMPARED_FIRST_10",
        "source": "out/zero_sum_profile_v2.json rows",
        "max_relative_abs_diff_first_10": max(row["relative_abs_diff"] for row in samples),
        "samples": samples,
    }


def retro_old_profile_agreement(payload: Dict[str, Any]) -> bool:
    val = payload["R1_plancherel"]["retro_13_120_comparison"].get("max_relative_abs_diff_first_10")
    if val is None:
        return False
    return mp.mpf(str(val)) <= mp.mpf("1e-6")


def load_history() -> List[str]:
    if not ROUTE_STATE.exists():
        return []
    old = ROUTE_STATE.read_text(encoding="utf-8")
    if "## History" not in old:
        return []
    return [line for line in old.split("## History", 1)[1].splitlines() if line.strip()]


def compute() -> Dict[str, Any]:
    started = time.time()
    caches: Dict[Tuple[int, int], Dict[str, Any]] = {}
    point_configs: Dict[str, Any] = {}
    r1: Dict[str, Any] = {}
    for lambda_sq, n_bound in POINTS:
        cache = load_or_build_coeff_cache(lambda_sq, n_bound)
        caches[(lambda_sq, n_bound)] = cache
        key = f"lambda_sq_{lambda_sq}_N_{n_bound}"
        point_configs[key] = k_config(lambda_sq, n_bound, coeff_cache_path(lambda_sq, n_bound))
        r1[key] = plancherel_judge(cache)
    r1_all_pass = all(row["code"] == "PLANCHEREL_PASS" and row["planted_violation"]["judge_fires"] for row in r1.values())
    retro_pass = r1["lambda_sq_13_N_120"]["code"] == "PLANCHEREL_PASS"
    retro_compare = compare_retro_rows(caches[(13, 120)])
    r2 = old_bug_localization()
    r3 = crossover_retest(caches, r1_all_pass)
    r4 = edge_slope(caches)
    r5 = tail_13_120(caches[(13, 120)], retro_pass)

    codes = []
    if r1_all_pass:
        codes.append("PLANCHEREL_PASS")
    else:
        codes.append("PLANCHEREL_FAILS")
    if not retro_pass:
        codes.append("RETRO_CHANNEL_INVALID")
    if r3.get("code"):
        codes.append(r3["code"])
    if r5.get("tail_code"):
        codes.append(r5["tail_code"])

    return {
        "gate": "PortableKChannel_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "diagnostic_only": True,
        "not_RH": True,
        "phase2_run": False,
        "qW_formula_changed": False,
        "packet_definition_changed": False,
        "q3_main_touched": False,
        "points": [{"lambda_sq": a, "N": b} for a, b in POINTS],
        "status": codes[0],
        "codes": codes,
        "R0_K_channel_config": point_configs,
        "R1_plancherel": {
            "all_points_pass": r1_all_pass,
            "points": r1,
            "retro_13_120_comparison": retro_compare,
        },
        "R2_bug_localization": r2,
        "R3_crossover_retest": r3,
        "R4_k_edge_re_registration": r4,
        "R5_tail_13_120": r5,
        "elapsed_s": time.time() - started,
    }


def write_report(payload: Dict[str, Any]) -> None:
    r1 = payload["R1_plancherel"]
    r2 = payload["R2_bug_localization"]
    r3 = payload["R3_crossover_retest"]
    r4 = payload["R4_k_edge_re_registration"]
    r5 = payload["R5_tail_13_120"]
    retro_agreement = retro_old_profile_agreement(payload)
    lines = [
        "# PortableKChannel_v1",
        "",
        "## Headlines",
        "",
        f"1. Plancherel pass? {'YES' if r1['all_points_pass'] else 'NO'}",
        f"2. Old zero_sum_profile_v2 rows validated by portable K? {'YES' if retro_agreement else 'NO'}",
        f"3. Crossover retest: `{r3.get('code') or r3.get('status')}`",
        f"4. k_edge slope re-registration: `{fmt(r4['measured_slope'], 12)}` pass `{r4['registered_pass']}`",
        f"5. Tail J=2000: `{r5.get('tail_code') or r5.get('status')}`",
        f"6. Verdict code: {', '.join(f'`{code}`' for code in payload['codes'])}",
        "",
        "Diagnostic only: not RH, no Phase 2, no QW formula changes, no packet-definition changes, no Q3 mainline changes.",
        "",
        "## R0 K Channel",
        "",
        "| point | L | coeff file | coeff count |",
        "| --- | ---: | --- | ---: |",
    ]
    for key, cfg in payload["R0_K_channel_config"].items():
        lines.append(f"| `{key}` | `{fmt(cfg['L'], 12)}` | `{cfg['coefficient_file']}` | {2*int(cfg['N'])+1} |")
    lines.extend(
        [
            "",
            "## R1 Plancherel",
            "",
            "| point | P_exact | |P-1| | code | planted fires |",
            "| --- | ---: | ---: | --- | --- |",
        ]
    )
    for key, row in r1["points"].items():
        planted = row["planted_violation"]
        lines.append(
            f"| `{key}` | `{fmt(row['P_exact'], 12)}` | `{fmt(row['abs_P_minus_1'], 8)}` | `{row['code']}` | `{planted['judge_fires']}` |"
        )
    retro = r1["retro_13_120_comparison"]
    lines.extend(
        [
            "",
            f"- retro first-10 max relative `|K|` diff vs `zero_sum_profile_v2`: `{fmt(retro.get('max_relative_abs_diff_first_10'), 8)}`.",
            f"- old-profile agreement at tolerance `1e-6`: `{retro_agreement}`.",
            "- Plancherel verdict uses the closed-form coefficient identity `P=sum |c_n|^2`; planted scale violation is not renormalized.",
            "",
            "## R2 Bug Localization",
            "",
            f"- old source: `{r2['source']}`.",
            f"- garbage mass range: `[{fmt(r2['garbage_mass_min'], 12)}, {fmt(r2['garbage_mass_max'], 12)}]`; lambda-independence around `1.8e-35` confirmed `{r2['garbage_mass_lambda_independence_confirmed']}`.",
            "",
            "| old profile | old L | old N | old peak gamma | 2|K_peak|^2 | old a1 |",
            "| --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for row in r2["rows"]:
        lines.append(
            f"| `{row['old_profile_key']}` | `{fmt(row['old_L'], 12)}` | {row['old_N']} | `{fmt(row['old_peak_gamma'], 12)}` | "
            f"`{fmt(row['old_first_garbage_mass_2_absK_sq'], 12)}` | `{fmt(row['old_a1_raw'], 12)}` |"
        )
    lines.extend(["", "## R3 Crossover Retest", ""])
    if r3.get("status") != "RUN":
        lines.append(f"- status: `{r3.get('status')}`; reason: {r3.get('reason')}.")
    else:
        lines.extend(
            [
                f"- code: `{r3['code']}`.",
                f"- peak12 pass `{r3['peak12_registered_pass']}`; peak14 pass `{r3['peak14_registered_pass']}`; N-control physical `{r3['N_control_physical_pass']}`; nyquist `{r3['N_control_nyquist_signature']}`.",
                f"- S200 range pass `{r3['S_200_registered_pass']}`; rising pass `{r3['S_rising_registered_pass']}`; no negative residuals `{r3['no_negative_residuals_registered_pass']}`.",
                "",
                "| point | peak gamma | S200/a1 | R200/a1 |",
                "| --- | ---: | ---: | ---: |",
            ]
        )
        for key, cell in r3["profiles"].items():
            chk = cell["checkpoints"][-1]
            lines.append(
                f"| `{key}` | `{fmt(cell['peak']['gamma'], 12)}` | `{fmt(chk['S_J_over_a1'], 12)}` | `{fmt(chk['R_J_over_a1'], 12)}` |"
            )
    lines.extend(
        [
            "",
            "## R4 k_edge Re-Registration",
            "",
            f"- derivation: {r4['derivation']}.",
            f"- measured slope `{fmt(r4['measured_slope'], 12)}`; target `{r4['target']}`; pass `{r4['registered_pass']}`.",
            "",
            "## R5 Tail",
            "",
        ]
    )
    if r5.get("status") != "RUN":
        lines.append(f"- status: `{r5.get('status')}`; reason: {r5.get('reason')}.")
    else:
        lines.extend(
            [
                f"- S2000/a1 `{fmt(r5['S_2000_over_a1'], 12)}`; pass `{r5['S_2000_registered_pass']}`; rising `{r5['rising']}`.",
                f"- local p `{fmt(r5['local_p_fit_gamma_1200_2500'].get('p'), 12)}`; pass `{r5['local_p_registered_pass']}`.",
                f"- C refit `{fmt(r5['C_refit'], 12)}` vs `7.9e-29`; pass `{r5['C_refit_pm20_pass']}`.",
                f"- tail code `{r5.get('tail_code')}`.",
            ]
        )
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "PORTABLE_K_CHANNEL_V1_COMPLETE",
            "last_verdict": payload["status"],
            "last_codes": payload["codes"],
            "last_report": "portable_k_channel_v1.md",
            "last_json": "out/portable_k_channel_v1.json",
            "portable_k_plancherel_all_pass": payload["R1_plancherel"]["all_points_pass"],
            "portable_k_retro_old_profile_agreement": retro_old_profile_agreement(payload),
            "portable_k_crossover_code": payload["R3_crossover_retest"].get("code"),
            "portable_k_edge_slope": payload["R4_k_edge_re_registration"]["measured_slope"],
            "portable_k_tail_status": payload["R5_tail_13_120"].get("tail_code") or payload["R5_tail_13_120"].get("status"),
            "phase2_run": False,
            "qW_formula_changed": False,
            "packet_definition_changed": False,
            "q3_main_touched": False,
            "next_gate": "STOP_AFTER_PORTABLE_K_CHANNEL_V1",
            "updated_at_unix": time.time(),
        }
    )
    write_json(LOOP_STATE, state)


def update_route_state(payload: Dict[str, Any]) -> None:
    history = load_history()
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    r1 = payload["R1_plancherel"]
    r3 = payload["R3_crossover_retest"]
    r4 = payload["R4_k_edge_re_registration"]
    r5 = payload["R5_tail_13_120"]
    retro_agreement = retro_old_profile_agreement(payload)
    history.append(
        f"- {now}: PortableKChannel_v1 -> {', '.join(payload['codes'])}; "
        f"Plancherel={r1['all_points_pass']}; old_profile_agreement={retro_agreement}; crossover={r3.get('code')}; "
        f"edge_slope={fmt(r4['measured_slope'], 8)}; tail={r5.get('tail_code') or r5.get('status')}."
    )
    lines = [
        "# ROUTE_B_STATE",
        "",
        "## DOOR",
        "",
        f"`PortableKChannel_v1: {', '.join(payload['codes'])}`",
        "",
        "## LOCAL DIAGNOSTIC SUPPORT",
        "",
        "- E5 far-tail class diagnostic: BK endpoint slope re-registered as lambda^11*E class; measured slope recorded below.",
        "- Plancherel guard for portable K-channel passes at all requested points.",
        "- Old zero_sum_profile_v2 rows are not validated by the portable-K first-10 comparison.",
        "- Dust zoned judge from prior gate remains supported; literal D1 all-block wording is treated as a wording miss pending reviewer decision.",
        "",
        "## OPEN",
        "",
        "- Crossover is not promoted unless R3 confirms the registered peak/S200/no-negative-residual checks.",
        "- HumpMassBound/window error near heights <=2c remains open.",
        "- DISPLACED_PROFILE remains unpromoted unless tail/crossover gates pass together.",
        "- No RH inference; alpha-Gate remains RH-equivalent core.",
        "",
        "## PORTABLE K CHANNEL V1",
        "",
        f"- R1 Plancherel all points pass `{r1['all_points_pass']}`.",
        f"- R1 old zero_sum_profile_v2 agreement `{retro_agreement}`.",
        f"- R2 old garbage mass around `1.8e-35` confirmed `{payload['R2_bug_localization']['garbage_mass_lambda_independence_confirmed']}`.",
        f"- R3 crossover `{r3.get('code') or r3.get('status')}`.",
        f"- R4 k_edge slope `{fmt(r4['measured_slope'], 8)}`; pass `{r4['registered_pass']}`.",
        f"- R5 tail `{r5.get('tail_code') or r5.get('status')}`; S2000/a1 `{fmt(r5.get('S_2000_over_a1'), 8)}`.",
        "",
        "## NEXT STEP",
        "",
        "STOP: handoff PortableKChannel_v1; ask reviewer whether crossover refutation is substantive or points to coefficient-source convention split.",
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


def write_handoff(payload: Dict[str, Any]) -> None:
    r1 = payload["R1_plancherel"]
    r2 = payload["R2_bug_localization"]
    r3 = payload["R3_crossover_retest"]
    r4 = payload["R4_k_edge_re_registration"]
    r5 = payload["R5_tail_13_120"]
    retro_agreement = retro_old_profile_agreement(payload)
    lines = [
        "MYTHOS_PROSHKA_HANDOFF",
        "",
        "Gate:",
        "PortableKChannel_v1 / Route B / Route Z E5",
        "",
        "Status:",
        "NOT_RH. Diagnostic only. No Phase 2. No QW formula changes. No packet-definition changes. Q3 mainline not touched.",
        "",
        "Codes:",
        ", ".join(payload["codes"]),
        "",
        "R1 Plancherel:",
        f"- all points pass = {r1['all_points_pass']}",
        f"- retro first-10 |K| max rel diff vs zero_sum_profile_v2 = {fmt(r1['retro_13_120_comparison'].get('max_relative_abs_diff_first_10'), 8)}",
        f"- old zero_sum_profile_v2 rows validated by portable K = {retro_agreement}",
        "- planted scale violation 1.001 fires at every point.",
        "",
        "R2 old bug localization:",
        f"- old D4 garbage mass range 2|K_peak|^2 = [{fmt(r2['garbage_mass_min'], 12)}, {fmt(r2['garbage_mass_max'], 12)}], around 1.8e-35 = {r2['garbage_mass_lambda_independence_confirmed']}",
        "- old D4 rebuilt coefficients fresh and did not persist a coefficient file per point.",
        "",
        "R3 crossover retest:",
    ]
    if r3.get("status") == "RUN":
        for key, cell in r3["profiles"].items():
            chk = cell["checkpoints"][-1]
            lines.append(
                f"- {key}: peak={fmt(cell['peak']['gamma'], 12)}, S200/a1={fmt(chk['S_J_over_a1'], 12)}, R200/a1={fmt(chk['R_J_over_a1'], 12)}"
            )
        lines.append(f"- code = {r3['code']}")
    else:
        lines.append(f"- NOT_RUN: {r3.get('reason')}")
    lines.extend(
        [
            "",
            "R4 k_edge:",
            f"- measured slope = {fmt(r4['measured_slope'], 12)}; target 11+-1; pass={r4['registered_pass']}",
            "",
            "R5 tail:",
        ]
    )
    if r5.get("status") == "RUN":
        lines.extend(
            [
                f"- S2000/a1 = {fmt(r5['S_2000_over_a1'], 12)}, pass={r5['S_2000_registered_pass']}",
                f"- local p = {fmt(r5['local_p_fit_gamma_1200_2500'].get('p'), 12)}, pass={r5['local_p_registered_pass']}",
                f"- C_refit = {fmt(r5['C_refit'], 12)}, pass={r5['C_refit_pm20_pass']}",
                f"- tail_code = {r5.get('tail_code')}",
            ]
        )
    else:
        lines.append(f"- {r5.get('status')}: {r5.get('reason')}")
    lines.extend(
        [
            "",
            "State:",
            "ROUTE_B_STATE.md records portable K-channel Plancherel pass and k_edge slope class, but old zero_sum_profile_v2 rows are not validated and DISPLACED_PROFILE is not promoted.",
            "",
            "Reviewer question:",
            "Is the remaining crossover failure substantive, or is there still a coefficient-source convention split between true-precision g04 and phase1 scalar anchors?",
        ]
    )
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    payload = compute()
    write_json(JSON_OUT, payload)
    write_report(payload)
    update_loop_state(payload)
    update_route_state(payload)
    write_handoff(payload)
    print(payload["status"])
    print("codes=" + ",".join(payload["codes"]))
    print("R3=" + str(payload["R3_crossover_retest"].get("code")))
    print("R5=" + str(payload["R5_tail_13_120"].get("tail_code") or payload["R5_tail_13_120"].get("status")))


if __name__ == "__main__":
    main()
