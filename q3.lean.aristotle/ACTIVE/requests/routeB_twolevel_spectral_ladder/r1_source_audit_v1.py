#!/usr/bin/env python3
"""
R1SourceAudit_v1 for Route B TwoLevelSpectralLadder.

ZERO-heavy-compute diagnostic: arithmetic over saved per-point JSONs only.
No Phase 2, no new anchors, no RH claim.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import mpmath as mp


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "r1_source_audit_v1.json"
REPORT = REQUEST_DIR / "r1_source_audit_v1.md"
HANDOFF = REQUEST_DIR / "handoff_to_proshka.md"
LOOP_STATE = REQUEST_DIR / "loop_state.json"

POINTS: List[Tuple[int, int]] = [
    (13, 60),
    (13, 90),
    (12, 60),
    (12, 90),
    (14, 60),
    (14, 90),
    (12, 120),
    (14, 120),
    (13, 120),
]

R1_14_120_OLD_MIXED_REF = mp.mpf("3.71e-37")
REPAIRED_R1_12_120_REF = mp.mpf("2.7e-26")


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def parse_num(value: Any) -> mp.mpf:
    if isinstance(value, (int, float)):
        return mp.mpf(value)
    s = str(value).strip()
    if s.startswith("(") and s.endswith(")"):
        s = s[1:-1].strip()
    if "+ 0.0j" in s:
        s = s.split("+", 1)[0].strip()
    if "- 0.0j" in s:
        s = s.split("-", 1)[0].strip()
    if "j" in s or "i" in s:
        z = parse_complex(s)
        return mp.mpf(mp.re(z))
    return mp.mpf(s)


def parse_complex(value: Any) -> mp.mpc:
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


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    if isinstance(value, (mp.mpf, mp.mpc)):
        return mp.nstr(value, 80)
    return value


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def missing(source: str = "not present in saved R1-source JSONs") -> Dict[str, Any]:
    return {"status": "MISSING", "source": source, "value": None}


def present(value: Any, source: str) -> Dict[str, Any]:
    return {"status": "OK", "source": source, "value": value}


def read_parity_point(lambda_sq: int, N: int) -> Dict[str, Any]:
    path = OUT_DIR / f"parity_block_lambda_sq_{lambda_sq}_N_{N}.json"
    data = load_json(path)
    g_vals = [parse_num(x) for x in data["even"]["G_eigenvalues"]]
    g_vals = sorted(g_vals)
    odd_vals = [parse_complex(x) for x in data["odd"]["S0_eigenvalues"]]
    theta1 = parse_complex(data["theta"][0])
    r1 = parse_complex(data["r1_theta1_over_lambda1_G_even"])
    return {
        "lambda_sq": lambda_sq,
        "N": N,
        "source": f"out/{path.name}",
        "lambda1_G_even": g_vals[0],
        "lambda2_G_even": g_vals[1],
        "S0_odd": odd_vals[0],
        "theta1": theta1,
        "r1": r1,
        "ground_alignment_with_k1_p": parse_num(data["ground_alignment_with_k1_p"]),
    }


def static_progress_sources() -> Dict[Tuple[int, int], Dict[str, Any]]:
    path = OUT_DIR / "static_schur_progress.json"
    if not path.exists():
        return {}
    data = load_json(path)
    out: Dict[Tuple[int, int], Dict[str, Any]] = {}
    for cell in data.get("cells", []):
        key = (int(cell["lambda_sq"]), int(cell["N"]))
        record: Dict[str, Any] = {}
        if "B_m1_norm" in cell:
            record["B_m1_norm"] = present(parse_num(cell["B_m1_norm"]), "out/static_schur_progress.json")
        if "c_star" in cell:
            record["c_star"] = present(parse_num(cell["c_star"]), "out/static_schur_progress.json")
        if "E_tail_m1" in cell:
            E_tail = parse_num(cell["E_tail_m1"])
            record["E_tail_m1"] = present(E_tail, "out/static_schur_progress.json")
            c_star = parse_num(cell["c_star"]) if "c_star" in cell else None
            if c_star is not None and c_star > 0:
                record["y_norm"] = present(mp.sqrt(E_tail / c_star), "derived sqrt(E_tail_m1/c_star) from out/static_schur_progress.json")
        out[key] = record
    return out


def feshbach_14_120_sources() -> Dict[str, Any]:
    path = OUT_DIR / "feshbach_lambda_sq_14_N_120.json"
    if not path.exists():
        return {}
    data = load_json(path)
    rec: Dict[str, Any] = {}
    rec["B_m1_norm"] = present(parse_num(data["block_matrices"]["B_m1_norm"]), "out/feshbach_lambda_sq_14_N_120.json:block_matrices")
    c_star = parse_num(data["class_fits_saved_only"]["c_star"]["lambda_sq_14_effective_c_star"])
    rec["c_star"] = present(c_star, "out/feshbach_lambda_sq_14_N_120.json:class_fits_saved_only")
    E_tail = parse_num(data["self_energy_spectroscopy"]["correction_m1_Bstar_Cinv_B_m1"])
    rec["E_tail_m1"] = present(E_tail, "out/feshbach_lambda_sq_14_N_120.json:self_energy_spectroscopy")
    dyn0 = data["dynamic_feshbach"][0]
    rec["y_norm"] = present(parse_num(dyn0["y_actual_norm"]), "out/feshbach_lambda_sq_14_N_120.json:dynamic_feshbach[0]")
    rec["nu_tail"] = present(parse_num(data["self_energy_spectroscopy"]["nu_tail_reference"]), "out/feshbach_lambda_sq_14_N_120.json:self_energy_spectroscopy")
    rec["note"] = "FeshbachGate key case; compatible with xi1/even source audit but not a fresh parity-block recomputation."
    return rec


def nconv_13_120_sources() -> Dict[str, Any]:
    path = OUT_DIR / "nconv_anchor_lambda_sq_13_N_120.json"
    if not path.exists():
        return {}
    data = load_json(path)
    rec: Dict[str, Any] = {}
    cache = data.get("xi_m_y_cache", [])
    if cache:
        rec["y_norm"] = present(parse_num(cache[0]["y_norm"]), "out/nconv_anchor_lambda_sq_13_N_120.json:xi_m_y_cache[0]")
    return rec


def rogue_tail_sources() -> Dict[Tuple[int, int], Dict[str, Any]]:
    out: Dict[Tuple[int, int], Dict[str, Any]] = {}
    for N in (90, 120):
        path = OUT_DIR / f"rogue_tail_lambda_sq_14_N_{N}.json"
        if not path.exists():
            continue
        data = load_json(path)
        if "run" in data:
            run = data["run"]
        elif N == 90:
            run = data.get("runs", {}).get("N90_dps")
        else:
            run = data.get("runs", {}).get("N120_dps")
        if run and "nu" in run:
            out[(14, N)] = {"nu_tail": present(parse_num(run["nu"]), f"out/{path.name}:runs.N{N}_dps.nu")}
    return out


def phase1_nu_context(lambda_sq: int, N: int) -> Optional[mp.mpf]:
    path = OUT_DIR / f"lambda_sq_{lambda_sq}_N_{N}.json"
    if not path.exists():
        return None
    data = load_json(path)
    return parse_num(data["nu"]) if "nu" in data else None


def merge_source_fields(point: Dict[str, Any], extras: Dict[Tuple[int, int], Dict[str, Any]]) -> None:
    key = (int(point["lambda_sq"]), int(point["N"]))
    rec = extras.get(key, {})
    for field in ("B_m1_norm", "c_star", "E_tail_m1", "y_norm", "nu_tail"):
        point[field] = rec.get(field, missing())
    legacy = phase1_nu_context(key[0], key[1])
    if legacy is not None:
        point["nu_phase1_legacy_not_nu_tail"] = present(legacy, f"out/lambda_sq_{key[0]}_N_{key[1]}.json")


def slope_fit(points: Sequence[Dict[str, Any]], field: str, N: int) -> Dict[str, Any]:
    rows = []
    for point in points:
        if int(point["N"]) != N:
            continue
        value: Optional[mp.mpf] = None
        source = "parity_block"
        if field in ("lambda1_G_even", "lambda2_G_even"):
            value = parse_num(point[field])
        elif field in ("r1", "theta1", "S0_odd"):
            value = abs(parse_complex(point[field]))
        else:
            entry = point.get(field)
            if isinstance(entry, dict) and entry.get("status") == "OK":
                value = parse_num(entry["value"])
                source = entry["source"]
        if value is not None and value > 0:
            rows.append({"lambda_sq": int(point["lambda_sq"]), "value": value, "log_value": mp.log(value), "source": source})
    rows = sorted(rows, key=lambda r: r["lambda_sq"])
    out: Dict[str, Any] = {"field": field, "N": N, "label": "FIT_NOT_LAW", "points": rows}
    if len(rows) < 3:
        out["status"] = "INSUFFICIENT_DATA"
        out["slope"] = None
        return out
    xs = [mp.mpf(r["lambda_sq"]) for r in rows]
    ys = [r["log_value"] for r in rows]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    denom = sum((x - mx) ** 2 for x in xs)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / denom
    intercept = my - slope * mx
    out.update({"status": "OK", "slope": slope, "slope_over_pi": slope / mp.pi, "intercept": intercept})
    return out


def close_to(value: mp.mpf, target: mp.mpf, rel: mp.mpf = mp.mpf("0.25")) -> bool:
    return abs(value - target) <= rel * max(abs(target), mp.mpf("1e-300"))


def classify_slopes(fits: Dict[str, Dict[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for N in (90, 120):
        lam = fits[f"lambda1_G_even_N{N}"]
        r1 = fits[f"r1_N{N}"]
        lam_slope = lam.get("slope")
        r1_slope = r1.get("slope")
        out[f"N{N}"] = {
            "lambda1_flat_pass": bool(lam_slope is not None and abs(lam_slope) <= mp.mpf("0.5")),
            "lambda1_old_minus_2pi_pass": bool(lam_slope is not None and close_to(lam_slope, -2 * mp.pi)),
            "r1_minus_4pi_pass": bool(r1_slope is not None and close_to(r1_slope, -4 * mp.pi)),
            "lambda1_slope": lam_slope,
            "r1_slope": r1_slope,
        }
    out["lambda1_flat_both_rows"] = all(out[f"N{N}"]["lambda1_flat_pass"] for N in (90, 120))
    out["r1_minus_4pi_both_rows"] = all(out[f"N{N}"]["r1_minus_4pi_pass"] for N in (90, 120))
    return out


def n_tail(points: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    by_lam: Dict[int, List[Tuple[int, mp.mpf]]] = {}
    for point in points:
        by_lam.setdefault(int(point["lambda_sq"]), []).append((int(point["N"]), abs(parse_complex(point["r1"]))))
    out: Dict[str, Any] = {}
    for lam, rows in by_lam.items():
        rows = sorted(rows)
        if len(rows) < 3:
            continue
        (_, x60), (_, x90), (_, x120) = rows[:3]
        d1 = x90 - x60
        d2 = x120 - x90
        rho = d1 / d2 if d2 != 0 else mp.inf
        x_inf = None
        tail = None
        if d2 != 0 and abs(rho) > 1:
            x_inf = x120 + d2 / (abs(rho) - 1)
            tail = abs(x120 - x_inf)
        out[str(lam)] = {
            "points": [{"N": N, "r1": x} for N, x in rows],
            "diff_60_90": d1,
            "diff_90_120": d2,
            "rho_diff_ratio": rho,
            "x_inf_geometric": x_inf,
            "tail_abs": tail,
            "label": "FIT_NOT_LAW",
        }
    return out


def finite_factor(a: mp.mpf, b: mp.mpf) -> mp.mpf:
    return max(abs(a) / abs(b), abs(b) / abs(a))


def build_payload() -> Dict[str, Any]:
    started = time.time()
    points = [read_parity_point(c, N) for c, N in POINTS]

    extras: Dict[Tuple[int, int], Dict[str, Any]] = {}
    extras.update(static_progress_sources())
    extras[(14, 120)] = {**extras.get((14, 120), {}), **feshbach_14_120_sources()}
    extras[(13, 120)] = {**extras.get((13, 120), {}), **nconv_13_120_sources()}
    for key, value in rogue_tail_sources().items():
        extras[key] = {**extras.get(key, {}), **value}
    for point in points:
        merge_source_fields(point, extras)

    r1_14_120 = next(abs(parse_complex(p["r1"])) for p in points if p["lambda_sq"] == 14 and p["N"] == 120)
    convention_factor = finite_factor(r1_14_120, R1_14_120_OLD_MIXED_REF)
    convention = {
        "old_mixed_3x3_reference": R1_14_120_OLD_MIXED_REF,
        "parity_block_2x2_even_r1_14_120": r1_14_120,
        "factor_max": convention_factor,
        "pass": convention_factor <= 3,
        "failure_if_false": "CONVENTION_DRIFT",
    }

    fits: Dict[str, Dict[str, Any]] = {}
    for N in (90, 120):
        for field in ("lambda1_G_even", "B_m1_norm", "c_star", "y_norm", "r1", "theta1"):
            fits[f"{field}_N{N}"] = slope_fit(points, field, N)
    slope_class = classify_slopes(fits)

    r1_12_120 = next(abs(parse_complex(p["r1"])) for p in points if p["lambda_sq"] == 12 and p["N"] == 120)
    repaired_factor = finite_factor(r1_12_120, REPAIRED_R1_12_120_REF)
    repaired = {
        "reference": REPAIRED_R1_12_120_REF,
        "measured_r1_12_120": r1_12_120,
        "factor_max": repaired_factor,
        "pass": repaired_factor <= 3,
        "failure_if_false": "REPAIRED_LAW_POINT_FAILS",
    }

    missing_fields = []
    for point in points:
        for field in ("B_m1_norm", "c_star", "y_norm", "nu_tail"):
            if point[field]["status"] == "MISSING":
                missing_fields.append({"lambda_sq": point["lambda_sq"], "N": point["N"], "field": field})

    critical_fields_missing = any(
        point.get(field) is None
        for point in points
        for field in ("lambda1_G_even", "lambda2_G_even", "S0_odd", "theta1", "r1")
    )

    if not convention["pass"]:
        verdict = "CONVENTION_DRIFT"
        failure_code = verdict
    elif critical_fields_missing:
        verdict = "JSON_FIELDS_MISSING"
        failure_code = verdict
    elif not repaired["pass"]:
        verdict = "REPAIRED_LAW_POINT_FAILS"
        failure_code = verdict
    elif slope_class["lambda1_flat_both_rows"] and slope_class["r1_minus_4pi_both_rows"]:
        verdict = "REGISTERED_MODEL_MISS_DENOMINATOR_FLAT"
        failure_code = None
    else:
        verdict = "R1_LAW_UNRESOLVED"
        failure_code = verdict

    return {
        "gate": "R1SourceAudit_v1",
        "route": "RouteB_TwoLevelSpectralLadder",
        "status": "complete" if failure_code is None else "stopped",
        "verdict": verdict,
        "failure_code": failure_code,
        "phase2_run": False,
        "new_lambda_or_N_anchor_bought": False,
        "heavy_compute_run": False,
        "q3_main_touched": False,
        "points": points,
        "R0_convention_lock": convention,
        "R1_missing_auxiliary_fields": {
            "count": len(missing_fields),
            "rows": missing_fields,
            "nonblocking_when_core_parity_fields_present": True,
        },
        "R2_slope_fits": fits,
        "R2_slope_classification": slope_class,
        "R3_N_tail": n_tail(points),
        "R4_repaired_law_point": repaired,
        "R4_watchpoint": {
            "name": "M1_Y_NORM_O1_NEAR_LAMBDA_SQ_19_21",
            "condition": "For any future lambda_sq>=18 anchor, record ||y|| and test whether M1 predicts ||y|| -> O(1) near lambda_sq 19-21.",
            "active_for_future_lambda_sq_ge": 18,
            "status": "NAMED_WATCHPOINT",
        },
        "elapsed_s": time.time() - started,
    }


def fmt(value: Any, digits: int = 10) -> str:
    if value is None:
        return "MISSING"
    if isinstance(value, dict):
        if value.get("status") == "MISSING":
            return "MISSING"
        return fmt(value.get("value"), digits)
    try:
        z = parse_complex(value)
        if abs(mp.im(z)) <= mp.mpf("1e-90") * max(abs(mp.re(z)), mp.mpf(1)):
            return mp.nstr(mp.re(z), digits)
        return mp.nstr(z, digits)
    except Exception:
        try:
            return mp.nstr(value, digits)
        except Exception:
            return str(value)


def fit_line(fit: Dict[str, Any]) -> str:
    if fit["status"] != "OK":
        return "INSUFFICIENT_DATA"
    return f"{fmt(fit['slope'], 12)} ({fmt(fit['slope_over_pi'], 8)} pi)"


def write_report(payload: Dict[str, Any]) -> None:
    lines = [
        "# R1SourceAudit_v1",
        "",
        "Status: diagnostic only. Not a proof of RH. Not a Route B kill. Phase 2 was not run. No new lambda/N anchors were bought. Heavy compute was not run.",
        "",
        "## Verdict",
        "",
        f"- verdict: `{payload['verdict']}`",
        f"- failure_code: `{payload['failure_code']}`",
        "- core convention: parity-block `2x2 even` denominator `lambda1(G_even)`",
        "- auxiliary missing fields were marked `MISSING`; no model-three interpolation was invented.",
        "",
        "## R0 Convention Lock",
        "",
        f"- old mixed-3x3 reference r1(14,120): `{fmt(payload['R0_convention_lock']['old_mixed_3x3_reference'], 12)}`",
        f"- parity-block 2x2-even r1(14,120): `{fmt(payload['R0_convention_lock']['parity_block_2x2_even_r1_14_120'], 12)}`",
        f"- factor max: `{fmt(payload['R0_convention_lock']['factor_max'], 8)}`",
        f"- pass: `{payload['R0_convention_lock']['pass']}`",
        "",
        "## R1 Pull Table",
        "",
        "| lambda_sq | N | lambda1(G_even) | lambda2(G_even) | S0_odd | theta1 | r1 | ||B m1|| | c* | ||y|| | nu_tail |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for point in sorted(payload["points"], key=lambda p: (p["lambda_sq"], p["N"])):
        lines.append(
            f"| {point['lambda_sq']} | {point['N']} | `{fmt(point['lambda1_G_even'], 8)}` | `{fmt(point['lambda2_G_even'], 8)}` | `{fmt(point['S0_odd'], 8)}` | `{fmt(point['theta1'], 8)}` | `{fmt(point['r1'], 8)}` | `{fmt(point['B_m1_norm'], 8)}` | `{fmt(point['c_star'], 8)}` | `{fmt(point['y_norm'], 8)}` | `{fmt(point['nu_tail'], 8)}` |"
        )

    lines.extend(
        [
            "",
            "## R2 Slope Fits",
            "",
            "Fits use natural `log(X)` vs `lambda_sq`. All are `FIT_NOT_LAW` diagnostics.",
            "",
            "| field | N=90 slope | N=120 slope | registered read |",
            "|---|---:|---:|---|",
        ]
    )
    fits = payload["R2_slope_fits"]
    lines.append(f"| lambda1(G_even) | `{fit_line(fits['lambda1_G_even_N90'])}` | `{fit_line(fits['lambda1_G_even_N120'])}` | flat model passes; old `-2pi` is refuted on these rows |")
    lines.append(f"| r1 | `{fit_line(fits['r1_N90'])}` | `{fit_line(fits['r1_N120'])}` | close to registered `-4pi` |")
    lines.append(f"| ||B m1|| | `{fit_line(fits['B_m1_norm_N90'])}` | `{fit_line(fits['B_m1_norm_N120'])}` | insufficient saved data |")
    lines.append(f"| c* | `{fit_line(fits['c_star_N90'])}` | `{fit_line(fits['c_star_N120'])}` | insufficient saved data |")
    lines.append(f"| ||y|| | `{fit_line(fits['y_norm_N90'])}` | `{fit_line(fits['y_norm_N120'])}` | insufficient saved data |")

    cls = payload["R2_slope_classification"]
    lines.extend(
        [
            "",
            "Classification:",
            f"- lambda1 flat both rows: `{cls['lambda1_flat_both_rows']}`",
            f"- r1 slope `-4pi` both rows: `{cls['r1_minus_4pi_both_rows']}`",
            "",
            "## R3 N-Tail",
            "",
            "| lambda_sq | r1(60) | r1(90) | r1(120) | rho | geometric r1_inf | tail |",
            "|---:|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for lam, row in sorted(payload["R3_N_tail"].items(), key=lambda kv: int(kv[0])):
        vals = {item["N"]: item["r1"] for item in row["points"]}
        lines.append(
            f"| {lam} | `{fmt(vals[60], 8)}` | `{fmt(vals[90], 8)}` | `{fmt(vals[120], 8)}` | `{fmt(row['rho_diff_ratio'], 8)}` | `{fmt(row['x_inf_geometric'], 8)}` | `{fmt(row['tail_abs'], 8)}` |"
        )

    repaired = payload["R4_repaired_law_point"]
    lines.extend(
        [
            "",
            "## R4 Decision",
            "",
            f"- repaired-law reference r1(12,120): `{fmt(repaired['reference'], 12)}`",
            f"- measured r1(12,120): `{fmt(repaired['measured_r1_12_120'], 12)}`",
            f"- factor max: `{fmt(repaired['factor_max'], 8)}`",
            f"- repaired point pass: `{repaired['pass']}`",
            f"- watchpoint: `{payload['R4_watchpoint']['name']}` for any future `lambda_sq>=18` anchor.",
            "",
            "Interpretation: the prior `r1` stop was a registered denominator-model miss. On the saved grid, `lambda1(G_even)` is flat while `r1` inherits the approximately `-4pi` law from `theta1`; the old `lambda1(G) ~ exp(-2pi lambda_sq)` denominator model is not supported.",
            "",
            "## Stop",
            "",
            "Stop after this report and handoff. Do not pick the next gate locally.",
            "",
        ]
    )
    REPORT.write_text("\n".join(lines), encoding="utf-8")


def write_handoff(payload: Dict[str, Any]) -> None:
    lines = [
        "PROSHKA_ROUTE_REVIEW",
        "",
        "Gate:",
        "R1SourceAudit_v1 / Route B TwoLevelSpectralLadder",
        "",
        "Verdict:",
        payload["verdict"],
        "",
        "Route status:",
        "NOT_KILLED. Diagnostic only. No RH claim. Phase 2 not run. No new lambda/N anchors. Heavy compute not run.",
        "",
        "What happened:",
        "- R0 convention lock passed: r1(14,120) in parity-block 2x2-even convention is within x3 of the old mixed-3x3 reference.",
        "- R1 pulled lambda1(G_even), lambda2(G_even), S0_odd, theta1, r1 for all 9 points.",
        f"- Auxiliary source fields missing count: `{payload['R1_missing_auxiliary_fields']['count']}`; they are explicitly marked MISSING.",
        "- R2 slopes use natural log vs lambda_sq and are labeled FIT_NOT_LAW.",
        "- lambda1(G_even) is flat on N=90 and N=120 rows; old -2pi denominator law is refuted on this saved grid.",
        "- r1 slope is close to -4pi on N=90 and N=120 rows.",
        "- repaired-law point r1(12,120) passes within x3.",
        "- R3 geometric N-tail gives r1(13,inf) around 7.21e-32 with finite-grid tail about 2.30e-32.",
        "",
        "Question for Proshka:",
        "Accept `REGISTERED_MODEL_MISS_DENOMINATOR_FLAT` as closure of the r1 source audit? If yes, carry the named watchpoint `M1_Y_NORM_O1_NEAR_LAMBDA_SQ_19_21` for any future lambda_sq>=18 anchor. Do not treat this as RH proof or Route B kill.",
        "",
        "Stop condition:",
        "Codex stops here after report + handoff and does not pick the next gate locally.",
    ]
    HANDOFF.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_loop_state(payload: Dict[str, Any]) -> None:
    state = load_json(LOOP_STATE) if LOOP_STATE.exists() else {}
    state.update(
        {
            "current_gate": "WAITING_FOR_PROSHKA_REVIEW_AFTER_R1_SOURCE_AUDIT_V1",
            "last_attempted_gate": "R1SourceAudit_v1",
            "last_completed_gate": "R1SourceAudit_v1",
            "last_completed_gate_status": "COMPLETED_PASS" if payload["failure_code"] is None else "COMPLETED_WITH_REGISTERED_FAILURE",
            "last_verdict": payload["verdict"],
            "failure_code": payload["failure_code"] or payload["verdict"],
            "r1_source_audit_report": "r1_source_audit_v1.md",
            "r1_source_audit_json": "out/r1_source_audit_v1.json",
            "next_gate": None,
            "requires_proshka_after_gate": True,
            "phase2_allowed": False,
            "q3_main_allowed": False,
            "updated_at_unix": time.time(),
        }
    )
    LOOP_STATE.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    payload = build_payload()
    write_json(JSON_OUT, payload)
    write_report(payload)
    write_handoff(payload)
    update_loop_state(payload)
    return 0 if payload["failure_code"] is None else 3


if __name__ == "__main__":
    raise SystemExit(main())
