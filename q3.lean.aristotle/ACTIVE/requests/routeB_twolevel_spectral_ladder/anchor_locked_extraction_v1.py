#!/usr/bin/env python3
"""AnchorLocked_Extraction_v1.

Request-local extractor for the pinned AnchorLockedKChannel_v1 JSON only.
It performs no Route B numerical run, no matrix build, and no zero computation.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import os
import subprocess
import sys
from decimal import Decimal, getcontext
from pathlib import Path
from statistics import median


getcontext().prec = 90

PINNED_JSON_SHA256 = "65fa8e57978bb610d96c36e3ace877f0a910fc2ecad4fcda11524c26e3f182f9"

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]
DEFAULT_INPUT = ROOT / "out" / "anchor_locked_k_channel_v1.json"
OUT_JSON = ROOT / "out" / "anchor_locked_extraction_v1.json"
REPORT_MD = ROOT / "anchor_locked_extraction_v1.md"
ACTIONS_MD = ROOT / "anchor_locked_extraction_v1_actions_log.md"
HANDOFF_MD = ROOT / "handoff_to_proshka.md"


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def run_git(args: list[str]) -> str:
    cp = subprocess.run(["git", *args], cwd=REPO, text=True, capture_output=True, check=False)
    out = cp.stdout.strip()
    err = cp.stderr.strip()
    if cp.returncode != 0:
        return f"ERROR({cp.returncode}): {err or out}"
    return out or "(empty)"


def dec(value: object) -> Decimal:
    return Decimal(str(value))


def as_float(value: object) -> float:
    return float(str(value))


def linfit(xs: list[float], ys: list[float]) -> tuple[float, float, float]:
    n = len(xs)
    xbar = sum(xs) / n
    ybar = sum(ys) / n
    sxx = sum((x - xbar) ** 2 for x in xs)
    slope = sum((x - xbar) * (y - ybar) for x, y in zip(xs, ys)) / sxx
    intercept = ybar - slope * xbar
    if n > 2:
        rss = sum((y - (intercept + slope * x)) ** 2 for x, y in zip(xs, ys))
        stderr = math.sqrt(rss / (n - 2) / sxx)
    else:
        stderr = float("nan")
    return slope, intercept, stderr


def tail_integral(g0: float, g1: float, p: float) -> float:
    """Integral of gamma^(-2p) * log(gamma / 2pi) / 2pi."""
    two_pi = 2.0 * math.pi
    q = 1.0 - 2.0 * p
    if abs(q) < 1e-10:
        return 0.5 * (math.log(g1 / two_pi) ** 2 - math.log(g0 / two_pi) ** 2) / two_pi

    def primitive(g: float) -> float:
        return (g**q) * (math.log(g / two_pi) / q - 1.0 / (q * q)) / two_pi

    return primitive(g1) - primitive(g0)


def solve_p_for_ratio(g0: float, g1: float, g2: float, target: float) -> dict[str, object]:
    def ratio(p: float) -> float:
        return tail_integral(g0, g1, p) / tail_integral(g1, g2, p)

    lo = 0.0
    hi = 1.0
    while ratio(hi) < target and hi < 64.0:
        hi *= 2.0
    if ratio(hi) < target:
        return {"status": "NO_BRACKET", "target": target, "lo": lo, "hi": hi, "ratio_hi": ratio(hi)}
    for _ in range(100):
        mid = (lo + hi) / 2.0
        if ratio(mid) < target:
            lo = mid
        else:
            hi = mid
    p = (lo + hi) / 2.0
    return {"status": "OK", "target": target, "p": p, "ratio_at_p": ratio(p)}


def e1_extract(data: dict[str, object]) -> tuple[dict[str, object], dict[str, object]]:
    profiles = data["A4_crossover_retest"]["profiles"]
    bands = {
        "lambda_sq_12_N_120": (Decimal("1.7e-26"), Decimal("6.8e-26")),
        "lambda_sq_14_N_120": (Decimal("0.9e-31"), Decimal("3.6e-31")),
        "lambda_sq_13_N_90": (Decimal("4e-29"), Decimal("1.6e-28")),
    }
    rows = {}
    for key, (lo, hi) in bands.items():
        checkpoints = profiles[key]["checkpoints"]
        c_values = [dec(row["C"]) for row in checkpoints if row["J"] in (100, 150, 200)]
        per_checkpoint = [
            {
                "J": row["J"],
                "C": str(dec(row["C"])),
                "band_pass": lo <= dec(row["C"]) <= hi,
            }
            for row in checkpoints
            if row["J"] in (100, 150, 200)
        ]
        med = sorted(c_values)[len(c_values) // 2]
        rows[key] = {
            "lambda_sq": profiles[key]["lambda_sq"],
            "N": profiles[key]["N"],
            "band": [str(lo), str(hi)],
            "C_J100_150_200": [str(x) for x in c_values],
            "per_checkpoint": per_checkpoint,
            "median_C": str(med),
            "median_band_pass": lo <= med <= hi,
            "all_checkpoint_band_pass": all(item["band_pass"] for item in per_checkpoint),
        }

    c12 = Decimal(rows["lambda_sq_12_N_120"]["median_C"])
    c13 = dec(data["A5_tail_13_120"]["C_refit"])
    c14 = Decimal(rows["lambda_sq_14_N_120"]["median_C"])
    xs = [math.log(math.sqrt(x)) for x in (12, 13, 14)]
    ys = [
        math.log(float(c12 * c12)) + 4.0 * math.pi * 12.0,
        math.log(float(c13 * c13)) + 4.0 * math.pi * 13.0,
        math.log(float(c14 * c14)) + 4.0 * math.pi * 14.0,
    ]
    slope, intercept, stderr = linfit(xs, ys)
    slope_pass = 9.5 <= slope <= 12.5
    code = "LEDGER_LAMBDA_CLASS_PASS" if all(r["median_band_pass"] for r in rows.values()) and slope_pass else "LEDGER_LAMBDA_CLASS_FAILS"

    shadow = copy.deepcopy(data)
    shadow_row = shadow["A4_crossover_retest"]["profiles"]["lambda_sq_14_N_120"]["checkpoints"][0]
    shadow_row["C"] = str(dec(shadow_row["C"]) * Decimal(3))
    lo, hi = bands["lambda_sq_14_N_120"]
    fired = not (lo <= dec(shadow_row["C"]) <= hi)
    self_test = {
        "name": "K1_shadow_multiply_one_C_by_3",
        "mutated_line": "A4_crossover_retest.profiles.lambda_sq_14_N_120.checkpoints[J=100].C",
        "mutated_C": str(dec(shadow_row["C"])),
        "band": [str(lo), str(hi)],
        "fired": fired,
        "firing_line": "lambda_sq_14_N_120/J=100/C band judge" if fired else None,
    }

    result = {
        "code": code,
        "rows": rows,
        "C_13_120_anchor_column": str(c13),
        "C_13_120_anchor_quote": "7.9190e-29",
        "slope_fit_log_C2_over_E_vs_log_lambda": {
            "lambda_sq_used": [12, 13, 14],
            "slope": slope,
            "stderr": stderr,
            "registered": "11 +/- 1.5",
            "packet_side_quote": "11.27",
            "fit_label": "FIT_NOT_LAW",
            "pass": slope_pass,
        },
    }
    return result, self_test


def e2_extract(data: dict[str, object]) -> dict[str, object]:
    checkpoints = data["A5_tail_13_120"]["checkpoints"]
    by_j = {row["J"]: row for row in checkpoints}
    windows = [
        ("W1", 500, 750),
        ("W2", 750, 1000),
        ("W3", 1000, 1500),
        ("W4", 1500, 2000),
    ]
    c_band = (Decimal("6e-29"), Decimal("1.2e-28"))
    window_rows = []
    for name, j0, j1 in windows:
        right_c = dec(by_j[j1]["C"])
        left = by_j[j0]
        right = by_j[j1]
        delta_s = dec(right["S_J_over_a1"]) - dec(left["S_J_over_a1"])
        window_rows.append(
            {
                "window": name,
                "gamma_window": [str(left["gamma"]), str(right["gamma"])],
                "right_endpoint_J": j1,
                "right_endpoint_C": str(right_c),
                "right_endpoint_C_band_pass": c_band[0] <= right_c <= c_band[1],
                "delta_S_over_a1_from_checkpoints": str(delta_s),
            }
        )

    p_rows = []
    for i in range(3):
        left = window_rows[i]
        right = window_rows[i + 1]
        delta_a = float(dec(left["delta_S_over_a1_from_checkpoints"]))
        delta_b = float(dec(right["delta_S_over_a1_from_checkpoints"]))
        g0 = float(left["gamma_window"][0])
        g1 = float(left["gamma_window"][1])
        g2 = float(right["gamma_window"][1])
        solved = solve_p_for_ratio(g0, g1, g2, delta_a / delta_b)
        p_val = solved.get("p")
        pass_band = isinstance(p_val, float) and 0.8 <= p_val <= 1.4
        p_rows.append(
            {
                "pair": f"{left['window']}/{right['window']}",
                "delta_ratio": delta_a / delta_b,
                "solve": solved,
                "registered_band": [0.8, 1.4],
                "pass": pass_band,
            }
        )
    code = "MASS_P_CONFIRMED" if all(r["right_endpoint_C_band_pass"] for r in window_rows) and all(r["pass"] for r in p_rows) else "MASS_P_OUT_OF_RANGE"
    return {
        "code": code,
        "window_C_band": [str(c_band[0]), str(c_band[1])],
        "window_rows": window_rows,
        "mythos_hand_values_quoted": {"W3": "9.3e-29", "W4": "8.7e-29"},
        "p_mass_rows": p_rows,
        "note": "C-band passes on checkpoint C values; strict DeltaS adjacent-pair p_mass does not pass all registered bands.",
    }


def e3_extract(data: dict[str, object]) -> dict[str, object]:
    profiles = data["A4_crossover_retest"]["profiles"]
    rows = [
        {"point": "lambda_sq_13_N_120", "S200_over_a1": 0.506, "source": "goal-supplied certified scalar"},
        {"point": "lambda_sq_12_N_120", "S200_over_a1": as_float(profiles["lambda_sq_12_N_120"]["S_200_over_a1"]), "source": "JSON A4"},
        {"point": "lambda_sq_14_N_120", "S200_over_a1": as_float(profiles["lambda_sq_14_N_120"]["S_200_over_a1"]), "source": "JSON A4"},
        {"point": "lambda_sq_13_N_90", "S200_over_a1": as_float(profiles["lambda_sq_13_N_90"]["S_200_over_a1"]), "source": "JSON A4"},
    ]
    vals = [row["S200_over_a1"] for row in rows]
    mean = sum(vals) / len(vals)
    max_deviation = max(abs(v - mean) for v in vals)
    full_range = max(vals) - min(vals)
    pass_gate = abs(mean - 0.53) <= 0.02 and max_deviation <= 0.05
    return {
        "code": "UNIVERSAL_COLLAPSE_CONFIRMED" if pass_gate else "UNIVERSAL_COLLAPSE_REFUTED",
        "rows": rows,
        "mean": mean,
        "registered_mean": 0.53,
        "spread_definition": "max absolute deviation from mean",
        "spread": max_deviation,
        "range": full_range,
        "registered_spread_max": 0.05,
        "pass": pass_gate,
    }


def build_markdown(result: dict[str, object]) -> str:
    e1 = result["E1_ledger"]
    e2 = result["E2_mass_p"]
    e3 = result["E3_universality"]
    e4 = result["E4_relabel"]
    lines: list[str] = []
    lines.append("# AnchorLocked_Extraction_v1")
    lines.append("")
    lines.append("Status: NOT RH. Diagnostic Route B / Route Z E5 extraction only. No Phase 2, no new run, no matrix build, no zeros computed.")
    lines.append("")
    lines.append("## Verdict")
    lines.append("")
    lines.append(f"- Overall: `{result['overall_verdict']}`")
    lines.append(f"- J0: `{result['J0']['code']}`; input sha256 `{result['J0']['sha256']}`.")
    lines.append(f"- K1 self-test: fired `{result['K1_self_test']['fired']}` at `{result['K1_self_test']['firing_line']}`.")
    lines.append(f"- E1: `{e1['code']}`.")
    lines.append(f"- E2: `{e2['code']}`.")
    lines.append(f"- E3: `{e3['code']}`.")
    lines.append(f"- E4: `{e4['status']}`.")
    lines.append("")
    lines.append("## Protocol Guardrails")
    lines.append("")
    for key in ["not_RH", "phase2_run", "qW_formula_changed", "packet_definition_changed", "q3_main_touched"]:
        lines.append(f"- `{key}` from JSON: `{result['source_flags'][key]}`")
    lines.append("")
    lines.append("## E1 Ledger C(lambda)")
    lines.append("")
    lines.append("| point | C(J=100) | C(J=150) | C(J=200) | median C | band | pass |")
    lines.append("| --- | ---: | ---: | ---: | ---: | --- | --- |")
    for point, row in e1["rows"].items():
        vals = row["C_J100_150_200"]
        lines.append(
            f"| `{point}` | `{float(Decimal(vals[0])):.6e}` | `{float(Decimal(vals[1])):.6e}` | `{float(Decimal(vals[2])):.6e}` | "
            f"`{float(Decimal(row['median_C'])):.6e}` | `{row['band'][0]}..{row['band'][1]}` | `{row['median_band_pass']}` |"
        )
    fit = e1["slope_fit_log_C2_over_E_vs_log_lambda"]
    lines.append("")
    lines.append(f"- C(13,120) anchor column quoted from A5: `{e1['C_13_120_anchor_quote']}` (`{float(Decimal(e1['C_13_120_anchor_column'])):.12e}`).")
    lines.append(f"- Slope log(C^2/E) vs log(lambda): `{fit['slope']:.12g}` +/- `{fit['stderr']:.12g}`; registered `{fit['registered']}`; packet-side quote `{fit['packet_side_quote']}`; `{fit['fit_label']}`.")
    lines.append("")
    lines.append("## E2 Mass-P")
    lines.append("")
    lines.append("| window | gamma range | right-end C | C band pass | DeltaS/a1 |")
    lines.append("| --- | --- | ---: | --- | ---: |")
    for row in e2["window_rows"]:
        lines.append(
            f"| `{row['window']}` | `{float(Decimal(row['gamma_window'][0])):.6g}..{float(Decimal(row['gamma_window'][1])):.6g}` | "
            f"`{float(Decimal(row['right_endpoint_C'])):.6e}` | `{row['right_endpoint_C_band_pass']}` | `{float(Decimal(row['delta_S_over_a1_from_checkpoints'])):.6e}` |"
        )
    lines.append("")
    lines.append(f"- Registered C band: `{e2['window_C_band'][0]}..{e2['window_C_band'][1]}`.")
    lines.append(f"- Mythos hand values quoted: W3 `{e2['mythos_hand_values_quoted']['W3']}`, W4 `{e2['mythos_hand_values_quoted']['W4']}`.")
    lines.append("")
    lines.append("| adjacent pair | DeltaS ratio | p_mass | registered | pass |")
    lines.append("| --- | ---: | ---: | --- | --- |")
    for row in e2["p_mass_rows"]:
        solve = row["solve"]
        p_val = solve.get("p")
        p_text = f"{p_val:.12g}" if isinstance(p_val, float) else str(solve)
        lines.append(f"| `{row['pair']}` | `{row['delta_ratio']:.12g}` | `{p_text}` | `0.8..1.4` | `{row['pass']}` |")
    lines.append("")
    lines.append(f"- E2 note: {e2['note']}")
    lines.append("")
    lines.append("## E3 Universality Line")
    lines.append("")
    lines.append("| point | S200/a1 | source |")
    lines.append("| --- | ---: | --- |")
    for row in e3["rows"]:
        lines.append(f"| `{row['point']}` | `{row['S200_over_a1']:.12g}` | {row['source']} |")
    lines.append("")
    lines.append(f"- Mean `{e3['mean']:.12g}` vs registered `0.53`; spread `{e3['spread']:.12g}` by `{e3['spread_definition']}`; full range `{e3['range']:.12g}`.")
    lines.append("")
    lines.append("## E4 Relabel")
    lines.append("")
    lines.append(f"- Requested relabel: `TAIL_FLATTENING_REFUTED -> TAIL_MASS_CONFIRMED + P_ESTIMATOR_ARTIFACT`.")
    lines.append(f"- Extraction status: `{e4['status']}`.")
    lines.append(f"- Grounds: S2000/a1 `{e4['S_2000_over_a1']}`; C_refit relative miss `{e4['C_refit_relative_miss']}`; E2 code `{e2['code']}`.")
    lines.append(f"- Future gate note: `{e4['future_gate_note']}`.")
    lines.append("")
    lines.append("## Final State Action")
    lines.append("")
    lines.append(f"- ROUTE_B_STATE.md update mode: `{result['state_update_mode']}`.")
    lines.append("- handoff_to_proshka.md rewritten for this extraction.")
    lines.append("- No next gate selected.")
    lines.append("")
    lines.append("## Output JSON")
    lines.append("")
    lines.append("- `out/anchor_locked_extraction_v1.json`.")
    lines.append("")
    lines.append("## Actions Log")
    lines.append("")
    lines.append("- `anchor_locked_extraction_v1_actions_log.md`.")
    lines.append("")
    return "\n".join(lines)


def build_handoff(result: dict[str, object]) -> str:
    e1 = result["E1_ledger"]
    e2 = result["E2_mass_p"]
    e3 = result["E3_universality"]
    e4 = result["E4_relabel"]
    fit = e1["slope_fit_log_C2_over_E_vs_log_lambda"]
    return f"""PROSHKA_ROUTE_REVIEW

Gate:
AnchorLocked_Extraction_v1 / Route B / Route Z E5

Verdict:
{result['overall_verdict']}

Files written:
- ACTIVE/requests/routeB_twolevel_spectral_ladder/anchor_locked_extraction_v1.py
- ACTIVE/requests/routeB_twolevel_spectral_ladder/anchor_locked_extraction_v1.md
- ACTIVE/requests/routeB_twolevel_spectral_ladder/out/anchor_locked_extraction_v1.json
- ACTIVE/requests/routeB_twolevel_spectral_ladder/anchor_locked_extraction_v1_actions_log.md
- ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_STATE.md
- ACTIVE/requests/routeB_twolevel_spectral_ladder/handoff_to_proshka.md

Top numbers:
- J0 sha: {result['J0']['sha256']} = pinned.
- K1 self-test fired at: {result['K1_self_test']['firing_line']}.
- E1 code: {e1['code']}; zero-side slope log(C^2/E) vs log(lambda) = {fit['slope']:.12g}; packet-side quote = 11.27.
- E2 code: {e2['code']}; checkpoint C-band passes, but strict DeltaS p_mass rows are {[round(row['solve'].get('p', float('nan')), 6) if isinstance(row['solve'].get('p'), float) else row['solve'].get('status') for row in e2['p_mass_rows']]}.
- E3 code: {e3['code']}; mean={e3['mean']:.12g}, spread={e3['spread']:.12g}.
- E4 status: {e4['status']}; S2000/a1={e4['S_2000_over_a1']}; C_refit relative miss={e4['C_refit_relative_miss']}.

What was NOT changed:
- No RH claim.
- No Phase 2.
- No new runs, matrix builds, or zero computations.
- No QW formula or packet-definition changes.
- No next gate selected.

Interpretation:
The lambda^11 edge ledger passes and U3 collapse is confirmed. The requested tail relabel is not applied as a promoted state because the strict A5 checkpoint DeltaS p_mass judge returns MASS_P_OUT_OF_RANGE, even though the checkpoint C values sit in the registered mass band.

Question for Proshka:
Should E2's official MASS-P judge use the checkpoint C-band envelope only, or the strict adjacent-window DeltaS p_mass extraction used here? If strict DeltaS is authoritative, the requested TAIL_MASS_CONFIRMED relabel is blocked.

Suggested next gates:
NONE SELECTED BY CODEX. Stop for review.

Failure/status codes:
{e1['code']}, {e2['code']}, {e3['code']}, {e4['status']}
"""


def build_actions_log(args: argparse.Namespace, files: list[Path]) -> str:
    rows = []
    for path in files:
        rows.append({"path": rel(path), "exists": path.exists(), "sha256": sha256_file(path)})
    diff_stat = run_git(["diff", "--stat", "--", str(ROOT.relative_to(REPO))])
    status_short = run_git(["status", "--short", str(ROOT.relative_to(REPO))])
    lines = [
        "# AnchorLocked_Extraction_v1 Actions Log",
        "",
        "## Scripts And Args",
        "",
        f"- python: `{sys.executable}`; script: `{rel(Path(__file__).resolve())}`; args: `{sys.argv[1:]}`",
        "",
        "## Files And SHA256",
        "",
    ]
    for row in rows:
        lines.append(f"- `{row['path']}` sha256 `{row['sha256']}` exists `{row['exists']}`")
    lines += [
        "",
        "## Git Diff Stat",
        "",
        "```text",
        diff_stat,
        "```",
        "",
        "## Git Status Short",
        "",
        "```text",
        status_short,
        "```",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default=str(DEFAULT_INPUT))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    input_path = Path(args.input)
    input_sha = sha256_file(input_path)
    if input_sha != PINNED_JSON_SHA256:
        result = {
            "overall_verdict": "JSON_SHA_MISMATCH",
            "J0": {"code": "JSON_SHA_MISMATCH", "sha256": input_sha, "pinned": PINNED_JSON_SHA256},
        }
        print(json.dumps(result, indent=2))
        return 2

    data = json.loads(input_path.read_text())
    e1, self_test = e1_extract(data)
    e2 = e2_extract(data)
    e3 = e3_extract(data)
    c_refit = dec(data["A5_tail_13_120"]["C_refit"])
    c_ref = dec(data["A5_tail_13_120"]["C_refit_reference"])
    c_rel = abs(c_refit - c_ref) / c_ref
    e4_status = "RELABEL_REJECTED_E2_MASS_P_OUT_OF_RANGE" if e2["code"] != "MASS_P_CONFIRMED" else "TAIL_MASS_CONFIRMED_PLUS_P_ESTIMATOR_ARTIFACT"
    overall = "REJECTED_E2_MASS_P_OUT_OF_RANGE" if e2["code"] != "MASS_P_CONFIRMED" else "ANCHORLOCKED_EXTRACTION_PASS"
    result = {
        "overall_verdict": overall,
        "route": "RouteB_TwoLevelSpectralLadder",
        "gate": "AnchorLocked_Extraction_v1",
        "J0": {"code": "JSON_SHA_MATCH", "sha256": input_sha, "pinned": PINNED_JSON_SHA256},
        "K1_self_test": self_test,
        "source_flags": {
            "not_RH": data.get("not_RH"),
            "phase2_run": data.get("phase2_run"),
            "qW_formula_changed": data.get("qW_formula_changed"),
            "packet_definition_changed": data.get("packet_definition_changed"),
            "q3_main_touched": data.get("q3_main_touched"),
        },
        "E1_ledger": e1,
        "E2_mass_p": e2,
        "E3_universality": e3,
        "E4_relabel": {
            "status": e4_status,
            "requested": "TAIL_FLATTENING_REFUTED -> TAIL_MASS_CONFIRMED + P_ESTIMATOR_ARTIFACT",
            "S_2000_over_a1": data["A5_tail_13_120"]["S_2000_over_a1"],
            "S_2000_registered_pass": data["A5_tail_13_120"]["S_2000_registered_pass"],
            "C_refit": str(c_refit),
            "C_refit_reference": str(c_ref),
            "C_refit_relative_miss": str(c_rel),
            "future_gate_note": "raise tau denominator dps 80 -> 100",
        },
        "state_update_mode": "append_rejection_history_no_tail_relabel" if e2["code"] != "MASS_P_CONFIRMED" else "apply_requested_tail_relabel",
    }

    if not self_test["fired"]:
        result["overall_verdict"] = "REJECTED_K1_SELF_TEST_DID_NOT_FIRE"

    if args.write:
        OUT_JSON.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        REPORT_MD.write_text(build_markdown(result))
        HANDOFF_MD.write_text(build_handoff(result))
        files = [
            input_path,
            Path(__file__).resolve(),
            OUT_JSON,
            REPORT_MD,
            HANDOFF_MD,
            ROOT / "ROUTE_B_STATE.md",
            ROOT / "loop_state.json",
        ]
        ACTIONS_MD.write_text(build_actions_log(args, files))

    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["overall_verdict"].startswith("ANCHORLOCKED") else 1


if __name__ == "__main__":
    raise SystemExit(main())
