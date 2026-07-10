#!/usr/bin/env python3
"""CombMeanValueFalsifier_v1.

Request-local Route B diagnostic. Uses the saved zero cache only; does not
recompute zeros.
"""

from __future__ import annotations

import argparse
import cmath
import hashlib
import json
import math
from pathlib import Path


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
ZERO_PATH = OUT_DIR / "anchor_locked_zeros_first_2000.json"
OUTPUT_PATH = OUT_DIR / "comb_meanvalue_falsifier_v1.json"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_gammas(path: Path) -> list[float]:
    with path.open() as f:
        payload = json.load(f)
    zeros = payload["zeros"]
    if len(zeros) < 2000:
        raise RuntimeError(f"expected at least 2000 zeros, got {len(zeros)}")
    return [float(row["gamma"]) for row in zeros]


LOGS = [math.log(m) for m in range(1, 14)]
WEIGHTS = [m ** -0.5 for m in range(1, 14)]
H13 = sum(1.0 / m for m in range(1, 14))
NULL_VALUE = 3.18


def D(gamma: float) -> complex:
    return sum(w * cmath.exp(1j * gamma * log_m) for w, log_m in zip(WEIGHTS, LOGS))


def mean_abs_D_sq(gammas: list[float]) -> float:
    return sum(abs(D(gamma)) ** 2 for gamma in gammas) / len(gammas)


def in_band(x: float, lo: float, hi: float) -> bool:
    return lo <= x <= hi


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    gammas = load_gammas(ZERO_PATH)
    f1 = {
        "J500": {
            "mean_abs_D_sq": mean_abs_D_sq(gammas[:500]),
            "registered_band": [1.10, 1.90],
            "prediction": 1.468,
            "gamma_J": gammas[499],
        },
        "J1000": {
            "mean_abs_D_sq": mean_abs_D_sq(gammas[:1000]),
            "gamma_J": gammas[999],
        },
        "J2000": {
            "mean_abs_D_sq": mean_abs_D_sq(gammas[:2000]),
            "registered_band": [1.55, 2.15],
            "prediction": 1.853,
            "gamma_J": gammas[1999],
        },
    }
    for key in ("J500", "J2000"):
        lo, hi = f1[key]["registered_band"]
        f1[key]["registered_pass"] = in_band(f1[key]["mean_abs_D_sq"], lo, hi)

    shadow_mean = mean_abs_D_sq([gamma + 0.25 for gamma in gammas[:2000]])
    f1["shadow_shift_plus_0_25_J2000"] = {
        "mean_abs_D_sq": shadow_mean,
        "target_null_value": NULL_VALUE,
        "moves_toward_null": abs(shadow_mean - NULL_VALUE)
        < abs(f1["J2000"]["mean_abs_D_sq"] - NULL_VALUE),
    }
    f1["null_control"] = {
        "null_value": NULL_VALUE,
        "excluded_at_J2000": not in_band(NULL_VALUE, *f1["J2000"]["registered_band"]),
        "H13": H13,
    }

    midpoint_gammas = [(gammas[i] + gammas[i + 1]) / 2.0 for i in range(500)]
    midpoint_mean = mean_abs_D_sq(midpoint_gammas)
    zero_mean_500 = f1["J500"]["mean_abs_D_sq"]
    f2 = {
        "midpoint_J500_mean_abs_D_sq": midpoint_mean,
        "zero_J500_mean_abs_D_sq": zero_mean_500,
        "ratio_midpoint_over_zero": midpoint_mean / zero_mean_500,
        "direction_pass": midpoint_mean >= zero_mean_500,
    }

    verdict = (
        "COMB_MEANVALUE_CONFIRMED"
        if f1["J500"]["registered_pass"]
        and f1["J2000"]["registered_pass"]
        and f1["null_control"]["excluded_at_J2000"]
        and f1["shadow_shift_plus_0_25_J2000"]["moves_toward_null"]
        and f2["direction_pass"]
        else "COMB_MEANVALUE_REFUTED"
    )

    payload = {
        "gate": "CombMeanValueFalsifier_v1",
        "status": "NOT_RH_DIAGNOSTIC_ONLY",
        "zero_compute": False,
        "zeros_recomputed": False,
        "zero_dataset": str(ZERO_PATH.relative_to(REQUEST_DIR)),
        "zero_dataset_sha256": sha256_file(ZERO_PATH),
        "formula": "D(gamma)=sum_{m<=13} m^(-1/2+i gamma)",
        "compute_class": "near_zero_float64_13_term_sums_on_cached_zeros",
        "float64_used": True,
        "F1": f1,
        "F2": f2,
        "verdict": verdict,
        "guardrails": {
            "not_RH": True,
            "phase2_run": False,
            "qW_formula_changed": False,
            "packet_definition_changed": False,
            "q3_main_touched": False,
            "next_gate_selected": False,
        },
    }

    if args.write:
        OUT_DIR.mkdir(parents=True, exist_ok=True)
        with OUTPUT_PATH.open("w") as f:
            json.dump(payload, f, indent=2, sort_keys=True)
            f.write("\n")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
