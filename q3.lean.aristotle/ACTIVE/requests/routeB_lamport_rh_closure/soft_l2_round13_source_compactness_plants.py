#!/usr/bin/env python3
"""Execute the three Round-13 validators for the optional source leaf."""

from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
OUT = HERE / "SOFT_L2_ROUND13_SOURCE_COMPACTNESS_PLANTS.json"


def integrate(y: np.ndarray, x: np.ndarray) -> float:
    return float(np.trapezoid(y, x))


def raw_bump(x: np.ndarray) -> np.ndarray:
    y = np.zeros_like(x)
    inside = np.abs(x) < 1.0
    y[inside] = np.exp(-1.0 / (1.0 - x[inside] ** 2))
    return y


def shifted(x: np.ndarray, values: np.ndarray, amount: float) -> np.ndarray:
    return np.interp(x - amount, x, values, left=0.0, right=0.0)


def autocorrelation(x: np.ndarray, values: np.ndarray, lag: float) -> float:
    return integrate(values * shifted(x, values, -lag), x)


def shift_plant(x: np.ndarray, q: np.ndarray) -> dict:
    amount = 3.0
    q_shift = shifted(x, q, amount)
    lags = [-0.7, 0.0, 0.55]
    base_a = [autocorrelation(x, q, t) for t in lags]
    shift_a = [autocorrelation(x, q_shift, t) for t in lags]
    max_diff = max(abs(a - b) for a, b in zip(base_a, shift_a))
    base_center = integrate(x * q**2, x)
    shifted_center = integrate(x * q_shift**2, x)
    fired = max_diff < 2e-7 and abs((shifted_center - base_center) - amount) < 2e-5
    return {
        "id": "P1_SHIFT",
        "formula": "q_a(u)=q(u-a)",
        "target": "autocorrelation cannot determine absolute source center",
        "lags": lags,
        "base_autocorrelation": base_a,
        "shifted_autocorrelation": shift_a,
        "max_abs_autocorrelation_difference": max_diff,
        "source_center_displacement": shifted_center - base_center,
        "nonzero_shift_breaks_even_sector": True,
        "status": "FIRED" if fired else "MISSED",
        "code": "SOURCE_CENTER_NOT_VISIBLE_TO_AUTOCORRELATION" if fired else "SHIFT_PLANT_MISSED",
    }


def scale_plant(x: np.ndarray, q: np.ndarray) -> dict:
    scales = [1.0, 2.0, 4.0, 8.0, 16.0]
    central_radius = 0.25
    fixed_lag = 0.2
    rows = []
    for a in scales:
        qa = math.sqrt(a) * np.interp(a * x, x, q, left=0.0, right=0.0)
        norm_sq = integrate(qa**2, x)
        central_mass = integrate(qa[np.abs(x) <= central_radius] ** 2, x[np.abs(x) <= central_radius])
        fixed_lag_a = autocorrelation(x, qa, fixed_lag)
        h = 1.0 / a
        translation_defect = math.sqrt(
            max(0.0, integrate((shifted(x, qa, h) - qa) ** 2, x))
        )
        rows.append(
            {
                "a": a,
                "norm_sq": norm_sq,
                "central_mass_radius_0p25": central_mass,
                "A_at_fixed_lag_0p2": fixed_lag_a,
                "translation_step_h_eq_1_over_a": h,
                "translation_defect": translation_defect,
                "distributional_L1_scaling_factor": 1.0 / a,
            }
        )

    norms_ok = max(abs(r["norm_sq"] - 1.0) for r in rows) < 2e-4
    concentration_ok = rows[-1]["central_mass_radius_0p25"] > 0.999
    fixed_lag_collapse = abs(rows[-1]["A_at_fixed_lag_0p2"]) < 1e-8
    translation_failure = min(r["translation_defect"] for r in rows) > 0.25
    fired = norms_ok and concentration_ok and fixed_lag_collapse and translation_failure
    return {
        "id": "P2_SCALE",
        "formula": "q_a(u)=a^(1/2) q(a u)",
        "target": "edge tightness alone does not imply uniform translation continuity or a nonzero local autocorrelation limit",
        "rows": rows,
        "identity": "A_(q_a)(t)=A_q(a*t)",
        "norms_preserved": norms_ok,
        "central_concentration_observed": concentration_ok,
        "fixed_nonzero_lag_collapses": fixed_lag_collapse,
        "uniform_translation_continuity_fails": translation_failure,
        "status": "FIRED" if fired else "MISSED",
        "code": "EDGE_TIGHTNESS_ALONE_KILLED" if fired else "SCALE_PLANT_MISSED",
    }


def oscillator_plant() -> dict:
    betas = [1.0, 2.0, 4.0, 8.0, 16.0]
    # A0(t)=exp(-t^2), phi(t)=exp(-t^2).  The exact pairing is the
    # Fourier transform of exp(-2t^2) at beta.
    pairings = [math.sqrt(math.pi / 2.0) * math.exp(-(b * b) / 8.0) for b in betas]
    envelope_ratio = 1.0
    fired = pairings[-1] / pairings[0] < 1e-12 and envelope_ratio <= 1.0
    return {
        "id": "P3_OSCILLATOR",
        "formula": "A_beta(t)=A0(t)*cos(beta*t), A0(t)=exp(-t^2)",
        "target": "uniform autocorrelation tails alone do not prevent frequency escape or the zero local-distribution limit",
        "betas": betas,
        "test_function": "phi(t)=exp(-t^2)",
        "exact_pairings": pairings,
        "last_over_first_pairing": pairings[-1] / pairings[0],
        "uniform_envelope_ratio": envelope_ratio,
        "positive_definite_certificate": "half-sum of the two beta-shifts of the positive Gaussian spectral measure",
        "status": "FIRED" if fired else "MISSED",
        "code": "UNIFORM_TAIL_ALONE_KILLED" if fired else "OSCILLATOR_PLANT_MISSED",
    }


def main() -> None:
    x = np.linspace(-12.0, 12.0, 240001)
    q = raw_bump(x)
    q /= math.sqrt(integrate(q**2, x))
    plants = [shift_plant(x, q), scale_plant(x, q), oscillator_plant()]
    all_live = all(p["status"] == "FIRED" for p in plants)
    payload = {
        "schema": "soft_l2_round13_source_compactness_plants_v1",
        "role": "VALIDATORS_FOR_OPTIONAL_SOURCE_COMPACTNESS_LEAF",
        "plants": plants,
        "all_plants_live": all_live,
        "output_code": (
            "SOFT_L2_SOURCE_COMPACTNESS_PLANTS_ALL_LIVE"
            if all_live
            else "SOFT_L2_SOURCE_COMPACTNESS_PLANT_MISS"
        ),
        "l2_2_evidence": False,
        "RH": False,
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(payload["output_code"])


if __name__ == "__main__":
    main()
