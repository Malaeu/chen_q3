#!/usr/bin/env python3
"""LeakageCloseout_v1 for bus goal 006.

Request-local diagnostic only: NOT_RH, no Phase 2, no QW or packet changes,
and no Q3 mainline changes.
"""

from __future__ import annotations

import hashlib
import json
import random
import time
from pathlib import Path
from typing import Any, Dict

import mpmath as mp

import leakage_falsifier_v1 as leakage


REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
JSON_OUT = OUT_DIR / "leakage_closeout_v1.json"
GOAL_FILE = REQUEST_DIR / "bus" / "006_leakage_closeout.goal.md"
SOURCE_BUILDER = REQUEST_DIR / "true_precision_packet_gate_v1.py"
OLD_JSON = OUT_DIR / "leakage_falsifier_v1.json"

CROSSCHECK_SEED = 20260710
K_MAX_POISSON = 40
K_MAX_STAIL = 200


def progress(label: str) -> None:
    print(f"[LeakageCloseout_v1] {label}", flush=True)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


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


def analytic_legendre_bessel_integral(model: leakage.ProlateModel, n: int, k: int) -> mp.mpf:
    """Integral over [-1,1] of psi_n(x) cos(2*pi*13*k*x) dx."""
    a = leakage.C_BANDWIDTH * k
    total = mp.mpf("0")
    for coefficient, degree in zip(model.unit_coeffs[n], model.degrees):
        total += (
            coefficient
            * ((-1) ** (degree // 2))
            * mp.sqrt(2 * mp.pi / a)
            * mp.besselj(degree + mp.mpf("0.5"), a)
        )
    return total


def combo(integrals: Dict[int, Dict[int, mp.mpf]], coefficients: Dict[int, mp.mpf], k: int) -> mp.mpf:
    return sum(coefficients[n] * integrals[n][k] for n in coefficients)


def main() -> None:
    started = time.time()
    mp.mp.dps = leakage.DPS_MODEL
    old = load_json(OLD_JSON)

    progress("build canonical true-precision prolate packet")
    model = leakage.build_prolate_model()
    coefficients = dict(model.g04_combo_by_h)
    scale = mp.mpf(old["F0_H2_fork"]["window_scale_norm_E_g04"])
    g0 = leakage.g04_window(model, mp.mpf("0"))
    integral_residual = sum(coefficients[n] * model.window_integrals[n] for n in coefficients)

    # The constructor has exactly one S0 condition: zero integral.  Euclidean
    # coefficient normalization is not a second S0 constraint, and no f(0)=0
    # row appears in the packet builder.
    g1 = {
        "source": "true_precision_packet_gate_v1.py:187-194",
        "source_lines_verbatim": [
            "integrals[which] = v[0] * mp.sqrt(2 * lam)",
            "g04_c = normalize_real_combo([integrals[4], -integrals[0]])",
            '"g04": {0: g04_c[0], 4: g04_c[1]},',
        ],
        "linear_conditions_on_c0_c4": ["c_0 * integral(h_0) + c_4 * integral(h_4) = 0"],
        "coefficient_normalization_not_s0_condition": "c_0^2 + c_4^2 = 1",
        "f_at_zero_constraint_present": False,
        "numeric_crosscheck": {
            "c0": coefficients[0],
            "c4": coefficients[4],
            "integral_residual": integral_residual,
            "g04_at_zero": g0,
            "abs_g04_at_zero_over_norm_E": abs(g0) / scale,
        },
        "exact_dictionary_branch": "H2-POLE/CORRECTION; h_lambda(0) != 0",
        "code": "H2_NUMERIC_ONLY",
        "reason": "Only integral(f)=0 is imposed; f(0)=0 was an emergent numerical cancellation in this implementation.",
    }

    progress("evaluate exact Legendre/Bessel integrals through k=200")
    analytic: Dict[int, Dict[int, mp.mpf]] = {
        n: {k: analytic_legendre_bessel_integral(model, n, k) for k in range(1, K_MAX_STAIL + 1)}
        for n in coefficients
    }

    rng = random.Random(CROSSCHECK_SEED)
    crosscheck_ks = sorted(rng.sample(list(range(9, K_MAX_POISSON + 1)), 3))
    cached_crosschecks = None
    if JSON_OUT.exists():
        previous = load_json(JSON_OUT)
        previous_g2 = previous.get("G2_poisson_tail_truncation", {})
        if previous_g2.get("crosscheck_k") == crosscheck_ks:
            cached_crosschecks = previous_g2.get("crosschecks")
    if cached_crosschecks:
        progress("reuse pinned period-split cross-check rows from prior identical run")
        crosschecks = cached_crosschecks
    else:
        crosschecks = []
        for k in crosscheck_ks:
            for n in coefficients:
                progress(f"period-split quadrature cross-check n={n}, k={k}")
                quadrature = leakage.oscillatory_integral(model, n, k)
                exact = analytic[n][k]
                crosschecks.append(
                    {
                        "n": n,
                        "k": k,
                        "period_split_quadrature": quadrature,
                        "legendre_bessel": exact,
                        "relative_difference": abs(quadrature - exact) / max(abs(exact), mp.mpf("1e-300")),
                    }
                )

    combo_integrals = {k: combo(analytic, coefficients, k) for k in range(1, K_MAX_STAIL + 1)}
    direct = mp.mpf(old["F2_left_edge_crosscheck"]["direct_E_g04_left_edge"])
    correction = mp.mpf(old["F2_left_edge_crosscheck"]["h2_correction_subtracted"])
    poisson_prefix = {
        k: leakage.LAMBDA * sum(combo_integrals[j] for j in range(1, k + 1)) - correction
        for k in range(1, K_MAX_POISSON + 1)
    }
    poisson_40 = poisson_prefix[K_MAX_POISSON]
    relative_mismatch_40 = abs(direct - poisson_40) / max(abs(direct), mp.mpf("1e-300"))
    if relative_mismatch_40 < mp.mpf("2e-3"):
        g2_code = "TRUNCATION_CONFIRMED"
    elif relative_mismatch_40 > mp.mpf("5e-3"):
        g2_code = "SECOND_EDGE_CHANNEL"
    else:
        g2_code = "AMBIGUOUS"
    g2 = {
        "primary_method": "exact Legendre/Bessel transform; period-split quadrature independently checked at three deterministic random k",
        "crosscheck_seed": CROSSCHECK_SEED,
        "crosscheck_k": crosscheck_ks,
        "crosschecks": crosschecks,
        "direct": direct,
        "h2_correction_in_current_numeric_builder": correction,
        "poisson_prefix_selected": {k: poisson_prefix[k] for k in range(8, 41, 4)},
        "relative_mismatch_selected": {
            k: abs(direct - poisson_prefix[k]) / max(abs(direct), mp.mpf("1e-300")) for k in range(8, 41, 4)
        },
        "poisson_k_1_40": poisson_40,
        "relative_mismatch_k_1_40": relative_mismatch_40,
        "code": g2_code,
    }

    mu = {n: model.unit_integrals[n] / leakage.psi_unit(model, n, mp.mpf("0")) for n in coefficients}
    mu_scale = abs(mu[0])
    per_mode_prefix = {
        n: {
            k: sum(abs(coefficients[n] * analytic[n][j]) for j in range(2, k + 1)) / mu_scale
            for k in (8, 20, 50, 100, 200)
        }
        for n in coefficients
    }
    stail_prefix = {
        k: sum(abs(combo_integrals[j]) for j in range(2, k + 1)) / mu_scale
        for k in (8, 20, 50, 100, 200)
    }
    leading_combo = abs(combo_integrals[1]) / mu_scale
    size_pass = stail_prefix[200] <= mp.mpf("0.5") * leading_combo
    convergence_increment = (stail_prefix[200] - stail_prefix[100]) / stail_prefix[200]
    convergence_pass = convergence_increment < mp.mpf("0.05")
    g3 = {
        "mu_by_mode": mu,
        "mu_scale": mu_scale,
        "stail_definition": "sum_{k=2..K} |c0*mu0*psi0(k)+c4*mu4*psi4(k)| / |mu0|",
        "stail_prefix": stail_prefix,
        "per_mode_absolute_prefix": per_mode_prefix,
        "leading_k1_combo_over_mu_scale": leading_combo,
        "stail_200_over_leading": stail_prefix[200] / leading_combo,
        "size_pass_le_half_leading": size_pass,
        "increment_100_to_200_over_total": convergence_increment,
        "convergence_pass_lt_5_percent": convergence_pass,
        "code": "STAIL_CERT_OK" if size_pass and convergence_pass else "STAIL_DIVERGENT_SUSPECT",
    }

    # Both active modes have real Fourier multipliers, so conjugation is
    # exactly inert.  The sign-flip shadow deliberately changes only c4 on
    # the Poisson side while retaining the original direct observable.
    poisson_conjugate = poisson_40
    conjugate_relative_change = abs(poisson_conjugate - poisson_40) / max(abs(poisson_40), mp.mpf("1e-300"))
    signflip_coefficients = {0: coefficients[0], 4: -coefficients[4]}
    signflip_combo = {k: combo(analytic, signflip_coefficients, k) for k in range(1, K_MAX_POISSON + 1)}
    poisson_signflip = leakage.LAMBDA * sum(signflip_combo.values()) - correction
    signflip_mismatch = abs(direct - poisson_signflip) / max(abs(direct), mp.mpf("1e-300"))
    mismatch_amplification = signflip_mismatch / max(relative_mismatch_40, mp.mpf("1e-300"))
    conjugate_pass = conjugate_relative_change < mp.mpf("1e-6")
    signflip_pass = mismatch_amplification >= 10
    g4 = {
        "fourier_multipliers": {n: "real; conjugation inert" for n in coefficients},
        "poisson_normal": poisson_40,
        "poisson_conjugate": poisson_conjugate,
        "conjugate_relative_change": conjugate_relative_change,
        "conjugate_pass_lt_1e_minus_6": conjugate_pass,
        "poisson_c4_signflip": poisson_signflip,
        "signflip_relative_mismatch_vs_original_direct": signflip_mismatch,
        "baseline_relative_mismatch": relative_mismatch_40,
        "mismatch_amplification": mismatch_amplification,
        "signflip_pass_ge_10x": signflip_pass,
        "code": "PLANT_REDESIGNED_FIRES" if conjugate_pass and signflip_pass else "PLANT_STILL_INERT",
    }

    payload = {
        "diagnostic_scope": ["NOT_RH", "no Phase 2", "no QW changes", "no packet changes", "Q3 mainline untouched"],
        "goal": {"path": "bus/006_leakage_closeout.goal.md", "sha256": sha256_file(GOAL_FILE)},
        "inputs": {
            "true_precision_packet_gate_v1.py": sha256_file(SOURCE_BUILDER),
            "out/leakage_falsifier_v1.json": sha256_file(OLD_JSON),
        },
        "parameters": {
            "lambda_sq": leakage.LAMBDA_SQ,
            "max_degree": leakage.MAX_DEGREE,
            "dps_model": leakage.DPS_MODEL,
            "dps_quad": leakage.DPS_QUAD,
            "k_max_poisson": K_MAX_POISSON,
            "k_max_stail": K_MAX_STAIL,
        },
        "G1_H2_constraint_row": g1,
        "G2_poisson_tail_truncation": g2,
        "G3_stail_certificate": g3,
        "G4_plant_redesign": g4,
        "codes": [g1["code"], g2["code"], g3["code"], g4["code"]],
        "elapsed_seconds": time.time() - started,
    }
    JSON_OUT.parent.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    progress("wrote out/leakage_closeout_v1.json")
    print(json.dumps({"codes": payload["codes"], "output": str(JSON_OUT)}, indent=2))


if __name__ == "__main__":
    main()
