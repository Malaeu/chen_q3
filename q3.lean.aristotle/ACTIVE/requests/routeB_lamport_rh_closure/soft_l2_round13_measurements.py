#!/usr/bin/env python3
"""Round-13 SOFT_L2 sign and autocorrelation-tail diagnostics.

This is numerical evidence only.  Trial packets remain trial packets, and the
single persisted finite ground packet is never generalized to the other cells.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

import soft_l2_projection_measurements as base


HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent.parent

SIGN_CSV = HERE / "SOFT_L2_GROUND_SIGN_PROBE.csv"
SIGN_JSON = HERE / "SOFT_L2_GROUND_SIGN_PROBE.json"
TAIL_CSV = HERE / "SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120.csv"
TAIL_JSON = HERE / "SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120.json"
TAIL_PNG = HERE / "SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120_LOG.png"

GRID_SIZE = 4096
INTERIOR_DEPTH_OVER_L = 0.05
SIGN_RATIO_THRESHOLD = 1e-6


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    return str(path.resolve().relative_to(REPO))


def sign_probe(packets: list[base.Packet]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for packet in packets:
        ns = np.asarray(sorted(packet.coeff), dtype=np.int64)
        coeff = np.asarray([complex(packet.coeff[int(n)]) for n in ns])
        L = float(packet.L)
        grid = np.linspace(
            INTERIOR_DEPTH_OVER_L * L,
            (1.0 - INTERIOR_DEPTH_OVER_L) * L,
            GRID_SIZE,
            endpoint=True,
        )
        values = (
            np.exp(2j * np.pi * np.outer(grid / L, ns)) @ coeff / np.sqrt(L)
        )

        # A global phase is immaterial.  Orient the largest sampled value to
        # the positive real axis before testing for a robust opposite lobe.
        anchor_index = int(np.argmax(np.abs(values)))
        anchor = values[anchor_index]
        gauge = np.exp(-1j * np.angle(anchor))
        oriented = gauge * values
        real = oriented.real
        imag = oriented.imag
        positive_max = float(np.max(real))
        signed_min = float(np.min(real))
        signed_min_over_max = signed_min / positive_max
        negative_to_positive_ratio = max(0.0, -signed_min) / positive_max
        sample_threshold = SIGN_RATIO_THRESHOLD * positive_max
        significant_positive = int(np.count_nonzero(real > sample_threshold))
        significant_negative = int(np.count_nonzero(real < -sample_threshold))
        verdict = (
            "SIGN_CHANGING"
            if negative_to_positive_ratio > SIGN_RATIO_THRESHOLD
            else "SIGN_CONSTANT"
        )
        max_imag_over_max_abs = float(
            np.max(np.abs(imag)) / np.max(np.abs(oriented))
        )
        rows.append(
            {
                "label": packet.label,
                "role": packet.role,
                "lambda_sq": packet.lambda_sq,
                "N": packet.N,
                "source": relative(packet.source),
                "grid_size": GRID_SIZE,
                "interior_depth_over_L": INTERIOR_DEPTH_OVER_L,
                "gauge_anchor_index": anchor_index,
                "gauge_anchor_u_over_L": float(grid[anchor_index] / L),
                "positive_max": positive_max,
                "signed_min": signed_min,
                "signed_min_over_max": signed_min_over_max,
                "negative_to_positive_extremum_ratio": negative_to_positive_ratio,
                "ratio_threshold": SIGN_RATIO_THRESHOLD,
                "significant_positive_samples": significant_positive,
                "significant_negative_samples": significant_negative,
                "max_imag_over_max_abs": max_imag_over_max_abs,
                "verdict": verdict,
            }
        )

    with SIGN_CSV.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    payload = {
        "schema": "soft_l2_ground_sign_probe_v1",
        "definition": (
            "on 4096 equally spaced samples in [0.05L,0.95L], orient the "
            "largest |q| sample to the positive real axis and compare the "
            "opposite-sign extremum to the positive maximum"
        ),
        "judge": (
            "SIGN_CHANGING iff max(0,-min Re(q))/max Re(q) > 1e-6; "
            "otherwise SIGN_CONSTANT"
        ),
        "rows": rows,
        "aggregate": {
            "all_rows": "SIGN_CONSTANT"
            if all(r["verdict"] == "SIGN_CONSTANT" for r in rows)
            else "SIGN_CHANGING",
            "finite_ground_rows": [
                r["verdict"] for r in rows if r["role"] == "finite_ground_xi1"
            ],
            "trial_rows_are_ground_evidence": False,
        },
        "guards": {
            "grid_result_is_not_a_positivity_theorem": True,
            "float64_rows_are_diagnostic_only": True,
            "only_persisted_full_ground_cell": "ground_xi1_m13_N120",
            "RH": False,
        },
    }
    SIGN_JSON.write_text(json.dumps(payload, indent=2) + "\n")
    return payload


def complex_abs(record: dict[str, str]) -> mp.mpf:
    return abs(mp.mpc(mp.mpf(record["re"]), mp.mpf(record["im"])))


def tail_check(ground: base.Packet) -> dict[str, Any]:
    mp.mp.dps = 80
    ledger_path = HERE / "SOFT_L2_LAG_LEDGER_13_120.json"
    edge_path = HERE / "SOFT_L2_EDGE_MASS_PROFILE.json"
    ledger = json.loads(ledger_path.read_text())
    edge = json.loads(edge_path.read_text())
    corr = base.correlation_coefficients(ground)
    L = ground.L
    rows: list[dict[str, Any]] = []

    for source_row in ledger["rows"]:
        # The registered ledger grid is k/6.  Reconstruct that rational lag
        # exactly instead of inheriting the display truncation of the t field.
        lag_index = round(float(source_row["t_over_L"]) * 6)
        t = mp.mpf(lag_index) * L / 6
        if t < L / 2 - mp.mpf("1e-28"):
            continue
        if t > L + mp.mpf("1e-28"):
            continue
        delta = L - t
        if abs(delta) < mp.mpf("1e-28"):
            delta = mp.mpf("0")
        abs_a_raw = complex_abs(source_row["A"])

        if delta == 0:
            # Compact support gives A(L)=0 exactly.  The ledger's ~1e-81 value
            # is the working-precision residue of the closed-form evaluator.
            majorant = mp.mpf("0")
            abs_a_judge = mp.mpf("0")
            ratio = None
            margin_orders = None
            endpoint_anchor = "EXACT_SUPPORT_ENDPOINT_A_OF_L_EQ_0"
            passed = True
        else:
            mass = base.interval_mass(ground, corr, mp.mpf("0"), delta)
            mass += base.interval_mass(ground, corr, L - delta, L)
            majorant = mp.sqrt(max(mp.mpf("0"), mass))
            abs_a_judge = abs_a_raw
            ratio = majorant / abs_a_judge if abs_a_judge else mp.inf
            margin_orders = mp.log10(ratio) if ratio != mp.inf else mp.inf
            endpoint_anchor = "NOT_ENDPOINT"
            passed = abs_a_judge <= majorant

        rows.append(
            {
                "t_over_L": float(t / L),
                "t": mp.nstr(t, 35),
                "delta_over_L": float(delta / L),
                "delta": mp.nstr(delta, 35),
                "abs_A_raw": mp.nstr(abs_a_raw, 35),
                "abs_A_for_judge": mp.nstr(abs_a_judge, 35),
                "edge_majorant_eL": mp.nstr(majorant, 35),
                "majorant_over_abs_A": None
                if ratio is None
                else ("inf" if ratio == mp.inf else mp.nstr(ratio, 25)),
                "margin_orders_log10": None
                if margin_orders is None
                else (
                    "inf"
                    if margin_orders == mp.inf
                    else mp.nstr(margin_orders, 20)
                ),
                "endpoint_anchor": endpoint_anchor,
                "passed": passed,
            }
        )

    finite_margins = [
        mp.mpf(r["margin_orders_log10"])
        for r in rows
        if r["margin_orders_log10"] not in (None, "inf")
    ]
    verdict = "TAIL_DOMINATED" if all(r["passed"] for r in rows) else "TAIL_VIOLATION"
    minimum_margin = min(finite_margins)

    with TAIL_CSV.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    payload = {
        "schema": "soft_l2_autocorrelation_tail_check_v1",
        "cell": {"lambda_sq": 13, "N": 120, "L": mp.nstr(L, 40)},
        "source_packet": ground.label,
        "tail_grid": "positive ledger lags t/L in {1/2,2/3,5/6,1}; negative lags duplicate by Hermitian symmetry",
        "majorant": "|A(t)| <= e_L(L-t) for L/2 <= t <= L",
        "edge_profile_definition": edge["definition"],
        "edge_evaluation": "direct evaluation of the registered edge-profile formula at each ledger delta; no interpolation",
        "input_sha256": {
            "lag_ledger_13_120": sha256(ledger_path),
            "edge_profile": sha256(edge_path),
            "ground_packet": sha256(ground.source),
        },
        "rows": rows,
        "verdict": verdict,
        "round13_role": "OPTIONAL_SOURCE_COMPACTNESS_SPATIAL_TIGHTNESS_DIAGNOSTIC",
        "l2_2_input": False,
        "supplies_uniform_translation_continuity": False,
        "map_recode": "FALSE_WALL_REMOVED_ROUND13",
        "minimum_margin_orders": mp.nstr(minimum_margin, 20),
        "minimum_margin_location_t_over_L": next(
            r["t_over_L"]
            for r in rows
            if r["margin_orders_log10"] == mp.nstr(minimum_margin, 20)
        ),
        "guards": {
            "endpoint_uses_exact_compact_support_anchor": True,
            "raw_endpoint_residue_is_preserved": True,
            "finite_grid_is_not_an_asymptotic_theorem": True,
            "RH": False,
        },
    }
    TAIL_JSON.write_text(json.dumps(payload, indent=2) + "\n")

    plot_rows = [r for r in rows if r["endpoint_anchor"] == "NOT_ENDPOINT"]
    x = [r["t_over_L"] for r in plot_rows]
    y_a = [float(r["abs_A_raw"]) for r in plot_rows]
    y_e = [float(r["edge_majorant_eL"]) for r in plot_rows]
    plt.figure(figsize=(7.6, 5.2))
    plt.semilogy(x, y_a, "o-", linewidth=2, label=r"$|A(t)|$")
    plt.semilogy(x, y_e, "s-", linewidth=2, label=r"$e_L(L-t)$")
    plt.xlabel(r"$t/L$")
    plt.ylabel("magnitude (log scale)")
    plt.title("SOFT_L2 autocorrelation tail check (13,120)")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(TAIL_PNG, dpi=180)
    plt.close()
    return payload


def main() -> None:
    packets, ground, _ = base.packets()
    sign = sign_probe(packets)
    tail = tail_check(ground)
    print(sign["aggregate"]["all_rows"])
    print(tail["verdict"], tail["minimum_margin_orders"])


if __name__ == "__main__":
    main()
