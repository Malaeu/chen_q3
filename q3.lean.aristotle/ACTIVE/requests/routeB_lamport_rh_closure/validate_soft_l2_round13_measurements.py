#!/usr/bin/env python3
"""Fail-closed validator for the SOFT_L2 Round-13 diagnostics."""

from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    verdict = HERE / "SOFT_L2_PRO_VERDICT_ROUND13_2026-07-13.md"
    sign_json_path = HERE / "SOFT_L2_GROUND_SIGN_PROBE.json"
    sign_csv_path = HERE / "SOFT_L2_GROUND_SIGN_PROBE.csv"
    tail_json_path = HERE / "SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120.json"
    tail_csv_path = HERE / "SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120.csv"
    tail_png_path = HERE / "SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120_LOG.png"

    require(verdict.is_file(), "ROUND13_VERDICT_NOT_MATERIALIZED")
    require(
        sha256(verdict)
        == "71f4e1276c774c5a857afea2d511f0c5e45cc31710f4689666b417f75b69b9dd",
        "ROUND13_VERBATIM_HASH_MISMATCH",
    )

    sign = json.loads(sign_json_path.read_text())
    sign_csv = list(csv.DictReader(sign_csv_path.open()))
    require(sign["schema"] == "soft_l2_ground_sign_probe_v1", "SIGN_SCHEMA_MISMATCH")
    require(len(sign["rows"]) == 7 == len(sign_csv), "SIGN_ALL_CELLS_MISSING")
    require(
        all(r["grid_size"] == 4096 for r in sign["rows"]),
        "SIGN_GRID_NOT_4096",
    )
    require(
        all(r["interior_depth_over_L"] == 0.05 for r in sign["rows"]),
        "SIGN_INTERIOR_DEPTH_MISMATCH",
    )
    require(
        all(r["ratio_threshold"] == 1e-6 for r in sign["rows"]),
        "SIGN_RATIO_THRESHOLD_MISMATCH",
    )
    require(
        all(r["verdict"] in {"SIGN_CONSTANT", "SIGN_CHANGING"} for r in sign["rows"]),
        "SIGN_VERDICT_VOCABULARY_MISMATCH",
    )
    require(
        all(r["verdict"] == "SIGN_CONSTANT" for r in sign["rows"]),
        "SIGN_CONSTANT_REPLAY_MISMATCH",
    )
    require(
        sum(r["role"] == "finite_ground_xi1" for r in sign["rows"]) == 1,
        "GROUND_TRIAL_PROVENANCE_COLLAPSED",
    )
    require(
        sign["aggregate"]["trial_rows_are_ground_evidence"] is False,
        "TRIAL_ROWS_MISLABELLED_AS_GROUND",
    )

    tail = json.loads(tail_json_path.read_text())
    tail_csv = list(csv.DictReader(tail_csv_path.open()))
    require(
        tail["schema"] == "soft_l2_autocorrelation_tail_check_v1",
        "TAIL_SCHEMA_MISMATCH",
    )
    require(tail["cell"] == {"lambda_sq": 13, "N": 120, "L": tail["cell"]["L"]}, "TAIL_CELL_MISMATCH")
    require(len(tail["rows"]) == 4 == len(tail_csv), "TAIL_GRID_MISSING")
    require(
        [r["t_over_L"] for r in tail["rows"]] == [0.5, 2 / 3, 5 / 6, 1.0],
        "TAIL_LAG_GRID_MISMATCH",
    )
    require(tail["verdict"] == "TAIL_DOMINATED", "TAIL_VERDICT_MISMATCH")
    require(
        tail["round13_role"]
        == "OPTIONAL_SOURCE_COMPACTNESS_SPATIAL_TIGHTNESS_DIAGNOSTIC",
        "TAIL_ROUND13_ROLE_MISMATCH",
    )
    require(tail["l2_2_input"] is False, "TAIL_SMUGGLED_INTO_L2_2")
    require(
        tail["supplies_uniform_translation_continuity"] is False,
        "TAIL_FALSE_TRANSLATION_CONTINUITY_CLAIM",
    )
    require(
        tail["map_recode"] == "FALSE_WALL_REMOVED_ROUND13",
        "TAIL_FALSE_WALL_RECODE_MISSING",
    )
    require(all(r["passed"] for r in tail["rows"]), "TAIL_POINTWISE_VIOLATION")
    require(
        float(tail["minimum_margin_orders"]) > 4.8,
        "TAIL_MARGIN_TOO_SMALL",
    )
    endpoint = tail["rows"][-1]
    require(
        endpoint["endpoint_anchor"] == "EXACT_SUPPORT_ENDPOINT_A_OF_L_EQ_0",
        "TAIL_ENDPOINT_ANCHOR_MISSING",
    )
    require(
        float(endpoint["abs_A_raw"]) < 1e-70
        and float(endpoint["abs_A_for_judge"]) == 0.0,
        "TAIL_ENDPOINT_NUMERICAL_RESIDUE_NOT_GUARDED",
    )
    require(tail_png_path.stat().st_size > 1000, "TAIL_OVERLAY_PLOT_MISSING")

    print("SOFT_L2_ROUND13_MEASUREMENTS_VALIDATED")


if __name__ == "__main__":
    main()
