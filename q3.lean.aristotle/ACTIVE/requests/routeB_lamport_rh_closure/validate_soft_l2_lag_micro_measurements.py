#!/usr/bin/env python3
"""Fail-closed validator for Round 11 materialization and the 12/14 lag ledgers."""

from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
VERDICT = HERE / "SOFT_L2_PRO_VERDICT_ROUND11_PARITY_2026-07-13.md"
MANIFEST = HERE / "ROUTE_B_DATA_MANIFEST.md"
REPORT = HERE / "SOFT_L2_LAG_LEDGER_12_14_120_REPORT_2026-07-13.md"
BUS = HERE.parent / "routeB_twolevel_spectral_ladder" / "bus"
VERDICT_SHA256 = "0085deb371e37dd319a850c66db4c2d7ecf9702af61d0ad68879c9d77ad959a9"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_cell(m: int) -> None:
    json_path = HERE / f"SOFT_L2_LAG_LEDGER_{m}_120.json"
    csv_path = HERE / f"SOFT_L2_LAG_LEDGER_{m}_120.csv"
    data = json.loads(json_path.read_text(encoding="utf-8"))
    rows = data["rows"]
    typing = data["source_typing"]
    prediction = data["prediction"]

    require(data["cell"]["lambda_sq"] == m and data["cell"]["N"] == 120,
            f"SOFT_L2_MICRO_WRONG_CELL:{m}")
    require(len(rows) == 13, f"SOFT_L2_MICRO_LAG_GRID_INCOMPLETE:{m}")
    require(typing["packet_role"] == "portable_k1_mu1_diagnostic_proxy",
            f"SOFT_L2_MICRO_SOURCE_TYPE_MISMATCH:{m}")
    require(not typing["full_ground_eigenvector_persisted"],
            f"SOFT_L2_MICRO_GROUND_CERTIFICATE_SMUGGLED:{m}")
    require(typing["mu_source"] == f"lambda_sq_{m}_N_120.json:mu1",
            f"SOFT_L2_MICRO_MU_SOURCE_MISMATCH:{m}")
    require(prediction["outer_opposite_real_sign"],
            f"SOFT_L2_MICRO_SIGN_PREDICTION_FAILED:{m}")
    require(float(prediction["max_outer_abs_residual_over_component_sum"]) < 1e-4,
            f"SOFT_L2_MICRO_RESIDUAL_PREDICTION_FAILED:{m}")
    require(prediction["outcome"] == "SUPPORTED_OUTER_WINDOW_REMAINDER_ANTICANCELLATION",
            f"SOFT_L2_MICRO_OUTCOME_MISMATCH:{m}")
    require(not data["claims"]["smallness"] and not data["claims"]["RH"],
            f"SOFT_L2_MICRO_OVERCLAIM:{m}")
    require(data["t0_matrix_anchor"]["status"] ==
            "NO_PERSISTED_FULL_GROUND_MATRIX_ANCHOR_FOR_THIS_CELL",
            f"SOFT_L2_MICRO_T0_ANCHOR_SMUGGLED:{m}")

    outer = [r for r in rows if abs(r["t_over_L"]) >= 0.5]
    require(len(outer) == 8, f"SOFT_L2_MICRO_OUTER_GRID_INCOMPLETE:{m}")
    require(all(float(r["window_D_sum"]["re"]) < 0 <
                float(r["remainder_Galerkin_sector_Arch_correction"]["re"])
                for r in outer), f"SOFT_L2_MICRO_ANTICANCELLATION_NOT_LIVE:{m}")
    endpoints = [r for r in rows if abs(r["t_over_L"]) == 1.0]
    require(len(endpoints) == 2 and all(float(r["abs_residual"]) < 1e-50 for r in endpoints),
            f"SOFT_L2_MICRO_ENDPOINT_RESIDUAL_NOT_NEAR_ZERO:{m}")

    with csv_path.open(newline="", encoding="utf-8") as handle:
        require(len(list(csv.DictReader(handle))) == 13,
                f"SOFT_L2_MICRO_CSV_GRID_INCOMPLETE:{m}")


def main() -> None:
    manifest = MANIFEST.read_text(encoding="utf-8")
    report = REPORT.read_text(encoding="utf-8")
    require(sha256(VERDICT) == VERDICT_SHA256,
            "SOFT_L2_ROUND11_VERBATIM_HASH_MISMATCH")
    require(VERDICT.name in manifest and VERDICT_SHA256 in manifest,
            "SOFT_L2_ROUND11_MANIFEST_REGISTRATION_MISSING")

    registered_data = {
        "SOFT_L2_LAG_LEDGER_12_120.csv": "2738ecfd4f101a6f9250ba57de56b1b5b7142511983beb0d47269478a3627c4c",
        "SOFT_L2_LAG_LEDGER_12_120.json": "66ca8eb9cb8b8489dbc084d1889a6d599e8e6864ea4fe7d24e3e984a4a434c0e",
        "SOFT_L2_LAG_LEDGER_14_120.csv": "02c259a528fff60e18859ff8044822b6fd544b05acd18eac6129a427d2c63bb6",
        "SOFT_L2_LAG_LEDGER_14_120.json": "acd652b8bbd58a5d63a610484937e46d29161ba6a6781d30a8ded7951dcde820",
    }
    for name, expected_hash in registered_data.items():
        require(sha256(HERE / name) == expected_hash,
                f"SOFT_L2_MICRO_DATA_HASH_MISMATCH:{name}")
        require(name in manifest and expected_hash in manifest,
                f"SOFT_L2_MICRO_MANIFEST_REGISTRATION_MISSING:{name}")

    for m in (12, 14):
        validate_cell(m)

    for token in [
        "SOFT_L2_LAG_MICRO_LEDGERS_COMPLETE",
        "REGISTERED_PREDICTION_SUPPORTED_12_120_14_120",
        "portable_k1 / mu1 diagnostic proxy",
        "Bus 010 was not created",
    ]:
        require(token in report, f"SOFT_L2_MICRO_REPORT_TOKEN_MISSING:{token}")

    require(not list(BUS.glob("010_*.goal.md")), "SOFT_L2_MICRO_BUS_010_SMUGGLED")

    print("SOFT_L2_ROUND11_PARITY_VERBATIM_MATERIALIZED")
    print("SOFT_L2_LAG_MICRO_LEDGERS_COMPLETE")
    print("REGISTERED_PREDICTION_SUPPORTED_12_120_14_120")
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
