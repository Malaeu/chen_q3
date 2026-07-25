#!/usr/bin/env python3
"""Fail-closed validation of the H2a cert.pilot artifact."""

from __future__ import annotations

import json
import math
from pathlib import Path


HERE = Path(__file__).resolve().parent
RESULT = HERE / "H2A_CERT_SPLIT_PILOT.json"
REPORT = HERE / "H2A_CERT_SPLIT_PILOT_REPORT_2026-07-25.md"
BUS = HERE.parent / "routeB_twolevel_spectral_ladder" / "bus"
EXPECTED_CELLS = [(m, n) for m in (12, 13, 14) for n in (2, 3, 4)]


def require(condition: bool, code: str) -> None:
    if not condition:
        raise RuntimeError(code)


def close(a: float, b: float, tolerance: float = 2e-15) -> bool:
    return abs(a - b) <= tolerance * max(1.0, abs(a), abs(b))


def main() -> None:
    payload = json.loads(RESULT.read_text(encoding="utf-8"))
    report = REPORT.read_text(encoding="utf-8")
    require(
        payload["schema"] == "route_b_h2a_cert_split_pilot.v1",
        "H2A_CERT_PILOT_SCHEMA_DRIFT",
    )
    require(
        payload["arithmetic"] == "IEEE754_BINARY64",
        "H2A_CERT_PILOT_NOT_BINARY64",
    )
    require(
        [tuple(row) for row in payload["registered_cells"]] == EXPECTED_CELLS,
        "H2A_CERT_PILOT_CELL_DRIFT",
    )
    require(
        payload["cert_split"]["cert.pilot"] == "EXECUTED_BINARY64_DIAGNOSTIC",
        "H2A_CERT_PILOT_NOT_EXECUTED",
    )
    require(
        payload["cert_split"]["cert.exact"] == "OPEN"
        and payload["cert_split"]["exact_leaf"] == "ExactSectorOrdering",
        "H2A_CERT_EXACT_FALSE_PROMOTION",
    )
    require(
        payload["cert_split"]["stop"] == "H2A_EXACT_SECTOR_ORDERING_MISSING",
        "H2A_CERT_EXACT_STOP_DRIFT",
    )
    require(
        payload["state_sha256_before"] == payload["state_sha256_after"],
        "H2A_CERT_PILOT_STATE_MUTATION",
    )
    require(payload["bus_010_absent"] and not list(BUS.glob("010_*")), "BUS_010_PRESENT")

    rows = payload["cells"]
    require(len(rows) == len(EXPECTED_CELLS), "H2A_CERT_PILOT_ROW_COUNT")
    for row, cell in zip(rows, EXPECTED_CELLS):
        require((row["m"], row["N"]) == cell, "H2A_CERT_PILOT_ROW_ORDER")
        lambda_1 = row["lambda_1"]
        lambda_2 = row["lambda_2"]
        require(
            close(row["beta"], (lambda_1 + lambda_2) / 2),
            "H2A_CERT_PILOT_BETA_FORMULA",
        )
        require(
            close(row["tau"], lambda_2 - lambda_1),
            "H2A_CERT_PILOT_TAU_FORMULA",
        )
        require(row["numeric_exact_sector_ordering"], "H2A_CERT_PILOT_ORDERING_FAIL")
        require(row["tau"] > row["roundoff_guard"], "H2A_CERT_PILOT_GAP_AT_ROUNDOFF")
        require(
            row["min_eig_cert"] > row["roundoff_guard"],
            "H2A_CERT_PILOT_PSD_MARGIN_FAIL",
        )
        require(
            row["tau_zero_min_eig_cert"] < -row["roundoff_guard"],
            "H2A_CERT_PILOT_TAU_ZERO_PLANT_INERT",
        )
        require(row["psd_achievable"], "H2A_CERT_PILOT_CELL_FAIL")
        require(math.isfinite(row["min_eig_cert"]), "H2A_CERT_PILOT_NONFINITE")

    require(
        payload["verdict"] == "PSD_ACHIEVABLE_ON_REGISTERED_SMALL_GRID",
        "H2A_CERT_PILOT_VERDICT_FAIL",
    )
    for marker in (
        "CERT_PILOT_EXECUTED / CERT_EXACT_OPEN / NOT_RH",
        "ExactSectorOrdering",
        "H2A_EXACT_SECTOR_ORDERING_MISSING",
        "PSD_ACHIEVABLE_ON_REGISTERED_SMALL_GRID",
    ):
        require(marker in report, "H2A_CERT_PILOT_REPORT_MARKER_MISSING")
    print("H2A_CERT_SPLIT_PILOT_VALIDATED")


if __name__ == "__main__":
    main()
