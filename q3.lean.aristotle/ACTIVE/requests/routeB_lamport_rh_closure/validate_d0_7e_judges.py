#!/usr/bin/env python3
"""Fail-closed reproducibility check for the persisted-vector T1 judges."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path


REQUEST_DIR = Path(__file__).resolve().parent
CERT = REQUEST_DIR / "D0_7E_JUDGE_CERTIFICATES.json"
NOTE = REQUEST_DIR / "D0_7E_T1_JUDGE_NOTE.md"
REPRODUCER = REQUEST_DIR / "d0_7e_t1_persisted_judges.py"
BUS = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    locked = json.loads(CERT.read_text(encoding="utf-8"))
    reproduced = json.loads(
        subprocess.check_output([sys.executable, str(REPRODUCER)], text=True)
    )
    require(locked == reproduced, "D0_7E_T1_REPRODUCTION_DRIFT")
    require(
        locked["overall_status"]
        == "PARTIAL_BLOCKED_MISSING_LAMBDA17_PERSISTED_VECTOR",
        "D0_7E_T1_MISSING_VECTOR_OVERCLAIM",
    )
    judges = locked["judges"]
    require(judges["J2_N_stability_13_90_vs_120"]["pass"], "D0_7E_T1_N_STABILITY_FAIL")
    require(
        judges["J3_two_way_evaluation"]["all_machine_zero_pass"],
        "D0_7E_T1_TWO_WAY_EVALUATION_FAIL",
    )
    require(
        judges["J4_central_zero_plant"]["status"]
        == "B_CENTRAL_ZERO_CELL_FIRES",
        "PLANT_INERT",
    )
    require(
        judges["P3_abs_bDet_sqrt_lambda_factor3"]["score_status"]
        == "NOT_FULLY_SCORED_LAMBDA17_MISSING",
        "D0_7E_T1_P3_OVERCLAIM",
    )
    require(not any(BUS.glob("010_*.goal.md")), "D0_7E_T1_BUS_010_CREATED")

    combined = "\n".join(
        path.read_text(encoding="utf-8") for path in (CERT, NOTE, REPRODUCER)
    )
    forbidden = (
        r"\balpha\s*:=",
        r"\bDeltaE\s*:=",
        r"\bWPrime\s*:=",
        r"\bkappa\s*:?=",
        r"N\(lambda\)\s*:?=",
        r"\bfilter\s*:=",
    )
    for pattern in forbidden:
        require(re.search(pattern, combined) is None, f"D0_7E_T1_FORBIDDEN_MINT:{pattern}")

    print(
        json.dumps(
            {
                "task": "T1_PRE_REGISTERED_BDET_JUDGES",
                "verdict": locked["overall_status"],
                "available_cells": [[13, 90], [13, 120], [14, 120]],
                "missing_cell": [17, 120],
                "N_stability": "PASS",
                "two_way_evaluation": "PASS_AVAILABLE_CELLS",
                "plant": "B_CENTRAL_ZERO_CELL_FIRES",
                "bus_010": "NOT_CREATED",
                "rh": "NOT_RH",
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
