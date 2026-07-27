#!/usr/bin/env python3
"""Fail-closed artifact validator for OffAxisGrowthProbe."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
LADDER = HERE.parent / "routeB_twolevel_spectral_ladder"
RESULT = HERE / "OFF_AXIS_GROWTH_PROBE.json"
MANIFEST = HERE / "ROUTE_B_DATA_MANIFEST.md"
STATE = HERE / "STATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def resolve(relative: str) -> Path:
    return REPO / relative


def main() -> None:
    result = json.loads(RESULT.read_text(encoding="utf-8"))
    require(result["schema"] == "route_b_off_axis_growth_probe.v1", "OFF_AXIS_SCHEMA_DRIFT")
    require(result["arithmetic"]["dtype"] == "float64/complex128", "OFF_AXIS_NOT_FLOAT64")
    require(result["arithmetic"]["dps_escalation"] is False, "OFF_AXIS_DPS_ESCALATION")
    require("lambda^(-i*z)" in result["object_lock"]["formula"], "OFF_AXIS_LAMBDA_PHASE_MISSING")
    require("gammaC" in result["object_lock"]["formula"], "OFF_AXIS_GAMMAC_MISSING")
    require(result["object_lock"]["ratio_cancellation"].startswith("bDet"), "OFF_AXIS_BDET_NOT_CANCELLED")

    cells = [(row["lambda_sq"], row["N"]) for row in result["cells"]]
    require(
        cells == [(13, 90), (13, 120), (14, 120), (53, 120), (101, 120)],
        "OFF_AXIS_CELL_SET_DRIFT",
    )
    for row in result["cells"]:
        require(row["bDet_float64_nonzero_check"] != 0, "OFF_AXIS_BDET_ZERO")
        for y in ("0.1", "0.2", "0.3", "0.4"):
            require(math.isfinite(row["ratios"][y]["R"]), "OFF_AXIS_NONFINITE_R")
            require(row["ratios"][y]["R"] > 0, "OFF_AXIS_NONPOSITIVE_R")

    fit = result["fit"]
    require(fit["cells"] == [[13, 120], [14, 120], [53, 120], [101, 120]], "OFF_AXIS_FIT_SET_DRIFT")
    require(abs(fit["slope"] - 0.0029166181315253155) <= 1e-14, "OFF_AXIS_SLOPE_DRIFT")
    require(fit["slope"] <= 0.03, "OFF_AXIS_REGISTERED_ALIVE_THRESHOLD_FAIL")
    require(
        result["verdict_code"] == "OFF_AXIS_PROBE_NONDECISIVE_FALSIFIER_PASS",
        "OFF_AXIS_VERDICT_DRIFT",
    )
    interpretation = result["interpretation_lock"]
    require(interpretation["classification"] == "NONDECISIVE_FALSIFIER_ONLY", "OFF_AXIS_OVERCLAIM")
    require(interpretation["completion_class_invariant"] is False, "OFF_AXIS_COMPLETION_INVARIANCE_SMUGGLED")
    require(
        abs(interpretation["slope_y_0_3_extra_lambda_phase"] - (fit["slope"] + 0.15)) <= 1e-14,
        "OFF_AXIS_GAUGE_SHIFT_PLUS_DRIFT",
    )
    require(
        abs(interpretation["slope_y_0_3_inverse_lambda_phase"] - (fit["slope"] - 0.15)) <= 1e-14,
        "OFF_AXIS_GAUGE_SHIFT_MINUS_DRIFT",
    )
    normalization = result["next_normalization_policy"]
    require(normalization["code"] == "CENTRAL_ANCHOR_NORMALIZATION_LOCKED", "OFF_AXIS_CENTRAL_ANCHOR_MISSING")
    require("Xi(0)/Ghat_j(0)" in normalization["formula"], "OFF_AXIS_ANCHOR_ORIENTATION_DRIFT")
    require("SUP_NORMALIZATION" in normalization["forbidden"], "OFF_AXIS_SUP_NORM_NOT_REJECTED")

    for entry in result["generated_coefficient_artifacts"]:
        path = resolve(entry["path"])
        require(path.is_file(), "OFF_AXIS_COEFF_ARTIFACT_MISSING")
        require(sha256(path) == entry["sha256"], "OFF_AXIS_COEFF_ARTIFACT_SHA_DRIFT")
        payload = json.loads(path.read_text(encoding="utf-8"))
        require(payload["status"] == "DIAGNOSTIC_ONLY_NOT_CANONICAL_SOURCE", "OFF_AXIS_COEFF_PROMOTION")
        require(abs(payload["metadata"]["coefficient_norm"] - 1) <= 5e-15, "OFF_AXIS_COEFF_NORM_DRIFT")

    for key in ("raw_csv", "report"):
        path = resolve(result[key]["path"])
        require(sha256(path) == result[key]["sha256"], f"OFF_AXIS_{key.upper()}_SHA_DRIFT")

    state = json.loads(STATE.read_text(encoding="utf-8"))
    node = state["nodes"]["D0.7e.5a"]
    require(node["proof_status"] == "BLOCKED", "OFF_AXIS_ILLEGAL_5A_CLOSURE")
    require(node["activity"] == "ACTIVE", "OFF_AXIS_5A_ACTIVITY_DRIFT")
    require(not list((LADDER / "bus").glob("010_*")), "OFF_AXIS_BUS_010_CREATED")
    require(result["control_plane_guards"]["mint_activated"] is False, "OFF_AXIS_MINT_ACTIVATED")
    report_text = resolve(result["report"]["path"]).read_text(encoding="utf-8")
    require("SOFT_ROUTE_ALIVE`" not in report_text, "OFF_AXIS_OLD_ALIVE_LABEL_PRESENT")
    require("completion-class dependent" in report_text, "OFF_AXIS_COMPLETION_DEPENDENCE_NOTE_MISSING")

    manifest = MANIFEST.read_text(encoding="utf-8")
    for entry in result["generated_coefficient_artifacts"]:
        require(entry["sha256"] in manifest, "OFF_AXIS_COEFF_NOT_REGISTERED")
    require(result["raw_csv"]["sha256"] in manifest, "OFF_AXIS_CSV_NOT_REGISTERED")
    require(sha256(RESULT) in manifest, "OFF_AXIS_RESULT_NOT_REGISTERED")
    print("OFF_AXIS_GROWTH_PROBE_VALID")


if __name__ == "__main__":
    main()
