#!/usr/bin/env python3
"""Fail-closed validator for SOFT_2 plants, phase probe, and state guards."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

from phase_structure_probe import classify, run_probe
from soft_2_planted_falsifiers import run_plants


HERE = Path(__file__).resolve().parent
CERT = HERE / "SOFT_2_LINEARITY_CROSSWALK_FORK_CERTIFICATE.json"
STATE = HERE / "STATE.json"
BUS = HERE.parent / "routeB_twolevel_spectral_ladder" / "bus"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT.read_text(encoding="utf-8"))
    require(cert["output_code"] == "C2_PHASE_FREE", "SOFT_2_VERDICT_DRIFT")

    for name, digest in cert["authority_pins"].items():
        path = HERE / name
        require(path.is_file(), f"SOFT_2_AUTHORITY_MISSING:{name}")
        require(sha256(path) == digest, f"SOFT_2_AUTHORITY_SHA_DRIFT:{name}")
    for item in cert["artifacts"].values():
        path = HERE / item["path"]
        require(path.is_file(), f"SOFT_2_ARTIFACT_MISSING:{path.name}")
        require(sha256(path) == item["sha256"], f"SOFT_2_ARTIFACT_SHA_DRIFT:{path.name}")

    stored_plants = json.loads((HERE / "SOFT_2_PLANTED_FALSIFIERS.json").read_text(encoding="utf-8"))
    replayed_plants = run_plants()
    require(stored_plants == replayed_plants, "SOFT_2_PLANT_REPLAY_DRIFT")
    expected = {
        "A": "SOFT_JOINT_LIMIT_QUANTIFIER_MISSING",
        "B": "SOFT_CRITICAL_LINE_ZERO_SUM_SMUGGLED",
        "C": "D06_GRID_ALIASING_FATAL",
    }
    for name, code in expected.items():
        row = stored_plants["plants"][name]
        require(row["fired"] is True, f"SOFT_2_PLANT_{name}_INERT")
        require(row["observed_code"] == code, f"SOFT_2_PLANT_{name}_WRONG_CODE")
    require(all(code == "PASS" for code in stored_plants["positive_controls"].values()), "SOFT_2_PLANT_FALSE_POSITIVE")
    require(stored_plants["plants"]["A"]["witness"]["tail_mass"] == 1.0, "SOFT_2_PLANT_A_WITNESS_INERT")
    require(stored_plants["plants"]["C"]["witness"]["max_grid_abs"] < 1e-12, "SOFT_2_PLANT_C_GRID_NOT_ZERO")
    require(stored_plants["plants"]["C"]["witness"]["max_midpoint_abs"] > 1 - 1e-12, "SOFT_2_PLANT_C_SUP_NOT_ONE")

    require(classify(0.01, False) == "C2_PHASE_RIGID", "SOFT_2_PHASE_RIGID_JUDGE_INERT")
    require(classify(0.31, False) == "C2_PHASE_FREE", "SOFT_2_PHASE_FREE_SD_JUDGE_INERT")
    require(classify(0.10, True) == "C2_PHASE_FREE", "SOFT_2_PHASE_FREE_DRIFT_JUDGE_INERT")
    require(classify(0.10, False) == "EXTEND", "SOFT_2_PHASE_EXTEND_JUDGE_INERT")

    stored_phase = json.loads((HERE / "PHASE_STRUCTURE_PROBE.json").read_text(encoding="utf-8"))
    replayed_phase = run_probe()
    stored_core = {k: v for k, v in stored_phase.items() if k not in {"raw_csv", "report"}}
    require(stored_core == replayed_phase, "SOFT_2_PHASE_REPLAY_DRIFT")
    require(stored_phase["arithmetic"]["dps_escalation"] is False, "SOFT_2_PHASE_DPS_ESCALATION")
    require(stored_phase["window"]["grid_count"] == 4096, "SOFT_2_PHASE_GRID_DRIFT")
    cells = [(row["lambda_sq"], row["N"]) for row in stored_phase["cells"]]
    require(cells == [(13, 120), (14, 120), (53, 120), (101, 120)], "SOFT_2_PHASE_CELL_DRIFT")
    for row, expected_sd in zip(stored_phase["cells"], cert["phase_probe"]["sd_theta_mod_pi"]):
        require(math.isclose(row["phase"]["sd_theta_mod_pi"], expected_sd, rel_tol=0, abs_tol=1e-14), "SOFT_2_PHASE_SD_DRIFT")
        require(row["phase"]["sd_theta_mod_pi"] >= 0.3, "SOFT_2_PHASE_FREE_THRESHOLD_NOT_MET")
        require(row["drift"]["systematic"] is True, "SOFT_2_PHASE_SYSTEMATIC_DRIFT_MISSING")
        require(row["verdict"] == "C2_PHASE_FREE", "SOFT_2_PHASE_CELL_VERDICT_DRIFT")
    require(stored_phase["verdict_code"] == "C2_PHASE_FREE", "SOFT_2_PHASE_OVERALL_VERDICT_DRIFT")

    symmetry = (HERE / cert["artifacts"]["symmetry_audit"]["path"]).read_text(encoding="utf-8")
    for token in (
        "KTRIAL_REAL_CONJUGATION_SYMMETRY_ONLY",
        "c_(-n)=conjugate(c_n)",
        "H(-conjugate(z))=conjugate(H(z))",
        "`B(-x)=conjugate(B(x)) => H(x) real` is false",
        "NOT_RH",
    ):
        require(token in symmetry, f"SOFT_2_SYMMETRY_TOKEN_MISSING:{token}")

    state = json.loads(STATE.read_text(encoding="utf-8"))
    node = state["nodes"]["D0.7e.5a"]
    require(node["proof_status"] == "BLOCKED", "SOFT_2_ILLEGAL_5A_CLOSURE")
    require(node["activity"] == "ACTIVE", "SOFT_2_5A_ACTIVITY_DRIFT")
    require(node["scheduler_marker"] == "NON_CRITICAL_PENDING_SOFT_2", "SOFT_2_5A_MARKER_MISSING")
    require(node["mint_activated"] is False, "SOFT_2_MINT_ACTIVATED")
    require(not list(BUS.glob("010_*")), "SOFT_2_BUS_010_CREATED")
    require(cert["guards"]["rh_status"] == "NOT_RH", "SOFT_2_RH_FIREWALL_MISSING")
    print("C2_PHASE_FREE")


if __name__ == "__main__":
    main()
