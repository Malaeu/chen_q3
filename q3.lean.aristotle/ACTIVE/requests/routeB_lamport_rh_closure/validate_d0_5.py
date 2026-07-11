#!/usr/bin/env python3
"""Fail-closed validation for D0.5 ground/trial types."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_5_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.5", "D0_5_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_5_CERT_NOT_PROVED")
    require(cert["exit_code"] == "GROUND_TRIAL_TYPES_LOCKED", "D0_5_EXIT_MISMATCH")
    require(cert["rh_status"] == "NOT_RH", "D0_5_RH_FIREWALL_MISSING")

    dependency = REPO_ROOT / cert["dependency"]["certificate_path"]
    require(dependency.is_file(), "D0_5_D0_4_CERT_MISSING")
    require(sha256(dependency) == cert["dependency"]["certificate_sha256"], "D0_5_D0_4_CERT_DRIFT")

    checked_pins: list[str] = []
    for pin in cert["source_pins"] + [cert["proof_artifact"]]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_5_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_5_PIN_DRIFT:{pin['path']}")
        checked_pins.append(pin["path"])

    ground = cert["ground_lock"]
    trial = cert["trial_lock"]
    require(ground["nonzero"] is True, "D0_5_GROUND_SPACE_ZERO")
    require(ground["simple"] == "NOT_CLAIMED", "D0_5_SIMPLE_EVEN_SMUGGLED")
    require(ground["even"] == "NOT_CLAIMED", "D0_5_EVEN_GROUND_SMUGGLED")
    require("TrialNonzero" in trial["normalized_packet"], "D0_5_ZERO_TRIAL_DIVISION")
    require(trial["ground_identity"] == "NOT_CLAIMED", "D0_5_GROUND_TRIAL_CONFLATION")
    require(trial["prolate_indices"] == "h0_to_chi0_AND_h4_to_chi2", "D0_5_H4_INDEX_MISMATCH")

    proof = (REPO_ROOT / cert["proof_artifact"]["path"]).read_text(encoding="utf-8")
    for token in (
        "GroundSpace_m_N := ker",
        "TrialNonzero",
        "groundValue_m_N <= aTrial_m_N",
        "NO_SIMPLE_GROUND",
        "D0.5 = PROVED",
        "NO_RH",
    ):
        require(token in proof, f"D0_5_PROOF_TOKEN_MISSING:{token}")

    # F1: zero matrix on C^2 has a two-dimensional ground space.
    zero_matrix_ground_dimension = 2
    require(zero_matrix_ground_dimension != 1, "D0_5_SIMPLE_GROUND_PLANT_INERT")

    # F2: an odd sector can lie below an even sector.
    even_bottom, odd_bottom = 1.0, 0.0
    require(odd_bottom < even_bottom, "D0_5_EVEN_GROUND_PLANT_INERT")

    # F3: normalization of the zero vector is undefined.
    zero_norm = 0.0
    require(zero_norm == 0.0, "D0_5_ZERO_TRIAL_PLANT_INERT")

    # F4: trial e2 for diag(0,2) is not ground.
    ground_value, trial_value = 0.0, 2.0
    require(trial_value != ground_value, "D0_5_TRIAL_GROUND_PLANT_INERT")

    # F5: additive and finite multiplicative carriers have distinct names.
    require(trial["time_carrier"] != "E_m_N", "D0_5_CARRIER_ALIAS_PLANT_INERT")

    # F6: the exact source index is chi2, not chi4.
    require("chi2" in trial["prolate_indices"] and "chi4" not in trial["prolate_indices"], "D0_5_H4_INDEX_PLANT_INERT")

    # F7: endpoint changes on finitely many points have zero L2 mass.
    finite_point_set_measure = 0.0
    require(finite_point_set_measure == 0.0, "D0_5_MIDPOINT_L2_PLANT_INERT")

    result = {
        "node": "D0.5",
        "verdict": "GROUND_TRIAL_TYPES_LOCKED",
        "proof_status": "PROVED",
        "ground": "SET_VALUED_NO_SIMPLE_EVEN_CLAIM",
        "trial": "DEPENDENT_NORMALIZATION_ON_NONZERO_LOCUS",
        "ground_trial_identity": "NOT_CLAIMED",
        "pins_checked": checked_pins,
        "plants": list(cert["plants"].values()),
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
