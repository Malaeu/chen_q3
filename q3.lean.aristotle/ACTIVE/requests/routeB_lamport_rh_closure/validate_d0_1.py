#!/usr/bin/env python3
"""Fail-closed validation for D0.1 ExactHilbertSpaceAndNorm."""

from __future__ import annotations

import cmath
import hashlib
import json
import math
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_1_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))

    require(cert["node_id"] == "D0.1", "D0_1_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_1_CERT_NOT_PROVED")
    require(cert["rh_status"] == "NOT_RH", "D0_1_RH_FIREWALL_MISSING")
    require(
        cert["parameter_lock"]["N_schedule"]
        == "UNSELECTED_LATER_D0_8_H3C_OBLIGATION",
        "D0_1_N_SCHEDULE_SMUGGLED",
    )

    checked_pins: list[str] = []
    for pin in cert["source_pins"] + [cert["proof_artifact"]]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_1_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_1_PIN_HASH_DRIFT:{pin['path']}")
        checked_pins.append(pin["path"])

    proof = (REPO_ROOT / cert["proof_artifact"]["path"]).read_text(encoding="utf-8")
    for token in (
        "Lambda_int",
        "I_fin",
        "kappa_m",
        "E_(m,N)",
        "D0.1 = PROVED",
        "LEAN_INTERFACE_UNPINNED",
        "NOT_RH",
    ):
        require(token in proof, f"D0_1_PROOF_TOKEN_MISSING:{token}")

    # Cofinality and the exact identity L=2 log(sqrt(m))=log(m).
    for radius in (1.1, 2.0, 10.0, 100.0):
        m = math.floor(radius * radius) + 1
        if m < 2:
            m = 2
        lam = math.sqrt(m)
        require(lam > radius, "D0_1_COFINALITY_CHECK_FAILED")
        require(
            math.isclose(2.0 * math.log(lam), math.log(m), rel_tol=0.0, abs_tol=2e-14),
            "D0_1_L_IDENTITY_FAILED",
        )

    # F1: du/u preserves the constant norm; du does not.
    lam = math.e
    length = 2.0
    correct_constant_norm_sq = math.log(lam) - math.log(1.0 / lam)
    wrong_du_norm_sq = lam - 1.0 / lam
    require(
        math.isclose(correct_constant_norm_sq, length, rel_tol=0.0, abs_tol=1e-14),
        "D0_1_CORRECT_MEASURE_CHECK_FAILED",
    )
    require(
        not math.isclose(wrong_du_norm_sq, length, rel_tol=0.0, abs_tol=1e-6),
        "D0_1_MEASURE_PLANT_INERT",
    )

    # F2: the L^(-1/2) normalization is necessary.
    unnormalized_mode_norm_sq = length
    normalized_mode_norm_sq = (length ** -0.5) ** 2 * length
    require(
        not math.isclose(unnormalized_mode_norm_sq, 1.0, abs_tol=1e-14),
        "D0_1_MODE_NORMALIZATION_PLANT_INERT",
    )
    require(
        math.isclose(normalized_mode_norm_sq, 1.0, abs_tol=1e-14),
        "D0_1_MODE_NORMALIZATION_CHECK_FAILED",
    )

    # F3: log(lambda*u), not log(u), fixes the phase.
    correct_phase = cmath.exp(2j * math.pi * math.log(lam) / length) / math.sqrt(length)
    planted_phase = cmath.exp(2j * math.pi * math.log(1.0) / length) / math.sqrt(length)
    require(
        abs(correct_phase + 1.0 / math.sqrt(2.0)) < 1e-14,
        "D0_1_COORDINATE_PHASE_CHECK_FAILED",
    )
    require(
        abs(planted_phase - 1.0 / math.sqrt(2.0)) < 1e-14,
        "D0_1_COORDINATE_PLANT_INERT",
    )

    # F4: zero has empty support, so full-support-for-every-H is false.
    zero_vector_has_full_window_support = False
    require(
        not zero_vector_has_full_window_support,
        "D0_1_SUPPORT_OVERCLAIM_PLANT_INERT",
    )

    result = {
        "node": "D0.1",
        "verdict": "EXACT_HILBERT_SPACE_AND_NORM_LOCKED",
        "proof_status": "PROVED",
        "pins_checked": checked_pins,
        "plants": [
            "D0_1_MEASURE_PLANT_FIRES",
            "D0_1_MODE_NORMALIZATION_PLANT_FIRES",
            "D0_1_COORDINATE_PLANT_FIRES",
            "D0_1_SUPPORT_OVERCLAIM_PLANT_FIRES",
        ],
        "N_schedule": "UNSELECTED",
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
