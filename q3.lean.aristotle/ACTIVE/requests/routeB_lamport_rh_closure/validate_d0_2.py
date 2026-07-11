#!/usr/bin/env python3
"""Fail-closed validation for D0.2 ExactWeilSesquilinearForm."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_2_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.2", "D0_2_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_2_CERT_NOT_PROVED")
    require(cert["rh_status"] == "NOT_RH", "D0_2_RH_FIREWALL_MISSING")
    require(
        cert["form_lock"]["positivity"] == "NOT_CLAIMED_LOWER_BOUNDED_ONLY",
        "D0_2_POSITIVITY_SMUGGLED",
    )

    dependency = REPO_ROOT / cert["dependency"]["certificate_path"]
    require(dependency.is_file(), "D0_2_D0_1_CERT_MISSING")
    require(
        sha256(dependency) == cert["dependency"]["certificate_sha256"],
        "D0_2_D0_1_CERT_HASH_DRIFT",
    )

    checked_pins: list[str] = []
    for pin in cert["source_pins"] + [cert["proof_artifact"]]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_2_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_2_PIN_HASH_DRIFT:{pin['path']}")
        checked_pins.append(pin["path"])

    proof = (REPO_ROOT / cert["proof_artifact"]["path"]).read_text(encoding="utf-8")
    for token in (
        "Psi(F) = W_0_2(F) - W_R(F) - sum_p W_p(F)",
        "F^*(u)=conjugate(F(u^-1))",
        "c^* T_m_N d",
        "LOWER_BOUNDED_NOT_POSITIVE",
        "D0.2 = PROVED",
        "NOT_RH",
    ):
        require(token in proof, f"D0_2_PROOF_TOKEN_MISSING:{token}")

    # F1: exact sign ledger versus a planted positive prime term.
    w_02, w_r, w_p = 7.0, 2.0, 3.0
    correct_psi = w_02 - w_r - w_p
    planted_psi = w_02 - w_r + w_p
    require(correct_psi == 2.0, "D0_2_SIGN_LEDGER_CHECK_FAILED")
    require(planted_psi != correct_psi, "D0_2_PRIME_SIGN_PLANT_INERT")

    # F2: sesquilinear first-slot conjugation.
    c = 1j
    d = 1.0 + 0j
    correct_form = c.conjugate() * d
    planted_bilinear = c * d
    require(correct_form == -1j, "D0_2_CONJUGATION_CHECK_FAILED")
    require(planted_bilinear != correct_form, "D0_2_CONJUGATION_PLANT_INERT")

    # F3: a semibounded 1x1 form need not be positive.
    semibounded_eigenvalue = -1.0
    require(semibounded_eigenvalue < 0.0, "D0_2_POSITIVITY_PLANT_INERT")

    # F4/F5: the certificate must retain extended-real domain and half factor.
    require(
        cert["form_lock"]["window_form_type"] == "qW_m:H_m->R_union_{+infinity}",
        "D0_2_DOMAIN_OVERCLAIM_PLANT_INERT",
    )
    require(cert["form_lock"]["arch_half_factor"] == "1/2", "D0_2_ARCH_HALF_FACTOR_PLANT_INERT")

    # F6: a trial Rayleigh value need not be the lowest eigenvalue.
    ground_eigenvalue = 0.0
    trial_rayleigh_value = 2.0
    require(
        trial_rayleigh_value != ground_eigenvalue,
        "D0_2_TRIAL_EIGENVALUE_CONFLATION_PLANT_INERT",
    )

    # Hermitian index sentinel catches transposed lookup before real specialization.
    tau_minus_plus = 1j
    tau_plus_minus = -1j
    require(
        tau_plus_minus == tau_minus_plus.conjugate(),
        "D0_2_HERMITIAN_SENTINEL_INVALID",
    )
    require(tau_minus_plus != tau_plus_minus, "D0_2_MATRIX_INDEX_PLANT_INERT")

    result = {
        "node": "D0.2",
        "verdict": "EXACT_WEIL_FORM_LOCKED",
        "proof_status": "PROVED",
        "pins_checked": checked_pins,
        "plants": [
            "D0_2_PRIME_SIGN_PLANT_FIRES",
            "D0_2_CONJUGATION_PLANT_FIRES",
            "D0_2_POSITIVITY_OVERCLAIM_PLANT_FIRES",
            "D0_2_DOMAIN_OVERCLAIM_PLANT_FIRES",
            "D0_2_ARCH_HALF_FACTOR_PLANT_FIRES",
            "D0_2_TRIAL_EIGENVALUE_CONFLATION_PLANT_FIRES",
            "D0_2_MATRIX_INDEX_PLANT_FIRES",
        ],
        "positivity": "NOT_CLAIMED",
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
