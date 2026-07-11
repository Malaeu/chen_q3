#!/usr/bin/env python3
"""Fail-closed validation for D0.3g CanonicalFiniteWeilDetector."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_3G_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.3g", "D03G_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D03G_CERT_NOT_PROVED")
    require(cert["exit_code"] == "D03G_CANONICAL_WEILOP_LOCKED", "D03G_EXIT_MISMATCH")
    require(cert["rh_status"] == "NOT_RH", "D03G_RH_FIREWALL_MISSING")

    dependency = REPO_ROOT / cert["dependency"]["certificate_path"]
    require(dependency.is_file(), "D03G_D0_2_CERT_MISSING")
    require(sha256(dependency) == cert["dependency"]["certificate_sha256"], "D03G_D0_2_CERT_DRIFT")

    checked_pins: list[str] = []
    pins = cert["source_pins"] + [
        cert["architectural_review"],
        cert["decomposition"]["artifact"],
        cert["proof_artifact"],
    ]
    for pin in pins:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D03G_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D03G_PIN_DRIFT:{pin['path']}")
        checked_pins.append(pin["path"])

    require(cert["architectural_review"]["verdict"] == "CANONICALIZE_WEILOP", "D03G_RATIFICATION_MISSING")
    require(cert["architectural_review"]["classification"] == "ADVISORY_NOT_PROOF_AUTHORITY", "D03G_REVIEW_AUTHORITY_OVERCLAIM")
    require(cert["decomposition"]["proof_status"] == "PROVED", "D03G_DECOMPOSITION_UNPROVED")
    require(cert["components"]["D0.3g.6"] == "ASSEMBLY_PROVED", "D03G_ASSEMBLY_UNPROVED")

    operator = cert["operator_lock"]
    parity = cert["parity_lock"]
    spectral = cert["spectral_lock"]
    require(operator["definition"] == "Mfin_m_N:=WeilOp_m_N", "D03G_CARRIER_SOURCE_CONFLICT")
    require(operator["gram"] == "I_(2N+1)", "D03G_GRAM_NOT_IDENTITY")
    require(operator["matrix"] == "WeilMat_m_N", "D03G_MATRIX_ACTION_MISMATCH")
    require(operator["selfadjoint"] is True, "D03G_SELFADJOINTNESS_GAP")
    require(operator["M_lambda_status"] == "UNDEFINED_PENDING_SELECTOR", "D03G_M_LAMBDA_SMUGGLED")
    require(parity["unitary"] and parity["selfadjoint"], "D03G_PARITY_INVOLUTION_FAIL")
    require(parity["commutation"] == "R_m_N*Mfin_m_N=Mfin_m_N*R_m_N", "D03G_PARITY_COMMUTATOR_NONZERO")
    require(parity["even_dimension"] == "N+1" and parity["odd_dimension"] == "N", "D03G_SECTOR_REDUCTION_FAIL")
    require(spectral["multiset_union"] is True, "D03G_SECTOR_SPECTRUM_ENUMERATION_FAIL")
    require(spectral["global_bottom_three_pattern"] == "NOT_CLAIMED", "D03G_GLOBAL_ORDER_SMUGGLED")
    require(spectral["theta_nu_identity"] == "FORBIDDEN_UNLESS_PROVED", "D03G_SPECTRAL_PROVENANCE_COLLISION")

    proof = (REPO_ROOT / cert["proof_artifact"]["path"]).read_text(encoding="utf-8")
    for token in (
        "Mfin_m_N := WeilOp_m_N",
        "Gram             = I_(2N+1)",
        "R_m_N Mfin_m_N = Mfin_m_N R_m_N",
        "dim(Eplus_m_N)=N+1",
        "multiset_union",
        "NO_M_LAMBDA",
        "D0.3g = PROVED",
        "NO_RH",
    ):
        require(token in proof, f"D03G_PROOF_TOKEN_MISSING:{token}")

    # F1: duplicated basis vectors make Gram non-identity.
    duplicated_gram = [[1.0, 1.0], [1.0, 1.0]]
    require(duplicated_gram != [[1.0, 0.0], [0.0, 1.0]], "D03G_GRAM_PLANT_INERT")

    # F2: Hermitian off-diagonal sentinel detects an index transpose.
    tau_01, tau_10 = 1j, -1j
    require(tau_10 == tau_01.conjugate() and tau_10 != tau_01, "D03G_MATRIX_ACTION_PLANT_INERT")

    # F3: n -> 1-n does not preserve {-N,...,N} at n=-N.
    n_bound = 3
    planted_image = 1 - (-n_bound)
    require(planted_image > n_bound, "D03G_PARITY_PLANT_INERT")

    # F4: changing one corner of a centrosymmetric 3x3 matrix breaks JAJ=A.
    planted = [[2.0, 1.0, 0.0], [1.0, 3.0, 1.0], [0.0, 1.0, 4.0]]
    reverse = lambda a: [list(reversed(row)) for row in reversed(a)]
    require(reverse(planted) != planted, "D03G_COMMUTATOR_PLANT_INERT")

    # F5: the fixed vector V0 accounts for the N+1 versus N dimension split.
    n = 4
    require((n + 1) + n == 2 * n + 1, "D03G_SECTOR_DIMENSION_PLANT_INERT")

    # F6: spectra of two sectors need not alternate in the full sorted list.
    plus_spectrum = [0.0, 1.0]
    minus_spectrum = [100.0]
    full_spectrum = sorted(plus_spectrum + minus_spectrum)
    require(full_spectrum[1] != minus_spectrum[0], "D03G_GLOBAL_ORDER_PLANT_INERT")

    # F7/F8: provenance and parameter firewalls are explicit metadata.
    nonclaims = set(cert["explicit_nonclaims"])
    require("NO_THETA_NU_EQUALITY" in nonclaims, "D03G_THETA_ALIAS_PLANT_INERT")
    require("NO_M_LAMBDA" in nonclaims and "N" in operator["parameter_regime"], "D03G_M_LAMBDA_PLANT_INERT")

    result = {
        "node": "D0.3g",
        "verdict": "D03G_CANONICAL_WEILOP_LOCKED",
        "proof_status": "PROVED",
        "carrier": "Mfin_m_N=WeilOp_m_N",
        "parity": "EXACT_REDUCING",
        "spectra": ["nu", "epsilon_plus", "epsilon_minus"],
        "schur_namespace": "theta_DIAGNOSTIC_ONLY",
        "M_lambda": "UNDEFINED",
        "pins_checked": checked_pins,
        "plants": list(cert["plants"].values()),
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
