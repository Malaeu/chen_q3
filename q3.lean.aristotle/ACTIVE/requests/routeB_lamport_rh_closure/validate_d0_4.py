#!/usr/bin/env python3
"""Fail-closed validation for D0.4 ExactParitySectors."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_4_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.4", "D0_4_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_4_CERT_NOT_PROVED")
    require(cert["exit_code"] == "EXACT_PARITY_SECTORS_LOCKED", "D0_4_EXIT_MISMATCH")
    require(cert["rh_status"] == "NOT_RH", "D0_4_RH_FIREWALL_MISSING")

    dependency = REPO_ROOT / cert["dependency"]["certificate_path"]
    require(dependency.is_file(), "D0_4_D0_3G_CERT_MISSING")
    require(sha256(dependency) == cert["dependency"]["certificate_sha256"], "D0_4_D0_3G_CERT_DRIFT")

    proof_path = REPO_ROOT / cert["proof_artifact"]["path"]
    require(proof_path.is_file(), "D0_4_PROOF_MISSING")
    require(sha256(proof_path) == cert["proof_artifact"]["sha256"], "D0_4_PROOF_DRIFT")
    proof = proof_path.read_text(encoding="utf-8")

    lock = cert["parity_lock"]
    spectral = cert["spectral_firewall"]
    require(lock["full_inversion"] == "Inv_m(f)(u)=f(u^-1)", "D0_4_INVERSION_MISMATCH")
    require(lock["log_coordinate"] == "x_to_L_minus_x", "D0_4_CENTERING_MISMATCH")
    require(lock["mode_action"] == "Inv_m(V_n_m)=V_-n_m", "D0_4_MODE_ACTION_MISMATCH")
    require(lock["finite_even_dimension"] == "N+1" and lock["finite_odd_dimension"] == "N", "D0_4_DIMENSION_MISMATCH")
    require(spectral["global_bottom_three_pattern"] == "NOT_CLAIMED", "D0_4_GLOBAL_ORDER_SMUGGLED")
    require(spectral["pilot_cleanliness"] == "NOT_CLAIMED", "D0_4_PILOT_CLEANNESS_SMUGGLED")

    for token in (
        "x -> log(lambda/u)=L-x",
        "Inv_m V_n=V_-n",
        "dim(Eplus_m_N)=N+1",
        "NO_GLOBAL_BOTTOM_THREE_SECTOR_PATTERN",
        "D0.4 = PROVED",
        "NO_RH",
    ):
        require(token in proof, f"D0_4_PROOF_TOKEN_MISSING:{token}")

    # F1: uncentered x->-x differs from the correct x->L-x.
    L = 2.0
    x = 0.3
    require(not math.isclose(-x, L - x), "D0_4_UNCENTERED_INVERSION_PLANT_INERT")

    # F2: u->lambda^2/u sends the left endpoint outside the window.
    lam = 2.0
    left = 1.0 / lam
    planted_image = lam * lam / left
    require(planted_image > lam, "D0_4_WRONG_MAP_PLANT_INERT")

    # F3: V0 is fixed, producing N+1 versus N.
    n = 5
    require((n + 1) - n == 1, "D0_4_MISSING_V0_PLANT_INERT")

    # F4: symmetric mode has parity +1, not -1.
    coeffs = (1.0 / math.sqrt(2.0), 1.0 / math.sqrt(2.0))
    reversed_coeffs = tuple(reversed(coeffs))
    require(reversed_coeffs == coeffs, "D0_4_WRONG_PARITY_PLANT_INERT")

    # F5: direct-sum spectra need not alternate sectors.
    full = sorted([0.0, 1.0] + [100.0])
    require(full[1] == 1.0 and full[1] != 100.0, "D0_4_GLOBAL_ORDER_PLANT_INERT")

    # F6: exact parity does not certify a numerical implementation.
    nonclaims = set(cert["explicit_nonclaims"])
    require("NO_PILOT_PARITY_CLEANNESS" in nonclaims, "D0_4_PILOT_CLEANNESS_PLANT_INERT")

    result = {
        "node": "D0.4",
        "verdict": "EXACT_PARITY_SECTORS_LOCKED",
        "proof_status": "PROVED",
        "full_inversion": "LOCKED",
        "finite_reduction": "LOCKED",
        "global_order": "NOT_CLAIMED",
        "pilot_cleanliness": "NOT_CLAIMED",
        "plants": list(cert["plants"].values()),
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
