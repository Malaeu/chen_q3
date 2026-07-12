#!/usr/bin/env python3
"""Fail-closed validation for partial D0.7e central calibration."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_7E_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.7e", "D0_7E_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "BLOCKED", "D0_7E_PARENT_MUST_BLOCK")
    require(cert["partial_exit_code"] == "D0_7E_CENTRAL_CALIBRATION_LOCKED", "D0_7E_PARTIAL_EXIT_MISMATCH")
    require(cert["stop_code"] == "D0_7E_XWALK_OPEN", "D0_7E_STOP_MISMATCH")
    require(cert["rh_status"] == "NOT_RH", "D0_7E_RH_FIREWALL_MISSING")

    checked: list[str] = []
    for pin in cert["dependency_pins"] + cert["source_pins"] + cert["artifacts"]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_7E_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_7E_PIN_DRIFT:{pin['path']}")
        checked.append(pin["path"])

    components = cert["components"]
    require(components["D0.7e.1"].startswith("PROVED_"), "D0_7E1_NOT_PROVED")
    require(components["D0.7e.2"].startswith("PROVED_"), "D0_7E2_NOT_PROVED")
    require(components["D0.7e.3"].startswith("PROVED_"), "D0_7E3_NOT_PROVED")
    require(components["D0.7e.4"].startswith("PROVED_"), "D0_7E4_NOT_PROVED")
    require(components["D0.7e.5"] == "BLOCKED_THEOREM_SHAPE_ONLY", "D0_7E_XWALK_OVERCLAIM")
    require(components["D0.7e.6"] == "BLOCKED_BY_D0.7e.5", "D0_7E_ASSEMBLY_OVERCLAIM")

    domain = cert["domain_lock"]
    require("m,N" in domain["finite_parameter_set"], "D0_7E_FINITE_TYPE_MISMATCH")
    require("TrialNonzero" in domain["definition_domain"], "D0_7E_TRIAL_ZERO_DIVISION")
    require("BDetNonzero" in domain["normalization_domain"], "D0_7E_B_ZERO_DIVISION")
    require(domain["N_lambda_schedule"] == "UNPINNED_KAPPA_UNSPECIFIED", "D0_7E_N_SELECTOR_SMUGGLED")

    transform = cert["transform_lock"]
    require("u^(-i*z)" in transform["canonical"], "D0_7E_CANONICAL_SIGN_DRIFT")
    require("(-z)" in transform["owner_tracker"], "D0_7E_TRANSFORM_REFLECTION_MISSING")
    require(transform["gamma_removable_value"] == "gammaC(0)=-1", "D0_7E_GAMMA_REMOVABLE_GAP")

    central = cert["central_lock"]
    require(central["zeta_half"] == "REAL_NEGATIVE_NONZERO_BY_ETA_SERIES", "D0_7E_ZETA_HALF_NONZERO_GAP")
    require(central["central_integral"] == "Fplus_m_N(0)=sqrt(L_m)*c0", "D0_7E_C0_SCALE_MISMATCH")
    require(central["scalar_field"] == "R", "D0_7E_REALITY_GAP")

    crosswalk = cert["crosswalk"]
    require(crosswalk["proof_status"] == "BLOCKED", "D0_7E_XWALK_FALSE_PASS")
    require(crosswalk["input_status"] == "THEOREM_SHAPE_TO_BE_PROVED", "D0_7E_XWALK_SHAPE_MISCLASSIFIED")
    require(crosswalk["alpha"].startswith("UNDEFINED"), "D0_7E_ALPHA_SMUGGLED")
    require(crosswalk["DeltaE"].startswith("UNDEFINED"), "D0_7E_DELTAE_SMUGGLED")
    require(crosswalk["limit_quantifier"] == "MISSING", "D0_7E_LIMIT_QUANTIFIER_SMUGGLED")
    require(crosswalk["uniform_A_K"] == "UNPROVED", "D0_7E_UNIFORM_CONSTANT_SMUGGLED")

    proof = (REPO_ROOT / cert["artifacts"][-1]["path"]).read_text(encoding="utf-8")
    for token in (
        "Fplus_(m,N)(z)",
        "= T_m(k1_(m,N))(-z)",
        "zeta(1/2)<0",
        "Fplus_(m,N)(0)",
        "D0_7E_XWALK_UNIFORM_CONSTANT_GAP",
        "D0_7E_XWALK_DEPENDENCY_CYCLE",
        "BLOCKED / THEOREM_SHAPE_ONLY",
        "NO_WPRIME_ZEO_CROSSWALK",
        "NO_RH",
    ):
        require(token in proof, f"D0_7E_PROOF_TOKEN_MISSING:{token}")

    owner = (REPO_ROOT / cert["artifacts"][0]["path"]).read_text(encoding="utf-8")
    for token in (
        "DETECTOR_B_NAME:",
        "PARAMETER_REGIME:",
        "SCALAR_FIELD_AND_TYPE:",
        "EXACT_FORMULA:",
        "NORMALIZED_OBJECT:",
        "NORMALIZATION_IDENTITY:",
        "DOMAIN_AND_NONVANISHING:",
        "REAL_COMPLEX_PHASE:",
        "W_PRIME_CROSSWALK",
        "SOURCE_POINTER:",
        "Owner-ratified NEW definition",
        "THEOREM SHAPE to be proved",
        "PO_D0_7E_XWALK",
        "D0_7E_XWALK_OPEN",
        "bDet is not bWeil_j",
        "bDet is not OCR xihat",
        "bDet is not automatically bPilot",
        "bDet is not automatically sTrial",
        "not obtained by tautologically redefining W-prime",
        "NOT_RH",
    ):
        require(token in owner, f"D0_7E_OWNER_TOKEN_MISSING:{token}")

    # Deterministic plants.
    require(1.0 - 1.0 / math.sqrt(2.0) > 0.0, "D0_7E_ZETA_DECIMAL_PLANT_INERT")
    require(1.0 - math.sqrt(2.0) < 0.0, "D0_7E_ZETA_SIGN_PLANT_INERT")
    L, c0 = 2.0, 3.0
    require(math.sqrt(L) * c0 != L * c0, "D0_7E_C0_SCALE_PLANT_INERT")
    require(transform["owner_tracker"] != transform["canonical"], "D0_7E_SIGN_PLANT_INERT")
    require("NO_N_LAMBDA_SELECTOR" in cert["explicit_nonclaims"], "D0_7E_N_SELECTOR_PLANT_INERT")
    require("NO_UNCONDITIONAL_TRIAL_NONZERO" in cert["explicit_nonclaims"], "D0_7E_TRIAL_ZERO_PLANT_INERT")
    require("NO_UNCONDITIONAL_BDET_NONZERO" in cert["explicit_nonclaims"], "D0_7E_B_ZERO_PLANT_INERT")
    require("NO_WPRIME_ZEO_CROSSWALK" in cert["explicit_nonclaims"], "D0_7E_XWALK_SHAPE_PLANT_INERT")

    result = {
        "node": "D0.7e",
        "verdict": "D0_7E_CENTRAL_CALIBRATION_LOCKED",
        "proof_status": "BLOCKED",
        "proved_children": ["D0.7e.1", "D0.7e.2", "D0.7e.3", "D0.7e.4"],
        "active_blocked_child": {"D0.7e.5": "D0_7E_XWALK_OPEN"},
        "assembly": "BLOCKED_BY_D0.7e.5",
        "pins_checked": checked,
        "plants": list(cert["plants"].values()),
        "N_lambda": "UNPINNED",
        "bus_010": "NOT_CREATED",
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
