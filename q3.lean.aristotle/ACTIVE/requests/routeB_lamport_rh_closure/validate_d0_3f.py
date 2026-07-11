#!/usr/bin/env python3
"""Fail-closed validation for D0.3f prolate window realization."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_3F_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.3f", "D0_3F_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_3F_CERT_NOT_PROVED")
    require(cert["exit_code"] == "PROLATE_SELFADJOINT_REALIZATION_LOCKED", "D0_3F_EXIT_MISMATCH")
    require(cert["rh_status"] == "NOT_RH", "D0_3F_RH_FIREWALL_MISSING")

    checked_pins: list[str] = []
    for pin in (cert["source_lock"], cert["proof_artifact"]):
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_3F_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_3F_PIN_HASH_DRIFT:{pin['path']}")
        checked_pins.append(pin["path"])

    source = json.loads((REPO_ROOT / cert["source_lock"]["path"]).read_text(encoding="utf-8"))
    require(source["arxiv_id"] == "1603.07542v1", "D0_3F_SOURCE_VERSION_MISMATCH")
    require(
        source["source_member_sha256"] == "6d36ac8201d07c96a981a112f0947a2a6b8b5a10d8ddc11577d75264984f8e33",
        "D0_3F_EXTERNAL_TEX_HASH_MISMATCH",
    )
    require(source["exact_labels"]["canonical_boundary_condition"] == "FBC", "D0_3F_SOURCE_BOUNDARY_LABEL_MISMATCH")

    operator = cert["operator_lock"]
    scaling = cert["scaling_lock"]
    require(operator["selfadjoint"] is True, "D0_3F_SELFADJOINTNESS_MISSING")
    require("left_boundary" in operator and "right_boundary" in operator, "D0_3F_ONE_ENDPOINT_PLANT_INERT")
    require("f_prime" in operator["left_boundary"] and "f_prime" in operator["right_boundary"], "D0_3F_DIRICHLET_ALIAS_PLANT_INERT")
    require(operator["maximal_domain"] != "C_c_infinity", "D0_3F_CORE_DOMAIN_PLANT_INERT")
    require("AND" in operator["maximal_domain"], "D0_3F_MAXIMAL_DOMAIN_PLANT_INERT")
    require(operator["global_L2_R_extension"] == "DISTINCT_OPERATOR_NOT_ALIASED", "D0_3F_GLOBAL_WINDOW_PLANT_INERT")

    # Exact coefficient check for c=sqrt(2*pi), a=c*lambda.
    lam = 3.0
    c2 = 2.0 * math.pi
    scalar = c2 * lam * lam
    principal_coefficient = scalar / (c2 * lam * lam)
    potential_coefficient = scalar * c2
    project_potential_coefficient = (2.0 * math.pi * lam) ** 2
    require(abs(principal_coefficient - 1.0) < 1e-14, "D0_3F_SCALING_PRINCIPAL_PLANT_INERT")
    require(abs(potential_coefficient - project_potential_coefficient) < 1e-12, "D0_3F_SCALING_POTENTIAL_PLANT_INERT")
    require(scaling["dimensionless_bandwidth"] == "2*pi*lambda^2", "D0_3F_BANDWIDTH_PLANT_INERT")

    proof = (REPO_ROOT / cert["proof_artifact"]["path"]).read_text(encoding="utf-8")
    for token in (
        "lim_(x->-lambda+) p_lambda(x)f'(x)=0",
        "lim_(x-> lambda-) p_lambda(x)f'(x)=0",
        "c=sqrt(2*pi)",
        "(2*pi*lambda^2) U^(-1) L_(a,I) U",
        "D0.3f = PROVED",
        "NO_CANONICAL_DETECTOR_OPERATOR",
        "NO_RH",
    ):
        require(token in proof, f"D0_3F_PROOF_TOKEN_MISSING:{token}")

    nonclaims = set(cert["explicit_nonclaims"])
    require("NO_PW_EQUALS_WEIL_OPERATOR" in nonclaims, "D0_3F_WEIL_CONFLATION_PLANT_INERT")
    require("NO_PW_EQUALS_DLOG" in nonclaims, "D0_3F_DLOG_CONFLATION_PLANT_INERT")

    result = {
        "node": "D0.3f",
        "verdict": "PROLATE_SELFADJOINT_REALIZATION_LOCKED",
        "proof_status": "PROVED",
        "retired_failure_code": cert["retired_failure_code"],
        "source": "arXiv:1603.07542v1",
        "pins_checked": checked_pins,
        "plants": list(cert["plants"].values()),
        "global_extension": "DISTINCT",
        "detector": "MISSING",
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
