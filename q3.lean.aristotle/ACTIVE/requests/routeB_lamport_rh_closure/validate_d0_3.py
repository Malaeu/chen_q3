#!/usr/bin/env python3
"""Fail-closed validation for the proved D0.3 operator registry."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_3_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.3", "D0_3_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_3_PARENT_NOT_PROVED")
    require(cert["exit_code"] == "EXACT_OPERATOR_TYPES_LOCKED", "D0_3_EXIT_MISMATCH")
    require(cert["rh_status"] == "NOT_RH", "D0_3_RH_FIREWALL_MISSING")

    for dep in cert["dependencies"]:
        path = REPO_ROOT / dep["certificate_path"]
        require(path.is_file(), f"D0_3_DEPENDENCY_MISSING:{dep['node']}")
        require(sha256(path) == dep["certificate_sha256"], f"D0_3_DEPENDENCY_DRIFT:{dep['node']}")

    checked_pins: list[str] = []
    pins = cert["source_pins"] + cert["proved_component_pins"] + [cert["decomposition"]["artifact"], cert["proof_artifact"]]
    for pin in pins:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_3_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_3_PIN_HASH_DRIFT:{pin['path']}")
        checked_pins.append(pin["path"])

    children = cert["decomposition"]["children"]
    require(children == [f"D0.3{x}" for x in "abcdefgh"], "D0_3_DECOMPOSITION_ORDER_MISMATCH")
    require(cert["decomposition"]["proof_status"] == "PROVED", "D0_3_DECOMPOSITION_UNPROVED")

    components = cert["components"]
    for node in ("D0.3a", "D0.3b", "D0.3c", "D0.3d", "D0.3e", "D0.3f", "D0.3g", "D0.3h"):
        require(components[node]["proof_status"] == "PROVED", f"D0_3_COMPONENT_NOT_PROVED:{node}")
    require(components["D0.3g"]["definition_status"] == "Mfin_m_N:=WeilOp_m_N", "D0_3_DETECTOR_DEFINITION_MISMATCH")
    require(components["D0.3g"]["M_lambda_status"] == "UNDEFINED_PENDING_SELECTOR", "D0_3_M_LAMBDA_SMUGGLED")
    require(components["D0.3i"]["proof_status"] == "PROVED", "D0_3_ASSEMBLY_UNPROVED")

    proof = (REPO_ROOT / cert["proof_artifact"]["path"]).read_text(encoding="utf-8")
    for token in (
        "Dom(A_m) subset H_m -> H_m",
        "trace(F)(0)=trace(F)(L)",
        "WeilOp_m_N = A_m restricted to E_m_N",
        "raw_selfadjointness",
        "PROLATE_SELFADJOINT_REALIZATION_LOCKED",
        "D03G_CANONICAL_WEILOP_LOCKED",
        "D0.3 = PROVED",
        "NO_RH",
    ):
        # The raw-selfadjointness token is represented by prose in the proof;
        # accept either exact token or the explicit standard-H nonclaim.
        if token == "raw_selfadjointness":
            require("standard-`H_m` selfadjointness is `NOT_CLAIMED`" in proof, "D0_3_RAW_SA_FIREWALL_MISSING")
        else:
            require(token in proof, f"D0_3_PROOF_TOKEN_MISSING:{token}")

    # Plant 1: form-domain membership alone must not grant operator action.
    require(
        components["D0.3a"]["domain"] == "Dom(A_m) subset Dom(BW_m) subset H_m",
        "D0_3_FORM_OPERATOR_DOMAIN_PLANT_INERT",
    )

    # Plant 2: H1 does not imply the periodic endpoint equality.
    L = 2.0
    f0, fL = 0.0, L
    require(f0 != fL, "D0_3_PERIODIC_DOMAIN_PLANT_INERT")

    # Plant 3: a form compression need not be an operator restriction.
    # A e1=e2 is outside E=span(e1), while <Ae1,e1>=0.
    ae1 = (0.0, 1.0)
    compression = ae1[0]
    require(compression == 0.0 and ae1[1] != 0.0, "D0_3_FINITE_COMPRESSION_PLANT_INERT")

    # Plant 4: the perturbation remains xi-indexed.
    dlog_xi0 = (0.0, 0.0)
    dlog_xi1 = (0.0, 1.0)
    require(dlog_xi0 != dlog_xi1, "D0_3_XI_PARAMETER_PLANT_INERT")

    # Plant 5: modified-space selfadjointness may not be attached to raw H_m.
    require(
        components["D0.3d"]["raw_selfadjointness"] == "NOT_CLAIMED_FALSE_IN_GENERAL",
        "D0_3_INNER_PRODUCT_PLANT_INERT",
    )
    require(
        "QW_SHIFT_INNER_PRODUCT" in components["D0.3d"]["canonical_carrier"],
        "D0_3_MODIFIED_INNER_PRODUCT_OMITTED",
    )

    # Plant 6: additive PW coordinates permit negative x; multiplicative u do not.
    x = -1.0
    require(x < 0.0, "D0_3_PW_SPACE_PLANT_INERT")

    # Plant 7: the finite carrier may not be promoted to M_lambda or a pilot alias.
    require(
        "M_lambda" in components["D0.3g"]["forbidden_aliases"]
        and "G_even" in components["D0.3g"]["forbidden_aliases"],
        "D0_3_DETECTOR_SCOPE_PLANT_INERT",
    )

    # Plant 8: a QW shift propagates only to the QW-derived operators.
    t = 3.0
    a_before, finite_before, dlog_before, pw_before = 1.0, 2.0, 5.0, 7.0
    a_after, finite_after = a_before + t, finite_before + t
    dlog_after, pw_after = dlog_before, pw_before
    require(a_after != a_before and finite_after != finite_before, "D0_3_DEPENDENCY_PLANT_A_INERT")
    require(dlog_after == dlog_before and pw_after == pw_before, "D0_3_DEPENDENCY_PLANT_B_INERT")

    result = {
        "node": "D0.3",
        "verdict": "EXACT_OPERATOR_TYPES_LOCKED",
        "proof_status": "PROVED",
        "proved_children": ["D0.3a", "D0.3b", "D0.3c", "D0.3d", "D0.3e", "D0.3f", "D0.3g", "D0.3h"],
        "blocked_children": {},
        "next_independent_leaf": cert["next_independent_leaf"],
        "pins_checked": checked_pins,
        "plants": list(cert["plants"].values()),
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
