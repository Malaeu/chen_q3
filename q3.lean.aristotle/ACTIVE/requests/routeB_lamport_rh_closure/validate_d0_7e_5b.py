#!/usr/bin/env python3
"""Fail-closed validator for the D0.7e.5b type-only interface."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_7E_5B_CERTIFICATE.json"
STATE_PATH = REQUEST_DIR / "STATE.json"
BUS_DIR = REQUEST_DIR.parent / "routeB_twolevel_spectral_ladder" / "bus"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def has_forbidden_instantiation(text: str) -> bool:
    compact = " ".join(text.split())
    return any(
        token in compact
        for token in (
            "alpha :=",
            "DeltaE :=",
            "delta_dict :=",
            "F :=",
            "N(lambda)",
            "N(λ)",
            "kappa",
            "κ",
        )
    )


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    state = json.loads(STATE_PATH.read_text(encoding="utf-8"))
    interface_path = REQUEST_DIR / "D0_7E_5B_TYPED_INTERFACE.md"
    interface = interface_path.read_text(encoding="utf-8")

    require(cert["node_id"] == "D0.7e.5b", "D0_7E_5B_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_7E_5B_NOT_PROVED")
    require(cert["proof_scope"] == "INTERFACE_TYPECHECK_ONLY", "D0_7E_5B_SCOPE_OVERCLAIM")
    require(cert["exit_code"] == "D0_7E_5B_TYPED_INTERFACE_LOCKED", "D0_7E_5B_EXIT_DRIFT")
    require(cert["rh_status"] == "NOT_RH", "D0_7E_5B_RH_FIREWALL_MISSING")

    checked: list[str] = []
    for pin in cert["dependency_pins"] + cert["artifacts"]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_7E_5B_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_7E_5B_PIN_DRIFT:{pin['path']}")
        checked.append(pin["path"])

    require(cert["carrier"]["kind"] == "INDEPENDENT_TWO_PARAMETER_m_N", "D0_7E_SELECTOR_INVENTED")
    require(cert["carrier"]["selector"] == "NONE", "D0_7E_SELECTOR_INVENTED")
    require(cert["carrier"]["coordinates_related"] is False, "D0_7E_SELECTOR_INVENTED")
    require(not has_forbidden_instantiation(interface), "D0_7E_TYPED_PARAMETER_INSTANTIATED_IN_D0")
    require("alpha       : I_two -> RealNonnegative" in interface, "D0_7E_ALPHA_TYPE_MISSING")
    require("DeltaE      : I_two -> RealStrictlyPositive" in interface, "D0_7E_TRUE_GAP_TYPE_MISSING")
    require("delta_dict  : I_two -> RealNonnegative" in interface, "D0_7E_DICTIONARY_TYPE_MISSING")
    require("FilterSpace : I_two -> Type" in interface, "D0_7E_FILTER_TYPE_MISSING")
    require("F           : product over i in I_two of FilterSpace(i)" in interface, "D0_7E_FILTER_PARAMETER_MISSING")

    node = state["nodes"]["D0.7e.5b"]
    require(node["proof_status"] == "PROVED", "D0_7E_5B_STATE_NOT_PROVED")
    require(node["activity"] == "INACTIVE", "D0_7E_5B_STATE_ACTIVE")
    require(node["dependencies"] == ["D0.7e.5.0", "D0.1", "D0.3g", "D0.7e.3"], "D0_7E_5B_DEPENDENCY_DRIFT")
    require(node["validation"] == "D0_7E_5B_TYPED_INTERFACE_LOCKED", "D0_7E_5B_STATE_VALIDATION_DRIFT")
    require(state["external_obligations"]["PO-1/A1"]["status"] == "OPEN_CRITICAL", "D0_7E_ALPHA_DEFINITION_SMUGGLED")

    # Deterministic plants.
    require(has_forbidden_instantiation(interface + "\nalpha := 0"), "D0_7E_TYPED_PARAMETER_INSTANTIATED_IN_D0_PLANT_INERT")
    require(has_forbidden_instantiation(interface + "\nN(lambda)"), "D0_7E_SELECTOR_INVENTED_PLANT_INERT")
    require("NO_MODEL_GAP_SUBSTITUTION" in cert["explicit_nonclaims"], "MODEL_GAP_SUBSTITUTION_PLANT_INERT")

    require(not any(BUS_DIR.glob("010_*.goal.md")), "D0_7E_5B_BUS_010_CREATED")
    require("NO_RH" in cert["explicit_nonclaims"], "D0_7E_5B_RH_OVERCLAIM")

    print(json.dumps({
        "node": "D0.7e.5b",
        "verdict": "D0_7E_5B_TYPED_INTERFACE_LOCKED",
        "proof_status": "PROVED",
        "scope": "INTERFACE_TYPECHECK_ONLY",
        "pins_checked": checked,
        "plants": list(cert["plants"].values()),
        "bus_010": "NOT_CREATED",
        "rh": "NOT_RH",
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
