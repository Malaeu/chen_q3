#!/usr/bin/env python3
"""Fail-closed validator for the SOFT_1 paper gate."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
Q3 = ROOT.parents[2]
CERT = ROOT / "SOFT_1_ZERO_FREE_GAUGE_AND_DISTRIBUTIONAL_IDENTIFICATION_CERTIFICATE.json"
PAPER = ROOT / "SOFT_1_ZERO_FREE_GAUGE_AND_DISTRIBUTIONAL_IDENTIFICATION_2026-07-13.md"
STATE = ROOT / "STATE.json"
BUS = ROOT.parent / "routeB_twolevel_spectral_ladder" / "bus"
EXPECTED = "SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC"
STOPS = {
    "SOFT_GAMMA_INTERIOR_POLE",
    "SOFT_GAMMA_NOT_ZERO_FREE",
    "SOFT_GAUGE_ORIENTATION_MISSING",
    "SOFT_GAUGE_NORMALITY_GAP",
    "SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC",
    "SOFT_S2_RH_CONDITIONAL_IMPORT",
    "SOFT_ANCHOR_FUNCTIONAL_ZERO",
    "SOFT_JOINT_LIMIT_QUANTIFIER_MISSING",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    cert = json.loads(CERT.read_text())
    paper = PAPER.read_text()
    state = json.loads(STATE.read_text())

    require(cert["output_code"] in STOPS, "certificate output is not a contract stop")
    require(cert["output_code"] == EXPECTED, "unexpected SOFT_1 verdict")

    for name, digest in cert["authority_pins"].items():
        if name.startswith("literature/"):
            path = Q3 / name
        else:
            path = ROOT / name
        require(path.is_file(), f"missing authority: {name}")
        require(sha256(path) == digest, f"authority pin drift: {name}")

    for item in cert["deliverables"].values():
        path = ROOT / item["path"]
        require(path.is_file(), f"missing deliverable: {path.name}")
        require(sha256(path) == item["sha256"], f"deliverable pin drift: {path.name}")

    required_paper_tokens = [
        "GaugeSoftSubsequenceZeroEscape",
        "SOFT_GAUGE_ROOF_TYPED",
        "Fhat_(m,N)/gamma_(m,N) = B_(m,N)",
        "H_(m,N)=gammaC(1/2) B_(m,N)/bDet_(m,N)",
        "SOFT_ZETA_ONE_QUARTER_SOURCE_LOCK.json",
        "NONREAL_ANCHOR_UNIFORM_CONTROL` remains `OPEN",
        "P_I(Fhat_(m,N),phi)",
        "sum_(|n|<=N) c_n A_(m,phi,n)",
        "linear crosswalk",
        "QW(f,g)=Psi(f^* * g)",
        "Replace `kTrial` by `exp(i theta) kTrial`",
        "product-tail filter",
        "RH_IMPORT_AUDIT_PASS",
        "MovingGridToIntervalBridge",
        EXPECTED,
        "NOT_RH",
    ]
    for token in required_paper_tokens:
        require(token in paper, f"paper token missing: {token}")

    g = cert["obligations"]
    require(g["G1"]["status"] == "TYPED_IMPLICATION", "G1 not typed")
    require(not g["G1"]["physical_local_normality_proved"], "G1 overclaims normality")
    require(g["G2"]["orientation"] == "Fhat/gamma=B", "G2 orientation drift")
    require(g["G3"]["uniform_control"].endswith("_OPEN"), "G3 uniformity overclaim")
    require(g["G4"]["status"] == "FAIL", "G4 must fail")
    require(g["G4"]["side"] == "TRANSFORM_SIDE", "G4 side confusion")
    require(g["G5"]["status"] == "POSED_OPEN", "G5 must remain open")
    require(g["G6"]["status"] == "RH_IMPORT_AUDIT_PASS", "G6 audit failed")
    require(not g["G6"]["bfm_imported"], "BFM import detected")
    require(not g["G6"]["critical_line_only_sum_imported"], "critical-line import detected")
    require(g["G7"]["status"] == "REGISTERED_NOT_EXECUTED", "G7 overclaim")

    nodes = state["nodes"].values() if isinstance(state["nodes"], dict) else state["nodes"]
    node = next(n for n in nodes if n["id"] == "D0.7e.5a")
    require(node["proof_status"] == "BLOCKED", "5a proof status changed")
    require(node["activity"] == "ACTIVE", "5a activity changed")
    require(
        node["scheduler_marker"] in {"NON_CRITICAL_PENDING_SOFT_1", "NON_CRITICAL_PENDING_SOFT_2"},
        "5a marker not advanced",
    )
    require(not node["mint_activated"], "5a mint activated")
    require(not any(BUS.glob("010_*")), "Bus 010 exists")

    print(EXPECTED)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"SOFT_1_VALIDATION_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(1)
