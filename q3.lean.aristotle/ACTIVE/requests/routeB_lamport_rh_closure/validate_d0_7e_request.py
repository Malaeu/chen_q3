#!/usr/bin/env python3
"""Validate the D0.7e external-owner request and provenance firewall."""

from pathlib import Path


HERE = Path(__file__).resolve().parent
DECISION = HERE / "D0_7E_PRO_REVIEW_DECISION.md"
REQUEST = HERE / "D0_7E_OWNER_INPUT_REQUEST.md"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


decision = DECISION.read_text(encoding="utf-8")
request = REQUEST.read_text(encoding="utf-8")

for token in (
    "C. EXTERNAL_OWNER_INPUT_REQUIRED",
    "bPilot=||E(g04)||",
    "not promotable",
    "D0_7_DETECTOR_B_DEFINITION_MISSING",
    "NO_BUS_010_CREATED",
    "NOT_RH",
):
    require(token in decision, f"D0_7E_DECISION_TOKEN_MISSING:{token}")

for token in (
    "EXACT_FORMULA:",
    "SCALAR_FIELD_AND_TYPE:",
    "NORMALIZATION_IDENTITY:",
    "DOMAIN_AND_NONVANISHING:",
    "REAL_COMPLEX_PHASE:",
    "W_PRIME_CROSSWALK:",
    "SOURCE_POINTER:",
    "bDet is not bWeil_j",
    "bDet is not automatically bPilot=||E(g04)||",
    "not obtained by tautologically redefining W-prime",
):
    require(token in request, f"D0_7E_REQUEST_TOKEN_MISSING:{token}")

print("D0_7E_EXTERNAL_OWNER_REQUEST_LOCKED")
print("D0_7_DETECTOR_B_DEFINITION_MISSING")
print("NO_BUS_010_CREATED")
print("NOT_RH")
