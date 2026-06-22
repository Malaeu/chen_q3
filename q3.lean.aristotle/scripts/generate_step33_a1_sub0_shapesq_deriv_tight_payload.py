#!/usr/bin/env python3
"""Fail-closed audit for the Step33A.1-A Sub0 tight ShapeSqDeriv payload.

This generator deliberately does not emit Lean.  Its job is to decide whether
the repository already contains a proof-grade tight coefficient stream that is
usable in the same convention as the active RawTaylorCoeffCert residual.  If
that stream is not identifiable, the payload stops before Lean theorem
emission with STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_COEFF_STREAM_GAP.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUESTS = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

SUPPORT_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean"
COEFF_ROWS_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAShapeSqDerivCoeffRows.lean"
LANDING_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAHRawLanding.lean"
CONTRACT_FILE = REQUESTS / "step33_a1_sub0_shapesq_deriv_tight_payload_contract.md"
COMPONENT_PAYLOAD_JSON = (
    REQUESTS / "step33_a1_sub0_component_taylor_residual_payload.json"
)
OUTPUT_JSON = REQUESTS / "step33_a1_sub0_shapesq_deriv_tight_payload.json"
OUTPUT_MD = REQUESTS / "step33_a1_sub0_shapesq_deriv_tight_payload.md"

SCHEMA = "q3_psdpd_step33_a1_sub0_shapesq_deriv_tight_payload.v1"
STATUS_FAIL_CLOSED = "fail_closed_tight_coeff_stream_not_identified"

FAIL_TIGHT_COEFF_STREAM = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_COEFF_STREAM_GAP"
)
FAIL_ROWS_ORDER16 = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP"
)
ROUTE_LEVEL_GAP = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP"
)

TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid"
)
TIGHT_COEFF = "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff"
TIGHT_COEFF_ERROR = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs"
)
TIGHT_ORDER16 = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs"
)

RAW_TAYLOR_COEFF = "primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeff"
RAW_TAYLOR_CERT = "primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert"
RESIDUAL_DERIV_MODEL = (
    "primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff"
)
FULL_TAYLOR_RESIDUAL_CROSSWALK = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm"
)
FULL_TAYLOR_POLY_CROSSWALK = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel"
)

VALID_POWER_SERIES_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_interval"
)
VALID_SHAPESQ_DERIVATIVE_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shapeSq_derivative_abs"
)
SINGLE_ABS = "ShapeSqDerivTaylorIntervalCert.singleAbs"
ROW0_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff0_interval_generated"
)
ROW1_INTERVAL = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff1_interval_generated"
)
POWER_SERIES_AT_CENTER = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter"
)
SHAPESQ_ORDER16_RECEIVER = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_order16_abs_of_shapeSq_order17_abs"
)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def line_of(text: str, needle: str) -> int | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        if needle in line:
            return idx
    return None


def source_entry(path: Path, text: str, symbols: list[str]) -> dict[str, Any]:
    return {
        "path": str(path.relative_to(ROOT)),
        "exists": path.exists(),
        "symbols": {
            sym: {
                "found": sym in text,
                "line": line_of(text, sym),
            }
            for sym in symbols
        },
    }


def load_component_payload() -> dict[str, Any] | None:
    if not COMPONENT_PAYLOAD_JSON.exists():
        return None
    return json.loads(COMPONENT_PAYLOAD_JSON.read_text(encoding="utf-8"))


def has_same_coeff_stream_crosswalk(lean_text: str) -> bool:
    """Conservative search for a theorem tying tight coeffs to active residual."""

    tight_present = TIGHT_COEFF in lean_text or "ShapeSqDerivTight" in lean_text
    active_present = (
        RAW_TAYLOR_CERT in lean_text
        or RAW_TAYLOR_COEFF in lean_text
        or RESIDUAL_DERIV_MODEL in lean_text
    )
    if not (tight_present and active_present):
        return False
    bridge_words = ("same", "matches", "crosswalk", "residual", "convention")
    return any(word in lean_text for word in bridge_words)


def build_report() -> dict[str, Any]:
    support = read_text(SUPPORT_FILE)
    coeff_rows = read_text(COEFF_ROWS_FILE)
    landing = read_text(LANDING_FILE)
    contract = read_text(CONTRACT_FILE)
    lean_text = "\n".join([support, coeff_rows, landing])
    component_payload = load_component_payload()

    receiver_ok = all(
        name in support
        for name in [
            VALID_POWER_SERIES_INTERVAL,
            VALID_SHAPESQ_DERIVATIVE_ABS,
            SINGLE_ABS,
            SHAPESQ_ORDER16_RECEIVER,
        ]
    )
    row0_ok = ROW0_INTERVAL in coeff_rows
    row1_ok = ROW1_INTERVAL in coeff_rows
    active_residual_ok = all(
        name in landing
        for name in [
            RAW_TAYLOR_COEFF,
            RAW_TAYLOR_CERT,
            RESIDUAL_DERIV_MODEL,
            FULL_TAYLOR_POLY_CROSSWALK,
            FULL_TAYLOR_RESIDUAL_CROSSWALK,
        ]
    )

    tight_objects_present_in_lean = all(
        name in lean_text for name in [TIGHT_COEFF, TIGHT_COEFF_ERROR, TIGHT_ORDER16]
    )
    tight_valid_theorem_present_in_lean = TARGET_THEOREM in lean_text
    same_coeff_crosswalk_present = has_same_coeff_stream_crosswalk(lean_text)

    if not same_coeff_crosswalk_present:
        first_failure = FAIL_TIGHT_COEFF_STREAM
        status = STATUS_FAIL_CLOSED
    elif not tight_objects_present_in_lean or not tight_valid_theorem_present_in_lean:
        first_failure = FAIL_ROWS_ORDER16
        status = "fail_closed_tight_rows_order16_payload_missing"
    else:
        first_failure = None
        status = "candidate_ready_for_lean_validation"

    required_rows = list(range(2, 16))
    report: dict[str, Any] = {
        "schema": SCHEMA,
        "status": status,
        "targetTheorem": TARGET_THEOREM,
        "routeLevelFailureCode": ROUTE_LEVEL_GAP,
        "firstFailure": first_failure,
        "proofBoundary": (
            "This payload is an audit/checkpoint only. It emits no Lean and "
            "does not prove Step33A.1-A."
        ),
        "sourceFiles": {
            "support": source_entry(
                SUPPORT_FILE,
                support,
                [
                    POWER_SERIES_AT_CENTER,
                    VALID_POWER_SERIES_INTERVAL,
                    VALID_SHAPESQ_DERIVATIVE_ABS,
                    SHAPESQ_ORDER16_RECEIVER,
                    SINGLE_ABS,
                ],
            ),
            "coeffRows": source_entry(
                COEFF_ROWS_FILE,
                coeff_rows,
                [ROW0_INTERVAL, ROW1_INTERVAL],
            ),
            "landing": source_entry(
                LANDING_FILE,
                landing,
                [
                    RESIDUAL_DERIV_MODEL,
                    RAW_TAYLOR_COEFF,
                    RAW_TAYLOR_CERT,
                    FULL_TAYLOR_POLY_CROSSWALK,
                    FULL_TAYLOR_RESIDUAL_CROSSWALK,
                ],
            ),
            "contract": source_entry(
                CONTRACT_FILE,
                contract,
                [TARGET_THEOREM, FAIL_TIGHT_COEFF_STREAM, ROUTE_LEVEL_GAP],
            ),
        },
        "existingLeanInputs": {
            "shapeSqDerivReceiversProofGrade": receiver_ok,
            "row0IntervalProofGrade": row0_ok,
            "row1IntervalProofGrade": row1_ok,
            "activeRawTaylorResidualSurfacePresent": active_residual_ok,
            "componentPayloadStatus": (
                component_payload.get("status") if component_payload else None
            ),
            "componentPayloadFirstFailure": (
                component_payload.get("firstFailure") if component_payload else None
            ),
        },
        "sameCoefficientGuard": {
            "required": True,
            "tightCoeffObjectsPresentInLean": tight_objects_present_in_lean,
            "tightValidTheoremPresentInLean": tight_valid_theorem_present_in_lean,
            "sameCoeffCrosswalkPresent": same_coeff_crosswalk_present,
            "guardPasses": same_coeff_crosswalk_present,
            "stopCodeIfMissing": FAIL_TIGHT_COEFF_STREAM,
            "searchedFor": [
                TIGHT_COEFF,
                TIGHT_COEFF_ERROR,
                TIGHT_ORDER16,
                RAW_TAYLOR_CERT,
                RAW_TAYLOR_COEFF,
                RESIDUAL_DERIV_MODEL,
            ],
        },
        "remainingObligations": {
            "rowsRemaining": required_rows,
            "order16BoundRemaining": True,
            "sameCoefficientCrosswalkRemaining": not same_coeff_crosswalk_present,
            "leanCanSeeFinalTheorem": tight_valid_theorem_present_in_lean,
        },
        "decision": {
            "canEmitLeanTheorem": (
                same_coeff_crosswalk_present
                and tight_objects_present_in_lean
                and tight_valid_theorem_present_in_lean
            ),
            "nextPatch": (
                "Identify or generate the tight coefficient stream in the same "
                "RawTaylorCoeffCert residual convention. If no such source "
                "exists, keep the blocker at "
                f"{FAIL_TIGHT_COEFF_STREAM}."
            ),
            "doNot": [
                "do not emit primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid yet",
                "do not spend the coarse zero-coefficient payload",
                "do not add another receiver before a concrete missing receiver is identified",
                "do not attack the final residual interval before same-coefficient source exists",
            ],
        },
    }
    return report


def render_markdown(report: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Step33A.1-A Sub0 ShapeSqDeriv Tight Payload Audit",
        "",
        f"Schema: `{report['schema']}`",
        "",
        f"Status: `{report['status']}`",
        "",
        f"Target theorem: `{report['targetTheorem']}`",
        "",
        f"Route-level gap: `{report['routeLevelFailureCode']}`",
        "",
        f"First failure: `{report['firstFailure']}`",
        "",
        "Boundary: this file is generated audit data only.  It is not Lean proof",
        "data and does not close Step33A.1-A.",
        "",
        "## Existing Inputs",
        "",
    ]
    for key, value in report["existingLeanInputs"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Same-Coefficient Guard", ""])
    guard = report["sameCoefficientGuard"]
    for key in [
        "tightCoeffObjectsPresentInLean",
        "tightValidTheoremPresentInLean",
        "sameCoeffCrosswalkPresent",
        "guardPasses",
    ]:
        lines.append(f"- `{key}`: `{guard[key]}`")
    lines.append(f"- stop code if missing: `{guard['stopCodeIfMissing']}`")

    lines.extend(["", "## Source Inventory", ""])
    for source_name, source in report["sourceFiles"].items():
        lines.append(f"### {source_name}")
        lines.append("")
        lines.append(f"- path: `{source['path']}`")
        lines.append(f"- exists: `{source['exists']}`")
        for sym, info in source["symbols"].items():
            lines.append(
                f"- `{sym}`: found=`{info['found']}`, line=`{info['line']}`"
            )
        lines.append("")

    lines.extend(["## Remaining Obligations", ""])
    obligations = report["remainingObligations"]
    lines.append(f"- rows remaining: `{obligations['rowsRemaining']}`")
    lines.append(f"- order16 bound remaining: `{obligations['order16BoundRemaining']}`")
    lines.append(
        "- same-coefficient crosswalk remaining: "
        f"`{obligations['sameCoefficientCrosswalkRemaining']}`"
    )
    lines.append(
        f"- Lean can see final theorem: `{obligations['leanCanSeeFinalTheorem']}`"
    )

    lines.extend(["", "## Decision", ""])
    decision = report["decision"]
    lines.append(f"- can emit Lean theorem: `{decision['canEmitLeanTheorem']}`")
    lines.append(f"- next patch: {decision['nextPatch']}")
    lines.append("")
    lines.append("Do not:")
    for item in decision["doNot"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    report = build_report()
    OUTPUT_JSON.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    OUTPUT_MD.write_text(render_markdown(report), encoding="utf-8")
    print(
        "status={status} first_failure={first}".format(
            status=report["status"],
            first=report["firstFailure"],
        )
    )


if __name__ == "__main__":
    main()
