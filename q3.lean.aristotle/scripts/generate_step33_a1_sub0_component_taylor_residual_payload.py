#!/usr/bin/env python3
"""Fail-closed component Taylor residual payload for Step33A.1-A sub0.

This is the route-B payload selected for the current full-Taylor residual
derivative interval blocker.  The generator records the proof-producing shape
for a cancellation-preserving component Taylor certificate:

1. build Taylor data for omega, omega', E, and E';
2. assemble the raw derivative polynomial exactly;
3. subtract the checked full-Taylor model derivative coefficients;
4. bound the assembled residual polynomial plus one combined remainder.

It does not emit Lean proof data yet.  The first open analytic gate is the
proof-grade omega/omega-prime Taylor remainder package.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any

from generate_step33_a1_sub0_cancellation_residual_interval_certificate import (
    COEFF_DEF,
    LANDING_FILE,
    REQUEST_DIR,
    extract_coefficients,
    file_hash,
    parse_rat,
    rat_text,
)


DEFAULT_COMPONENT_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_cancellation_residual_interval_certificate.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.md"
)

SCHEMA = "q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v1"
ROUTE_ID = "STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL"
STATUS = "fail_closed_missing_omega_omegaprime_taylor_remainder"
FIRST_FAILURE = "STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP"

TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "fullTaylor_residual_deriv_taylor_enclosure"
)
TARGET_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean"
TARGET_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "fullTaylor_residual_deriv_closedForm_interval"
)
TARGET_INTERVAL_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean"

CELL_L = "0"
CELL_U = "1/10"
CENTER = "1/20"
RADIUS = "1/20"
COMPONENT_DEGREE = 15
ASSEMBLED_DEGREE = 45
TARGET_LOWER = "-94119513411/500000000000000000000000000000"
TARGET_UPPER = "1866608532757/500000000000000000000000000000"


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def padded_model_coefficients(
    model_coeffs: list[dict[str, Any]],
    *,
    assembled_degree: int,
) -> list[dict[str, Any]]:
    coeff_by_index = {
        int(item["index"]): parse_rat(str(item["value"])) for item in model_coeffs
    }
    out: list[dict[str, Any]] = []
    for index in range(assembled_degree + 1):
        value = coeff_by_index.get(index, Fraction(0, 1))
        out.append({"index": index, "value": rat_text(value)})
    return out


def component_slots(name: str) -> list[dict[str, Any]]:
    return [
        {
            "index": index,
            "value": None,
            "status": "missing_proof_grade_component_taylor_coeff",
            "component": name,
        }
        for index in range(COMPONENT_DEGREE + 1)
    ]


def build_report(
    *,
    landing_path: Path,
    component_ledger_path: Path,
) -> dict[str, Any]:
    model_coeffs, source_lines = extract_coefficients(landing_path)
    component_ledger = load_json(component_ledger_path)
    target_lower = parse_rat(TARGET_LOWER)
    target_upper = parse_rat(TARGET_UPPER)

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": STATUS,
        "chosenRoute": "B",
        "advisorySource": "browser_proshka_route_advice_not_proof_evidence",
        "firstFailure": FIRST_FAILURE,
        "failureCodes": [
            FIRST_FAILURE,
            "STEP33_A1_SUB0_SHAPE_SHAPEDERIV_TAYLOR_REMAINDER_GAP",
            "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_GAP",
            "STEP33_A1_SUB0_RESIDUAL_POLYNOMIAL_RANGE_GAP",
            "STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL_LEAN_PAYLOAD_MISSING",
        ],
        "cell": {
            "cellL": CELL_L,
            "cellU": CELL_U,
            "center": CENTER,
            "radius": RADIUS,
            "targetLower": TARGET_LOWER,
            "targetUpper": TARGET_UPPER,
            "targetWidth": rat_text(target_upper - target_lower),
        },
        "degrees": {
            "componentDegree": COMPONENT_DEGREE,
            "assembledDegree": ASSEMBLED_DEGREE,
            "modelDegree": 15,
        },
        "targetTheorem": {
            "file": TARGET_FILE,
            "name": TARGET_THEOREM,
            "statementAscii": (
                f"theorem {TARGET_THEOREM} {{eta : Real}} "
                "(heta : eta in Set.Icc 0 (1/10)) : "
                "norm ((RawIntegrandDerivClosedForm eta - "
                "rawOmegaATaylorPolynomial 15 (1/20) ResidualDerivmodelCoeff eta) - "
                "rawOmegaATaylorPolynomial 45 (1/20) ResidualTaylorCoeff eta) <= "
                "ResidualTaylorRemainderAbs"
            ),
        },
        "downstreamIntervalTheorem": {
            "file": TARGET_INTERVAL_FILE,
            "name": TARGET_INTERVAL_THEOREM,
            "consumes": [
                TARGET_THEOREM,
                "residualPolynomialLower",
                "residualPolynomialUpper",
                "finalResidualLower",
                "finalResidualUpper",
                "budgetPassed",
            ],
        },
        "generatorFields": {
            "omegaCoeff": component_slots("omega"),
            "omegaDerivCoeff": component_slots("omegaDeriv"),
            "shapeCoeff": component_slots("shape"),
            "shapeDerivCoeff": component_slots("shapeDeriv"),
            "omegaRemainderAbs": None,
            "omegaDerivRemainderAbs": None,
            "shapeRemainderAbs": None,
            "shapeDerivRemainderAbs": None,
            "assembledRawDerivCoeff": None,
            "modelDerivCoeff": model_coeffs,
            "modelDerivCoeffPaddedToAssembledDegree": padded_model_coefficients(
                model_coeffs, assembled_degree=ASSEMBLED_DEGREE
            ),
            "residualTaylorCoeff": None,
            "productTruncationRemainderAbs": None,
            "componentPropagationRemainderAbs": None,
            "residualTaylorRemainderAbs": None,
            "residualPolynomialLower": None,
            "residualPolynomialUpper": None,
            "finalResidualLower": None,
            "finalResidualUpper": None,
        },
        "proofStatus": {
            "exactCoefficientAssemblyPassed": False,
            "componentTaylorProofsPresent": False,
            "residualPolynomialRangePassed": False,
            "finalBudgetPassed": False,
            "proofSafeClosedFields": 0,
            "outLeanWritten": False,
        },
        "existingLeanInputs": {
            "modelDerivCoeffSource": COEFF_DEF,
            "modelDerivCoeffCount": len(model_coeffs),
            "fullTaylorPolynomialDerivativeCrosswalk": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "fullTaylor_polynomial_deriv_eq_derivmodel"
            ),
            "fullTaylorResidualDerivativeCrosswalk": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "fullTaylor_residual_deriv_eq_closedForm"
            ),
            "fullTaylorDirectValidityBridge": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "fullTaylor_direct_segment_cert_valid_of_residual_bounds"
            ),
        },
        "proshkaDecision": {
            "chosen": "B",
            "whyNotA": (
                "Endpoint finite-cover machinery still lacks proof-grade "
                "Omega/OmegaPrime/E/EPrime remainder sources; it would create "
                "another empty checker first."
            ),
            "whyNotC": (
                "A monolithic direct Lean proof would mix component expansions, "
                "product assembly, model subtraction, and range proof in one "
                "hard-to-audit theorem."
            ),
        },
        "sourceStatus": {
            "componentLedgerPath": str(component_ledger_path),
            "componentLedgerSchema": (
                component_ledger.get("schema") if component_ledger else None
            ),
            "componentLedgerStatus": (
                component_ledger.get("status") if component_ledger else None
            ),
        },
        "sourceDefinitionLines": source_lines,
        "sourceDefinitionHashes": {
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean": file_hash(
                landing_path
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_cancellation_residual_interval_certificate.json": (
                file_hash(component_ledger_path)
            ),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Sub0 Component Taylor Residual Payload",
        "",
        "Fail-closed route-B payload. This is not Lean proof data and does",
        "not close Step33A.1-A.",
        "",
        "## Status",
        "",
        f"- schema: `{report['schema']}`",
        f"- route: `{report['routeId']}`",
        f"- chosen route: `{report['chosenRoute']}`",
        f"- status: `{report['status']}`",
        f"- first failure: `{report['firstFailure']}`",
        f"- advisory source: `{report['advisorySource']}`",
        f"- proof-safe closed fields: `{report['proofStatus']['proofSafeClosedFields']}`",
        f"- Lean emitted: `{report['proofStatus']['outLeanWritten']}`",
        "",
        "## Target",
        "",
        f"- theorem: `{report['targetTheorem']['name']}`",
        f"- file: `{report['targetTheorem']['file']}`",
        f"- component degree: `{report['degrees']['componentDegree']}`",
        f"- assembled degree: `{report['degrees']['assembledDegree']}`",
        f"- center: `{report['cell']['center']}`",
        f"- radius: `{report['cell']['radius']}`",
        f"- target interval: `[{report['cell']['targetLower']}, {report['cell']['targetUpper']}]`",
        "",
        "```text",
        report["targetTheorem"]["statementAscii"],
        "```",
        "",
        "## Model Derivative Coefficients",
        "",
        f"Extracted from local Lean definition `{report['existingLeanInputs']['modelDerivCoeffSource']}`.",
        "",
        "| i | coeff | source line |",
        "| --- | --- | --- |",
    ]
    for item in report["generatorFields"]["modelDerivCoeff"]:
        lines.append(
            f"| {item['index']} | `{item['value']}` | {item['sourceLine']} |"
        )

    lines.extend(
        [
            "",
            "## Required Component Fields",
            "",
            "- `omegaCoeff[0..15]`",
            "- `omegaDerivCoeff[0..15]`",
            "- `shapeCoeff[0..15]`",
            "- `shapeDerivCoeff[0..15]`",
            "- `omegaRemainderAbs`",
            "- `omegaDerivRemainderAbs`",
            "- `shapeRemainderAbs`",
            "- `shapeDerivRemainderAbs`",
            "- `assembledRawDerivCoeff[0..45]`",
            "- `residualTaylorCoeff[0..45]`",
            "- `residualTaylorRemainderAbs`",
            "- `residualPolynomialLower` / `residualPolynomialUpper`",
            "- `finalResidualLower` / `finalResidualUpper`",
            "",
            "## Proof Status",
            "",
        ]
    )
    for key, value in report["proofStatus"].items():
        lines.append(f"- {key}: `{value}`")

    lines.extend(
        [
            "",
            "## Existing Lean Inputs",
            "",
        ]
    )
    for key, value in report["existingLeanInputs"].items():
        lines.append(f"- {key}: `{value}`")

    lines.extend(
        [
            "",
            "## Proshka Decision",
            "",
            "- chosen: `B`",
            f"- why not A: {report['proshkaDecision']['whyNotA']}",
            f"- why not C: {report['proshkaDecision']['whyNotC']}",
            "",
            "## Failure Codes",
            "",
        ]
    )
    for code in report["failureCodes"]:
        lines.append(f"- `{code}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            "The next proof-producing gate is component Taylor/remainder data for",
            "`omega`, `omegaDeriv`, `shape`, and `shapeDeriv`.  Only after those",
            "component proofs exist may the generator assemble the raw derivative,",
            "subtract the model derivative coefficients, bound the residual",
            "polynomial, and emit Lean for the interval theorem.",
            "",
        ]
    )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--landing", type=Path, default=LANDING_FILE)
    parser.add_argument(
        "--component-ledger", type=Path, default=DEFAULT_COMPONENT_LEDGER
    )
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(
        landing_path=args.landing,
        component_ledger_path=args.component_ledger,
    )
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} first_failure={failure} model_coeffs={coeffs} out_json={out_json}".format(
            status=report["status"],
            failure=report["firstFailure"],
            coeffs=len(report["generatorFields"]["modelDerivCoeff"]),
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
