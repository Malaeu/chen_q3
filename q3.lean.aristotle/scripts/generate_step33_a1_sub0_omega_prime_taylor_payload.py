#!/usr/bin/env python3
"""Fail-closed OmegaPrime Taylor payload for Step33A.1-A sub0.

This generator records the smallest proof-producing surface for the current
component Taylor blocker:

    step22OmegaArchWeightDerivClosedForm

around center 1/20 on radius 1/20, degree 15.  It deliberately does not emit
Lean until the order-16/polygamma bound and center-jet coefficient enclosures
are proof-grade.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"

CHUNK_FILE = ROOT / "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean"
ENDPOINT_HIGH_ORDER_FILE = (
    ROOT / "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean"
)
COMPONENT_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.json"
)
GAP_MAP = (
    REQUEST_DIR / "step33_a1_sub0_omega_omegaprime_taylor_remainder_gap.md"
)
DEFAULT_OUT_JSON = REQUEST_DIR / "step33_a1_sub0_omega_prime_taylor_payload.json"
DEFAULT_OUT_MD = REQUEST_DIR / "step33_a1_sub0_omega_prime_taylor_payload.md"

SCHEMA = "q3_psdpd_step33_a1_sub0_omega_prime_taylor_payload.v2"
ROUTE_ID = "STEP33_A1_SUB0_OMEGA_PRIME_TAYLOR_PAYLOAD"
STATUS = "fail_closed_missing_centered_taylor_reflection_bridge"
FIRST_FAILURE = "STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP"
ORDER16_FAILURE = "STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP"

FUNCTION_ID = "step22OmegaArchWeightDerivClosedForm"
TARGET_CERT = "Step33Sub0OmegaPrimeTaylorRemainderCert"
TARGET_VALID = "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid"
TARGET_BOUND = "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound"
TARGET_CENTER_BRIDGE = (
    "Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound"
)
TARGET_VALID_OF_ORDER16 = "Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound"
GENERATOR_NAME = "scripts/generate_step33_a1_sub0_omega_prime_taylor_payload.py"
LEAN_TARGET_FILE = "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean"

CELL_L = "0"
CELL_U = "1/10"
CENTER = "1/20"
RADIUS = "1/20"
DEGREE = 15
ORDER = 16


SOURCE_SYMBOLS = {
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean": [
        "rawOmegaATaylorPolynomial",
        "digamma_analyticAt_of_re_pos",
        "trigamma_differentiableAt_of_re_pos",
        "step22OmegaArchWeightDerivClosedForm",
        "step22OmegaArchWeightDerivClosedForm_differentiableAt",
        "step22OmegaArchWeight_deriv_eq_closedForm",
        "Step22OmegaClosedFormEndpointBoundsCert",
        "ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound",
    ],
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean": [
        "step33_shift16_digamma_m6_integral_remainder_bound",
        "Q3.digammaM6IntegralRemainderBound",
    ],
}

SOURCE_PATTERNS = {
    "rawOmegaATaylorPolynomial": "def rawOmegaATaylorPolynomial",
    "digamma_analyticAt_of_re_pos": "theorem digamma_analyticAt_of_re_pos",
    "trigamma_differentiableAt_of_re_pos": (
        "theorem trigamma_differentiableAt_of_re_pos"
    ),
    "step22OmegaArchWeightDerivClosedForm": (
        "def step22OmegaArchWeightDerivClosedForm"
    ),
    "step22OmegaArchWeightDerivClosedForm_differentiableAt": (
        "theorem step22OmegaArchWeightDerivClosedForm_differentiableAt"
    ),
    "step22OmegaArchWeight_deriv_eq_closedForm": (
        "theorem step22OmegaArchWeight_deriv_eq_closedForm"
    ),
    "Step22OmegaClosedFormEndpointBoundsCert": (
        "structure Step22OmegaClosedFormEndpointBoundsCert"
    ),
    "ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound": (
        "theorem ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound"
    ),
    "step33_shift16_digamma_m6_integral_remainder_bound": (
        "theorem step33_shift16_digamma_m6_integral_remainder_bound"
    ),
}

TARGET_SYMBOLS = [
    TARGET_CERT,
    TARGET_VALID,
    TARGET_BOUND,
    TARGET_CENTER_BRIDGE,
    TARGET_VALID_OF_ORDER16,
    FIRST_FAILURE,
    ORDER16_FAILURE,
]

TARGET_PATTERNS = {
    TARGET_CERT: "structure Step33Sub0OmegaPrimeTaylorRemainderCert",
    TARGET_VALID: "structure Valid (data : Step33Sub0OmegaPrimeTaylorRemainderCert)",
    TARGET_BOUND: "theorem Valid.bound",
    TARGET_CENTER_BRIDGE: "theorem centerTaylorBridge_of_order16_bound",
    TARGET_VALID_OF_ORDER16: "theorem Valid.of_order16_bound",
    FIRST_FAILURE: FIRST_FAILURE,
    ORDER16_FAILURE: ORDER16_FAILURE,
}


def file_hash(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def line_of_symbol(path: Path, symbol: str) -> int | None:
    if not path.exists():
        return None
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if symbol in line:
            return line_no
    return None


def symbol_scan(path_by_label: dict[str, Path]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = {}
    for label, symbols in SOURCE_SYMBOLS.items():
        path = path_by_label[label]
        out[label] = []
        for symbol in symbols:
            line = line_of_symbol(path, SOURCE_PATTERNS.get(symbol, symbol))
            out[label].append(
                {
                    "symbol": symbol,
                    "line": line,
                    "status": "found" if line is not None else "missing",
                }
            )
    return out


def target_symbol_scan(path: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for symbol in TARGET_SYMBOLS:
        line = line_of_symbol(path, TARGET_PATTERNS.get(symbol, symbol))
        out[symbol] = {
            "line": line,
            "status": "found" if line is not None else "gap",
        }
    return out


def missing_coeff_slots(name: str) -> list[dict[str, Any]]:
    return [
        {
            "index": index,
            "value": None,
            "status": f"missing_proof_grade_{name}",
        }
        for index in range(DEGREE + 1)
    ]


def build_report(
    *,
    chunk_file: Path,
    endpoint_file: Path,
    component_payload_path: Path,
    gap_map_path: Path,
) -> dict[str, Any]:
    path_by_label = {
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean": chunk_file,
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean": endpoint_file,
    }
    component_payload = load_json(component_payload_path)
    target_scan = target_symbol_scan(endpoint_file)
    receiver_present = all(
        target_scan[symbol]["status"] == "found"
        for symbol in [TARGET_CERT, TARGET_VALID, TARGET_BOUND]
    )
    centered_bridge_present = all(
        target_scan[symbol]["status"] == "found"
        for symbol in [TARGET_CENTER_BRIDGE, TARGET_VALID_OF_ORDER16]
    )

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": STATUS,
        "firstFailure": FIRST_FAILURE,
        "failureCodes": [
            FIRST_FAILURE,
            ORDER16_FAILURE,
            "STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SOURCE_GAP",
            "STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_GAP",
            "STEP33_A1_SUB0_OMEGAPRIME_TAYLOR_LEAN_PAYLOAD_MISSING",
        ],
        "generator": GENERATOR_NAME,
        "functionId": FUNCTION_ID,
        "cell": {
            "cellL": CELL_L,
            "cellU": CELL_U,
            "center": CENTER,
            "radius": RADIUS,
            "degree": DEGREE,
            "orderForLagrangeRemainder": ORDER,
        },
        "targetLeanSurface": {
            "file": LEAN_TARGET_FILE,
            "structure": TARGET_CERT,
            "validPredicate": TARGET_VALID,
            "boundTheorem": TARGET_BOUND,
            "centerTaylorBridgeTheorem": TARGET_CENTER_BRIDGE,
            "validOfOrder16Theorem": TARGET_VALID_OF_ORDER16,
            "status": (
                "receiver_and_centered_taylor_bridge_present_missing_payload"
                if receiver_present and centered_bridge_present
                else "receiver_present_missing_centered_taylor_bridge"
                if receiver_present
                else "planned_not_in_lean"
            ),
            "statementAscii": (
                "theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound "
                "{data : Step33Sub0OmegaPrimeTaylorRemainderCert} "
                "(h : data.Valid) : forall eta in Set.Icc 0 (1/10), "
                "norm (step22OmegaArchWeightDerivClosedForm eta - data.poly eta) "
                "<= data.remainderAbs"
            ),
            "localNormalization": (
                "rawOmegaATaylorPolynomial expects a Rat center and a "
                "Fin (degree + 1) -> Rat coefficient function."
            ),
            "nextBridgeStatementAscii": (
                "theorem Step33Sub0OmegaPrimeTaylorRemainderCert."
                "centerTaylorBridge_of_order16_bound "
                "(data : Step33Sub0OmegaPrimeTaylorRemainderCert) "
                "(hSmooth : ContDiff Real 16 step22OmegaArchWeightDerivClosedForm) "
                "(hCenterJet : center coefficient enclosures) "
                "(hOrder16 : forall eta in [0,1/10], "
                "norm (iteratedDeriv 16 step22OmegaArchWeightDerivClosedForm eta) "
                "<= data.order16Abs) "
                "(hBudget : coefficient plus Lagrange budget <= data.remainderAbs) : "
                "forall eta in [0,1/10], "
                "norm (step22OmegaArchWeightDerivClosedForm eta - exactTaylorPoly eta) "
                "<= data.order16Abs * radius^16 / 16!"
            ),
        },
        "generatorFields": {
            "schemaVersion": SCHEMA,
            "functionId": FUNCTION_ID,
            "center": CENTER,
            "radius": RADIUS,
            "degree": DEGREE,
            "coeff": missing_coeff_slots("coefficient_enclosure"),
            "coeffErrorAbs": missing_coeff_slots("coefficient_error_bound"),
            "order16Abs": None,
            "coefficientErrorBudget": None,
            "lagrangeRemainderBudget": None,
            "remainderAbs": None,
            "centerJetSource": missing_coeff_slots("center_jet_source"),
            "order16BoundSource": None,
            "exactRationalChecksPassed": False,
            "proofSafeClosedFields": 0,
            "outLeanWritten": False,
        },
        "requiredProofs": [
            (
                "prove the centered Taylor bridge from a uniform order-16 "
                "bound: right half by taylor_mean_remainder_bound, left half "
                "by reflecting x |-> 1/10 - x"
            ),
            (
                "prove the reflected iterated derivative identity "
                "iteratedDeriv n (fun x => f (1/10 - x)) x = "
                "(-1)^n * iteratedDeriv n f (1/10 - x)"
            ),
            (
                "for each j < 16, prove |iteratedDeriv j "
                "step22OmegaArchWeightDerivClosedForm (1/20) / j! - coeff[j]| "
                "<= coeffErrorAbs[j]"
            ),
            (
                "prove forall eta in [0, 1/10], |iteratedDeriv 16 "
                "step22OmegaArchWeightDerivClosedForm eta| <= order16Abs"
            ),
            (
                "prove sum_j coeffErrorAbs[j] * radius^j + "
                "order16Abs * radius^16 / 16! <= remainderAbs"
            ),
        ],
        "proofStatus": {
            "componentTaylorBoundsProved": False,
            "centeredTaylorBridgeProved": False,
            "reflectedIteratedDerivBridgeProved": False,
            "omegaPrimeCenterJetBoundsProved": False,
            "omegaPrimeOrder16BoundProved": False,
            "omegaPrimeRemainderBudgetPassed": False,
            "exactRationalChecksPassed": False,
            "proofSafeClosedFields": 0,
            "outLeanWritten": False,
        },
        "localSourceScan": symbol_scan(path_by_label),
        "targetSymbolScan": target_scan,
        "sourceStatus": {
            "componentPayloadPath": str(component_payload_path),
            "componentPayloadSchema": (
                component_payload.get("schema") if component_payload else None
            ),
            "componentPayloadStatus": (
                component_payload.get("status") if component_payload else None
            ),
            "componentPayloadFirstFailure": (
                component_payload.get("firstFailure") if component_payload else None
            ),
            "gapMapPath": str(gap_map_path),
            "gapMapExists": gap_map_path.exists(),
        },
        "sourceDefinitionHashes": {
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean": file_hash(
                chunk_file
            ),
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean": file_hash(
                endpoint_file
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_component_taylor_residual_payload.json": file_hash(
                component_payload_path
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_omega_omegaprime_taylor_remainder_gap.md": file_hash(
                gap_map_path
            ),
        },
        "advisorySource": {
            "browserProshka": "advisory_only_not_proof_evidence",
            "chosen": "A",
            "recommendedLeanBridge": TARGET_CENTER_BRIDGE,
            "recommendedGenerator": GENERATOR_NAME,
            "firstFailure": FIRST_FAILURE,
            "nextFailureAfterBridge": ORDER16_FAILURE,
            "whyNotEndpointFiniteCover": (
                "Endpoint finite-cover subdivision still needs the same "
                "trigamma/polygamma source bounds, repeated over segments."
            ),
        },
        "externalSearch": {
            "mathlibTaylorDocs": (
                "Mathlib.Analysis.Calculus.Taylor exposes Taylor theorem "
                "surfaces such as taylor_mean_remainder_lagrange; this is "
                "route context only until imported and checked locally."
            ),
            "localMathlibReflectionHints": (
                "Local Mathlib has iteratedDeriv_comp_neg, "
                "iteratedDeriv_comp_const_add, and "
                "iteratedDeriv_comp_add_const in IteratedDeriv/Lemmas.lean; "
                "the exact reflected bridge is not yet proved in this repo."
            ),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Sub0 OmegaPrime Taylor Payload",
        "",
        "Fail-closed payload surface. This is not Lean proof data and does",
        "not close Step33A.1-A.",
        "",
        "## Status",
        "",
        f"- schema: `{report['schema']}`",
        f"- route: `{report['routeId']}`",
        f"- status: `{report['status']}`",
        f"- first failure: `{report['firstFailure']}`",
        f"- function: `{report['functionId']}`",
        f"- center: `{report['cell']['center']}`",
        f"- radius: `{report['cell']['radius']}`",
        f"- degree: `{report['cell']['degree']}`",
        f"- proof-safe closed fields: `{report['proofStatus']['proofSafeClosedFields']}`",
        f"- Lean emitted: `{report['proofStatus']['outLeanWritten']}`",
        "",
        "## Target Lean Surface",
        "",
        f"- file: `{report['targetLeanSurface']['file']}`",
        f"- structure: `{report['targetLeanSurface']['structure']}`",
        f"- valid predicate: `{report['targetLeanSurface']['validPredicate']}`",
        f"- bound theorem: `{report['targetLeanSurface']['boundTheorem']}`",
        f"- centered bridge theorem: `{report['targetLeanSurface']['centerTaylorBridgeTheorem']}`",
        f"- valid constructor: `{report['targetLeanSurface']['validOfOrder16Theorem']}`",
        f"- status: `{report['targetLeanSurface']['status']}`",
        "",
        "```text",
        report["targetLeanSurface"]["statementAscii"],
        "```",
        "",
        "Next bridge surface:",
        "",
        "```text",
        report["targetLeanSurface"]["nextBridgeStatementAscii"],
        "```",
        "",
        "Normalization note:",
        "",
        f"`{report['targetLeanSurface']['localNormalization']}`",
        "",
        "## Required Fields",
        "",
        "- `coeff[0..15]`",
        "- `coeffErrorAbs[0..15]`",
        "- `order16Abs`",
        "- `coefficientErrorBudget`",
        "- `lagrangeRemainderBudget`",
        "- `remainderAbs`",
        "- `centerJetSource[0..15]`",
        "- `order16BoundSource`",
        "- `exactRationalChecksPassed`",
        "- `sourceDefinitionHashes`",
        "- `proofSafeClosedFields`",
        "- `outLeanWritten`",
        "- `failureCodes[]`",
        "",
        "## Required Proofs",
        "",
    ]
    for item in report["requiredProofs"]:
        lines.append(f"- {item}")

    lines.extend(
        [
            "",
            "## Local Source Scan",
            "",
        ]
    )
    for file_name, items in report["localSourceScan"].items():
        lines.extend(["", f"### {file_name}", ""])
        lines.append("| symbol | line | status |")
        lines.append("| --- | --- | --- |")
        for item in items:
            lines.append(
                f"| `{item['symbol']}` | `{item['line']}` | `{item['status']}` |"
            )

    lines.extend(
        [
            "",
            "## Target Symbol Scan",
            "",
            "| symbol | line | status |",
            "| --- | --- | --- |",
        ]
    )
    for symbol, info in report["targetSymbolScan"].items():
        lines.append(f"| `{symbol}` | `{info['line']}` | `{info['status']}` |")

    lines.extend(
        [
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
            "The next proof-producing step is not endpoint subdivision and not",
            "a full residual interval payload.  It is the centered Taylor",
            "bridge from the uniform order-16 bound.  The right half can use",
            "`taylor_mean_remainder_bound`; the left half needs a reflected",
            "iterated-derivative bridge for `x |-> 1/10 - x` before the",
            "order-16/polygamma payload can be spent.",
            "",
            "Until that exists locally, the correct fail code is:",
            "",
            "```text",
            report["firstFailure"],
            "```",
            "",
        ]
    )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk-file", type=Path, default=CHUNK_FILE)
    parser.add_argument("--endpoint-file", type=Path, default=ENDPOINT_HIGH_ORDER_FILE)
    parser.add_argument("--component-payload", type=Path, default=COMPONENT_PAYLOAD)
    parser.add_argument("--gap-map", type=Path, default=GAP_MAP)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(
        chunk_file=args.chunk_file,
        endpoint_file=args.endpoint_file,
        component_payload_path=args.component_payload,
        gap_map_path=args.gap_map,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} first_failure={failure} out_json={out_json}".format(
            status=report["status"],
            failure=report["firstFailure"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
