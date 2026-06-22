#!/usr/bin/env python3
"""Fail-closed component assembly coefficient-stream ledger.

This generator records the first proof-moving patch selected by the
browser/Proshka review after the tight ShapeSqDeriv audit:

    assembledRawDerivCoeff =
      scale * (cauchy(omegaPrimeCoeff, shapeSqCoeff)
        + cauchy(omegaCoeff, shapeSqDerivCoeff))

    residualTaylorCoeff =
      assembledRawDerivCoeff - zeroExtend15(ResidualDerivmodelCoeff)

It deliberately emits no Lean.  It fails closed until the repository contains
a checked component assembly/crosswalk theorem tying the component coefficient
stream to the active RawTaylorCoeffCert residual convention.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUESTS = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

LANDING_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAHRawLanding.lean"
CHUNK_CHECKER_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean"
COMPONENT_PAYLOAD_JSON = (
    REQUESTS / "step33_a1_sub0_component_taylor_residual_payload.json"
)
TIGHT_PAYLOAD_JSON = REQUESTS / "step33_a1_sub0_shapesq_deriv_tight_payload.json"
OUTPUT_JSON = REQUESTS / "step33_a1_sub0_component_assembly_stream_ledger.json"
OUTPUT_MD = REQUESTS / "step33_a1_sub0_component_assembly_stream_ledger.md"

SCHEMA = "q3_psdpd_step33_a1_sub0_component_assembly_stream_ledger.v1"
STATUS = "fail_closed_active_model_coeff_crosswalk_not_checked"
FIRST_FAILURE = "STEP33_A1_SUB0_COMPONENT_TAYLOR_ACTIVE_MODEL_COEFF_MISMATCH"
RAW_ASSEMBLY_GAP = "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_GAP"
TIGHT_ROUTE_GAP = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP"
)

RAW_INTEGRAND_DERIV = "primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm"
RESIDUAL_MODEL = "primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff"
RAW_TAYLOR_CERT = "primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert"
POLY_CROSSWALK = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel"
)
RESIDUAL_CROSSWALK = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm"
)
RAW_OMEGA_TAYLOR_POLY = "rawOmegaATaylorPolynomial"
INTEGRATED_TAYLOR_COEFF = "integratedTaylorCoeff"
SHAPESQ_INTEGRATED_RECEIVER = "shapeSqTaylor_bound_of_shapeSqDerivTaylor_bound"
SHAPESQ_DERIV_CERT = "ShapeSqDerivTaylorIntervalCert"

TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "componentTaylor_residualCoeff_crosswalk"
)
ASSEMBLED_COEFF = "primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff"
RESIDUAL_COEFF = "primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff"
ASSEMBLED_DEGREE = "primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree"


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def line_of(text: str, needle: str) -> int | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        if needle in line:
            return idx
    return None


def source_symbols(path: Path, text: str, symbols: list[str]) -> dict[str, Any]:
    return {
        "path": str(path.relative_to(ROOT)),
        "exists": path.exists(),
        "symbols": {
            symbol: {
                "found": symbol in text,
                "line": line_of(text, symbol),
            }
            for symbol in symbols
        },
    }


def nested_get(data: dict[str, Any] | None, path: list[str], default: Any = None) -> Any:
    cur: Any = data
    for key in path:
        if not isinstance(cur, dict) or key not in cur:
            return default
        cur = cur[key]
    return cur


def proof_status(component: dict[str, Any] | None, key: str) -> Any:
    return nested_get(component, ["proofStatus", key])


def has_checked_crosswalk(landing_text: str) -> bool:
    return TARGET_THEOREM in landing_text


def component_field_state(component: dict[str, Any] | None) -> dict[str, Any]:
    generator_fields = component.get("generatorFields", {}) if component else {}
    component_status = component.get("componentTaylorStatus", {}) if component else {}
    proof = component.get("proofStatus", {}) if component else {}
    return {
        "payloadExists": component is not None,
        "payloadSchema": component.get("schema") if component else None,
        "payloadStatus": component.get("status") if component else None,
        "payloadFirstFailure": component.get("firstFailure") if component else None,
        "componentTaylorAssemblyLeanWritten": component_status.get(
            "assemblyLeanWritten"
        ),
        "componentTaylorOverallProofSafe": component_status.get("overallProofSafe"),
        "exactCoefficientAssemblyPassed": proof.get("exactCoefficientAssemblyPassed"),
        "componentTaylorProofsPresent": proof.get("componentTaylorProofsPresent"),
        "omegaDerivTaylorProofPresent": proof.get("omegaDerivTaylorProofPresent"),
        "omegaTaylorIntegratedPolyDerivCrosswalkProofPresent": proof.get(
            "omegaTaylorIntegratedPolyDerivCrosswalkProofPresent"
        ),
        "omegaTaylorCenterAnchorPayloadPresent": proof.get(
            "omegaTaylorCenterAnchorPayloadPresent"
        ),
        "shapeSqDerivCenterCoeffRowsClosedCount": proof.get(
            "shapeSqDerivCenterCoeffRowsClosedCount"
        ),
        "shapeSqDerivCenterCoeffRowsRequiredCount": proof.get(
            "shapeSqDerivCenterCoeffRowsRequiredCount"
        ),
        "shapeSqDerivOrder16UniformBoundPresent": proof.get(
            "shapeSqDerivOrder16UniformBoundPresent"
        ),
        "assembledRawDerivCoeffPresent": generator_fields.get(
            "assembledRawDerivCoeff"
        )
        is not None,
        "residualTaylorCoeffPresent": generator_fields.get("residualTaylorCoeff")
        is not None,
        "residualTaylorRemainderAbsPresent": generator_fields.get(
            "residualTaylorRemainderAbs"
        )
        is not None,
    }


def build_report() -> dict[str, Any]:
    landing_text = read_text(LANDING_FILE)
    checker_text = read_text(CHUNK_CHECKER_FILE)
    component = load_json(COMPONENT_PAYLOAD_JSON)
    tight = load_json(TIGHT_PAYLOAD_JSON)

    checked_crosswalk = has_checked_crosswalk(landing_text)
    fields = component_field_state(component)
    guard_passes = bool(
        checked_crosswalk
        and fields["assembledRawDerivCoeffPresent"]
        and fields["residualTaylorCoeffPresent"]
        and fields["exactCoefficientAssemblyPassed"]
    )

    return {
        "schema": SCHEMA,
        "status": "candidate_ready_for_lean_validation" if guard_passes else STATUS,
        "firstFailure": None if guard_passes else FIRST_FAILURE,
        "localAssemblyGap": None if guard_passes else RAW_ASSEMBLY_GAP,
        "routeLevelGap": TIGHT_ROUTE_GAP,
        "proofBoundary": (
            "Generated audit only. No Lean theorem is emitted and Step33A.1-A "
            "is not closed."
        ),
        "browserProshkaDecision": {
            "chosen": "A_component_assembly_coefficient_stream_ledger_first",
            "firstPatchOrTheorem": TARGET_THEOREM,
            "failureCodeIfFails": FIRST_FAILURE,
            "whySmallest": (
                "Rows 2..15 can prove bounds for the correct function but "
                "still feed the wrong polynomial payload unless the component "
                "coefficient stream is first fixed in the active "
                "RawTaylorCoeffCert residual convention."
            ),
            "doNot": [
                "do not generate ShapeSqDeriv rows 2..15 before the crosswalk",
                "do not declare arbitrary ShapeSqDerivTightCoeff objects",
                "do not move to the direct residual interval theorem",
                "do not add a new receiver",
                "do not set componentTaylorProofsPresent=true without Lean check",
            ],
        },
        "targetTheoremContract": {
            "name": TARGET_THEOREM,
            "file": "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean",
            "status": "NOT_WRITTEN",
            "statementAscii": (
                "rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) "
                "AssembledRawDerivCoeff eta - rawOmegaATaylorPolynomial 15 "
                "(1/20) ResidualDerivmodelCoeff eta = rawOmegaATaylorPolynomial "
                "AssembledRawDerivDegree (1/20) ResidualTaylorCoeff eta"
            ),
            "coeffDefinitionsRequired": [
                ASSEMBLED_DEGREE,
                ASSEMBLED_COEFF,
                RESIDUAL_COEFF,
            ],
        },
        "componentAssemblyFormula": {
            "scale": "((3 : Real) / 10) / Real.pi",
            "rawClosedForm": (
                "scale * (omegaPrime * shapeSq + omega * shapeSqDeriv)"
            ),
            "assembledRawDerivCoeffFormula": (
                "scale * (cauchy(omegaPrimeCoeff, shapeSqCoeff) + "
                "cauchy(omegaCoeff, shapeSqDerivCoeff))"
            ),
            "residualTaylorCoeffFormula": (
                "assembledRawDerivCoeff - "
                "zeroExtend15(ResidualDerivmodelCoeff)"
            ),
            "center": "1/20",
            "componentDegree": 15,
            "assembledDegree": 45,
            "normalizationWarning": (
                "Do not identify a ShapeSqDeriv coefficient stream with the "
                "active residual coefficient stream. It feeds through the "
                "product assembly with omega and omegaPrime first."
            ),
        },
        "sourceFiles": {
            "landing": source_symbols(
                LANDING_FILE,
                landing_text,
                [
                    RAW_INTEGRAND_DERIV,
                    RAW_TAYLOR_CERT,
                    RESIDUAL_MODEL,
                    POLY_CROSSWALK,
                    RESIDUAL_CROSSWALK,
                    TARGET_THEOREM,
                    ASSEMBLED_COEFF,
                    RESIDUAL_COEFF,
                ],
            ),
            "chunkTaylorChecker": source_symbols(
                CHUNK_CHECKER_FILE,
                checker_text,
                [
                    RAW_OMEGA_TAYLOR_POLY,
                    INTEGRATED_TAYLOR_COEFF,
                    SHAPESQ_INTEGRATED_RECEIVER,
                    SHAPESQ_DERIV_CERT,
                ],
            ),
            "componentPayload": {
                "path": str(COMPONENT_PAYLOAD_JSON.relative_to(ROOT)),
                "exists": COMPONENT_PAYLOAD_JSON.exists(),
                "schema": component.get("schema") if component else None,
                "status": component.get("status") if component else None,
                "firstFailure": component.get("firstFailure") if component else None,
            },
            "tightPayload": {
                "path": str(TIGHT_PAYLOAD_JSON.relative_to(ROOT)),
                "exists": TIGHT_PAYLOAD_JSON.exists(),
                "schema": tight.get("schema") if tight else None,
                "status": tight.get("status") if tight else None,
                "firstFailure": tight.get("firstFailure") if tight else None,
            },
        },
        "currentComponentFieldState": fields,
        "guard": {
            "checkedCrosswalkTheoremPresent": checked_crosswalk,
            "assembledRawDerivCoeffPresent": fields["assembledRawDerivCoeffPresent"],
            "residualTaylorCoeffPresent": fields["residualTaylorCoeffPresent"],
            "exactCoefficientAssemblyPassed": fields[
                "exactCoefficientAssemblyPassed"
            ],
            "guardPasses": guard_passes,
        },
        "decision": {
            "canGenerateRows2To15Now": False,
            "canEmitLeanCrosswalkNow": False,
            "nextPatch": (
                "Build the exact rational coefficient definitions and the Lean "
                "crosswalk for component assembly in the active residual model "
                "convention, then return to tight ShapeSqDeriv rows."
            ),
            "downstreamAfterThisCloses": [
                "generate proof-grade ShapeSqDeriv rows 2..15 and order16",
                "prove primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid",
                "assemble raw derivative residual interval payload",
                "prove the final direct residual interval theorem",
            ],
        },
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Step33A.1-A Sub0 Component Assembly Stream Ledger",
        "",
        f"Schema: `{report['schema']}`",
        "",
        f"Status: `{report['status']}`",
        "",
        f"First failure: `{report['firstFailure']}`",
        "",
        f"Local assembly gap: `{report['localAssemblyGap']}`",
        "",
        f"Route-level gap: `{report['routeLevelGap']}`",
        "",
        f"Boundary: {report['proofBoundary']}",
        "",
        "## Browser/Proshka Decision",
        "",
    ]
    decision = report["browserProshkaDecision"]
    lines.append(f"- chosen: `{decision['chosen']}`")
    lines.append(f"- first patch/theorem: `{decision['firstPatchOrTheorem']}`")
    lines.append(f"- failure code if fails: `{decision['failureCodeIfFails']}`")
    lines.append(f"- why smallest: {decision['whySmallest']}")
    lines.append("")
    lines.append("Do not:")
    for item in decision["doNot"]:
        lines.append(f"- {item}")

    target = report["targetTheoremContract"]
    lines.extend(
        [
            "",
            "## Target Theorem Contract",
            "",
            f"- name: `{target['name']}`",
            f"- file: `{target['file']}`",
            f"- status: `{target['status']}`",
            "",
            "```text",
            target["statementAscii"],
            "```",
            "",
            "Required coefficient definitions:",
        ]
    )
    for name in target["coeffDefinitionsRequired"]:
        lines.append(f"- `{name}`")

    formula = report["componentAssemblyFormula"]
    lines.extend(
        [
            "",
            "## Assembly Formula",
            "",
            f"- scale: `{formula['scale']}`",
            f"- raw closed form: `{formula['rawClosedForm']}`",
            f"- assembled raw derivative coeff: `{formula['assembledRawDerivCoeffFormula']}`",
            f"- residual Taylor coeff: `{formula['residualTaylorCoeffFormula']}`",
            f"- center: `{formula['center']}`",
            f"- component degree: `{formula['componentDegree']}`",
            f"- assembled degree: `{formula['assembledDegree']}`",
            f"- warning: {formula['normalizationWarning']}",
            "",
            "## Source Files",
            "",
        ]
    )
    for source_name, source in report["sourceFiles"].items():
        lines.append(f"### {source_name}")
        lines.append("")
        lines.append(f"- path: `{source['path']}`")
        lines.append(f"- exists: `{source['exists']}`")
        if "symbols" in source:
            for sym, info in source["symbols"].items():
                lines.append(
                    f"- `{sym}`: found=`{info['found']}`, line=`{info['line']}`"
                )
        else:
            for key in ["schema", "status", "firstFailure"]:
                lines.append(f"- {key}: `{source[key]}`")
        lines.append("")

    lines.extend(["## Current Component Field State", ""])
    for key, value in report["currentComponentFieldState"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Guard", ""])
    for key, value in report["guard"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Decision", ""])
    final_decision = report["decision"]
    lines.append(
        f"- can generate rows 2..15 now: `{final_decision['canGenerateRows2To15Now']}`"
    )
    lines.append(
        f"- can emit Lean crosswalk now: `{final_decision['canEmitLeanCrosswalkNow']}`"
    )
    lines.append(f"- next patch: {final_decision['nextPatch']}")
    lines.append("")
    lines.append("Downstream after this closes:")
    for item in final_decision["downstreamAfterThisCloses"]:
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
        "status={status} first_failure={failure}".format(
            status=report["status"],
            failure=report["firstFailure"],
        )
    )


if __name__ == "__main__":
    main()
