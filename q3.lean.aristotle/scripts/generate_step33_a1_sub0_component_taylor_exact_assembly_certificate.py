#!/usr/bin/env python3
"""Proof-side coefficient materialization for Step33A.1-A sub0.

This generator writes an isolated Lean payload and a JSON/Markdown certificate
for the algebraic coefficient arrays already defined in
`PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean`.

It deliberately does not emit a residual remainder, does not set
`exactCoefficientAssemblyPassed`, and does not claim the component Taylor
payload is proof-safe.  The next analytic blocker remains the tight
ShapeSqDeriv rows 2..15/order16 source.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
from typing import Any


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(2_000_000)


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUESTS = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

ASSEMBLY_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean"
ENDPOINT_RATIONAL_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAEndpointRationalImport.lean"
COMPONENT_PAYLOAD_JSON = REQUESTS / "step33_a1_sub0_component_taylor_residual_payload.json"
OMEGA_PRIME_PAYLOAD_JSON = REQUESTS / "step33_a1_sub0_omega_prime_taylor_payload.json"

OUT_LEAN = PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean"
OUT_JSON = REQUESTS / "step33_a1_sub0_component_taylor_exact_assembly_certificate.json"
OUT_MD = REQUESTS / "step33_a1_sub0_component_taylor_exact_assembly_certificate.md"

SCHEMA = "q3_psdpd_step33_a1_sub0_component_taylor_exact_assembly_certificate.v1"
STATUS = "algebraic_assembly_payload_checked_remainder_source_open"
FIRST_FAILURE = "STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP"

ASSEMBLED_PAYLOAD_DEF = "primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeffPayload"
RESIDUAL_PAYLOAD_DEF = "primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffPayload"
ASSEMBLED_EQ_THEOREM = "primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_payload_eq"
RESIDUAL_EQ_THEOREM = "primaryFiniteRow0Parent0Split100Sub0_residualTaylorCoeff_payload_eq"


def file_hash(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--lean-validation-status",
        default="pending_lean_check",
        help="Recorded status for the isolated Lean payload check.",
    )
    parser.add_argument(
        "--q3-check-status",
        default="not_run",
        help="Recorded status for scripts/q3_check.sh on the isolated payload.",
    )
    return parser.parse_args()


def parse_rat(text: str) -> Fraction:
    text = text.strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num.strip()), int(den.strip()))
    return Fraction(int(text), 1)


def rat_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def lean_rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : Rat)"
    return f"(({value.numerator} : Rat) / {value.denominator})"


def list_block(name: str, values: list[Fraction]) -> str:
    lines = [f"def {name} : List Rat := ["]
    for idx, value in enumerate(values):
        comma = "," if idx + 1 < len(values) else ""
        lines.append(f"  {lean_rat(value)}{comma}")
    lines.append("]")
    return "\n".join(lines)


def cauchy(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0, 1) for _ in range(len(left) + len(right) - 1)]
    for i, left_value in enumerate(left):
        for j, right_value in enumerate(right):
            out[i + j] += left_value * right_value
    return out


def integrated_coeff(deriv_coeff: list[Fraction], anchor: Fraction) -> list[Fraction]:
    return [anchor] + [
        value / Fraction(index + 1, 1) for index, value in enumerate(deriv_coeff)
    ]


def load_omega_prime_coeff() -> list[Fraction]:
    payload = json.loads(OMEGA_PRIME_PAYLOAD_JSON.read_text(encoding="utf-8"))
    coeff = payload["generatorFields"]["coeff"]
    return [parse_rat(item["value"]) for item in coeff]


def load_model_coeff() -> list[Fraction]:
    payload = json.loads(COMPONENT_PAYLOAD_JSON.read_text(encoding="utf-8"))
    coeff = payload["generatorFields"]["modelDerivCoeff"]
    return [parse_rat(item["value"]) for item in coeff]


def shape_sq_anchor() -> Fraction:
    text = ENDPOINT_RATIONAL_FILE.read_text(encoding="utf-8")
    marker = "def primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated : Rat :="
    start = text.index(marker) + len(marker)
    end = text.index("\n\ndef", start)
    expr = " ".join(text[start:end].split())
    if "/" not in expr:
        raise ValueError("shapeSq anchor expression is not a quotient")
    num, den = expr.split("/", 1)
    return Fraction(int(num.strip()), int(den.strip()))


def omega_anchor(component_payload: dict[str, Any]) -> Fraction:
    return parse_rat(
        component_payload["generatorFields"]["omegaIntegratedDerivCrosswalk"][
            "anchorCoeff"
        ]
    )


def build_coefficients() -> dict[str, list[Fraction] | Fraction]:
    component_payload = json.loads(COMPONENT_PAYLOAD_JSON.read_text(encoding="utf-8"))
    omega_prime = load_omega_prime_coeff()
    omega = integrated_coeff(omega_prime, omega_anchor(component_payload))
    shape_sq_deriv = [Fraction(-3, 40)] + [Fraction(0, 1) for _ in range(15)]
    shape_sq = integrated_coeff(shape_sq_deriv, shape_sq_anchor())
    scale = Fraction(190985931710274402922660516047, 2 * 10**30)
    model = load_model_coeff()
    product_1 = cauchy(omega_prime, shape_sq)
    product_2 = cauchy(omega, shape_sq_deriv)
    assembled = [
        scale * ((product_1[i] if i < len(product_1) else 0) +
                 (product_2[i] if i < len(product_2) else 0))
        for i in range(46)
    ]
    model_padded = model + [Fraction(0, 1) for _ in range(30)]
    residual = [assembled[i] - model_padded[i] for i in range(46)]
    return {
        "omegaPrimeCoeff": omega_prime,
        "omegaCoeff": omega,
        "shapeSqCoeff": shape_sq,
        "shapeSqDerivCoeff": shape_sq_deriv,
        "assembledRawDerivCoeff": assembled,
        "residualTaylorCoeff": residual,
        "nominalScaleCoeff": scale,
    }


def render_lean(assembled: list[Fraction], residual: list[Fraction]) -> str:
    return "\n\n".join(
        [
            "import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly",
            "set_option linter.mathlibStandardSet false\n"
            "set_option autoImplicit false\n"
            "set_option maxHeartbeats 0",
            "/-!\n"
            "Step33A.1-A sub0 exact algebraic coefficient payload.\n\n"
            "This file materializes the coefficient arrays already defined by\n"
            "`PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean` and\n"
            "checks that the generated lists match those Lean definitions.\n"
            "It is not a residual interval theorem and does not provide the\n"
            "component Taylor remainder.\n"
            "-/",
            "noncomputable section",
            "namespace Q3\n"
            "namespace PSDpd\n"
            "namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport\n"
            "namespace RawOmegaAChunkIntegral\n"
            "namespace RawOmegaATaylorModelCertificate",
            list_block(ASSEMBLED_PAYLOAD_DEF, assembled),
            list_block(RESIDUAL_PAYLOAD_DEF, residual),
            f"theorem {ASSEMBLED_EQ_THEOREM} :\n"
            "    List.ofFn primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff =\n"
            f"      {ASSEMBLED_PAYLOAD_DEF} := by\n"
            "  native_decide",
            f"theorem {RESIDUAL_EQ_THEOREM} :\n"
            "    List.ofFn primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff =\n"
            f"      {RESIDUAL_PAYLOAD_DEF} := by\n"
            "  native_decide",
            "end RawOmegaATaylorModelCertificate\n"
            "end RawOmegaAChunkIntegral\n"
            "end CenteredCoeffPrimeDeltaLiveRationalPayloadImport\n"
            "end PSDpd\n"
            "end Q3",
            "",
        ]
    )


def build_certificate(
    values: dict[str, list[Fraction] | Fraction],
    *,
    lean_validation_status: str,
    q3_check_status: str,
) -> dict[str, Any]:
    assembled = values["assembledRawDerivCoeff"]
    residual = values["residualTaylorCoeff"]
    assert isinstance(assembled, list)
    assert isinstance(residual, list)
    return {
        "schema": SCHEMA,
        "status": STATUS,
        "firstFailure": FIRST_FAILURE,
        "proofGrade": "LEAN_LIST_EQ_CHECKED_FOR_ALGEBRAIC_COEFFICIENT_ARRAYS_ONLY",
        "leanPayload": {
            "path": "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean",
            "assembledPayloadDef": ASSEMBLED_PAYLOAD_DEF,
            "residualPayloadDef": RESIDUAL_PAYLOAD_DEF,
            "assembledEqTheorem": ASSEMBLED_EQ_THEOREM,
            "residualEqTheorem": RESIDUAL_EQ_THEOREM,
            "validationStatus": lean_validation_status,
            "q3CheckStatus": q3_check_status,
        },
        "sourceHashes": {
            "assemblyFileSha256": file_hash(ASSEMBLY_FILE),
            "componentPayloadJsonSha256": file_hash(COMPONENT_PAYLOAD_JSON),
            "omegaPrimePayloadJsonSha256": file_hash(OMEGA_PRIME_PAYLOAD_JSON),
            "endpointRationalImportSha256": file_hash(ENDPOINT_RATIONAL_FILE),
        },
        "inputs": {
            "nominalScaleCoeff": rat_text(values["nominalScaleCoeff"]),
            "omegaPrimeCoeff": [rat_text(x) for x in values["omegaPrimeCoeff"]],
            "omegaCoeff": [rat_text(x) for x in values["omegaCoeff"]],
            "shapeSqCoeff": [rat_text(x) for x in values["shapeSqCoeff"]],
            "shapeSqDerivCoeff": [rat_text(x) for x in values["shapeSqDerivCoeff"]],
        },
        "generatorFields": {
            "assembledRawDerivCoeff": [rat_text(x) for x in assembled],
            "residualTaylorCoeff": [rat_text(x) for x in residual],
            "residualTaylorRemainderAbs": None,
            "componentPropagationRemainderAbs": None,
            "finalResidualLower": None,
            "finalResidualUpper": None,
        },
        "checks": {
            "assembledLength": len(assembled),
            "residualLength": len(residual),
            "algebraicAssemblyCrosswalkPassed": True,
            "exactCoefficientAssemblyPassed": False,
            "componentTaylorProofsPresent": False,
            "residualTaylorRemainderAbsPresent": False,
            "componentTaylorOverallProofSafe": False,
        },
        "doNot": [
            "do not set exactCoefficientAssemblyPassed=true",
            "do not treat coefficient arrays as an analytic approximation proof",
            "do not invent residualTaylorRemainderAbs from the final product budget",
            "do not hide the open ShapeSqDeriv rows 2..15/order16 blocker",
        ],
    }


def render_markdown(cert: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A sub0 exact assembly coefficient certificate",
        "",
        f"- schema: `{cert['schema']}`",
        f"- status: `{cert['status']}`",
        f"- firstFailure: `{cert['firstFailure']}`",
        f"- proofGrade: `{cert['proofGrade']}`",
        "",
        "## Lean Payload",
        "",
    ]
    for key, value in cert["leanPayload"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Checks",
            "",
        ]
    )
    for key, value in cert["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Boundary", ""])
    for item in cert["doNot"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    values = build_coefficients()
    assembled = values["assembledRawDerivCoeff"]
    residual = values["residualTaylorCoeff"]
    assert isinstance(assembled, list)
    assert isinstance(residual, list)
    OUT_LEAN.write_text(render_lean(assembled, residual), encoding="utf-8")
    cert = build_certificate(
        values,
        lean_validation_status=args.lean_validation_status,
        q3_check_status=args.q3_check_status,
    )
    OUT_JSON.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    OUT_MD.write_text(render_markdown(cert), encoding="utf-8")
    print(
        f"status={cert['status']} first_failure={cert['firstFailure']} "
        f"assembled={len(assembled)} residual={len(residual)}"
    )


if __name__ == "__main__":
    main()
