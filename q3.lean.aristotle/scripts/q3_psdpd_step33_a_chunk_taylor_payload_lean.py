#!/usr/bin/env python3
"""Guard and future Lean emitter for Step33 raw-Omega A Taylor payloads.

This script is deliberately conservative.  It consumes the proof-data schema
for `RawOmegaAChunkTaylorPayload.PayloadFin`, runs the same completeness
inventory used by the Step33 monitor, and refuses to write a Lean payload while
any proof-bearing field is missing.

The current proof-data skeleton is address-complete but proof-empty, so the
expected result today is a dry-run report with `out_lean_written = false`.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    DEFAULT_PROBE,
    DEFAULT_WORKLIST,
    PROOF_DATA_SCHEMA,
    build_inventory,
    load_json,
    validate_probe,
    validate_worklist,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_PROOF_DATA = REQUEST_DIR / "a_chunk_taylor_payload_proof_data_skeleton.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_chunk_taylor_payload_lean_emitter.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_chunk_taylor_payload_lean_emitter.md"
DEFAULT_OUT_LEAN = (
    ROOT / "Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorGeneratedPayloadImport.lean"
)

EMITTER_SCHEMA = "q3_psdpd_step33_a_chunk_taylor_payload_lean_emitter.v1"

FAMILY_ORDER = [
    "primary_finite",
    "primary_tail",
    "control_finite",
    "control_tail",
]

FAMILY_CONFIGS = {
    "primary_finite": {
        "record_field": "primaryFinite",
        "record_type": "PrimaryFiniteFin",
        "prefix": "primaryFinite",
        "block": "primary",
        "kind": "finite",
        "k": "11",
        "ell": "primaryK11Ell",
        "left": "((0 : Real) + (10 : Real) * (i.1 : Real))",
        "right": "((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))",
        "integrable": "primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left",
        "hL": "by norm_num",
        "hLU": "by norm_num",
    },
    "primary_tail": {
        "record_field": "primaryTail",
        "record_type": "PrimaryTailFin",
        "prefix": "primaryTail",
        "block": "primary",
        "kind": "tail",
        "k": "11",
        "ell": "primaryK11Ell",
        "left": "(rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))",
        "right": "(rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))",
        "integrable": "primaryK11RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left",
        "hL": "by norm_num [rawOmegaAFiniteTailCutoff]",
        "hLU": "by norm_num [rawOmegaAFiniteTailCutoff]",
    },
    "control_finite": {
        "record_field": "controlFinite",
        "record_type": "ControlFiniteFin",
        "prefix": "controlFinite",
        "block": "control",
        "kind": "finite",
        "k": "9",
        "ell": "controlK9Ell",
        "left": "((0 : Real) + (10 : Real) * (i.1 : Real))",
        "right": "((0 : Real) + (10 : Real) * ((i.1 + 1 : Nat) : Real))",
        "integrable": "controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left",
        "hL": "by norm_num",
        "hLU": "by norm_num",
    },
    "control_tail": {
        "record_field": "controlTail",
        "record_type": "ControlTailFin",
        "prefix": "controlTail",
        "block": "control",
        "kind": "tail",
        "k": "9",
        "ell": "controlK9Ell",
        "left": "(rawOmegaAFiniteTailCutoff + (10 : Real) * (i.1 : Real))",
        "right": "(rawOmegaAFiniteTailCutoff + (10 : Real) * ((i.1 + 1 : Nat) : Real))",
        "integrable": "controlK9RawOmegaAIntegrand_integrableOn_Ioc_of_nonneg_left",
        "hL": "by norm_num [rawOmegaAFiniteTailCutoff]",
        "hLU": "by norm_num [rawOmegaAFiniteTailCutoff]",
    },
}

REAL_FIELDS = {
    "chunkLower",
    "chunkUpper",
    "center",
    "radius",
    "remainder",
    "omegaLower",
    "omegaUpper",
    "shapeSqLower",
    "shapeSqUpper",
    "cosLower",
    "cosUpper",
    "rawLower",
    "rawUpper",
    "scaleLower",
    "scaleUpper",
    "polyLower",
    "polyUpper",
    "lowerSum",
    "upperSum",
}

PROOF_FIELDS = {
    "omegaLowerBound",
    "omegaUpperBound",
    "shapeSqLowerBound",
    "shapeSqUpperBound",
    "cosLowerBound",
    "cosUpperBound",
    "radiusNonneg",
    "remainderNonneg",
    "radiusLeft",
    "radiusRight",
    "componentProductLower",
    "componentProductUpper",
    "componentProductCornerLowerLLL",
    "componentProductCornerLowerLLU",
    "componentProductCornerLowerLUL",
    "componentProductCornerLowerLUU",
    "componentProductCornerLowerULL",
    "componentProductCornerLowerULU",
    "componentProductCornerLowerUUL",
    "componentProductCornerLowerUUU",
    "componentProductCornerUpperLLL",
    "componentProductCornerUpperLLU",
    "componentProductCornerUpperLUL",
    "componentProductCornerUpperLUU",
    "componentProductCornerUpperULL",
    "componentProductCornerUpperULU",
    "componentProductCornerUpperUUL",
    "componentProductCornerUpperUUU",
    "scaleLowerBound",
    "scaleUpperBound",
    "componentProductScaleCornerLowerLLLL",
    "componentProductScaleCornerLowerLLLU",
    "componentProductScaleCornerLowerLLUL",
    "componentProductScaleCornerLowerLLUU",
    "componentProductScaleCornerLowerLULL",
    "componentProductScaleCornerLowerLULU",
    "componentProductScaleCornerLowerLUUL",
    "componentProductScaleCornerLowerLUUU",
    "componentProductScaleCornerLowerULLL",
    "componentProductScaleCornerLowerULLU",
    "componentProductScaleCornerLowerULUL",
    "componentProductScaleCornerLowerULUU",
    "componentProductScaleCornerLowerUULL",
    "componentProductScaleCornerLowerUULU",
    "componentProductScaleCornerLowerUUUL",
    "componentProductScaleCornerLowerUUUU",
    "componentProductScaleCornerUpperLLLL",
    "componentProductScaleCornerUpperLLLU",
    "componentProductScaleCornerUpperLLUL",
    "componentProductScaleCornerUpperLLUU",
    "componentProductScaleCornerUpperLULL",
    "componentProductScaleCornerUpperLULU",
    "componentProductScaleCornerUpperLUUL",
    "componentProductScaleCornerUpperLUUU",
    "componentProductScaleCornerUpperULLL",
    "componentProductScaleCornerUpperULLU",
    "componentProductScaleCornerUpperULUL",
    "componentProductScaleCornerUpperULUU",
    "componentProductScaleCornerUpperUULL",
    "componentProductScaleCornerUpperUULU",
    "componentProductScaleCornerUpperUUUL",
    "componentProductScaleCornerUpperUUUU",
    "polynomialLowerBound",
    "polynomialUpperBound",
    "polynomialTermBounds",
    "polyLowerSum",
    "polyUpperSum",
    "diffLower",
    "diffUpper",
    "integralLower",
    "integralUpper",
    "lowerSum",
    "upperSum",
}

PRODUCT_CORNER_SUFFIXES = [
    "LLL",
    "LLU",
    "LUL",
    "LUU",
    "ULL",
    "ULU",
    "UUL",
    "UUU",
]

PRODUCT_CORNER_LOWER_FIELDS = [
    f"componentProductCornerLower{suffix}" for suffix in PRODUCT_CORNER_SUFFIXES
]

PRODUCT_CORNER_UPPER_FIELDS = [
    f"componentProductCornerUpper{suffix}" for suffix in PRODUCT_CORNER_SUFFIXES
]

PRODUCT_SCALE_CORNER_SUFFIXES = [
    "LLLL",
    "LLLU",
    "LLUL",
    "LLUU",
    "LULL",
    "LULU",
    "LUUL",
    "LUUU",
    "ULLL",
    "ULLU",
    "ULUL",
    "ULUU",
    "UULL",
    "UULU",
    "UUUL",
    "UUUU",
]

PRODUCT_SCALE_CORNER_LOWER_FIELDS = [
    f"componentProductScaleCornerLower{suffix}"
    for suffix in PRODUCT_SCALE_CORNER_SUFFIXES
]

PRODUCT_SCALE_CORNER_UPPER_FIELDS = [
    f"componentProductScaleCornerUpper{suffix}"
    for suffix in PRODUCT_SCALE_CORNER_SUFFIXES
]

SCALE_INTERVAL_PRODUCT_FIELDS = [
    "scaleLower",
    "scaleUpper",
    "scaleLowerBound",
    "scaleUpperBound",
    *PRODUCT_SCALE_CORNER_LOWER_FIELDS,
    *PRODUCT_SCALE_CORNER_UPPER_FIELDS,
]

POLYNOMIAL_DIRECT_FIELDS = [
    "polyLower",
    "polyUpper",
    "polynomialLowerBound",
    "polynomialUpperBound",
]

def family_summaries(inventory: dict[str, Any]) -> list[dict[str, Any]]:
    summaries = []
    for family in inventory.get("families", []):
        summaries.append(
            {
                "id": family["id"],
                "distance_rows": family["distance_rows"],
                "chunk_count": family["chunk_count"],
                "chunk_cells": family["chunk_cells"],
                "complete_rows": family["complete_rows"],
                "complete_cells": family["complete_cells"],
                "missing_cells": int(family["chunk_cells"]) - int(family["complete_cells"]),
                "first_missing_examples": family.get("examples", [])[:3],
            }
        )
    return summaries


def validate_proof_data(proof_data: dict[str, Any], path: Path) -> None:
    schema = proof_data.get("schema")
    if schema != PROOF_DATA_SCHEMA:
        raise ValueError(f"{path}: unexpected proof-data schema {schema!r}")


def decimal_to_rat_expr(value: str) -> str:
    try:
        decimal = Decimal(value)
    except InvalidOperation as exc:
        raise ValueError(f"not a decimal literal: {value!r}") from exc
    if not decimal.is_finite():
        raise ValueError(f"non-finite decimal literal: {value!r}")

    sign, digits, exponent = decimal.as_tuple()
    numerator = int("".join(str(digit) for digit in digits) or "0")
    if sign:
        numerator = -numerator
    denominator = 1
    if exponent >= 0:
        numerator *= 10**exponent
    else:
        denominator = 10 ** (-exponent)

    if denominator == 1:
        return f"({numerator} : Rat)"
    return f"(({numerator} : Rat) / ({denominator} : Rat))"


def looks_decimal(value: str) -> bool:
    try:
        Decimal(value)
    except InvalidOperation:
        return False
    return True


def lean_expr(value: Any, *, kind: str = "real") -> str:
    if isinstance(value, dict):
        if "lean" in value:
            return str(value["lean"])
        raise ValueError(f"expected object with 'lean' field, got {value!r}")
    if isinstance(value, bool):
        raise ValueError("boolean is not a Lean expression")
    if isinstance(value, int):
        if kind == "nat":
            return str(value)
        if kind == "rat":
            return f"({value} : Rat)"
        return f"(({value} : Rat) : Real)"
    if isinstance(value, str):
        stripped = value.strip()
        if kind == "nat":
            return stripped
        if kind == "proof":
            return stripped
        if looks_decimal(stripped):
            rat_expr = decimal_to_rat_expr(stripped)
            return rat_expr if kind == "rat" else f"({rat_expr} : Real)"
        return stripped
    raise ValueError(f"unsupported Lean expression value: {value!r}")


def lean_proof(value: Any) -> str:
    if value is True:
        return "by norm_num"
    return lean_expr(value, kind="proof")


def fin_function_from_values(values: Any, *, kind: str) -> str:
    if isinstance(values, str) or isinstance(values, dict):
        return lean_expr(values, kind="proof" if kind == "proof" else kind)
    if not isinstance(values, list):
        raise ValueError(f"expected list or Lean expression, got {values!r}")
    lines = ["fun j =>", "  match j with"]
    for index, value in enumerate(values):
        lines.append(f"  | ⟨{index}, _⟩ => {lean_expr(value, kind=kind)}")
    return "\n".join(lines)


def proof_family_map(proof_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(family["id"]): family for family in proof_data.get("families", [])}


def sorted_rows(family: dict[str, Any]) -> list[dict[str, Any]]:
    return sorted(family.get("distances", []), key=lambda row: int(row["index"]))


def sorted_chunks(row: dict[str, Any]) -> list[dict[str, Any]]:
    return sorted(row.get("chunks", []), key=lambda chunk: int(chunk["index"]))


def require_field(payload: dict[str, Any], field: str) -> Any:
    if field not in payload or payload[field] is None:
        raise ValueError(f"missing required field {field!r}")
    return payload[field]


def has_field(payload: dict[str, Any], field: str) -> bool:
    return field in payload and payload[field] is not None


def has_all_fields(payload: dict[str, Any], fields: list[str]) -> bool:
    return all(has_field(payload, field) for field in fields)


def cell_decl_name(prefix: str, row: dict[str, Any], chunk: dict[str, Any]) -> str:
    return f"{prefix}D{int(row['index'])}C{int(chunk['index'])}"


def emit_fin_cases_table(
    *,
    name: str,
    result_type: str,
    rows: list[dict[str, Any]],
    branch_expr,
) -> list[str]:
    lines = [f"private def {name} (n : CoeffIndex23) (i : Fin 26) : {result_type} := by"]
    lines.append("  fin_cases n <;> fin_cases i")
    for row in rows:
        for chunk in sorted_chunks(row):
            expr = branch_expr(row, chunk)
            lines.append(f"  · exact {expr}")
    lines.append("")
    return lines


def emit_fin_cases_proof(
    *,
    name: str,
    result_type: str,
    rows: list[dict[str, Any]],
    branch_proof,
) -> list[str]:
    lines = [f"private theorem {name} (n : CoeffIndex23) (i : Fin 26) : {result_type} := by"]
    lines.append("  fin_cases n <;> fin_cases i")
    for row in rows:
        for chunk in sorted_chunks(row):
            proof = branch_proof(row, chunk)
            lines.append(f"  · exact {proof}")
    lines.append("")
    return lines


def emit_row_proof(
    *,
    name: str,
    result_type: str,
    rows: list[dict[str, Any]],
    field: str,
) -> list[str]:
    lines = [f"private theorem {name} (n : CoeffIndex23) : {result_type} := by"]
    lines.append("  fin_cases n")
    for row in rows:
        lines.append(f"  · exact {lean_proof(require_field(row, field))}")
    lines.append("")
    return lines


def emit_cert_expr(cell: dict[str, Any]) -> str:
    degree = int(require_field(cell, "degree"))
    coeff = require_field(cell, "coeff")
    if isinstance(coeff, list) and len(coeff) != degree + 1:
        raise ValueError(
            f"coeff list length {len(coeff)} does not match degree {degree}"
        )
    return (
        "{ center := "
        + lean_expr(require_field(cell, "center"), kind="rat")
        + "\n    radius := "
        + lean_expr(require_field(cell, "radius"), kind="rat")
        + f"\n    degree := {degree}"
        + "\n    coeff := "
        + fin_function_from_values(coeff, kind="rat")
        + "\n    remainder := "
        + lean_expr(require_field(cell, "remainder"), kind="rat")
        + " }"
    )


def emit_component_product_corner_bound(cell: dict[str, Any], *, side: str) -> str:
    direct_field = f"componentProduct{side}"
    if has_field(cell, direct_field):
        return lean_proof(require_field(cell, direct_field))

    projection = "1" if side == "Lower" else "2"
    if has_all_fields(cell, PRODUCT_CORNER_LOWER_FIELDS + PRODUCT_CORNER_UPPER_FIELDS):
        lower_proofs = [
            lean_proof(require_field(cell, field)) for field in PRODUCT_CORNER_LOWER_FIELDS
        ]
        upper_proofs = [
            lean_proof(require_field(cell, field)) for field in PRODUCT_CORNER_UPPER_FIELDS
        ]
        corner_args = "\n        ".join(lower_proofs + upper_proofs)
        return (
            "by\n"
            "  intro omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower\n"
            "    hShapeSqUpper hCosLower hCosUpper\n"
            "  exact\n"
            "    (RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
            "product_bounds_of_eight_corners\n"
            f"        {corner_args}\n"
            "        omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower\n"
            f"        hShapeSqUpper hCosLower hCosUpper).{projection}"
        )

    if has_all_fields(cell, SCALE_INTERVAL_PRODUCT_FIELDS):
        lower_proofs = [
            lean_proof(require_field(cell, field))
            for field in PRODUCT_SCALE_CORNER_LOWER_FIELDS
        ]
        upper_proofs = [
            lean_proof(require_field(cell, field))
            for field in PRODUCT_SCALE_CORNER_UPPER_FIELDS
        ]
        corner_args = "\n        ".join(lower_proofs + upper_proofs)
        return (
            "by\n"
            "  intro omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower\n"
            "    hShapeSqUpper hCosLower hCosUpper\n"
            "  exact\n"
            "    (RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
            "product_bounds_of_scale_interval_and_sixteen_corners\n"
            f"        (scaleLower := {lean_expr(require_field(cell, 'scaleLower'))})\n"
            f"        (scaleUpper := {lean_expr(require_field(cell, 'scaleUpper'))})\n"
            f"        {lean_proof(require_field(cell, 'scaleLowerBound'))}\n"
            f"        {lean_proof(require_field(cell, 'scaleUpperBound'))}\n"
            f"        {corner_args}\n"
            "        omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower\n"
            f"        hShapeSqUpper hCosLower hCosUpper).{projection}"
        )

    lower_proofs = [
        lean_proof(require_field(cell, field)) for field in PRODUCT_CORNER_LOWER_FIELDS
    ]
    upper_proofs = [
        lean_proof(require_field(cell, field)) for field in PRODUCT_CORNER_UPPER_FIELDS
    ]
    corner_args = "\n        ".join(lower_proofs + upper_proofs)
    return (
        "by\n"
        "  intro omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower\n"
        "    hShapeSqUpper hCosLower hCosUpper\n"
        "  exact\n"
        "    (RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
        "product_bounds_of_eight_corners\n"
        f"        {corner_args}\n"
        "        omega shapeSq cosValue hOmegaLower hOmegaUpper hShapeSqLower\n"
        f"        hShapeSqUpper hCosLower hCosUpper).{projection}"
    )


def emit_valid_proof_expr(config: dict[str, str], prefix: str, row: dict[str, Any], cell: dict[str, Any]) -> str:
    cell_name = cell_decl_name(prefix, row, cell)
    degree = int(require_field(cell, "degree"))
    direct_polynomial = has_all_fields(cell, POLYNOMIAL_DIRECT_FIELDS)
    if not direct_polynomial:
        term_lower = require_field(cell, "termLower")
        term_upper = require_field(cell, "termUpper")
        if isinstance(term_lower, list) and len(term_lower) != degree + 1:
            raise ValueError(
                f"{cell_name}: termLower length {len(term_lower)} does not match degree {degree}"
            )
        if isinstance(term_upper, list) and len(term_upper) != degree + 1:
            raise ValueError(
                f"{cell_name}: termUpper length {len(term_upper)} does not match degree {degree}"
            )
    bounds = [
        "rawLower := " + lean_expr(require_field(cell, "rawLower")),
        "rawUpper := " + lean_expr(require_field(cell, "rawUpper")),
        "polyLower := " + lean_expr(require_field(cell, "polyLower")),
        "polyUpper := " + lean_expr(require_field(cell, "polyUpper")),
        "omegaLower := " + lean_expr(require_field(cell, "omegaLower")),
        "omegaUpper := " + lean_expr(require_field(cell, "omegaUpper")),
        "shapeSqLower := " + lean_expr(require_field(cell, "shapeSqLower")),
        "shapeSqUpper := " + lean_expr(require_field(cell, "shapeSqUpper")),
        "cosLower := " + lean_expr(require_field(cell, "cosLower")),
        "cosUpper := " + lean_expr(require_field(cell, "cosUpper")),
        "hOmegaLower := " + lean_proof(require_field(cell, "omegaLowerBound")),
        "hOmegaUpper := " + lean_proof(require_field(cell, "omegaUpperBound")),
        "hShapeSqLower := " + lean_proof(require_field(cell, "shapeSqLowerBound")),
        "hShapeSqUpper := " + lean_proof(require_field(cell, "shapeSqUpperBound")),
        "hCosLower := " + lean_proof(require_field(cell, "cosLowerBound")),
        "hCosUpper := " + lean_proof(require_field(cell, "cosUpperBound")),
        "hProductLower := " + emit_component_product_corner_bound(cell, side="Lower"),
        "hProductUpper := " + emit_component_product_corner_bound(cell, side="Upper"),
    ]
    proof_data_type = "ComponentValueChunkProofData" if direct_polynomial else "ComponentChunkProofData"
    if direct_polynomial:
        bounds.extend(
            [
                "hPolyLower := " + lean_proof(require_field(cell, "polynomialLowerBound")),
                "hPolyUpper := " + lean_proof(require_field(cell, "polynomialUpperBound")),
            ]
        )
    else:
        bounds.extend(
            [
                "termLower := " + fin_function_from_values(term_lower, kind="real"),
                "termUpper := " + fin_function_from_values(term_upper, kind="real"),
                "hTerms := " + lean_proof(require_field(cell, "polynomialTermBounds")),
                "hPolyLower := " + lean_proof(require_field(cell, "polyLowerSum")),
                "hPolyUpper := " + lean_proof(require_field(cell, "polyUpperSum")),
            ]
        )
    data_fields = [
        "bounds :=\n      { " + "\n        ".join(bounds) + " }",
        "hLU := " + config["hLU"],
        "hRadiusNonneg := " + lean_proof(require_field(cell, "radiusNonneg")),
        "hRemainderNonneg := " + lean_proof(require_field(cell, "remainderNonneg")),
        "hLeft := " + lean_proof(require_field(cell, "radiusLeft")),
        "hRight := " + lean_proof(require_field(cell, "radiusRight")),
        "hProfileInt := by\n      exact RawOmegaAChunkIntegral."
        + config["integrable"]
        + " n _ _ ("
        + config["hL"]
        + ")",
        "hDiffLower := " + lean_proof(require_field(cell, "diffLower")),
        "hDiffUpper := " + lean_proof(require_field(cell, "diffUpper")),
        "hIntegralLower := " + lean_proof(require_field(cell, "integralLower")),
        "hIntegralUpper := " + lean_proof(require_field(cell, "integralUpper")),
    ]
    return (
        "({ "
        + "\n    ".join(data_fields)
        + " } : RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
        + f"{proof_data_type} ({prefix}Cert n i)).valid"
    )


def emit_family(config: dict[str, str], family: dict[str, Any]) -> list[str]:
    prefix = config["prefix"]
    rows = sorted_rows(family)
    cert_type = (
        "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate\n"
        f"    {config['k']} {config['ell']} ((n.1 : Real) / 4)\n"
        f"    {config['left']} {config['right']}\n"
        f"    ({prefix}ChunkLower n i) ({prefix}ChunkUpper n i)"
    )
    valid_type = f"({prefix}Cert n i).Valid"
    lines: list[str] = []
    lines.extend(
        emit_fin_cases_table(
            name=f"{prefix}ChunkLower",
            result_type="Real",
            rows=rows,
            branch_expr=lambda _row, cell: lean_expr(require_field(cell, "chunkLower")),
        )
    )
    lines.extend(
        emit_fin_cases_table(
            name=f"{prefix}ChunkUpper",
            result_type="Real",
            rows=rows,
            branch_expr=lambda _row, cell: lean_expr(require_field(cell, "chunkUpper")),
        )
    )
    lines.extend(
        emit_fin_cases_table(
            name=f"{prefix}Cert",
            result_type=cert_type,
            rows=rows,
            branch_expr=lambda _row, cell: emit_cert_expr(cell),
        )
    )
    lines.extend(
        emit_fin_cases_proof(
            name=f"{prefix}Valid",
            result_type=valid_type,
            rows=rows,
            branch_proof=lambda row, cell: emit_valid_proof_expr(
                config, prefix, row, cell
            ),
        )
    )
    row_sum_type = (
        f"{config['block']}K{config['k']}RawOmegaAComparisonTailWindowArithmeticPayload_generated."
    )
    if config["block"] == "primary" and config["k"] == "11":
        row_sum_prefix = "primaryK11"
    elif config["block"] == "control" and config["k"] == "9":
        row_sum_prefix = "controlK9"
    else:
        raise ValueError(f"unsupported family config {config!r}")
    lower_target = (
        f"{row_sum_prefix}RawOmegaAComparisonTailWindowArithmeticPayload_generated."
        + ("finiteLower" if config["kind"] == "finite" else "tailWindowLower")
    )
    upper_target = (
        f"{row_sum_prefix}RawOmegaAComparisonTailWindowArithmeticPayload_generated."
        + ("finiteUpper" if config["kind"] == "finite" else "tailWindowUpper")
    )
    sum_lower = (
        f"{lower_target} n <= ∑ i ∈ Finset.range 26, "
        f"RawOmegaAChunkTaylorPayload.chunkValueFromFin26 ({prefix}ChunkLower n) i"
    )
    sum_upper = (
        f"(∑ i ∈ Finset.range 26, "
        f"RawOmegaAChunkTaylorPayload.chunkValueFromFin26 ({prefix}ChunkUpper n) i) <= "
        f"{upper_target} n"
    )
    lines.extend(
        emit_row_proof(
            name=f"{prefix}LowerSum",
            result_type=sum_lower,
            rows=rows,
            field="lowerSum",
        )
    )
    lines.extend(
        emit_row_proof(
            name=f"{prefix}UpperSum",
            result_type=sum_upper,
            rows=rows,
            field="upperSum",
        )
    )
    lines.append(f"private def {prefix}Payload : RawOmegaAChunkTaylorPayload.{config['record_type']} :=")
    lines.append("  { chunkLower := " + f"{prefix}ChunkLower")
    lines.append("    chunkUpper := " + f"{prefix}ChunkUpper")
    lines.append("    cert := by")
    lines.append("      intro n i")
    lines.append(
        "      simpa [RawOmegaAChunkTaylorPayload.chunkValueFromFin26_apply] "
        f"using {prefix}Cert n i"
    )
    lines.append("    valid := by")
    lines.append("      intro n i")
    lines.append(
        "      simpa [RawOmegaAChunkTaylorPayload.chunkValueFromFin26_apply] "
        f"using {prefix}Valid n i"
    )
    lines.append(f"    hLowerSum := {prefix}LowerSum")
    lines.append(f"    hUpperSum := {prefix}UpperSum")
    lines.append("  }")
    lines.append("")
    return lines


def emit_lean_payload(proof_data: dict[str, Any]) -> str:
    families = proof_family_map(proof_data)
    missing = [family_id for family_id in FAMILY_ORDER if family_id not in families]
    if missing:
        raise ValueError(f"proof data is missing families: {missing}")

    lines = [
        "import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorPayloadImport",
        "",
        "set_option linter.mathlibStandardSet false",
        "set_option autoImplicit false",
        "set_option maxHeartbeats 0",
        "",
        "/-!",
        "Generated Step33A.1-A raw-Omega Taylor/model PayloadFin.",
        "",
        "This file is proof-bearing generated code.  It should only be emitted",
        "from a complete q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1",
        "payload and must still be checked by Lean before use.",
        "-/",
        "",
        "noncomputable section",
        "",
        "open scoped BigOperators",
        "",
        "namespace Q3",
        "namespace PSDpd",
        "namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport",
        "",
        "open CenteredCoeffPayloadImport",
        "open RawOmegaAChunkIntegral",
        "",
        "namespace RawOmegaAChunkTaylorGeneratedPayload",
        "",
    ]
    for family_id in FAMILY_ORDER:
        lines.extend(emit_family(FAMILY_CONFIGS[family_id], families[family_id]))

    lines.extend(
        [
            "def payloadFin : RawOmegaAChunkTaylorPayload.PayloadFin :=",
            "  { primaryFinite := primaryFinitePayload",
            "    primaryTail := primaryTailPayload",
            "    controlFinite := controlFinitePayload",
            "    controlTail := controlTailPayload }",
            "",
            "def directTailWindowInputs : RawOmegaADirectTailWindowInputs :=",
            "  payloadFin.toDirectTailWindowInputs",
            "",
            "end RawOmegaAChunkTaylorGeneratedPayload",
            "end CenteredCoeffPrimeDeltaLiveRationalPayloadImport",
            "end PSDpd",
            "end Q3",
            "",
        ]
    )
    return "\n".join(lines)


def build_report(
    *,
    worklist_path: Path,
    probe_path: Path | None,
    proof_data_path: Path,
    out_lean: Path,
    inventory: dict[str, Any],
    out_lean_written: bool,
) -> dict[str, Any]:
    ready = inventory["status"] == "ready_to_generate_lean_payload"
    status = (
        "lean_payload_emitted_needs_lean_check"
        if ready
        else "missing_proof_data_no_lean_emitted"
    )
    reason = (
        "Proof data is complete and a generated Lean payload was written.  The "
        "file is not accepted until lake env lean checks it."
        if ready
        else "Proof data is incomplete; emitting a Lean payload here would "
        "turn missing Taylor/model facts into a fake trusted import."
    )
    totals = inventory["totals"]
    return {
        "schema": EMITTER_SCHEMA,
        "status": status,
        "reason": reason,
        "worklist": str(worklist_path),
        "probe": str(probe_path) if probe_path is not None else None,
        "proof_data": str(proof_data_path),
        "proof_data_schema": inventory["proof_data_schema_expected"],
        "lean_payload_type": inventory["lean_payload_type"],
        "lean_step33a_wrapper": inventory["lean_step33a_wrapper"],
        "lean_step33b_wrapper": inventory["lean_step33b_wrapper"],
        "lean_chunk_proof_wrapper": (
            "RawOmegaATaylorModelCertificate.ComponentValueChunkProofData "
            "or ComponentChunkProofData"
        ),
        "product_proof_strategy": {
            "direct_fields": ["componentProductLower", "componentProductUpper"],
            "corner_lower_fields": PRODUCT_CORNER_LOWER_FIELDS,
            "corner_upper_fields": PRODUCT_CORNER_UPPER_FIELDS,
            "corner_receiver": (
                "RawOmegaATaylorModelCertificate.product_bounds_of_eight_corners"
            ),
            "scale_interval_fields": SCALE_INTERVAL_PRODUCT_FIELDS,
            "scale_interval_lower_corner_fields": PRODUCT_SCALE_CORNER_LOWER_FIELDS,
            "scale_interval_upper_corner_fields": PRODUCT_SCALE_CORNER_UPPER_FIELDS,
            "scale_interval_receiver": (
                "RawOmegaATaylorModelCertificate."
                "product_bounds_of_scale_interval_and_sixteen_corners"
            ),
        },
        "out_lean": str(out_lean),
        "out_lean_written": out_lean_written,
        "ready_path_implemented": True,
        "ready_path_status_requires": "lake env lean on generated payload import",
        "totals": totals,
        "missing_field_counts": inventory["missing_field_counts"],
        "families": family_summaries(inventory),
        "route_guard": [
            "do not emit Lean from skeleton, null, or omitted proof fields",
            "do not use Arb/acb numeric probe intervals as trusted proof data",
            "do not mutate A CSV, ARadius, radius-floor, or LDL",
            "do not call Step33A.1-A closed until PayloadFin compiles",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    totals = report["totals"]
    lines = [
        "# Step33A.1-A Taylor Payload Lean Emitter Guard",
        "",
        "This report says whether the current proof-data contract is ready for",
        "`RawOmegaAChunkTaylorPayload.PayloadFin` Lean emission.",
        "",
        "## Verdict",
        "",
        f"- status: `{report['status']}`",
        f"- reason: {report['reason']}",
        f"- payload type: `{report['lean_payload_type']}`",
        f"- Step33A wrapper: `{report['lean_step33a_wrapper']}`",
        f"- Step33B/33C wrapper: `{report['lean_step33b_wrapper']}`",
        f"- chunk proof wrapper: `{report['lean_chunk_proof_wrapper']}`",
        f"- product corner receiver: `{report['product_proof_strategy']['corner_receiver']}`",
        f"- product scale-interval receiver: `{report['product_proof_strategy']['scale_interval_receiver']}`",
        f"- proof-data source: `{report['proof_data']}`",
        f"- intended Lean output: `{report['out_lean']}`",
        f"- Lean output written: `{report['out_lean_written']}`",
        f"- ready path implemented: `{report['ready_path_implemented']}`",
        f"- ready path requires: `{report['ready_path_status_requires']}`",
        "",
        "## Counts",
        "",
        f"- families: `{totals['families']}`",
        f"- distance rows: `{totals['distance_rows']}`",
        f"- chunk cells: `{totals['chunk_cells']}`",
        f"- complete rows: `{totals['complete_rows']}`",
        f"- complete cells: `{totals['complete_cells']}`",
        f"- missing cells: `{totals['missing_cells']}`",
        "",
        "## Families",
        "",
        "| family | rows | chunks | cells | complete rows | complete cells | missing cells |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for family in report["families"]:
        lines.append(
            "| {id} | {distance_rows} | {chunk_count} | {chunk_cells} | "
            "{complete_rows} | {complete_cells} | {missing_cells} |".format(**family)
        )

    lines.extend(["", "## Missing Field Counts", ""])
    for field, count in report["missing_field_counts"].items():
        lines.append(f"- `{field}`: `{count}`")

    product = report["product_proof_strategy"]
    lines.extend(["", "## Product Proof Strategy", ""])
    lines.append(
        "For `hProductLower` and `hProductUpper`, the emitter accepts direct "
        "universal proof fields, the full exact-scale eight-corner packet, or "
        "a family-scale interval with sixteen scale/omega/shape/cos corners. "
        "This route is sign-generic and remains valid on early finite chunks "
        "where the raw Step22 omega weight is negative."
    )
    lines.append("")
    lines.append("Direct fields:")
    for field in product["direct_fields"]:
        lines.append(f"- `{field}`")
    lines.append("")
    lines.append(f"Corner receiver: `{product['corner_receiver']}`")
    lines.append("")
    lines.append("Lower corner fields:")
    for field in product["corner_lower_fields"]:
        lines.append(f"- `{field}`")
    lines.append("")
    lines.append("Upper corner fields:")
    for field in product["corner_upper_fields"]:
        lines.append(f"- `{field}`")
    lines.append("")
    lines.append(f"Scale-interval receiver: `{product['scale_interval_receiver']}`")
    lines.append("")
    lines.append("Scale-interval fields:")
    for field in product["scale_interval_fields"]:
        lines.append(f"- `{field}`")

    lines.extend(["", "## Route Guard", ""])
    for item in report["route_guard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--probe", type=Path, default=DEFAULT_PROBE)
    parser.add_argument("--proof-data", type=Path, default=DEFAULT_PROOF_DATA)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--out-lean", type=Path, default=DEFAULT_OUT_LEAN)
    args = parser.parse_args()

    worklist = load_json(args.worklist)
    validate_worklist(worklist, args.worklist)

    probe = None
    probe_path = None
    if args.probe is not None and args.probe.exists():
        probe = load_json(args.probe)
        validate_probe(probe, args.probe)
        probe_path = args.probe

    proof_data = load_json(args.proof_data)
    validate_proof_data(proof_data, args.proof_data)

    inventory = build_inventory(
        worklist,
        probe=probe,
        proof_data=proof_data,
        proof_data_source=str(args.proof_data),
    )
    out_lean_written = False
    if inventory["status"] == "ready_to_generate_lean_payload":
        lean_payload = emit_lean_payload(proof_data)
        args.out_lean.parent.mkdir(parents=True, exist_ok=True)
        args.out_lean.write_text(lean_payload, encoding="utf-8")
        out_lean_written = True

    report = build_report(
        worklist_path=args.worklist,
        probe_path=probe_path,
        proof_data_path=args.proof_data,
        out_lean=args.out_lean,
        inventory=inventory,
        out_lean_written=out_lean_written,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    totals = report["totals"]
    print(
        "status={status} families={families} rows={rows} cells={cells} "
        "complete_cells={complete} missing_cells={missing} out_lean_written={written}".format(
            status=report["status"],
            families=totals["families"],
            rows=totals["distance_rows"],
            cells=totals["chunk_cells"],
            complete=totals["complete_cells"],
            missing=totals["missing_cells"],
            written=report["out_lean_written"],
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(run())
