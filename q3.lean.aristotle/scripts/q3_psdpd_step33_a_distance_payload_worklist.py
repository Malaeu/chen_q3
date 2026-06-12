#!/usr/bin/env python3
"""Build the Step33A.1-A raw-Omega distance-payload worklist.

This is not a proof producer.  It translates the checked chunk comparison-
integral contract into the exact four distance-indexed payload collections
that the next generator must inhabit.

The active raw-Omega direct route uses the positive-axis finite window
`(0,260]` and targets the generated raw-Omega finite lower/upper rows directly.
Do not divide the finite targets by two here; the older centered positive-half
route did that before doubling back to the full centered finite window, but the
raw-Omega receiver consumes `step22PositiveAxisOmegaAFinitePart` itself.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_CONTRACT = REQUEST_DIR / "a_signed_chunk_payload_contract.json"
DEFAULT_WINDOW_CONTRACT = REQUEST_DIR / "a_window_contract.json"

DISTANCE_PAYLOAD = "RawOmegaAChunkTaylorPayload.PayloadFin"
NAT_DISTANCE_PAYLOAD = "RawOmegaAChunkTaylorPayload.Payload"
FIN_CHUNK_VALUE_ADAPTER = "RawOmegaAChunkTaylorPayload.chunkValueFromFin26"
CHUNKED_RANGE_PAYLOAD = "RawOmegaAChunkedRangePayload"
TAYLOR_MODEL_CERT = "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate"
TAYLOR_MODEL_VALID = "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid"
TAYLOR_MODEL_VALUE_BOUNDS = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ValueBounds"
)
TAYLOR_MODEL_POLYNOMIAL_TERM_BOUNDS = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.PolynomialTermBounds"
)
TAYLOR_MODEL_POLYNOMIAL_VALUE_BOUNDS_HELPER = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.polynomial_value_bounds_of_term_bounds"
)
TAYLOR_MODEL_VALUE_BOUNDS_FROM_RAW_TERM_HELPER = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ValueBounds.of_raw_and_polynomial_term_bounds"
)
TAYLOR_MODEL_RAW_INTEGRAND_COMPONENT_BOUNDS = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.RawIntegrandComponentBounds"
)
TAYLOR_MODEL_RAW_COMPONENT_BOUNDS_ABS_COS_HELPER = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.RawIntegrandComponentBounds."
    "of_nonneg_abs_cos_product_bounds"
)
TAYLOR_MODEL_RAW_INTEGRAND_VALUE_BOUNDS_FROM_COMPONENTS_HELPER = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.rawOmegaAIntegrand_value_bounds_of_component_bounds"
)
TAYLOR_MODEL_VALUE_BOUNDS_FROM_RAW_COMPONENT_TERM_HELPER = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.ValueBounds."
    "of_raw_component_abs_cos_and_polynomial_term_bounds"
)
TAYLOR_MODEL_ABS_COS_COMPONENT_TERM_BOUNDS = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
    "AbsCosComponentTermBounds"
)
TAYLOR_MODEL_ABS_COS_COMPONENT_TERM_BOUNDS_VALUE_HELPER = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
    "AbsCosComponentTermBounds.toValueBounds"
)
TAYLOR_MODEL_ABS_COS_CHUNK_PROOF_DATA = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
    "AbsCosChunkProofData"
)
TAYLOR_MODEL_ABS_COS_CHUNK_PROOF_DATA_VALID_HELPER = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate."
    "AbsCosChunkProofData.valid"
)
TAYLOR_MODEL_LOWER_INTEGRAL = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.lowerModelIntegral"
)
TAYLOR_MODEL_UPPER_INTEGRAL = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.upperModelIntegral"
)
TAYLOR_MODEL_VALID_GENERIC_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.of_diff_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_of_diff_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_of_diff_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_FINITE_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_diff_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_TAIL_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_diff_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_FINITE_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_diff_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_TAIL_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_diff_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_VALUE_GENERIC_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.of_value_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_VALUE_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_of_value_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_VALUE_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_of_value_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_FINITE_VALUE_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_value_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_TAIL_VALUE_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_value_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_FINITE_VALUE_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_value_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_TAIL_VALUE_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_value_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_FINITE_RAW_TERM_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_TAIL_RAW_TERM_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_FINITE_RAW_TERM_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_TAIL_RAW_TERM_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_and_polynomial_term_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_FINITE_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_PRIMARY_TAIL_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_FINITE_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds"
)
TAYLOR_MODEL_VALID_CONTROL_TAIL_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR = (
    "RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds"
)
EXACT_INTEGRAND_DISTANCE_HELPER = "RawOmegaAChunkIntegral.WindowPartBoundsCert"
DISTANCE_ASSEMBLER = "RawOmegaAChunkTaylorPayload.PayloadFin.toChunkedRangePayload"
CHUNKED_RANGE_ASSEMBLER = "RawOmegaAChunkedRangePayload.toChunkIntegralBoundsCert"
STEP33A_WRAPPER = "RawOmegaAChunkTaylorPayload.PayloadFin.toDirectTailWindowInputs"
STEP33B_WRAPPER = (
    "psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs"
)
STEP33C_WRAPPER = (
    "psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs"
)

TARGETS = {
    ("primary", "finite"): {
        "target_lower": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower",
        "target_upper": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper",
        "collection": "primaryFinite",
        "domain": "(0,260]",
        "chunks_key": "positive_half_chunks",
        "L": "fun i => 0 + (10 : Real) * (i : Real)",
        "U": "fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real)",
    },
    ("primary", "tail"): {
        "target_lower": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower",
        "target_upper": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper",
        "collection": "primaryTail",
        "domain": "(260,520]",
        "chunks_key": "chunks",
        "L": (
            "fun i => rawOmegaAFiniteTailCutoff + "
            "(10 : Real) * (i : Real)"
        ),
        "U": (
            "fun i => rawOmegaAFiniteTailCutoff + "
            "(10 : Real) * ((i + 1 : Nat) : Real)"
        ),
    },
    ("control", "finite"): {
        "target_lower": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteLower",
        "target_upper": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.finiteUpper",
        "collection": "controlFinite",
        "domain": "(0,260]",
        "chunks_key": "positive_half_chunks",
        "L": "fun i => 0 + (10 : Real) * (i : Real)",
        "U": "fun i => 0 + (10 : Real) * ((i + 1 : Nat) : Real)",
    },
    ("control", "tail"): {
        "target_lower": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowLower",
        "target_upper": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated.tailWindowUpper",
        "collection": "controlTail",
        "domain": "(260,520]",
        "chunks_key": "chunks",
        "L": (
            "fun i => rawOmegaAFiniteTailCutoff + "
            "(10 : Real) * (i : Real)"
        ),
        "U": (
            "fun i => rawOmegaAFiniteTailCutoff + "
            "(10 : Real) * ((i + 1 : Nat) : Real)"
        ),
    },
}


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def block_map(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(block["block"]): block for block in payload["blocks"]}


def row_map(block: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {int(row["index"]): row for row in block["distances"]}


def family_targets(block_name: str, family_kind: str) -> dict[str, str]:
    target = TARGETS[(block_name, family_kind)]
    return {
        "target_lower": target["target_lower"],
        "target_upper": target["target_upper"],
        "L": target["L"],
        "U": target["U"],
    }


def valid_constructor_for(block_name: str, family_kind: str) -> str:
    if (block_name, family_kind) == ("primary", "finite"):
        return TAYLOR_MODEL_VALID_PRIMARY_FINITE_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR
    if (block_name, family_kind) == ("primary", "tail"):
        return TAYLOR_MODEL_VALID_PRIMARY_TAIL_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR
    if (block_name, family_kind) == ("control", "finite"):
        return TAYLOR_MODEL_VALID_CONTROL_FINITE_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR
    if (block_name, family_kind) == ("control", "tail"):
        return TAYLOR_MODEL_VALID_CONTROL_TAIL_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR
    raise ValueError(
        f"unexpected block/family pair {block_name!r}/{family_kind!r}"
    )


def interval_sign(lower: str, upper: str) -> str:
    lo = Decimal(str(lower))
    hi = Decimal(str(upper))
    if hi < 0:
        return "negative"
    if 0 < lo:
        return "positive"
    if lo == 0 and hi == 0:
        return "zero"
    return "crossing"


def decimal_str(value: Decimal) -> str:
    if value == 0:
        return "0.000000000000000000E+0"
    return format(value, ".18E")


def load_target_refresh(path: Path | None) -> tuple[dict[str, dict[int, dict[str, str]]], int]:
    if path is None:
        return {}, 0
    payload = load_json(path)
    if payload.get("schema") != "q3_psdpd_step33_a_chunk_integral_probe.v1":
        raise ValueError(f"{path}: unexpected schema {payload.get('schema')!r}")

    refresh: dict[str, dict[int, dict[str, str]]] = {}
    for family in payload.get("families", []):
        family_id = str(family["family"])
        for row in family.get("rows", []):
            if row.get("fits_target"):
                continue
            if not row.get("fits_after_local_target_refresh"):
                raise ValueError(
                    f"{path}: {family_id}[{row.get('distance_index')}] "
                    "does not fit the current target and is not slack-absorbable"
                )
            idx = int(row["distance_index"])
            lower = str(row["suggested_target_lower"])
            upper = str(row["suggested_target_upper"])
            if Decimal(upper) < Decimal(lower):
                raise ValueError(f"{path}: inverted refresh interval at {family_id}[{idx}]")
            refresh.setdefault(family_id, {})[idx] = {
                "target_lower_value": lower,
                "target_upper_value": upper,
                "available_target_refresh_slack": str(row.get("available_target_refresh_slack")),
                "needed_target_refresh_slack": str(row.get("needed_target_refresh_slack")),
                "target_refresh_guard": str(row.get("target_refresh_guard")),
                "slack_after_suggested_refresh": str(row.get("slack_after_suggested_refresh")),
            }
    return refresh, sum(len(rows) for rows in refresh.values())


def priority_for(sign: str, family_kind: str) -> int:
    if sign == "negative":
        return 0
    if family_kind == "tail":
        return 1
    return 2


def build_distance_rows(
    block: dict[str, Any],
    family_kind: str,
    source_rows: dict[int, dict[str, Any]],
    target_refresh: dict[str, dict[int, dict[str, str]]],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    family_id = f"{block['block']}_{family_kind}"
    for row in block["distances"]:
        idx = int(row["index"])
        source = source_rows.get(idx, {})
        if family_kind == "finite":
            lower_value = row["finite_lower"]
            upper_value = row["finite_upper"]
        else:
            lower_value = row["positive_window_lower"]
            upper_value = row["positive_window_upper"]
        refresh = target_refresh.get(family_id, {}).get(idx)
        if refresh is not None:
            lower_value = refresh["target_lower_value"]
            upper_value = refresh["target_upper_value"]
        sign = interval_sign(lower_value, upper_value)
        rows.append(
            {
                "index": idx,
                "distance": row["distance"],
                "target_interval_sign": sign,
                "route_positive_window_sign": row["signed_positive_window_sign"],
                "target_lower_value": lower_value,
                "target_upper_value": upper_value,
                "target_refresh_applied": refresh is not None,
                "target_refresh_guard": (
                    refresh["target_refresh_guard"] if refresh is not None else None
                ),
                "target_refresh_needed_slack": (
                    refresh["needed_target_refresh_slack"] if refresh is not None else None
                ),
                "target_refresh_slack_after": (
                    refresh["slack_after_suggested_refresh"] if refresh is not None else None
                ),
                "proof_remainder_radius": row.get("proof_remainder_radius"),
                "generated_tail_radius": row.get("generated_tail_radius"),
                "tail_radius_slack": source.get("tail_radius_slack"),
                "tail_excess": source.get("tail_excess"),
                "priority": priority_for(sign, family_kind),
                "missing_payload": {
                    "chunkLower": "CoeffIndex23 -> Fin 26 -> Real",
                    "chunkUpper": "CoeffIndex23 -> Fin 26 -> Real",
                    "natCompatibilityAdapter": FIN_CHUNK_VALUE_ADAPTER,
                    "taylorCert": TAYLOR_MODEL_CERT,
                    "taylorValid": TAYLOR_MODEL_VALID,
                    "taylorValidConstructor": valid_constructor_for(
                        str(block["block"]), family_kind
                    ),
                    "absCosComponentTermBoundsRecord": (
                        TAYLOR_MODEL_ABS_COS_COMPONENT_TERM_BOUNDS
                    ),
                    "absCosComponentTermBoundsValueHelper": (
                        TAYLOR_MODEL_ABS_COS_COMPONENT_TERM_BOUNDS_VALUE_HELPER
                    ),
                    "absCosChunkProofDataRecord": (
                        TAYLOR_MODEL_ABS_COS_CHUNK_PROOF_DATA
                    ),
                    "absCosChunkProofDataValidHelper": (
                        TAYLOR_MODEL_ABS_COS_CHUNK_PROOF_DATA_VALID_HELPER
                    ),
                    "foldsTo": EXACT_INTEGRAND_DISTANCE_HELPER,
                    "endpointShape": "finite/tail chunk constructor proves 0 <= L and L <= U",
                    "radiusNonneg": "0 <= radius",
                    "remainderNonneg": "0 <= remainder",
                    "radiusLeft": "center - radius <= L",
                    "radiusRight": "U <= center + radius",
                    "taylorValueBounds": (
                        "assembled directly by valueBoundsFromRawComponentTermHelper"
                    ),
                    "omegaLower": "lower value enclosure for step22OmegaArchWeight",
                    "omegaUpper": "upper value enclosure for step22OmegaArchWeight",
                    "omegaLowerBound": (
                        "forall eta in chunk, omegaLower <= step22OmegaArchWeight eta"
                    ),
                    "omegaUpperBound": (
                        "forall eta in chunk, step22OmegaArchWeight eta <= omegaUpper"
                    ),
                    "shapeSqLower": "lower value enclosure for centered B-spline transform squared",
                    "shapeSqUpper": "upper value enclosure for centered B-spline transform squared",
                    "shapeSqLowerBound": (
                        "forall eta in chunk, shapeSqLower <= centered transform squared"
                    ),
                    "shapeSqUpperBound": (
                        "forall eta in chunk, centered transform squared <= shapeSqUpper"
                    ),
                    "cosLower": "lower value enclosure for cos(eta * x)",
                    "cosUpper": "upper value enclosure for cos(eta * x)",
                    "cosLowerBound": (
                        "forall eta in chunk, cosLower <= cos(eta * x)"
                    ),
                    "cosUpperBound": (
                        "forall eta in chunk, cos(eta * x) <= cosUpper"
                    ),
                    "cosAbs": "absolute enclosure radius for cos(eta * x)",
                    "rawLower": "lower value enclosure for rawOmegaIntegrand from component product",
                    "rawUpper": "upper value enclosure for rawOmegaIntegrand from component product",
                    "internalRawComponentBoundsAbsCosHelper": (
                        TAYLOR_MODEL_RAW_COMPONENT_BOUNDS_ABS_COS_HELPER
                    ),
                    "scaleNonneg": "0 <= ell / pi",
                    "omegaLowerNonneg": "0 <= omegaLower",
                    "shapeSqLowerNonneg": "0 <= shapeSqLower",
                    "cosAbsLower": "-cosAbs <= cosLower",
                    "cosAbsUpper": "cosUpper <= cosAbs",
                    "componentProductAbsLower": (
                        "rawLower <= -((ell / pi) * omegaUpper * shapeSqUpper * cosAbs)"
                    ),
                    "componentProductAbsUpper": (
                        "(ell / pi) * omegaUpper * shapeSqUpper * cosAbs <= rawUpper"
                    ),
                    "polynomialTermBounds": TAYLOR_MODEL_POLYNOMIAL_TERM_BOUNDS,
                    "termLower": "Fin (degree + 1) -> Real lower enclosure for Taylor terms",
                    "termUpper": "Fin (degree + 1) -> Real upper enclosure for Taylor terms",
                    "polynomialValueBoundsHelper": (
                        TAYLOR_MODEL_POLYNOMIAL_VALUE_BOUNDS_HELPER
                    ),
                    "internalRawValueBoundsFromComponentsHelper": (
                        TAYLOR_MODEL_RAW_INTEGRAND_VALUE_BOUNDS_FROM_COMPONENTS_HELPER
                    ),
                    "valueBoundsFromRawTermHelper": (
                        TAYLOR_MODEL_VALUE_BOUNDS_FROM_RAW_TERM_HELPER
                    ),
                    "valueBoundsFromRawComponentTermHelper": (
                        TAYLOR_MODEL_VALUE_BOUNDS_FROM_RAW_COMPONENT_TERM_HELPER
                    ),
                    "polyLower": "lower value enclosure for Taylor polynomial",
                    "polyUpper": "upper value enclosure for Taylor polynomial",
                    "valueDiffLower": (
                        "-remainder <= rawLower - polyUpper"
                    ),
                    "valueDiffUpper": (
                        "rawUpper - polyLower <= remainder"
                    ),
                    "integralLower": "chunkLower <= lowerModelIntegral",
                    "integralUpper": "upperModelIntegral <= chunkUpper",
                    "lowerBound": "targetLower n <= sum chunkLower",
                    "upperBound": "sum chunkUpper <= targetUpper n",
                    "helper": valid_constructor_for(str(block["block"]), family_kind),
                },
            }
        )
    return rows


def build_family(
    block: dict[str, Any],
    family_kind: str,
    window_block: dict[str, Any],
    target_refresh: dict[str, dict[int, dict[str, str]]],
) -> dict[str, Any]:
    block_name = str(block["block"])
    target = TARGETS[(block_name, family_kind)]
    chunk_source = (
        block["finite_window"] if family_kind == "finite" else block["positive_tail_window"]
    )
    chunks_key = target["chunks_key"]
    rows = build_distance_rows(block, family_kind, row_map(window_block), target_refresh)
    negative = sum(1 for row in rows if row["target_interval_sign"] == "negative")
    positive = sum(1 for row in rows if row["target_interval_sign"] == "positive")
    crossing = sum(1 for row in rows if row["target_interval_sign"] == "crossing")
    zero = sum(1 for row in rows if row["target_interval_sign"] == "zero")
    return {
        "id": f"{block_name}_{family_kind}",
        "collection_name": target["collection"],
        "block": block_name,
        "family_kind": family_kind,
        "k": block["k"],
        "domain": target["domain"],
        "lean_payload_type": DISTANCE_PAYLOAD,
        "lean_valid_constructor": valid_constructor_for(block_name, family_kind),
        "lean_L": target["L"],
        "lean_U": target["U"],
        "target_lower": target["target_lower"],
        "target_upper": target["target_upper"],
        "distance_count": len(rows),
        "chunk_count": len(chunk_source[chunks_key]),
        "signed_rows": {
            "positive": positive,
            "negative": negative,
            "crossing": crossing,
            "zero": zero,
        },
        "chunks": chunk_source[chunks_key],
        "distances": rows,
    }


def build_worklist(
    contract: dict[str, Any],
    window_contract: dict[str, Any],
    *,
    target_refresh: dict[str, dict[int, dict[str, str]]] | None = None,
    target_refresh_source: str | None = None,
    target_refresh_count: int = 0,
) -> dict[str, Any]:
    if contract.get("schema") != "q3_psdpd_step33_a_signed_chunk_payload_contract.v1":
        raise ValueError(f"unexpected signed contract schema: {contract.get('schema')!r}")
    if window_contract.get("schema") != "q3_psdpd_step33_a_window_contract.v1":
        raise ValueError(f"unexpected window contract schema: {window_contract.get('schema')!r}")

    target_refresh = target_refresh or {}
    windows = block_map(window_contract)
    families: list[dict[str, Any]] = []
    for block in contract["blocks"]:
        name = str(block["block"])
        window_block = windows[name]
        families.append(build_family(block, "finite", window_block, target_refresh))
        families.append(build_family(block, "tail", window_block, target_refresh))

    distance_rows = sum(family["distance_count"] for family in families)
    chunk_cells = sum(
        family["distance_count"] * family["chunk_count"] for family in families
    )
    return {
        "schema": "q3_psdpd_step33_a_distance_payload_worklist.v1",
        "meaning": (
            "Exact Step33A.1-A worklist for the next proof-producing "
            "distance-payload generator."
        ),
        "source_contract": contract.get("schema"),
        "source_window_contract": window_contract.get("schema"),
        "finite_route": "raw_omega_positive_axis_direct",
        "target_refresh_probe": target_refresh_source,
        "target_refresh_rows": target_refresh_count,
        "lean_payload_type": DISTANCE_PAYLOAD,
        "lean_nat_payload_type": NAT_DISTANCE_PAYLOAD,
        "lean_fin_chunk_value_adapter": FIN_CHUNK_VALUE_ADAPTER,
        "lean_chunked_range_payload_type": CHUNKED_RANGE_PAYLOAD,
        "lean_taylor_model_certificate": TAYLOR_MODEL_CERT,
        "lean_taylor_model_valid": TAYLOR_MODEL_VALID,
        "lean_taylor_model_value_bounds": TAYLOR_MODEL_VALUE_BOUNDS,
        "lean_taylor_model_polynomial_term_bounds": (
            TAYLOR_MODEL_POLYNOMIAL_TERM_BOUNDS
        ),
        "lean_taylor_model_polynomial_value_bounds_helper": (
            TAYLOR_MODEL_POLYNOMIAL_VALUE_BOUNDS_HELPER
        ),
        "lean_taylor_model_value_bounds_from_raw_term_helper": (
            TAYLOR_MODEL_VALUE_BOUNDS_FROM_RAW_TERM_HELPER
        ),
        "lean_taylor_model_raw_integrand_component_bounds": (
            TAYLOR_MODEL_RAW_INTEGRAND_COMPONENT_BOUNDS
        ),
        "lean_taylor_model_raw_component_bounds_abs_cos_helper": (
            TAYLOR_MODEL_RAW_COMPONENT_BOUNDS_ABS_COS_HELPER
        ),
        "lean_taylor_model_raw_integrand_value_bounds_from_components_helper": (
            TAYLOR_MODEL_RAW_INTEGRAND_VALUE_BOUNDS_FROM_COMPONENTS_HELPER
        ),
        "lean_taylor_model_value_bounds_from_raw_component_term_helper": (
            TAYLOR_MODEL_VALUE_BOUNDS_FROM_RAW_COMPONENT_TERM_HELPER
        ),
        "lean_taylor_model_abs_cos_component_term_bounds": (
            TAYLOR_MODEL_ABS_COS_COMPONENT_TERM_BOUNDS
        ),
        "lean_taylor_model_abs_cos_component_term_bounds_value_helper": (
            TAYLOR_MODEL_ABS_COS_COMPONENT_TERM_BOUNDS_VALUE_HELPER
        ),
        "lean_taylor_model_abs_cos_chunk_proof_data": (
            TAYLOR_MODEL_ABS_COS_CHUNK_PROOF_DATA
        ),
        "lean_taylor_model_abs_cos_chunk_proof_data_valid_helper": (
            TAYLOR_MODEL_ABS_COS_CHUNK_PROOF_DATA_VALID_HELPER
        ),
        "lean_taylor_model_lower_integral": TAYLOR_MODEL_LOWER_INTEGRAL,
        "lean_taylor_model_upper_integral": TAYLOR_MODEL_UPPER_INTEGRAL,
        "lean_taylor_model_valid_generic_constructor": (
            TAYLOR_MODEL_VALID_GENERIC_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_finite_chunk_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_FINITE_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_tail_chunk_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_TAIL_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_finite_chunk_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_FINITE_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_tail_chunk_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_TAIL_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_value_generic_constructor": (
            TAYLOR_MODEL_VALID_VALUE_GENERIC_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_value_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_VALUE_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_value_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_VALUE_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_finite_value_chunk_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_FINITE_VALUE_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_tail_value_chunk_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_TAIL_VALUE_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_finite_value_chunk_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_FINITE_VALUE_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_tail_value_chunk_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_TAIL_VALUE_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_finite_raw_term_chunk_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_FINITE_RAW_TERM_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_tail_raw_term_chunk_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_TAIL_RAW_TERM_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_finite_raw_term_chunk_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_FINITE_RAW_TERM_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_tail_raw_term_chunk_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_TAIL_RAW_TERM_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_finite_raw_component_term_chunk_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_FINITE_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_primary_tail_raw_component_term_chunk_constructor": (
            TAYLOR_MODEL_VALID_PRIMARY_TAIL_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_finite_raw_component_term_chunk_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_FINITE_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR
        ),
        "lean_taylor_model_valid_control_tail_raw_component_term_chunk_constructor": (
            TAYLOR_MODEL_VALID_CONTROL_TAIL_RAW_COMPONENT_TERM_CHUNK_CONSTRUCTOR
        ),
        "lean_exact_integrand_distance_helper": EXACT_INTEGRAND_DISTANCE_HELPER,
        "lean_distance_assembler": DISTANCE_ASSEMBLER,
        "lean_chunked_range_assembler": CHUNKED_RANGE_ASSEMBLER,
        "lean_step33a_wrapper": STEP33A_WRAPPER,
        "lean_step33b_wrapper": STEP33B_WRAPPER,
        "lean_step33c_wrapper": STEP33C_WRAPPER,
        "global_totals": {
            "families": len(families),
            "distance_rows": distance_rows,
            "chunk_cells": chunk_cells,
        },
        "current_missing_layer": [
            "radius/nonnegativity checks for every Taylor chunk",
            "structural finite/tail endpoint checks are discharged by chunk constructors",
            "Omega/shape-squared/cos component enclosures on every chunk",
            "component product comparisons producing raw integrand value enclosures",
            "Taylor polynomial term enclosures and summed polynomial value bounds",
            "raw/term constructor comparisons implying the Taylor diff enclosure",
            "explicit Taylor model integral endpoint comparisons for every chunk",
            "distance-level sum comparisons against generated targets",
        ],
        "not_part_of_this_route": [
            "global A radius update",
            "CSV rewrite",
            "radius-floor regeneration",
            "23x23 entry crawl",
            "Q3.Main or H1/PO3 reroute",
        ],
        "families": families,
    }


def render_md(worklist: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Distance Payload Worklist",
        "",
        "This file is generated worklist data, not a Lean proof object.",
        "It names the exact distance-compressed payloads still missing for the",
        "Arch-side A finite-tail analytic cert gate.",
        "",
        "## Lean receiver",
        "",
        f"- payload row type: `{worklist['lean_payload_type']}`",
        f"- compatibility payload row type: `{worklist['lean_nat_payload_type']}`",
        f"- Fin-to-Nat chunk adapter: `{worklist['lean_fin_chunk_value_adapter']}`",
        f"- Taylor/model certificate: `{worklist['lean_taylor_model_certificate']}`",
        f"- Taylor/model validity proof: `{worklist['lean_taylor_model_valid']}`",
        f"- Taylor value bounds: `{worklist['lean_taylor_model_value_bounds']}`",
        (
            "- Taylor polynomial term bounds: "
            f"`{worklist['lean_taylor_model_polynomial_term_bounds']}`"
        ),
        (
            "- polynomial value-bound helper: "
            f"`{worklist['lean_taylor_model_polynomial_value_bounds_helper']}`"
        ),
        (
            "- value bounds from raw/term helper: "
            f"`{worklist['lean_taylor_model_value_bounds_from_raw_term_helper']}`"
        ),
        (
            "- raw integrand component bounds: "
            f"`{worklist['lean_taylor_model_raw_integrand_component_bounds']}`"
        ),
        (
            "- raw component abs-cos product helper: "
            f"`{worklist['lean_taylor_model_raw_component_bounds_abs_cos_helper']}`"
        ),
        (
            "- raw value bounds from component helper: "
            f"`{worklist['lean_taylor_model_raw_integrand_value_bounds_from_components_helper']}`"
        ),
        (
            "- value bounds from raw component/term helper: "
            f"`{worklist['lean_taylor_model_value_bounds_from_raw_component_term_helper']}`"
        ),
        (
            "- abs-cos component/term record: "
            f"`{worklist['lean_taylor_model_abs_cos_component_term_bounds']}`"
        ),
        (
            "- abs-cos component/term record value helper: "
            f"`{worklist['lean_taylor_model_abs_cos_component_term_bounds_value_helper']}`"
        ),
        (
            "- abs-cos chunk proof-data record: "
            f"`{worklist['lean_taylor_model_abs_cos_chunk_proof_data']}`"
        ),
        (
            "- abs-cos chunk proof-data valid helper: "
            f"`{worklist['lean_taylor_model_abs_cos_chunk_proof_data_valid_helper']}`"
        ),
        f"- lower model integral: `{worklist['lean_taylor_model_lower_integral']}`",
        f"- upper model integral: `{worklist['lean_taylor_model_upper_integral']}`",
        (
            "- generic validity constructor: "
            f"`{worklist['lean_taylor_model_valid_generic_constructor']}`"
        ),
        (
            "- primary validity constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_constructor']}`"
        ),
        (
            "- control validity constructor: "
            f"`{worklist['lean_taylor_model_valid_control_constructor']}`"
        ),
        (
            "- primary finite chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_finite_chunk_constructor']}`"
        ),
        (
            "- primary tail chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_tail_chunk_constructor']}`"
        ),
        (
            "- control finite chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_control_finite_chunk_constructor']}`"
        ),
        (
            "- control tail chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_control_tail_chunk_constructor']}`"
        ),
        (
            "- generic value-bound constructor: "
            f"`{worklist['lean_taylor_model_valid_value_generic_constructor']}`"
        ),
        (
            "- primary value-bound constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_value_constructor']}`"
        ),
        (
            "- control value-bound constructor: "
            f"`{worklist['lean_taylor_model_valid_control_value_constructor']}`"
        ),
        (
            "- primary finite value-bound chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_finite_value_chunk_constructor']}`"
        ),
        (
            "- primary tail value-bound chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_tail_value_chunk_constructor']}`"
        ),
        (
            "- control finite value-bound chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_control_finite_value_chunk_constructor']}`"
        ),
        (
            "- control tail value-bound chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_control_tail_value_chunk_constructor']}`"
        ),
        (
            "- primary finite raw/term chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_finite_raw_term_chunk_constructor']}`"
        ),
        (
            "- primary tail raw/term chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_tail_raw_term_chunk_constructor']}`"
        ),
        (
            "- control finite raw/term chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_control_finite_raw_term_chunk_constructor']}`"
        ),
        (
            "- control tail raw/term chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_control_tail_raw_term_chunk_constructor']}`"
        ),
        (
            "- primary finite raw component abs-cos/term chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_finite_raw_component_term_chunk_constructor']}`"
        ),
        (
            "- primary tail raw component abs-cos/term chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_primary_tail_raw_component_term_chunk_constructor']}`"
        ),
        (
            "- control finite raw component abs-cos/term chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_control_finite_raw_component_term_chunk_constructor']}`"
        ),
        (
            "- control tail raw component abs-cos/term chunk constructor: "
            f"`{worklist['lean_taylor_model_valid_control_tail_raw_component_term_chunk_constructor']}`"
        ),
        f"- exact-integrand row helper: `{worklist['lean_exact_integrand_distance_helper']}`",
        f"- distance assembler: `{worklist['lean_distance_assembler']}`",
        f"- chunked-range payload: `{worklist['lean_chunked_range_payload_type']}`",
        f"- chunked-range assembler: `{worklist['lean_chunked_range_assembler']}`",
        f"- Step33A wrapper: `{worklist['lean_step33a_wrapper']}`",
        f"- Step33B wrapper: `{worklist['lean_step33b_wrapper']}`",
        f"- Step33C wrapper: `{worklist['lean_step33c_wrapper']}`",
        "",
        "## Totals",
        "",
        f"- families: `{worklist['global_totals']['families']}`",
        f"- distance rows: `{worklist['global_totals']['distance_rows']}`",
        f"- distance/chunk cells: `{worklist['global_totals']['chunk_cells']}`",
        f"- local target refresh rows: `{worklist['target_refresh_rows']}`",
        "",
        "## Current missing layer",
        "",
    ]
    for item in worklist["current_missing_layer"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Route guard", ""])
    for item in worklist["not_part_of_this_route"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Families",
            "",
            "| family | k | domain | target lower | target upper | distances | chunks | target signs |",
            "| --- | ---: | --- | --- | --- | ---: | ---: | --- |",
        ]
    )
    for family in worklist["families"]:
        signs = family["signed_rows"]
        lines.append(
            "| {id} | {k} | {domain} | `{target_lower}` | `{target_upper}` | "
            "{distance_count} | {chunk_count} | +{pos}/-{neg}/x{cross}/z{zero} |".format(
                id=family["id"],
                k=family["k"],
                domain=family["domain"],
                target_lower=family["target_lower"],
                target_upper=family["target_upper"],
                distance_count=family["distance_count"],
                chunk_count=family["chunk_count"],
                pos=signs["positive"],
                neg=signs["negative"],
                cross=signs["crossing"],
                zero=signs["zero"],
            )
        )

    for family in worklist["families"]:
        lines.extend(
            [
                "",
                f"## {family['id']}",
                "",
                f"- collection name: `{family['collection_name']}`",
                f"- validity constructor: `{family['lean_valid_constructor']}`",
                f"- Lean L: `{family['lean_L']}`",
                f"- Lean U: `{family['lean_U']}`",
                "",
                "| idx | d | target sign | route tail sign | target lower | target upper | tail slack | tail excess | priority |",
                "| ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for row in family["distances"]:
            lines.append(
                "| {index} | {distance} | {target_interval_sign} | "
                "{route_positive_window_sign} | {target_lower_value} | "
                "{target_upper_value} | {tail_radius_slack} | "
                "{tail_excess} | {priority} |".format(**row)
            )
        refreshed = [row for row in family["distances"] if row["target_refresh_applied"]]
        if refreshed:
            lines.extend(
                [
                    "",
                    "| refreshed idx | guard | needed slack | slack after |",
                    "| ---: | ---: | ---: | ---: |",
                ]
            )
            for row in refreshed:
                lines.append(
                    "| {index} | {target_refresh_guard} | "
                    "{target_refresh_needed_slack} | {target_refresh_slack_after} |".format(
                        **row
                    )
                )
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--window-contract", type=Path, default=DEFAULT_WINDOW_CONTRACT)
    parser.add_argument(
        "--target-refresh-probe",
        type=Path,
        help=(
            "Optional local raw-Omega chunk probe JSON. Slack-absorbable rows "
            "refresh worklist target values to match the generated arithmetic import."
        ),
    )
    parser.add_argument("--out-json", type=Path)
    parser.add_argument("--out-md", type=Path)
    args = parser.parse_args()

    contract = load_json(args.contract)
    window_contract = load_json(args.window_contract)
    target_refresh, refresh_count = load_target_refresh(args.target_refresh_probe)
    worklist = build_worklist(
        contract,
        window_contract,
        target_refresh=target_refresh,
        target_refresh_source=(
            str(args.target_refresh_probe) if args.target_refresh_probe is not None else None
        ),
        target_refresh_count=refresh_count,
    )

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(worklist, indent=2, sort_keys=True) + "\n")
    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_md(worklist), encoding="utf-8")

    totals = worklist["global_totals"]
    print(
        "families={families} distance_rows={distance_rows} "
        "distance_chunk_cells={chunk_cells} target_refresh_rows={refresh}".format(
            refresh=refresh_count,
            **totals,
        )
    )
    for family in worklist["families"]:
        signs = family["signed_rows"]
        print(
            "{id}: k={k} domain={domain} distances={distance_count} chunks={chunk_count} "
            "target_signs=+{pos}/-{neg}/x{cross}/z{zero}".format(
                id=family["id"],
                k=family["k"],
                domain=family["domain"],
                distance_count=family["distance_count"],
                chunk_count=family["chunk_count"],
                pos=signs["positive"],
                neg=signs["negative"],
                cross=signs["crossing"],
                zero=signs["zero"],
            )
        )


if __name__ == "__main__":
    run()
