#!/usr/bin/env python3
"""Fail-closed contract for Step33A.1-A Omega closed-form endpoint rows.

This script does not emit Lean proofs.  It turns the active endpoint worklist
into an exact proof-data contract for the next generated theorem:

    rawOmegaEndpointClosedFormBounds_generated

The preferred Lean receiver is:

    Step22OmegaClosedFormEndpointBoundsCert
      .of_re_series_anchor_interval_tail_trigamma_im_closed_form_term_prefix_cubic_tail_Icc

Rows must remain fail-closed until the trigamma term-prefix/tail-majorant data
and the direct real-series Omega anchor data are generated as Lean-checkable
proof data.  The old absolute-tail anchor receiver remains available as a
fallback, but it is not the active target because the tight small-eta rows make
plain absolute tails impractical.  Schema v13 records the combined checked
prefix/tail closed-form receiver below the positive p-series receiver:
the generator should now prove finite q2/q3 prefix comparisons and rational
comparisons against the closed tail formula, then let Lean assemble the signed
Omega anchor tail.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_component_endpoint_worklist.json"
)
DEFAULT_OUT_JSON = REQUEST_DIR / "a_omega_closed_form_endpoint_contract.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_omega_closed_form_endpoint_contract.md"

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.v21"
)
SCHEMA = "q3_psdpd_step33_a_omega_closed_form_endpoint_contract.v14"

RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "Step22OmegaClosedFormEndpointBoundsCert."
    "of_re_series_anchor_interval_tail_trigamma_im_closed_form_term_prefix_cubic_tail_Icc"
)
ABS_TAIL_FALLBACK_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "Step22OmegaClosedFormEndpointBoundsCert."
    "of_re_series_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc"
)
DERIVATIVE_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "Step22OmegaClosedFormEndpointBoundsCert."
    "of_direct_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc"
)
TARGET_THEOREM = "rawOmegaEndpointClosedFormBounds_generated"
NEXT_THEOREM = "rawOmegaEndpointValueDerivIntervalCert_generated"
FIRST_ROW_PILOT_LEAN = (
    "q3.lean.aristotle/aristotle_input/step33_endpoint_v18_first_row_pilot.lean"
)
FIRST_ROW_PROOF_PACK = (
    "q3.lean.aristotle/aristotle_input/step33_endpoint_v18_first_row_proof_pack.md"
)
FIRST_ROW_CONTEXT_BUNDLE_SCRIPT = (
    "q3.lean.aristotle/scripts/q3_psdpd_step33_endpoint_first_row_context_bundle.py"
)
FIRST_ROW_OMEGA_TARGET = (
    "primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_aristotle_v18"
)
FIRST_ROW_SHAPESQ_TARGET = (
    "primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_aristotle_v18"
)
FIRST_ROW_COMBINER = (
    "primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_aristotle_v18"
)
TAIL_MAJORANT_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "abs_trigammaImSeriesTermClosedForm_le_etaUpper_cubic"
)
TAIL_MAJORANT_SUMMABLE_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "summable_trigammaImSeriesTermClosedForm_cubic_majorant"
)
TAIL_MAJORANT_SERIES = (
    "g n = etaUpper / ((((n + derivN : Nat) : Real) + 1/4)^3)"
)
ANCHOR_RE_SERIES_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeight_bounds_from_re_series_prefix_tail_abs"
)
ANCHOR_RE_SERIES_INTERVAL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeight_bounds_from_re_series_prefix_tail_interval"
)
ANCHOR_RE_SERIES_ACCELERATED_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeightReSeries_tail_bounds_from_model_abs_error"
)
GENERIC_ACCELERATED_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_shifted_tail_bounds_of_model_abs_error"
)
GENERIC_NONNEG_PREFIX_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "nonneg_tsum_bounds_of_sum_range_tail_upper"
)
ANCHOR_RE_SERIES_LEADING_QUADRATIC_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_model_error"
)
ANCHOR_RE_SERIES_POSITIVE_SERIES_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_positive_series_bounds"
)
ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "abs_step22OmegaArchWeightReSeriesTerm_sub_leading_quadratic_model_le_cubic"
)
ANCHOR_RE_SERIES_LEADING_QUADRATIC_SUMMABLE_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "summable_one_div_nat_add_quarter_sq"
)
ANCHOR_RE_SERIES_LEADING_CUBIC_SUMMABLE_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "summable_one_div_nat_add_quarter_cubic"
)
ANCHOR_RE_SERIES_Q2_TAIL_CLOSED_FORM_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_one_div_nat_add_quarter_sq_le_inv_pred"
)
ANCHOR_RE_SERIES_Q3_TAIL_CLOSED_FORM_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_const_mul_one_div_nat_add_quarter_cubic_le"
)
ANCHOR_RE_SERIES_Q2_SHIFTED_TAIL_CLOSED_FORM_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_anchor_q2_shifted_tail_le_closed_form"
)
ANCHOR_RE_SERIES_Q3_SHIFTED_TAIL_CLOSED_FORM_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_anchor_q3_shifted_tail_le_closed_form"
)
ANCHOR_RE_SERIES_PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_prefix_tail_closed_form"
)
ANCHOR_RE_SERIES_TERM = (
    "1/(n+1) - (n+1/4)/((n+1/4)^2 + (eta/2)^2)"
)
ANCHOR_RE_SERIES_LEADING_QUADRATIC_MODEL = (
    "model n = -(3/4) / ((((n + anchorN : Nat) : Real) + 1/4)^2)"
)
ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_MAJORANT = (
    "g n = ((3/4)^2 + (etaUpper/2)^2) / "
    "((((n + anchorN : Nat) : Real) + 1/4)^3)"
)
ANCHOR_RE_SERIES_Q2_SERIES = (
    "q2 n = 1 / ((((n + anchorN : Nat) : Real) + 1/4)^2)"
)
ANCHOR_RE_SERIES_Q3_SERIES = ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_MAJORANT

REQUIRED_GENERATED_FIELDS = [
    "derivN",
    "anchorN",
    "etaUpper",
    "termLower",
    "termUpper",
    "imPrefixLower",
    "imPrefixUpper",
    "tailRadius",
    "hANonneg",
    "hBUpper",
    "hTermLower over trigammaImSeriesTermClosedForm on [a,b]",
    "hTermUpper over trigammaImSeriesTermClosedForm on [a,b]",
    "hPrefixLower",
    "hPrefixUpper",
    "hCubicTailSum",
    "hDerivLower",
    "hDerivUpper",
    "anchorConstLower",
    "anchorConstUpper",
    "anchorPrefixLower",
    "anchorPrefixUpper",
    "anchorTailLower",
    "anchorTailUpper",
    "anchorQ2Lower",
    "anchorQ2Upper",
    "anchorQ3Upper",
    "anchorQ2PrefixN",
    "anchorQ2PrefixLower",
    "anchorQ2PrefixUpper",
    "anchorQ2TailUpper",
    "anchorQ2TailIndex",
    "anchorQ2TailClosedFormUpper",
    "anchorQ3PrefixN",
    "anchorQ3PrefixUpper",
    "anchorQ3TailUpper",
    "anchorQ3TailIndex",
    "anchorQ3TailCoeff",
    "anchorQ3TailClosedFormUpper",
    "hAnchorConstLower",
    "hAnchorConstUpper",
    "hAnchorPrefixLower",
    "hAnchorPrefixUpper",
    "hAnchorQ2Lower",
    "hAnchorQ2Upper",
    "hAnchorQ3Upper",
    "hAnchorQ2PrefixLower",
    "hAnchorQ2PrefixUpper",
    "hAnchorQ2TailIndexEq",
    "hAnchorQ2TailIndexGeOne",
    "hAnchorQ2TailClosedFormUpper",
    "hAnchorQ2TailUpperFromClosedForm",
    "hAnchorQ2TailUpper",
    "hAnchorQ3PrefixUpper",
    "hAnchorQ3TailIndexEq",
    "hAnchorQ3TailIndexGeOne",
    "hAnchorQ3TailCoeffNonneg",
    "hAnchorQ3TailClosedFormUpper",
    "hAnchorQ3TailUpperFromClosedForm",
    "hAnchorQ3TailUpper",
    "hAnchorTailLowerFromPositiveSeries",
    "hAnchorTailUpperFromPositiveSeries",
    "hAnchorLowerFromReSeries",
    "hAnchorUpperFromReSeries",
]

PROOF_DATA_GROUPS = [
    {
        "name": "derivative_trigamma_prefix_tail",
        "status": "missing_lean_proof_data",
        "receiver": DERIVATIVE_RECEIVER,
        "fields": [
            "derivN",
            "etaUpper",
            "termLower",
            "termUpper",
            "imPrefixLower",
            "imPrefixUpper",
            "hANonneg",
            "hBUpper",
            "hTermLower over trigammaImSeriesTermClosedForm on [a,b]",
            "hTermUpper over trigammaImSeriesTermClosedForm on [a,b]",
            "hPrefixLower",
            "hPrefixUpper",
            "hCubicTailSum",
            "hDerivLower",
            "hDerivUpper",
        ],
        "checkedCommonLemmas": [
            TAIL_MAJORANT_LEMMA,
            TAIL_MAJORANT_SUMMABLE_LEMMA,
        ],
    },
    {
        "name": "anchor_re_series_prefix_signed_tail",
        "status": "missing_lean_proof_data",
        "receiver": ANCHOR_RE_SERIES_INTERVAL_LEMMA,
        "fields": [
            "anchorN",
            "anchorConstLower",
            "anchorConstUpper",
            "anchorPrefixLower",
            "anchorPrefixUpper",
            "anchorTailLower",
            "anchorTailUpper",
            "hAnchorConstLower",
            "hAnchorConstUpper",
            "hAnchorPrefixLower",
            "hAnchorPrefixUpper",
            "hAnchorTailLower",
            "hAnchorTailUpper",
            "hAnchorLowerFromReSeries",
            "hAnchorUpperFromReSeries",
        ],
        "checkedCommonLemmas": [
            ANCHOR_RE_SERIES_INTERVAL_LEMMA,
            GENERIC_NONNEG_PREFIX_TAIL_LEMMA,
            ANCHOR_RE_SERIES_ACCELERATED_TAIL_LEMMA,
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_TAIL_LEMMA,
            ANCHOR_RE_SERIES_POSITIVE_SERIES_TAIL_LEMMA,
        ],
        "activeTailProducer": "anchor_re_series_positive_pseries_tail",
        "fallbackNotActive": {
            "receiver": ANCHOR_RE_SERIES_LEMMA,
            "reason": (
                "plain absolute tail requires impractically large anchorN on "
                "the active tight small-eta endpoint rows"
            ),
            "fields": [
                "anchorTailRadius",
                "hAnchorTailAbs",
            ],
        },
    },
    {
        "name": "anchor_re_series_positive_pseries_tail",
        "status": "missing_positive_pseries_sum_rows",
        "receiver": ANCHOR_RE_SERIES_POSITIVE_SERIES_TAIL_LEMMA,
        "fields": [
            "anchorN",
            "etaUpper",
            "anchorQ2Lower",
            "anchorQ2Upper",
            "anchorQ3Upper",
            "hEtaNonneg",
            "hEtaUpper",
            "hAnchorQ2Lower",
            "hAnchorQ2Upper",
            "hAnchorQ3Upper",
            "hAnchorTailLowerFromPositiveSeries",
            "hAnchorTailUpperFromPositiveSeries",
        ],
        "checkedCommonLemmas": [
            ANCHOR_RE_SERIES_POSITIVE_SERIES_TAIL_LEMMA,
            ANCHOR_RE_SERIES_PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA,
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_TAIL_LEMMA,
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_LEMMA,
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_SUMMABLE_LEMMA,
            ANCHOR_RE_SERIES_LEADING_CUBIC_SUMMABLE_LEMMA,
            GENERIC_NONNEG_PREFIX_TAIL_LEMMA,
            GENERIC_ACCELERATED_TAIL_LEMMA,
            ANCHOR_RE_SERIES_ACCELERATED_TAIL_LEMMA,
        ],
        "activeSeriesProducer": "anchor_re_series_positive_pseries_prefix_tail",
        "activePrefixTailReceiver": (
            ANCHOR_RE_SERIES_PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA
        ),
        "model": ANCHOR_RE_SERIES_LEADING_QUADRATIC_MODEL,
        "errorMajorant": ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_MAJORANT,
        "positiveSeries": [
            ANCHOR_RE_SERIES_Q2_SERIES,
            ANCHOR_RE_SERIES_Q3_SERIES,
        ],
        "fallbacksNotActive": {
            "leadingQuadraticModelRows": {
                "name": "anchor_re_series_leading_quadratic_tail",
                "receiver": ANCHOR_RE_SERIES_LEADING_QUADRATIC_TAIL_LEMMA,
                "status": "available_not_active_after_positive_series_receiver",
            },
            "genericModelRows": {
                "name": "anchor_re_series_accelerated_model_tail",
                "receiver": ANCHOR_RE_SERIES_ACCELERATED_TAIL_LEMMA,
                "status": "available_not_active_after_leading_quadratic_receiver",
            },
        },
        "feeds": [
            "hAnchorTailLower",
            "hAnchorTailUpper",
        ],
    },
    {
        "name": "anchor_re_series_positive_pseries_prefix_tail",
        "status": "missing_positive_pseries_prefix_rows_and_closed_tail_comparisons",
        "receiver": ANCHOR_RE_SERIES_PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA,
        "fields": [
            "anchorN",
            "etaUpper",
            "anchorQ2PrefixN",
            "anchorQ2PrefixLower",
            "anchorQ2PrefixUpper",
            "anchorQ2TailUpper",
            "anchorQ2TailIndex",
            "anchorQ2TailClosedFormUpper",
            "anchorQ3PrefixN",
            "anchorQ3PrefixUpper",
            "anchorQ3TailUpper",
            "anchorQ3TailIndex",
            "anchorQ3TailCoeff",
            "anchorQ3TailClosedFormUpper",
            "hAnchorQ2PrefixLower",
            "hAnchorQ2PrefixUpper",
            "hAnchorQ2TailIndexEq",
            "hAnchorQ2TailIndexGeOne",
            "hAnchorQ2TailClosedFormUpper",
            "hAnchorQ2TailUpperFromClosedForm",
            "hAnchorQ2TailUpper",
            "hAnchorQ3PrefixUpper",
            "hAnchorQ3TailIndexEq",
            "hAnchorQ3TailIndexGeOne",
            "hAnchorQ3TailCoeffNonneg",
            "hAnchorQ3TailClosedFormUpper",
            "hAnchorQ3TailUpperFromClosedForm",
            "hAnchorQ3TailUpper",
        ],
        "checkedCommonLemmas": [
            ANCHOR_RE_SERIES_PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA,
            GENERIC_NONNEG_PREFIX_TAIL_LEMMA,
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_SUMMABLE_LEMMA,
            ANCHOR_RE_SERIES_LEADING_CUBIC_SUMMABLE_LEMMA,
            ANCHOR_RE_SERIES_Q2_TAIL_CLOSED_FORM_LEMMA,
            ANCHOR_RE_SERIES_Q3_TAIL_CLOSED_FORM_LEMMA,
            ANCHOR_RE_SERIES_Q2_SHIFTED_TAIL_CLOSED_FORM_LEMMA,
            ANCHOR_RE_SERIES_Q3_SHIFTED_TAIL_CLOSED_FORM_LEMMA,
        ],
        "tailUpperProducer": "checked_telescoping_closed_form_tail_bounds",
        "closedTailBounds": {
            "anchorQ2TailIndex": "anchorN + anchorQ2PrefixN",
            "anchorQ2TailClosedFormUpper": (
                "1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1)"
            ),
            "anchorQ3TailIndex": "anchorN + anchorQ3PrefixN",
            "anchorQ3TailCoeff": "((3/4)^2 + (etaUpper/2)^2)",
            "anchorQ3TailClosedFormUpper": (
                "((3/4)^2 + (etaUpper/2)^2) * "
                "(1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2))"
            ),
        },
        "series": [
            ANCHOR_RE_SERIES_Q2_SERIES,
            ANCHOR_RE_SERIES_Q3_SERIES,
        ],
        "feeds": [
            "hAnchorTailLower",
            "hAnchorTailUpper",
        ],
    },
    {
        "name": "anchor_re_series_prefix_abs_tail_fallback",
        "status": "available_not_active",
        "receiver": ANCHOR_RE_SERIES_LEMMA,
        "fields": [
            "anchorN",
            "anchorConstLower",
            "anchorConstUpper",
            "anchorPrefixLower",
            "anchorPrefixUpper",
            "anchorTailRadius",
            "hAnchorConstLower",
            "hAnchorConstUpper",
            "hAnchorPrefixLower",
            "hAnchorPrefixUpper",
            "hAnchorTailAbs",
            "hAnchorLowerFromReSeries",
            "hAnchorUpperFromReSeries",
        ],
        "checkedCommonLemmas": [
            ANCHOR_RE_SERIES_LEMMA,
        ],
    },
    {
        "name": "endpoint_rational_containment",
        "status": "already_generated_checked_after_endpoint_packages",
        "receiver": (
            "primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_"
            "of_endpoint_bounds_generated"
        ),
        "fields": [
            "hOmegaContain",
            "hShapeSqContain",
            "hOmegaLower",
            "hOmegaUpper",
            "hShapeSqLower",
            "hShapeSqUpper",
        ],
        "checkedCommonLemmas": [],
    },
]

WORKLIST_ENDPOINTS = {
    "omegaDerivLower",
    "omegaDerivUpper",
    "omegaAnchorLower",
    "omegaAnchorUpper",
}


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_worklist(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != WORKLIST_SCHEMA:
        raise ValueError(f"{path}: expected schema {WORKLIST_SCHEMA!r}, found {schema!r}")


def row_label(row: dict[str, Any]) -> str:
    return (
        f"{row['family']} row={row['row']} parent={row['parentChunk']} "
        f"split={row['split']} sub={row['subchunk']}"
    )


def endpoint_fact_map(row: dict[str, Any]) -> dict[str, dict[str, Any]]:
    facts = {}
    for item in row.get("endpointFacts") or []:
        endpoint = item.get("endpoint")
        if endpoint in WORKLIST_ENDPOINTS:
            facts[str(endpoint)] = item
    return facts


def omega_endpoint_candidates(row: dict[str, Any]) -> dict[str, str | None]:
    facts = endpoint_fact_map(row)
    return {
        endpoint: (
            str(facts[endpoint]["candidateRational"])
            if endpoint in facts and facts[endpoint].get("candidateRational") is not None
            else None
        )
        for endpoint in sorted(WORKLIST_ENDPOINTS)
    }


def omega_candidate_statuses(row: dict[str, Any]) -> dict[str, str | None]:
    facts = endpoint_fact_map(row)
    return {
        endpoint: (
            str(facts[endpoint]["status"])
            if endpoint in facts and facts[endpoint].get("status") is not None
            else None
        )
        for endpoint in sorted(WORKLIST_ENDPOINTS)
    }


def endpoint_targets(row: dict[str, Any], endpoints: set[str]) -> list[dict[str, Any]]:
    targets = []
    for item in row.get("endpointFacts") or []:
        endpoint = item.get("endpoint")
        if endpoint not in endpoints:
            continue
        targets.append(
            {
                "endpoint": endpoint,
                "field": item.get("field"),
                "statement": item.get("statement"),
                "candidateRational": item.get("candidateRational"),
                "candidateDecimal": item.get("candidateDecimal"),
                "status": item.get("status"),
            }
        )
    return targets


def first_row_proof_request(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "status": "ready_for_first_row_proof_data_generation_or_aristotle_after_user_ok",
        "label": row_label(row),
        "targetLeanFile": FIRST_ROW_PILOT_LEAN,
        "proofPack": FIRST_ROW_PROOF_PACK,
        "contextBundleScript": FIRST_ROW_CONTEXT_BUNDLE_SCRIPT,
        "requiresExplicitUserOKForAristotleSubmit": True,
        "omegaTargetTheorem": FIRST_ROW_OMEGA_TARGET,
        "shapeSqTargetTheorem": FIRST_ROW_SHAPESQ_TARGET,
        "checkedCombiner": FIRST_ROW_COMBINER,
        "omegaReceiver": RECEIVER,
        "omegaAbsTailFallbackReceiver": ABS_TAIL_FALLBACK_RECEIVER,
        "shapeSqPreferredReceiver": (
            "primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_"
            "of_value_deriv_anchor_value_bounds_generated"
        ),
        "shapeSqDirectAnchorSquareFallbackReceiver": (
            "primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_"
            "of_value_deriv_bounds_generated"
        ),
        "rowParameters": {
            "family": row.get("family"),
            "row": row.get("row"),
            "parentChunk": row.get("parentChunk"),
            "split": row.get("split"),
            "subchunk": row.get("subchunk"),
            "k": row.get("k"),
            "ell": row.get("ell"),
            "distance": row.get("distance"),
            "interval": row.get("interval"),
        },
        "omegaEndpointTargets": endpoint_targets(row, WORKLIST_ENDPOINTS),
        "shapeSqEndpointTargets": endpoint_targets(
            row,
            {
                "shapeValueLower",
                "shapeValueUpper",
                "shapeDerivLower",
                "shapeDerivUpper",
                "shapeAnchorValueLower",
                "shapeAnchorValueUpper",
                "shapeSqDerivLower",
                "shapeSqDerivUpper",
                "shapeSqAnchorLower",
                "shapeSqAnchorUpper",
            },
        ),
        "containmentComparisons": row.get("containmentComparisons"),
        "proofDataGroups": PROOF_DATA_GROUPS,
        "doNotUse": [
            "naive Q3.a_star migration",
            "-Q3.a_star scalar fit",
            "A CSV or ARadius widening",
            "radius-floor or LDL rebuild",
            "Q3.Main/H1/PO3 routing",
        ],
    }


def build_row_contract(row: dict[str, Any]) -> dict[str, Any]:
    interval = row.get("interval") or {}
    return {
        "label": row_label(row),
        "family": row.get("family"),
        "row": row.get("row"),
        "parentChunk": row.get("parentChunk"),
        "split": row.get("split"),
        "subchunk": row.get("subchunk"),
        "interval": {
            "a": interval.get("a"),
            "b": interval.get("b"),
            "anchor": interval.get("anchor"),
        },
        "availableFromEndpointWorklist": omega_endpoint_candidates(row),
        "candidateStatuses": omega_candidate_statuses(row),
        "missingProofData": REQUIRED_GENERATED_FIELDS,
        "receiver": RECEIVER,
        "absTailFallbackReceiver": ABS_TAIL_FALLBACK_RECEIVER,
        "derivativeReceiver": DERIVATIVE_RECEIVER,
        "tailMajorantLemma": TAIL_MAJORANT_LEMMA,
        "tailMajorantSummableLemma": TAIL_MAJORANT_SUMMABLE_LEMMA,
        "tailMajorantSeries": TAIL_MAJORANT_SERIES,
        "anchorReSeriesLemma": ANCHOR_RE_SERIES_LEMMA,
        "anchorReSeriesIntervalLemma": ANCHOR_RE_SERIES_INTERVAL_LEMMA,
        "genericNonnegativePrefixTailLemma": GENERIC_NONNEG_PREFIX_TAIL_LEMMA,
        "anchorReSeriesLeadingQuadraticTailLemma": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_TAIL_LEMMA
        ),
        "anchorReSeriesPositiveSeriesTailLemma": (
            ANCHOR_RE_SERIES_POSITIVE_SERIES_TAIL_LEMMA
        ),
        "anchorReSeriesLeadingQuadraticErrorLemma": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_LEMMA
        ),
        "anchorReSeriesLeadingQuadraticModel": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_MODEL
        ),
        "anchorReSeriesLeadingQuadraticErrorMajorant": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_MAJORANT
        ),
        "anchorReSeriesQ2Series": ANCHOR_RE_SERIES_Q2_SERIES,
        "anchorReSeriesQ3Series": ANCHOR_RE_SERIES_Q3_SERIES,
        "anchorReSeriesQ2TailClosedFormLemma": (
            ANCHOR_RE_SERIES_Q2_TAIL_CLOSED_FORM_LEMMA
        ),
        "anchorReSeriesQ3TailClosedFormLemma": (
            ANCHOR_RE_SERIES_Q3_TAIL_CLOSED_FORM_LEMMA
        ),
        "anchorReSeriesQ2ShiftedTailClosedFormLemma": (
            ANCHOR_RE_SERIES_Q2_SHIFTED_TAIL_CLOSED_FORM_LEMMA
        ),
        "anchorReSeriesQ3ShiftedTailClosedFormLemma": (
            ANCHOR_RE_SERIES_Q3_SHIFTED_TAIL_CLOSED_FORM_LEMMA
        ),
        "anchorReSeriesPrefixTailClosedFormTailLemma": (
            ANCHOR_RE_SERIES_PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA
        ),
        "anchorReSeriesQ2TailClosedForm": (
            "1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1)"
        ),
        "anchorReSeriesQ3TailClosedForm": (
            "((3/4)^2 + (etaUpper/2)^2) * "
            "(1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2))"
        ),
        "anchorReSeriesTerm": ANCHOR_RE_SERIES_TERM,
        "targetGeneratedTheorem": TARGET_THEOREM,
        "nextGeneratedTheorem": NEXT_THEOREM,
    }


def build_report(worklist: dict[str, Any]) -> dict[str, Any]:
    rows = [row for row in worklist.get("rows") or [] if isinstance(row, dict)]
    contracts = [build_row_contract(row) for row in rows]
    statuses: dict[str, int] = {}
    for row in contracts:
        for status in row["candidateStatuses"].values():
            key = str(status)
            statuses[key] = statuses.get(key, 0) + 1
    families = sorted({str(row.get("family")) for row in rows})
    return {
        "schema": SCHEMA,
        "status": "blocked_missing_closed_form_proof_rows_not_lean",
        "meaning": (
            "Fail-closed contract for the Omega side of "
            "rawOmegaEndpointClosedFormBounds_generated.  Candidate endpoint "
            "numbers are present in the v19 worklist, but the term-prefix, "
            "cubic-tail sum, and direct real-series anchor proofs still have "
            "to be generated and Lean-checked.  Schema v13 targets the checked "
            "signed-tail combined receiver and records the checked "
            "prefix/tail closed-form receiver below the positive p-series "
            "receiver.  This captures the large signed "
            "`-(3/4)/(n+N+1/4)^2` tail while letting the generator prove only "
            "finite q2/q3 prefix comparisons and rational comparisons against "
            "checked telescoping shifted-tail closed forms."
        ),
        "worklist": worklist.get("schema"),
        "endpointMode": worklist.get("endpointMode"),
        "targetGeneratedTheorem": TARGET_THEOREM,
        "nextGeneratedTheorem": NEXT_THEOREM,
        "receiver": RECEIVER,
        "absTailFallbackReceiver": ABS_TAIL_FALLBACK_RECEIVER,
        "derivativeReceiver": DERIVATIVE_RECEIVER,
        "tailMajorantLemma": TAIL_MAJORANT_LEMMA,
        "tailMajorantSummableLemma": TAIL_MAJORANT_SUMMABLE_LEMMA,
        "tailMajorantSeries": TAIL_MAJORANT_SERIES,
        "anchorReSeriesLemma": ANCHOR_RE_SERIES_LEMMA,
        "anchorReSeriesIntervalLemma": ANCHOR_RE_SERIES_INTERVAL_LEMMA,
        "anchorReSeriesAcceleratedTailLemma": ANCHOR_RE_SERIES_ACCELERATED_TAIL_LEMMA,
        "genericAcceleratedTailLemma": GENERIC_ACCELERATED_TAIL_LEMMA,
        "genericNonnegativePrefixTailLemma": GENERIC_NONNEG_PREFIX_TAIL_LEMMA,
        "anchorReSeriesLeadingQuadraticTailLemma": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_TAIL_LEMMA
        ),
        "anchorReSeriesPositiveSeriesTailLemma": (
            ANCHOR_RE_SERIES_POSITIVE_SERIES_TAIL_LEMMA
        ),
        "anchorReSeriesLeadingQuadraticErrorLemma": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_LEMMA
        ),
        "anchorReSeriesLeadingQuadraticSummableLemma": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_SUMMABLE_LEMMA
        ),
        "anchorReSeriesLeadingCubicSummableLemma": (
            ANCHOR_RE_SERIES_LEADING_CUBIC_SUMMABLE_LEMMA
        ),
        "anchorReSeriesLeadingQuadraticModel": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_MODEL
        ),
        "anchorReSeriesLeadingQuadraticErrorMajorant": (
            ANCHOR_RE_SERIES_LEADING_QUADRATIC_ERROR_MAJORANT
        ),
        "anchorReSeriesQ2Series": ANCHOR_RE_SERIES_Q2_SERIES,
        "anchorReSeriesQ3Series": ANCHOR_RE_SERIES_Q3_SERIES,
        "anchorReSeriesQ2TailClosedFormLemma": (
            ANCHOR_RE_SERIES_Q2_TAIL_CLOSED_FORM_LEMMA
        ),
        "anchorReSeriesQ3TailClosedFormLemma": (
            ANCHOR_RE_SERIES_Q3_TAIL_CLOSED_FORM_LEMMA
        ),
        "anchorReSeriesQ2ShiftedTailClosedFormLemma": (
            ANCHOR_RE_SERIES_Q2_SHIFTED_TAIL_CLOSED_FORM_LEMMA
        ),
        "anchorReSeriesQ3ShiftedTailClosedFormLemma": (
            ANCHOR_RE_SERIES_Q3_SHIFTED_TAIL_CLOSED_FORM_LEMMA
        ),
        "anchorReSeriesPrefixTailClosedFormTailLemma": (
            ANCHOR_RE_SERIES_PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA
        ),
        "anchorReSeriesQ2TailClosedForm": (
            "1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1)"
        ),
        "anchorReSeriesQ3TailClosedForm": (
            "((3/4)^2 + (etaUpper/2)^2) * "
            "(1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2))"
        ),
        "anchorReSeriesTerm": ANCHOR_RE_SERIES_TERM,
        "closedFormTerm": (
            "trigammaImSeriesTermClosedForm eta n = "
            "-((2 * (n + 1/4) * (eta/2)) / "
            "(((n + 1/4)^2 + (eta/2)^2)^2))"
        ),
        "rows": len(rows),
        "families": families,
        "candidateStatusCounts": statuses,
        "requiredGeneratedFields": REQUIRED_GENERATED_FIELDS,
        "proofDataGroups": PROOF_DATA_GROUPS,
        "firstRowProofDataRequest": (
            first_row_proof_request(rows[0]) if rows else None
        ),
        "contracts": contracts,
        "routeGuard": [
            "do not emit rawOmegaEndpointClosedFormBounds_generated until each row has proof data",
            "candidate endpoint rationals are not Lean proofs",
            "do not route tight direct anchors through Stieltjes main/error",
            "prefer signed/accelerated anchor-tail intervals over absolute anchor tails",
            "do not call Step33A.1-A or A hbox closed from this contract",
            "do not edit A CSV, ARadius, radius-floor, or LDL",
            "do not touch Q3.Main, H1, or PO3",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Omega Closed-Form Endpoint Contract",
        "",
        f"- Schema: `{report['schema']}`",
        f"- Status: `{report['status']}`",
        f"- Worklist: `{report['worklist']}`",
        f"- Endpoint mode: `{report['endpointMode']}`",
        f"- Target theorem: `{report['targetGeneratedTheorem']}`",
        f"- Next theorem: `{report['nextGeneratedTheorem']}`",
        f"- Receiver: `{report['receiver']}`",
        f"- Absolute-tail fallback receiver: `{report['absTailFallbackReceiver']}`",
        f"- Derivative sub-receiver: `{report['derivativeReceiver']}`",
        f"- Tail majorant lemma: `{report['tailMajorantLemma']}`",
        f"- Tail majorant summable lemma: `{report['tailMajorantSummableLemma']}`",
        f"- Anchor re-series lemma: `{report['anchorReSeriesLemma']}`",
        f"- Anchor signed-tail lemma: `{report['anchorReSeriesIntervalLemma']}`",
        f"- Anchor accelerated-tail lemma: `{report['anchorReSeriesAcceleratedTailLemma']}`",
        f"- Generic accelerated-tail lemma: `{report['genericAcceleratedTailLemma']}`",
        f"- Generic nonnegative prefix/tail lemma: `{report['genericNonnegativePrefixTailLemma']}`",
        f"- Anchor leading quadratic tail lemma: `{report['anchorReSeriesLeadingQuadraticTailLemma']}`",
        f"- Anchor positive p-series tail lemma: `{report['anchorReSeriesPositiveSeriesTailLemma']}`",
        f"- Anchor leading quadratic error lemma: `{report['anchorReSeriesLeadingQuadraticErrorLemma']}`",
        f"- Anchor q2 closed tail lemma: `{report['anchorReSeriesQ2TailClosedFormLemma']}`",
        f"- Anchor q3 closed tail lemma: `{report['anchorReSeriesQ3TailClosedFormLemma']}`",
        f"- Anchor q2 shifted closed tail lemma: `{report['anchorReSeriesQ2ShiftedTailClosedFormLemma']}`",
        f"- Anchor q3 shifted closed tail lemma: `{report['anchorReSeriesQ3ShiftedTailClosedFormLemma']}`",
        f"- Anchor prefix/tail closed-form tail lemma: `{report['anchorReSeriesPrefixTailClosedFormTailLemma']}`",
        f"- Rows: `{report['rows']}`",
        f"- Families: `{', '.join(report['families'])}`",
        "",
        "## Closed-Form Term",
        "",
        "```text",
        report["closedFormTerm"],
        "```",
        "",
        "## Cubic Tail Series",
        "",
        "```text",
        report["tailMajorantSeries"],
        "```",
        "",
        "## Anchor Re-Series Term",
        "",
        "```text",
        report["anchorReSeriesTerm"],
        "```",
        "",
        "## Anchor Leading Tail Model",
        "",
        "```text",
        report["anchorReSeriesLeadingQuadraticModel"],
        report["anchorReSeriesLeadingQuadraticErrorMajorant"],
        report["anchorReSeriesQ2Series"],
        report["anchorReSeriesQ3Series"],
        report["anchorReSeriesQ2TailClosedForm"],
        report["anchorReSeriesQ3TailClosedForm"],
        "```",
        "",
        "## Required Generated Fields",
        "",
    ]
    for field in report["requiredGeneratedFields"]:
        lines.append(f"- `{field}`")
    lines.extend(["", "## Candidate Status Counts", ""])
    for status, count in sorted(report["candidateStatusCounts"].items()):
        lines.append(f"- `{status}`: `{count}`")
    first = report.get("firstRowProofDataRequest")
    if first:
        params = first["rowParameters"]
        interval = params["interval"] or {}
        lines.extend(
            [
                "",
                "## First Row Proof-Data Request",
                "",
                f"- Status: `{first['status']}`",
                f"- Row: `{first['label']}`",
                f"- Target Lean file: `{first['targetLeanFile']}`",
                f"- Proof pack: `{first['proofPack']}`",
                f"- Context bundle script: `{first['contextBundleScript']}`",
                f"- Aristotle submit requires explicit user OK: `{first['requiresExplicitUserOKForAristotleSubmit']}`",
                f"- Omega target theorem: `{first['omegaTargetTheorem']}`",
                f"- ShapeSq target theorem: `{first['shapeSqTargetTheorem']}`",
                f"- Checked combiner: `{first['checkedCombiner']}`",
                f"- Interval: `[{interval.get('a')}, {interval.get('b')}]`, anchor `{interval.get('anchor')}`",
                f"- Parameters: `k={params.get('k')}`, `ell={params.get('ell')}`, `distance={params.get('distance')}`",
                "",
                "### First Row Omega Endpoint Targets",
                "",
                "| endpoint | field | status | candidate decimal |",
                "| --- | --- | --- | ---: |",
            ]
        )
        for target in first["omegaEndpointTargets"]:
            lines.append(
                "| {endpoint} | `{field}` | `{status}` | `{decimal}` |".format(
                    endpoint=target["endpoint"],
                    field=target["field"],
                    status=target["status"],
                    decimal=target["candidateDecimal"],
                )
            )
        lines.extend(
            [
                "",
                "### First Row Proof-Data Groups",
                "",
                "| group | status | receiver | fields |",
                "| --- | --- | --- | ---: |",
            ]
        )
        for group in first["proofDataGroups"]:
            lines.append(
                "| {name} | `{status}` | `{receiver}` | {count} |".format(
                    name=group["name"],
                    status=group["status"],
                    receiver=group["receiver"],
                    count=len(group["fields"]),
                )
            )
    lines.extend(
        [
            "",
            "## Sample Rows",
            "",
            "| row | interval | available endpoint candidates |",
            "| --- | --- | ---: |",
        ]
    )
    for row in report["contracts"][:8]:
        interval = row["interval"]
        available = sum(1 for value in row["availableFromEndpointWorklist"].values() if value)
        lines.append(
            "| {label} | [{a}, {b}] anchor={anchor} | {available}/4 |".format(
                label=row["label"],
                a=interval["a"],
                b=interval["b"],
                anchor=interval["anchor"],
                available=available,
            )
        )
    lines.extend(["", "## Route Guard", ""])
    for item in report["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    worklist = load_json(args.worklist)
    validate_worklist(worklist, args.worklist)
    report = build_report(worklist)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    args.out_md.write_text(render_md(report), encoding="utf-8")
    print(
        "omega_closed_form_endpoint_contract: "
        f"status={report['status']} rows={report['rows']} out={args.out_json}"
    )


if __name__ == "__main__":
    main()
