#!/usr/bin/env python3
"""Build the Step33A.1-A signed chunked comparison-integral contract.

This is a route-shaping artifact, not a proof producer.  It pins the exact
Lean receiver and chunk grid for the next A-window generator without mutating
ARadius, CSV payloads, radius floors, or generated global radii.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WINDOW_CONTRACT = REQUEST_DIR / "a_window_contract.json"
DEFAULT_ROUTE_DIAGNOSTIC = REQUEST_DIR / "a_tail_route_diagnostic.json"

RECEIVER = "activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload"
UNDERLYING_RECEIVER = "activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload"
PAYLOAD_STRUCTURE = "Step33ASignedChunkedComparisonIntegralPayload"
PAYLOAD_WRAPPER = (
    "psd_step33_closed_from_rationalDeltaLiveGeneratedP0A"
    "SignedChunkedComparisonIntegralPayload"
)
CHUNKED_WINDOW_PAYLOAD_STRUCTURE = "Step33AChunkedWindowPayload"
CHUNKED_WINDOW_FOLD_WRAPPER = "step33AFoldedWindowPayload_of_chunkedWindowPayload"
CHUNKED_WINDOW_STEP33A_WRAPPER = "activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload"
CHUNKED_WINDOW_STEP33B_WRAPPER = (
    "psd_step33_finite_analytic_weil_positivity_of_chunkedWindowPayload"
)
CHUNKED_WINDOW_STEP33C_WRAPPER = (
    "psd_step33_singleton_directed_family_handoff_of_chunkedWindowPayload"
)
CHUNKED_POINTWISE_PAYLOAD_STRUCTURE = "Step33AChunkedPointwiseWindowPayload"
CHUNKED_POINTWISE_TO_WINDOW_WRAPPER = (
    "step33AChunkedWindowPayload_of_chunkedPointwiseWindowPayload"
)
CHUNKED_POINTWISE_STEP33A_WRAPPER = (
    "activeCenteredCoeffEntryHboxCert_of_chunkedPointwiseWindowPayload"
)
CHUNKED_POINTWISE_STEP33B_WRAPPER = (
    "psd_step33_finite_analytic_weil_positivity_of_chunkedPointwiseWindowPayload"
)
CHUNKED_POINTWISE_STEP33C_WRAPPER = (
    "psd_step33_singleton_directed_family_handoff_of_chunkedPointwiseWindowPayload"
)
CHUNKED_COMPARISON_PAYLOAD_STRUCTURE = "Step33AChunkedComparisonIntegralPayload"
CHUNKED_COMPARISON_FAMILY_PAYLOAD_STRUCTURE = (
    "Step33AChunkedComparisonIntegralFamilyPayload"
)
CHUNKED_COMPARISON_DISTANCE_PAYLOAD_STRUCTURE = (
    "Step33AChunkedComparisonIntegralDistancePayload"
)
CHUNKED_COMPARISON_FAMILY_ASSEMBLER = (
    "step33AChunkedComparisonIntegralPayload_of_familyPayloads"
)
CHUNKED_COMPARISON_DISTANCE_ASSEMBLER = (
    "step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads"
)
CHUNKED_COMPARISON_TO_WINDOW_WRAPPER = (
    "step33AChunkedWindowPayload_of_chunkedComparisonIntegralPayload"
)
CHUNKED_COMPARISON_STEP33A_WRAPPER = (
    "activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralPayload"
)
CHUNKED_COMPARISON_STEP33B_WRAPPER = (
    "psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralPayload"
)
CHUNKED_COMPARISON_STEP33C_WRAPPER = (
    "psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralPayload"
)
CHUNKED_COMPARISON_FAMILY_STEP33A_WRAPPER = (
    "activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralFamilyPayloads"
)
CHUNKED_COMPARISON_FAMILY_STEP33B_WRAPPER = (
    "psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralFamilyPayloads"
)
CHUNKED_COMPARISON_FAMILY_STEP33C_WRAPPER = (
    "psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralFamilyPayloads"
)
CHUNKED_COMPARISON_DISTANCE_STEP33A_WRAPPER = (
    "activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralDistancePayloads"
)
CHUNKED_COMPARISON_DISTANCE_STEP33B_WRAPPER = (
    "psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralDistancePayloads"
)
CHUNKED_COMPARISON_DISTANCE_STEP33C_WRAPPER = (
    "psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralDistancePayloads"
)
FOLDED_PAYLOAD_STRUCTURE = "Step33AFoldedWindowPayload"
FOLDED_PAYLOAD_WRAPPER = (
    "psd_step33_closed_from_rationalDeltaLiveGeneratedP0A"
    "FoldedWindowPayload"
)
CHUNK_ASSEMBLER_HELPERS = [
    "centeredBSplineArchKernelProfileFinitePart_eq_two_positiveFinitePart",
    "centeredBSplineArchKernelProfilePositiveFinitePart_bounds_of_comparison_integrals",
    "centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_comparison_integrals",
    "centeredBSplineArchKernelProfilePositiveFinitePart_bounds_of_two_piece_comparison_integrals",
    "centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_two_piece_comparison_integrals",
    "centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert",
    "centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_comparison_integrals",
    "centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_pointwise_bounds",
    "centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_glue_adjacent",
    "centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_empty",
    "centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range",
    "centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunked_range_bounds",
    "centeredBSplineArchKernelProfileFinitePart_bounds_of_positive_window_cert",
    "primaryK11AnalyticAFinitePartBoundsCert_of_positiveComparisonIntegrals",
    "primaryK11AnalyticAFinitePartBoundsCert_of_positiveTwoPieceComparisonIntegrals",
    "controlK9AnalyticAFinitePartBoundsCert_of_positiveComparisonIntegrals",
    "controlK9AnalyticAFinitePartBoundsCert_of_positiveTwoPieceComparisonIntegrals",
    "centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_window_cert",
    "primaryK11AnalyticAFinitePartBoundsCert_of_positiveWindowCert",
    "primaryK11AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert",
    "controlK9AnalyticAFinitePartBoundsCert_of_positiveWindowCert",
    "controlK9AnalyticAPositiveTailWindowBoundsCert_of_positiveWindowCert",
    "Step33AFoldedWindowPayload",
    "primaryK11AnalyticAFinitePositiveLower",
    "primaryK11AnalyticAFinitePositiveUpper",
    "primaryK11AnalyticAFinitePositiveLowerBound_generated",
    "primaryK11AnalyticAFinitePositiveUpperBound_generated",
    "controlK9AnalyticAFinitePositiveLower",
    "controlK9AnalyticAFinitePositiveUpper",
    "controlK9AnalyticAFinitePositiveLowerBound_generated",
    "controlK9AnalyticAFinitePositiveUpperBound_generated",
    "step33AFoldedWindowPayload_of_generatedAWindowCerts",
    "Step33AChunkedWindowPayload",
    "Step33AChunkedPointwiseWindowPayload",
    "step33AChunkedWindowPayload_of_chunkedPointwiseWindowPayload",
    "Step33AChunkedComparisonIntegralPayload",
    "Step33AChunkedComparisonIntegralFamilyPayload",
    "Step33AChunkedComparisonIntegralDistancePayload",
    "step33AChunkedComparisonIntegralDistancePayload_of_integrand_chunk_bounds",
    "step33AChunkedComparisonIntegralPayload_of_familyPayloads",
    "step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads",
    "centeredBSplineArchKernelProfilePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "primaryK11AnalyticAFinitePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "primaryK11AnalyticAFinitePartBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "primaryK11AnalyticAPositiveTailWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "primaryK11AnalyticAPositiveTailWindowBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralFamilyPayloads",
    "primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralDistancePayloads",
    "controlK9AnalyticAFinitePositiveWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "controlK9AnalyticAFinitePartBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "controlK9AnalyticAPositiveTailWindowPartBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "controlK9AnalyticAPositiveTailWindowBoundsCert_of_chunkedComparisonIntegralFamilyPayload",
    "controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralFamilyPayloads",
    "controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_chunkedComparisonIntegralDistancePayloads",
    "step33AChunkedWindowPayload_of_chunkedComparisonIntegralPayload",
    "step33AFoldedWindowPayload_of_chunkedWindowPayload",
    "step33AFoldedWindowPayload_of_signedChunkedComparisonIntegralPayload",
    "primaryK11AnalyticAFinitePartBoundsCert_of_foldedWindowPayload",
    "primaryK11AnalyticAPositiveTailWindowBoundsCert_of_foldedWindowPayload",
    "primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_foldedWindowPayload",
    "primaryK11AnalyticAAbsDistanceHboxCert_of_foldedWindowPayload",
    "primaryK11AnalyticA_entry_hbox_of_foldedWindowPayload",
    "controlK9AnalyticAFinitePartBoundsCert_of_foldedWindowPayload",
    "controlK9AnalyticAPositiveTailWindowBoundsCert_of_foldedWindowPayload",
    "controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_foldedWindowPayload",
    "controlK9AnalyticAAbsDistanceHboxCert_of_foldedWindowPayload",
    "controlK9AnalyticA_entry_hbox_of_foldedWindowPayload",
    "primaryK11AnalyticP0_entry_hbox_generated",
    "controlK9AnalyticP0_entry_hbox_generated",
    "activeCenteredCoeffEntryHboxCert_of_foldedWindowPayload",
    "psd_step33_finite_analytic_weil_positivity_of_foldedWindowPayload",
    "psd_step33_singleton_directed_family_handoff_of_foldedWindowPayload",
    "activeCenteredCoeffEntryHboxCert_of_generatedAWindowCerts",
    "psd_step33_finite_analytic_weil_positivity_of_generatedAWindowCerts",
    "psd_step33_singleton_directed_family_handoff_of_generatedAWindowCerts",
    "activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload",
    "psd_step33_finite_analytic_weil_positivity_of_chunkedWindowPayload",
    "psd_step33_singleton_directed_family_handoff_of_chunkedWindowPayload",
    "activeCenteredCoeffEntryHboxCert_of_chunkedPointwiseWindowPayload",
    "psd_step33_finite_analytic_weil_positivity_of_chunkedPointwiseWindowPayload",
    "psd_step33_singleton_directed_family_handoff_of_chunkedPointwiseWindowPayload",
    "activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralPayload",
    "psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralPayload",
    "psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralPayload",
    "activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralFamilyPayloads",
    "psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralFamilyPayloads",
    "psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralFamilyPayloads",
    "activeCenteredCoeffEntryHboxCert_of_chunkedComparisonIntegralDistancePayloads",
    "psd_step33_finite_analytic_weil_positivity_of_chunkedComparisonIntegralDistancePayloads",
    "psd_step33_singleton_directed_family_handoff_of_chunkedComparisonIntegralDistancePayloads",
    "activeCenteredCoeffEntryHboxCert_of_signedChunkedComparisonIntegralPayload",
    "psd_step33_finite_analytic_weil_positivity_of_signedChunkedComparisonIntegralPayload",
    "psd_step33_singleton_directed_family_handoff_of_signedChunkedComparisonIntegralPayload",
    "psd_step33_closed_from_rationalDeltaLiveGeneratedP0AFoldedWindowPayload",
    "centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_comparison_integrals",
    "primaryK11AnalyticAFinitePartBoundsCert_of_twoPieceComparisonIntegrals",
    "controlK9AnalyticAFinitePartBoundsCert_of_twoPieceComparisonIntegrals",
    "centeredBSplineArchKernelProfilePositiveTailWindowPart_bounds_of_two_piece_comparison_integrals",
    "centeredBSplineArchKernelProfilePositiveTailWindowIntervalCert_of_two_piece_comparison_integrals",
    "primaryK11AnalyticAPositiveTailWindowBoundsCert_of_twoPieceComparisonIntegrals",
    "controlK9AnalyticAPositiveTailWindowBoundsCert_of_twoPieceComparisonIntegrals",
]


def dec(text: str) -> Decimal:
    return Decimal(str(text))


def dstr(value: Decimal) -> str:
    if value == 0:
        return "0.000000000000000000E+0"
    return format(value, ".18E")


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def load_window_contract(path: Path) -> dict:
    payload = load_json(path)
    schema = payload.get("schema")
    if schema != "q3_psdpd_step33_a_window_contract.v1":
        raise ValueError(f"{path}: unexpected schema {schema!r}")
    return payload


def load_route_diagnostic(path: Path) -> dict:
    payload = load_json(path)
    schema = payload.get("schema")
    if schema != "q3_psdpd_step33_a_tail_route_diagnostic.v1":
        raise ValueError(f"{path}: unexpected schema {schema!r}")
    return payload


def chunks(start: Decimal, end: Decimal, chunk_size: Decimal) -> list[dict]:
    if chunk_size <= 0:
        raise ValueError(f"chunk_size must be positive, got {chunk_size}")
    count = (end - start) / chunk_size
    if count != count.to_integral_value():
        raise ValueError(
            f"chunk grid does not divide interval: start={start} end={end} "
            f"chunk_size={chunk_size}"
        )
    rows = []
    for idx in range(int(count)):
        left = start + chunk_size * idx
        right = left + chunk_size
        rows.append({"index": idx, "left": dstr(left), "right": dstr(right)})
    return rows


def route_block_map(route: dict) -> dict[str, dict]:
    return {block["block"]: block for block in route["blocks"]}


def sign_by_index(route_block: dict) -> dict[int, str]:
    signs: dict[int, str] = {}
    for key, sign in [
        ("negative_rows", "negative"),
        ("positive_rows", "positive"),
        ("crossing_rows", "crossing"),
    ]:
        for row in route_block.get(key, []):
            signs[int(row["index"])] = sign
    return signs


def build_block(block: dict, route_block: dict) -> dict:
    params = block["parameters"]
    cutoff = dec(params["cutoff_t"])
    tail_end = dec(params["positive_tail_window_end"])
    chunk_size = dec(params["chunk_size"])
    signs = sign_by_index(route_block)

    rows = []
    for row in block["distances"]:
        idx = int(row["index"])
        rows.append(
            {
                "index": idx,
                "distance": row["distance"],
                "signed_positive_window_sign": signs.get(idx, "unknown"),
                "finite_lower": row["finite_lower"],
                "finite_upper": row["finite_upper"],
                "positive_window_lower": row["positive_window_lower"],
                "positive_window_upper": row["positive_window_upper"],
                "proof_remainder_radius": row["proof_remainder_radius"],
                "generated_tail_radius": row["generated_tail_radius"],
            }
        )

    return {
        "block": block["block"],
        "label": block["label"],
        "k": block["k"],
        "lean_targets": block["lean_targets"],
        "distance_count": len(rows),
        "signed_window_counts": {
            "positive": route_block["positive_window_rows"],
            "negative": route_block["negative_window_rows"],
            "crossing": route_block["crossing_window_rows"],
        },
        "finite_window": {
            "receiver_domain": "Set.Icc (-archAFiniteTailCutoff) archAFiniteTailCutoff",
            "source_positive_half_domain": "Set.Ioc 0 archAFiniteTailCutoff",
            "positive_half_chunks": chunks(Decimal(0), cutoff, chunk_size),
            "direct_full_chunks": chunks(-cutoff, cutoff, Decimal(2) * chunk_size),
            "note": (
                "The existing numerical source used the positive half-window. "
                "The checked finite-part positive-half receiver doubles the "
                "Ioc(0,T) comparison integrals by the proved evenness identity. "
                "The active direct-finite route uses 26 full-window chunks of "
                "width 20 on Ioc(-T,T), landing on FiniteLower/FiniteUpper."
            ),
        },
        "positive_tail_window": {
            "receiver_domain": "Set.Ioc archAFiniteTailCutoff archAPositiveTailWindowEnd",
            "chunks": chunks(cutoff, tail_end, chunk_size),
        },
        "distances": rows,
    }


def render_md(contract: dict) -> str:
    lines = [
        "# Step33A.1-A Signed Chunk Payload Contract",
        "",
        "This file is generated contract data, not a Lean proof object.",
        "It names the signed chunked comparison-integral route after the",
        "absolute log-majorant final payload was rejected by the route diagnostic.",
        "",
        "Hard guard: no ARadius, CSV, radius-floor, or global A-radius payload",
        "mutation is part of this route.",
        "",
        "## Receiver",
        "",
        f"- named receiver: `{contract['lean_receiver']}`",
        f"- underlying checked receiver: `{contract['underlying_receiver']}`",
        f"- generated payload record: `{contract['lean_payload_structure']}`",
        f"- payload wrapper: `{contract['lean_payload_wrapper']}`",
        f"- chunked window payload record: `{contract['lean_chunked_window_payload_structure']}`",
        f"- chunked window fold wrapper: `{contract['lean_chunked_window_fold_wrapper']}`",
        f"- chunked window Step33A wrapper: `{contract['lean_chunked_window_step33a_wrapper']}`",
        f"- chunked window Step33B wrapper: `{contract['lean_chunked_window_step33b_wrapper']}`",
        f"- chunked window Step33C wrapper: `{contract['lean_chunked_window_step33c_wrapper']}`",
        f"- chunked pointwise payload record: `{contract['lean_chunked_pointwise_payload_structure']}`",
        f"- chunked pointwise-to-window wrapper: `{contract['lean_chunked_pointwise_to_window_wrapper']}`",
        f"- chunked pointwise Step33A wrapper: `{contract['lean_chunked_pointwise_step33a_wrapper']}`",
        f"- chunked pointwise Step33B wrapper: `{contract['lean_chunked_pointwise_step33b_wrapper']}`",
        f"- chunked pointwise Step33C wrapper: `{contract['lean_chunked_pointwise_step33c_wrapper']}`",
        f"- chunked comparison-integral payload record: `{contract['lean_chunked_comparison_payload_structure']}`",
        f"- chunked comparison-integral family payload record: `{contract['lean_chunked_comparison_family_payload_structure']}`",
        f"- chunked comparison-integral distance payload record: `{contract['lean_chunked_comparison_distance_payload_structure']}`",
        f"- chunked comparison-integral family assembler: `{contract['lean_chunked_comparison_family_assembler']}`",
        f"- chunked comparison-integral distance assembler: `{contract['lean_chunked_comparison_distance_assembler']}`",
        f"- chunked comparison-integral-to-window wrapper: `{contract['lean_chunked_comparison_to_window_wrapper']}`",
        f"- chunked comparison-integral Step33A wrapper: `{contract['lean_chunked_comparison_step33a_wrapper']}`",
        f"- chunked comparison-integral Step33B wrapper: `{contract['lean_chunked_comparison_step33b_wrapper']}`",
        f"- chunked comparison-integral Step33C wrapper: `{contract['lean_chunked_comparison_step33c_wrapper']}`",
        f"- chunked comparison-integral family Step33A wrapper: `{contract['lean_chunked_comparison_family_step33a_wrapper']}`",
        f"- chunked comparison-integral family Step33B wrapper: `{contract['lean_chunked_comparison_family_step33b_wrapper']}`",
        f"- chunked comparison-integral family Step33C wrapper: `{contract['lean_chunked_comparison_family_step33c_wrapper']}`",
        f"- chunked comparison-integral distance Step33A wrapper: `{contract['lean_chunked_comparison_distance_step33a_wrapper']}`",
        f"- chunked comparison-integral distance Step33B wrapper: `{contract['lean_chunked_comparison_distance_step33b_wrapper']}`",
        f"- chunked comparison-integral distance Step33C wrapper: `{contract['lean_chunked_comparison_distance_step33c_wrapper']}`",
        f"- folded payload record: `{contract['lean_folded_payload_structure']}`",
        f"- folded payload wrapper: `{contract['lean_folded_payload_wrapper']}`",
        "",
        "## Checked Chunk Assembler Helpers",
        "",
    ]
    for item in contract["checked_chunk_assembler_helpers"]:
        lines.append(f"- `{item}`")
    lines.extend([
        "",
        "## Required proof-producing payload",
        "",
    ])
    for item in contract["proof_obligations"]:
        lines.append(f"- {item}")
    lines.append("")

    for block in contract["blocks"]:
        lines.extend(
            [
                f"## {block['label']}",
                "",
                f"- distances: `{block['distance_count']}`",
                f"- finite positive-half chunks: `{len(block['finite_window']['positive_half_chunks'])}`",
                f"- finite direct full-window chunks: `{len(block['finite_window']['direct_full_chunks'])}`",
                f"- positive-tail chunks: `{len(block['positive_tail_window']['chunks'])}`",
                (
                    "- signed positive-window rows: "
                    f"`positive={block['signed_window_counts']['positive']}`, "
                    f"`negative={block['signed_window_counts']['negative']}`, "
                    f"`crossing={block['signed_window_counts']['crossing']}`"
                ),
                "",
                "| idx | d | sign | finite lower | finite upper | window lower | window upper |",
                "| ---: | ---: | --- | ---: | ---: | ---: | ---: |",
            ]
        )
        for row in block["distances"]:
            lines.append(
                "| {index} | {distance} | {signed_positive_window_sign} | "
                "{finite_lower} | {finite_upper} | {positive_window_lower} | "
                "{positive_window_upper} |".format(**row)
            )
        lines.append("")

    return "\n".join(lines)


def build_contract(window_contract: dict, route: dict) -> dict:
    route_by_block = route_block_map(route)
    blocks = []
    for block in window_contract["blocks"]:
        name = block["block"]
        if name not in route_by_block:
            raise ValueError(f"route diagnostic missing block {name!r}")
        blocks.append(build_block(block, route_by_block[name]))

    return {
        "schema": "q3_psdpd_step33_a_signed_chunk_payload_contract.v1",
        "meaning": (
            "Exact non-mutating Step33A.1-A route contract for the 26-chunk "
            "A-window payload."
        ),
        "source_window_contract": window_contract.get("schema"),
        "source_route_diagnostic": route.get("schema"),
        "lean_receiver": RECEIVER,
        "underlying_receiver": UNDERLYING_RECEIVER,
        "lean_payload_structure": PAYLOAD_STRUCTURE,
        "lean_payload_wrapper": PAYLOAD_WRAPPER,
        "lean_chunked_window_payload_structure": CHUNKED_WINDOW_PAYLOAD_STRUCTURE,
        "lean_chunked_window_fold_wrapper": CHUNKED_WINDOW_FOLD_WRAPPER,
        "lean_chunked_window_step33a_wrapper": CHUNKED_WINDOW_STEP33A_WRAPPER,
        "lean_chunked_window_step33b_wrapper": CHUNKED_WINDOW_STEP33B_WRAPPER,
        "lean_chunked_window_step33c_wrapper": CHUNKED_WINDOW_STEP33C_WRAPPER,
        "lean_chunked_pointwise_payload_structure": CHUNKED_POINTWISE_PAYLOAD_STRUCTURE,
        "lean_chunked_pointwise_to_window_wrapper": CHUNKED_POINTWISE_TO_WINDOW_WRAPPER,
        "lean_chunked_pointwise_step33a_wrapper": CHUNKED_POINTWISE_STEP33A_WRAPPER,
        "lean_chunked_pointwise_step33b_wrapper": CHUNKED_POINTWISE_STEP33B_WRAPPER,
        "lean_chunked_pointwise_step33c_wrapper": CHUNKED_POINTWISE_STEP33C_WRAPPER,
        "lean_chunked_comparison_payload_structure": CHUNKED_COMPARISON_PAYLOAD_STRUCTURE,
        "lean_chunked_comparison_family_payload_structure": (
            CHUNKED_COMPARISON_FAMILY_PAYLOAD_STRUCTURE
        ),
        "lean_chunked_comparison_distance_payload_structure": (
            CHUNKED_COMPARISON_DISTANCE_PAYLOAD_STRUCTURE
        ),
        "lean_chunked_comparison_family_assembler": CHUNKED_COMPARISON_FAMILY_ASSEMBLER,
        "lean_chunked_comparison_distance_assembler": CHUNKED_COMPARISON_DISTANCE_ASSEMBLER,
        "lean_chunked_comparison_to_window_wrapper": CHUNKED_COMPARISON_TO_WINDOW_WRAPPER,
        "lean_chunked_comparison_step33a_wrapper": CHUNKED_COMPARISON_STEP33A_WRAPPER,
        "lean_chunked_comparison_step33b_wrapper": CHUNKED_COMPARISON_STEP33B_WRAPPER,
        "lean_chunked_comparison_step33c_wrapper": CHUNKED_COMPARISON_STEP33C_WRAPPER,
        "lean_chunked_comparison_family_step33a_wrapper": (
            CHUNKED_COMPARISON_FAMILY_STEP33A_WRAPPER
        ),
        "lean_chunked_comparison_family_step33b_wrapper": (
            CHUNKED_COMPARISON_FAMILY_STEP33B_WRAPPER
        ),
        "lean_chunked_comparison_family_step33c_wrapper": (
            CHUNKED_COMPARISON_FAMILY_STEP33C_WRAPPER
        ),
        "lean_chunked_comparison_distance_step33a_wrapper": (
            CHUNKED_COMPARISON_DISTANCE_STEP33A_WRAPPER
        ),
        "lean_chunked_comparison_distance_step33b_wrapper": (
            CHUNKED_COMPARISON_DISTANCE_STEP33B_WRAPPER
        ),
        "lean_chunked_comparison_distance_step33c_wrapper": (
            CHUNKED_COMPARISON_DISTANCE_STEP33C_WRAPPER
        ),
        "lean_folded_payload_structure": FOLDED_PAYLOAD_STRUCTURE,
        "lean_folded_payload_wrapper": FOLDED_PAYLOAD_WRAPPER,
        "checked_chunk_assembler_helpers": CHUNK_ASSEMBLER_HELPERS,
        "proof_obligations": [
            "active lower-level route: instantiate four collections of Step33AChunkedComparisonIntegralDistancePayloads, one collection per family",
            "each distance payload covers one CoeffIndex23 distance and 26 adjacent chunks",
            "use step33AChunkedComparisonIntegralDistancePayload_of_integrand_chunk_bounds when lowerF/upperF are the analytic A integrand itself",
            "assemble each family with step33AChunkedComparisonIntegralFamilyPayload_of_distancePayloads",
            "each family payload now extracts a checked positive-window or finite-window cert",
            "primary finite+tail family payloads now extract primaryK11AnalyticAFiniteTailAnalyticBoundsCert",
            "control finite+tail family payloads now extract controlK9AnalyticAFiniteTailAnalyticBoundsCert",
            "assemble them with step33AChunkedComparisonIntegralPayload_of_familyPayloads",
            "then instantiate Step33AChunkedComparisonIntegralPayload",
            "prove each chunk lower/upper scalar comparison against the analytic A-integrand integral",
            "define chunk lower/upper values for primary/control finite windows, 26 chunks each",
            "define chunk lower/upper values for primary/control positive-tail windows, 26 chunks each",
            "active direct-finite route: prove primaryFiniteChunks for intervals -archAFiniteTailCutoff + 20*i to -archAFiniteTailCutoff + 20*(i+1)",
            "active direct-finite route: prove controlFiniteChunks for intervals -archAFiniteTailCutoff + 20*i to -archAFiniteTailCutoff + 20*(i+1)",
            "legacy folded route still records positive-half finite chunks for receiver comparison but is not the active worklist after the local slack audit",
            "prove primaryTailChunks for intervals archAFiniteTailCutoff + 10*i to archAFiniteTailCutoff + 10*(i+1)",
            "prove controlTailChunks for intervals archAFiniteTailCutoff + 10*i to archAFiniteTailCutoff + 10*(i+1)",
            "prove finite-window sum lower/upper comparisons against generated FiniteLower/FiniteUpper bounds",
            "prove tail-window sum lower/upper comparisons against generated positive-tail bounds",
            "convert to Step33AChunkedWindowPayload via the checked comparison-integral-to-window wrapper",
            "instantiate Step33AChunkedWindowPayload",
            "feed activeCenteredCoeffEntryHboxCert_of_chunkedWindowPayload to close Step33A",
            "feed the chunkedWindowPayload Step33B/Step33C wrappers for final handoff",
            "pointwise-constant chunks are a checked helper only, not the active route for current tight signed windows",
            "do not mutate ARadius, CSV, radius floors, or global A-radius payloads",
        ],
        "blocks": blocks,
    }


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--window-contract", type=Path, default=DEFAULT_WINDOW_CONTRACT)
    parser.add_argument("--route-diagnostic", type=Path, default=DEFAULT_ROUTE_DIAGNOSTIC)
    parser.add_argument("--out-json", type=Path)
    parser.add_argument("--out-md", type=Path)
    args = parser.parse_args()

    getcontext().prec = 100
    window_contract = load_window_contract(args.window_contract)
    route = load_route_diagnostic(args.route_diagnostic)
    contract = build_contract(window_contract, route)

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(contract, indent=2, sort_keys=True) + "\n")
    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_md(contract), encoding="utf-8")

    for block in contract["blocks"]:
        counts = block["signed_window_counts"]
        print(
            f"{block['label']}: distances={block['distance_count']} "
            f"tail_chunks={len(block['positive_tail_window']['chunks'])} "
            f"negative_signed_rows={counts['negative']}"
        )


if __name__ == "__main__":
    run()
