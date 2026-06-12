#!/usr/bin/env python3
"""Feasibility audit for the first Step33A.1-A Omega direct-anchor row.

This is a fail-closed control-plane artifact.  It does not emit Lean proofs and
does not change endpoint constants.  Its purpose is to keep the accepted Route A
worklist honest after the v21 containment-budget direct-anchor refresh:

* the derivative-side wrapper is already relaxed to a local [0,2] slope budget;
* the active missing proof target is the direct anchor bound for
  step22OmegaArchWeight (1/20);
* the old q2/q3 finite-prefix route should not be mistaken for the live target.

The derivative endpoint interval can be locally relaxed without touching A
tables or radii because the endpoint containment uses an absolute derivative
slope times a tiny eta radius.  The anchor interval is different: it must stay
inside the imported Omega radius budget, so even after the v21 proof-pad refresh
the simple real-series q2/q3 tail route remains impractical.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any


getcontext().prec = 100

ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_component_endpoint_worklist.json"
)
DEFAULT_OUT_JSON = REQUEST_DIR / "a_omega_first_row_feasibility_audit.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_omega_first_row_feasibility_audit.md"

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.v21"
)
SCHEMA = "q3_psdpd_step33_a_omega_first_row_feasibility_audit.v11"

RELAXED_DERIV_LOWER = Decimal(1)
RELAXED_DERIV_UPPER = Decimal(2)
DERIV_TEST_N = 4
ANCHOR_ABS_TAIL_ASYMPTOTIC_COEFF = Decimal(3) / Decimal(4)
Q2_TAIL_WIDTH_COEFF = Decimal(3) / Decimal(4)
SIGNED_TAIL_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "Step22OmegaClosedFormEndpointBoundsCert."
    "of_re_series_anchor_interval_tail_trigamma_im_closed_form_term_prefix_cubic_tail_Icc"
)
SIGNED_TAIL_ANCHOR_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeight_bounds_from_re_series_prefix_tail_interval"
)
ACCELERATED_TAIL_ANCHOR_LEMMA = (
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
LEADING_QUADRATIC_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_model_error"
)
POSITIVE_SERIES_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_positive_series_bounds"
)
PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_prefix_tail_closed_form"
)
DIRECT_ANCHOR_WRAPPER = (
    "primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_of_direct_anchor_generated"
)
LEADING_QUADRATIC_ERROR_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "abs_step22OmegaArchWeightReSeriesTerm_sub_leading_quadratic_model_le_cubic"
)
Q2_TAIL_CLOSED_FORM_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_one_div_nat_add_quarter_sq_le_inv_pred"
)
Q3_TAIL_CLOSED_FORM_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_const_mul_one_div_nat_add_quarter_cubic_le"
)
Q2_SHIFTED_TAIL_CLOSED_FORM_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_anchor_q2_shifted_tail_le_closed_form"
)
Q3_SHIFTED_TAIL_CLOSED_FORM_LEMMA = (
    "RawOmegaATaylorModelCertificate."
    "tsum_anchor_q3_shifted_tail_le_closed_form"
)
LEADING_QUADRATIC_MODEL = (
    "model n = -(3/4) / ((((n + anchorN : Nat) : Real) + 1/4)^2)"
)
LEADING_QUADRATIC_ERROR_MAJORANT = (
    "g n = ((3/4)^2 + (etaUpper/2)^2) / "
    "((((n + anchorN : Nat) : Real) + 1/4)^3)"
)
Q2_SERIES = "q2 n = 1 / ((((n + anchorN : Nat) : Real) + 1/4)^2)"
Q3_SERIES = LEADING_QUADRATIC_ERROR_MAJORANT


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


def dec(value: Any) -> Decimal:
    return Decimal(str(value))


def rat_dec(value: str) -> Decimal:
    text = str(value)
    if "/" not in text:
        return Decimal(text)
    num, den = text.split("/", 1)
    return Decimal(num) / Decimal(den)


def endpoint_map(row: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(item["endpoint"]): item for item in row.get("endpointFacts") or []}


def interval_auto_abs_bound(lower: Decimal, upper: Decimal) -> Decimal:
    return max(abs(lower), abs(upper))


def interval_auto_center_error(
    lower: Decimal, upper: Decimal, center: Decimal
) -> Decimal:
    return max(abs(lower - center), abs(upper - center))


def ceil_decimal(value: Decimal) -> int:
    rounded = int(value)
    if Decimal(rounded) < value:
        return rounded + 1
    return rounded


def trigamma_closed_form(eta: Decimal, n: int) -> Decimal:
    x = Decimal(n) + Decimal(1) / Decimal(4)
    y = eta / Decimal(2)
    return -((Decimal(2) * x * y) / (((x * x) + (y * y)) ** 2))


def cubic_tail_bound(eta_upper: Decimal, n: int) -> Decimal:
    """Simple monotone-series upper bound for the cubic majorant tail.

    sum_{m >= 0} etaUpper / (m + n + 1/4)^3
      <= first term + integral from 0 to infinity.
    """
    x0 = Decimal(n) + Decimal(1) / Decimal(4)
    return eta_upper / (x0**3) + eta_upper / (Decimal(2) * (x0**2))


def build_report(worklist: dict[str, Any]) -> dict[str, Any]:
    rows = [row for row in worklist.get("rows") or [] if isinstance(row, dict)]
    if not rows:
        raise ValueError("worklist has no rows")
    row = rows[0]
    facts = endpoint_map(row)
    interval = row["interval"]
    params = row["parameters"]
    endpoint_intervals = row["endpointIntervals"]
    auto_definitions = row.get("autoDefinitions") or {}
    omega_anchor_proof_interval = endpoint_intervals.get("omegaAnchorProof") or {}

    a = rat_dec(interval["a"])
    b = rat_dec(interval["b"])
    eta_radius = rat_dec(interval["etaRadius"])
    eta_upper = b
    omega_radius = rat_dec(params["omegaRadius"])
    omega_center = rat_dec(params["omegaCenter"])

    current_deriv_lower = rat_dec(facts["omegaDerivLower"]["candidateRational"])
    current_deriv_upper = rat_dec(facts["omegaDerivUpper"]["candidateRational"])
    current_anchor_lower = rat_dec(facts["omegaAnchorLower"]["candidateRational"])
    current_anchor_upper = rat_dec(facts["omegaAnchorUpper"]["candidateRational"])

    current_abs_slope = interval_auto_abs_bound(
        current_deriv_lower, current_deriv_upper
    )
    current_anchor_error = interval_auto_center_error(
        current_anchor_lower, current_anchor_upper, omega_center
    )
    current_consumed = current_abs_slope * eta_radius + current_anchor_error

    relaxed_abs_slope = interval_auto_abs_bound(
        RELAXED_DERIV_LOWER, RELAXED_DERIV_UPPER
    )
    relaxed_consumed = relaxed_abs_slope * eta_radius + current_anchor_error

    allowed_anchor_error_relaxed = omega_radius - relaxed_abs_slope * eta_radius
    relaxed_margin = omega_radius - relaxed_consumed

    term_lower = [
        trigamma_closed_form(b, n)
        for n in range(DERIV_TEST_N)
    ]
    term_upper = [
        trigamma_closed_form(a, n)
        for n in range(DERIV_TEST_N)
    ]
    prefix_lower = sum(term_lower, Decimal(0))
    prefix_upper = sum(term_upper, Decimal(0))
    tail = cubic_tail_bound(eta_upper, DERIV_TEST_N)
    produced_deriv_lower = -((prefix_upper + tail) * (Decimal(1) / Decimal(2)))
    produced_deriv_upper = -((prefix_lower - tail) * (Decimal(1) / Decimal(2)))

    derivative_current_tight_passes = (
        current_deriv_lower <= produced_deriv_lower
        and produced_deriv_upper <= current_deriv_upper
    )
    derivative_relaxed_passes = (
        RELAXED_DERIV_LOWER <= produced_deriv_lower
        and produced_deriv_upper <= RELAXED_DERIV_UPPER
    )

    target_deriv_width = current_deriv_upper - current_deriv_lower
    if target_deriv_width > 0:
        rough_min_deriv_n = (
            (eta_upper / (Decimal(2) * target_deriv_width)).sqrt()
        )
    else:
        rough_min_deriv_n = None

    if allowed_anchor_error_relaxed > 0:
        rough_min_anchor_n = (
            ANCHOR_ABS_TAIL_ASYMPTOTIC_COEFF / allowed_anchor_error_relaxed
        )
    else:
        rough_min_anchor_n = None

    anchor_interval_width = current_anchor_upper - current_anchor_lower
    q3_tail_coeff = (Decimal(3) / Decimal(4)) ** 2 + (eta_upper / Decimal(2)) ** 2
    if anchor_interval_width > 0:
        min_q2_index_decimal = (
            Q2_TAIL_WIDTH_COEFF / anchor_interval_width
            + Decimal(3) / Decimal(4)
        )
        min_q2_index = ceil_decimal(min_q2_index_decimal)
        min_q3_index_decimal = (
            (Decimal(2) * q3_tail_coeff / anchor_interval_width).sqrt()
            + Decimal(3) / Decimal(4)
        )
        min_q3_index = ceil_decimal(min_q3_index_decimal)
    else:
        min_q2_index_decimal = None
        min_q2_index = None
        min_q3_index_decimal = None
        min_q3_index = None

    return {
        "schema": SCHEMA,
        "status": "route_feasibility_audit_not_lean_proof",
        "row": {
            "family": row.get("family"),
            "row": row.get("row"),
            "parentChunk": row.get("parentChunk"),
            "split": row.get("split"),
            "subchunk": row.get("subchunk"),
            "interval": interval,
            "endpointIntervals": {
                "omegaDerivative": endpoint_intervals.get("omegaDerivative"),
                "omegaAnchorProof": endpoint_intervals.get("omegaAnchorProof"),
            },
        },
        "currentEndpointContainment": {
            "omegaRadius": str(omega_radius),
            "omegaCenter": str(omega_center),
            "derivativeAbsSlope": str(current_abs_slope),
            "anchorCenterError": str(current_anchor_error),
            "consumed": str(current_consumed),
            "margin": str(omega_radius - current_consumed),
            "passes": current_consumed <= omega_radius,
        },
        "relaxedDerivativeCandidate": {
            "derivLower": str(RELAXED_DERIV_LOWER),
            "derivUpper": str(RELAXED_DERIV_UPPER),
            "derivativeAbsSlope": str(relaxed_abs_slope),
            "consumedWithCurrentAnchorProof": str(relaxed_consumed),
            "marginWithCurrentAnchorProof": str(relaxed_margin),
            "allowedAnchorCenterError": str(allowed_anchor_error_relaxed),
            "passesContainmentWithCurrentAnchorProof": relaxed_consumed <= omega_radius,
            "meaning": (
                "Derivative endpoints may be widened locally; the containment "
                "uses max(abs deriv endpoints) times etaRadius, not derivative "
                "interval width."
            ),
        },
        "directAnchorProofTarget": {
            "status": "direct_anchor_wrapper_checked_anchor_inequalities_open",
            "wrapper": DIRECT_ANCHOR_WRAPPER,
            "proofPad": auto_definitions.get("omegaAnchorProofPad"),
            "proofPadDecimal": auto_definitions.get("omegaAnchorProofPadDecimal"),
            "proofInterval": omega_anchor_proof_interval,
            "proofWidth": omega_anchor_proof_interval.get("widthDecimal"),
            "lowerStatement": "omegaAnchorLower <= step22OmegaArchWeight anchor",
            "upperStatement": "step22OmegaArchWeight anchor <= omegaAnchorUpper",
            "meaning": (
                "The active v21 endpoint receiver asks for the two direct "
                "anchor inequalities around step22OmegaArchWeight (1/20).  "
                "This is below the checked Route A subchunk wrapper; it is "
                "not a request to regenerate A data or replay a full row."
            ),
        },
        "derivativePrefixTailCandidate": {
            "derivN": DERIV_TEST_N,
            "etaUpper": str(eta_upper),
            "termLowerAtB": [str(x) for x in term_lower],
            "termUpperAtA": [str(x) for x in term_upper],
            "prefixLower": str(prefix_lower),
            "prefixUpper": str(prefix_upper),
            "cubicTailBound": str(tail),
            "producedDerivLower": str(produced_deriv_lower),
            "producedDerivUpper": str(produced_deriv_upper),
            "passesCurrentTightDerivativeTargets": derivative_current_tight_passes,
            "passesRelaxedDerivativeTargets": derivative_relaxed_passes,
            "roughMinNForCurrentTightWidthFromCubicTail": (
                None if rough_min_deriv_n is None else str(rough_min_deriv_n)
            ),
        },
        "anchorReSeriesAbsTailFeasibility": {
            "status": "plain_abs_tail_impractical_for_current_direct_anchor_budget",
            "allowedAnchorCenterErrorAfterRelaxedDerivative": str(
                allowed_anchor_error_relaxed
            ),
            "asymptoticTailModel": "abs tail roughly >= 3/(4*N) before acceleration",
            "roughMinAnchorNForAllowedError": (
                None if rough_min_anchor_n is None else str(rough_min_anchor_n)
            ),
            "implication": (
                "The direct real-series prefix/absolute-tail receiver is not a "
                "good first proof route for the v21 direct anchor endpoint.  "
                "Use a sharper high-order/asymptotic bridge or a certified "
                "constant backend before trying to materialize anchorN rows."
            ),
        },
        "anchorReSeriesSignedTailRoute": {
            "status": "checked_combined_prefix_tail_receiver_available_but_simple_prefix_tail_width_impractical",
            "receiver": SIGNED_TAIL_RECEIVER,
            "anchorLemma": SIGNED_TAIL_ANCHOR_LEMMA,
            "acceleratedTailLemma": ACCELERATED_TAIL_ANCHOR_LEMMA,
            "genericAcceleratedTailLemma": GENERIC_ACCELERATED_TAIL_LEMMA,
            "genericNonnegativePrefixTailLemma": GENERIC_NONNEG_PREFIX_TAIL_LEMMA,
            "leadingQuadraticTailLemma": LEADING_QUADRATIC_TAIL_LEMMA,
            "positiveSeriesTailLemma": POSITIVE_SERIES_TAIL_LEMMA,
            "prefixTailClosedFormTailLemma": PREFIX_TAIL_CLOSED_FORM_TAIL_LEMMA,
            "leadingQuadraticErrorLemma": LEADING_QUADRATIC_ERROR_LEMMA,
            "q2TailClosedFormLemma": Q2_TAIL_CLOSED_FORM_LEMMA,
            "q3TailClosedFormLemma": Q3_TAIL_CLOSED_FORM_LEMMA,
            "q2ShiftedTailClosedFormLemma": Q2_SHIFTED_TAIL_CLOSED_FORM_LEMMA,
            "q3ShiftedTailClosedFormLemma": Q3_SHIFTED_TAIL_CLOSED_FORM_LEMMA,
            "leadingQuadraticModel": LEADING_QUADRATIC_MODEL,
            "leadingQuadraticErrorMajorant": LEADING_QUADRATIC_ERROR_MAJORANT,
            "q2Series": Q2_SERIES,
            "q3Series": Q3_SERIES,
            "q2TailClosedForm": (
                "1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1)"
            ),
            "q3TailClosedForm": (
                "((3/4)^2 + (etaUpper/2)^2) * "
                "(1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2))"
            ),
            "requiredTailFacts": [
                "anchorTailLower <= tail",
                "tail <= anchorTailUpper",
                "omegaAnchorLower <= constLower + prefixLower + anchorTailLower",
                "constUpper + prefixUpper + anchorTailUpper <= omegaAnchorUpper",
            ],
            "acceleratedModelTailFacts": [
                "anchorQ2Lower <= tsum (fun n => 1/(n+anchorN+1/4)^2)",
                "tsum (fun n => 1/(n+anchorN+1/4)^2) <= anchorQ2Upper",
                "tsum (fun n => ((3/4)^2 + (etaUpper/2)^2)/(n+anchorN+1/4)^3) <= anchorQ3Upper",
                "anchorTailLower <= -(3/4) * anchorQ2Upper - anchorQ3Upper",
                "-(3/4) * anchorQ2Lower + anchorQ3Upper <= anchorTailUpper",
            ],
            "positivePSeriesPrefixTailFacts": [
                "anchorQ2PrefixLower <= sum range anchorQ2PrefixN q2",
                "tsum (fun n => q2 (n + anchorQ2PrefixN)) <= 1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1)",
                "1 / ((anchorN + anchorQ2PrefixN + 1/4) - 1) <= anchorQ2TailUpper",
                "sum range anchorQ2PrefixN q2 + anchorQ2TailUpper <= anchorQ2Upper",
                "tsum (fun n => q3 (n + anchorQ3PrefixN)) <= ((3/4)^2 + (etaUpper/2)^2) * (1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2))",
                "((3/4)^2 + (etaUpper/2)^2) * (1 / ((anchorN + anchorQ3PrefixN + 1/4 - 1)^2)) <= anchorQ3TailUpper",
                "sum range anchorQ3PrefixN q3 + anchorQ3TailUpper <= anchorQ3Upper",
            ],
            "meaning": (
                "The Lean receiver no longer requires |tail| <= radius.  The "
                "remaining proof-producing task is now localized to finite "
                "prefix sums and rational comparisons against checked "
                "closed-form shifted-tail bounds for the positive q2/q3 "
                "p-series; the combined Lean receiver now splits the "
                "nonnegative tsums and performs the negative-model sign flip.  "
                "However, using this receiver with only the current integral "
                "closed tails still leaves a first-order q2 tail-width "
                "constraint, so it is not a practical row-generation route for "
                "the v21 direct anchor interval."
            ),
        },
        "anchorSignedTailPrefixFeasibility": {
            "status": "current_simple_q2_q3_prefix_tail_receiver_impractical_for_v21_direct_anchor_interval",
            "anchorIntervalWidth": str(anchor_interval_width),
            "q2TailWidthModel": "width contains roughly (3/4) / (anchorN + anchorQ2PrefixN - 3/4)",
            "q3TailWidthModel": (
                "width contains roughly 2*((3/4)^2 + (etaUpper/2)^2) "
                "/ (anchorN + anchorQ3PrefixN - 3/4)^2"
            ),
            "q3TailCoefficient": str(q3_tail_coeff),
            "minCombinedQ2TailIndexForAnchorWidth": (
                None if min_q2_index is None else str(min_q2_index)
            ),
            "roughMinCombinedQ2TailIndexDecimal": (
                None if min_q2_index_decimal is None else str(min_q2_index_decimal)
            ),
            "minCombinedQ3TailIndexForAnchorWidth": (
                None if min_q3_index is None else str(min_q3_index)
            ),
            "roughMinCombinedQ3TailIndexDecimal": (
                None if min_q3_index_decimal is None else str(min_q3_index_decimal)
            ),
            "verdict": (
                "Do not treat the remaining anchor task as finite-prefix row "
                "crawl.  Under the current simple closed-tail receiver, the "
                "q2 tail alone asks for an astronomically large combined "
                "anchorN+prefixN index.  The next proof route should introduce "
                "a sharper analytic/asymptotic tail bridge, a certified "
                "special-function constant backend, or an equivalent route "
                "chosen by Pro/Louise."
            ),
        },
        "recommendation": [
            "Do not try to prove the current tight derivative endpoint interval with cubic absolute tail.",
            "Keep the derivative-side wrapper that closes the first endpoint with relaxed derivative interval [0,2].",
            "Use the v21 direct-anchor wrapper and prove only the two anchor inequalities for step22OmegaArchWeight (1/20).",
            "Do not route the anchor side back to the old q2/q3 finite-prefix crawl under the current closed-tail receiver.",
            "Ask Pro/Louise only for the canonical direct-anchor theorem shape: certified special-function constant backend, high-order/asymptotic digamma bridge, or another semantic rewrite.",
            "Do not widen A radius/CSV/radius-floor/LDL.",
            "Do not use the plain absolute-tail anchor receiver as the active tight-row target.",
        ],
        "notProof": True,
    }


def render_md(report: dict[str, Any]) -> str:
    row = report["row"]
    current = report["currentEndpointContainment"]
    relaxed = report["relaxedDerivativeCandidate"]
    direct = report["directAnchorProofTarget"]
    deriv = report["derivativePrefixTailCandidate"]
    anchor = report["anchorReSeriesAbsTailFeasibility"]
    signed = report["anchorReSeriesSignedTailRoute"]
    signed_feas = report["anchorSignedTailPrefixFeasibility"]
    lines = [
        "# Step33A.1-A Omega First-Row Feasibility Audit",
        "",
        f"- Schema: `{report['schema']}`",
        f"- Status: `{report['status']}`",
        f"- Row: `{row['family']} row={row['row']} parent={row['parentChunk']} split={row['split']} sub={row['subchunk']}`",
        f"- Interval: `[{row['interval']['a']}, {row['interval']['b']}]`, anchor `{row['interval']['anchor']}`",
        "- Lean proof emitted: `False`",
        "",
        "## Current Containment",
        "",
        f"- omega radius: `{current['omegaRadius']}`",
        f"- derivative abs slope: `{current['derivativeAbsSlope']}`",
        f"- anchor center error: `{current['anchorCenterError']}`",
        f"- consumed: `{current['consumed']}`",
        f"- margin: `{current['margin']}`",
        f"- passes: `{current['passes']}`",
        "",
        "## Relaxed Derivative Candidate",
        "",
        f"- derivative interval: `[{relaxed['derivLower']}, {relaxed['derivUpper']}]`",
        f"- consumed with current anchor proof: `{relaxed['consumedWithCurrentAnchorProof']}`",
        f"- margin with current anchor proof: `{relaxed['marginWithCurrentAnchorProof']}`",
        f"- allowed anchor center error: `{relaxed['allowedAnchorCenterError']}`",
        f"- passes containment: `{relaxed['passesContainmentWithCurrentAnchorProof']}`",
        "",
        "## Direct Anchor Proof Target",
        "",
        f"- status: `{direct['status']}`",
        f"- wrapper: `{direct['wrapper']}`",
        f"- proof pad: `{direct['proofPad']}`",
        f"- proof pad decimal: `{direct['proofPadDecimal']}`",
        f"- proof interval width: `{direct['proofWidth']}`",
        f"- lower statement: `{direct['lowerStatement']}`",
        f"- upper statement: `{direct['upperStatement']}`",
        f"- meaning: {direct['meaning']}",
        "",
        "## Derivative Prefix/Tail Candidate",
        "",
        f"- derivN: `{deriv['derivN']}`",
        f"- cubic tail bound: `{deriv['cubicTailBound']}`",
        f"- produced derivative interval: `[{deriv['producedDerivLower']}, {deriv['producedDerivUpper']}]`",
        f"- passes current tight derivative targets: `{deriv['passesCurrentTightDerivativeTargets']}`",
        f"- passes relaxed derivative targets: `{deriv['passesRelaxedDerivativeTargets']}`",
        f"- rough min N for current tight width via cubic tail: `{deriv['roughMinNForCurrentTightWidthFromCubicTail']}`",
        "",
        "## Anchor Real-Series Abs-Tail Feasibility",
        "",
        f"- status: `{anchor['status']}`",
        f"- allowed anchor center error after relaxed derivative: `{anchor['allowedAnchorCenterErrorAfterRelaxedDerivative']}`",
        f"- rough min anchorN for plain abs tail: `{anchor['roughMinAnchorNForAllowedError']}`",
        f"- implication: {anchor['implication']}",
        "",
        "## Anchor Signed-Tail Route",
        "",
        f"- status: `{signed['status']}`",
        f"- receiver: `{signed['receiver']}`",
        f"- anchor lemma: `{signed['anchorLemma']}`",
        f"- accelerated-tail lemma: `{signed['acceleratedTailLemma']}`",
        f"- generic accelerated-tail lemma: `{signed['genericAcceleratedTailLemma']}`",
        f"- generic nonnegative prefix/tail lemma: `{signed['genericNonnegativePrefixTailLemma']}`",
        f"- leading quadratic tail lemma: `{signed['leadingQuadraticTailLemma']}`",
        f"- positive p-series tail lemma: `{signed['positiveSeriesTailLemma']}`",
        f"- prefix/tail closed-form tail lemma: `{signed['prefixTailClosedFormTailLemma']}`",
        f"- leading quadratic error lemma: `{signed['leadingQuadraticErrorLemma']}`",
        f"- q2 closed tail lemma: `{signed['q2TailClosedFormLemma']}`",
        f"- q3 closed tail lemma: `{signed['q3TailClosedFormLemma']}`",
        f"- q2 shifted closed tail lemma: `{signed['q2ShiftedTailClosedFormLemma']}`",
        f"- q3 shifted closed tail lemma: `{signed['q3ShiftedTailClosedFormLemma']}`",
        f"- meaning: {signed['meaning']}",
        "",
        "```text",
        signed["leadingQuadraticModel"],
        signed["leadingQuadraticErrorMajorant"],
        signed["q2Series"],
        signed["q3Series"],
        signed["q2TailClosedForm"],
        signed["q3TailClosedForm"],
        "```",
        "",
        "### Accelerated Model Tail Facts",
        "",
    ]
    for item in signed["acceleratedModelTailFacts"]:
        lines.append(f"- `{item}`")
    lines.extend([
        "",
        "### Positive P-Series Prefix/Tail Facts",
        "",
    ])
    for item in signed["positivePSeriesPrefixTailFacts"]:
        lines.append(f"- `{item}`")
    lines.extend([
        "",
        "## Anchor Signed-Tail Prefix Feasibility",
        "",
        f"- status: `{signed_feas['status']}`",
        f"- anchor interval width: `{signed_feas['anchorIntervalWidth']}`",
        f"- q2 tail width model: `{signed_feas['q2TailWidthModel']}`",
        f"- min combined q2 tail index for anchor width: `{signed_feas['minCombinedQ2TailIndexForAnchorWidth']}`",
        f"- rough q2 index decimal: `{signed_feas['roughMinCombinedQ2TailIndexDecimal']}`",
        f"- q3 tail width model: `{signed_feas['q3TailWidthModel']}`",
        f"- q3 tail coefficient: `{signed_feas['q3TailCoefficient']}`",
        f"- min combined q3 tail index for anchor width: `{signed_feas['minCombinedQ3TailIndexForAnchorWidth']}`",
        f"- rough q3 index decimal: `{signed_feas['roughMinCombinedQ3TailIndexDecimal']}`",
        f"- verdict: {signed_feas['verdict']}",
        "",
        "## Recommendation",
        "",
    ])
    for item in report["recommendation"]:
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
        "omega_first_row_feasibility_audit: "
        f"status={report['status']} out={args.out_json}"
    )


if __name__ == "__main__":
    main()
