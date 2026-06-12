#!/usr/bin/env python3
"""Emit proof-safe rational endpoint certs for Step33A.1-A refined rows.

This generator does not prove the analytic Omega/shape endpoint packages.
It only packages the rational endpoint-radius arithmetic already checked by
the active v21 worklist into Lean theorems.

It also emits the row-specific Omega closed-form wrapper shape: future proof
rows supply derivative trigamma prefix facts, derivative closed-tail
comparisons, and anchor facts, while Lean composes them through checked
receivers into a
`Step22OmegaClosedFormEndpointBoundsCert`.

For the first tiny endpoint row it also emits a checked derivative-side
specialization.  That specialization proves the coarse local derivative target
`0 <= omega' <= 2` from the single `n = 0` trigamma term plus the checked
closed-form derivative tail receiver.  Schema v9 also emits a direct-anchor
variant for that first row, leaving only the two direct anchor inequalities
against `step22OmegaArchWeight (1/20)` open.  Schema v10 consumes the widened
containment-budget anchor proof pads from the v21 worklist.  Schema v11 also
emits a small conjunction adapter for the first direct-anchor target, matching
the prepared Aristotle theorem shape.  Schema v12 emits a first-anchor
re-series interval adapter: explicit constant, finite-prefix, and signed-tail
interval premises imply the same direct-anchor conjunction.  Schema v13 also
emits the first-anchor `N = 16` finite-prefix bounds as a checked rational
proof row.  Schema v14 adds first-anchor wrappers that consume that checked
prefix row, leaving only constant bounds, signed tail after `N = 16`, and
rational glue as premises for the re-series route.
Schema v15 adds first-anchor shifted-Stieltjes wrappers, consuming the checked
digamma shift receiver and leaving only shifted main/error rational
comparisons.  Schema v16 adds a first-anchor generic main/error adapter for
future high-order digamma/Bernoulli receivers.  Schema v17 adds a shifted
digamma main/error adapter so asymptotic receivers can target `psi(z+shift)`
and feed the same endpoint landing.  Schema v18 adds the corresponding complex
main/error adapter so asymptotic receivers can supply a complex norm remainder
bound and let Lean project it to the real-part bound.
Schema v19 adds the first-row ShapeSq reduction from anchor `E`, anchor `E'`,
and inner-deriv interval bounds.  Schema v20 adds shifted-digamma rectangular
Re/Im error and interval adapters.  Schema v21 adds shifted-digamma
    series-prefix-tail interval and absolute-tail endpoint adapters.
    Schema v22 adds the N=16 specialization for the signed-tail shifted-digamma
    series endpoint adapter, parallel to the existing N=16 absolute-tail wrapper.
    Schema v23 adds N=16 exact-prefix facades for signed-tail and absolute-tail
    routes, so generators do not emit separate lower/upper proof rows for the
    finite prefix sums.
    Schema v24 adds Euler-Mascheroni sequence facades on top of those exact
    prefix routes, so generators can select a checked `gammaN` bracket instead
    of passing gamma lower/upper premises explicitly.
    Schema v25 adds a complex norm-tail facade on top of the exact-prefix
    gamma-seq absolute-tail route, so one complex tail majorant feeds both Re
    and Im component tails.
    Schema v26 adds a majorant facade on top of the complex-tail route: future
    proof-data can provide a summable `g`, pointwise norm bounds, and a checked
    `∑' g <= tailRadius` comparison instead of a direct complex tail `tsum`
    proof.
    Schema v27 adds a quadratic-majorant facade that fixes
    `g n = C / (((n+16)+1/4)^2)` and consumes the checked p-series package from
    the raw-Omega checker.
    Schema v28 adds a shift+1 closed-tail err-sum facade, discharging the
    rectangular `hErr : errRe + errIm <= err` premise with `err = errRe + errIm`.
Schema v29 adds a centered-rectangle facade, fixing the Re/Im interval
endpoints to `psiMain.re/im ± errRe/errIm` and discharging the four
center-comparison premises.  Schema v30 also emits the concrete shifted
digamma point identities for the live `shift=16, N=16` endpoint:
`step22OmegaArchWeightShiftedDigammaArg (1/20) 16 + 16 = 129/4 + i/40`.
Schema v31 adds a shift16/N16 complex-main-error facade on top of the checked
finite inverse-sum rectangle: one tight complex norm bound for
`Q3.digamma (129/4 + i/40)` now supplies the four shifted Re/Im rectangle
premises.  Schema v32 adds a centered facade over that route, fixing the
unshifted midpoint to the shifted midpoint minus the checked inverse-sum
midpoint and fixing the Re/Im radii to the shifted error plus inverse-sum
radii.
Schema v33 adds a real-only centered facade for the same shift16 route.  Since
the Omega anchor only depends on the real part, this facade spends only
`shiftedErr + invReRadius` instead of also charging the imaginary inverse-sum
radius.
Schema v34 adds a log-pi interval facade over the real-only route.  Future
proof-data can supply a checked interval for `Real.log Real.pi` plus rational
comparisons that mention `logPiLower/logPiUpper`, instead of leaving literal
`Real.log Real.pi` premises at the generated endpoint surface.
Schema v35 adds the first fixed-constant facade for the live endpoint: it fixes
the shifted digamma center, `shiftedErr = 5e-22`, and a narrow log-pi interval,
then discharges the remaining rational endpoint comparisons in Lean.  The only
open analytic inputs are the tight shifted-digamma complex ball and the checked
log-pi interval.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_component_endpoint_worklist.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_endpoint_rational_lean.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_endpoint_rational_lean.md"
)
DEFAULT_OUT_LEAN = (
    ROOT
    / "Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointRationalImport.lean"
)

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.v21"
)
SCHEMA = "q3_psdpd_step33_a_refined_subchunk_endpoint_rational_lean.v35"

FIRST_SHAPE_DERIV_ANCHOR_LOWER = Fraction(
    -96383175790535848471,
    1000000000000000000000000,
)
FIRST_SHAPE_DERIV_ANCHOR_UPPER = Fraction(
    -96383175790535848469,
    1000000000000000000000000,
)
SHIFT16_N16_INVSUM_RE_LOWER = Fraction(
    "0.700924887563594248046878214364"
)
SHIFT16_N16_INVSUM_RE_UPPER = Fraction(
    "0.700924887563594248046878214365"
)
SHIFT16_N16_INVSUM_IM_LOWER = Fraction(
    "-0.000799431431042814488464286604"
)
SHIFT16_N16_INVSUM_IM_UPPER = Fraction(
    "-0.000799431431042814488464286603"
)
SHIFT16_ADD16_FIXED_PSI_RE_CENTER = Fraction(
    "3.457934361506642309616650171583002119"
)
SHIFT16_ADD16_FIXED_PSI_IM_CENTER = Fraction(
    "0.000787336342742450123549615764241626"
)
SHIFT16_ADD16_FIXED_SHIFTED_ERR = Fraction(
    "0.0000000000000000000005"
)
SHIFT16_ADD16_FIXED_LOG_PI_LOWER = Fraction(
    "1.144729885849400174143417351353058711"
)
SHIFT16_ADD16_FIXED_LOG_PI_UPPER = Fraction(
    "1.144729885849400174143437351353058712"
)

FIRST_ROW_SHAPE_PRELUDE_END = (
    "\ntheorem primaryFiniteRow0Parent0Split100Sub0EndpointRationalCert_generated :"
)


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


def frac(value: Any) -> Fraction:
    return Fraction(str(value))


def lean_rat(value: Fraction | str) -> str:
    q = frac(value) if not isinstance(value, Fraction) else value
    if q.denominator == 1:
        return f"({q.numerator} : Real)"
    return f"(({q.numerator} : Real) / ({q.denominator} : Real))"


def first_row_shape_prelude_from_existing() -> str:
    """Preserve the checked first-row ShapeSq prelude until it gets its own emitter.

    The active endpoint Lean file already contains a hole-free checked first-row
    shape payload.  This endpoint emitter owns the rational/Omega landing layer,
    so for now it preserves that prelude instead of silently deleting it during
    regeneration.
    """
    if not DEFAULT_OUT_LEAN.exists():
        raise FileNotFoundError(
            f"missing checked shape prelude source: {DEFAULT_OUT_LEAN}"
        )
    text = DEFAULT_OUT_LEAN.read_text(encoding="utf-8")
    namespace_marker = (
        "namespace RawOmegaATaylorModelCertificate\n\n"
    )
    start = text.find(namespace_marker)
    body_start = start + len(namespace_marker)
    end = text.find(FIRST_ROW_SHAPE_PRELUDE_END, body_start)
    if start < 0 or end < 0:
        raise ValueError(
            "could not locate first-row checked ShapeSq prelude in "
            f"{DEFAULT_OUT_LEAN}"
        )
    prelude = text[body_start:end].strip()
    if (
        "primaryFiniteRow0Parent0Split100Sub0ShapeAnchorValueBounds_generated" not in prelude
        or "primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated" not in prelude
    ):
        raise ValueError(
            "checked first-row shape anchor prelude missing from preserved prelude"
        )
    return prelude + "\n\n"


def theorem_name(row: dict[str, Any]) -> str:
    family = str(row["family"])
    if family != "primary_finite":
        raise ValueError(f"unsupported endpoint rational family: {family!r}")
    return (
        "primaryFinite"
        f"Row{row['row']}"
        f"Parent{row['parentChunk']}"
        f"Split{row['split']}"
        f"Sub{row['subchunk']}"
        "EndpointRationalCert_generated"
    )


def interval_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_endpoint_bounds_generated",
    )


def shape_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "ShapeSqEndpointBounds_of_value_deriv_bounds_generated",
    )


def shape_anchor_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "ShapeSqEndpointBounds_of_value_deriv_anchor_value_bounds_generated",
    )


def shape_deriv_anchor_second_deriv_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "ShapeDerivClosedForm_interval_bounds_of_anchor_second_deriv_bound_generated",
    )


def shape_value_from_deriv_anchor_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "ShapeValueBounds_of_deriv_bounds_and_anchor_generated",
    )


def shape_sq_from_deriv_anchor_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "ShapeSqEndpointBounds_of_deriv_bounds_and_anchor_generated",
    )


def shape_sq_from_second_deriv_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "ShapeSqEndpointBounds_of_second_deriv_bound_generated",
    )


def shape_sq_from_inner_deriv_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "ShapeSqEndpointBounds_of_inner_deriv_interval_bounds_generated",
    )


def shape_sq_endpoint_bounds_closed_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "ShapeSqEndpointBounds_generated",
    )


def omega_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaEndpointBounds_of_prefix_tail_closed_form_generated",
    )


def omega_first_term_lower_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "TrigammaImFirstTermLower_generated",
    )


def omega_first_term_upper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "TrigammaImFirstTermUpper_generated",
    )


def omega_derivative_closed_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaEndpointBounds_of_anchor_prefix_tail_closed_form_generated",
    )


def omega_direct_anchor_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaEndpointBounds_of_direct_anchor_generated",
    )


def omega_direct_anchor_pair_wrapper_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaEndpointBounds_of_direct_anchor_pair_generated",
    )


def interval_from_direct_anchor_pair_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_direct_anchor_pair_and_shape_generated",
    )


def omega_re_series_anchor_pair_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorPair_of_re_series_interval_generated",
    )


def interval_from_re_series_interval_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_re_series_interval_and_shape_generated",
    )


def omega_re_series_prefix_bounds_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorReSeriesPrefixBoundsN16_generated",
    )


def omega_re_series_n16_anchor_pair_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorPair_of_re_series_N16_prefix_generated",
    )


def interval_from_re_series_n16_prefix_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_re_series_N16_prefix_and_shape_generated",
    )


def omega_shifted_stieltjes_anchor_pair_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorPair_of_shifted_stieltjes_generated",
    )


def interval_from_shifted_stieltjes_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_stieltjes_and_shape_generated",
    )


def omega_main_error_anchor_pair_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorPair_of_main_error_generated",
    )


def interval_from_main_error_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_main_error_and_shape_generated",
    )


def interval_from_main_error_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_main_error_generated",
    )


def omega_shifted_digamma_main_error_anchor_pair_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorPair_of_shifted_digamma_main_error_generated",
    )


def interval_from_shifted_digamma_main_error_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_main_error_and_shape_generated",
    )


def interval_from_shifted_digamma_main_error_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_main_error_generated",
    )


def omega_shifted_digamma_complex_main_error_anchor_pair_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorPair_of_shifted_digamma_complex_main_error_generated",
    )


def interval_from_shifted_digamma_complex_main_error_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_complex_main_error_and_shape_generated",
    )


def interval_from_shifted_digamma_complex_main_error_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_complex_main_error_generated",
    )


def omega_shifted_digamma_rect_error_anchor_pair_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorPair_of_shifted_digamma_rect_error_generated",
    )


def interval_from_shifted_digamma_rect_error_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_rect_error_and_shape_generated",
    )


def omega_shifted_digamma_rect_interval_anchor_pair_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "OmegaAnchorPair_of_shifted_digamma_rect_interval_generated",
    )


def interval_from_shifted_digamma_rect_interval_shape_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_rect_interval_and_shape_generated",
    )


def interval_from_shifted_digamma_rect_error_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_rect_error_generated",
    )


def interval_from_shifted_digamma_rect_interval_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_rect_interval_generated",
    )


def interval_from_shifted_digamma_rect_shift16_n16_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16",
    )


def interval_from_shifted_digamma_rect_shift16_n16_invsum_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16_invSumGenerated",
    )


def interval_from_shifted_digamma_rect_shift16_n16_complex_main_error_invsum_theorem_name(
    row: dict[str, Any],
) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16_complexMainError_invSumGenerated",
    )


def interval_from_shifted_digamma_rect_shift16_n16_centered_complex_main_error_invsum_theorem_name(
    row: dict[str, Any],
) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16_centeredComplexMainError_invSumGenerated",
    )


def interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_theorem_name(
    row: dict[str, Any],
) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shiftedDigammaAdd16_centeredComplexMainError_invSumRealOnlyGenerated",
    )


def interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_log_pi_interval_theorem_name(
    row: dict[str, Any],
) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shiftedDigammaAdd16_centeredComplexMainError_invSumRealOnly_logPiIntervalGenerated",
    )


def interval_from_shifted_digamma_add16_fixed_complex_main_error_log_pi_interval_theorem_name(
    row: dict[str, Any],
) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiIntervalGenerated",
    )


def shifted_digamma_rect_shift16_n16_invsum_bounds_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "Shift16N16InvSumBounds_generated",
    )


def shifted_digamma_rect_shift16_n16_point_eq_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "Shift16N16ShiftedDigammaPoint_eq_generated",
    )


def shifted_digamma_rect_shift16_n16_point_re_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "Shift16N16ShiftedDigammaPoint_re_generated",
    )


def shifted_digamma_rect_shift16_n16_point_im_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "Shift16N16ShiftedDigammaPoint_im_generated",
    )


def interval_from_shifted_digamma_series_prefix_tail_interval_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_prefix_tail_interval_generated",
    )


def interval_from_shifted_digamma_series_n16_prefix_tail_interval_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_prefix_tail_interval_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_tail_interval_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_tail_interval_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_interval_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_tail_interval_generated",
    )


def interval_from_shifted_digamma_series_prefix_tail_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_prefix_tail_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_tail_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_tail_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_tail_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_majorant_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_majorant_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_abs_generated",
    )


def interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_centered_abs_theorem_name(row: dict[str, Any]) -> str:
    return theorem_name(row).replace(
        "EndpointRationalCert_generated",
        "EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_centered_abs_generated",
    )


def is_first_derivative_closed_row(row: dict[str, Any]) -> bool:
    return (
        row.get("family") == "primary_finite"
        and int(row.get("row")) == 0
        and int(row.get("parentChunk")) == 0
        and int(row.get("split")) == 100
        and int(row.get("subchunk")) == 0
    )


def endpoint_fact(row: dict[str, Any], endpoint: str) -> Fraction:
    for item in row["endpointFacts"]:
        if item.get("endpoint") == endpoint:
            return frac(item["candidateRational"])
    raise KeyError(endpoint)


def endpoint_interval(row: dict[str, Any], key: str, side: str) -> Fraction:
    return frac(row["endpointIntervals"][key][side]["rational"])


def row_terms(row: dict[str, Any]) -> dict[str, Fraction]:
    interval = row["interval"]
    params = row["parameters"]
    omega_center = frac(params["omegaCenter"])
    omega_radius = frac(params["omegaRadius"])
    shape_center = frac(params["shapeSqCenter"])
    shape_radius = frac(params["shapeSqRadius"])
    return {
        "k": Fraction(int(row["k"]), 1),
        "ell": frac(row["ell"]),
        "a": frac(interval["a"]),
        "b": frac(interval["b"]),
        "anchor": frac(interval["anchor"]),
        "etaRadius": frac(interval["etaRadius"]),
        "omegaCenter": omega_center,
        "omegaRadius": omega_radius,
        "shapeSqCenter": shape_center,
        "shapeSqRadius": shape_radius,
        "omegaDerivLower": endpoint_fact(row, "omegaDerivLower"),
        "omegaDerivUpper": endpoint_fact(row, "omegaDerivUpper"),
        "omegaAnchorLower": endpoint_fact(row, "omegaAnchorLower"),
        "omegaAnchorUpper": endpoint_fact(row, "omegaAnchorUpper"),
        "shapeSqDerivLower": endpoint_interval(row, "shapeSqDerivative", "lower"),
        "shapeSqDerivUpper": endpoint_interval(row, "shapeSqDerivative", "upper"),
        "shapeSqAnchorLower": endpoint_fact(row, "shapeSqAnchorLower"),
        "shapeSqAnchorUpper": endpoint_fact(row, "shapeSqAnchorUpper"),
        "shapeValueLower": endpoint_interval(row, "shapeValue", "lower"),
        "shapeValueUpper": endpoint_interval(row, "shapeValue", "upper"),
        "shapeDerivLower": endpoint_interval(row, "shapeDerivative", "lower"),
        "shapeDerivUpper": endpoint_interval(row, "shapeDerivative", "upper"),
        "shapeAnchorValueLower": endpoint_fact(row, "shapeAnchorValueLower"),
        "shapeAnchorValueUpper": endpoint_fact(row, "shapeAnchorValueUpper"),
        "omegaLower": omega_center - omega_radius,
        "omegaUpper": omega_center + omega_radius,
        "shapeSqLower": shape_center - shape_radius,
        "shapeSqUpper": shape_center + shape_radius,
    }


def omega_re_series_term_fraction(eta: Fraction, n: int) -> Fraction:
    x = Fraction(n, 1) + Fraction(1, 4)
    y = eta / 2
    return Fraction(1, n + 1) - x / (x * x + y * y)


def omega_re_series_prefix_fraction(eta: Fraction, n: int) -> Fraction:
    return sum((omega_re_series_term_fraction(eta, i) for i in range(n)), Fraction(0))


TERM_ORDER = [
    "a",
    "b",
    "anchor",
    "etaRadius",
    "omegaCenter",
    "omegaRadius",
    "shapeSqCenter",
    "shapeSqRadius",
    "omegaDerivLower",
    "omegaDerivUpper",
    "omegaAnchorLower",
    "omegaAnchorUpper",
    "shapeSqDerivLower",
    "shapeSqDerivUpper",
    "shapeSqAnchorLower",
    "shapeSqAnchorUpper",
    "omegaLower",
    "omegaUpper",
    "shapeSqLower",
    "shapeSqUpper",
]


def render_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    args = "\n      ".join(lean_rat(terms[key]) for key in TERM_ORDER)
    return f"""theorem {theorem_name(row)} :
    LocalRawOmegaComponentDirectEndpointRationalCert
      {args} := by
  refine
    {{ hAnchorIn := by norm_num
      hEtaLeft := by norm_num
      hEtaRight := by norm_num
      hOmegaContain := by
        norm_num [intervalAutoAbsBound, intervalAutoCenterError]
      hShapeSqContain := by
        norm_num [intervalAutoAbsBound, intervalAutoCenterError]
      hOmegaLower := by norm_num
      hOmegaUpper := by norm_num
      hShapeSqLower := by norm_num
      hShapeSqUpper := by norm_num }}
"""


def render_omega_wrapper_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    omega_deriv_lower = lean_rat(terms["omegaDerivLower"])
    omega_deriv_upper = lean_rat(terms["omegaDerivUpper"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    return f"""theorem {omega_wrapper_theorem_name(row)}
    (derivN anchorN anchorQ2PrefixN anchorQ3PrefixN : Nat)
    (termLower termUpper : Nat -> Real)
    (etaUpper imPrefixLower imPrefixUpper tailRadius
      anchorConstLower anchorConstUpper anchorPrefixLower anchorPrefixUpper
      anchorTailLower anchorTailUpper anchorQ2Lower anchorQ2Upper
      anchorQ3Upper anchorQ2TailUpper anchorQ3TailUpper : Real)
    (hANonneg : 0 <= {a})
    (hBUpper : {b} <= etaUpper)
    (hTermLower :
      ∀ eta ∈ Set.Icc {a} {b}, ∀ n : Nat, n < derivN ->
        termLower n <= trigammaImSeriesTermClosedForm eta n)
    (hTermUpper :
      ∀ eta ∈ Set.Icc {a} {b}, ∀ n : Nat, n < derivN ->
        trigammaImSeriesTermClosedForm eta n <= termUpper n)
    (hPrefixLower : imPrefixLower <= (Finset.range derivN).sum termLower)
    (hPrefixUpper : (Finset.range derivN).sum termUpper <= imPrefixUpper)
    (hDerivTailIndexGeOne : 1 <= derivN)
    (hDerivTailClosedFormUpper :
      etaUpper * (1 / (((derivN : Real) + (1 / 4 : Real) - 1) ^ 2)) <=
          tailRadius)
    (hDerivLower :
      {omega_deriv_lower} <= -((imPrefixUpper + tailRadius) * (1 / 2 : Real)))
    (hDerivUpper :
      -((imPrefixLower - tailRadius) * (1 / 2 : Real)) <=
        {omega_deriv_upper})
    (hAnchorNonneg : 0 <= {anchor})
    (hAnchorEtaUpper : {anchor} <= etaUpper)
    (hAnchorConstLower :
      anchorConstLower <= -Real.eulerMascheroniConstant - Real.log Real.pi)
    (hAnchorConstUpper :
      -Real.eulerMascheroniConstant - Real.log Real.pi <= anchorConstUpper)
    (hAnchorPrefixLower :
      anchorPrefixLower <=
        (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm {anchor}))
    (hAnchorPrefixUpper :
      (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm {anchor}) <=
        anchorPrefixUpper)
    (hAnchorQ2TailIndexGeOne : 1 <= anchorN + anchorQ2PrefixN)
    (hAnchorQ2PrefixLower :
      anchorQ2Lower <=
        (Finset.range anchorQ2PrefixN).sum (fun n : Nat =>
          1 /
            ((((n + anchorN : Nat) : Real) + (1 / 4 : Real)) ^ 2)))
    (hAnchorQ2PrefixUpper :
      (Finset.range anchorQ2PrefixN).sum (fun n : Nat =>
          1 /
            ((((n + anchorN : Nat) : Real) + (1 / 4 : Real)) ^ 2)) +
            anchorQ2TailUpper <=
        anchorQ2Upper)
    (hAnchorQ2TailUpperFromClosedForm :
      1 / ((((anchorN + anchorQ2PrefixN : Nat) : Real) +
              (1 / 4 : Real)) - 1) <=
        anchorQ2TailUpper)
    (hAnchorQ3TailIndexGeOne : 1 <= anchorN + anchorQ3PrefixN)
    (hAnchorQ3PrefixUpper :
      (Finset.range anchorQ3PrefixN).sum (fun n : Nat =>
          (((3 / 4 : Real) ^ 2 + (etaUpper / 2) ^ 2) /
            ((((n + anchorN : Nat) : Real) + (1 / 4 : Real)) ^ 3))) +
            anchorQ3TailUpper <=
        anchorQ3Upper)
    (hAnchorQ3TailUpperFromClosedForm :
      ((3 / 4 : Real) ^ 2 + (etaUpper / 2) ^ 2) *
          (1 /
            ((((anchorN + anchorQ3PrefixN : Nat) : Real) +
                (1 / 4 : Real) - 1) ^ 2)) <=
        anchorQ3TailUpper)
    (hAnchorTailLowerFromPositiveSeries :
      anchorTailLower <= (-(3 / 4 : Real)) * anchorQ2Upper - anchorQ3Upper)
    (hAnchorTailUpperFromPositiveSeries :
      (-(3 / 4 : Real)) * anchorQ2Lower + anchorQ3Upper <= anchorTailUpper)
    (hAnchorLowerFromReSeries :
      {omega_anchor_lower} <=
        anchorConstLower + anchorPrefixLower + anchorTailLower)
    (hAnchorUpperFromReSeries :
      anchorConstUpper + anchorPrefixUpper + anchorTailUpper <=
        {omega_anchor_upper}) :
    Step22OmegaClosedFormEndpointBoundsCert
      {a} {b} {anchor}
      {omega_deriv_lower} {omega_deriv_upper}
      {omega_anchor_lower} {omega_anchor_upper} := by
  have hEtaUpperNonneg : 0 <= etaUpper := by
    have hbNonneg : 0 <= {b} := by norm_num
    exact le_trans hbNonneg hBUpper
  have hTailSum :
      (∑' n : Nat,
        etaUpper / ((((n + derivN : Nat) : Real) + (1 / 4 : Real)) ^ 3)) <=
          tailRadius := by
    exact le_trans
      (tsum_trigamma_cubic_majorant_tail_le_closed_form
        etaUpper derivN hEtaUpperNonneg hDerivTailIndexGeOne)
      hDerivTailClosedFormUpper
  have hAnchorTail :=
    step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_prefix_tail_closed_form
      {anchor} etaUpper anchorN anchorQ2PrefixN anchorQ3PrefixN
      anchorQ2Lower anchorQ2Upper anchorQ3Upper anchorQ2TailUpper
      anchorQ3TailUpper anchorTailLower anchorTailUpper hAnchorNonneg
      hAnchorEtaUpper hAnchorQ2TailIndexGeOne hAnchorQ2PrefixLower
      hAnchorQ2PrefixUpper hAnchorQ2TailUpperFromClosedForm
      hAnchorQ3TailIndexGeOne hAnchorQ3PrefixUpper
      hAnchorQ3TailUpperFromClosedForm hAnchorTailLowerFromPositiveSeries
      hAnchorTailUpperFromPositiveSeries
  exact
    Step22OmegaClosedFormEndpointBoundsCert.of_re_series_anchor_interval_tail_trigamma_im_closed_form_term_prefix_cubic_tail_Icc
      derivN anchorN termLower termUpper hANonneg hBUpper hTermLower
      hTermUpper hPrefixLower hPrefixUpper hTailSum hDerivLower hDerivUpper
      hAnchorConstLower hAnchorConstUpper hAnchorPrefixLower
      hAnchorPrefixUpper hAnchorTail.1 hAnchorTail.2 hAnchorLowerFromReSeries
      hAnchorUpperFromReSeries
"""


def render_first_derivative_closed_theorems(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    omega_deriv_lower = lean_rat(terms["omegaDerivLower"])
    omega_deriv_upper = lean_rat(terms["omegaDerivUpper"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    lower_name = omega_first_term_lower_theorem_name(row)
    upper_name = omega_first_term_upper_theorem_name(row)
    wrapper_name = omega_wrapper_theorem_name(row)
    theorem = omega_derivative_closed_wrapper_theorem_name(row)
    return f"""theorem {lower_name} :
    ∀ eta ∈ Set.Icc {a} {b},
      (-16 / 5 : Real) <= trigammaImSeriesTermClosedForm eta 0 := by
  intro eta heta
  unfold trigammaImSeriesTermClosedForm
  have hhigh : eta <= {b} := heta.2
  have hnum_le : (1 / 2 : Real) * (eta / 2) <= (1 : Real) / 80 := by
    nlinarith [hhigh]
  have hden_base : (1 / 16 : Real) <= (1 / 16 : Real) + (eta / 2) ^ 2 := by
    nlinarith [sq_nonneg (eta / 2)]
  have hden_sq_base :
      ((1 / 16 : Real) ^ 2) <=
        ((1 / 16 : Real) + (eta / 2) ^ 2) ^ 2 := by
    exact sq_le_sq'
      (by
        nlinarith [hden_base] :
          -((1 / 16 : Real) + (eta / 2) ^ 2) <= (1 / 16 : Real))
      hden_base
  have hden_sq_pos :
      0 < ((1 / 16 : Real) + (eta / 2) ^ 2) ^ 2 := by
    positivity
  have hq_le :
      ((1 / 2 : Real) * (eta / 2)) /
          (((1 / 16 : Real) + (eta / 2) ^ 2) ^ 2) <=
        (16 / 5 : Real) := by
    have hmul :
        ((1 / 2 : Real) * (eta / 2)) <=
          (16 / 5 : Real) *
            (((1 / 16 : Real) + (eta / 2) ^ 2) ^ 2) := by
      nlinarith [hnum_le, hden_sq_base]
    exact (div_le_iff₀ hden_sq_pos).2 hmul
  norm_num
  exact hq_le

theorem {upper_name} :
    ∀ eta ∈ Set.Icc {a} {b},
      trigammaImSeriesTermClosedForm eta 0 <= (-3 : Real) := by
  intro eta heta
  unfold trigammaImSeriesTermClosedForm
  have hlow : {a} <= eta := heta.1
  have hhigh : eta <= {b} := heta.2
  have h_eta2_high : eta / 2 <= (1 : Real) / 40 := by
    nlinarith [hhigh]
  have hsq : (eta / 2) ^ 2 <= ((1 : Real) / 40) ^ 2 := by
    exact sq_le_sq'
      (by nlinarith [hlow] : -((1 : Real) / 40) <= eta / 2)
      h_eta2_high
  have hden_le : (1 / 16 : Real) + (eta / 2) ^ 2 <= (101 : Real) / 1600 := by
    norm_num at hsq ⊢
    linarith
  have hden_sq_le :
      ((1 / 16 : Real) + (eta / 2) ^ 2) ^ 2 <=
        ((101 : Real) / 1600) ^ 2 := by
    exact sq_le_sq'
      (by
        nlinarith [sq_nonneg (eta / 2)] :
          -((101 : Real) / 1600) <= (1 / 16 : Real) + (eta / 2) ^ 2)
      hden_le
  have hnum_const :
      (3 : Real) * (((101 : Real) / 1600) ^ 2) <=
        (1 / 2) * (eta / 2) := by
    nlinarith [hlow]
  have hnum :
      (3 : Real) * (((1 / 16 : Real) + (eta / 2) ^ 2) ^ 2) <=
        (1 / 2) * (eta / 2) := by
    nlinarith [hden_sq_le, hnum_const]
  have hden_sq_pos :
      0 < ((1 / 16 : Real) + (eta / 2) ^ 2) ^ 2 := by
    positivity
  have hdiv :
      (3 : Real) <=
        ((1 / 2) * (eta / 2)) /
          (((1 / 16 : Real) + (eta / 2) ^ 2) ^ 2) := by
    exact (le_div_iff₀ hden_sq_pos).2 hnum
  norm_num
  exact hdiv

theorem {theorem}
    (anchorN anchorQ2PrefixN anchorQ3PrefixN : Nat)
    (anchorConstLower anchorConstUpper anchorPrefixLower anchorPrefixUpper
      anchorTailLower anchorTailUpper anchorQ2Lower anchorQ2Upper
      anchorQ3Upper anchorQ2TailUpper anchorQ3TailUpper : Real)
    (hAnchorConstLower :
      anchorConstLower <= -Real.eulerMascheroniConstant - Real.log Real.pi)
    (hAnchorConstUpper :
      -Real.eulerMascheroniConstant - Real.log Real.pi <= anchorConstUpper)
    (hAnchorPrefixLower :
      anchorPrefixLower <=
        (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm {anchor}))
    (hAnchorPrefixUpper :
      (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm {anchor}) <=
        anchorPrefixUpper)
    (hAnchorQ2TailIndexGeOne : 1 <= anchorN + anchorQ2PrefixN)
    (hAnchorQ2PrefixLower :
      anchorQ2Lower <=
        (Finset.range anchorQ2PrefixN).sum (fun n : Nat =>
          1 /
            ((((n + anchorN : Nat) : Real) + (1 / 4 : Real)) ^ 2)))
    (hAnchorQ2PrefixUpper :
      (Finset.range anchorQ2PrefixN).sum (fun n : Nat =>
          1 /
            ((((n + anchorN : Nat) : Real) + (1 / 4 : Real)) ^ 2)) +
            anchorQ2TailUpper <=
        anchorQ2Upper)
    (hAnchorQ2TailUpperFromClosedForm :
      1 / ((((anchorN + anchorQ2PrefixN : Nat) : Real) +
              (1 / 4 : Real)) - 1) <=
        anchorQ2TailUpper)
    (hAnchorQ3TailIndexGeOne : 1 <= anchorN + anchorQ3PrefixN)
    (hAnchorQ3PrefixUpper :
      (Finset.range anchorQ3PrefixN).sum (fun n : Nat =>
          (((3 / 4 : Real) ^ 2 + ({b} / 2) ^ 2) /
            ((((n + anchorN : Nat) : Real) + (1 / 4 : Real)) ^ 3))) +
            anchorQ3TailUpper <=
        anchorQ3Upper)
    (hAnchorQ3TailUpperFromClosedForm :
      ((3 / 4 : Real) ^ 2 + ({b} / 2) ^ 2) *
          (1 /
            ((((anchorN + anchorQ3PrefixN : Nat) : Real) +
                (1 / 4 : Real) - 1) ^ 2)) <=
        anchorQ3TailUpper)
    (hAnchorTailLowerFromPositiveSeries :
      anchorTailLower <= (-(3 / 4 : Real)) * anchorQ2Upper - anchorQ3Upper)
    (hAnchorTailUpperFromPositiveSeries :
      (-(3 / 4 : Real)) * anchorQ2Lower + anchorQ3Upper <= anchorTailUpper)
    (hAnchorLowerFromReSeries :
      {omega_anchor_lower} <=
        anchorConstLower + anchorPrefixLower + anchorTailLower)
    (hAnchorUpperFromReSeries :
      anchorConstUpper + anchorPrefixUpper + anchorTailUpper <=
        {omega_anchor_upper}) :
    Step22OmegaClosedFormEndpointBoundsCert
      {a} {b} {anchor}
      {omega_deriv_lower} {omega_deriv_upper}
      {omega_anchor_lower} {omega_anchor_upper} := by
  exact
    {wrapper_name}
      1 anchorN anchorQ2PrefixN anchorQ3PrefixN
      (fun _ => (-16 / 5 : Real)) (fun _ => (-3 : Real))
      {b} (-16 / 5 : Real) (-3 : Real) ((4 : Real) / 5)
      anchorConstLower anchorConstUpper anchorPrefixLower anchorPrefixUpper
      anchorTailLower anchorTailUpper anchorQ2Lower anchorQ2Upper
      anchorQ3Upper anchorQ2TailUpper anchorQ3TailUpper
      (by norm_num)
      (by norm_num)
      (by
        intro eta heta n hn
        have hn0 : n = 0 := Nat.lt_one_iff.mp hn
        subst n
        exact {lower_name} eta heta)
      (by
        intro eta heta n hn
        have hn0 : n = 0 := Nat.lt_one_iff.mp hn
        subst n
        exact {upper_name} eta heta)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      hAnchorConstLower
      hAnchorConstUpper
      hAnchorPrefixLower
      hAnchorPrefixUpper
      hAnchorQ2TailIndexGeOne
      hAnchorQ2PrefixLower
      hAnchorQ2PrefixUpper
      hAnchorQ2TailUpperFromClosedForm
      hAnchorQ3TailIndexGeOne
      hAnchorQ3PrefixUpper
      hAnchorQ3TailUpperFromClosedForm
      hAnchorTailLowerFromPositiveSeries
      hAnchorTailUpperFromPositiveSeries
      hAnchorLowerFromReSeries
      hAnchorUpperFromReSeries
"""


def render_first_direct_anchor_closed_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    omega_deriv_lower = lean_rat(terms["omegaDerivLower"])
    omega_deriv_upper = lean_rat(terms["omegaDerivUpper"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    lower_name = omega_first_term_lower_theorem_name(row)
    upper_name = omega_first_term_upper_theorem_name(row)
    theorem = omega_direct_anchor_wrapper_theorem_name(row)
    return f"""theorem {theorem}
    (hAnchorLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor})
    (hAnchorUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper}) :
    Step22OmegaClosedFormEndpointBoundsCert
      {a} {b} {anchor}
      {omega_deriv_lower} {omega_deriv_upper}
      {omega_anchor_lower} {omega_anchor_upper} := by
  exact
    Step22OmegaClosedFormEndpointBoundsCert.of_direct_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc
      (a := {a}) (b := {b}) (anchor := {anchor})
      (omegaDerivLower := {omega_deriv_lower})
      (omegaDerivUpper := {omega_deriv_upper})
      (omegaAnchorLower := {omega_anchor_lower})
      (omegaAnchorUpper := {omega_anchor_upper})
      (imPrefixLower := (-16 / 5 : Real))
      (imPrefixUpper := (-3 : Real))
      (tailRadius := ((4 : Real) / 5))
      (etaUpper := {b})
      1 (fun _ => (-16 / 5 : Real)) (fun _ => (-3 : Real))
      (by norm_num)
      (by norm_num)
      (by
        intro eta heta n hn
        have hn0 : n = 0 := Nat.lt_one_iff.mp hn
        subst n
        exact {lower_name} eta heta)
      (by
        intro eta heta n hn
        have hn0 : n = 0 := Nat.lt_one_iff.mp hn
        subst n
        exact {upper_name} eta heta)
      (by norm_num)
      (by norm_num)
      (by
        exact le_trans
          (tsum_trigamma_cubic_majorant_tail_le_closed_form
            {b} 1 (by norm_num) (by norm_num))
          (by norm_num))
      (by norm_num)
      (by norm_num)
      hAnchorLower
      hAnchorUpper
"""


def render_first_direct_anchor_pair_closed_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    omega_deriv_lower = lean_rat(terms["omegaDerivLower"])
    omega_deriv_upper = lean_rat(terms["omegaDerivUpper"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    direct_name = omega_direct_anchor_wrapper_theorem_name(row)
    pair_name = omega_direct_anchor_pair_wrapper_theorem_name(row)
    return f"""theorem {pair_name}
    (hAnchor :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper}) :
    Step22OmegaClosedFormEndpointBoundsCert
      {a} {b} {anchor}
      {omega_deriv_lower} {omega_deriv_upper}
      {omega_anchor_lower} {omega_anchor_upper} := by
  exact {direct_name} hAnchor.1 hAnchor.2
"""


def render_first_re_series_anchor_pair_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    pair_name = omega_re_series_anchor_pair_theorem_name(row)
    return f"""theorem {pair_name}
    (anchorN : Nat)
    (anchorConstLower anchorConstUpper anchorPrefixLower anchorPrefixUpper
      anchorTailLower anchorTailUpper : Real)
    (hAnchorConstLower :
      anchorConstLower <= -Real.eulerMascheroniConstant - Real.log Real.pi)
    (hAnchorConstUpper :
      -Real.eulerMascheroniConstant - Real.log Real.pi <= anchorConstUpper)
    (hAnchorPrefixLower :
      anchorPrefixLower <=
        (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm {anchor}))
    (hAnchorPrefixUpper :
      (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm {anchor}) <=
        anchorPrefixUpper)
    (hAnchorTailLower :
      anchorTailLower <=
        ∑' n : Nat, step22OmegaArchWeightReSeriesTerm {anchor} (n + anchorN))
    (hAnchorTailUpper :
      (∑' n : Nat, step22OmegaArchWeightReSeriesTerm {anchor} (n + anchorN)) <=
        anchorTailUpper)
    (hAnchorLowerFromReSeries :
      {omega_anchor_lower} <=
        anchorConstLower + anchorPrefixLower + anchorTailLower)
    (hAnchorUpperFromReSeries :
      anchorConstUpper + anchorPrefixUpper + anchorTailUpper <=
        {omega_anchor_upper}) :
    {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper} := by
  exact
    step22OmegaArchWeight_bounds_from_re_series_prefix_tail_interval
      {anchor} {omega_anchor_lower} {omega_anchor_upper}
      anchorConstLower anchorConstUpper anchorPrefixLower anchorPrefixUpper
      anchorTailLower anchorTailUpper anchorN
      hAnchorConstLower hAnchorConstUpper hAnchorPrefixLower hAnchorPrefixUpper
      hAnchorTailLower hAnchorTailUpper hAnchorLowerFromReSeries
      hAnchorUpperFromReSeries
"""


def render_first_re_series_prefix_bounds_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = terms["anchor"]
    prefix_n = 16
    prefix = omega_re_series_prefix_fraction(anchor, prefix_n)
    theorem = omega_re_series_prefix_bounds_theorem_name(row)
    return f"""theorem {theorem} :
    {lean_rat(prefix)} <=
        (Finset.range {prefix_n}).sum
          (step22OmegaArchWeightReSeriesTerm {lean_rat(anchor)}) ∧
      (Finset.range {prefix_n}).sum
          (step22OmegaArchWeightReSeriesTerm {lean_rat(anchor)}) <=
        {lean_rat(prefix)} := by
  constructor <;> norm_num [step22OmegaArchWeightReSeriesTerm]
"""


def render_first_re_series_n16_anchor_pair_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    prefix_n = 16
    prefix = lean_rat(omega_re_series_prefix_fraction(terms["anchor"], prefix_n))
    theorem = omega_re_series_n16_anchor_pair_theorem_name(row)
    pair_name = omega_re_series_anchor_pair_theorem_name(row)
    prefix_name = omega_re_series_prefix_bounds_theorem_name(row)
    return f"""theorem {theorem}
    (anchorConstLower anchorConstUpper anchorTailLower anchorTailUpper : Real)
    (hAnchorConstLower :
      anchorConstLower <= -Real.eulerMascheroniConstant - Real.log Real.pi)
    (hAnchorConstUpper :
      -Real.eulerMascheroniConstant - Real.log Real.pi <= anchorConstUpper)
    (hAnchorTailLower :
      anchorTailLower <=
        ∑' n : Nat, step22OmegaArchWeightReSeriesTerm {anchor} (n + {prefix_n}))
    (hAnchorTailUpper :
      (∑' n : Nat, step22OmegaArchWeightReSeriesTerm {anchor} (n + {prefix_n})) <=
        anchorTailUpper)
    (hAnchorLowerFromReSeries :
      {omega_anchor_lower} <=
        anchorConstLower + {prefix} + anchorTailLower)
    (hAnchorUpperFromReSeries :
      anchorConstUpper + {prefix} + anchorTailUpper <=
        {omega_anchor_upper}) :
    {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper} := by
  exact
    {pair_name}
      {prefix_n} anchorConstLower anchorConstUpper {prefix} {prefix}
      anchorTailLower anchorTailUpper hAnchorConstLower hAnchorConstUpper
      {prefix_name}.1 {prefix_name}.2
      hAnchorTailLower hAnchorTailUpper hAnchorLowerFromReSeries
      hAnchorUpperFromReSeries
"""


def render_first_shifted_stieltjes_anchor_pair_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = omega_shifted_stieltjes_anchor_pair_theorem_name(row)
    return f"""theorem {theorem}
    (shift : Nat)
    (hShiftLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedStieltjesMain
            {anchor} shift -
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedStieltjesErr
            {anchor} shift)
    (hShiftUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedStieltjesMain
            {anchor} shift +
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedStieltjesErr
            {anchor} shift <=
        {omega_anchor_upper}) :
    {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper} := by
  exact
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_anchor_bounds_from_shifted_stieltjes
      {anchor} {omega_anchor_lower} {omega_anchor_upper} shift
      hShiftLower hShiftUpper
"""


def render_first_main_error_anchor_pair_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = omega_main_error_anchor_pair_theorem_name(row)
    return f"""theorem {theorem}
    (main err : Real)
    (hAbs :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} - main| <= err)
    (hMainLower :
      {omega_anchor_lower} <= main - err)
    (hMainUpper :
      main + err <= {omega_anchor_upper}) :
    {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper} := by
  exact
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_anchor_bounds_from_main_error
      {anchor} {omega_anchor_lower} {omega_anchor_upper} main err
      hAbs hMainLower hMainUpper
"""


def render_first_shifted_digamma_main_error_anchor_pair_theorem(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = omega_shifted_digamma_main_error_anchor_pair_theorem_name(row)
    pair_name = omega_main_error_anchor_pair_theorem_name(row)
    return f"""theorem {theorem}
    (shift : Nat) (psiMain err : Real)
    (hShiftedAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re - psiMain| <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain + err <=
        {omega_anchor_upper}) :
    {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper} := by
  exact
    {pair_name}
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
        {anchor} shift psiMain)
      err
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_abs_sub_shifted_digamma_main
        {anchor} shift psiMain err hShiftedAbs)
      hMainLower hMainUpper
"""


def render_first_shifted_digamma_complex_main_error_anchor_pair_theorem(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = omega_shifted_digamma_complex_main_error_anchor_pair_theorem_name(row)
    pair_name = omega_main_error_anchor_pair_theorem_name(row)
    return f"""theorem {theorem}
    (shift : Nat) (psiMain : Complex) (err : Real)
    (hShiftedAbs :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift) - psiMain‖ <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :
    {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper} := by
  exact
    {pair_name}
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
        {anchor} shift psiMain.re)
      err
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_abs_sub_shifted_digamma_complex_main
        {anchor} shift psiMain err hShiftedAbs)
      hMainLower hMainUpper
"""


def render_first_shifted_digamma_rect_error_anchor_pair_theorem(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = omega_shifted_digamma_rect_error_anchor_pair_theorem_name(row)
    pair_name = omega_shifted_digamma_complex_main_error_anchor_pair_theorem_name(row)
    return f"""theorem {theorem}
    (shift : Nat) (psiMain : Complex) (errRe errIm err : Real)
    (hReAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re - psiMain.re| <= errRe)
    (hImAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im - psiMain.im| <= errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :
    {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper} := by
  exact
    {pair_name}
      shift psiMain err
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_complex_main_error_of_re_im_abs
        {anchor} shift psiMain errRe errIm err
        hReAbs hImAbs hErr)
      hMainLower hMainUpper
"""


def render_first_shifted_digamma_rect_interval_anchor_pair_theorem(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = omega_shifted_digamma_rect_interval_anchor_pair_theorem_name(row)
    pair_name = omega_shifted_digamma_complex_main_error_anchor_pair_theorem_name(row)
    return f"""theorem {theorem}
    (shift : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (hReLower :
      reLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re)
    (hReUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re <= reUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImLower :
      imLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im)
    (hImUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im <= imUpper)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :
    {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper} := by
  exact
    {pair_name}
      shift psiMain err
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_complex_main_error_of_re_im_intervals
        {anchor} shift psiMain
        reLower reUpper imLower imUpper errRe errIm err
        hReLower hReUpper hReCenterLower hReCenterUpper
        hImLower hImUpper hImCenterLower hImCenterUpper hErr)
      hMainLower hMainUpper
"""


def render_shape_wrapper_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    shape_value_lower = lean_rat(terms["shapeValueLower"])
    shape_value_upper = lean_rat(terms["shapeValueUpper"])
    shape_deriv_lower = lean_rat(terms["shapeDerivLower"])
    shape_deriv_upper = lean_rat(terms["shapeDerivUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    return f"""theorem {shape_wrapper_theorem_name(row)}
    (hShapeValueLower :
      ∀ eta ∈ Set.Icc {a} {b},
        {shape_value_lower} <=
          centeredBSplineImagTransformRealClosedForm {k} {ell} eta)
    (hShapeValueUpper :
      ∀ eta ∈ Set.Icc {a} {b},
        centeredBSplineImagTransformRealClosedForm {k} {ell} eta <=
          {shape_value_upper})
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc {a} {b},
        {shape_deriv_lower} <=
          centeredBSplineImagTransformRealClosedFormDerivClosedForm {k} {ell} eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc {a} {b},
        centeredBSplineImagTransformRealClosedFormDerivClosedForm {k} {ell} eta <=
          {shape_deriv_upper})
    (hShapeSqAnchorLower :
      {shape_sq_anchor_lower} <=
        (centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor}) ^ 2)
    (hShapeSqAnchorUpper :
      (centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor}) ^ 2 <=
        {shape_sq_anchor_upper}) :
    ShapeSqEndpointBoundsCert
      {k} {ell} {a} {b} {anchor}
      {shape_sq_deriv_lower} {shape_sq_deriv_upper}
      {shape_sq_anchor_lower} {shape_sq_anchor_upper} := by
  exact
    ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals
      hShapeValueLower hShapeValueUpper hShapeDerivLower hShapeDerivUpper
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hShapeSqAnchorLower hShapeSqAnchorUpper
"""


def render_shape_anchor_wrapper_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    shape_value_lower = lean_rat(terms["shapeValueLower"])
    shape_value_upper = lean_rat(terms["shapeValueUpper"])
    shape_deriv_lower = lean_rat(terms["shapeDerivLower"])
    shape_deriv_upper = lean_rat(terms["shapeDerivUpper"])
    shape_anchor_value_lower = lean_rat(terms["shapeAnchorValueLower"])
    shape_anchor_value_upper = lean_rat(terms["shapeAnchorValueUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    return f"""theorem {shape_anchor_wrapper_theorem_name(row)}
    (hShapeValueLower :
      ∀ eta ∈ Set.Icc {a} {b},
        {shape_value_lower} <=
          centeredBSplineImagTransformRealClosedForm {k} {ell} eta)
    (hShapeValueUpper :
      ∀ eta ∈ Set.Icc {a} {b},
        centeredBSplineImagTransformRealClosedForm {k} {ell} eta <=
          {shape_value_upper})
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc {a} {b},
        {shape_deriv_lower} <=
          centeredBSplineImagTransformRealClosedFormDerivClosedForm {k} {ell} eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc {a} {b},
        centeredBSplineImagTransformRealClosedFormDerivClosedForm {k} {ell} eta <=
          {shape_deriv_upper})
    (hShapeAnchorValueLower :
      {shape_anchor_value_lower} <=
        centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor})
    (hShapeAnchorValueUpper :
      centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor} <=
        {shape_anchor_value_upper}) :
    ShapeSqEndpointBoundsCert
      {k} {ell} {a} {b} {anchor}
      {shape_sq_deriv_lower} {shape_sq_deriv_upper}
      {shape_sq_anchor_lower} {shape_sq_anchor_upper} := by
  exact
    ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals_anchorValueBounds
      hShapeValueLower hShapeValueUpper hShapeDerivLower hShapeDerivUpper
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hShapeAnchorValueLower hShapeAnchorValueUpper
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
"""


def render_first_shape_anchor_second_deriv_reduction_theorems(
    row: dict[str, Any],
) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    shape_value_lower = lean_rat(terms["shapeValueLower"])
    shape_value_upper = lean_rat(terms["shapeValueUpper"])
    shape_deriv_lower = lean_rat(terms["shapeDerivLower"])
    shape_deriv_upper = lean_rat(terms["shapeDerivUpper"])
    shape_deriv_anchor_lower = lean_rat(FIRST_SHAPE_DERIV_ANCHOR_LOWER)
    shape_deriv_anchor_upper = lean_rat(FIRST_SHAPE_DERIV_ANCHOR_UPPER)
    shape_anchor_value_lower = lean_rat(terms["shapeAnchorValueLower"])
    shape_anchor_value_upper = lean_rat(terms["shapeAnchorValueUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    deriv_interval_name = shape_deriv_anchor_second_deriv_wrapper_theorem_name(row)
    value_name = shape_value_from_deriv_anchor_wrapper_theorem_name(row)
    sq_deriv_anchor_name = shape_sq_from_deriv_anchor_wrapper_theorem_name(row)
    sq_second_name = shape_sq_from_second_deriv_wrapper_theorem_name(row)
    sq_inner_name = shape_sq_from_inner_deriv_wrapper_theorem_name(row)
    anchor_wrapper_name = shape_anchor_wrapper_theorem_name(row)
    return f"""theorem {deriv_interval_name}
    (hShapeDerivAnchorLower :
      {shape_deriv_anchor_lower} <=
        centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} {anchor})
    (hShapeDerivAnchorUpper :
      centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} {anchor} <=
        {shape_deriv_anchor_upper})
    (hSecondDerivBound :
      ∀ eta ∈ Set.Icc {a} {b},
        ‖deriv
          (fun t : Real =>
            centeredBSplineImagTransformRealClosedFormDerivClosedForm
              {k} {ell} t) eta‖ <=
            ((1 : Real) / (100 : Real))) :
    (∀ eta ∈ Set.Icc {a} {b},
      {shape_deriv_lower} <=
        centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} eta) ∧
      (∀ eta ∈ Set.Icc {a} {b},
        centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} eta <=
        {shape_deriv_upper}) := by
  exact
    value_interval_bounds_on_Icc_of_anchor_deriv_bound
      (f := fun t : Real =>
        centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} t)
      (a := {a})
      (b := {b})
      (anchor := {anchor})
      (slope := ((1 : Real) / (100 : Real)))
      (etaRadius := {eta_radius})
      (anchorLower := {shape_deriv_anchor_lower})
      (anchorUpper := {shape_deriv_anchor_upper})
      (by norm_num)
      (by
        intro eta heta
        exact primaryK11ShapeDerivClosedForm_differentiableAt_of_pos
          (lt_of_lt_of_le (by norm_num) heta.1))
      hSecondDerivBound
      (by
        intro eta heta
        exact abs_le.mpr ⟨by nlinarith [heta.1], by nlinarith [heta.2]⟩)
      (by norm_num)
      hShapeDerivAnchorLower hShapeDerivAnchorUpper
      (by norm_num)
      (by norm_num)

theorem {value_name}
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc {a} {b},
        {shape_deriv_lower} <=
          centeredBSplineImagTransformRealClosedFormDerivClosedForm {k} {ell} eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc {a} {b},
        centeredBSplineImagTransformRealClosedFormDerivClosedForm {k} {ell} eta <=
          {shape_deriv_upper})
    (hShapeAnchorValueLower :
      {shape_anchor_value_lower} <=
        centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor})
    (hShapeAnchorValueUpper :
      centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor} <=
        {shape_anchor_value_upper}) :
    (∀ eta ∈ Set.Icc {a} {b},
        {shape_value_lower} <=
          centeredBSplineImagTransformRealClosedForm {k} {ell} eta) ∧
      (∀ eta ∈ Set.Icc {a} {b},
        centeredBSplineImagTransformRealClosedForm {k} {ell} eta <=
          {shape_value_upper}) := by
  have hDerivBound :
      ∀ eta ∈ Set.Icc {a} {b},
        ‖deriv
          (fun t : Real =>
            centeredBSplineImagTransformRealClosedForm
              {k} {ell} t) eta‖ <=
            ((1 : Real) / (100 : Real)) := by
    intro eta heta
    rw [centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm]
    exact
      le_trans
        (norm_le_intervalAutoAbsBound_of_interval_bounds
          (hShapeDerivLower eta heta) (hShapeDerivUpper eta heta))
        (by norm_num [intervalAutoAbsBound])
  exact
    value_interval_bounds_on_Icc_of_anchor_deriv_bound
      (f := fun t : Real =>
        centeredBSplineImagTransformRealClosedForm
          {k} {ell} t)
      (a := {a})
      (b := {b})
      (anchor := {anchor})
      (slope := ((1 : Real) / (100 : Real)))
      (etaRadius := {eta_radius})
      (anchorLower := {shape_anchor_value_lower})
      (anchorUpper := {shape_anchor_value_upper})
      (by norm_num)
      (by
        intro eta _
        unfold centeredBSplineImagTransformRealClosedForm
        fun_prop)
      hDerivBound
      (by
        intro eta heta
        exact abs_le.mpr ⟨by nlinarith [heta.1], by nlinarith [heta.2]⟩)
      (by norm_num)
      hShapeAnchorValueLower hShapeAnchorValueUpper
      (by norm_num)
      (by norm_num)

theorem {sq_deriv_anchor_name}
    (hShapeDerivLower :
      ∀ eta ∈ Set.Icc {a} {b},
        {shape_deriv_lower} <=
          centeredBSplineImagTransformRealClosedFormDerivClosedForm {k} {ell} eta)
    (hShapeDerivUpper :
      ∀ eta ∈ Set.Icc {a} {b},
        centeredBSplineImagTransformRealClosedFormDerivClosedForm {k} {ell} eta <=
          {shape_deriv_upper})
    (hShapeAnchorValueLower :
      {shape_anchor_value_lower} <=
        centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor})
    (hShapeAnchorValueUpper :
      centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor} <=
        {shape_anchor_value_upper}) :
    ShapeSqEndpointBoundsCert
      {k} {ell} {a} {b} {anchor}
      {shape_sq_deriv_lower} {shape_sq_deriv_upper}
      {shape_sq_anchor_lower} {shape_sq_anchor_upper} := by
  have hShapeValue :=
    {value_name}
      hShapeDerivLower hShapeDerivUpper hShapeAnchorValueLower
      hShapeAnchorValueUpper
  exact
    {anchor_wrapper_name}
      hShapeValue.1 hShapeValue.2 hShapeDerivLower hShapeDerivUpper
      hShapeAnchorValueLower hShapeAnchorValueUpper

theorem {sq_second_name}
    (hShapeDerivAnchorLower :
      {shape_deriv_anchor_lower} <=
        centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} {anchor})
    (hShapeDerivAnchorUpper :
      centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} {anchor} <=
        {shape_deriv_anchor_upper})
    (hShapeAnchorValueLower :
      {shape_anchor_value_lower} <=
        centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor})
    (hShapeAnchorValueUpper :
      centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor} <=
        {shape_anchor_value_upper})
    (hSecondDerivBound :
      ∀ eta ∈ Set.Icc {a} {b},
        ‖deriv
          (fun t : Real =>
            centeredBSplineImagTransformRealClosedFormDerivClosedForm
              {k} {ell} t) eta‖ <=
            ((1 : Real) / (100 : Real))) :
    ShapeSqEndpointBoundsCert
      {k} {ell} {a} {b} {anchor}
      {shape_sq_deriv_lower} {shape_sq_deriv_upper}
      {shape_sq_anchor_lower} {shape_sq_anchor_upper} := by
  have hShapeDeriv :=
    {deriv_interval_name}
      hShapeDerivAnchorLower hShapeDerivAnchorUpper hSecondDerivBound
  exact
    {sq_deriv_anchor_name}
      hShapeDeriv.1 hShapeDeriv.2 hShapeAnchorValueLower
      hShapeAnchorValueUpper

theorem {sq_inner_name}
    {{innerDerivLower innerDerivUpper : Real}}
    (hShapeDerivAnchorLower :
      {shape_deriv_anchor_lower} <=
        centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} {anchor})
    (hShapeDerivAnchorUpper :
      centeredBSplineImagTransformRealClosedFormDerivClosedForm
          {k} {ell} {anchor} <=
        {shape_deriv_anchor_upper})
    (hShapeAnchorValueLower :
      {shape_anchor_value_lower} <=
        centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor})
    (hShapeAnchorValueUpper :
      centeredBSplineImagTransformRealClosedForm {k} {ell} {anchor} <=
        {shape_anchor_value_upper})
    (hInnerDerivLower :
      ∀ eta ∈ Set.Icc {a} {b},
        innerDerivLower <= deriv primaryK11ShapeDerivInner eta)
    (hInnerDerivUpper :
      ∀ eta ∈ Set.Icc {a} {b},
        deriv primaryK11ShapeDerivInner eta <= innerDerivUpper)
    (hAbsBound :
      intervalAutoAbsBound innerDerivLower innerDerivUpper <=
        ((1 : Real) / 100)) :
    ShapeSqEndpointBoundsCert
      {k} {ell} {a} {b} {anchor}
      {shape_sq_deriv_lower} {shape_sq_deriv_upper}
      {shape_sq_anchor_lower} {shape_sq_anchor_upper} := by
  exact
    {sq_second_name}
      hShapeDerivAnchorLower hShapeDerivAnchorUpper
      hShapeAnchorValueLower hShapeAnchorValueUpper
      (primaryFiniteRow0Parent0Split100Sub0ShapeDerivClosedForm_second_deriv_bound_of_inner_deriv_interval_bounds
        hInnerDerivLower hInnerDerivUpper hAbsBound)
"""


def render_first_shape_sq_endpoint_bounds_closed_theorem(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    theorem = shape_sq_endpoint_bounds_closed_theorem_name(row)
    inner_name = shape_sq_from_inner_deriv_wrapper_theorem_name(row)
    return f"""theorem {theorem} :
    ShapeSqEndpointBoundsCert
      {k} {ell} {a} {b} {anchor}
      {shape_sq_deriv_lower} {shape_sq_deriv_upper}
      {shape_sq_anchor_lower} {shape_sq_anchor_upper} := by
  exact
    {inner_name}
      primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated.1
      primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated.2
      primaryFiniteRow0Parent0Split100Sub0ShapeAnchorValueBounds_generated.1
      primaryFiniteRow0Parent0Split100Sub0ShapeAnchorValueBounds_generated.2
      primaryFiniteRow0Parent0Split100Sub0ShapeDerivInner_deriv_interval_bounds_cubic.1
      primaryFiniteRow0Parent0Split100Sub0ShapeDerivInner_deriv_interval_bounds_cubic.2
      (by norm_num [intervalAutoAbsBound])
"""


def render_interval_def(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_deriv_lower = lean_rat(terms["omegaDerivLower"])
    omega_deriv_upper = lean_rat(terms["omegaDerivUpper"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    return f"""def {interval_theorem_name(row)}
    (hOmega :
      Step22OmegaClosedFormEndpointBoundsCert
        {a} {b} {anchor}
        {omega_deriv_lower} {omega_deriv_upper}
        {omega_anchor_lower} {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds_rational
      hOmega hShape {theorem_name(row)}
"""


def render_first_interval_from_direct_anchor_pair_shape(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_deriv_lower = lean_rat(terms["omegaDerivLower"])
    omega_deriv_upper = lean_rat(terms["omegaDerivUpper"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_direct_anchor_pair_wrapper_theorem_name(row)
    interval_name = interval_theorem_name(row)
    theorem = interval_from_direct_anchor_pair_shape_theorem_name(row)
    return f"""def {theorem}
    (hAnchor :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} <= {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact {interval_name} ({pair_name} hAnchor) hShape
"""


def render_first_interval_from_re_series_interval_shape(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_re_series_anchor_pair_theorem_name(row)
    direct_interval_name = interval_from_direct_anchor_pair_shape_theorem_name(row)
    theorem = interval_from_re_series_interval_shape_theorem_name(row)
    return f"""def {theorem}
    (anchorN : Nat)
    (anchorConstLower anchorConstUpper anchorPrefixLower anchorPrefixUpper
      anchorTailLower anchorTailUpper : Real)
    (hAnchorConstLower :
      anchorConstLower <= -Real.eulerMascheroniConstant - Real.log Real.pi)
    (hAnchorConstUpper :
      -Real.eulerMascheroniConstant - Real.log Real.pi <= anchorConstUpper)
    (hAnchorPrefixLower :
      anchorPrefixLower <=
        (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm {anchor}))
    (hAnchorPrefixUpper :
      (Finset.range anchorN).sum (step22OmegaArchWeightReSeriesTerm {anchor}) <=
        anchorPrefixUpper)
    (hAnchorTailLower :
      anchorTailLower <=
        ∑' n : Nat, step22OmegaArchWeightReSeriesTerm {anchor} (n + anchorN))
    (hAnchorTailUpper :
      (∑' n : Nat, step22OmegaArchWeightReSeriesTerm {anchor} (n + anchorN)) <=
        anchorTailUpper)
    (hAnchorLowerFromReSeries :
      {omega_anchor_lower} <=
        anchorConstLower + anchorPrefixLower + anchorTailLower)
    (hAnchorUpperFromReSeries :
      anchorConstUpper + anchorPrefixUpper + anchorTailUpper <=
        {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    {direct_interval_name}
      ({pair_name}
        anchorN anchorConstLower anchorConstUpper anchorPrefixLower
        anchorPrefixUpper anchorTailLower anchorTailUpper
        hAnchorConstLower hAnchorConstUpper hAnchorPrefixLower
        hAnchorPrefixUpper hAnchorTailLower hAnchorTailUpper
        hAnchorLowerFromReSeries hAnchorUpperFromReSeries)
      hShape
"""


def render_first_interval_from_re_series_n16_prefix_shape(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    prefix = lean_rat(omega_re_series_prefix_fraction(terms["anchor"], 16))
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_re_series_n16_anchor_pair_theorem_name(row)
    direct_interval_name = interval_from_direct_anchor_pair_shape_theorem_name(row)
    theorem = interval_from_re_series_n16_prefix_shape_theorem_name(row)
    return f"""def {theorem}
    (anchorConstLower anchorConstUpper anchorTailLower anchorTailUpper : Real)
    (hAnchorConstLower :
      anchorConstLower <= -Real.eulerMascheroniConstant - Real.log Real.pi)
    (hAnchorConstUpper :
      -Real.eulerMascheroniConstant - Real.log Real.pi <= anchorConstUpper)
    (hAnchorTailLower :
      anchorTailLower <=
        ∑' n : Nat, step22OmegaArchWeightReSeriesTerm {anchor} (n + 16))
    (hAnchorTailUpper :
      (∑' n : Nat, step22OmegaArchWeightReSeriesTerm {anchor} (n + 16)) <=
        anchorTailUpper)
    (hAnchorLowerFromN16ReSeries :
      {omega_anchor_lower} <=
        anchorConstLower
          + {prefix}
          + anchorTailLower)
    (hAnchorUpperFromN16ReSeries :
      anchorConstUpper
          + {prefix}
          + anchorTailUpper <=
        {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    {direct_interval_name}
      ({pair_name}
        anchorConstLower anchorConstUpper anchorTailLower anchorTailUpper
        hAnchorConstLower hAnchorConstUpper hAnchorTailLower hAnchorTailUpper
        hAnchorLowerFromN16ReSeries hAnchorUpperFromN16ReSeries)
      hShape
"""


def render_first_interval_from_shifted_stieltjes_shape(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_shifted_stieltjes_anchor_pair_theorem_name(row)
    direct_interval_name = interval_from_direct_anchor_pair_shape_theorem_name(row)
    theorem = interval_from_shifted_stieltjes_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat)
    (hShiftLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedStieltjesMain
            {anchor} shift -
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedStieltjesErr
            {anchor} shift)
    (hShiftUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedStieltjesMain
            {anchor} shift +
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedStieltjesErr
            {anchor} shift <=
        {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    {direct_interval_name}
      ({pair_name} shift hShiftLower hShiftUpper)
      hShape
"""


def render_first_interval_from_main_error_shape(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_main_error_anchor_pair_theorem_name(row)
    direct_interval_name = interval_from_direct_anchor_pair_shape_theorem_name(row)
    theorem = interval_from_main_error_shape_theorem_name(row)
    return f"""def {theorem}
    (main err : Real)
    (hAbs :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} - main| <= err)
    (hMainLower :
      {omega_anchor_lower} <= main - err)
    (hMainUpper :
      main + err <= {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    {direct_interval_name}
      ({pair_name} main err hAbs hMainLower hMainUpper)
      hShape
"""


def render_first_interval_from_shifted_digamma_main_error_shape(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_shifted_digamma_main_error_anchor_pair_theorem_name(row)
    direct_interval_name = interval_from_direct_anchor_pair_shape_theorem_name(row)
    theorem = interval_from_shifted_digamma_main_error_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain err : Real)
    (hShiftedAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re - psiMain| <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain + err <=
        {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    {direct_interval_name}
      ({pair_name} shift psiMain err hShiftedAbs hMainLower hMainUpper)
      hShape
"""


def render_first_interval_from_shifted_digamma_complex_main_error_shape(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_shifted_digamma_complex_main_error_anchor_pair_theorem_name(row)
    direct_interval_name = interval_from_direct_anchor_pair_shape_theorem_name(row)
    theorem = interval_from_shifted_digamma_complex_main_error_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex) (err : Real)
    (hShiftedAbs :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift) - psiMain‖ <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    {direct_interval_name}
      ({pair_name} shift psiMain err hShiftedAbs hMainLower hMainUpper)
      hShape
"""


def render_first_interval_from_shifted_digamma_rect_error_shape(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_shifted_digamma_rect_error_anchor_pair_theorem_name(row)
    direct_interval_name = interval_from_direct_anchor_pair_shape_theorem_name(row)
    theorem = interval_from_shifted_digamma_rect_error_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex) (errRe errIm err : Real)
    (hReAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re - psiMain.re| <= errRe)
    (hImAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im - psiMain.im| <= errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    {direct_interval_name}
      ({pair_name}
        shift psiMain errRe errIm err hReAbs hImAbs hErr hMainLower hMainUpper)
      hShape
"""


def render_first_interval_from_shifted_digamma_rect_interval_shape(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    k = int(terms["k"])
    ell = lean_rat(terms["ell"])
    a = lean_rat(terms["a"])
    b = lean_rat(terms["b"])
    anchor = lean_rat(terms["anchor"])
    eta_radius = lean_rat(terms["etaRadius"])
    omega_center = lean_rat(terms["omegaCenter"])
    omega_radius = lean_rat(terms["omegaRadius"])
    shape_center = lean_rat(terms["shapeSqCenter"])
    shape_radius = lean_rat(terms["shapeSqRadius"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_sq_deriv_lower = lean_rat(terms["shapeSqDerivLower"])
    shape_sq_deriv_upper = lean_rat(terms["shapeSqDerivUpper"])
    shape_sq_anchor_lower = lean_rat(terms["shapeSqAnchorLower"])
    shape_sq_anchor_upper = lean_rat(terms["shapeSqAnchorUpper"])
    omega_lower = lean_rat(terms["omegaLower"])
    omega_upper = lean_rat(terms["omegaUpper"])
    shape_sq_lower = lean_rat(terms["shapeSqLower"])
    shape_sq_upper = lean_rat(terms["shapeSqUpper"])
    pair_name = omega_shifted_digamma_rect_interval_anchor_pair_theorem_name(row)
    direct_interval_name = interval_from_direct_anchor_pair_shape_theorem_name(row)
    theorem = interval_from_shifted_digamma_rect_interval_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (hReLower :
      reLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re)
    (hReUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re <= reUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImLower :
      imLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im)
    (hImUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im <= imUpper)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper})
    (hShape :
      ShapeSqEndpointBoundsCert
        {k} {ell} {a} {b} {anchor}
        {shape_sq_deriv_lower} {shape_sq_deriv_upper}
        {shape_sq_anchor_lower} {shape_sq_anchor_upper}) :
    LocalRawOmegaComponentDirectEndpointIntervalCert
      {k} {ell} {a} {b} {anchor} {eta_radius}
      {omega_lower} {omega_upper} {shape_sq_lower} {shape_sq_upper}
      {omega_center} {omega_radius} {shape_center} {shape_radius} := by
  exact
    {direct_interval_name}
      ({pair_name}
        shift psiMain reLower reUpper imLower imUpper errRe errIm err
        hReLower hReUpper hReCenterLower hReCenterUpper
        hImLower hImUpper hImCenterLower hImCenterUpper hErr
        hMainLower hMainUpper)
      hShape
"""


def render_first_interval_from_main_error(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_name = shape_sq_endpoint_bounds_closed_theorem_name(row)
    theorem = interval_from_main_error_theorem_name(row)
    shape_theorem = interval_from_main_error_shape_theorem_name(row)
    return f"""def {theorem}
    (main err : Real)
    (hAbs :
      |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          {anchor} - main| <= err)
    (hMainLower :
      {omega_anchor_lower} <= main - err)
    (hMainUpper :
      main + err <= {omega_anchor_upper}) :=
  {shape_theorem}
    main err hAbs hMainLower hMainUpper
    {shape_name}
"""


def render_first_interval_from_shifted_digamma_main_error(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_name = shape_sq_endpoint_bounds_closed_theorem_name(row)
    theorem = interval_from_shifted_digamma_main_error_theorem_name(row)
    shape_theorem = interval_from_shifted_digamma_main_error_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain err : Real)
    (hShiftedAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re - psiMain| <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain + err <=
        {omega_anchor_upper}) :=
  {shape_theorem}
    shift psiMain err hShiftedAbs hMainLower hMainUpper
    {shape_name}
"""


def render_first_interval_from_shifted_digamma_complex_main_error(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_name = shape_sq_endpoint_bounds_closed_theorem_name(row)
    theorem = interval_from_shifted_digamma_complex_main_error_theorem_name(row)
    shape_theorem = interval_from_shifted_digamma_complex_main_error_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex) (err : Real)
    (hShiftedAbs :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift) - psiMain‖ <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :=
  {shape_theorem}
    shift psiMain err hShiftedAbs hMainLower hMainUpper
    {shape_name}
"""


def render_first_interval_from_shifted_digamma_rect_error(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_name = shape_sq_endpoint_bounds_closed_theorem_name(row)
    theorem = interval_from_shifted_digamma_rect_error_theorem_name(row)
    shape_theorem = interval_from_shifted_digamma_rect_error_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex) (errRe errIm err : Real)
    (hReAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re - psiMain.re| <= errRe)
    (hImAbs :
      |(Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im - psiMain.im| <= errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :=
  {shape_theorem}
    shift psiMain errRe errIm err hReAbs hImAbs hErr hMainLower hMainUpper
    {shape_name}
"""


def render_first_interval_from_shifted_digamma_rect_interval(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    shape_name = shape_sq_endpoint_bounds_closed_theorem_name(row)
    theorem = interval_from_shifted_digamma_rect_interval_theorem_name(row)
    shape_theorem = interval_from_shifted_digamma_rect_interval_shape_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (hReLower :
      reLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re)
    (hReUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).re <= reUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImLower :
      imLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im)
    (hImUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift)).im <= imUpper)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :=
  {shape_theorem}
    shift psiMain reLower reUpper imLower imUpper errRe errIm err
    hReLower hReUpper hReCenterLower hReCenterUpper
    hImLower hImUpper hImCenterLower hImCenterUpper hErr
    hMainLower hMainUpper
    {shape_name}
"""


def render_first_shifted_digamma_rect_shift16_n16_invsum_bounds(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    theorem = shifted_digamma_rect_shift16_n16_invsum_bounds_theorem_name(row)
    re_lower = lean_rat(SHIFT16_N16_INVSUM_RE_LOWER)
    re_upper = lean_rat(SHIFT16_N16_INVSUM_RE_UPPER)
    im_lower = lean_rat(SHIFT16_N16_INVSUM_IM_LOWER)
    im_upper = lean_rat(SHIFT16_N16_INVSUM_IM_UPPER)
    inv_sum = f"""((Finset.range 16).sum (fun m : Nat =>
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (m : Complex))⁻¹))"""
    return f"""theorem {theorem} :
    {re_lower} <= {inv_sum}.re ∧
      {inv_sum}.re <= {re_upper} ∧
      {im_lower} <= {inv_sum}.im ∧
      {inv_sum}.im <= {im_upper} := by
  constructor
  · norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg,
      Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  constructor
  · norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg,
      Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  constructor
  · norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg,
      Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  · norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg,
      Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
"""


def render_first_shifted_digamma_rect_shift16_n16_point_identities(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    eq_theorem = shifted_digamma_rect_shift16_n16_point_eq_theorem_name(row)
    re_theorem = shifted_digamma_rect_shift16_n16_point_re_theorem_name(row)
    im_theorem = shifted_digamma_rect_shift16_n16_point_im_theorem_name(row)
    z = f"""(Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
        {anchor} 16 + (16 : Complex))"""
    return f"""theorem {eq_theorem} :
    {z} =
      ((129 : Real) / (4 : Real) : Complex) +
        Complex.I * (((1 : Real) / (40 : Real) : Complex)) := by
  apply Complex.ext
  · norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg]
  · norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg]

theorem {re_theorem} :
    {z}.re = ((129 : Real) / (4 : Real)) := by
  norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg]

theorem {im_theorem} :
    {z}.im = ((1 : Real) / (40 : Real)) := by
  norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg]
"""


def render_first_interval_from_shifted_digamma_rect_shift16_n16(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    rect_name = interval_from_shifted_digamma_rect_interval_theorem_name(row)
    theorem = interval_from_shifted_digamma_rect_shift16_n16_theorem_name(row)
    return f"""def {theorem}
    (psiMain : Complex)
    (reLower reUpper imLower imUpper shiftedReLower shiftedReUpper
      shiftedImLower shiftedImUpper invReLower invReUpper invImLower
      invImUpper errRe errIm err : Real)
    (hShiftReLower :
      shiftedReLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex))).re)
    (hShiftReUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex))).re <= shiftedReUpper)
    (hShiftImLower :
      shiftedImLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex))).im)
    (hShiftImUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex))).im <= shiftedImUpper)
    (hInvReLower :
      invReLower <=
        ((Finset.range 16).sum (fun m : Nat =>
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (m : Complex))⁻¹)).re)
    (hInvReUpper :
      ((Finset.range 16).sum (fun m : Nat =>
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (m : Complex))⁻¹)).re <= invReUpper)
    (hInvImLower :
      invImLower <=
        ((Finset.range 16).sum (fun m : Nat =>
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (m : Complex))⁻¹)).im)
    (hInvImUpper :
      ((Finset.range 16).sum (fun m : Nat =>
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (m : Complex))⁻¹)).im <= invImUpper)
    (hRectReLower : reLower <= shiftedReLower - invReUpper)
    (hRectReUpper : shiftedReUpper - invReLower <= reUpper)
    (hRectImLower : imLower <= shiftedImLower - invImUpper)
    (hRectImUpper : shiftedImUpper - invImLower <= imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 psiMain.re + err <=
        {omega_anchor_upper}) := by
  let hRect :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigamma_interval_of_shift16_rect
      {anchor} 16
      reLower reUpper imLower imUpper shiftedReLower shiftedReUpper
      shiftedImLower shiftedImUpper invReLower invReUpper invImLower
      invImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper
      hInvReLower hInvReUpper hInvImLower hInvImUpper
      hRectReLower hRectReUpper hRectImLower hRectImUpper
  exact
    {rect_name}
      16 psiMain reLower reUpper imLower imUpper errRe errIm err
      hRect.1 hRect.2.1 hReCenterLower hReCenterUpper
      hRect.2.2.1 hRect.2.2.2 hImCenterLower hImCenterUpper
      hErr hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_rect_shift16_n16_invsum(row: dict[str, Any]) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_rect_shift16_n16_invsum_theorem_name(row)
    base_theorem = interval_from_shifted_digamma_rect_shift16_n16_theorem_name(row)
    inv_theorem = shifted_digamma_rect_shift16_n16_invsum_bounds_theorem_name(row)
    inv_re_lower = lean_rat(SHIFT16_N16_INVSUM_RE_LOWER)
    inv_re_upper = lean_rat(SHIFT16_N16_INVSUM_RE_UPPER)
    inv_im_lower = lean_rat(SHIFT16_N16_INVSUM_IM_LOWER)
    inv_im_upper = lean_rat(SHIFT16_N16_INVSUM_IM_UPPER)
    return f"""def {theorem}
    (psiMain : Complex)
    (reLower reUpper imLower imUpper shiftedReLower shiftedReUpper
      shiftedImLower shiftedImUpper errRe errIm err : Real)
    (hShiftReLower :
      shiftedReLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex))).re)
    (hShiftReUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex))).re <= shiftedReUpper)
    (hShiftImLower :
      shiftedImLower <=
        (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex))).im)
    (hShiftImUpper :
      (Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex))).im <= shiftedImUpper)
    (hRectReLower : reLower <= shiftedReLower - {inv_re_upper})
    (hRectReUpper : shiftedReUpper - {inv_re_lower} <= reUpper)
    (hRectImLower : imLower <= shiftedImLower - {inv_im_upper})
    (hRectImUpper : shiftedImUpper - {inv_im_lower} <= imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 psiMain.re + err <=
        {omega_anchor_upper}) := by
  exact
    {base_theorem}
      psiMain reLower reUpper imLower imUpper shiftedReLower shiftedReUpper
      shiftedImLower shiftedImUpper {inv_re_lower} {inv_re_upper}
      {inv_im_lower} {inv_im_upper} errRe errIm err
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper
      {inv_theorem}.1 {inv_theorem}.2.1 {inv_theorem}.2.2.1
      {inv_theorem}.2.2.2 hRectReLower hRectReUpper hRectImLower
      hRectImUpper hReCenterLower hReCenterUpper hImCenterLower
      hImCenterUpper hErr hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_rect_shift16_n16_complex_main_error_invsum(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = (
        interval_from_shifted_digamma_rect_shift16_n16_complex_main_error_invsum_theorem_name(
            row
        )
    )
    base_theorem = interval_from_shifted_digamma_rect_shift16_n16_invsum_theorem_name(row)
    inv_re_lower = lean_rat(SHIFT16_N16_INVSUM_RE_LOWER)
    inv_re_upper = lean_rat(SHIFT16_N16_INVSUM_RE_UPPER)
    inv_im_lower = lean_rat(SHIFT16_N16_INVSUM_IM_LOWER)
    inv_im_upper = lean_rat(SHIFT16_N16_INVSUM_IM_UPPER)
    return f"""def {theorem}
    (psiMain shiftedPsiMain : Complex)
    (reLower reUpper imLower imUpper shiftedErr errRe errIm err : Real)
    (hShiftAbs :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex)) -
        shiftedPsiMain‖ <= shiftedErr)
    (hRectReLower :
      reLower <= (shiftedPsiMain.re - shiftedErr) - {inv_re_upper})
    (hRectReUpper :
      (shiftedPsiMain.re + shiftedErr) - {inv_re_lower} <= reUpper)
    (hRectImLower :
      imLower <= (shiftedPsiMain.im - shiftedErr) - {inv_im_upper})
    (hRectImUpper :
      (shiftedPsiMain.im + shiftedErr) - {inv_im_lower} <= imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 psiMain.re + err <=
        {omega_anchor_upper}) := by
  let hShiftRect :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_add_sixteen_rect_interval_of_complex_main_error
      {anchor} 16 shiftedPsiMain
      (shiftedPsiMain.re - shiftedErr) (shiftedPsiMain.re + shiftedErr)
      (shiftedPsiMain.im - shiftedErr) (shiftedPsiMain.im + shiftedErr)
      shiftedErr hShiftAbs le_rfl le_rfl le_rfl le_rfl
  exact
    {base_theorem}
      psiMain reLower reUpper imLower imUpper
      (shiftedPsiMain.re - shiftedErr) (shiftedPsiMain.re + shiftedErr)
      (shiftedPsiMain.im - shiftedErr) (shiftedPsiMain.im + shiftedErr)
      errRe errIm err
      hShiftRect.1 hShiftRect.2.1 hShiftRect.2.2.1 hShiftRect.2.2.2
      hRectReLower hRectReUpper hRectImLower hRectImUpper
      hReCenterLower hReCenterUpper hImCenterLower hImCenterUpper
      hErr hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_rect_shift16_n16_centered_complex_main_error_invsum(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = (
        interval_from_shifted_digamma_rect_shift16_n16_centered_complex_main_error_invsum_theorem_name(
            row
        )
    )
    base_theorem = (
        interval_from_shifted_digamma_rect_shift16_n16_complex_main_error_invsum_theorem_name(
            row
        )
    )
    inv_re_center_frac = (
        SHIFT16_N16_INVSUM_RE_LOWER + SHIFT16_N16_INVSUM_RE_UPPER
    ) / 2
    inv_re_radius_frac = (
        SHIFT16_N16_INVSUM_RE_UPPER - SHIFT16_N16_INVSUM_RE_LOWER
    ) / 2
    inv_im_center_frac = (
        SHIFT16_N16_INVSUM_IM_LOWER + SHIFT16_N16_INVSUM_IM_UPPER
    ) / 2
    inv_im_radius_frac = (
        SHIFT16_N16_INVSUM_IM_UPPER - SHIFT16_N16_INVSUM_IM_LOWER
    ) / 2
    inv_re_center = lean_rat(inv_re_center_frac)
    inv_re_radius = lean_rat(inv_re_radius_frac)
    inv_im_center = lean_rat(inv_im_center_frac)
    inv_im_radius = lean_rat(inv_im_radius_frac)
    return f"""def {theorem}
    (shiftedPsiMain : Complex) (shiftedErr : Real)
    (hShiftAbs :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex)) -
        shiftedPsiMain‖ <= shiftedErr)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 (shiftedPsiMain.re - {inv_re_center}) -
          ((shiftedErr + {inv_re_radius}) + (shiftedErr + {inv_im_radius})))
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 (shiftedPsiMain.re - {inv_re_center}) +
          ((shiftedErr + {inv_re_radius}) + (shiftedErr + {inv_im_radius})) <=
        {omega_anchor_upper}) := by
  let psiMain : Complex :=
    ((shiftedPsiMain.re - {inv_re_center} : Real) : Complex) +
      Complex.I * ((shiftedPsiMain.im - {inv_im_center} : Real) : Complex)
  exact
    {base_theorem}
      psiMain shiftedPsiMain
      (psiMain.re - (shiftedErr + {inv_re_radius}))
      (psiMain.re + (shiftedErr + {inv_re_radius}))
      (psiMain.im - (shiftedErr + {inv_im_radius}))
      (psiMain.im + (shiftedErr + {inv_im_radius}))
      shiftedErr
      (shiftedErr + {inv_re_radius})
      (shiftedErr + {inv_im_radius})
      ((shiftedErr + {inv_re_radius}) + (shiftedErr + {inv_im_radius}))
      hShiftAbs
      (by
        simp [psiMain]
        ring_nf
        exact le_rfl)
      (by
        simp [psiMain]
        ring_nf
        exact le_rfl)
      (by
        simp [psiMain]
        ring_nf
        exact le_rfl)
      (by
        simp [psiMain]
        ring_nf
        exact le_rfl)
      le_rfl le_rfl le_rfl le_rfl le_rfl
      (by
        simpa [psiMain] using hMainLower)
      (by
        simpa [psiMain] using hMainUpper)
"""


def render_first_interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = (
        interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_theorem_name(
            row
        )
    )
    inv_bounds_theorem = shifted_digamma_rect_shift16_n16_invsum_bounds_theorem_name(row)
    main_error_theorem = interval_from_main_error_theorem_name(row)
    inv_re_center_frac = (
        SHIFT16_N16_INVSUM_RE_LOWER + SHIFT16_N16_INVSUM_RE_UPPER
    ) / 2
    inv_re_radius_frac = (
        SHIFT16_N16_INVSUM_RE_UPPER - SHIFT16_N16_INVSUM_RE_LOWER
    ) / 2
    inv_re_center = lean_rat(inv_re_center_frac)
    inv_re_radius = lean_rat(inv_re_radius_frac)
    return f"""def {theorem}
    (shiftedPsiMain : Complex) (shiftedErr : Real)
    (hShiftAbs :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex)) -
        shiftedPsiMain‖ <= shiftedErr)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 (shiftedPsiMain.re - {inv_re_center}) -
          (shiftedErr + {inv_re_radius}))
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} 16 (shiftedPsiMain.re - {inv_re_center}) +
          (shiftedErr + {inv_re_radius}) <=
        {omega_anchor_upper}) := by
  have hInvAbs :
      |((Finset.range 16).sum (fun m : Nat =>
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (m : Complex))⁻¹)).re - {inv_re_center}| <=
        {inv_re_radius} := by
    have hLo := {inv_bounds_theorem}.1
    have hHi := {inv_bounds_theorem}.2.1
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hAbs :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_abs_sub_shifted_digamma_add_sixteen_invsum_recentered_complex_main
      {anchor} 16 shiftedPsiMain shiftedErr {inv_re_center} {inv_re_radius}
      hShiftAbs hInvAbs
  exact
    {main_error_theorem}
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
        {anchor} 16 (shiftedPsiMain.re - {inv_re_center}))
      (shiftedErr + {inv_re_radius})
      hAbs hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_log_pi_interval(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = (
        interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_log_pi_interval_theorem_name(
            row
        )
    )
    base_theorem = (
        interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_theorem_name(
            row
        )
    )
    inv_re_center_frac = (
        SHIFT16_N16_INVSUM_RE_LOWER + SHIFT16_N16_INVSUM_RE_UPPER
    ) / 2
    inv_re_radius_frac = (
        SHIFT16_N16_INVSUM_RE_UPPER - SHIFT16_N16_INVSUM_RE_LOWER
    ) / 2
    inv_re_center = lean_rat(inv_re_center_frac)
    inv_re_radius = lean_rat(inv_re_radius_frac)
    return f"""def {theorem}
    (shiftedPsiMain : Complex) (shiftedErr logPiLower logPiUpper : Real)
    (hShiftAbs :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex)) -
        shiftedPsiMain‖ <= shiftedErr)
    (hLogPiLower : logPiLower <= Real.log Real.pi)
    (hLogPiUpper : Real.log Real.pi <= logPiUpper)
    (hMainLower :
      {omega_anchor_lower} <=
        (shiftedPsiMain.re - {inv_re_center}) - logPiUpper -
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftCorrection
            {anchor} 16).re -
          (shiftedErr + {inv_re_radius}))
    (hMainUpper :
      (shiftedPsiMain.re - {inv_re_center}) - logPiLower -
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftCorrection
            {anchor} 16).re +
          (shiftedErr + {inv_re_radius}) <=
        {omega_anchor_upper}) := by
  have hMainBounds :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain_bounds_of_log_pi_interval
      {anchor} 16 (shiftedPsiMain.re - {inv_re_center})
      (shiftedErr + {inv_re_radius})
      {omega_anchor_lower} {omega_anchor_upper} logPiLower logPiUpper
      hLogPiLower hLogPiUpper hMainLower hMainUpper
  exact
    {base_theorem}
      shiftedPsiMain shiftedErr hShiftAbs hMainBounds.1 hMainBounds.2
"""


def render_first_interval_from_shifted_digamma_add16_fixed_complex_main_error_log_pi_interval(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    theorem = (
        interval_from_shifted_digamma_add16_fixed_complex_main_error_log_pi_interval_theorem_name(
            row
        )
    )
    base_theorem = (
        interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_log_pi_interval_theorem_name(
            row
        )
    )
    psi_re = lean_rat(SHIFT16_ADD16_FIXED_PSI_RE_CENTER)
    psi_im = lean_rat(SHIFT16_ADD16_FIXED_PSI_IM_CENTER)
    shifted_err = lean_rat(SHIFT16_ADD16_FIXED_SHIFTED_ERR)
    log_pi_lower = lean_rat(SHIFT16_ADD16_FIXED_LOG_PI_LOWER)
    log_pi_upper = lean_rat(SHIFT16_ADD16_FIXED_LOG_PI_UPPER)
    return f"""def {theorem}
    (hShiftAbs :
      ‖Q3.digamma
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} 16 + (16 : Complex)) -
        ((({psi_re} : Real) : Complex) + Complex.I * ((({psi_im} : Real) : Complex)))‖ <=
          {shifted_err})
    (hLogPiLower : {log_pi_lower} <= Real.log Real.pi)
    (hLogPiUpper : Real.log Real.pi <= {log_pi_upper}) := by
  exact
    {base_theorem}
      ((({psi_re} : Real) : Complex) + Complex.I * ((({psi_im} : Real) : Complex)))
      {shifted_err} {log_pi_lower} {log_pi_upper}
      hShiftAbs hLogPiLower hLogPiUpper
      (by
        norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftCorrection,
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg,
          Complex.inv_re, Complex.inv_im, Complex.normSq_apply])
      (by
        norm_num [Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftCorrection,
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg,
          Complex.inv_re, Complex.inv_im, Complex.normSq_apply])
"""


def render_first_interval_from_shifted_digamma_series_prefix_tail_interval(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_prefix_tail_interval_theorem_name(row)
    rect_name = interval_from_shifted_digamma_rect_interval_theorem_name(row)
    return f"""def {theorem}
    (shift N : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (gammaLower gammaUpper rePrefixLower rePrefixUpper reTailLower reTailUpper
      imPrefixLower imPrefixUpper imTailLower imTailUpper : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re))
    (hRePrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re) <=
        rePrefixUpper)
    (hReTailLower :
      reTailLower <=
        ∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + N : Nat) : Complex))).re)
    (hReTailUpper :
      (∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + N : Nat) : Complex))).re) <=
        reTailUpper)
    (hReLowerFinal :
      reLower <= -gammaUpper + rePrefixLower + reTailLower)
    (hReUpperFinal :
      -gammaLower + rePrefixUpper + reTailUpper <= reUpper)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im))
    (hImPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im) <=
        imPrefixUpper)
    (hImTailLower :
      imTailLower <=
        ∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + N : Nat) : Complex))).im)
    (hImTailUpper :
      (∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + N : Nat) : Complex))).im) <=
        imTailUpper)
    (hImLowerFinal : imLower <= imPrefixLower + imTailLower)
    (hImUpperFinal : imPrefixUpper + imTailUpper <= imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :=
  let hRe :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_re_interval_of_series_prefix_tail_interval
      {anchor} shift N reLower reUpper gammaLower
      gammaUpper rePrefixLower rePrefixUpper reTailLower reTailUpper
      hGammaLower hGammaUpper hRePrefixLower hRePrefixUpper hReTailLower
      hReTailUpper hReLowerFinal hReUpperFinal
  let hIm :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_im_interval_of_series_prefix_tail_interval
      {anchor} shift N imLower imUpper imPrefixLower
      imPrefixUpper imTailLower imTailUpper hImPrefixLower hImPrefixUpper
      hImTailLower hImTailUpper hImLowerFinal hImUpperFinal
  {rect_name}
    shift psiMain reLower reUpper imLower imUpper errRe errIm err
    hRe.1 hRe.2 hReCenterLower hReCenterUpper
    hIm.1 hIm.2 hImCenterLower hImCenterUpper hErr
    hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_n16_prefix_tail_interval(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_n16_prefix_tail_interval_theorem_name(row)
    generic_name = interval_from_shifted_digamma_series_prefix_tail_interval_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (gammaLower gammaUpper rePrefixLower rePrefixUpper reTailLower reTailUpper
      imPrefixLower imPrefixUpper imTailLower imTailUpper : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re))
    (hRePrefixUpper :
      (Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re) <=
        rePrefixUpper)
    (hReTailLower :
      reTailLower <=
        ∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).re)
    (hReTailUpper :
      (∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).re) <=
        reTailUpper)
    (hReLowerFinal :
      reLower <= -gammaUpper + rePrefixLower + reTailLower)
    (hReUpperFinal :
      -gammaLower + rePrefixUpper + reTailUpper <= reUpper)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im))
    (hImPrefixUpper :
      (Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im) <=
        imPrefixUpper)
    (hImTailLower :
      imTailLower <=
        ∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).im)
    (hImTailUpper :
      (∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).im) <=
        imTailUpper)
    (hImLowerFinal : imLower <= imPrefixLower + imTailLower)
    (hImUpperFinal : imPrefixUpper + imTailUpper <= imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :=
  {generic_name}
    shift 16 psiMain reLower reUpper imLower imUpper errRe errIm err
    gammaLower gammaUpper rePrefixLower rePrefixUpper reTailLower reTailUpper
    imPrefixLower imPrefixUpper imTailLower imTailUpper
    hGammaLower hGammaUpper hRePrefixLower hRePrefixUpper hReTailLower
    hReTailUpper hReLowerFinal hReUpperFinal hImPrefixLower hImPrefixUpper
    hImTailLower hImTailUpper hImLowerFinal hImUpperFinal hReCenterLower
    hReCenterUpper hImCenterLower hImCenterUpper hErr hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_n16_exact_prefix_tail_interval(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_n16_exact_prefix_tail_interval_theorem_name(row)
    n16_name = interval_from_shifted_digamma_series_n16_prefix_tail_interval_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (gammaLower gammaUpper reTailLower reTailUpper
      imTailLower imTailUpper : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hReTailLower :
      reTailLower <=
        ∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).re)
    (hReTailUpper :
      (∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).re) <=
        reTailUpper)
    (hReLowerFinal :
      reLower <= -gammaUpper +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + reTailLower)
    (hReUpperFinal :
      -gammaLower +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + reTailUpper <=
        reUpper)
    (hImTailLower :
      imTailLower <=
        ∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).im)
    (hImTailUpper :
      (∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).im) <=
        imTailUpper)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + imTailLower)
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + imTailUpper <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :=
  {n16_name}
    shift psiMain reLower reUpper imLower imUpper errRe errIm err
    gammaLower gammaUpper
    ((Finset.range 16).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) -
        1 /
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift + (n : Complex))).re))
    ((Finset.range 16).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) -
        1 /
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift + (n : Complex))).re))
    reTailLower reTailUpper
    ((Finset.range 16).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) -
        1 /
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift + (n : Complex))).im))
    ((Finset.range 16).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) -
        1 /
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift + (n : Complex))).im))
    imTailLower imTailUpper hGammaLower hGammaUpper le_rfl le_rfl
    hReTailLower hReTailUpper hReLowerFinal hReUpperFinal le_rfl le_rfl
    hImTailLower hImTailUpper hImLowerFinal hImUpperFinal hReCenterLower
    hReCenterUpper hImCenterLower hImCenterUpper hErr hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_interval(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_interval_theorem_name(row)
    exact_name = interval_from_shifted_digamma_series_n16_exact_prefix_tail_interval_theorem_name(row)
    return f"""def {theorem}
    (shift gammaN : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (reTailLower reTailUpper imTailLower imTailUpper : Real)
    (hReTailLower :
      reTailLower <=
        ∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).re)
    (hReTailUpper :
      (∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).re) <=
        reTailUpper)
    (hReLowerFinal :
      reLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + reTailLower)
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + reTailUpper <=
        reUpper)
    (hImTailLower :
      imTailLower <=
        ∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).im)
    (hImTailUpper :
      (∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).im) <=
        imTailUpper)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + imTailLower)
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + imTailUpper <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) := by
  have hGamma := Q3.eulerMascheroniConstant_interval_of_seq gammaN
  exact
    {exact_name}
      shift psiMain reLower reUpper imLower imUpper errRe errIm err
      (Real.eulerMascheroniSeq gammaN) (Real.eulerMascheroniSeq' gammaN)
      reTailLower reTailUpper imTailLower imTailUpper
      hGamma.1 hGamma.2 hReTailLower hReTailUpper hReLowerFinal
      hReUpperFinal hImTailLower hImTailUpper hImLowerFinal hImUpperFinal
      hReCenterLower hReCenterUpper hImCenterLower hImCenterUpper hErr
      hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_prefix_tail_abs(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_prefix_tail_abs_theorem_name(row)
    rect_name = interval_from_shifted_digamma_rect_interval_theorem_name(row)
    return f"""def {theorem}
    (shift N : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (gammaLower gammaUpper rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re))
    (hRePrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re) <=
        rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + N : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLowerFinal :
      reLower <= -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpperFinal :
      -gammaLower + rePrefixUpper + reTailRadius <= reUpper)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im))
    (hImPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im) <=
        imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + N : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLowerFinal : imLower <= imPrefixLower - imTailRadius)
    (hImUpperFinal : imPrefixUpper + imTailRadius <= imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :=
  let hRe :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_re_interval_of_series_prefix_tail_abs
      {anchor} shift N reLower reUpper gammaLower
      gammaUpper rePrefixLower rePrefixUpper reTailRadius hGammaLower
      hGammaUpper hRePrefixLower hRePrefixUpper hReTail hReLowerFinal
      hReUpperFinal
  let hIm :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_im_interval_of_series_prefix_tail_abs
      {anchor} shift N imLower imUpper imPrefixLower
      imPrefixUpper imTailRadius hImPrefixLower hImPrefixUpper hImTail
      hImLowerFinal hImUpperFinal
  {rect_name}
    shift psiMain reLower reUpper imLower imUpper errRe errIm err
    hRe.1 hRe.2 hReCenterLower hReCenterUpper
    hIm.1 hIm.2 hImCenterLower hImCenterUpper hErr
    hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_n16_exact_prefix_tail_abs(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_n16_exact_prefix_tail_abs_theorem_name(row)
    generic_name = interval_from_shifted_digamma_series_prefix_tail_abs_theorem_name(row)
    return f"""def {theorem}
    (shift : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (gammaLower gammaUpper reTailRadius imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLowerFinal :
      reLower <= -gammaUpper +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) - reTailRadius)
    (hReUpperFinal :
      -gammaLower +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + reTailRadius <=
        reUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) - imTailRadius)
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + imTailRadius <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) :=
  {generic_name}
    shift 16 psiMain reLower reUpper imLower imUpper errRe errIm err
    gammaLower gammaUpper
    ((Finset.range 16).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) -
        1 /
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift + (n : Complex))).re))
    ((Finset.range 16).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) -
        1 /
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift + (n : Complex))).re))
    reTailRadius
    ((Finset.range 16).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) -
        1 /
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift + (n : Complex))).im))
    ((Finset.range 16).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) -
        1 /
          (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
            {anchor} shift + (n : Complex))).im))
    imTailRadius hGammaLower hGammaUpper le_rfl le_rfl hReTail
    hReLowerFinal hReUpperFinal le_rfl le_rfl hImTail hImLowerFinal
    hImUpperFinal hReCenterLower hReCenterUpper hImCenterLower
    hImCenterUpper hErr hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_abs(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_abs_theorem_name(row)
    exact_name = interval_from_shifted_digamma_series_n16_exact_prefix_tail_abs_theorem_name(row)
    return f"""def {theorem}
    (shift gammaN : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (reTailRadius imTailRadius : Real)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLowerFinal :
      reLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) - reTailRadius)
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + reTailRadius <=
        reUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) - imTailRadius)
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + imTailRadius <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) := by
  have hGamma := Q3.eulerMascheroniConstant_interval_of_seq gammaN
  exact
    {exact_name}
      shift psiMain reLower reUpper imLower imUpper errRe errIm err
      (Real.eulerMascheroniSeq gammaN) (Real.eulerMascheroniSeq' gammaN)
      reTailRadius imTailRadius hGamma.1 hGamma.2 hReTail
      hReLowerFinal hReUpperFinal hImTail hImLowerFinal hImUpperFinal
      hReCenterLower hReCenterUpper hImCenterLower hImCenterUpper hErr
      hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_abs(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_abs_theorem_name(row)
    component_tail_name = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_abs_theorem_name(row)
    return f"""def {theorem}
    (shift gammaN : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (tailRadius : Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + 16 : Nat) : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift +
                  ((n + 16 : Nat) : Complex))‖) <=
        tailRadius)
    (hReLowerFinal :
      reLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) - tailRadius)
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + tailRadius <=
        reUpper)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) - tailRadius)
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + tailRadius <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) := by
  have hTailParts :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_series_tail_re_im_abs_of_complex_norm_tail
      {anchor} shift 16 tailRadius hTailNorm
  exact
    {component_tail_name}
      shift gammaN psiMain reLower reUpper imLower imUpper errRe errIm err
      tailRadius tailRadius hTailParts.1 hReLowerFinal hReUpperFinal
      hTailParts.2 hImLowerFinal hImUpperFinal hReCenterLower hReCenterUpper
      hImCenterLower hImCenterUpper hErr hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_majorant_abs(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_majorant_abs_theorem_name(row)
    complex_tail_name = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_abs_theorem_name(row)
    return f"""def {theorem}
    (shift gammaN : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (g : Nat -> Real) (tailRadius : Real)
    (hg : Summable g)
    (hTerm :
      ∀ n : Nat,
        ‖1 / (((n + 16 : Nat) : Complex) + 1) -
          1 /
            (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
              {anchor} shift +
                ((n + 16 : Nat) : Complex))‖ <=
          g n)
    (hSum : (∑' n : Nat, g n) <= tailRadius)
    (hReLowerFinal :
      reLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) - tailRadius)
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + tailRadius <=
        reUpper)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) - tailRadius)
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + tailRadius <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) := by
  have hTailNorm :=
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.shifted_digamma_series_complex_tail_norm_le_of_majorant
      {anchor} shift 16 g tailRadius hg hTerm hSum
  exact
    {complex_tail_name}
      shift gammaN psiMain reLower reUpper imLower imUpper errRe errIm err
      tailRadius hTailNorm hReLowerFinal hReUpperFinal hImLowerFinal
      hImUpperFinal hReCenterLower hReCenterUpper hImCenterLower
      hImCenterUpper hErr hMainLower hMainUpper
"""


def render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_abs(
    row: dict[str, Any]
) -> str:
    terms = row_terms(row)
    anchor = lean_rat(terms["anchor"])
    omega_anchor_lower = lean_rat(terms["omegaAnchorLower"])
    omega_anchor_upper = lean_rat(terms["omegaAnchorUpper"])
    theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_abs_theorem_name(row)
    shift_plus_one_theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_abs_theorem_name(row)
    closed_tail_theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_abs_theorem_name(row)
    err_sum_theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_abs_theorem_name(row)
    centered_theorem = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_centered_abs_theorem_name(row)
    majorant_name = interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_majorant_abs_theorem_name(row)
    return f"""def {theorem}
    (shift gammaN : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (C tailRadius : Real)
    (hCnonneg : 0 <= C)
    (hZ :
      ‖Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
          {anchor} shift - 1‖ <= C)
    (hClosed :
      C * (1 / (((16 : Nat) : Real) + (1 / 4 : Real) - 1)) <=
        tailRadius)
    (hReLowerFinal :
      reLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) - tailRadius)
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + tailRadius <=
        reUpper)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) - tailRadius)
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + tailRadius <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) := by
  have hpkg :=
    step22OmegaArchWeightShiftedDigamma_quadratic_majorant_package
      {anchor} shift 16 C tailRadius (by norm_num) hCnonneg hZ
      (by simpa using hClosed)
  exact
    {majorant_name}
      shift gammaN psiMain reLower reUpper imLower imUpper errRe errIm err
      (fun n : Nat =>
        C / ((((n + 16 : Nat) : Real) + (1 / 4 : Real)) ^ 2))
      tailRadius hpkg.1 hpkg.2.1 hpkg.2.2 hReLowerFinal hReUpperFinal
      hImLowerFinal hImUpperFinal hReCenterLower hReCenterUpper
      hImCenterLower hImCenterUpper hErr hMainLower hMainUpper

def {shift_plus_one_theorem}
    (shift gammaN : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err tailRadius : Real)
    (hClosed :
      ((shift : Real) + 1) *
          (1 / (((16 : Nat) : Real) + (1 / 4 : Real) - 1)) <=
        tailRadius)
    (hReLowerFinal :
      reLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) - tailRadius)
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) + tailRadius <=
        reUpper)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) - tailRadius)
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) + tailRadius <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) := by
  have hCnonneg : 0 <= (shift : Real) + 1 := by
    have hshift : 0 <= (shift : Real) := by
      exact_mod_cast Nat.zero_le shift
    linarith
  exact
    {theorem}
      shift gammaN psiMain reLower reUpper imLower imUpper errRe errIm err
      ((shift : Real) + 1) tailRadius hCnonneg
      (step22OmegaArchWeightShiftedDigammaArg_one_twentieth_sub_one_norm_le_shift_plus_one shift)
      hClosed hReLowerFinal hReUpperFinal hImLowerFinal hImUpperFinal
      hReCenterLower hReCenterUpper hImCenterLower hImCenterUpper hErr
      hMainLower hMainUpper

def {closed_tail_theorem}
    (shift gammaN : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm err : Real)
    (hReLowerFinal :
      reLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) -
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))))
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) +
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))) <=
        reUpper)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) -
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))))
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) +
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))) <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hErr : errRe + errIm <= err)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - err)
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + err <=
        {omega_anchor_upper}) := by
  have hClosed :
      ((shift : Real) + 1) *
          (1 / (((16 : Nat) : Real) + (1 / 4 : Real) - 1)) <=
        (((shift : Real) + 1) * ((4 : Real) / (61 : Real))) := by
    norm_num
  exact
    {shift_plus_one_theorem}
      shift gammaN psiMain reLower reUpper imLower imUpper errRe errIm err
      (((shift : Real) + 1) * ((4 : Real) / (61 : Real))) hClosed
      hReLowerFinal hReUpperFinal hImLowerFinal hImUpperFinal
      hReCenterLower hReCenterUpper hImCenterLower hImCenterUpper hErr
      hMainLower hMainUpper

def {err_sum_theorem}
    (shift gammaN : Nat) (psiMain : Complex)
    (reLower reUpper imLower imUpper errRe errIm : Real)
    (hReLowerFinal :
      reLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) -
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))))
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) +
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))) <=
        reUpper)
    (hImLowerFinal :
      imLower <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) -
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))))
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) +
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))) <=
        imUpper)
    (hReCenterLower : psiMain.re - errRe <= reLower)
    (hReCenterUpper : reUpper <= psiMain.re + errRe)
    (hImCenterLower : psiMain.im - errIm <= imLower)
    (hImCenterUpper : imUpper <= psiMain.im + errIm)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - (errRe + errIm))
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + (errRe + errIm) <=
        {omega_anchor_upper}) := by
  exact
    {closed_tail_theorem}
      shift gammaN psiMain reLower reUpper imLower imUpper errRe errIm
      (errRe + errIm)
      hReLowerFinal hReUpperFinal hImLowerFinal hImUpperFinal
      hReCenterLower hReCenterUpper hImCenterLower hImCenterUpper le_rfl
      hMainLower hMainUpper

def {centered_theorem}
    (shift gammaN : Nat) (psiMain : Complex) (errRe errIm : Real)
    (hReLowerFinal :
      psiMain.re - errRe <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) -
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))))
    (hReUpperFinal :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).re)) +
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))) <=
        psiMain.re + errRe)
    (hImLowerFinal :
      psiMain.im - errIm <=
        ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) -
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))))
    (hImUpperFinal :
      ((Finset.range 16).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                {anchor} shift + (n : Complex))).im)) +
          (((shift : Real) + 1) * ((4 : Real) / (61 : Real))) <=
        psiMain.im + errIm)
    (hMainLower :
      {omega_anchor_lower} <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re - (errRe + errIm))
    (hMainUpper :
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaMain
          {anchor} shift psiMain.re + (errRe + errIm) <=
        {omega_anchor_upper}) := by
  exact
    {err_sum_theorem}
      shift gammaN psiMain
      (psiMain.re - errRe) (psiMain.re + errRe)
      (psiMain.im - errIm) (psiMain.im + errIm) errRe errIm
      hReLowerFinal hReUpperFinal hImLowerFinal hImUpperFinal
      le_rfl le_rfl le_rfl le_rfl hMainLower hMainUpper
"""


def render_lean(rows: list[dict[str, Any]]) -> str:
    shape_prelude = first_row_shape_prelude_from_existing()
    body = "\n".join(
        render_theorem(row) + "\n" +
        render_omega_wrapper_theorem(row) + "\n" +
        (
            render_first_derivative_closed_theorems(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_direct_anchor_closed_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_direct_anchor_pair_closed_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_re_series_anchor_pair_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_re_series_prefix_bounds_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_re_series_n16_anchor_pair_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_shifted_stieltjes_anchor_pair_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_main_error_anchor_pair_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_shifted_digamma_main_error_anchor_pair_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_shifted_digamma_complex_main_error_anchor_pair_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_shifted_digamma_rect_error_anchor_pair_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_shifted_digamma_rect_interval_anchor_pair_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        render_shape_wrapper_theorem(row) + "\n" +
        render_shape_anchor_wrapper_theorem(row) + "\n" +
        (
            render_first_shape_anchor_second_deriv_reduction_theorems(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            render_first_shape_sq_endpoint_bounds_closed_theorem(row) + "\n"
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        render_interval_def(row) +
        (
            "\n" + render_first_interval_from_direct_anchor_pair_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_re_series_interval_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_re_series_n16_prefix_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_stieltjes_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_main_error_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_main_error_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_complex_main_error_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_rect_error_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_rect_interval_shape(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_main_error(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_main_error(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_complex_main_error(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_rect_error(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_rect_interval(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_shifted_digamma_rect_shift16_n16_invsum_bounds(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_shifted_digamma_rect_shift16_n16_point_identities(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_rect_shift16_n16(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_rect_shift16_n16_invsum(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_rect_shift16_n16_complex_main_error_invsum(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_rect_shift16_n16_centered_complex_main_error_invsum(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_log_pi_interval(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_add16_fixed_complex_main_error_log_pi_interval(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_prefix_tail_interval(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_n16_prefix_tail_interval(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_n16_exact_prefix_tail_interval(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_interval(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_prefix_tail_abs(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_n16_exact_prefix_tail_abs(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_abs(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_abs(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_majorant_abs(row)
            if is_first_derivative_closed_row(row)
            else ""
        ) +
        (
            "\n" + render_first_interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_abs(row)
            if is_first_derivative_closed_row(row)
            else ""
        )
        for row in rows
    )
    return f"""import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker
import Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-safe rational endpoint certs for the active Step33A.1-A v21 refined
subchunk lane.

These theorems do not prove the analytic endpoint bounds.  They only package
the rational containment and endpoint-radius arithmetic consumed by
`LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds_rational`.
The v21 worklist uses containment-budget rational proof pads for anchor endpoint
facts, so generated analytic packages will not require exact rational values of
transcendental endpoint functions.

For each row this import also generates a definition that combines future Omega
and ShapeSq endpoint packages with the checked rational cert into the local
endpoint interval cert.

It also emits a shape-square wrapper that closes the purely rational
`2 * E * E'` corner comparisons.  A second wrapper uses the checked
`...anchorValueBounds` receiver: future analytic work may prove two tight
one-point facts for `E(anchor)` and let generated rational square corners close
the `E(anchor)^2` enclosure.

For the Omega side it emits row-specific wrappers around the checked
`Step22OmegaClosedFormEndpointBoundsCert
  .of_re_series_anchor_interval_tail_trigamma_im_closed_form_term_prefix_cubic_tail_Icc`
receiver, the checked derivative cubic-tail closed-form receiver, and the
checked q2/q3 prefix-tail anchor receiver.  These wrappers do not prove
analytic inequalities; they fix the exact premise shape for the next proof-data
generator.

For the first tiny row this import additionally emits a checked coarse
derivative-side specialization:

```lean
primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_of_anchor_prefix_tail_closed_form_generated
primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_of_direct_anchor_generated
primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_of_direct_anchor_pair_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_re_series_interval_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorReSeriesPrefixBoundsN16_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_re_series_N16_prefix_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_shifted_stieltjes_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_main_error_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_shifted_digamma_main_error_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_shifted_digamma_complex_main_error_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_shifted_digamma_rect_error_generated
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_shifted_digamma_rect_interval_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_direct_anchor_pair_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_re_series_interval_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_re_series_N16_prefix_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_stieltjes_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_main_error_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_main_error_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_complex_main_error_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_rect_error_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_rect_interval_and_shape_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_main_error_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_main_error_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_complex_main_error_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_rect_error_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_rect_interval_generated
primaryFiniteRow0Parent0Split100Sub0Shift16N16InvSumBounds_generated
primaryFiniteRow0Parent0Split100Sub0Shift16N16ShiftedDigammaPoint_eq_generated
primaryFiniteRow0Parent0Split100Sub0Shift16N16ShiftedDigammaPoint_re_generated
primaryFiniteRow0Parent0Split100Sub0Shift16N16ShiftedDigammaPoint_im_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16_invSumGenerated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16_complexMainError_invSumGenerated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaRect_shift16_N16_centeredComplexMainError_invSumGenerated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_centeredComplexMainError_invSumRealOnlyGenerated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_centeredComplexMainError_invSumRealOnly_logPiIntervalGenerated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiIntervalGenerated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_prefix_tail_interval_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_prefix_tail_interval_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_tail_interval_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_tail_interval_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_prefix_tail_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_tail_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_tail_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_majorant_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_abs_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shifted_digamma_series_N16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_centered_abs_generated
```

The direct-anchor theorem discharges the derivative trigamma prefix/tail
premises for the local target `0 <= omega' <= 2` and leaves exactly the two
anchor inequalities against `step22OmegaArchWeight (1/20)` explicit.  It is a
proof-slice, not a full endpoint closure.  The pair adapter is only a
convenience wrapper for the prepared first-anchor conjunction theorem.  The
re-series interval adapter gives a second route to that same conjunction from
checked constant, finite-prefix, signed-tail, and rational enclosure premises.
The `N = 16` prefix row closes the finite-prefix premise for the first anchor.
The `N = 16` wrappers consume that checked prefix row and leave only constant
bounds, signed-tail bounds, rational glue, and ShapeSq endpoint facts open.
The shifted-Stieltjes wrappers consume the checked digamma shift receiver and
leave only shifted main/error rational comparisons plus ShapeSq endpoint facts.
The main/error wrappers consume any future high-order Omega abs-bound and leave
only the generated `main ± err` comparisons plus ShapeSq endpoint facts.
The shifted-digamma main/error wrappers let future asymptotic receivers prove
an abs-bound for `ψ(z+shift)` and land at the same first-anchor interval.
The complex shifted-digamma wrappers additionally accept a complex norm
remainder and project it to the required real-part abs-bound in Lean.
The rectangular shifted-digamma wrappers accept componentwise Re/Im error or
interval payloads, and the series-prefix-tail wrappers consume the checked
semantic Re/Im digamma prefix-tail receivers.  The complex-tail wrapper accepts
one complex norm-tail majorant and projects it to both Re/Im tail radii in
Lean.  The majorant wrapper accepts a summable pointwise majorant and a checked
majorant `tsum` comparison, then builds the complex norm-tail premise in Lean.
The quadratic shift+1 closed-tail err-sum wrapper also discharges the purely
rectangular error-budget premise by setting `err = errRe + errIm`.
The centered facade additionally fixes Re/Im lower and upper bounds to
`psiMain.re/im ± errRe/errIm`, discharging the four center-comparison premises.
The shift16/N16 complex-main-error facade consumes one tight complex norm
bound for `Q3.digamma (129/4+i/40)` and the checked finite inverse-sum
rectangle, leaving only rational rectangle/center/main comparisons.
The centered shift16/N16 complex-main-error facade additionally fixes the
unshifted midpoint/radius from the shifted midpoint/error and the checked
inverse-sum midpoint/radius, leaving only the complex norm bound and final
Omega main comparisons.
The real-only add16 centered facade uses the same shifted complex norm bound
but spends only the real inverse-sum radius in the Omega main/error budget.
The log-pi interval facade wraps that real-only add16 facade with checked
`Real.log Real.pi` lower/upper bounds, so final endpoint proof-data can avoid
literal log-pi premises.
The fixed add16/log-pi facade also fixes the shifted digamma complex center,
the shifted error budget, and the log-pi rational interval; it leaves only the
two analytic proofs for that fixed data.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkIntegral
namespace RawOmegaATaylorModelCertificate

{shape_prelude}{body}
end RawOmegaATaylorModelCertificate
end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
"""


def build_report(worklist: dict[str, Any], out_lean: Path) -> dict[str, Any]:
    rows = [row for row in worklist.get("rows") or [] if isinstance(row, dict)]
    omega_failures = [
        row for row in rows
        if not row["containmentComparisons"]["hOmegaContain"]["passes"]
    ]
    shape_failures = [
        row for row in rows
        if not row["containmentComparisons"]["hShapeSqContain"]["passes"]
    ]
    status = (
        "blocked_endpoint_candidate_containment_failed_not_lean"
        if omega_failures or shape_failures
        else "lean_emitted_pending_validation"
    )
    return {
        "schema": SCHEMA,
        "status": status,
        "worklist": worklist.get("schema"),
        "targetLeanFile": str(out_lean),
        "rows": len(rows),
        "families": sorted({str(row["family"]) for row in rows}),
        "generatedTheorems": [theorem_name(row) for row in rows],
        "generatedOmegaPrefixTailWrappers": [
            omega_wrapper_theorem_name(row) for row in rows
        ],
        "generatedOmegaDerivativeClosedWrappers": [
            omega_derivative_closed_wrapper_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaDirectAnchorWrappers": [
            omega_direct_anchor_wrapper_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaDirectAnchorPairWrappers": [
            omega_direct_anchor_pair_wrapper_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaReSeriesAnchorPairWrappers": [
            omega_re_series_anchor_pair_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaReSeriesPrefixBounds": [
            omega_re_series_prefix_bounds_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaReSeriesN16AnchorPairWrappers": [
            omega_re_series_n16_anchor_pair_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaShiftedStieltjesAnchorPairWrappers": [
            omega_shifted_stieltjes_anchor_pair_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaMainErrorAnchorPairWrappers": [
            omega_main_error_anchor_pair_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaShiftedDigammaMainErrorAnchorPairWrappers": [
            omega_shifted_digamma_main_error_anchor_pair_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaShiftedDigammaComplexMainErrorAnchorPairWrappers": [
            omega_shifted_digamma_complex_main_error_anchor_pair_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaShiftedDigammaRectErrorAnchorPairWrappers": [
            omega_shifted_digamma_rect_error_anchor_pair_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedOmegaShiftedDigammaRectIntervalAnchorPairWrappers": [
            omega_shifted_digamma_rect_interval_anchor_pair_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromDirectAnchorPairShapeDefs": [
            interval_from_direct_anchor_pair_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromReSeriesIntervalShapeDefs": [
            interval_from_re_series_interval_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromReSeriesN16PrefixShapeDefs": [
            interval_from_re_series_n16_prefix_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedStieltjesShapeDefs": [
            interval_from_shifted_stieltjes_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromMainErrorShapeDefs": [
            interval_from_main_error_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaMainErrorShapeDefs": [
            interval_from_shifted_digamma_main_error_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaComplexMainErrorShapeDefs": [
            interval_from_shifted_digamma_complex_main_error_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaRectErrorShapeDefs": [
            interval_from_shifted_digamma_rect_error_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaRectIntervalShapeDefs": [
            interval_from_shifted_digamma_rect_interval_shape_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromMainErrorDefs": [
            interval_from_main_error_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaMainErrorDefs": [
            interval_from_shifted_digamma_main_error_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaComplexMainErrorDefs": [
            interval_from_shifted_digamma_complex_main_error_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaRectErrorDefs": [
            interval_from_shifted_digamma_rect_error_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaRectIntervalDefs": [
            interval_from_shifted_digamma_rect_interval_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedShift16N16InvSumBounds": [
            shifted_digamma_rect_shift16_n16_invsum_bounds_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedShift16N16ShiftedDigammaPointIdentities": [
            shifted_digamma_rect_shift16_n16_point_eq_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ] + [
            shifted_digamma_rect_shift16_n16_point_re_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ] + [
            shifted_digamma_rect_shift16_n16_point_im_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaRectShift16N16Defs": [
            interval_from_shifted_digamma_rect_shift16_n16_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaRectShift16N16InvSumDefs": [
            interval_from_shifted_digamma_rect_shift16_n16_invsum_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaRectShift16N16ComplexMainErrorInvSumDefs": [
            interval_from_shifted_digamma_rect_shift16_n16_complex_main_error_invsum_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaRectShift16N16CenteredComplexMainErrorInvSumDefs": [
            interval_from_shifted_digamma_rect_shift16_n16_centered_complex_main_error_invsum_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaAdd16CenteredComplexMainErrorInvSumRealOnlyDefs": [
            interval_from_shifted_digamma_add16_centered_complex_main_error_invsum_real_only_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaAdd16FixedComplexMainErrorLogPiIntervalDefs": [
            interval_from_shifted_digamma_add16_fixed_complex_main_error_log_pi_interval_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesPrefixTailIntervalDefs": [
            interval_from_shifted_digamma_series_prefix_tail_interval_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16PrefixTailIntervalDefs": [
            interval_from_shifted_digamma_series_n16_prefix_tail_interval_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixTailIntervalDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_tail_interval_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqTailIntervalDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_interval_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesPrefixTailAbsDefs": [
            interval_from_shifted_digamma_series_prefix_tail_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixTailAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_tail_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqTailAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_tail_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailMajorantAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_majorant_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantShiftPlusOneAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantShiftPlusOneClosedTailAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantShiftPlusOneClosedTailErrSumAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantShiftPlusOneClosedTailErrSumCenteredAbsDefs": [
            interval_from_shifted_digamma_series_n16_exact_prefix_gamma_seq_complex_tail_quadratic_majorant_shift_plus_one_closed_tail_err_sum_centered_abs_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedIntervalDefs": [
            interval_theorem_name(row) for row in rows
        ],
        "generatedShapeWrappers": [
            shape_wrapper_theorem_name(row) for row in rows
        ],
        "generatedShapeAnchorValueWrappers": [
            shape_anchor_wrapper_theorem_name(row) for row in rows
        ],
        "generatedFirstShapeDerivAnchorSecondDerivWrappers": [
            shape_deriv_anchor_second_deriv_wrapper_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedFirstShapeValueFromDerivAnchorWrappers": [
            shape_value_from_deriv_anchor_wrapper_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedFirstShapeSqFromDerivAnchorWrappers": [
            shape_sq_from_deriv_anchor_wrapper_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedFirstShapeSqFromSecondDerivWrappers": [
            shape_sq_from_second_deriv_wrapper_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "generatedFirstShapeSqFromInnerDerivWrappers": [
            shape_sq_from_inner_deriv_wrapper_theorem_name(row)
            for row in rows
            if is_first_derivative_closed_row(row)
        ],
        "omegaContainmentFailures": len(omega_failures),
        "shapeSqContainmentFailures": len(shape_failures),
        "guard": [
            "rational endpoint certs only",
            "Omega wrappers compose explicit analytic premises through checked prefix/tail receivers only",
            "Omega wrappers reduce derivative tails to closed-form rational comparisons",
            "Omega wrappers do not close derivative trigamma prefix rows or anchor q2/q3 prefix rows",
            "first tiny row has a checked derivative-side wrapper for 0 <= omega' <= 2",
            "first tiny row has a direct-anchor wrapper that leaves only hAnchorLower/hAnchorUpper open",
            "first tiny row has a direct-anchor conjunction adapter matching the prepared Aristotle theorem shape",
            "first tiny row has a re-series interval adapter for the same direct-anchor conjunction",
            "first tiny row has checked N=16 finite-prefix bounds for the re-series adapter",
            "first tiny row has N=16 re-series wrappers that consume the checked finite-prefix bounds",
            "first tiny row has shifted-Stieltjes anchor pair wrapper through checked digamma shift receiver",
            "first tiny row has shifted-Stieltjes plus shape endpoint wrapper",
            "first tiny row has generic main/error anchor pair wrapper for future high-order Omega abs-bounds",
            "first tiny row has main/error plus shape endpoint wrapper",
            "first tiny row has shifted-digamma main/error anchor pair wrapper for future high-order shifted digamma abs-bounds",
            "first tiny row has shifted-digamma main/error plus shape endpoint wrapper",
            "first tiny row has shifted-digamma complex main/error anchor pair wrapper for future high-order complex norm bounds",
            "first tiny row has shifted-digamma complex main/error plus shape endpoint wrapper",
            "first tiny row has shifted-digamma rectangular Re/Im error and interval wrappers",
            "first tiny row has shifted-digamma series-prefix-tail interval and absolute-tail endpoint wrappers",
            "first tiny row has a shifted-digamma complex-tail wrapper that projects one norm-tail bound to Re/Im tails",
            "first tiny row has a shifted-digamma complex-tail majorant wrapper that builds the norm-tail bound from g and tsum g",
            "first tiny row has a shifted-digamma quadratic-majorant wrapper using the checked C/((n+16+1/4)^2) tail package",
            "first tiny row has a shifted-digamma quadratic-majorant shift+1 wrapper that discharges hZ with a checked anchor norm bound",
            "first tiny row has a shifted-digamma quadratic-majorant shift+1 closed-tail wrapper with tailRadius = (shift+1)*4/61",
            "first tiny row has a shifted-digamma quadratic-majorant shift+1 closed-tail err-sum wrapper with err = errRe+errIm",
            "first tiny row has a shifted-digamma quadratic-majorant shift+1 closed-tail err-sum centered wrapper with Re/Im endpoints fixed to psiMain +/- err",
            "first tiny row has a shift16/N16 complex-main-error facade over the checked invSum rectangle",
            "first tiny row has a centered shift16/N16 complex-main-error facade with midpoint/radius fixed from the checked invSum rectangle",
            "first tiny row has a real-only add16 centered facade that spends shiftedErr + invReRadius for Omega",
            "first tiny row has ShapeSq endpoint reduction from anchor E, anchor E', and inner-deriv interval bounds",
            "first tiny row q2/q3 prefix-tail wrapper remains available but is no longer the preferred route",
            "shape-square wrappers close derivative-square rational corner comparisons only",
            "shape anchor-value wrappers close anchor-square rational corner comparisons only",
            "tight shape-square anchor endpoint facts remain open",
            "tight shape anchor-value endpoint facts remain open",
            "shape value and derivative analytic interval facts remain open",
            "analytic endpoint packages remain open",
            "do not call A hbox closed from this artifact",
            "no CSV/ARadius/radius-floor/LDL/Q3.Main/H1/PO3 route touched",
        ],
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Endpoint Rational Lean Import",
        "",
        f"- Schema: `{report['schema']}`",
        f"- Status: `{report['status']}`",
        f"- Worklist: `{report['worklist']}`",
        f"- Target Lean file: `{report['targetLeanFile']}`",
        f"- Rows: `{report['rows']}`",
        f"- Families: `{', '.join(report['families'])}`",
        "- Omega derivative-closed wrappers: "
        f"`{len(report['generatedOmegaDerivativeClosedWrappers'])}`",
        "- Omega direct-anchor wrappers: "
        f"`{len(report['generatedOmegaDirectAnchorWrappers'])}`",
        "- Omega direct-anchor pair wrappers: "
        f"`{len(report['generatedOmegaDirectAnchorPairWrappers'])}`",
        "- Omega re-series anchor pair wrappers: "
        f"`{len(report['generatedOmegaReSeriesAnchorPairWrappers'])}`",
        "- Omega re-series prefix bounds: "
        f"`{len(report['generatedOmegaReSeriesPrefixBounds'])}`",
        "- Omega re-series N16-prefix anchor pair wrappers: "
        f"`{len(report['generatedOmegaReSeriesN16AnchorPairWrappers'])}`",
        "- Omega shifted-Stieltjes anchor pair wrappers: "
        f"`{len(report['generatedOmegaShiftedStieltjesAnchorPairWrappers'])}`",
        "- Omega main/error anchor pair wrappers: "
        f"`{len(report['generatedOmegaMainErrorAnchorPairWrappers'])}`",
        "- Omega shifted-digamma main/error anchor pair wrappers: "
        f"`{len(report['generatedOmegaShiftedDigammaMainErrorAnchorPairWrappers'])}`",
        "- Omega shifted-digamma complex main/error anchor pair wrappers: "
        f"`{len(report['generatedOmegaShiftedDigammaComplexMainErrorAnchorPairWrappers'])}`",
        "- Interval defs from direct-anchor pair and shape: "
        f"`{len(report['generatedIntervalFromDirectAnchorPairShapeDefs'])}`",
        "- Interval defs from re-series interval and shape: "
        f"`{len(report['generatedIntervalFromReSeriesIntervalShapeDefs'])}`",
        "- Interval defs from re-series N16-prefix and shape: "
        f"`{len(report['generatedIntervalFromReSeriesN16PrefixShapeDefs'])}`",
        "- Interval defs from shifted-Stieltjes and shape: "
        f"`{len(report['generatedIntervalFromShiftedStieltjesShapeDefs'])}`",
        "- Interval defs from main/error and shape: "
        f"`{len(report['generatedIntervalFromMainErrorShapeDefs'])}`",
        "- Interval defs from shifted-digamma main/error and shape: "
        f"`{len(report['generatedIntervalFromShiftedDigammaMainErrorShapeDefs'])}`",
        "- Interval defs from shifted-digamma complex main/error and shape: "
        f"`{len(report['generatedIntervalFromShiftedDigammaComplexMainErrorShapeDefs'])}`",
        "- Interval defs from shifted-digamma N16 signed-tail series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16PrefixTailIntervalDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix signed-tail series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixTailIntervalDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq signed-tail series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqTailIntervalDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix abs-tail series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixTailAbsDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq abs-tail series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqTailAbsDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq complex-tail series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailAbsDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq complex-tail majorant series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailMajorantAbsDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq complex-tail quadratic majorant series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantAbsDefs'])}`",
        "- Shift16/N16 shifted digamma point identities: "
        f"`{len(report['generatedShift16N16ShiftedDigammaPointIdentities'])}`",
        "- Interval defs from shift16/N16 complex-main error plus checked invSum: "
        f"`{len(report['generatedIntervalFromShiftedDigammaRectShift16N16ComplexMainErrorInvSumDefs'])}`",
        "- Interval defs from centered shift16/N16 complex-main error plus checked invSum: "
        f"`{len(report['generatedIntervalFromShiftedDigammaRectShift16N16CenteredComplexMainErrorInvSumDefs'])}`",
        "- Interval defs from real-only add16 centered complex-main error plus checked invSum: "
        f"`{len(report['generatedIntervalFromShiftedDigammaAdd16CenteredComplexMainErrorInvSumRealOnlyDefs'])}`",
        "- Interval defs from fixed add16 complex-main error plus log-pi interval: "
        f"`{len(report['generatedIntervalFromShiftedDigammaAdd16FixedComplexMainErrorLogPiIntervalDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq complex-tail quadratic shift+1 series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantShiftPlusOneAbsDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq complex-tail quadratic shift+1 closed-tail series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantShiftPlusOneClosedTailAbsDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq complex-tail quadratic shift+1 closed-tail err-sum series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantShiftPlusOneClosedTailErrSumAbsDefs'])}`",
        "- Interval defs from shifted-digamma N16 exact-prefix gamma-seq complex-tail quadratic shift+1 closed-tail err-sum centered series: "
        f"`{len(report['generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailQuadraticMajorantShiftPlusOneClosedTailErrSumCenteredAbsDefs'])}`",
        "- First ShapeSq anchor/second-deriv reduction wrappers: "
        f"`{len(report['generatedFirstShapeSqFromInnerDerivWrappers'])}`",
        f"- Omega containment failures: `{report['omegaContainmentFailures']}`",
        f"- ShapeSq containment failures: `{report['shapeSqContainmentFailures']}`",
        "",
        "## Generated Shape",
        "",
        "```lean",
        "LocalRawOmegaComponentDirectEndpointRationalCert ...",
        "Step22OmegaClosedFormEndpointBoundsCert.of_re_series_anchor_interval_tail_trigamma_im_closed_form_term_prefix_cubic_tail_Icc ...",
        "tsum_trigamma_cubic_majorant_tail_le_closed_form ...",
        "step22OmegaArchWeightReSeries_tail_bounds_from_leading_quadratic_prefix_tail_closed_form ...",
        "ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals ...",
        "ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals_anchorValueBounds ...",
        "first ShapeSqEndpointBoundsCert from anchor E, anchor E', and inner-deriv interval bounds ...",
        "def ... : LocalRawOmegaComponentDirectEndpointIntervalCert ...",
        "```",
        "",
        "## Derivative Closed Proof Slices",
        "",
    ]
    for item in report["generatedOmegaDerivativeClosedWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaDerivativeClosedWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Direct Anchor Proof Slices",
        "",
    ])
    for item in report["generatedOmegaDirectAnchorWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaDirectAnchorWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Direct Anchor Pair Adapters",
        "",
    ])
    for item in report["generatedOmegaDirectAnchorPairWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaDirectAnchorPairWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Re-Series Anchor Pair Adapters",
        "",
    ])
    for item in report["generatedOmegaReSeriesAnchorPairWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaReSeriesAnchorPairWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Re-Series Prefix Bounds",
        "",
    ])
    for item in report["generatedOmegaReSeriesPrefixBounds"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaReSeriesPrefixBounds"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Re-Series N16-Prefix Anchor Pair Adapters",
        "",
    ])
    for item in report["generatedOmegaReSeriesN16AnchorPairWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaReSeriesN16AnchorPairWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Shifted-Stieltjes Anchor Pair Adapters",
        "",
    ])
    for item in report["generatedOmegaShiftedStieltjesAnchorPairWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaShiftedStieltjesAnchorPairWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Main/Error Anchor Pair Adapters",
        "",
    ])
    for item in report["generatedOmegaMainErrorAnchorPairWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaMainErrorAnchorPairWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Shifted Digamma Main/Error Anchor Pair Adapters",
        "",
    ])
    for item in report["generatedOmegaShiftedDigammaMainErrorAnchorPairWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaShiftedDigammaMainErrorAnchorPairWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Shifted Digamma Complex Main/Error Anchor Pair Adapters",
        "",
    ])
    for item in report["generatedOmegaShiftedDigammaComplexMainErrorAnchorPairWrappers"]:
        lines.append(f"- `{item}`")
    if not report["generatedOmegaShiftedDigammaComplexMainErrorAnchorPairWrappers"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Direct Anchor Pair And Shape",
        "",
    ])
    for item in report["generatedIntervalFromDirectAnchorPairShapeDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromDirectAnchorPairShapeDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Re-Series Interval And Shape",
        "",
    ])
    for item in report["generatedIntervalFromReSeriesIntervalShapeDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromReSeriesIntervalShapeDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Re-Series N16-Prefix And Shape",
        "",
    ])
    for item in report["generatedIntervalFromReSeriesN16PrefixShapeDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromReSeriesN16PrefixShapeDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted-Stieltjes And Shape",
        "",
    ])
    for item in report["generatedIntervalFromShiftedStieltjesShapeDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedStieltjesShapeDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Main/Error And Shape",
        "",
    ])
    for item in report["generatedIntervalFromMainErrorShapeDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromMainErrorShapeDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma Main/Error And Shape",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaMainErrorShapeDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaMainErrorShapeDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma Complex Main/Error And Shape",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaComplexMainErrorShapeDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaComplexMainErrorShapeDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma Series Prefix/Tail",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesPrefixTailIntervalDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesPrefixTailIntervalDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma N16 Prefix/Tail",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesN16PrefixTailIntervalDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesN16PrefixTailIntervalDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma N16 Exact Prefix/Tail",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixTailIntervalDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixTailIntervalDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma N16 Exact Prefix Gamma-Seq/Tail",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqTailIntervalDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqTailIntervalDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma Prefix/Abs-Tail",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesPrefixTailAbsDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesPrefixTailAbsDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma N16 Exact Prefix/Abs-Tail",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixTailAbsDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixTailAbsDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma N16 Exact Prefix Gamma-Seq/Abs-Tail",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqTailAbsDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqTailAbsDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma N16 Exact Prefix Gamma-Seq/Complex-Tail",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailAbsDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailAbsDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Interval From Shifted Digamma N16 Exact Prefix Gamma-Seq/Complex-Tail Majorant",
        "",
    ])
    for item in report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailMajorantAbsDefs"]:
        lines.append(f"- `{item}`")
    if not report["generatedIntervalFromShiftedDigammaSeriesN16ExactPrefixGammaSeqComplexTailMajorantAbsDefs"]:
        lines.append("- none")
    lines.extend([
        "",
        "## Guard",
        "",
    ])
    for item in report["guard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--out-lean", type=Path, default=DEFAULT_OUT_LEAN)
    args = parser.parse_args()

    worklist = load_json(args.worklist)
    validate_worklist(worklist, args.worklist)
    report = build_report(worklist, args.out_lean)

    if report["status"] == "lean_emitted_pending_validation":
        rows = [row for row in worklist.get("rows") or [] if isinstance(row, dict)]
        args.out_lean.parent.mkdir(parents=True, exist_ok=True)
        args.out_lean.write_text(render_lean(rows), encoding="utf-8")

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    args.out_md.write_text(render_md(report), encoding="utf-8")
    print(
        "endpoint_rational_lean: "
        f"status={report['status']} rows={report['rows']} out={args.out_json}"
    )


if __name__ == "__main__":
    main()
