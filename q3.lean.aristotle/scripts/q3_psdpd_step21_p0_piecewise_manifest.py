#!/usr/bin/env python3
"""
Exact piecewise-polynomial manifest for the Step21 P0 backend.

It records the rational segment decomposition used by
q3_psdpd_step21_p0_interval.py and can emit checked Lean pilot terms against
Q3.Proofs.PSD_P0Piecewise for individual exp-polynomial segments.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any


def frac_from_decimal_text(text: str) -> Fraction:
    return Fraction(text)


def frac_text(x: Fraction) -> str:
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def frac_json(x: Fraction) -> dict[str, int]:
    return {"num": x.numerator, "den": x.denominator}


def lean_rat(x: Fraction) -> str:
    if x.denominator == 1:
        return f"(({x.numerator} : Real))"
    return f"(({x.numerator} : Real) / ({x.denominator} : Real))"


def lean_ident_part(text: str) -> str:
    return "".join(ch if ch.isalnum() else "_" for ch in text)


def centered_bspline_rational(degree: int, x: Fraction) -> Fraction:
    """
    Exact centered cardinal B-spline value at a rational point.

    b_degree(x) = 1 / degree! * sum_j (-1)^j C(degree+1,j)
      * (x + (degree+1)/2 - j)_+^degree
    """
    if degree == 0:
        return Fraction(1) if Fraction(-1, 2) <= x <= Fraction(1, 2) else Fraction(0)

    y = x + Fraction(degree + 1, 2)
    total = Fraction(0)

    for j in range(degree + 2):
        t = y - j
        if t <= 0:
            continue
        total += Fraction(((-1) ** j) * math.comb(degree + 1, j)) * (t ** degree)

    return total / math.factorial(degree)


def spline_breakpoints(k_spline: int) -> list[Fraction]:
    q = 2 * k_spline + 1
    scale = Fraction(k_spline + 1, 2)
    shift = Fraction(q + 1, 2)
    pts = [(Fraction(j) - shift) / scale for j in range(q + 2)]
    pts.extend([Fraction(-2), Fraction(2)])
    return sorted(set(pts))


def active_bspline_poly_coeffs(
    *,
    k_spline: int,
    seg_mid: Fraction,
    norm: Fraction,
) -> list[Fraction]:
    """
    Polynomial coefficients for r_k(x)=b_q(s_k*x)/c_k on one open segment.

    The segment midpoint is used only to choose the active positive-part terms;
    all returned coefficients are exact rational numbers.
    """
    q = 2 * k_spline + 1
    scale = Fraction(k_spline + 1, 2)
    shift = Fraction(q + 1, 2)
    y_mid = scale * seg_mid + shift
    coeffs = [Fraction(0) for _ in range(q + 1)]
    inv_fact_norm = Fraction(1, math.factorial(q)) / norm

    for j in range(q + 2):
        if y_mid - j <= 0:
            continue

        sign_comb = ((-1) ** j) * math.comb(q + 1, j)
        base_const = shift - j
        pref = Fraction(sign_comb) * inv_fact_norm

        for n in range(q + 1):
            coeffs[n] += (
                pref
                * math.comb(q, n)
                * (scale ** n)
                * (base_const ** (q - n))
            )

    return coeffs


def active_bspline_term_count(*, k_spline: int, seg_mid: Fraction) -> int:
    q = 2 * k_spline + 1
    scale = Fraction(k_spline + 1, 2)
    shift = Fraction(q + 1, 2)
    y_mid = scale * seg_mid + shift
    return sum(1 for j in range(q + 2) if y_mid - j > 0)


def clipped_segments(
    *,
    lo: Fraction,
    hi: Fraction,
    k_spline: int,
    norm: Fraction,
) -> list[dict[str, Any]]:
    support_lo = Fraction(-2)
    support_hi = Fraction(2)
    a = max(lo, support_lo)
    b = min(hi, support_hi)

    if b <= a:
        return []

    pts = [a]
    for bp in spline_breakpoints(k_spline):
        if a < bp < b:
            pts.append(bp)
    pts.append(b)
    pts = sorted(set(pts))

    out: list[dict[str, Any]] = []
    for left, right in zip(pts[:-1], pts[1:]):
        if right <= left:
            continue
        mid = (left + right) / 2
        coeffs = active_bspline_poly_coeffs(
            k_spline=k_spline,
            seg_mid=mid,
            norm=norm,
        )
        out.append(
            {
                "lo": frac_text(left),
                "hi": frac_text(right),
                "lo_q": frac_json(left),
                "hi_q": frac_json(right),
                "degree": len(coeffs) - 1,
                "nonzero_coefficients": sum(1 for c in coeffs if c),
                "coefficients": [frac_text(c) for c in coeffs],
            }
        )

    return out


def distance_manifest(
    *,
    d_index: int,
    k_spline: int,
    ell: Fraction,
    support_radius: Fraction,
    norm: Fraction,
) -> dict[str, Any]:
    d = Fraction(d_index, 4)
    lam_minus = -ell / 2
    lam_plus = ell / 2

    plus_lo = (d - 2 * support_radius) / ell
    plus_hi = d / ell
    minus_lo = d / ell
    minus_hi = (d + 2 * support_radius) / ell

    return {
        "distance_index": d_index,
        "distance": frac_text(d),
        "distance_q": frac_json(d),
        "terms": [
            {
                "label": "plus_window",
                "outside_exp": frac_text(d / 2),
                "outside_exp_q": frac_json(d / 2),
                "lambda": frac_text(lam_minus),
                "lambda_q": frac_json(lam_minus),
                "lo": frac_text(plus_lo),
                "hi": frac_text(plus_hi),
                "segments": clipped_segments(
                    lo=plus_lo,
                    hi=plus_hi,
                    k_spline=k_spline,
                    norm=norm,
                ),
            },
            {
                "label": "minus_window",
                "outside_exp": frac_text(-d / 2),
                "outside_exp_q": frac_json(-d / 2),
                "lambda": frac_text(lam_plus),
                "lambda_q": frac_json(lam_plus),
                "lo": frac_text(minus_lo),
                "hi": frac_text(minus_hi),
                "segments": clipped_segments(
                    lo=minus_lo,
                    hi=minus_hi,
                    k_spline=k_spline,
                    norm=norm,
                ),
            },
        ],
    }


def build_manifest(args: argparse.Namespace) -> dict[str, Any]:
    k_spline = args.k_spline
    q = 2 * k_spline + 1
    ell = frac_from_decimal_text(args.ell)
    support_radius = frac_from_decimal_text(args.support_radius)
    norm = centered_bspline_rational(q, Fraction(0))
    distances = range(args.max_distance + 1)

    entries = [
        distance_manifest(
            d_index=d,
            k_spline=k_spline,
            ell=ell,
            support_radius=support_radius,
            norm=norm,
        )
        for d in distances
    ]

    return {
        "schema": "q3_psdpd_step21_p0_piecewise_manifest.v1",
        "purpose": "Exact rational P0 segment decomposition for Lean proof generation.",
        "k_spline": k_spline,
        "autocorr_degree": q,
        "ell": frac_text(ell),
        "support_radius": frac_text(support_radius),
        "bspline_scale": frac_text(Fraction(k_spline + 1, 2)),
        "bspline_autocorr_norm": frac_text(norm),
        "distances": entries,
    }


def summarize(manifest: dict[str, Any]) -> dict[str, Any]:
    segment_counts = []
    nonzero_coeff_counts = []

    for entry in manifest["distances"]:
        total_segments = 0
        for term in entry["terms"]:
            total_segments += len(term["segments"])
            nonzero_coeff_counts.extend(
                seg["nonzero_coefficients"] for seg in term["segments"]
            )
        segment_counts.append(total_segments)

    return {
        "schema": manifest["schema"],
        "k_spline": manifest["k_spline"],
        "autocorr_degree": manifest["autocorr_degree"],
        "distance_count": len(manifest["distances"]),
        "total_segments": sum(segment_counts),
        "max_segments_per_distance": max(segment_counts, default=0),
        "max_nonzero_coefficients_per_segment": max(nonzero_coeff_counts, default=0),
        "bspline_autocorr_norm": manifest["bspline_autocorr_norm"],
    }


def find_distance(manifest: dict[str, Any], distance_index: int) -> dict[str, Any]:
    for entry in manifest["distances"]:
        if entry["distance_index"] == distance_index:
            return entry
    raise ValueError(f"distance_index={distance_index} is not in the manifest")


def find_term(entry: dict[str, Any], label: str) -> dict[str, Any]:
    for term in entry["terms"]:
        if term["label"] == label:
            return term
    raise ValueError(f"term label {label!r} is not present")


def emit_lean_segment(
    manifest: dict[str, Any],
    args: argparse.Namespace,
    *,
    include_prelude: bool = True,
    include_footer: bool = True,
) -> str:
    entry = find_distance(manifest, args.distance_index)
    term = find_term(entry, args.term_label)
    segments = term["segments"]

    if not 0 <= args.segment_index < len(segments):
        raise ValueError(
            f"segment_index={args.segment_index} out of range 0..{len(segments) - 1}"
        )

    segment = segments[args.segment_index]
    coeffs = [Fraction(text) for text in segment["coefficients"]]
    degree = segment["degree"] + 1
    q = manifest["autocorr_degree"]
    spline_range = q + 2
    scale = Fraction(manifest["bspline_scale"])
    shift = Fraction(q + 1, 2)
    lo = Fraction(segment["lo"])
    hi = Fraction(segment["hi"])
    lam = Fraction(term["lambda"])
    seg_mid = (lo + hi) / 2
    active_count = active_bspline_term_count(
        k_spline=manifest["k_spline"],
        seg_mid=seg_mid,
    )
    if active_count <= 0:
        raise ValueError("emitted segments must have at least one active B-spline term")
    active_floor = active_count - 1
    norm_theorem = f"bsplineAutocorrNorm_{manifest['k_spline']}_exact"
    prefix = (
        f"p0PieceK{manifest['k_spline']}D{entry['distance_index']}"
        f"{lean_ident_part(term['label']).title().replace('_', '')}"
        f"Seg{args.segment_index}"
    )

    lines: list[str] = []
    if include_prelude:
        lines.extend(
            [
                "import Q3.Proofs.PSD_P0Piecewise",
                "",
                "set_option linter.mathlibStandardSet false",
                "set_option maxHeartbeats 0",
                "",
                "noncomputable section",
                "",
                "open MeasureTheory",
                "",
                "namespace Q3",
                "namespace PSDpd",
                "",
            ]
        )

    lines.append(f"def {prefix}Coeff : Nat -> Real")

    for n, coeff in enumerate(coeffs):
        lines.append(f"  | {n} => {lean_rat(coeff)}")
    lines.append("  | _ => 0")
    lines.extend(
        [
            "",
            f"theorem {prefix}_centeredBSplineR_eq_expPoly",
            f"    (x : Real) (hxlo : {lean_rat(lo)} < x) (hxhi : x < {lean_rat(hi)}) :",
            f"    centeredBSplineR {manifest['k_spline']} x = expPoly {prefix}Coeff {degree} x := by",
            "  have hsum :",
            f"      (Finset.range {spline_range}).sum (fun j =>",
            f"        ((-1 : Real) ^ j) * (Nat.choose {q + 1} j : Real) *",
            f"          positivePartPower {q}",
            f"            (bsplineScale {manifest['k_spline']} * x + {lean_rat(shift)} - (j : Real))) =",
            f"      (Finset.range {active_count}).sum (fun j =>",
            f"        ((-1 : Real) ^ j) * (Nat.choose {q + 1} j : Real) *",
            f"          positivePartPower {q}",
            f"            (bsplineScale {manifest['k_spline']} * x + {lean_rat(shift)} - (j : Real))) := by",
            "    symm",
            "    refine Finset.sum_subset ?subset ?zero_tail",
            "    · intro j hj",
            "      simp at hj ⊢",
            "      omega",
            "    · intro j hjRange hjNotActive",
            f"      have hj_ge : {active_count} <= j := by",
            "        simp at hjNotActive",
            "        omega",
            f"      have hj_ge_real : ({active_count} : Real) <= (j : Real) := by",
            "        exact_mod_cast hj_ge",
            f"      have hnon : ¬ (0 : Real) <",
            f"          bsplineScale {manifest['k_spline']} * x + {lean_rat(shift)} - (j : Real) := by",
            "        intro hpos",
            f"        have hscale :",
            f"            bsplineScale {manifest['k_spline']} * x + {lean_rat(shift)} - (j : Real) =",
            f"              {lean_rat(scale)} * x + {lean_rat(shift)} - (j : Real) := by",
            f"          norm_num [bsplineScale]",
            "        rw [hscale] at hpos",
            "        linarith",
            f"      rw [positivePartPower_of_nonpos {q} hnon]",
            "      ring",
            "  have hactive :",
            f"      (Finset.range {active_count}).sum (fun j =>",
            f"        ((-1 : Real) ^ j) * (Nat.choose {q + 1} j : Real) *",
            f"          positivePartPower {q}",
            f"            (bsplineScale {manifest['k_spline']} * x + {lean_rat(shift)} - (j : Real))) =",
            f"      (Finset.range {active_count}).sum (fun j =>",
            f"        ((-1 : Real) ^ j) * (Nat.choose {q + 1} j : Real) *",
            f"          (bsplineScale {manifest['k_spline']} * x + {lean_rat(shift)} - (j : Real)) ^ {q}) := by",
            "    apply Finset.sum_congr rfl",
            "    intro j hj",
            f"    have hj_lt : j < {active_count} := by simpa using hj",
            f"    have hj_le_nat : j <= {active_floor} := by omega",
            f"    have hj_le_real : (j : Real) <= ({active_floor} : Real) := by",
            "      exact_mod_cast hj_le_nat",
            f"    have hpos : (0 : Real) <",
            f"        bsplineScale {manifest['k_spline']} * x + {lean_rat(shift)} - (j : Real) := by",
            f"      have hscale :",
            f"          bsplineScale {manifest['k_spline']} * x + {lean_rat(shift)} - (j : Real) =",
            f"            {lean_rat(scale)} * x + {lean_rat(shift)} - (j : Real) := by",
            f"        norm_num [bsplineScale]",
            "      rw [hscale]",
            f"      have hy_gt : ({active_floor} : Real) < {lean_rat(scale)} * x + {lean_rat(shift)} := by",
            "        linarith",
            "      linarith",
            f"    rw [positivePartPower_of_pos {q} hpos]",
            f"  unfold centeredBSplineR centeredCardinalBSpline expPoly {prefix}Coeff",
            "  norm_num [bsplineAutocorrDegree]",
            f"  rw [hsum, hactive, {norm_theorem}]",
            "  norm_num [Finset.sum_range_succ, Nat.choose, bsplineScale]",
            "  ring",
            "",
            f"theorem {prefix}_expPolyIntegral :",
            f"    ∫ x in {lean_rat(lo)}..{lean_rat(hi)},",
            f"      Real.exp ({lean_rat(lam)} * x) *",
            f"        expPoly {prefix}Coeff {degree} x =",
            f"      expPolyIntegral {prefix}Coeff {degree}",
            f"        {lean_rat(lam)}",
            f"        {lean_rat(lo)}",
            f"        {lean_rat(hi)} := by",
            "  exact intervalIntegral_exp_mul_poly_eq_sum",
            f"    {prefix}Coeff {degree}",
            f"    {lean_rat(lam)}",
            f"    {lean_rat(lo)}",
            f"    {lean_rat(hi)}",
            "    (by norm_num)",
            "",
            f"theorem {prefix}_centeredBSplineR_expIntegral :",
            f"    ∫ x in {lean_rat(lo)}..{lean_rat(hi)},",
            f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"      expPolyIntegral {prefix}Coeff {degree}",
            f"        {lean_rat(lam)}",
            f"        {lean_rat(lo)}",
            f"        {lean_rat(hi)} := by",
            "  calc",
            f"    ∫ x in {lean_rat(lo)}..{lean_rat(hi)},",
            f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"        ∫ x in {lean_rat(lo)}..{lean_rat(hi)},",
            f"          Real.exp ({lean_rat(lam)} * x) *",
            f"            expPoly {prefix}Coeff {degree} x := by",
            "          apply intervalIntegral.integral_congr_ae",
            "          filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp",
            f"            (MeasureTheory.measure_singleton {lean_rat(hi)})] with x hxne hxmem",
            "          norm_num [Set.uIoc] at hxmem",
            "          have hxlo :",
            f"              {lean_rat(lo)} < x := by",
            "            linarith [hxmem.1]",
            "          have hxle_hi :",
            f"              x <= {lean_rat(hi)} := by",
            "            linarith [hxmem.2]",
            "          have hxhi :",
            f"              x < {lean_rat(hi)} := by",
            "            exact lt_of_le_of_ne hxle_hi",
            "              (by simpa [Set.mem_singleton_iff] using hxne)",
            f"          rw [{prefix}_centeredBSplineR_eq_expPoly x hxlo hxhi]",
            f"    _ = expPolyIntegral {prefix}Coeff {degree}",
            f"        {lean_rat(lam)}",
            f"        {lean_rat(lo)}",
            f"        {lean_rat(hi)} := by",
            f"        exact {prefix}_expPolyIntegral",
        ]
    )
    if include_footer:
        lines.extend(
            [
                "",
                "end PSDpd",
                "end Q3",
            ]
        )
    return "\n".join(lines) + "\n"


def emit_lean_distance(
    manifest: dict[str, Any],
    args: argparse.Namespace,
    *,
    include_prelude: bool = True,
    include_footer: bool = True,
) -> str:
    entry = find_distance(manifest, args.distance_index)
    term = find_term(entry, args.term_label)
    segments = term["segments"]

    if not segments:
        raise ValueError(
            f"distance_index={args.distance_index} term={args.term_label!r} has no segments"
        )

    distance_prefix = (
        f"p0PieceK{manifest['k_spline']}D{entry['distance_index']}"
        f"{lean_ident_part(term['label']).title().replace('_', '')}"
    )
    lo = Fraction(segments[0]["lo"])
    hi = Fraction(segments[-1]["hi"])
    lam = Fraction(term["lambda"])

    lines: list[str] = []
    if include_prelude:
        lines.extend(
            [
                "import Q3.Proofs.PSD_P0Piecewise",
                "",
                "set_option linter.mathlibStandardSet false",
                "set_option maxHeartbeats 0",
                "",
                "noncomputable section",
                "",
                "open MeasureTheory",
                "",
                "namespace Q3",
                "namespace PSDpd",
                "",
            ]
        )

    for segment_index in range(len(segments)):
        segment_args = argparse.Namespace(**vars(args))
        segment_args.segment_index = segment_index
        lines.append(
            emit_lean_segment(
                manifest,
                segment_args,
                include_prelude=False,
                include_footer=False,
            ).rstrip()
        )
        lines.append("")

    breakpoints = [Fraction(segments[0]["lo"])] + [
        Fraction(segment["hi"]) for segment in segments
    ]
    lines.append(f"def {distance_prefix}Break : Nat -> Real")
    for index, breakpoint in enumerate(breakpoints):
        lines.append(f"  | {index} => {lean_rat(breakpoint)}")
    lines.append(f"  | _ => {lean_rat(breakpoints[-1])}")
    lines.append("")

    lines.append(f"def {distance_prefix}SegmentExpIntegral : Nat -> Real")
    for segment_index, segment in enumerate(segments):
        segment_prefix = f"{distance_prefix}Seg{segment_index}"
        lines.append(
            f"  | {segment_index} => expPolyIntegral {segment_prefix}Coeff {segment['degree'] + 1}"
        )
        lines.append(f"        {lean_rat(lam)}")
        lines.append(f"        {lean_rat(Fraction(segment['lo']))}")
        lines.append(f"        {lean_rat(Fraction(segment['hi']))}")
    lines.append("  | _ => 0")
    lines.append("")
    lines.append(f"def {distance_prefix}ExpPolyIntegralSum : Real :=")
    lines.append(f"  (Finset.range {len(segments)}).sum {distance_prefix}SegmentExpIntegral")
    lines.append("")

    lines.extend(
        [
            f"theorem {distance_prefix}_centeredBSplineR_expIntegral_sum :",
            f"    ∫ x in {lean_rat(lo)}..{lean_rat(hi)},",
            f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"      {distance_prefix}ExpPolyIntegralSum := by",
            "  have hsplit := intervalIntegral.sum_integral_adjacent_intervals",
            f"    (f := fun x : Real => Real.exp ({lean_rat(lam)} * x) *",
            f"      centeredBSplineR {manifest['k_spline']} x)",
            f"    (a := {distance_prefix}Break) (n := {len(segments)})",
            "    (μ := volume) ?hint",
            "  calc",
            f"    ∫ x in {lean_rat(lo)}..{lean_rat(hi)},",
            f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"        (Finset.range {len(segments)}).sum (fun i =>",
            f"          ∫ x in {distance_prefix}Break i..{distance_prefix}Break (i + 1),",
            f"            Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) := by",
            f"          simpa [{distance_prefix}Break] using hsplit.symm",
            f"    _ = (Finset.range {len(segments)}).sum {distance_prefix}SegmentExpIntegral := by",
            "        apply Finset.sum_congr rfl",
            "        intro i hi",
            "        simp at hi",
            "        interval_cases i <;>",
            f"          simp [{distance_prefix}Break, {distance_prefix}SegmentExpIntegral]",
        ]
    )
    for segment_index in range(len(segments)):
        lines.append(
            f"        · simpa [mul_assoc] using {distance_prefix}Seg{segment_index}_centeredBSplineR_expIntegral"
        )
    lines.extend(
        [
            f"    _ = {distance_prefix}ExpPolyIntegralSum := by",
            f"        rfl",
            "  · intro k hk",
            "    exact ((Real.continuous_exp.comp (by continuity)).mul",
            f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _",
        ]
    )

    if include_footer:
        lines.extend(
            [
                "",
                "end PSDpd",
                "end Q3",
            ]
        )

    return "\n".join(lines) + "\n"


def support_zero_theorem(k_spline: int, side: str) -> str:
    if k_spline == 11 and side == "left":
        return "CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_le_neg_two"
    if k_spline == 11 and side == "right":
        return "CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le"
    if k_spline == 9 and side == "left":
        return "CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_le_neg_two"
    if k_spline == 9 and side == "right":
        return "CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le"
    raise ValueError(f"unsupported support-zero theorem k={k_spline} side={side}")


def emit_lean_outside_zero_integral(
    *,
    prefix: str,
    manifest: dict[str, Any],
    lam: Fraction,
    lo: Fraction,
    hi: Fraction,
    side: str,
) -> list[str]:
    if not lo < hi:
        raise ValueError("outside zero integral requires a nonempty interval")

    theorem = support_zero_theorem(manifest["k_spline"], side)
    hineq = "by linarith"
    return [
        f"theorem {prefix}_{side}SupportZeroIntegral :",
        f"    ∫ x in {lean_rat(lo)}..{lean_rat(hi)},",
        f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x = 0 := by",
        "  calc",
        f"    ∫ x in {lean_rat(lo)}..{lean_rat(hi)},",
        f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
        f"        ∫ x in {lean_rat(lo)}..{lean_rat(hi)}, (0 : Real) := by",
        "          apply intervalIntegral.integral_congr",
        "          intro x hx",
        "          norm_num [Set.uIcc] at hx",
        f"          have hzero := {theorem}",
        f"            (x := x) ({hineq})",
        f"          change Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x = (0 : Real)",
        "          rw [hzero]",
        "          ring",
        "    _ = 0 := by simp",
        "",
    ]


def emit_lean_full_window_integral(
    *,
    distance_prefix: str,
    manifest: dict[str, Any],
    term: dict[str, Any],
) -> list[str]:
    segments = term["segments"]

    lam = Fraction(term["lambda"])
    full_lo = Fraction(term["lo"])
    full_hi = Fraction(term["hi"])

    if not segments:
        if Fraction(2) <= full_lo:
            side = "right"
        elif full_hi <= Fraction(-2):
            side = "left"
        else:
            raise ValueError(
                f"empty term={term['label']!r} is not wholly outside support"
            )
        lines = emit_lean_outside_zero_integral(
            prefix=distance_prefix,
            manifest=manifest,
            lam=lam,
            lo=full_lo,
            hi=full_hi,
            side=side,
        )
        lines.extend(
            [
                f"theorem {distance_prefix}_fullWindow_centeredBSplineR_expIntegral_sum :",
                f"    ∫ x in {lean_rat(full_lo)}..{lean_rat(full_hi)},",
                f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
                f"      {distance_prefix}ExpPolyIntegralSum := by",
                f"  simpa [{distance_prefix}ExpPolyIntegralSum] using",
                f"    {distance_prefix}_{side}SupportZeroIntegral",
                "",
            ]
        )
        return lines

    clip_lo = Fraction(segments[0]["lo"])
    clip_hi = Fraction(segments[-1]["hi"])

    if full_lo == clip_lo and full_hi == clip_hi:
        return [
            f"theorem {distance_prefix}_fullWindow_centeredBSplineR_expIntegral_sum :",
            f"    ∫ x in {lean_rat(full_lo)}..{lean_rat(full_hi)},",
            f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"      {distance_prefix}ExpPolyIntegralSum := by",
            f"  exact {distance_prefix}_centeredBSplineR_expIntegral_sum",
            "",
        ]

    lines: list[str] = []

    if full_lo < clip_lo and clip_hi < full_hi:
        lines.extend(
            emit_lean_outside_zero_integral(
                prefix=distance_prefix,
                manifest=manifest,
                lam=lam,
                lo=full_lo,
                hi=clip_lo,
                side="left",
            )
        )
        lines.extend(
            emit_lean_outside_zero_integral(
                prefix=distance_prefix,
                manifest=manifest,
                lam=lam,
                lo=clip_hi,
                hi=full_hi,
                side="right",
            )
        )
        lines.extend(
            [
                f"theorem {distance_prefix}_fullWindow_centeredBSplineR_expIntegral_sum :",
                f"    ∫ x in {lean_rat(full_lo)}..{lean_rat(full_hi)},",
                f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
                f"      {distance_prefix}ExpPolyIntegralSum := by",
                "  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals",
                f"    (a := {lean_rat(full_lo)}) (b := {lean_rat(clip_lo)}) (c := {lean_rat(full_hi)})",
                f"    (f := fun x : Real => Real.exp ({lean_rat(lam)} * x) *",
                f"      centeredBSplineR {manifest['k_spline']} x)",
                "    (μ := volume)",
                "    (((Real.continuous_exp.comp (by continuity)).mul",
                f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _)",
                "    (((Real.continuous_exp.comp (by continuity)).mul",
                f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _)",
                "  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals",
                f"    (a := {lean_rat(clip_lo)}) (b := {lean_rat(clip_hi)}) (c := {lean_rat(full_hi)})",
                f"    (f := fun x : Real => Real.exp ({lean_rat(lam)} * x) *",
                f"      centeredBSplineR {manifest['k_spline']} x)",
                "    (μ := volume)",
                "    (((Real.continuous_exp.comp (by continuity)).mul",
                f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _)",
                "    (((Real.continuous_exp.comp (by continuity)).mul",
                f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _)",
                "  calc",
                f"    ∫ x in {lean_rat(full_lo)}..{lean_rat(full_hi)},",
                f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
                f"        (∫ x in {lean_rat(full_lo)}..{lean_rat(clip_lo)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) +",
                f"        (∫ x in {lean_rat(clip_lo)}..{lean_rat(full_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) := by",
                "        simpa using hsplitLeft.symm",
                f"    _ = ∫ x in {lean_rat(clip_lo)}..{lean_rat(full_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x := by",
                f"        rw [{distance_prefix}_leftSupportZeroIntegral]",
                "        ring",
                f"    _ = (∫ x in {lean_rat(clip_lo)}..{lean_rat(clip_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) +",
                f"        (∫ x in {lean_rat(clip_hi)}..{lean_rat(full_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) := by",
                "        simpa using hsplitRight.symm",
                f"    _ = ∫ x in {lean_rat(clip_lo)}..{lean_rat(clip_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x := by",
                f"        rw [{distance_prefix}_rightSupportZeroIntegral]",
                "        ring",
                f"    _ = {distance_prefix}ExpPolyIntegralSum := by",
                f"        exact {distance_prefix}_centeredBSplineR_expIntegral_sum",
                "",
            ]
        )
        return lines

    if full_lo < clip_lo and full_hi == clip_hi:
        lines.extend(
            emit_lean_outside_zero_integral(
                prefix=distance_prefix,
                manifest=manifest,
                lam=lam,
                lo=full_lo,
                hi=clip_lo,
                side="left",
            )
        )
        lines.extend(
            [
                f"theorem {distance_prefix}_fullWindow_centeredBSplineR_expIntegral_sum :",
                f"    ∫ x in {lean_rat(full_lo)}..{lean_rat(full_hi)},",
                f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
                f"      {distance_prefix}ExpPolyIntegralSum := by",
                "  have hsplit := intervalIntegral.integral_add_adjacent_intervals",
                f"    (a := {lean_rat(full_lo)}) (b := {lean_rat(clip_lo)}) (c := {lean_rat(clip_hi)})",
                f"    (f := fun x : Real => Real.exp ({lean_rat(lam)} * x) *",
                f"      centeredBSplineR {manifest['k_spline']} x)",
                "    (μ := volume)",
                "    (((Real.continuous_exp.comp (by continuity)).mul",
                f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _)",
                "    (((Real.continuous_exp.comp (by continuity)).mul",
                f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _)",
                "  calc",
                f"    ∫ x in {lean_rat(full_lo)}..{lean_rat(full_hi)},",
                f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
                f"        (∫ x in {lean_rat(full_lo)}..{lean_rat(clip_lo)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) +",
                f"        (∫ x in {lean_rat(clip_lo)}..{lean_rat(clip_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) := by",
                "        simpa using hsplit.symm",
                f"    _ = ∫ x in {lean_rat(clip_lo)}..{lean_rat(clip_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x := by",
                f"        rw [{distance_prefix}_leftSupportZeroIntegral]",
                "        ring",
                f"    _ = {distance_prefix}ExpPolyIntegralSum := by",
                f"        exact {distance_prefix}_centeredBSplineR_expIntegral_sum",
                "",
            ]
        )
        return lines

    if full_lo == clip_lo and clip_hi < full_hi:
        lines.extend(
            emit_lean_outside_zero_integral(
                prefix=distance_prefix,
                manifest=manifest,
                lam=lam,
                lo=clip_hi,
                hi=full_hi,
                side="right",
            )
        )
        lines.extend(
            [
                f"theorem {distance_prefix}_fullWindow_centeredBSplineR_expIntegral_sum :",
                f"    ∫ x in {lean_rat(full_lo)}..{lean_rat(full_hi)},",
                f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
                f"      {distance_prefix}ExpPolyIntegralSum := by",
                "  have hsplit := intervalIntegral.integral_add_adjacent_intervals",
                f"    (a := {lean_rat(clip_lo)}) (b := {lean_rat(clip_hi)}) (c := {lean_rat(full_hi)})",
                f"    (f := fun x : Real => Real.exp ({lean_rat(lam)} * x) *",
                f"      centeredBSplineR {manifest['k_spline']} x)",
                "    (μ := volume)",
                "    (((Real.continuous_exp.comp (by continuity)).mul",
                f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _)",
                "    (((Real.continuous_exp.comp (by continuity)).mul",
                f"      (centeredBSplineR_continuous {manifest['k_spline']})).intervalIntegrable _ _)",
                "  calc",
                f"    ∫ x in {lean_rat(full_lo)}..{lean_rat(full_hi)},",
                f"      Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x =",
                f"        (∫ x in {lean_rat(clip_lo)}..{lean_rat(clip_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) +",
                f"        (∫ x in {lean_rat(clip_hi)}..{lean_rat(full_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x) := by",
                "        simpa using hsplit.symm",
                f"    _ = ∫ x in {lean_rat(clip_lo)}..{lean_rat(clip_hi)},",
                f"          Real.exp ({lean_rat(lam)} * x) * centeredBSplineR {manifest['k_spline']} x := by",
                f"        rw [{distance_prefix}_rightSupportZeroIntegral]",
                "        ring",
                f"    _ = {distance_prefix}ExpPolyIntegralSum := by",
                f"        exact {distance_prefix}_centeredBSplineR_expIntegral_sum",
                "",
            ]
        )
        return lines

    raise ValueError(
        "profile full-window generation currently supports unclipped, "
        "left-clipped, or right-clipped one-sided support windows only"
    )


def emit_lean_profile_distance(
    manifest: dict[str, Any],
    args: argparse.Namespace,
    *,
    include_prelude: bool = True,
    include_footer: bool = True,
) -> str:
    entry = find_distance(manifest, args.distance_index)
    plus = find_term(entry, "plus_window")
    minus = find_term(entry, "minus_window")

    profile_prefix = f"p0PieceK{manifest['k_spline']}D{entry['distance_index']}"
    d = Fraction(entry["distance"])
    ell = Fraction(manifest["ell"])
    support_radius = Fraction(manifest["support_radius"])
    plus_prefix = f"{profile_prefix}PlusWindow"
    minus_prefix = f"{profile_prefix}MinusWindow"

    lines: list[str] = []
    if include_prelude:
        lines.extend(
            [
                "import Q3.Proofs.PSD_P0Piecewise",
                "import Q3.Proofs.PSD_CenteredBSplineRBoundsImport",
                "",
                "set_option linter.mathlibStandardSet false",
                "set_option maxHeartbeats 0",
                "",
                "noncomputable section",
                "",
                "open MeasureTheory",
                "",
                "namespace Q3",
                "namespace PSDpd",
                "",
            ]
        )

    for label in ["plus_window", "minus_window"]:
        term = find_term(entry, label)
        distance_prefix = (
            f"{profile_prefix}{lean_ident_part(label).title().replace('_', '')}"
        )
        if not term["segments"]:
            lines.extend(
                [
                    f"def {distance_prefix}ExpPolyIntegralSum : Real := 0",
                    "",
                ]
            )
            continue
        distance_args = argparse.Namespace(**vars(args))
        distance_args.term_label = label
        lines.append(
            emit_lean_distance(
                manifest,
                distance_args,
                include_prelude=False,
                include_footer=False,
            ).rstrip()
        )
        lines.append("")

    lines.extend(
        emit_lean_full_window_integral(
            distance_prefix=plus_prefix,
            manifest=manifest,
            term=plus,
        )
    )
    lines.extend(
        emit_lean_full_window_integral(
            distance_prefix=minus_prefix,
            manifest=manifest,
            term=minus,
        )
    )

    lines.extend(
        [
            f"theorem {profile_prefix}_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums :",
            f"    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile",
            f"      {manifest['k_spline']} {lean_rat(ell)} {lean_rat(support_radius)} {lean_rat(d)} =",
            f"      {lean_rat(ell)} * Real.exp ({lean_rat(d)} / 2) *",
            f"        {plus_prefix}ExpPolyIntegralSum +",
            f"      {lean_rat(ell)} * Real.exp (-({lean_rat(d)} / 2)) *",
            f"        {minus_prefix}ExpPolyIntegralSum := by",
            "  have hprofile :=",
            "    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile_eq_transformed_integrals",
            f"      (k := {manifest['k_spline']})",
            f"      (ell := {lean_rat(ell)})",
            f"      (L := {lean_rat(support_radius)})",
            f"      (d := {lean_rat(d)})",
            "      (by norm_num)",
            "  calc",
            f"    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile",
            f"      {manifest['k_spline']} {lean_rat(ell)} {lean_rat(support_radius)} {lean_rat(d)} =",
            f"      {lean_rat(ell)} * Real.exp ({lean_rat(d)} / 2) *",
            f"        (∫ x in {lean_rat(Fraction(plus['lo']))}..{lean_rat(Fraction(plus['hi']))},",
            f"          Real.exp (-({lean_rat(ell)} / 2) * x) * centeredBSplineR {manifest['k_spline']} x) +",
            f"      {lean_rat(ell)} * Real.exp (-({lean_rat(d)} / 2)) *",
            f"        (∫ x in {lean_rat(Fraction(minus['lo']))}..{lean_rat(Fraction(minus['hi']))},",
            f"          Real.exp (({lean_rat(ell)} / 2) * x) * centeredBSplineR {manifest['k_spline']} x) := by",
            "        norm_num at hprofile ⊢",
            "        simpa [mul_assoc] using hprofile",
            f"    _ = {lean_rat(ell)} * Real.exp ({lean_rat(d)} / 2) *",
            f"        {plus_prefix}ExpPolyIntegralSum +",
            f"      {lean_rat(ell)} * Real.exp (-({lean_rat(d)} / 2)) *",
            f"        {minus_prefix}ExpPolyIntegralSum := by",
            "        have hplus :",
            f"            ∫ x in {lean_rat(Fraction(plus['lo']))}..{lean_rat(Fraction(plus['hi']))},",
            f"              Real.exp (-({lean_rat(ell)} / 2) * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"            {plus_prefix}ExpPolyIntegralSum := by",
            "          calc",
            f"            ∫ x in {lean_rat(Fraction(plus['lo']))}..{lean_rat(Fraction(plus['hi']))},",
            f"              Real.exp (-({lean_rat(ell)} / 2) * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"                ∫ x in {lean_rat(Fraction(plus['lo']))}..{lean_rat(Fraction(plus['hi']))},",
            f"                  Real.exp ({lean_rat(Fraction(plus['lambda']))} * x) * centeredBSplineR {manifest['k_spline']} x := by",
            "                apply intervalIntegral.integral_congr",
            "                intro x hx",
            f"                change Real.exp (-({lean_rat(ell)} / 2) * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"                  Real.exp ({lean_rat(Fraction(plus['lambda']))} * x) * centeredBSplineR {manifest['k_spline']} x",
            f"                have harg : -({lean_rat(ell)} / 2) * x = {lean_rat(Fraction(plus['lambda']))} * x := by",
            "                  ring",
            "                rw [harg]",
            f"            _ = {plus_prefix}ExpPolyIntegralSum := by",
            f"                exact {plus_prefix}_fullWindow_centeredBSplineR_expIntegral_sum",
            "        have hminus :",
            f"            ∫ x in {lean_rat(Fraction(minus['lo']))}..{lean_rat(Fraction(minus['hi']))},",
            f"              Real.exp (({lean_rat(ell)} / 2) * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"            {minus_prefix}ExpPolyIntegralSum := by",
            "          calc",
            f"            ∫ x in {lean_rat(Fraction(minus['lo']))}..{lean_rat(Fraction(minus['hi']))},",
            f"              Real.exp (({lean_rat(ell)} / 2) * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"                ∫ x in {lean_rat(Fraction(minus['lo']))}..{lean_rat(Fraction(minus['hi']))},",
            f"                  Real.exp ({lean_rat(Fraction(minus['lambda']))} * x) * centeredBSplineR {manifest['k_spline']} x := by",
            "                apply intervalIntegral.integral_congr",
            "                intro x hx",
            f"                change Real.exp (({lean_rat(ell)} / 2) * x) * centeredBSplineR {manifest['k_spline']} x =",
            f"                  Real.exp ({lean_rat(Fraction(minus['lambda']))} * x) * centeredBSplineR {manifest['k_spline']} x",
            f"                have harg : ({lean_rat(ell)} / 2) * x = {lean_rat(Fraction(minus['lambda']))} * x := by",
            "                  ring",
            "                rw [harg]",
            f"            _ = {minus_prefix}ExpPolyIntegralSum := by",
            f"                exact {minus_prefix}_fullWindow_centeredBSplineR_expIntegral_sum",
            "        rw [hplus, hminus]",
            "",
        ]
    )

    if include_footer:
        lines.extend(
            [
                "end PSDpd",
                "end Q3",
            ]
        )

    return "\n".join(lines) + "\n"


def emit_lean_profile_all(manifest: dict[str, Any], args: argparse.Namespace) -> str:
    distance_start = getattr(args, "distance_start", 0)
    distance_end = getattr(args, "distance_end", None)
    if distance_end is None:
        distance_end = manifest["distances"][-1]["distance_index"]

    lines: list[str] = [
        "import Q3.Proofs.PSD_P0Piecewise",
        "import Q3.Proofs.PSD_CenteredBSplineRBoundsImport",
        "",
        "set_option linter.mathlibStandardSet false",
        "set_option maxHeartbeats 0",
        "",
        "noncomputable section",
        "",
        "open MeasureTheory",
        "",
        "namespace Q3",
        "namespace PSDpd",
        "",
    ]

    for entry in manifest["distances"]:
        if not distance_start <= entry["distance_index"] <= distance_end:
            continue
        distance_args = argparse.Namespace(**vars(args))
        distance_args.distance_index = entry["distance_index"]
        lines.append(
            emit_lean_profile_distance(
                manifest,
                distance_args,
                include_prelude=False,
                include_footer=False,
            ).rstrip()
        )
        lines.append("")

    lines.extend(
        [
            "end PSDpd",
            "end Q3",
        ]
    )
    return "\n".join(lines) + "\n"


def fraction_floor_to_scale(x: Fraction, scale: int) -> Fraction:
    return Fraction((x.numerator * scale) // x.denominator, scale)


def fraction_ceil_to_scale(x: Fraction, scale: int) -> Fraction:
    return Fraction(-((-x.numerator * scale) // x.denominator), scale)


def exp_taylor_square_interval(x: Fraction, n: int) -> tuple[Fraction, Fraction]:
    half = x / 2
    s = sum((half**m) / Fraction(math.factorial(m)) for m in range(n))
    e = abs(half) ** n * Fraction(n + 1, math.factorial(n) * n)
    lo = (s - e) ** 2
    hi = (s + e) ** 2
    return (lo, hi) if lo <= hi else (hi, lo)


def exp_taylor_fourth_interval(x: Fraction, n: int) -> tuple[Fraction, Fraction]:
    quarter = x / 4
    s = sum((quarter**m) / Fraction(math.factorial(m)) for m in range(n))
    e = abs(quarter) ** n * Fraction(n + 1, math.factorial(n) * n)
    lo = (s - e) ** 4
    hi = (s + e) ** 4
    return (lo, hi) if lo <= hi else (hi, lo)


def exp_taylor_interval(x: Fraction, n: int) -> tuple[str, Fraction, Fraction]:
    if abs(x) <= 2:
        lo, hi = exp_taylor_square_interval(x, n)
        return "half", lo, hi
    if abs(x) <= 4:
        lo, hi = exp_taylor_fourth_interval(x, n)
        return "quarter", lo, hi
    raise ValueError(f"exp endpoint {x} is outside the supported |x| <= 4 range")


def rounded_exp_mid_rad(x: Fraction, n: int, decimal_digits: int) -> tuple[str, Fraction, Fraction]:
    mode, lo, hi = exp_taylor_interval(x, n)
    scale = 10**decimal_digits
    lo_out = fraction_floor_to_scale(lo, scale)
    hi_out = fraction_ceil_to_scale(hi, scale)
    mid = (lo_out + hi_out) / 2
    rad = (hi_out - lo_out) / 2
    return mode, mid, rad


def exp_endpoint_theorem_suffix(x: Fraction) -> str:
    if x == 0:
        return "zero"
    sign = "m" if x < 0 else "p"
    y = abs(x)
    return f"{sign}{y.numerator}_{y.denominator}"


def collect_internal_exp_endpoints(manifest: dict[str, Any]) -> list[Fraction]:
    out: set[Fraction] = set()
    for entry in manifest["distances"]:
        for term in entry["terms"]:
            lam = Fraction(term["lambda"])
            for segment in term["segments"]:
                out.add(lam * Fraction(segment["lo"]))
                out.add(lam * Fraction(segment["hi"]))
    return sorted(out)


def collect_profile_exp_endpoints(manifest: dict[str, Any]) -> list[Fraction]:
    out: set[Fraction] = set()
    for entry in manifest["distances"]:
        for term in entry["terms"]:
            outside_exp = Fraction(term["outside_exp"])
            lam = Fraction(term["lambda"])
            for segment in term["segments"]:
                out.add(outside_exp + lam * Fraction(segment["lo"]))
                out.add(outside_exp + lam * Fraction(segment["hi"]))
    return sorted(out)


def exp_mul_pow_right_coeff(lam: Fraction, a: Fraction, b: Fraction, n: int) -> Fraction:
    if n == 0:
        return Fraction(1) / lam
    return b**n / lam - Fraction(n) / lam * exp_mul_pow_right_coeff(lam, a, b, n - 1)


def exp_mul_pow_left_coeff(lam: Fraction, a: Fraction, b: Fraction, n: int) -> Fraction:
    if n == 0:
        return -Fraction(1) / lam
    return -(a**n / lam) - Fraction(n) / lam * exp_mul_pow_left_coeff(lam, a, b, n - 1)


def window_name(label: str) -> str:
    if label == "plus_window":
        return "PlusWindow"
    if label == "minus_window":
        return "MinusWindow"
    raise ValueError(f"unknown window label: {label}")


def profile_prefix(manifest: dict[str, Any], entry: dict[str, Any]) -> str:
    return f"p0PieceK{manifest['k_spline']}D{entry['distance_index']}"


def profile_theorem_name(manifest: dict[str, Any], entry: dict[str, Any]) -> str:
    return f"{profile_prefix(manifest, entry)}_centeredBSplineP0KernelProfile_eq_expPolyIntegralSums"


def segment_coeff_def_name(
    manifest: dict[str, Any],
    entry: dict[str, Any],
    term: dict[str, Any],
    segment_index: int,
) -> str:
    return f"{profile_prefix(manifest, entry)}{window_name(term['label'])}Seg{segment_index}Coeff"


def segment_integral_name(
    manifest: dict[str, Any],
    entry: dict[str, Any],
    term: dict[str, Any],
) -> str:
    return f"{profile_prefix(manifest, entry)}{window_name(term['label'])}SegmentExpIntegral"


def window_sum_name(
    manifest: dict[str, Any],
    entry: dict[str, Any],
    term: dict[str, Any],
) -> str:
    return f"{profile_prefix(manifest, entry)}{window_name(term['label'])}ExpPolyIntegralSum"


def segment_profile_linear_name(
    manifest: dict[str, Any],
    entry: dict[str, Any],
    term: dict[str, Any],
    segment_index: int,
) -> str:
    return (
        f"{profile_prefix(manifest, entry)}"
        f"{window_name(term['label'])}Seg{segment_index}_profile_linear"
    )


def profile_linear_name(manifest: dict[str, Any], entry: dict[str, Any]) -> str:
    return f"{profile_prefix(manifest, entry)}_profile_linear"


def segment_profile_linear_data(
    manifest: dict[str, Any],
    entry: dict[str, Any],
    term: dict[str, Any],
    segment_index: int,
) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    segment = term["segments"][segment_index]
    coeffs = [Fraction(c) for c in segment["coefficients"]]
    lam = Fraction(term["lambda"])
    a = Fraction(segment["lo"])
    b = Fraction(segment["hi"])
    ell = Fraction(manifest["ell"])
    outside_exp = Fraction(term["outside_exp"])
    right = sum(
        coeff * exp_mul_pow_right_coeff(lam, a, b, n)
        for n, coeff in enumerate(coeffs)
    )
    left = sum(
        coeff * exp_mul_pow_left_coeff(lam, a, b, n)
        for n, coeff in enumerate(coeffs)
    )
    return (
        ell * right,
        outside_exp + lam * b,
        ell * left,
        outside_exp + lam * a,
    )


def distance_profile_linear_coeffs(
    manifest: dict[str, Any],
    entry: dict[str, Any],
) -> dict[Fraction, Fraction]:
    out: dict[Fraction, Fraction] = {}
    for term in entry["terms"]:
        for segment_index, _segment in enumerate(term["segments"]):
            right_coeff, right_exp, left_coeff, left_exp = segment_profile_linear_data(
                manifest, entry, term, segment_index
            )
            out[right_exp] = out.get(right_exp, Fraction(0)) + right_coeff
            out[left_exp] = out.get(left_exp, Fraction(0)) + left_coeff
    return {exp: coeff for exp, coeff in sorted(out.items()) if coeff}


def lean_exp_linear_expr(coeffs: dict[Fraction, Fraction]) -> str:
    terms = [
        f"{lean_rat(coeff)} * Real.exp {lean_rat(exp)}"
        for exp, coeff in coeffs.items()
        if coeff
    ]
    if not terms:
        return "0"
    return " +\n      ".join(terms)


def exp_hbox_have_name(x: Fraction) -> str:
    return f"h_{exp_endpoint_theorem_suffix(x)}"


def fin_distance_lit(distance_index: int) -> str:
    return f"(⟨{distance_index}, by norm_num⟩ : CoeffIndex23)"


def p0_block_prefix(k_spline: int) -> str:
    if k_spline == 11:
        return "primaryK11AnalyticP0"
    if k_spline == 9:
        return "controlK9AnalyticP0"
    raise ValueError(f"unsupported k_spline: {k_spline}")


def p0_payload_prefix(k_spline: int) -> str:
    if k_spline == 11:
        return "primaryK11P0"
    if k_spline == 9:
        return "controlK9P0"
    raise ValueError(f"unsupported k_spline: {k_spline}")


def p0_bounds_cert_name(k_spline: int) -> str:
    if k_spline == 11:
        return "primaryK11AnalyticP0AbsDistanceBoundsCert_generated"
    if k_spline == 9:
        return "controlK9AnalyticP0AbsDistanceBoundsCert_generated"
    raise ValueError(f"unsupported k_spline: {k_spline}")


def p0_bounds_cert_type(k_spline: int) -> str:
    block_prefix = p0_block_prefix(k_spline)
    return f"CenteredCoeffBaseP0HboxImport.{block_prefix}AbsDistanceBoundsCert"


def p0_bounds_chunk_module_name(k_spline: int, distance_start: int, distance_end: int) -> str:
    return (
        f"PSD_CenteredCoeffAnalyticP0BoundsK{k_spline}"
        f"D{distance_start}To{distance_end}Import"
    )


def distance_range_chunks(max_distance: int) -> list[tuple[int, int]]:
    if max_distance < 0:
        return []
    chunks: list[tuple[int, int]] = []
    first_end = min(2, max_distance)
    chunks.append((0, first_end))
    start = first_end + 1
    while start <= max_distance:
        end = min(start + 1, max_distance)
        chunks.append((start, end))
        start = end + 1
    return chunks


def emit_segment_profile_linear_theorem(
    manifest: dict[str, Any],
    entry: dict[str, Any],
    term: dict[str, Any],
    segment_index: int,
) -> list[str]:
    segment = term["segments"][segment_index]
    right_coeff, right_exp, left_coeff, left_exp = segment_profile_linear_data(
        manifest, entry, term, segment_index
    )
    theorem_name = segment_profile_linear_name(manifest, entry, term, segment_index)
    integral_name = segment_integral_name(manifest, entry, term)
    coeff_name = segment_coeff_def_name(manifest, entry, term, segment_index)
    outside_exp = Fraction(term["outside_exp"])
    ell = Fraction(manifest["ell"])
    lam = Fraction(term["lambda"])
    a = Fraction(segment["lo"])
    b = Fraction(segment["hi"])
    degree = int(segment["degree"]) + 1
    lhs = (
        f"{integral_name} {segment_index} * {lean_rat(ell)}"
        if outside_exp == 0
        else f"Real.exp {lean_rat(outside_exp)} * {integral_name} {segment_index} * {lean_rat(ell)}"
    )
    changed_lhs = (
        f"expPolyIntegral {coeff_name} {degree} {lean_rat(lam)} {lean_rat(a)} {lean_rat(b)} * {lean_rat(ell)}"
        if outside_exp == 0
        else f"Real.exp {lean_rat(outside_exp)} * expPolyIntegral {coeff_name} {degree} {lean_rat(lam)} {lean_rat(a)} {lean_rat(b)} * {lean_rat(ell)}"
    )
    lines = [
        f"private theorem {theorem_name} :",
        f"    {lhs} =",
        f"      {lean_rat(right_coeff)} * Real.exp {lean_rat(right_exp)} +",
        f"      {lean_rat(left_coeff)} * Real.exp {lean_rat(left_exp)} := by",
        f"  unfold {integral_name}",
        f"  change {changed_lhs} =",
        f"      {lean_rat(right_coeff)} * Real.exp {lean_rat(right_exp)} +",
        f"      {lean_rat(left_coeff)} * Real.exp {lean_rat(left_exp)}",
        "  rw [expPolyIntegral_eq_exp_linear]",
        "  norm_num [",
        f"    {coeff_name},",
        "    expPolyIntegralRightCoeff,",
        "    expPolyIntegralLeftCoeff,",
        "    expMulPowIntegralRightCoeff,",
        "    expMulPowIntegralLeftCoeff,",
        "    Finset.sum_range_succ",
        "  ]",
    ]
    if outside_exp != 0:
        lines.extend(
            [
                "  ring_nf",
                "  repeat rw [sq]",
                "  repeat rw [← Real.exp_add]",
                "  norm_num",
                "  try ring",
            ]
        )
    else:
        lines.append("  ring")
    lines.append("")
    return lines


def emit_profile_linear_theorem(
    manifest: dict[str, Any],
    entry: dict[str, Any],
) -> list[str]:
    coeffs = distance_profile_linear_coeffs(manifest, entry)
    expr = lean_exp_linear_expr(coeffs)
    prefix = profile_prefix(manifest, entry)
    lines = [
        f"theorem {profile_linear_name(manifest, entry)} :",
        "    CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile",
        f"      {manifest['k_spline']} {lean_rat(Fraction(manifest['ell']))} "
        f"{lean_rat(Fraction(manifest['support_radius']))} "
        f"{lean_rat(Fraction(entry['distance']))} =",
        f"      {expr} := by",
        f"  rw [{profile_theorem_name(manifest, entry)}]",
    ]
    for term in entry["terms"]:
        lines.append(f"  unfold {window_sum_name(manifest, entry, term)}")
    lines.append("  simp only [Finset.sum_range_succ]")
    lines.append("  norm_num")
    lines.append("  ring_nf")
    for term in entry["terms"]:
        for segment_index, _segment in enumerate(term["segments"]):
            lines.append(
                f"  rw [{segment_profile_linear_name(manifest, entry, term, segment_index)}]"
            )
    lines.extend(
        [
            "  try rw [Real.exp_zero]",
            "  ring",
            "",
        ]
    )
    return lines


def emit_distance_bound_theorem(
    manifest: dict[str, Any],
    entry: dict[str, Any],
    *,
    upper: bool,
) -> list[str]:
    coeffs = distance_profile_linear_coeffs(manifest, entry)
    k = manifest["k_spline"]
    block_prefix = p0_block_prefix(k)
    payload_prefix = p0_payload_prefix(k)
    dist = entry["distance_index"]
    bound_kind = "Upper" if upper else "Lower"
    theorem_name = f"{block_prefix}_h{bound_kind}{dist}_generated"
    bound_name = f"CenteredCoeffBaseP0HboxImport.{block_prefix}AbsDistance{bound_kind}"
    cmp = "<=" if upper else ">="
    lhs = (
        "CenteredCoeffAnalyticP0Import.centeredBSplineP0KernelProfile\n"
        f"      {k} {lean_rat(Fraction(manifest['ell']))} "
        f"{lean_rat(Fraction(manifest['support_radius']))} "
        f"(({dist} : Real) / (4 : Real))"
    )
    rhs = f"{bound_name} {fin_distance_lit(dist)}"
    if upper:
        statement = [f"theorem {theorem_name} :", f"    {lhs} <=", f"      {rhs} := by"]
    else:
        statement = [f"theorem {theorem_name} :", f"    {rhs} <=", f"      {lhs} := by"]
    lines = statement
    for exp in coeffs:
        hname = exp_hbox_have_name(exp)
        lines.append(
            f"  have {hname} := abs_sub_le_iff.mp p0ExpK{k}_{exp_endpoint_theorem_suffix(exp)}_hbox"
        )
    lines.append(
        f"  rw [show (({dist} : Real) / (4 : Real)) = {lean_rat(Fraction(entry['distance']))} by norm_num]"
    )
    lines.append(f"  rw [{profile_linear_name(manifest, entry)}]")
    lines.extend(
        [
            "  norm_num [",
            f"    {bound_name},",
            f"    {payload_prefix}AbsDistanceEntryRat,",
            f"    {payload_prefix}RadiusAbsDistanceEntryRat",
            "  ]",
        ]
    )
    linarith_terms: list[str] = []
    for exp in coeffs:
        hname = exp_hbox_have_name(exp)
        linarith_terms.append(f"{hname}.1")
        linarith_terms.append(f"{hname}.2")
    if linarith_terms:
        lines.append("  ring_nf")
        lines.append("  linarith [" + ", ".join(linarith_terms) + "]")
    else:
        lines.append("  norm_num")
    lines.append("")
    return lines


def emit_lean_bounds_distance(
    manifest: dict[str, Any],
    args: argparse.Namespace,
    *,
    include_prelude: bool = True,
    include_footer: bool = True,
) -> str:
    entry = manifest["distances"][args.distance_index]
    lines: list[str] = []
    if include_prelude:
        lines.extend(
            [
                "import Q3.Proofs.PSD_CenteredCoeffAnalyticP0ProfileImport",
                "import Q3.Proofs.PSD_CenteredCoeffAnalyticP0ExpHboxImport",
                "import Q3.Proofs.PSD_CenteredCoeffBaseP0HboxImport",
                "",
                "set_option linter.mathlibStandardSet false",
                "set_option linter.unusedTactic false",
                "set_option maxHeartbeats 0",
                "",
                "noncomputable section",
                "",
                "namespace Q3",
                "namespace PSDpd",
                "",
                "open CenteredCoeffPayloadImport",
                "",
            ]
        )
    for term in entry["terms"]:
        for segment_index, _segment in enumerate(term["segments"]):
            lines.extend(
                emit_segment_profile_linear_theorem(
                    manifest, entry, term, segment_index
                )
            )
    lines.extend(emit_profile_linear_theorem(manifest, entry))
    lines.extend(emit_distance_bound_theorem(manifest, entry, upper=False))
    lines.extend(emit_distance_bound_theorem(manifest, entry, upper=True))
    if include_footer:
        lines.extend(["end PSDpd", "end Q3"])
    return "\n".join(lines) + "\n"


def emit_lean_bounds_all(
    manifest: dict[str, Any],
    args: argparse.Namespace,
    *,
    include_prelude: bool = True,
    include_footer: bool = True,
) -> str:
    distance_start = getattr(args, "distance_start", 0)
    distance_end = getattr(args, "distance_end", None)
    if distance_end is None:
        distance_end = manifest["distances"][-1]["distance_index"]

    lines: list[str] = []
    if include_prelude:
        lines.extend(
            [
                "import Q3.Proofs.PSD_CenteredCoeffAnalyticP0ProfileImport",
                "import Q3.Proofs.PSD_CenteredCoeffAnalyticP0ExpHboxImport",
                "import Q3.Proofs.PSD_CenteredCoeffBaseP0HboxImport",
                "",
                "set_option linter.mathlibStandardSet false",
                "set_option linter.unusedTactic false",
                "set_option maxHeartbeats 0",
                "",
                "noncomputable section",
                "",
                "namespace Q3",
                "namespace PSDpd",
                "",
                "open CenteredCoeffPayloadImport",
                "",
            ]
        )

    for entry in manifest["distances"]:
        if not distance_start <= entry["distance_index"] <= distance_end:
            continue
        distance_args = argparse.Namespace(**vars(args))
        distance_args.distance_index = entry["distance_index"]
        lines.append(
            emit_lean_bounds_distance(
                manifest,
                distance_args,
                include_prelude=False,
                include_footer=False,
            ).rstrip()
        )
        lines.append("")

    if include_footer:
        lines.extend(["end PSDpd", "end Q3"])
    return "\n".join(lines) + "\n"


def emit_lean_bounds_cert(manifest: dict[str, Any], args: argparse.Namespace) -> str:
    max_distance = manifest["distances"][-1]["distance_index"]
    k = manifest["k_spline"]
    block_prefix = p0_block_prefix(k)

    lines: list[str] = []
    for start, end in distance_range_chunks(max_distance):
        lines.append(
            f"import Q3.Proofs.{p0_bounds_chunk_module_name(k, start, end)}"
        )
    lines.extend(
        [
            "",
            "set_option linter.mathlibStandardSet false",
            "set_option linter.unusedTactic false",
            "",
            "/-!",
            f"Generated Step33 P0 distance-bound certificate for k={k}.",
            "",
            "This file packages the generated lower/upper distance bounds into",
            "`CenteredCoeffBaseP0HboxImport`'s compact receiver structure.",
            "-/",
            "",
            "noncomputable section",
            "",
            "namespace Q3",
            "namespace PSDpd",
            "",
            f"theorem {p0_bounds_cert_name(k)} :",
            f"    {p0_bounds_cert_type(k)} := by",
            "  exact ⟨",
        ]
    )
    fields: list[str] = []
    for dist in range(max_distance + 1):
        fields.append(f"{block_prefix}_hLower{dist}_generated")
        fields.append(f"{block_prefix}_hUpper{dist}_generated")
    for index, field in enumerate(fields):
        suffix = "," if index + 1 < len(fields) else ""
        lines.append(f"    {field}{suffix}")
    lines.extend(
        [
            "  ⟩",
            "",
            "end PSDpd",
            "end Q3",
        ]
    )
    return "\n".join(lines) + "\n"


def emit_lean_exp_hboxes(manifest: dict[str, Any], args: argparse.Namespace) -> str:
    taylor_order = getattr(args, "exp_taylor_order", 23)
    decimal_digits = getattr(args, "exp_decimal_digits", 45)
    endpoints = sorted(
        set(collect_internal_exp_endpoints(manifest))
        | set(collect_profile_exp_endpoints(manifest))
    )
    prefix = f"p0ExpK{manifest['k_spline']}"

    lines: list[str] = [
        "import Q3.Proofs.PSD_ExpInterval",
        "",
        "set_option linter.mathlibStandardSet false",
        "",
        "/-!",
        f"Generated endpoint `Real.exp` hboxes for the Step21 P0 k={manifest['k_spline']} profile sums.",
        "",
        "These facts cover the internal segment endpoints `lambda * endpoint`",
        "that occur after reducing the P0 profile to exact `expPolyIntegral`",
        "sums.  They are generated from `PSD_ExpInterval.exp_abs_sub_le_of_half_taylor`",
        "and do not assert any numeric table as trusted proof data.",
        "-/",
        "",
        "noncomputable section",
        "",
        "namespace Q3",
        "namespace PSDpd",
        "",
    ]

    for x in endpoints:
        mode, mid, rad = rounded_exp_mid_rad(x, taylor_order, decimal_digits)
        name = f"{prefix}_{exp_endpoint_theorem_suffix(x)}_hbox"
        helper = (
            "exp_abs_sub_le_of_half_taylor"
            if mode == "half"
            else "exp_abs_sub_le_of_quarter_taylor"
        )
        series_s = "expHalfTaylorS" if mode == "half" else "expQuarterTaylorS"
        series_e = "expHalfTaylorE" if mode == "half" else "expQuarterTaylorE"
        lines.extend(
            [
                f"theorem {name} :",
                f"    |Real.exp {lean_rat(x)} - {lean_rat(mid)}| <= {lean_rat(rad)} := by",
                f"  exact {helper}",
                f"    {lean_rat(x)} {lean_rat(mid)} {lean_rat(rad)} (n := {taylor_order})",
                "    (by norm_num)",
                "    (by norm_num)",
                f"    (by norm_num [{series_s}, {series_e}])",
                f"    (by norm_num [{series_s}, {series_e}])",
                f"    (by norm_num [{series_s}, {series_e}])",
                "",
            ]
        )

    lines.extend(
        [
            "end PSDpd",
            "end Q3",
        ]
    )
    return "\n".join(lines) + "\n"


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k-spline", type=int, choices=[9, 11], default=11)
    parser.add_argument("--ell", type=str, default="3/10")
    parser.add_argument("--support-radius", type=str, default="3")
    parser.add_argument("--max-distance", type=int, default=22)
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--emit-lean-segment", action="store_true")
    parser.add_argument("--emit-lean-distance", action="store_true")
    parser.add_argument("--emit-lean-exp-hboxes", action="store_true")
    parser.add_argument("--emit-lean-bounds-distance", action="store_true")
    parser.add_argument("--emit-lean-bounds-all", action="store_true")
    parser.add_argument("--emit-lean-bounds-cert", action="store_true")
    parser.add_argument("--emit-lean-profile-distance", action="store_true")
    parser.add_argument("--emit-lean-profile-all", action="store_true")
    parser.add_argument("--exp-taylor-order", type=int)
    parser.add_argument("--exp-decimal-digits", type=int)
    parser.add_argument("--distance-index", type=int, default=0)
    parser.add_argument("--distance-start", type=int, default=0)
    parser.add_argument("--distance-end", type=int)
    parser.add_argument(
        "--term-label",
        choices=["plus_window", "minus_window"],
        default="plus_window",
    )
    parser.add_argument("--segment-index", type=int, default=0)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    if args.exp_taylor_order is None:
        args.exp_taylor_order = 56 if args.k_spline == 11 else 52
    if args.exp_decimal_digits is None:
        args.exp_decimal_digits = 125 if args.k_spline == 11 else 115

    if (
        args.emit_lean_segment
        or args.emit_lean_distance
        or args.emit_lean_bounds_distance
        or args.emit_lean_bounds_all
        or args.emit_lean_bounds_cert
        or args.emit_lean_profile_distance
    ):
        args.max_distance = max(args.max_distance, args.distance_index)
    if args.emit_lean_bounds_all and args.distance_end is not None:
        args.max_distance = max(args.max_distance, args.distance_end)
    if args.emit_lean_profile_all and args.distance_end is not None:
        args.max_distance = max(args.max_distance, args.distance_end)

    manifest = build_manifest(args)
    if args.emit_lean_exp_hboxes:
        text = emit_lean_exp_hboxes(manifest, args)
    elif args.emit_lean_bounds_distance:
        text = emit_lean_bounds_distance(manifest, args)
    elif args.emit_lean_bounds_all:
        text = emit_lean_bounds_all(manifest, args)
    elif args.emit_lean_bounds_cert:
        text = emit_lean_bounds_cert(manifest, args)
    elif args.emit_lean_profile_all:
        text = emit_lean_profile_all(manifest, args)
    elif args.emit_lean_profile_distance:
        text = emit_lean_profile_distance(manifest, args)
    elif args.emit_lean_distance:
        text = emit_lean_distance(manifest, args)
    elif args.emit_lean_segment:
        text = emit_lean_segment(manifest, args)
    else:
        payload = summarize(manifest) if args.summary else manifest
        text = json.dumps(payload, indent=2, sort_keys=True) + "\n"

    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    run()
