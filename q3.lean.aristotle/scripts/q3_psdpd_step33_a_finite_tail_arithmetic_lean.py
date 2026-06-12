#!/usr/bin/env python3
"""Generate Lean arithmetic checks for Step33 A finite/tail payload data."""

from __future__ import annotations

import argparse
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
OUT_FILE = ROOT / "Q3/Proofs/PSD_CenteredCoeffAnalyticAFiniteTailArithmeticImport.lean"


BLOCKS = [
    {
        "label": "primary k=11",
        "prefix": "primaryK11AnalyticA",
        "manifest": REQUEST_DIR / "a_finite_tail_components_k11.json",
        "tail_probe": REQUEST_DIR / "a_signed_tail_probe_k11.json",
        "entry": "primaryK11AAbsDistanceEntryRat",
        "radius": "primaryK11ARadiusAbsDistanceEntryRat",
        "cert": "primaryK11AnalyticAFiniteTailArithmeticBoundsCert",
        "payload": "primaryK11A",
        "payload_radius": "primaryK11ARadius",
        "k": "11",
        "ell": "((3 : Real) / (10 : Real))",
        "proof_remainder_pow": "21",
    },
    {
        "label": "control k=9",
        "prefix": "controlK9AnalyticA",
        "manifest": REQUEST_DIR / "a_finite_tail_components_k9.json",
        "tail_probe": REQUEST_DIR / "a_signed_tail_probe_k9.json",
        "entry": "controlK9AAbsDistanceEntryRat",
        "radius": "controlK9ARadiusAbsDistanceEntryRat",
        "cert": "controlK9AnalyticAFiniteTailArithmeticBoundsCert",
        "payload": "controlK9A",
        "payload_radius": "controlK9ARadius",
        "k": "9",
        "ell": "((3 : Real) / (10 : Real))",
        "proof_remainder_pow": "18",
    },
]


def frac_from_decimal(text: str) -> Fraction:
    return Fraction(Decimal(text))


def lean_rat(frac: Fraction) -> str:
    if frac.denominator == 1:
        return f"(({frac.numerator} : Rat))"
    return f"(({frac.numerator} : Rat) / ({frac.denominator} : Rat))"


def lean_real(frac: Fraction) -> str:
    if frac.denominator == 1:
        return f"(({frac.numerator} : Real))"
    return f"(({frac.numerator} : Real) / ({frac.denominator} : Real))"


def load_manifest(path: Path) -> tuple[list[dict[str, Fraction]], Fraction]:
    with path.open() as handle:
        payload = json.load(handle)
    if payload.get("schema") != "q3_psdpd_step22_arch_finite_tail_components.v1":
        raise ValueError(f"{path}: unexpected schema {payload.get('schema')!r}")
    cutoff_t = frac_from_decimal(payload["parameters"]["cutoff_t"])
    rows = []
    for row in payload["distances"]:
        finite_mid = frac_from_decimal(row["finite_mid"])
        finite_radius = frac_from_decimal(row["finite_radius"])
        tail_radius = frac_from_decimal(row["tail_radius"])
        rows.append(
            {
                "finite_lower": finite_mid - finite_radius,
                "finite_upper": finite_mid + finite_radius,
                "tail_radius": tail_radius,
            }
        )
    if len(rows) != 23:
        raise ValueError(f"{path}: expected 23 rows, got {len(rows)}")
    return rows, cutoff_t


def load_tail_probe(path: Path) -> tuple[list[dict[str, Fraction]], Fraction, Fraction]:
    with path.open() as handle:
        payload = json.load(handle)
    if payload.get("schema") != "q3_psdpd_step33_a_signed_tail_probe.v1":
        raise ValueError(f"{path}: unexpected schema {payload.get('schema')!r}")
    params = payload["parameters"]
    cutoff_t = frac_from_decimal(params["cutoff_t"])
    tail_window_end = frac_from_decimal(params["tail_window_end"])
    rows = []
    for row in payload["distances"]:
        rows.append(
            {
                "index": int(row["index"]),
                "window_lower": frac_from_decimal(row["window_lower"]),
                "window_upper": frac_from_decimal(row["window_upper"]),
                "remainder_radius": frac_from_decimal(row["remainder_radius"]),
                "tail_lower": frac_from_decimal(row["tail_lower"]),
                "tail_upper": frac_from_decimal(row["tail_upper"]),
                "generated_tail_radius": frac_from_decimal(row["generated_tail_radius"]),
            }
        )
    if len(rows) != 23:
        raise ValueError(f"{path}: expected 23 rows, got {len(rows)}")
    rows.sort(key=lambda row: row["index"])
    for expected, row in enumerate(rows):
        if row["index"] != expected:
            raise ValueError(f"{path}: expected row index {expected}, got {row['index']}")
    return rows, cutoff_t, tail_window_end


def emit_rat_function(name: str, rows: list[Fraction]) -> list[str]:
    lines = [f"def {name} : Nat -> Rat"]
    for idx, value in enumerate(rows):
        lines.append(f"  | {idx} => {lean_rat(value)}")
    lines.append("  | _ => 0")
    lines.append("")
    return lines


def emit_real_function(name: str, rat_name: str) -> list[str]:
    return [
        f"def {name} (n : CoeffIndex23) : Real :=",
        f"  ({rat_name} n.1 : Real)",
        "",
    ]


def emit_mid_radius_helpers(block: dict[str, str]) -> list[str]:
    prefix = block["prefix"]
    lower = f"{prefix}FiniteLower"
    upper = f"{prefix}FiniteUpper"
    mid = f"{prefix}FiniteMid"
    radius = f"{prefix}FiniteRadius"
    return [
        f"/-- Center of the generated finite-window enclosure for {block['label']}. -/",
        f"def {mid} (n : CoeffIndex23) : Real :=",
        f"  ({lower} n + {upper} n) / 2",
        "",
        f"/-- Radius of the generated finite-window enclosure for {block['label']}. -/",
        f"def {radius} (n : CoeffIndex23) : Real :=",
        f"  ({upper} n - {lower} n) / 2",
        "",
    ]


def emit_positive_half_finite_helpers(block: dict[str, str]) -> list[str]:
    prefix = block["prefix"]
    lower = f"{prefix}FiniteLower"
    upper = f"{prefix}FiniteUpper"
    positive_lower = f"{prefix}FinitePositiveLower"
    positive_upper = f"{prefix}FinitePositiveUpper"
    lower_bound = f"{prefix}FinitePositiveLowerBound_generated"
    upper_bound = f"{prefix}FinitePositiveUpperBound_generated"
    return [
        f"/-- Positive-half finite-window lower target for the folded payload, {block['label']}. -/",
        f"def {positive_lower} (n : CoeffIndex23) : Real :=",
        f"  {lower} n / 2",
        "",
        f"/-- Positive-half finite-window upper target for the folded payload, {block['label']}. -/",
        f"def {positive_upper} (n : CoeffIndex23) : Real :=",
        f"  {upper} n / 2",
        "",
        f"theorem {lower_bound} :",
        "    ∀ n : CoeffIndex23,",
        f"      {lower} n <= 2 * {positive_lower} n := by",
        "  intro n",
        "  have h :",
        f"      2 * {positive_lower} n = {lower} n := by",
        f"    unfold {positive_lower}",
        "    ring",
        "  rw [h]",
        "",
        f"theorem {upper_bound} :",
        "    ∀ n : CoeffIndex23,",
        f"      2 * {positive_upper} n <= {upper} n := by",
        "  intro n",
        "  have h :",
        f"      2 * {positive_upper} n = {upper} n := by",
        f"    unfold {positive_upper}",
        "    ring",
        "  rw [h]",
        "",
    ]


def emit_cert(block: dict[str, str]) -> list[str]:
    prefix = block["prefix"]
    cert = block["cert"]
    entry = block["entry"]
    radius = block["radius"]
    lower = f"{prefix}FiniteLower"
    upper = f"{prefix}FiniteUpper"
    tail = f"{prefix}TailRadius"
    lower_rat = f"{lower}Rat"
    upper_rat = f"{upper}Rat"
    tail_rat = f"{tail}Rat"
    interval = f"CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailArithmeticIntervalCert"
    cert_name = f"{prefix}FiniteTailArithmeticBoundsCert_generated"
    simp_list = [
        interval,
        "CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileFiniteTailArithmeticCert",
        f"CenteredCoeffBaseAHboxImport.{prefix}AbsDistanceLower",
        f"CenteredCoeffBaseAHboxImport.{prefix}AbsDistanceUpper",
        lower,
        upper,
        tail,
        lower_rat,
        upper_rat,
        tail_rat,
        f"CenteredCoeffPayloadImport.{entry}",
        f"CenteredCoeffPayloadImport.{radius}",
    ]
    simp = ",\n      ".join(simp_list)
    return [
        f"theorem {cert_name} :",
        f"    CenteredCoeffAnalyticABoundsBackend.{cert}",
        f"      {lower} {upper} {tail} := by",
        "  refine { h := ?_ }",
        "  intro n",
        "  fin_cases n <;>",
        "    refine { hLower := ?_, hUpper := ?_ } <;>",
        "    norm_num [",
        f"      {simp}",
        "    ]",
        "",
    ]


def emit_generated_receiver(block: dict[str, str]) -> list[str]:
    prefix = block["prefix"]
    k = block["k"]
    ell = block["ell"]
    lower = f"{prefix}FiniteLower"
    upper = f"{prefix}FiniteUpper"
    tail = f"{prefix}TailRadius"
    tail_common = f"{prefix}TailRadiusCommon"
    arith_cert = f"{prefix}FiniteTailArithmeticBoundsCert_generated"
    theorem_name = f"{prefix}FiniteTailBoundsCert_of_generatedArithmetic"
    tail_growth_theorem_name = (
        f"{prefix}TailGrowthBoundsCert_of_commonGeneratedTailRadius"
    )
    finite_part_theorem_name = (
        f"{prefix}FiniteTailBoundsCert_of_generatedFinitePartAndTailGrowth"
    )
    finite_part_tail_interval_theorem_name = (
        f"{prefix}FiniteTailBoundsCert_of_generatedFinitePartAndTailInterval"
    )
    finite_part_common_tail_theorem_name = (
        f"{prefix}FiniteTailBoundsCert_of_generatedFinitePartAndCommonTailGrowth"
    )
    return [
        f"theorem {theorem_name}",
        "    (analytic :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper} {tail}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailBoundsCert",
        f"      archAFiniteTailCutoff {lower} {upper} {tail} := by",
        "  exact",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailBoundsCert_of_analyticAndArithmeticBoundsCert",
        f"      analytic {arith_cert}",
        "",
        f"theorem {tail_growth_theorem_name}",
        "    {C0 C1 : Real}",
        "    (hTail :",
        "      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound",
        f"        {k} {ell} archAFiniteTailCutoff C0 C1 <= {tail_common}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}TailGrowthBoundsCert",
        f"      archAFiniteTailCutoff C0 C1 {tail} := by",
        "  refine ⟨?_⟩",
        "  intro n",
        "  fin_cases n <;>",
        "    simpa [",
        "      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound,",
        f"      {tail},",
        f"      {tail}Rat,",
        f"      {tail_common},",
        f"      {tail_common}Rat",
        "    ] using hTail",
        "",
        f"theorem {finite_part_theorem_name}",
        "    {C0 C1 : Real}",
        "    (hC0 : 0 <= C0) (hC1 : 0 <= C1)",
        "    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)",
        "    (finite :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FinitePartBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper})",
        "    (tailGrowth :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}TailGrowthBoundsCert",
        f"        archAFiniteTailCutoff C0 C1 {tail}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailBoundsCert",
        f"      archAFiniteTailCutoff {lower} {upper} {tail} := by",
        f"  exact {theorem_name}",
        f"    (CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert_of_finitePartAndTailGrowthBounds",
        "      hC0 hC1 hgrowth (by norm_num [archAFiniteTailCutoff]) finite tailGrowth)",
        "",
        f"theorem {finite_part_tail_interval_theorem_name}",
        "    {tailLower tailUpper : CoeffIndex23 → Real}",
        "    (finite :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FinitePartBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper})",
        "    (tail :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}TailIntervalBoundsCert",
        f"        archAFiniteTailCutoff tailLower tailUpper {tail}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailBoundsCert",
        f"      archAFiniteTailCutoff {lower} {upper} {tail} := by",
        f"  exact {theorem_name}",
        f"    (CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds",
        "      finite tail)",
        "",
        f"theorem {finite_part_common_tail_theorem_name}",
        "    {C0 C1 : Real}",
        "    (hC0 : 0 <= C0) (hC1 : 0 <= C1)",
        "    (hgrowth : ∀ t : Real, |Q3.a_star t| <= C0 + C1 * |t|)",
        "    (finite :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FinitePartBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper})",
        "    (hTail :",
        "      CenteredCoeffAnalyticABoundsBackend.centeredBSplineArchKernelProfileTailGrowthBound",
        f"        {k} {ell} archAFiniteTailCutoff C0 C1 <= {tail_common}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailBoundsCert",
        f"      archAFiniteTailCutoff {lower} {upper} {tail} := by",
        f"  exact {finite_part_theorem_name} hC0 hC1 hgrowth finite",
        f"    ({tail_growth_theorem_name} hTail)",
        "",
    ]


def emit_tail_window_receiver(block: dict[str, str]) -> list[str]:
    prefix = block["prefix"]
    lower = f"{prefix}FiniteLower"
    upper = f"{prefix}FiniteUpper"
    tail = f"{prefix}TailRadius"
    window_lower = f"{prefix}TailWindowLower"
    window_upper = f"{prefix}TailWindowUpper"
    remainder = f"{prefix}TailRemainderRadius"
    proof_remainder = f"{prefix}TailProofRemainderRadius"
    signed_tail_lower = f"{prefix}SignedTailLower"
    signed_tail_upper = f"{prefix}SignedTailUpper"
    signed_tail_proof_lower = f"{prefix}SignedTailProofLower"
    signed_tail_proof_upper = f"{prefix}SignedTailProofUpper"
    window_lower_rat = f"{window_lower}Rat"
    window_upper_rat = f"{window_upper}Rat"
    remainder_rat = f"{remainder}Rat"
    tail_rat = f"{tail}Rat"
    tail_interval_theorem = (
        f"{prefix}TailIntervalBoundsCert_of_generatedPositiveTailWindow"
    )
    finite_tail_theorem = (
        f"{prefix}FiniteTailBoundsCert_of_generatedFinitePartAndPositiveTailWindow"
    )
    proof_tail_interval_theorem = (
        f"{prefix}TailIntervalBoundsCert_of_generatedPositiveTailWindowProofRemainder"
    )
    proof_finite_tail_theorem = (
        f"{prefix}FiniteTailBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder"
    )
    proof_finite_tail_analytic_theorem = (
        f"{prefix}FiniteTailAnalyticBoundsCert_of_generatedFinitePartAndPositiveTailWindowProofRemainder"
    )
    simp_defs = [
        signed_tail_lower,
        signed_tail_upper,
        window_lower,
        window_upper,
        remainder,
        tail,
        window_lower_rat,
        window_upper_rat,
        remainder_rat,
        tail_rat,
    ]
    simp = ",\n          ".join(simp_defs)
    proof_simp_defs = [
        signed_tail_proof_lower,
        signed_tail_proof_upper,
        window_lower,
        window_upper,
        proof_remainder,
        tail,
        window_lower_rat,
        window_upper_rat,
        tail_rat,
    ]
    proof_simp = ",\n          ".join(proof_simp_defs)
    return [
        f"theorem {tail_interval_theorem}",
        "    (window :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}PositiveTailWindowBoundsCert",
        f"        archAFiniteTailCutoff archAPositiveTailWindowEnd",
        f"        {window_lower} {window_upper} {remainder}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}TailIntervalBoundsCert",
        f"      archAFiniteTailCutoff {signed_tail_lower} {signed_tail_upper} {tail} := by",
        "  exact",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}TailIntervalBoundsCert_of_positiveTailWindowBoundsCert",
        "      (by norm_num [archAFiniteTailCutoff])",
        "      (by norm_num [archAFiniteTailCutoff, archAPositiveTailWindowEnd])",
        "      window",
        "      (by",
        "        intro n",
        "        fin_cases n <;>",
        "          norm_num [",
        f"          {simp}",
        "          ])",
        "      (by",
        "        intro n",
        "        fin_cases n <;>",
        "          norm_num [",
        f"          {simp}",
        "          ])",
        "      (by",
        "        intro n",
        "        fin_cases n <;>",
        "          norm_num [",
        f"          {simp}",
        "          ])",
        "      (by",
        "        intro n",
        "        fin_cases n <;>",
        "          norm_num [",
        f"          {simp}",
        "          ])",
        "",
        f"theorem {finite_tail_theorem}",
        "    (finite :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FinitePartBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper})",
        "    (window :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}PositiveTailWindowBoundsCert",
        f"        archAFiniteTailCutoff archAPositiveTailWindowEnd",
        f"        {window_lower} {window_upper} {remainder}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailBoundsCert",
        f"      archAFiniteTailCutoff {lower} {upper} {tail} := by",
        f"  exact {prefix}FiniteTailBoundsCert_of_generatedFinitePartAndTailInterval",
        "    finite",
        f"    ({tail_interval_theorem} window)",
        "",
        f"theorem {proof_tail_interval_theorem}",
        "    (window :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}PositiveTailWindowBoundsCert",
        f"        archAFiniteTailCutoff archAPositiveTailWindowEnd",
        f"        {window_lower} {window_upper}",
        f"        {proof_remainder}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}TailIntervalBoundsCert",
        f"      archAFiniteTailCutoff {signed_tail_proof_lower}",
        f"      {signed_tail_proof_upper} {tail} := by",
        "  exact",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}TailIntervalBoundsCert_of_positiveTailWindowBoundsCert",
        "      (by norm_num [archAFiniteTailCutoff])",
        "      (by norm_num [archAFiniteTailCutoff, archAPositiveTailWindowEnd])",
        "      window",
        "      (by",
        "        intro n",
        "        fin_cases n <;>",
        "          norm_num [",
        f"          {proof_simp}",
        "          ])",
        "      (by",
        "        intro n",
        "        fin_cases n <;>",
        "          norm_num [",
        f"          {proof_simp}",
        "          ])",
        "      (by",
        "        intro n",
        "        fin_cases n <;>",
        "          norm_num [",
        f"          {proof_simp}",
        "          ])",
        "      (by",
        "        intro n",
        "        fin_cases n <;>",
        "          norm_num [",
        f"          {proof_simp}",
        "          ])",
        "",
        f"theorem {proof_finite_tail_theorem}",
        "    (finite :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FinitePartBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper})",
        "    (window :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}PositiveTailWindowBoundsCert",
        f"        archAFiniteTailCutoff archAPositiveTailWindowEnd",
        f"        {window_lower} {window_upper}",
        f"        {proof_remainder}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailBoundsCert",
        f"      archAFiniteTailCutoff {lower} {upper}",
        f"      {tail} := by",
        f"  exact {prefix}FiniteTailBoundsCert_of_generatedFinitePartAndTailInterval",
        "    finite",
        f"    ({proof_tail_interval_theorem} window)",
        "",
        f"theorem {proof_finite_tail_analytic_theorem}",
        "    (finite :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FinitePartBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper})",
        "    (window :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}PositiveTailWindowBoundsCert",
        f"        archAFiniteTailCutoff archAPositiveTailWindowEnd",
        f"        {window_lower} {window_upper}",
        f"        {proof_remainder}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert",
        f"      archAFiniteTailCutoff {lower} {upper}",
        f"      {tail} := by",
        "  exact",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert_of_finitePartAndTailIntervalBounds",
        "      finite",
        f"      ({proof_tail_interval_theorem} window)",
        "",
    ]


def emit_recenter_receiver(block: dict[str, str]) -> list[str]:
    prefix = block["prefix"]
    entry = block["entry"]
    radius = block["radius"]
    payload = block["payload"]
    payload_radius = block["payload_radius"]
    lower = f"{prefix}FiniteLower"
    upper = f"{prefix}FiniteUpper"
    mid = f"{prefix}FiniteMid"
    finite_radius = f"{prefix}FiniteRadius"
    tail = f"{prefix}TailRadius"
    lower_rat = f"{lower}Rat"
    upper_rat = f"{upper}Rat"
    tail_rat = f"{tail}Rat"
    recenter_theorem_name = f"{prefix}RecenterContainment_generated"
    to_mid_radius_theorem_name = f"{prefix}FiniteTailAnalyticBoundsCert_to_midRadius"
    abs_distance_theorem_name = f"{prefix}AbsDistanceHboxCert_of_delta_recenter_checks"
    entry_theorem_name = f"{prefix}_entry_hbox_of_delta_recenter_checks"
    return [
        f"theorem {recenter_theorem_name} :",
        "    ∀ n : CoeffIndex23,",
        f"      {finite_radius} n + {tail} n +",
        f"          |{mid} n -",
        f"            (CenteredCoeffPayloadImport.{entry} n.1 : Real)| <=",
        f"        (CenteredCoeffPayloadImport.{radius} n.1 : Real) := by",
        "  intro n",
        "  fin_cases n <;>",
        "    norm_num [",
        f"      {mid},",
        f"      {finite_radius},",
        f"      {lower},",
        f"      {upper},",
        f"      {tail},",
        f"      {lower_rat},",
        f"      {upper_rat},",
        f"      {tail_rat},",
        f"      CenteredCoeffPayloadImport.{entry},",
        f"      CenteredCoeffPayloadImport.{radius}",
        "    ]",
        "",
        f"theorem {to_mid_radius_theorem_name}",
        "    (analytic :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper}",
        f"        {tail}) :",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert",
        "      archAFiniteTailCutoff",
        f"      (fun n => {mid} n - {finite_radius} n)",
        f"      (fun n => {mid} n + {finite_radius} n)",
        f"      {tail} := by",
        "  refine ⟨?_⟩",
        "  intro n",
        "  have hn := analytic.h n",
        "  refine",
        "    { hFiniteLower := ?_",
        "      hFiniteUpper := ?_",
        "      hTail := hn.hTail }",
        "  · have hLowerEq :",
        f"        {mid} n - {finite_radius} n =",
        f"          {lower} n := by",
        f"      unfold {mid} {finite_radius}",
        "      ring",
        "    rw [hLowerEq]",
        "    exact hn.hFiniteLower",
        "  · have hUpperEq :",
        f"        {mid} n + {finite_radius} n =",
        f"          {upper} n := by",
        f"      unfold {mid} {finite_radius}",
        "      ring",
        "    rw [hUpperEq]",
        "    exact hn.hFiniteUpper",
        "",
        f"theorem {abs_distance_theorem_name}",
        "    (analytic :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper}",
        f"        {tail}) :",
        f"    CenteredCoeffBaseAHboxImport.{prefix}AbsDistanceHboxCert := by",
        "  exact",
        f"    CenteredCoeffAnalyticABoundsBackend.{prefix}AbsDistanceHboxCert_of_finiteTailAnalyticRecenter",
        "      (T := archAFiniteTailCutoff)",
        f"      (finiteMid := {mid})",
        f"      (finiteRadius := {finite_radius})",
        f"      (tailRadius := {tail})",
        f"      ({to_mid_radius_theorem_name} analytic)",
        f"      {recenter_theorem_name}",
        "",
        f"theorem {entry_theorem_name}",
        "    (analytic :",
        f"      CenteredCoeffAnalyticABoundsBackend.{prefix}FiniteTailAnalyticBoundsCert",
        f"        archAFiniteTailCutoff {lower} {upper}",
        f"        {tail}) :",
        "    Q3.Proofs.matrixEntrywiseAbsLe",
        f"      CenteredCoeffBaseHboxImport.{prefix}",
        f"      CenteredCoeffPayloadImport.{payload}",
        f"      CenteredCoeffPayloadImport.{payload_radius} := by",
        "  exact",
        f"    CenteredCoeffBaseAHboxImport.{prefix}_entry_hbox_of_abs_distance_cert",
        f"      ({abs_distance_theorem_name} analytic)",
        "",
    ]


def emit_block(block: dict[str, str]) -> list[str]:
    rows, _ = load_manifest(block["manifest"])
    tail_probe_rows, probe_cutoff, _ = load_tail_probe(block["tail_probe"])
    manifest_cutoff = load_manifest(block["manifest"])[1]
    if probe_cutoff != manifest_cutoff:
        raise ValueError(
            f"{block['tail_probe']}: cutoff {probe_cutoff} does not match "
            f"{block['manifest']} cutoff {manifest_cutoff}"
        )
    prefix = block["prefix"]
    finite_lower = [row["finite_lower"] for row in rows]
    finite_upper = [row["finite_upper"] for row in rows]
    tail_radius = [row["tail_radius"] for row in rows]
    tail_common_value = tail_radius[0]
    if any(value != tail_common_value for value in tail_radius):
        raise ValueError(f"{block['manifest']}: expected one common tail radius")
    generated_tail_radius = [row["generated_tail_radius"] for row in tail_probe_rows]
    if generated_tail_radius != tail_radius:
        raise ValueError(
            f"{block['tail_probe']}: generated tail radii do not match finite-tail manifest"
        )
    tail_window_lower = [row["window_lower"] for row in tail_probe_rows]
    tail_window_upper = [row["window_upper"] for row in tail_probe_rows]
    tail_remainder_radius = [row["remainder_radius"] for row in tail_probe_rows]
    lower_rat = f"{prefix}FiniteLowerRat"
    upper_rat = f"{prefix}FiniteUpperRat"
    tail_rat = f"{prefix}TailRadiusRat"
    tail_common_rat = f"{prefix}TailRadiusCommonRat"
    tail_window_lower_rat = f"{prefix}TailWindowLowerRat"
    tail_window_upper_rat = f"{prefix}TailWindowUpperRat"
    tail_remainder_radius_rat = f"{prefix}TailRemainderRadiusRat"
    lines = [f"/-- Generated finite-window lower data for {block['label']}. -/"]
    lines.extend(emit_rat_function(lower_rat, finite_lower))
    lines.append(f"/-- Generated finite-window upper data for {block['label']}. -/")
    lines.extend(emit_rat_function(upper_rat, finite_upper))
    lines.append(f"/-- Generated tail radius data for {block['label']}. -/")
    lines.extend(emit_rat_function(tail_rat, tail_radius))
    lines.append(f"/-- Common generated tail radius for {block['label']}. -/")
    lines.append(f"def {tail_common_rat} : Rat := {lean_rat(tail_common_value)}")
    lines.append("")
    lines.append(f"/-- Generated positive-tail-window lower data for {block['label']}. -/")
    lines.extend(emit_rat_function(tail_window_lower_rat, tail_window_lower))
    lines.append(f"/-- Generated positive-tail-window upper data for {block['label']}. -/")
    lines.extend(emit_rat_function(tail_window_upper_rat, tail_window_upper))
    lines.append(f"/-- Generated positive-tail remainder radius data for {block['label']}. -/")
    lines.extend(emit_rat_function(tail_remainder_radius_rat, tail_remainder_radius))
    lines.append(f"/-- Real-valued finite-window lower data for {block['label']}. -/")
    lines.extend(emit_real_function(f"{prefix}FiniteLower", lower_rat))
    lines.append(f"/-- Real-valued finite-window upper data for {block['label']}. -/")
    lines.extend(emit_real_function(f"{prefix}FiniteUpper", upper_rat))
    lines.append(f"/-- Real-valued tail radius data for {block['label']}. -/")
    lines.extend(emit_real_function(f"{prefix}TailRadius", tail_rat))
    lines.append(f"/-- Real-valued common tail radius for {block['label']}. -/")
    lines.append(f"def {prefix}TailRadiusCommon : Real :=")
    lines.append(f"  ({tail_common_rat} : Real)")
    lines.append("")
    lines.append(f"/-- Real-valued positive-tail-window lower data for {block['label']}. -/")
    lines.extend(emit_real_function(f"{prefix}TailWindowLower", tail_window_lower_rat))
    lines.append(f"/-- Real-valued positive-tail-window upper data for {block['label']}. -/")
    lines.extend(emit_real_function(f"{prefix}TailWindowUpper", tail_window_upper_rat))
    lines.append(f"/-- Real-valued positive-tail remainder radius data for {block['label']}. -/")
    lines.extend(emit_real_function(f"{prefix}TailRemainderRadius", tail_remainder_radius_rat))
    lines.append(f"/-- Local proof slack for post-520 {block['label'].split()[0]} log-majorant tail comparisons. -/")
    lines.append(f"def {prefix}TailProofRemainderRadius (_n : CoeffIndex23) : Real :=")
    lines.append(f"  (1 : Real) / (10 : Real) ^ {block['proof_remainder_pow']}")
    lines.append("")
    lines.append(f"/-- Real-valued signed two-sided tail lower data for {block['label']}. -/")
    lines.append(f"def {prefix}SignedTailLower (n : CoeffIndex23) : Real :=")
    lines.append(f"  2 * ({prefix}TailWindowLower n - {prefix}TailRemainderRadius n)")
    lines.append("")
    lines.append(f"/-- Real-valued signed two-sided tail upper data for {block['label']}. -/")
    lines.append(f"def {prefix}SignedTailUpper (n : CoeffIndex23) : Real :=")
    lines.append(f"  2 * ({prefix}TailWindowUpper n + {prefix}TailRemainderRadius n)")
    lines.append("")
    lines.append(f"/-- Real-valued signed two-sided tail lower data using the local proof slack. -/")
    lines.append(f"def {prefix}SignedTailProofLower (n : CoeffIndex23) : Real :=")
    lines.append(f"  2 * ({prefix}TailWindowLower n - {prefix}TailProofRemainderRadius n)")
    lines.append("")
    lines.append(f"/-- Real-valued signed two-sided tail upper data using the local proof slack. -/")
    lines.append(f"def {prefix}SignedTailProofUpper (n : CoeffIndex23) : Real :=")
    lines.append(f"  2 * ({prefix}TailWindowUpper n + {prefix}TailProofRemainderRadius n)")
    lines.append("")
    lines.extend(emit_positive_half_finite_helpers(block))
    lines.extend(emit_mid_radius_helpers(block))
    lines.extend(emit_cert(block))
    lines.extend(emit_generated_receiver(block))
    lines.extend(emit_tail_window_receiver(block))
    lines.extend(emit_recenter_receiver(block))
    return lines


def emit_file() -> str:
    cutoffs = [load_manifest(block["manifest"])[1] for block in BLOCKS]
    if any(cutoff != cutoffs[0] for cutoff in cutoffs):
        raise ValueError(f"mismatched cutoff_t values: {cutoffs!r}")
    tail_windows = [load_tail_probe(block["tail_probe"])[2] for block in BLOCKS]
    if any(tail_window != tail_windows[0] for tail_window in tail_windows):
        raise ValueError(f"mismatched tail_window_end values: {tail_windows!r}")
    lines = [
        "import Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend",
        "",
        "set_option linter.mathlibStandardSet false",
        "set_option linter.unusedTactic false",
        "set_option maxHeartbeats 0",
        "",
        "/-!",
        "Generated Step33 Arch A finite/tail arithmetic layer.",
        "",
        "This file does not prove the finite-window integral enclosures.",
        "It checks the rational arithmetic showing that the generated finite",
        "window and tail payload data fit inside the synchronized Step22 A",
        "midpoint-radius boxes consumed by the active hbox receiver.",
        "-/",
        "",
        "noncomputable section",
        "",
        "namespace Q3",
        "namespace PSDpd",
        "",
        "open CenteredCoeffPayloadImport",
        "",
        "/-- Common finite-window cutoff from the generated Step22 A manifests. -/",
        f"def archAFiniteTailCutoff : Real := {lean_real(cutoffs[0])}",
        "",
        "/-- Common positive-tail-window endpoint from the Step33 A tail probes. -/",
        f"def archAPositiveTailWindowEnd : Real := {lean_real(tail_windows[0])}",
        "",
    ]
    for block in BLOCKS:
        lines.extend(emit_block(block))
    lines.extend(
        [
            "end PSDpd",
            "end Q3",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-dir", type=Path, default=ROOT)
    parser.add_argument("--out", type=Path, default=OUT_FILE)
    args = parser.parse_args()
    output = args.out
    if not output.is_absolute():
        output = args.repo_dir / output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(emit_file())
    print(output)


if __name__ == "__main__":
    main()
