#!/usr/bin/env python3
"""Generate Step33 tight positivePartPower hbox payloads.

The emitted Lean module uses certified PrimeCert log intervals l_p/u_p for the
active L=3 prime-power dictionary and feeds the existing positivePartPower
receiver chain.  It intentionally keeps the coarse payloads in
PSD_CenteredCoeffPrimeEntryHboxImport.lean as fallback witnesses.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DICT = ROOT / "Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean"
OUT = ROOT / "Q3/Proofs/PSD_CenteredCoeffPrimePositivePartTightImport.lean"


def parse_nat_entries(name: str) -> list[int]:
    text = DICT.read_text()
    m = re.search(rf"def {name} : Nat -> Nat\n(?P<body>(?:  \| .*?\n)+)", text)
    if not m:
        raise SystemExit(f"could not find {name}")
    entries: dict[int, int] = {}
    for idx, val in re.findall(r"\| (\d+) => (\d+)", m.group("body")):
        entries[int(idx)] = int(val)
    missing = sorted(set(range(98)) - set(entries))
    if missing:
        raise SystemExit(f"{name} missing entries: {missing[:8]}")
    return [entries[i] for i in range(98)]


def match_cases(fn_name: str, values: list[int], side: str) -> str:
    lines = [
        f"def {fn_name}Entry : Nat -> Real",
    ]
    for i, p in enumerate(values):
        lines.append(f"  | {i} => _root_.Q3.Proofs.PrimeCert.{side}_{p}")
    lines.append("  | _ => 0")
    return "\n".join(lines)


def log_bound_theorem(values: list[int], theorem_name: str, fn_name: str, side: str) -> str:
    is_lower = side == "lower"
    direction = (
        f"{fn_name} n <= Real.log (activeL3PrimeBase n : Real)"
        if is_lower
        else f"Real.log (activeL3PrimeBase n : Real) <= {fn_name} n"
    )
    lines = [
        f"theorem {theorem_name} (n : PrimeShiftIndexL3) :",
        f"    {direction} := by",
        "  fin_cases n",
    ]
    for p in values:
        lemma = f"l_{p}_le_log" if is_lower else f"log_le_u_{p}"
        goal = (
            f"_root_.Q3.Proofs.PrimeCert.l_{p} <= Real.log ({p} : Real)"
            if is_lower
            else f"Real.log ({p} : Real) <= _root_.Q3.Proofs.PrimeCert.u_{p}"
        )
        lines.extend(
            [
                f"  · change {goal}",
                f"    exact _root_.Q3.Proofs.PrimeCert.{lemma}",
            ]
        )
    return "\n".join(lines)


def arg_defs(prefix: str, k: int, center: str, shift: str, ell: str) -> str:
    return f"""
def {prefix}MinusArgLower
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale {k} *
      ((({center} j - {center} i) -
        activeL3PrimeShiftUpper n) / {ell}) +
    (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
    (m : Real)

def {prefix}MinusArgUpper
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale {k} *
      ((({center} j - {center} i) -
        activeL3PrimeShiftLower n) / {ell}) +
    (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
    (m : Real)

def {prefix}PlusArgLower
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale {k} *
      ((({center} j - {center} i) +
        activeL3PrimeShiftLower n) / {ell}) +
    (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
    (m : Real)

def {prefix}PlusArgUpper
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  bsplineScale {k} *
      ((({center} j - {center} i) +
        activeL3PrimeShiftUpper n) / {ell}) +
    (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
    (m : Real)
"""


def payload_defs(prefix: str, k: int) -> str:
    return f"""
def {prefix}MinusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree {k})
      ({prefix}MinusArgLower i j n m) +
    positivePartPower (bsplineAutocorrDegree {k})
      ({prefix}MinusArgUpper i j n m)) / 2

def {prefix}MinusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree {k})
      ({prefix}MinusArgUpper i j n m) -
    positivePartPower (bsplineAutocorrDegree {k})
      ({prefix}MinusArgLower i j n m)) / 2

def {prefix}PlusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree {k})
      ({prefix}PlusArgLower i j n m) +
    positivePartPower (bsplineAutocorrDegree {k})
      ({prefix}PlusArgUpper i j n m)) / 2

def {prefix}PlusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree {k})
      ({prefix}PlusArgUpper i j n m) -
    positivePartPower (bsplineAutocorrDegree {k})
      ({prefix}PlusArgLower i j n m)) / 2

def {prefix}MinusTermMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree {k} + 1) m : Real)) *
      {prefix}MinusMid i j n m

def {prefix}MinusTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree {k} + 1) m : Real)| *
      {prefix}MinusRad i j n m

def {prefix}PlusTermMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  (((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree {k} + 1) m : Real)) *
      {prefix}PlusMid i j n m

def {prefix}PlusTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree {k} + 1) m : Real)| *
      {prefix}PlusRad i j n m

def {prefix}MinusCardMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((Nat.factorial (bsplineAutocorrDegree {k}) : Real)⁻¹) *
    ((Finset.range (bsplineAutocorrDegree {k} + 2)).sum fun m =>
      {prefix}MinusTermMid i j n m)

def {prefix}MinusCardRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree {k}) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree {k} + 2)).sum fun m =>
      {prefix}MinusTermRad i j n m)

def {prefix}PlusCardMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((Nat.factorial (bsplineAutocorrDegree {k}) : Real)⁻¹) *
    ((Finset.range (bsplineAutocorrDegree {k} + 2)).sum fun m =>
      {prefix}PlusTermMid i j n m)

def {prefix}PlusCardRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree {k}) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree {k} + 2)).sum fun m =>
      {prefix}PlusTermRad i j n m)
"""


def log_exp_weight_payload_defs() -> str:
    return """
def activeL3PrimeLogMid (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeLogLower n + activeL3PrimeLogUpper n) / 2

def activeL3PrimeLogRad (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeLogUpper n - activeL3PrimeLogLower n) / 2

def activeL3PrimeExpMid (n : PrimeShiftIndexL3) : Real :=
  Real.exp (-(activeL3PrimeShift n) / 2)

def activeL3PrimeExpRad (_n : PrimeShiftIndexL3) : Real :=
  0

def activeL3PrimeWeightMid (n : PrimeShiftIndexL3) : Real :=
  activeL3PrimeLogMid n * activeL3PrimeExpMid n

def activeL3PrimeWeightRad (n : PrimeShiftIndexL3) : Real :=
  (|activeL3PrimeLogMid n| + activeL3PrimeLogRad n) *
      activeL3PrimeExpRad n +
    activeL3PrimeLogRad n * |activeL3PrimeExpMid n|

theorem activeL3PrimeLog_hbox_of_tight_payload :
    ∀ n,
      |Real.log (activeL3PrimeBase n : Real) - activeL3PrimeLogMid n| <=
        activeL3PrimeLogRad n := by
  intro n
  simpa [activeL3PrimeLogMid, activeL3PrimeLogRad] using
    abs_sub_mid_le_half_width
      (lo := activeL3PrimeLogLower n)
      (y := Real.log (activeL3PrimeBase n : Real))
      (hi := activeL3PrimeLogUpper n)
      (activeL3PrimeLogLower_le_log n)
      (activeL3PrimeLog_le_upper n)

theorem activeL3PrimeExp_exact_hbox :
    ∀ n,
      |Real.exp (-(activeL3PrimeShift n) / 2) - activeL3PrimeExpMid n| <=
        activeL3PrimeExpRad n := by
  intro n
  simp [activeL3PrimeExpMid, activeL3PrimeExpRad]

theorem activeL3PrimeLogLower_le_upper (n : PrimeShiftIndexL3) :
    activeL3PrimeLogLower n <= activeL3PrimeLogUpper n :=
  le_trans (activeL3PrimeLogLower_le_log n) (activeL3PrimeLog_le_upper n)

theorem activeL3PrimeLogRad_nonneg (n : PrimeShiftIndexL3) :
    0 <= activeL3PrimeLogRad n := by
  have h := activeL3PrimeLogLower_le_upper n
  dsimp [activeL3PrimeLogRad]
  linarith

theorem activeL3PrimeExpMid_pos (n : PrimeShiftIndexL3) :
    0 < activeL3PrimeExpMid n := by
  simpa [activeL3PrimeExpMid] using
    Real.exp_pos (-(activeL3PrimeShift n) / 2)

theorem activeL3PrimeExpMid_nonneg (n : PrimeShiftIndexL3) :
    0 <= activeL3PrimeExpMid n :=
  le_of_lt (activeL3PrimeExpMid_pos n)

theorem activeL3PrimeExpMid_le_one (n : PrimeShiftIndexL3) :
    activeL3PrimeExpMid n <= 1 := by
  have hshift : 0 <= activeL3PrimeShift n :=
    activeL3PrimeShift_nonneg n
  have harg : -(activeL3PrimeShift n) / 2 <= 0 := by
    nlinarith
  have h := (Real.exp_le_exp).2 harg
  simpa [activeL3PrimeExpMid] using h

theorem activeL3PrimeExpMid_bounds_of_shift_exp_bounds
    (n : PrimeShiftIndexL3) {lower upper : Real}
    (hlower : lower <= Real.exp (-activeL3PrimeShiftUpper n / 2))
    (hupper : Real.exp (-activeL3PrimeShiftLower n / 2) <= upper) :
    lower <= activeL3PrimeExpMid n ∧ activeL3PrimeExpMid n <= upper := by
  have hshift := activeL3PrimeShift_tight_bounds n
  simpa [activeL3PrimeExpMid] using
    _root_.Q3.Proofs.PrimeCert.exp_neg_half_bounds_of_bounds
      (shift := activeL3PrimeShift n)
      (lo := activeL3PrimeShiftLower n)
      (hi := activeL3PrimeShiftUpper n)
      (lower := lower)
      (upper := upper)
      hshift.1 hshift.2 hlower hupper

theorem activeL3PrimeExpMid_hbox_of_shift_exp_bounds
    (n : PrimeShiftIndexL3) {lower upper : Real}
    (hlower : lower <= Real.exp (-activeL3PrimeShiftUpper n / 2))
    (hupper : Real.exp (-activeL3PrimeShiftLower n / 2) <= upper) :
    |activeL3PrimeExpMid n - ((lower + upper) / 2)| <=
      (upper - lower) / 2 := by
  have hbounds :=
    activeL3PrimeExpMid_bounds_of_shift_exp_bounds
      n hlower hupper
  exact abs_sub_mid_le_half_width hbounds.1 hbounds.2

theorem activeL3PrimeWeight_mid_eq :
    ∀ n,
      activeL3PrimeWeightMid n =
        activeL3PrimeLogMid n * activeL3PrimeExpMid n := by
  intro n
  rfl

theorem activeL3PrimeWeight_rad_bound :
    ∀ n,
      (|activeL3PrimeLogMid n| + activeL3PrimeLogRad n) *
          activeL3PrimeExpRad n +
        activeL3PrimeLogRad n * |activeL3PrimeExpMid n| <=
          activeL3PrimeWeightRad n := by
  intro n
  dsimp [activeL3PrimeWeightRad]
  exact le_rfl

theorem activeL3PrimeWeightRad_eq_logRad_mul_expMid
    (n : PrimeShiftIndexL3) :
    activeL3PrimeWeightRad n =
      activeL3PrimeLogRad n * activeL3PrimeExpMid n := by
  dsimp [activeL3PrimeWeightRad, activeL3PrimeExpRad]
  rw [abs_of_nonneg (activeL3PrimeExpMid_nonneg n)]
  ring

theorem abs_activeL3PrimeWeightMid_eq
    (n : PrimeShiftIndexL3) :
    |activeL3PrimeWeightMid n| =
      |activeL3PrimeLogMid n| * activeL3PrimeExpMid n := by
  rw [activeL3PrimeWeightMid]
  rw [abs_mul]
  rw [abs_of_nonneg (activeL3PrimeExpMid_nonneg n)]

theorem activeL3PrimeWeightRad_nonneg (n : PrimeShiftIndexL3) :
    0 <= activeL3PrimeWeightRad n := by
  rw [activeL3PrimeWeightRad_eq_logRad_mul_expMid n]
  exact mul_nonneg (activeL3PrimeLogRad_nonneg n)
    (activeL3PrimeExpMid_nonneg n)
"""


def term_linearization_defs() -> str:
    return """
theorem primaryK11PositivePartPowerTightPrimeTermMid_eq_expMid_mul
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    primaryK11PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid i j n =
      activeL3PrimeExpMid n *
        (activeL3PrimeLogMid n *
          (primaryK11PositivePartPowerTightMinusRMid i j n +
            primaryK11PositivePartPowerTightPlusRMid i j n)) := by
  dsimp [primaryK11PositivePartPowerTightPrimeTermMid, activeL3PrimeWeightMid]
  ring

theorem primaryK11PositivePartPowerTightPrimeTermRad_eq_expMid_mul
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    primaryK11PositivePartPowerTightPrimeTermRad
        activeL3PrimeWeightMid activeL3PrimeWeightRad i j n =
      activeL3PrimeExpMid n *
        ((|activeL3PrimeLogMid n| + activeL3PrimeLogRad n) *
            (primaryK11PositivePartPowerTightMinusRRad i j n +
              primaryK11PositivePartPowerTightPlusRRad i j n) +
          activeL3PrimeLogRad n *
            |primaryK11PositivePartPowerTightMinusRMid i j n +
              primaryK11PositivePartPowerTightPlusRMid i j n|) := by
  dsimp [primaryK11PositivePartPowerTightPrimeTermRad]
  rw [activeL3PrimeWeightRad_eq_logRad_mul_expMid n]
  rw [abs_activeL3PrimeWeightMid_eq n]
  ring

theorem controlK9PositivePartPowerTightPrimeTermMid_eq_expMid_mul
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    controlK9PositivePartPowerTightPrimeTermMid activeL3PrimeWeightMid i j n =
      activeL3PrimeExpMid n *
        (activeL3PrimeLogMid n *
          (controlK9PositivePartPowerTightMinusRMid i j n +
            controlK9PositivePartPowerTightPlusRMid i j n)) := by
  dsimp [controlK9PositivePartPowerTightPrimeTermMid, activeL3PrimeWeightMid]
  ring

theorem controlK9PositivePartPowerTightPrimeTermRad_eq_expMid_mul
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) :
    controlK9PositivePartPowerTightPrimeTermRad
        activeL3PrimeWeightMid activeL3PrimeWeightRad i j n =
      activeL3PrimeExpMid n *
        ((|activeL3PrimeLogMid n| + activeL3PrimeLogRad n) *
            (controlK9PositivePartPowerTightMinusRRad i j n +
              controlK9PositivePartPowerTightPlusRRad i j n) +
          activeL3PrimeLogRad n *
            |controlK9PositivePartPowerTightMinusRMid i j n +
              controlK9PositivePartPowerTightPlusRMid i j n|) := by
  dsimp [controlK9PositivePartPowerTightPrimeTermRad]
  rw [activeL3PrimeWeightRad_eq_logRad_mul_expMid n]
  rw [abs_activeL3PrimeWeightMid_eq n]
  ring
"""


def receiver_lift_defs(prefix: str, theorem_prefix: str, k: int) -> str:
    r_receiver = (
        "primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_cardinal_hboxes"
        if k == 11
        else "controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_cardinal_hboxes"
    )
    r_theorem = (
        "primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_tight_cardinal_payload"
        if k == 11
        else "controlK9CenteredBSplineR9PrimeShiftPair_hbox_of_tight_cardinal_payload"
    )
    p_receiver = (
        "primaryK11AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes"
        if k == 11
        else "controlK9AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes"
    )
    p_theorem = (
        "primaryK11AnalyticP_entry_hbox_of_tight_R_and_log_exp_weight_hboxes"
        if k == 11
        else "controlK9AnalyticP_entry_hbox_of_tight_R_and_log_exp_weight_hboxes"
    )
    p_concrete_theorem = (
        "primaryK11AnalyticP_entry_hbox_of_tight_log_exp_weight_and_sum_checks"
        if k == 11
        else "controlK9AnalyticP_entry_hbox_of_tight_log_exp_weight_and_sum_checks"
    )
    analytic_p = (
        "_root_.Q3.PSDpd.CenteredCoeffBaseHboxImport.primaryK11AnalyticP"
        if k == 11
        else "_root_.Q3.PSDpd.CenteredCoeffBaseHboxImport.controlK9AnalyticP"
    )
    imported_p = "primaryK11P" if k == 11 else "controlK9P"
    imported_rad = "primaryK11PRadius" if k == 11 else "controlK9PRadius"
    finite_term = (
        "_root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.primaryK11FinitePrimeProfileTerm"
        if k == 11
        else "_root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.controlK9FinitePrimeProfileTerm"
    )
    return f"""
def {prefix}MinusRMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  {prefix}MinusCardMid i j n / bsplineAutocorrNorm {k}

def {prefix}MinusRRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  {prefix}MinusCardRad i j n / bsplineAutocorrNorm {k}

def {prefix}PlusRMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  {prefix}PlusCardMid i j n / bsplineAutocorrNorm {k}

def {prefix}PlusRRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  {prefix}PlusCardRad i j n / bsplineAutocorrNorm {k}

theorem {r_theorem} :
    (∀ i j n,
      |centeredBSplineR {k}
          ((({"primaryK11Center" if k == 11 else "controlK9Center"} j -
              {"primaryK11Center" if k == 11 else "controlK9Center"} i) -
            {"primaryK11PrimeShift" if k == 11 else "controlK9PrimeShift"} n) /
            {"primaryK11Ell" if k == 11 else "controlK9Ell"}) -
        {prefix}MinusRMid i j n| <=
          {prefix}MinusRRad i j n) ∧
    (∀ i j n,
      |centeredBSplineR {k}
          ((({"primaryK11Center" if k == 11 else "controlK9Center"} j -
              {"primaryK11Center" if k == 11 else "controlK9Center"} i) +
            {"primaryK11PrimeShift" if k == 11 else "controlK9PrimeShift"} n) /
            {"primaryK11Ell" if k == 11 else "controlK9Ell"}) -
        {prefix}PlusRMid i j n| <=
          {prefix}PlusRRad i j n) := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.{r_receiver}
      {prefix}MinusCardMid
      {prefix}MinusCardRad
      {prefix}PlusCardMid
      {prefix}PlusCardRad
      {prefix}MinusRMid
      {prefix}MinusRRad
      {prefix}PlusRMid
      {prefix}PlusRRad
      ({theorem_prefix}_of_tight_positivePartPower_payload).1
      ({theorem_prefix}_of_tight_positivePartPower_payload).2
      (fun i j n => by rfl)
      (fun i j n => by rw [{prefix}MinusRRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [{prefix}PlusRRad])

def {prefix}PrimeTermMid
    (weightMid : PrimeShiftIndexL3 -> Real)
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  weightMid n *
    ({prefix}MinusRMid i j n + {prefix}PlusRMid i j n)

def {prefix}PrimeTermRad
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  (|weightMid n| + weightRad n) *
      ({prefix}MinusRRad i j n + {prefix}PlusRRad i j n) +
    weightRad n *
      |{prefix}MinusRMid i j n + {prefix}PlusRMid i j n|

theorem {p_theorem}
    (logMid logRad expMid expRad weightMid weightRad :
      PrimeShiftIndexL3 -> Real)
    (hlog :
      ∀ n,
        |Real.log (activeL3PrimeBase n : Real) - logMid n| <= logRad n)
    (hexp :
      ∀ n,
        |Real.exp (-(activeL3PrimeShift n) / 2) - expMid n| <= expRad n)
    (hweightMid :
      ∀ n,
        weightMid n = logMid n * expMid n)
    (hweightRad :
      ∀ n,
        (|logMid n| + logRad n) * expRad n +
          logRad n * |expMid n| <= weightRad n)
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          {prefix}PrimeTermMid weightMid i j n) = {imported_p} i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          {prefix}PrimeTermRad weightMid weightRad i j n) <=
            {imported_rad} i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      {analytic_p} {imported_p} {imported_rad} := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.{p_receiver}
      logMid
      logRad
      expMid
      expRad
      weightMid
      weightRad
      {prefix}MinusRMid
      {prefix}MinusRRad
      {prefix}PlusRMid
      {prefix}PlusRRad
      ({prefix}PrimeTermMid weightMid)
      ({prefix}PrimeTermRad weightMid weightRad)
      hlog
      hexp
      hweightMid
      hweightRad
      ({r_theorem}).1
      ({r_theorem}).2
      (fun i j n => by rfl)
      (fun i j n => by rw [{prefix}PrimeTermRad])
      hmid
      hrad

theorem {p_concrete_theorem}
    (hmid :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          {prefix}PrimeTermMid activeL3PrimeWeightMid i j n) =
            {imported_p} i j)
    (hrad :
      ∀ i j,
        (∑ n : PrimeShiftIndexL3,
          {prefix}PrimeTermRad
              activeL3PrimeWeightMid activeL3PrimeWeightRad i j n) <=
            {imported_rad} i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      {analytic_p} {imported_p} {imported_rad} := by
  exact
    {p_theorem}
      activeL3PrimeLogMid
      activeL3PrimeLogRad
      activeL3PrimeExpMid
      activeL3PrimeExpRad
      activeL3PrimeWeightMid
      activeL3PrimeWeightRad
      activeL3PrimeLog_hbox_of_tight_payload
      activeL3PrimeExp_exact_hbox
      activeL3PrimeWeight_mid_eq
      activeL3PrimeWeight_rad_bound
      hmid
      hrad

theorem {prefix}FinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n,
        |{"primaryK11PrimeWeight" if k == 11 else "controlK9PrimeWeight"} n -
          weightMid n| <= weightRad n) :
    ∀ i j n,
      |{finite_term} i j n -
        {prefix}PrimeTermMid weightMid i j n| <=
          {prefix}PrimeTermRad weightMid weightRad i j n := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.{"primaryK11FinitePrimeProfileTerm_hbox_of_weight_and_R_pair_hboxes" if k == 11 else "controlK9FinitePrimeProfileTerm_hbox_of_weight_and_R_pair_hboxes"}
      weightMid
      weightRad
      {prefix}MinusRMid
      {prefix}MinusRRad
      {prefix}PlusRMid
      {prefix}PlusRRad
      ({prefix}PrimeTermMid weightMid)
      ({prefix}PrimeTermRad weightMid weightRad)
      hweight
      ({r_theorem}).1
      ({r_theorem}).2
      (fun i j n => by rfl)
      (fun i j n => by rw [{prefix}PrimeTermRad])
"""


def block(prefix: str, theorem_prefix: str, k: int, center: str, shift: str, ell: str, hell: str) -> str:
    degree_mono = "positivePartPower23_mono" if k == 11 else "positivePartPower19_mono"
    receiver = (
        "primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_positivePartPower_hboxes"
        if k == 11
        else "controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox_of_positivePartPower_hboxes"
    )
    return f"""
{arg_defs(prefix, k, center, shift, ell)}
{payload_defs(prefix, k)}

private theorem {prefix}MinusArg_bounds
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) :
    {prefix}MinusArgLower i j n m <=
      bsplineScale {k} *
          ((({center} j - {center} i) -
            {shift} n) / {ell}) +
        (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
        (m : Real) ∧
    bsplineScale {k} *
          ((({center} j - {center} i) -
            {shift} n) / {ell}) +
        (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
        (m : Real) <=
      {prefix}MinusArgUpper i j n m := by
  have hs := activeL3PrimeShift_tight_bounds n
  have h :=
    scaled_minus_arg_bounds
      (center := {center} j - {center} i)
      (shift := activeL3PrimeShift n)
      (lo := activeL3PrimeShiftLower n)
      (hi := activeL3PrimeShiftUpper n)
      (ell := {ell})
      (scale := bsplineScale {k})
      (offset := (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2))
      (m := (m : Real))
      {hell} (le_of_lt (bsplineScale_pos {k})) hs.1 hs.2
  simpa [{prefix}MinusArgLower, {prefix}MinusArgUpper, {shift}] using h

private theorem {prefix}PlusArg_bounds
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat) :
    {prefix}PlusArgLower i j n m <=
      bsplineScale {k} *
          ((({center} j - {center} i) +
            {shift} n) / {ell}) +
        (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
        (m : Real) ∧
    bsplineScale {k} *
          ((({center} j - {center} i) +
            {shift} n) / {ell}) +
        (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
        (m : Real) <=
      {prefix}PlusArgUpper i j n m := by
  have hs := activeL3PrimeShift_tight_bounds n
  have h :=
    scaled_plus_arg_bounds
      (center := {center} j - {center} i)
      (shift := activeL3PrimeShift n)
      (lo := activeL3PrimeShiftLower n)
      (hi := activeL3PrimeShiftUpper n)
      (ell := {ell})
      (scale := bsplineScale {k})
      (offset := (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2))
      (m := (m : Real))
      {hell} (le_of_lt (bsplineScale_pos {k})) hs.1 hs.2
  simpa [{prefix}PlusArgLower, {prefix}PlusArgUpper, {shift}] using h

private theorem {prefix}Minus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (_hm : m ∈ Finset.range (bsplineAutocorrDegree {k} + 2)) :
    |positivePartPower (bsplineAutocorrDegree {k})
        (bsplineScale {k} *
            ((({center} j - {center} i) -
              {shift} n) / {ell}) +
          (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      {prefix}MinusMid i j n m| <=
        {prefix}MinusRad i j n m := by
  have hb := {prefix}MinusArg_bounds i j n m
  have h :=
    positivePartPower_hbox_of_bounds
      (d := bsplineAutocorrDegree {k})
      (x := bsplineScale {k} *
            ((({center} j - {center} i) -
              {shift} n) / {ell}) +
          (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
          (m : Real))
      (lo := {prefix}MinusArgLower i j n m)
      (hi := {prefix}MinusArgUpper i j n m)
      {degree_mono} hb.1 hb.2
  simpa [{prefix}MinusMid, {prefix}MinusRad] using h

private theorem {prefix}Plus_hbox
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) (m : Nat)
    (_hm : m ∈ Finset.range (bsplineAutocorrDegree {k} + 2)) :
    |positivePartPower (bsplineAutocorrDegree {k})
        (bsplineScale {k} *
            ((({center} j - {center} i) +
              {shift} n) / {ell}) +
          (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
          (m : Real)) -
      {prefix}PlusMid i j n m| <=
        {prefix}PlusRad i j n m := by
  have hb := {prefix}PlusArg_bounds i j n m
  have h :=
    positivePartPower_hbox_of_bounds
      (d := bsplineAutocorrDegree {k})
      (x := bsplineScale {k} *
            ((({center} j - {center} i) +
              {shift} n) / {ell}) +
          (((bsplineAutocorrDegree {k} + 1 : Nat) : Real) / 2) -
          (m : Real))
      (lo := {prefix}PlusArgLower i j n m)
      (hi := {prefix}PlusArgUpper i j n m)
      {degree_mono} hb.1 hb.2
  simpa [{prefix}PlusMid, {prefix}PlusRad] using h

theorem {theorem_prefix}_of_tight_positivePartPower_payload :
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree {k})
          (bsplineScale {k} *
            ((({center} j - {center} i) -
              {shift} n) / {ell})) -
        {prefix}MinusCardMid i j n| <=
          {prefix}MinusCardRad i j n) ∧
    (∀ i j n,
      |centeredCardinalBSpline (bsplineAutocorrDegree {k})
          (bsplineScale {k} *
            ((({center} j - {center} i) +
              {shift} n) / {ell})) -
        {prefix}PlusCardMid i j n| <=
          {prefix}PlusCardRad i j n) := by
  exact
    _root_.Q3.PSDpd.CenteredCoeffPrimeEntryHboxImport.{receiver}
      {prefix}MinusMid
      {prefix}MinusRad
      {prefix}PlusMid
      {prefix}PlusRad
      {prefix}MinusTermMid
      {prefix}MinusTermRad
      {prefix}PlusTermMid
      {prefix}PlusTermRad
      {prefix}MinusCardMid
      {prefix}MinusCardRad
      {prefix}PlusCardMid
      {prefix}PlusCardRad
      {prefix}Minus_hbox
      {prefix}Plus_hbox
      (fun i j n m => by rfl)
      (fun i j n m => by rw [{prefix}MinusTermRad])
      (fun i j n m => by rfl)
      (fun i j n m => by rw [{prefix}PlusTermRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [{prefix}MinusCardRad])
      (fun i j n => by rfl)
      (fun i j n => by rw [{prefix}PlusCardRad])

{receiver_lift_defs(prefix, theorem_prefix, k)}
"""


def main() -> None:
    bases = parse_nat_entries("activeL3PrimeBaseEntry")

    header = """import Q3.Proofs.PSD_CenteredCoeffPrimeEntryHboxImport
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowBucket0Auto_0_249
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowBucket0Auto_250_499

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 5000000

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimePositivePartTightImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffPrimeDictionaryBoundsImport

/-!
Step33A.1 tight scalar positive-part-power payload.

The coarse payload in `PSD_CenteredCoeffPrimeEntryHboxImport` remains available
as a fallback.  This module builds a sharper symbolic midpoint/radius payload
from certified PrimeCert log intervals for the active L=3 prime dictionary and
feeds the existing positivePartPower -> summand -> cardinal receiver chain.
-/
"""

    core = f"""
{match_cases("activeL3PrimeLogLower", bases, "l")}

def activeL3PrimeLogLower (n : PrimeShiftIndexL3) : Real :=
  activeL3PrimeLogLowerEntry n.1

{match_cases("activeL3PrimeLogUpper", bases, "u")}

def activeL3PrimeLogUpper (n : PrimeShiftIndexL3) : Real :=
  activeL3PrimeLogUpperEntry n.1

{log_bound_theorem(bases, "activeL3PrimeLogLower_le_log", "activeL3PrimeLogLower", "lower")}

{log_bound_theorem(bases, "activeL3PrimeLog_le_upper", "activeL3PrimeLogUpper", "upper")}

def activeL3PrimeShiftLower (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeExponent n : Real) * activeL3PrimeLogLower n

def activeL3PrimeShiftUpper (n : PrimeShiftIndexL3) : Real :=
  (activeL3PrimeExponent n : Real) * activeL3PrimeLogUpper n

theorem activeL3PrimeShift_tight_bounds (n : PrimeShiftIndexL3) :
    activeL3PrimeShiftLower n <= activeL3PrimeShift n ∧
      activeL3PrimeShift n <= activeL3PrimeShiftUpper n := by
  have hexp_nonneg : 0 <= (activeL3PrimeExponent n : Real) := by positivity
  constructor
  · simpa [activeL3PrimeShift, activeL3PrimeShiftLower] using
      mul_le_mul_of_nonneg_left
        (activeL3PrimeLogLower_le_log n) hexp_nonneg
  · simpa [activeL3PrimeShift, activeL3PrimeShiftUpper] using
      mul_le_mul_of_nonneg_left
        (activeL3PrimeLog_le_upper n) hexp_nonneg

private theorem abs_sub_mid_le_half_width {{lo y hi : Real}}
    (hlo : lo <= y) (hhi : y <= hi) :
    |y - ((lo + hi) / 2)| <= (hi - lo) / 2 := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

private theorem positivePartPower_succ_mono (d : Nat) :
    Monotone (positivePartPower (d + 1)) := by
  intro x y hxy
  rw [positivePartPower_succ_eq_max d x, positivePartPower_succ_eq_max d y]
  exact pow_le_pow_left₀ (le_max_right x 0) (max_le_max hxy le_rfl) (d + 1)

private theorem positivePartPower23_mono :
    Monotone (positivePartPower (bsplineAutocorrDegree 11)) := by
  simpa [bsplineAutocorrDegree] using positivePartPower_succ_mono 22

private theorem positivePartPower19_mono :
    Monotone (positivePartPower (bsplineAutocorrDegree 9)) := by
  simpa [bsplineAutocorrDegree] using positivePartPower_succ_mono 18

private theorem positivePartPower_hbox_of_bounds
    {{d : Nat}} {{x lo hi : Real}}
    (hmono : Monotone (positivePartPower d))
    (hlo : lo <= x) (hhi : x <= hi) :
    |positivePartPower d x -
      ((positivePartPower d lo + positivePartPower d hi) / 2)| <=
        (positivePartPower d hi - positivePartPower d lo) / 2 :=
  abs_sub_mid_le_half_width (hmono hlo) (hmono hhi)

{log_exp_weight_payload_defs()}

private theorem scaled_minus_arg_bounds
    (center shift lo hi ell scale offset m : Real)
    (hell : 0 < ell) (hscale : 0 <= scale)
    (hlo : lo <= shift) (hhi : shift <= hi) :
    scale * ((center - hi) / ell) + offset - m <=
      scale * ((center - shift) / ell) + offset - m ∧
    scale * ((center - shift) / ell) + offset - m <=
      scale * ((center - lo) / ell) + offset - m := by
  have hsub_low : center - hi <= center - shift := by linarith
  have hdiv_low :
      (center - hi) / ell <= (center - shift) / ell :=
    div_le_div_of_nonneg_right hsub_low (le_of_lt hell)
  have hmul_low :
      scale * ((center - hi) / ell) <=
        scale * ((center - shift) / ell) :=
    mul_le_mul_of_nonneg_left hdiv_low hscale
  have hsub_high : center - shift <= center - lo := by linarith
  have hdiv_high :
      (center - shift) / ell <= (center - lo) / ell :=
    div_le_div_of_nonneg_right hsub_high (le_of_lt hell)
  have hmul_high :
      scale * ((center - shift) / ell) <=
        scale * ((center - lo) / ell) :=
    mul_le_mul_of_nonneg_left hdiv_high hscale
  constructor <;> linarith

private theorem scaled_plus_arg_bounds
    (center shift lo hi ell scale offset m : Real)
    (hell : 0 < ell) (hscale : 0 <= scale)
    (hlo : lo <= shift) (hhi : shift <= hi) :
    scale * ((center + lo) / ell) + offset - m <=
      scale * ((center + shift) / ell) + offset - m ∧
    scale * ((center + shift) / ell) + offset - m <=
      scale * ((center + hi) / ell) + offset - m := by
  have hsub_low : center + lo <= center + shift := by linarith
  have hdiv_low :
      (center + lo) / ell <= (center + shift) / ell :=
    div_le_div_of_nonneg_right hsub_low (le_of_lt hell)
  have hmul_low :
      scale * ((center + lo) / ell) <=
        scale * ((center + shift) / ell) :=
    mul_le_mul_of_nonneg_left hdiv_low hscale
  have hsub_high : center + shift <= center + hi := by linarith
  have hdiv_high :
      (center + shift) / ell <= (center + hi) / ell :=
    div_le_div_of_nonneg_right hsub_high (le_of_lt hell)
  have hmul_high :
      scale * ((center + shift) / ell) <=
        scale * ((center + hi) / ell) :=
    mul_le_mul_of_nonneg_left hdiv_high hscale
  constructor <;> linarith
"""

    footer = """
end CenteredCoeffPrimePositivePartTightImport
end PSDpd
end Q3
"""

    text = "\n".join(
        [
            header,
            core,
            block(
                "primaryK11PositivePartPowerTight",
                "primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox",
                11,
                "primaryK11Center",
                "primaryK11PrimeShift",
                "primaryK11Ell",
                "primaryK11_hell",
            ),
            block(
                "controlK9PositivePartPowerTight",
                "controlK9CenteredCardinalBSpline19PrimeShiftPair_hbox",
                9,
                "controlK9Center",
                "controlK9PrimeShift",
                "controlK9Ell",
                "controlK9_hell",
            ),
            term_linearization_defs(),
            footer,
        ]
    )
    OUT.write_text(text)
    print(f"wrote {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
