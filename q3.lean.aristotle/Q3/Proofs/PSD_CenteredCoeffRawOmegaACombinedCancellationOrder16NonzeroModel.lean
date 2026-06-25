import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NormalForm
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Nonzero model split for the Step33A.1-A sub0 order-16
combined-cancellation source.

The zero-model rawProduct17 branch is Lean-checked but arithmetically too large.
This file records the next safe algebraic split selected by route review: keep
the nominal component-product derivative as a nonzero model, and bound only the
actual-minus-nominal derivative plus the active-vs-nominal scale defect.

This file does not claim the final interval certificate.  It only exposes the
exact source split that a later rational Horner/range payload must certify.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Coefficients of the degree-29 polynomial obtained by differentiating the
repository's degree-45 residual Taylor polynomial sixteen times. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff
    (j : Fin 30) : Rat :=
  ((16 + j.1).descFactorial 16 : Rat) *
    primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
      ⟨16 + j.1, by
        unfold primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        omega⟩

/-- The rational polynomial surface for the nonzero model, in the direct
interval checker's centered-Taylor convention. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff eta

/-- Exact sum-of-absolute-coefficients bound for the nonzero degree-29 model on
the active radius `1/20` cell.  This is a proof-grade range envelope, not a
Horner-stage certificate. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelAbsBoundRat :
    Rat :=
  ∑ i : Fin 30,
    |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff i| *
      ((1 : Rat) / 20) ^ i.1

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16NonzeroModel_sumAbsBudget_fail_rat :
    ((1866608532757 : Rat) /
        500000000000000000000000000000) <
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelAbsBoundRat := by
  native_decide

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeffList :
    List Rat :=
  List.ofFn
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff

/-- One-cell symmetric Horner interval step for
`x = eta - 1/20 ∈ [-1/20, 1/20]`.  This is only an exact route audit for the
natural single-cell Horner rows; it is not a final interval certificate. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelHornerIntervalStep
    (c : Rat) (acc : Rat × Rat) : Rat × Rat :=
  let m := max |acc.1| |acc.2| * ((1 : Rat) / 20)
  (c - m, c + m)

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelHornerInterval :
    Rat × Rat :=
  match
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeffList.reverse
  with
  | [] => (0, 0)
  | c :: cs =>
      cs.foldl
        (fun acc c =>
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelHornerIntervalStep
            c acc)
        (c, c)

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16NonzeroModel_singleCellHornerLower_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelHornerInterval.1 <
      step33Sub0CombinedCancellationTargetLower := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16NonzeroModel_singleCellHornerUpper_pass_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelHornerInterval.2 <=
      step33Sub0CombinedCancellationTargetUpper := by
  native_decide

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCenterValueRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff
    ⟨0, by omega⟩

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16NonzeroModel_centerLower_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCenterValueRat <
      step33Sub0CombinedCancellationTargetLower := by
  native_decide

/-- Lower endpoint of the current exact one-cell Horner audit for the nonzero
model.  This is an audit endpoint, not yet a final range payload row. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCurrentLowerRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelHornerInterval.1

/-- Upper endpoint of the current exact one-cell Horner audit for the nonzero
model.  This is an audit endpoint, not yet a final range payload row. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCurrentUpperRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelHornerInterval.2

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasLowerRat :
    Rat :=
  step33Sub0CombinedCancellationTargetLower -
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCurrentLowerRat

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasUpperRat :
    Rat :=
  step33Sub0CombinedCancellationTargetUpper -
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCurrentUpperRat

/-- Midpoint bias selected inside the exact rational feasible window. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
    Rat :=
  (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasLowerRat +
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasUpperRat) / 2

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16NonzeroModel_bias_window_nonempty_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasLowerRat <=
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasUpperRat := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_singleCellHornerLower_pass_rat :
    step33Sub0CombinedCancellationTargetLower <=
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCurrentLowerRat +
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_singleCellHornerUpper_pass_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCurrentUpperRat +
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat <=
      step33Sub0CombinedCancellationTargetUpper := by
  native_decide

/-- Biased nonzero model selected by the exact rational feasible window above.
This direct definition records the route split; a later payload can expose the
equivalent coefficient-row form for the Horner checker. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
    (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta +
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
      Real)

/-- Coefficient-row form of the biased nonzero model.  The bias only changes
the constant row in the same centered-Taylor convention as the existing
Horner checker. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelBiasCoeff
    (j : Fin 30) : Rat :=
  if j.1 = 0 then
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat
  else
    0

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
    (j : Fin 30) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff j +
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelBiasCoeff
      j

/-- The coefficient-row biased model in the repository's rawOmega Taylor
polynomial convention. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeffPoly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
    eta

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModelPoly_eq
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
        eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta +
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) := by
  rfl

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModelCoeffPoly_eq
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeffPoly
        eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
        eta := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeffPoly
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
  rw [rawOmegaATaylorPolynomial_add_coeff]
  unfold
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
  congr 1
  unfold rawOmegaATaylorPolynomial
  rw [Fin.sum_univ_succ]
  simp [
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelBiasCoeff,
    pow_zero]

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeffList :
    List Rat :=
  List.ofFn
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerIntervalOfList
    (coeffs : List Rat) : Rat × Rat :=
  match coeffs.reverse with
  | [] => (0, 0)
  | c :: cs =>
      cs.foldl
        (fun acc c =>
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelHornerIntervalStep
            c acc)
        (c, c)

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerStageInterval
    (i : Fin 30) : Rat × Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerIntervalOfList
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeffList.drop
      i.1)

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
    (i : Fin 30) : Rat :=
  (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerStageInterval
    i).1

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
    (i : Fin 30) : Rat :=
  (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerStageInterval
    i).2

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData :
    Step33Sub0CombinedCancellationIntervalCert where
  cellL := 0
  cellU := (1 : Rat) / 10
  center := (1 : Rat) / 20
  degree := 29
  coeff := primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
  remainderAbs := 0
  polyLower :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
      ⟨0, by omega⟩
  polyUpper :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
      ⟨0, by omega⟩

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData :
    Step33Sub0CombinedCancellationHornerRangeCert
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
    where
  stageLower :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
  stageUpper :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_targetLower_pass_rat :
    step33Sub0CombinedCancellationTargetLower <=
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_targetUpper_pass_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper <=
      step33Sub0CombinedCancellationTargetUpper := by
  native_decide

private theorem primaryFiniteRow0Parent0Split100Sub0_abs_le_max_abs_of_mem_interval
    {lower upper y : Real}
    (hy : lower <= y ∧ y <= upper) :
    |y| <= max |lower| |upper| := by
  have hLowerAbs : |lower| <= max |lower| |upper| :=
    le_max_left |lower| |upper|
  have hUpperAbs : |upper| <= max |lower| |upper| :=
    le_max_right |lower| |upper|
  have hLower := abs_le.mp hLowerAbs
  have hUpper := abs_le.mp hUpperAbs
  rw [abs_le]
  constructor
  · exact hLower.1.trans hy.1
  · exact hy.2.trans hUpper.2

private theorem primaryFiniteRow0Parent0Split100Sub0_mul_mem_symmetric_interval_of_mem_interval
    {q y lower upper radius : Real}
    (hy : lower <= y ∧ y <= upper)
    (hq : |q| <= radius)
    (hradius : 0 <= radius) :
    let margin := max |lower| |upper| * radius;
    -margin <= q * y ∧ q * y <= margin := by
  intro margin
  have hYAbs :
      |y| <= max |lower| |upper| :=
    primaryFiniteRow0Parent0Split100Sub0_abs_le_max_abs_of_mem_interval hy
  have hMaxNonneg : 0 <= max |lower| |upper| :=
    le_trans (abs_nonneg lower) (le_max_left |lower| |upper|)
  have hProd :
      |q * y| <= margin := by
    have hMul :=
      mul_le_mul hq hYAbs (abs_nonneg y) hradius
    dsimp [margin]
    rw [abs_mul]
    nlinarith
  exact abs_le.mp hProd

private theorem primaryFiniteRow0Parent0Split100Sub0_ratCast_max_abs
    (a b : Rat) :
    ((max |a| |b| : Rat) : Real) = max |(a : Real)| |(b : Real)| := by
  by_cases h : |a| <= |b|
  · have hReal : |(a : Real)| <= |(b : Real)| := by
      exact_mod_cast h
    rw [max_eq_right h, max_eq_right hReal]
    norm_num [Rat.cast_abs]
  · have hRat : |b| <= |a| := le_of_not_ge h
    have hReal : |(b : Real)| <= |(a : Real)| := by
      exact_mod_cast hRat
    rw [max_eq_left hRat, max_eq_left hReal]
    norm_num [Rat.cast_abs]

private theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStage29_bounds
    {eta : Real}
    (_hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
        ⟨29, by omega⟩ : Real) <=
        Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          29 eta ∧
      Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          29 eta <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
          ⟨29, by omega⟩ : Real) := by
  have hTail :
      Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          29 eta =
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨29, by omega⟩ : Real) := by
    unfold Step33Sub0CombinedCancellationIntervalCert.hornerTail
    change
      (Finset.sum (Finset.univ : Finset (Fin 30))
        (fun j : Fin 30 =>
          if _h : 29 <= j.1 then
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.coeff
              j : Real) *
              (eta -
                (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.center :
                  Real)) ^ (j.1 - 29)
          else
            0)) =
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨29, by omega⟩ : Real)
    rw [Finset.sum_eq_single (a := (⟨29, by omega⟩ : Fin 30))]
    · simp [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData,
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff,
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelBiasCoeff]
    · intro b _hb hbne
      have hbLt : b.1 < 30 := b.2
      by_cases h : 29 <= b.1
      · have hbEqVal : b.1 = 29 := by omega
        have hbEq : b = (⟨29, by omega⟩ : Fin 30) := by
          ext
          exact hbEqVal
        exact False.elim (hbne hbEq)
      · simp [h]
    · intro hmem
      simp at hmem
  constructor
  · rw [hTail]
    have hRat :
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
            ⟨29, by omega⟩ <=
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
            ⟨29, by omega⟩ := by
      native_decide
    exact_mod_cast hRat
  · rw [hTail]
    have hRat :
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
            ⟨29, by omega⟩ <=
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
            ⟨29, by omega⟩ := by
      native_decide
    exact_mod_cast hRat

private def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
    (i j : Nat) (eta : Real) : Real :=
  if hj : j < 30 then
    if _hij : i <= j then
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
        ⟨j, hj⟩ : Real) * (eta - (1 : Real) / 20) ^ (j - i)
    else
      0
  else
    0

private def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTail
    (i : Nat) (eta : Real) : Real :=
  ∑ j ∈ Finset.range 30,
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
      i j eta

private theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_natTailTerm_step
    {i j : Nat} (hi : i < 29) (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
        i j eta =
      if j = i then
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨i, by omega⟩ : Real)
      else
        (eta - (1 : Real) / 20) *
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
            (i + 1) j eta := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
  by_cases hj : j < 30
  · by_cases hji : j = i
    · subst j
      simp [hj]
    · by_cases hij : i <= j
      · have hijSucc : i + 1 <= j := by omega
        have hsub : j - i = (j - (i + 1)) + 1 := by omega
        simp [hj, hji, hij, hijSucc, hsub, pow_succ]
        ring
      · have hijSuccFalse : ¬i + 1 <= j := by omega
        simp [hj, hji, hij, hijSuccFalse]
  · have hji : j ≠ i := by omega
    simp [hj, hji]

private theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerTail_eq_natTail
    (i : Nat) (eta : Real) :
    Step33Sub0CombinedCancellationIntervalCert.hornerTail
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
        i eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTail
        i eta := by
  unfold
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTail
    Step33Sub0CombinedCancellationIntervalCert.hornerTail
  rw [← Fin.sum_univ_eq_sum_range
    (f :=
      fun j : Nat =>
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
          i j eta)
    30]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
  have hjLt : j.1 < 30 := j.2
  simp [
    hjLt,
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData]

private theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_natTail_step
    {i : Nat} (hi : i < 29) (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTail
        i eta =
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
        ⟨i, by omega⟩ : Real) +
        (eta - (1 : Real) / 20) *
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTail
            (i + 1) eta := by
  let q : Real := eta - (1 : Real) / 20
  let c : Real :=
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
      ⟨i, by omega⟩ : Real)
  let termNext : Nat -> Real := fun j =>
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
      (i + 1) j eta
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTail
  calc
    ∑ j ∈ Finset.range 30,
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
          i j eta =
        ∑ j ∈ Finset.range 30,
          if j = i then c else q * termNext j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          dsimp [c, q, termNext]
          exact
            primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_natTailTerm_step
              hi eta
    _ =
        (∑ j ∈ Finset.range 30, if j = i then c else 0) +
          ∑ j ∈ Finset.range 30, if j = i then 0 else q * termNext j := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hji : j = i <;> simp [hji]
    _ =
        c + q * ∑ j ∈ Finset.range 30, termNext j := by
          have hiMem : i ∈ Finset.range 30 := by
            exact Finset.mem_range.mpr (by omega)
          have hFirst :
              (∑ j ∈ Finset.range 30, if j = i then c else 0) = c := by
            rw [Finset.sum_ite_eq']
            simp [hiMem]
          have hSecond :
              (∑ j ∈ Finset.range 30, if j = i then 0 else q * termNext j) =
                q * ∑ j ∈ Finset.range 30, termNext j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hji : j = i
            · subst j
              have hnot : ¬i + 1 <= i := by omega
              simp [
                termNext,
                primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm,
                hnot]
            · simp [hji, termNext]
          rw [hFirst, hSecond]
    _ =
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨i, by omega⟩ : Real) +
        (eta - (1 : Real) / 20) *
          ∑ j ∈ Finset.range 30,
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelNatTailTerm
              (i + 1) j eta := by
          rfl

private theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds
    {i : Nat} (hi : i < 29)
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hNext :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
          ⟨i + 1, by omega⟩ : Real) <=
          Step33Sub0CombinedCancellationIntervalCert.hornerTail
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
            (i + 1) eta ∧
        Step33Sub0CombinedCancellationIntervalCert.hornerTail
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
            (i + 1) eta <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
            ⟨i + 1, by omega⟩ : Real))
    (hLowerStep :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
          ⟨i, by omega⟩ : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨i, by omega⟩ : Real) -
          max
            |(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
              ⟨i + 1, by omega⟩ : Real)|
            |(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
              ⟨i + 1, by omega⟩ : Real)| *
            ((1 : Real) / 20))
    (hUpperStep :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨i, by omega⟩ : Real) +
          max
            |(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
              ⟨i + 1, by omega⟩ : Real)|
            |(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
              ⟨i + 1, by omega⟩ : Real)| *
            ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
          ⟨i, by omega⟩ : Real)) :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
        ⟨i, by omega⟩ : Real) <=
        Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          i eta ∧
      Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          i eta <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
          ⟨i, by omega⟩ : Real) := by
  let q : Real := eta - (1 : Real) / 20
  have hRadius :
      |q| <= (1 : Real) / 20 := by
    dsimp [q]
    simpa using
      primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth hEta
  have hProd :=
    primaryFiniteRow0Parent0Split100Sub0_mul_mem_symmetric_interval_of_mem_interval
      (q := q)
      (y :=
        Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          (i + 1) eta)
      (lower :=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
          ⟨i + 1, by omega⟩ : Real))
      (upper :=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
          ⟨i + 1, by omega⟩ : Real))
      (radius := (1 : Real) / 20)
      hNext hRadius (by norm_num)
  dsimp at hProd
  have hTail :
      Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          i eta =
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨i, by omega⟩ : Real) +
          q *
            Step33Sub0CombinedCancellationIntervalCert.hornerTail
              primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
              (i + 1) eta := by
    rw [
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerTail_eq_natTail,
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_natTail_step
        hi,
      ← primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerTail_eq_natTail]
  constructor
  · rw [hTail]
    linarith [hLowerStep, hProd.1]
  · rw [hTail]
    linarith [hUpperStep, hProd.2]

private theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
    {i : Nat} (hi : i < 29)
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hNext :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
          ⟨i + 1, by omega⟩ : Real) <=
          Step33Sub0CombinedCancellationIntervalCert.hornerTail
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
            (i + 1) eta ∧
        Step33Sub0CombinedCancellationIntervalCert.hornerTail
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
            (i + 1) eta <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
            ⟨i + 1, by omega⟩ : Real))
    (hLowerStepRat :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
          ⟨i, by omega⟩ <=
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨i, by omega⟩ -
          max
            |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
              ⟨i + 1, by omega⟩|
            |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
              ⟨i + 1, by omega⟩| *
            ((1 : Rat) / 20))
    (hUpperStepRat :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          ⟨i, by omega⟩ +
          max
            |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
              ⟨i + 1, by omega⟩|
            |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
              ⟨i + 1, by omega⟩| *
            ((1 : Rat) / 20) <=
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
          ⟨i, by omega⟩) :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
        ⟨i, by omega⟩ : Real) <=
        Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          i eta ∧
      Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          i eta <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
          ⟨i, by omega⟩ : Real) := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds
      hi hEta hNext ?_ ?_
  · have hReal :
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
            ⟨i, by omega⟩ : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
              ⟨i, by omega⟩ : Real) -
            ((max
              |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
                ⟨i + 1, by omega⟩|
              |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
                ⟨i + 1, by omega⟩| *
              ((1 : Rat) / 20) : Rat) : Real) := by
      exact_mod_cast hLowerStepRat
    simpa [Rat.cast_mul,
      primaryFiniteRow0Parent0Split100Sub0_ratCast_max_abs,
      Rat.cast_abs] using hReal
  · have hReal :
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
              ⟨i, by omega⟩ : Real) +
            ((max
              |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
                ⟨i + 1, by omega⟩|
              |primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
                ⟨i + 1, by omega⟩| *
              ((1 : Rat) / 20) : Rat) : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
            ⟨i, by omega⟩ : Real) := by
      exact_mod_cast hUpperStepRat
    simpa [Rat.cast_mul,
      primaryFiniteRow0Parent0Split100Sub0_ratCast_max_abs,
      Rat.cast_abs] using hReal

private theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStage28_bounds
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageLower
        ⟨28, by omega⟩ : Real) <=
        Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          28 eta ∧
      Step33Sub0CombinedCancellationIntervalCert.hornerTail
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          28 eta <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelStageUpper
          ⟨28, by omega⟩ : Real) := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
      (i := 28) (by omega) hEta
      (primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStage29_bounds
        hEta)
      ?_ ?_
  · native_decide
  · native_decide

private theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_horner_valid :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData.Valid := by
  refine
    { stage_bounds := ?_
      outputLower := ?_
      outputUpper := ?_ }
  · intro i eta hEtaData
    have hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData]
        using hEtaData
    have h29 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStage29_bounds
        hEta
    have h28 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStage28_bounds
        hEta
    have h27 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 27) (by omega) hEta h28 (by native_decide)
        (by native_decide)
    have h26 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 26) (by omega) hEta h27 (by native_decide)
        (by native_decide)
    have h25 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 25) (by omega) hEta h26 (by native_decide)
        (by native_decide)
    have h24 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 24) (by omega) hEta h25 (by native_decide)
        (by native_decide)
    have h23 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 23) (by omega) hEta h24 (by native_decide)
        (by native_decide)
    have h22 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 22) (by omega) hEta h23 (by native_decide)
        (by native_decide)
    have h21 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 21) (by omega) hEta h22 (by native_decide)
        (by native_decide)
    have h20 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 20) (by omega) hEta h21 (by native_decide)
        (by native_decide)
    have h19 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 19) (by omega) hEta h20 (by native_decide)
        (by native_decide)
    have h18 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 18) (by omega) hEta h19 (by native_decide)
        (by native_decide)
    have h17 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 17) (by omega) hEta h18 (by native_decide)
        (by native_decide)
    have h16 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 16) (by omega) hEta h17 (by native_decide)
        (by native_decide)
    have h15 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 15) (by omega) hEta h16 (by native_decide)
        (by native_decide)
    have h14 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 14) (by omega) hEta h15 (by native_decide)
        (by native_decide)
    have h13 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 13) (by omega) hEta h14 (by native_decide)
        (by native_decide)
    have h12 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 12) (by omega) hEta h13 (by native_decide)
        (by native_decide)
    have h11 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 11) (by omega) hEta h12 (by native_decide)
        (by native_decide)
    have h10 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 10) (by omega) hEta h11 (by native_decide)
        (by native_decide)
    have h9 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 9) (by omega) hEta h10 (by native_decide)
        (by native_decide)
    have h8 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 8) (by omega) hEta h9 (by native_decide)
        (by native_decide)
    have h7 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 7) (by omega) hEta h8 (by native_decide)
        (by native_decide)
    have h6 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 6) (by omega) hEta h7 (by native_decide)
        (by native_decide)
    have h5 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 5) (by omega) hEta h6 (by native_decide)
        (by native_decide)
    have h4 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 4) (by omega) hEta h5 (by native_decide)
        (by native_decide)
    have h3 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 3) (by omega) hEta h4 (by native_decide)
        (by native_decide)
    have h2 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 2) (by omega) hEta h3 (by native_decide)
        (by native_decide)
    have h1 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 1) (by omega) hEta h2 (by native_decide)
        (by native_decide)
    have h0 :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_hornerStageStep_bounds_rat
        (i := 0) (by omega) hEta h1 (by native_decide)
        (by native_decide)
    fin_cases i
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h0
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h1
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h2
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h3
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h4
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h5
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h6
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h7
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h8
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h9
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h10
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h11
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h12
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h13
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h14
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h15
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h16
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h17
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h18
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h19
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h20
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h21
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h22
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h23
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h24
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h25
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h26
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h27
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h28
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData] using
        h29
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData,
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData]
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelHornerRangeData,
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_poly_range
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
        Real) <=
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta ∧
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
          Real) := by
  have hRange :=
    Step33Sub0CombinedCancellationHornerRangeCert.Valid.poly_range_unit_cell
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_horner_valid
      rfl
      rfl
      eta
      hEta
  have hPoly :
      Step33Sub0CombinedCancellationIntervalCert.poly
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
          eta =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta := by
    unfold
      Step33Sub0CombinedCancellationIntervalCert.poly
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData
    change
      rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelCoeff
          eta =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta
    exact
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModelCoeffPoly_eq
        eta
  simpa [hPoly] using hRange

/-- Exact symmetric order-16 budget obtained from the chosen target interval. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16AbsRat :
    Rat :=
  max |step33Sub0CombinedCancellationTargetLower|
    |step33Sub0CombinedCancellationTargetUpper|

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData :
    Step33Sub0CombinedCancellationOrder16DirectIntervalCert where
  lower := step33Sub0CombinedCancellationTargetLower
  upper := step33Sub0CombinedCancellationTargetUpper
  order16Abs :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16AbsRat

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16Budget_rat :
    -primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16AbsRat <=
        step33Sub0CombinedCancellationTargetLower ∧
      step33Sub0CombinedCancellationTargetUpper <=
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16AbsRat := by
  native_decide

/-- Exact slack left between the biased model Horner envelope and the selected
target interval.  A future residual certificate must fit inside this slack. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
    Rat :=
  min
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower -
      step33Sub0CombinedCancellationTargetLower)
    (step33Sub0CombinedCancellationTargetUpper -
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper)

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_residualSlack_nonneg_rat :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_residualSlack_lower_rat :
    step33Sub0CombinedCancellationTargetLower <=
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat := by
  native_decide

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_residualSlack_upper_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper +
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat <=
      step33Sub0CombinedCancellationTargetUpper := by
  native_decide

/-- The remaining analytic/proof-grade obligation for the biased nonzero
order-16 route.  This is the live gap; the file only proves how to spend such a
bound once a later rational/interval certificate supplies it. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
    (residualAbs : Rat) : Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta‖ <=
      (residualAbs : Real)

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_componentSource_target_interval_of_residual_bound
    {residualAbs : Rat}
    (hResidualBudget :
      (residualAbs : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
          Real))
    (hResidual :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
        residualAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget
      step33Sub0CombinedCancellationTargetLower
      step33Sub0CombinedCancellationTargetUpper := by
  intro eta hEta
  have hPoly :=
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_poly_range
      hEta
  have hRem := hResidual eta hEta
  rw [Real.norm_eq_abs] at hRem
  have hAbs := abs_le.mp hRem
  have hLowerSlack :
      (step33Sub0CombinedCancellationTargetLower : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
          Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
            Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_residualSlack_lower_rat
  have hUpperSlack :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
            Real) <=
        (step33Sub0CombinedCancellationTargetUpper : Real) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_residualSlack_upper_rat
  constructor
  · have hBudget :
        (step33Sub0CombinedCancellationTargetLower : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
            Real) -
            (residualAbs : Real) := by
      linarith
    linarith
  · have hBudget :
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
            Real) +
            (residualAbs : Real) <=
          (step33Sub0CombinedCancellationTargetUpper : Real) := by
      linarith
    linarith

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound
    {residualAbs : Rat}
    (hResidualBudget :
      (residualAbs : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
          Real))
    (hResidual :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
        residualAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid := by
  refine
    { sourceInterval := ?_
      order16Budget := ?_ }
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData]
      using
        primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_componentSource_target_interval_of_residual_bound
          hResidualBudget hResidual
  · have hBudgetRat :=
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16Budget_rat
    constructor
    · exact_mod_cast hBudgetRat.1
    · exact_mod_cast hBudgetRat.2

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16NonzeroModelPoly_abs_le
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta‖ <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelAbsBoundRat :
        Real) := by
  have hRadius :=
    primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth hEta
  have hPoly :
      |rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff
        eta| <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelAbsBoundRat :
          Real) :=
    (abs_rawOmegaATaylorPolynomial_le_sum_abs_coeff_mul_radius
      29
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff
      hRadius).trans
      (by
        dsimp [
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelAbsBoundRat]
        norm_num [Rat.cast_abs])
  simpa [
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly,
    Real.norm_eq_abs] using hPoly

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16NonzeroModelPoly_range
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelAbsBoundRat :
        Real) <=
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta ∧
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelAbsBoundRat :
        Real) := by
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16NonzeroModelPoly_abs_le
      hEta
  simpa [Real.norm_eq_abs, abs_le] using hAbs

private def primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyNonzeroModel
    (degree : Nat) (center : Rat)
    (coeff : Fin (degree + 1) -> Rat) : Polynomial Real :=
  ∑ i : Fin (degree + 1),
    Polynomial.C (coeff i : Real) *
      (Polynomial.X - Polynomial.C (center : Real)) ^ i.1

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolyNonzeroModel_eval
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    (eta : Real) :
    rawOmegaATaylorPolynomial degree center coeff eta =
      (primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyNonzeroModel
        degree center coeff).eval eta := by
  unfold rawOmegaATaylorPolynomial
    primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyNonzeroModel
  simp [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]

private theorem
    primaryFiniteRow0Parent0Split100Sub0_polynomial_iteratedDeriv_eval_nonzeroModel
    (p : Polynomial Real) (n : Nat) :
    iteratedDeriv n (fun eta : Real => p.eval eta) =
      fun eta : Real => (Polynomial.derivative^[n] p).eval eta := by
  induction n generalizing p with
  | zero =>
      ext eta
      simp [iteratedDeriv]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      ext eta
      rw [ih p]
      rw [Polynomial.deriv]
      rw [Function.iterate_succ_apply']

private theorem
    primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolynomial_deriv16_eq_shifted29
    (coeff : Fin 46 -> Rat) (eta : Real) :
    iteratedDeriv 16
        (rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20) coeff) eta =
      rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        (fun j : Fin 30 =>
          ((16 + j.1).descFactorial 16 : Rat) *
            coeff ⟨16 + j.1, by omega⟩) eta := by
  let p :=
    primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyNonzeroModel
      45 ((1 : Rat) / 20) coeff
  have hEval :
      rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20) coeff =
        fun eta : Real => p.eval eta := by
    funext eta
    exact
      primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolyNonzeroModel_eval
        45 ((1 : Rat) / 20) coeff eta
  have hDeriv :
      iteratedDeriv 16
          (rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20) coeff) eta =
        (Polynomial.derivative^[16] p).eval eta := by
    rw [hEval]
    simpa using congrFun
      (primaryFiniteRow0Parent0Split100Sub0_polynomial_iteratedDeriv_eval_nonzeroModel
        p 16) eta
  let center : Real := (((1 : Rat) / 20 : Rat) : Real)
  let term : Nat -> Real := fun k =>
    if hk : k < 46 then
      (coeff ⟨k, hk⟩ : Real) * (k.descFactorial 16 : Real) *
        (eta - center) ^ (k - 16)
    else
      0
  have hLhsTerms :
      (Polynomial.derivative^[16] p).eval eta =
        ∑ k ∈ Finset.range 46, term k := by
    unfold p primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyNonzeroModel
    rw [Polynomial.iterate_derivative_sum
      (R := Real) (k := 16) (s := Finset.univ)
      (f := fun i : Fin 46 =>
        Polynomial.C (coeff i : Real) *
          (Polynomial.X - Polynomial.C ((((1 : Rat) / 20 : Rat) : Real))) ^
            i.1)]
    rw [Polynomial.eval_finset_sum]
    rw [← Fin.sum_univ_eq_sum_range term 46]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    dsimp [term, center]
    change
      ((Polynomial.derivative^[16])
        (Polynomial.C (coeff i : Real) *
          (Polynomial.X - Polynomial.C ((((1 : Rat) / 20 : Rat) : Real))) ^
            i.1)).eval eta =
        (if hk : i.1 < 46 then
          (coeff ⟨i.1, hk⟩ : Real) * (i.1.descFactorial 16 : Real) *
            (eta - (((1 : Rat) / 20 : Rat) : Real)) ^ (i.1 - 16)
        else
          0)
    rw [Polynomial.iterate_derivative_C_mul]
    rw [Polynomial.iterate_derivative_X_sub_pow]
    simp [i.2]
    ring
  have hRhsTerms :
      rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
          (fun j : Fin 30 =>
            ((16 + j.1).descFactorial 16 : Rat) *
              coeff ⟨16 + j.1, by omega⟩) eta =
        ∑ k ∈ Finset.range 30, term (16 + k) := by
    unfold rawOmegaATaylorPolynomial
    rw [← Fin.sum_univ_eq_sum_range (fun k => term (16 + k)) 30]
    refine Finset.sum_congr rfl ?_
    intro j _hi
    change
      (((((16 + j.1).descFactorial 16 : Rat) *
            coeff ⟨16 + j.1, by omega⟩ : Rat) : Real) *
          (eta - ((((1 : Rat) / 20 : Rat) : Real))) ^ j.1) =
        term (16 + j.1)
    dsimp [term, center]
    have hlt : 16 + j.1 < 46 := by omega
    rw [dif_pos hlt]
    have hsub : 16 + j.1 - 16 = j.1 := by omega
    rw [hsub]
    have hidx :
        (⟨16 + j.1, by omega⟩ : Fin 46) = ⟨16 + j.1, hlt⟩ := by
      ext
      rfl
    rw [hidx]
    change
      (((((16 + j.1).descFactorial 16 : Rat) *
            coeff ⟨16 + j.1, hlt⟩ : Rat) : Real) *
          (eta - ((((1 : Rat) / 20 : Rat) : Real))) ^ j.1) =
        (coeff ⟨16 + j.1, hlt⟩ : Real) *
          ((16 + j.1).descFactorial 16 : Real) *
          (eta - ((((1 : Rat) / 20 : Rat) : Real))) ^ j.1
    rw [Rat.cast_mul]
    have hNatCast :
        (((((16 + j.1).descFactorial 16 : Nat) : Rat) : Real)) =
          ((16 + j.1).descFactorial 16 : Real) := by
      norm_num
    rw [hNatCast]
    ring_nf
  have hHeadZero :
      ∑ k ∈ Finset.range 16, term k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < 16 := Finset.mem_range.mp hk
    dsimp [term]
    have hk46 : k < 46 := by omega
    rw [dif_pos hk46]
    change
      (coeff ⟨k, hk46⟩ : Real) * (k.descFactorial 16 : Real) *
          (eta - center) ^ (k - 16) =
        0
    have hdesc : k.descFactorial 16 = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr hklt
    rw [hdesc]
    simp
  have hSplit := Finset.sum_range_add term 16 30
  have hRange :
      ∑ k ∈ Finset.range 46, term k =
        ∑ k ∈ Finset.range 30, term (16 + k) := by
    calc
      ∑ k ∈ Finset.range 46, term k =
          ∑ k ∈ Finset.range (16 + 30), term k := by norm_num
      _ = ∑ k ∈ Finset.range 16, term k +
          ∑ k ∈ Finset.range 30, term (16 + k) := hSplit
      _ = ∑ k ∈ Finset.range 30, term (16 + k) := by
          rw [hHeadZero, zero_add]
  calc
    iteratedDeriv 16
        (rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20) coeff) eta =
        (Polynomial.derivative^[16] p).eval eta := hDeriv
    _ = ∑ k ∈ Finset.range 46, term k := hLhsTerms
    _ = ∑ k ∈ Finset.range 30, term (16 + k) := hRange
    _ = rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        (fun j : Fin 30 =>
          ((16 + j.1).descFactorial 16 : Rat) *
            coeff ⟨16 + j.1, by omega⟩) eta := hRhsTerms.symm

/-- Public wrapper for the degree-45-to-degree-29 order-16 Taylor derivative
shift.  This exposes only the coefficient-shift theorem; it does not expose or
reuse any numerical budget. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolynomial_deriv16_eq_shifted29_public
    (coeff : Fin 46 -> Rat) (eta : Real) :
    iteratedDeriv 16
        (rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20) coeff) eta =
      rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        (fun j : Fin 30 =>
          ((16 + j.1).descFactorial 16 : Rat) *
            coeff ⟨16 + j.1, by omega⟩) eta :=
  primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolynomial_deriv16_eq_shifted29
    coeff eta

/- Coefficient crosswalk: the degree-45 residual Taylor polynomial, after sixteen
derivatives, is exactly the degree-29 nonzero model polynomial.  The remaining
work is the proof-grade Horner/range payload and residual-term bounds; this file
does not claim a final Step33A.1 interval certificate. -/

theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylor_order16_eq_nonzeroModelPoly
    (eta : Real) :
    iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly
        eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
        eta := by
  unfold primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff
  change
    iteratedDeriv 16
        (rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff) eta =
      rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
        (fun j : Fin 30 =>
            ((16 + j.1).descFactorial 16 : Rat) *
              primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
                ⟨16 + j.1, by
                  unfold primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
                  have hj : j.1 < 30 := j.2
                  omega⟩) eta
  exact
    primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolynomial_deriv16_eq_shifted29
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta

/-- The cancellation-preserving nonzero model for the assembled order-16 source.

This is the nominal-scale, nominal component-product order-16 derivative.  It is
the component-product version of the equivalent `D^17(Omega * ShapeSq)` nominal
model and avoids spending the killed zero-model rawProduct17 budget. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelSource
    (eta : Real) : Real :=
  (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
    iteratedDeriv 16
      primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta

/-- Exact algebraic split after subtracting the nonzero nominal model.

The two remaining terms are the true proof obligations for the next payload:

* an active-scale actual-minus-nominal component-product derivative;
* a same-unit active-scale minus nominal-scale defect times the nominal
  component-product derivative.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelSource
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelSource
          eta =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta) +
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual]
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelSource
  ring

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta +
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
  rw [
    ← primaryFiniteRow0Parent0Split100Sub0_residualTaylor_order16_eq_nonzeroModelPoly
      eta]
  ring

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_biasedNonzeroModelPoly
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta =
      (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta +
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta) -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModelPoly_eq]
  rw [
    show
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta +
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
              Real)) =
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
            eta -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) by
      ring]
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly]

end Step33
end PSDpd
end Q3
