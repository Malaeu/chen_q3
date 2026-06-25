import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectIntervalPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationPolynomialRange

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Conditional direct order-16 model checker for Step33A.1-A sub0.

This file does not emit the concrete direct polynomial rows yet.  It proves the
certificate checker shape selected by Browser/Computer Use route review:
exact rational Horner rows and exact budget rows may be checked locally, while
the only analytic premise is the whole-source approximation
`hRemainder` for the assembled order-16 component source.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Analytic source premise left to the future direct-order16 generator/proof.
The polynomial is a cancellation-preserving model of the assembled component
source, not a separate norm bound for the product summands. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp
    (data : Step33Sub0CombinedCancellationIntervalCert) : Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        Step33Sub0CombinedCancellationIntervalCert.poly data eta‖ <=
      (data.remainderAbs : Real)

/-- Package the rational lower/upper/order16Abs rows for the checked direct
interval adapter. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectIntervalData
    (sourceLower sourceUpper order16Abs : Rat) :
    Step33Sub0CombinedCancellationOrder16DirectIntervalCert where
  lower := sourceLower
  upper := sourceUpper
  order16Abs := order16Abs

/--
Checker theorem for the next direct-order16 payload.

The generated payload must provide:
* exact Horner range rows for `data.poly`,
* exact propagation from `polyLower/polyUpper` and `remainderAbs` to
  `sourceLower/sourceUpper`,
* exact `order16Abs` budget rows.

The only remaining analytic assumption is `hRemainder`, which bounds the
assembled component source by the same polynomial model.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectInterval_valid_of_horner_remainder
    {data : Step33Sub0CombinedCancellationIntervalCert}
    {range : Step33Sub0CombinedCancellationHornerRangeCert data}
    {sourceLower sourceUpper order16Abs : Rat}
    (hCellL : data.cellL = 0)
    (hCellU : data.cellU = (1 : Rat) / 10)
    (hRemainder :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp
        data)
    (hRange : range.Valid)
    (hBudgetLower :
      (sourceLower : Real) <=
        (data.polyLower : Real) - (data.remainderAbs : Real))
    (hBudgetUpper :
      (data.polyUpper : Real) + (data.remainderAbs : Real) <=
        (sourceUpper : Real))
    (hOrder16Budget :
      -(order16Abs : Real) <= (sourceLower : Real) ∧
        (sourceUpper : Real) <= (order16Abs : Real)) :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectIntervalData
      sourceLower sourceUpper order16Abs).Valid := by
  refine
    { sourceInterval := ?_
      order16Budget := ?_ }
  · intro eta hEta
    have hRem := hRemainder eta hEta
    rw [Real.norm_eq_abs] at hRem
    have hAbs := abs_le.mp hRem
    have hPoly :=
      Step33Sub0CombinedCancellationHornerRangeCert.Valid.poly_range_unit_cell
        hRange hCellL hCellU eta hEta
    constructor
    · have hPolyLower :
          (sourceLower : Real) <=
            Step33Sub0CombinedCancellationIntervalCert.poly data eta -
              (data.remainderAbs : Real) := by
        linarith [hBudgetLower, hPoly.1]
      have hSourceLower :
          Step33Sub0CombinedCancellationIntervalCert.poly data eta -
              (data.remainderAbs : Real) <=
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta := by
        linarith [hAbs.1]
      exact hPolyLower.trans hSourceLower
    · have hSourceUpper :
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta <=
            Step33Sub0CombinedCancellationIntervalCert.poly data eta +
              (data.remainderAbs : Real) := by
        linarith [hAbs.2]
      have hPolyUpper :
          Step33Sub0CombinedCancellationIntervalCert.poly data eta +
              (data.remainderAbs : Real) <=
            (sourceUpper : Real) := by
        linarith [hPoly.2, hBudgetUpper]
      exact hSourceUpper.trans hPolyUpper
  · exact hOrder16Budget

/--
Concrete threshold zero-model for the direct order-16 source.

This is not a proof of the analytic approximation.  It fixes all rational
checker fields around the exact one-cell order-16 budget threshold.  The only
remaining premise below is the proof that the assembled component source lies
within this threshold of the zero polynomial on `[0, 1/10]`.
-/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth *
    (Nat.factorial 16 : Rat) / (((1 : Rat) / 20) ^ 16)

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelCoeff
    (_i : Fin 1) : Rat :=
  0

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData :
    Step33Sub0CombinedCancellationIntervalCert where
  cellL := 0
  cellU := (1 : Rat) / 10
  center := (1 : Rat) / 20
  degree := 0
  coeff := primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelCoeff
  remainderAbs :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs
  polyLower := 0
  polyUpper := 0

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelStageLower
    (_i :
      Fin
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData.degree +
          1)) : Rat :=
  0

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelStageUpper
    (_i :
      Fin
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData.degree +
          1)) : Rat :=
  0

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelHornerRangeData :
    Step33Sub0CombinedCancellationHornerRangeCert
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData
    where
  stageLower :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelStageLower
  stageUpper :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelStageUpper

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower :
    Rat :=
  -primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelIntervalData :
    Step33Sub0CombinedCancellationOrder16DirectIntervalCert :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectIntervalData
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs

def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp :
    Prop :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData

/-- The direct zero-model analytic premise is exactly an absolute bound for the
assembled order-16 component source, since the model polynomial is `0`.  This
is an interface bridge only; it does not provide the source bound. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_componentSource_abs
    (hSource :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta‖ <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
            Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp := by
  intro eta hEta
  have h := hSource eta hEta
  simpa [
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp,
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp,
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData,
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelCoeff,
    Step33Sub0CombinedCancellationIntervalCert.poly,
    rawOmegaATaylorPolynomial] using h

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_horner_valid :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelHornerRangeData.Valid := by
  refine
    { stage_bounds := ?_
      outputLower := ?_
      outputUpper := ?_ }
  · intro i eta hEta
    fin_cases i
    constructor <;>
      simp [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelHornerRangeData,
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelStageLower,
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelStageUpper,
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData,
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelCoeff,
        Step33Sub0CombinedCancellationIntervalCert.hornerTail]
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelHornerRangeData,
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelStageLower,
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData]
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelHornerRangeData,
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelStageUpper,
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_source_lower_budget :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower :
        Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData.polyLower :
          Real) -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData.remainderAbs :
          Real) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower,
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_source_upper_budget :
    (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData.polyUpper :
        Real) +
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData.remainderAbs :
          Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper :
        Real) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper,
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_order16_budget :
    -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
        Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower :
          Real) ∧
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper :
        Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real) := by
  constructor <;>
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower,
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_order16_remainder_width_pass_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs *
        ((1 : Rat) / 20) ^ 16 / (Nat.factorial 16 : Rat) <=
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_remainder
    (hRemainder :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelIntervalData.Valid := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectInterval_valid_of_horner_remainder
      (data := primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData)
      (range := primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelHornerRangeData)
      rfl
      rfl
      hRemainder
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_horner_valid
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_source_lower_budget
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_source_upper_budget
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_order16_budget

end Step33
end PSDpd
end Q3
