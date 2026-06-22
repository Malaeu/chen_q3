import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationPolynomialRange

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Concrete conditional payload for the Step33A.1-A sub0 combined-cancellation
interval.

This file closes the concrete cell, Horner range, and target-budget arithmetic
for a one-cell constant model.  It does not prove the analytic source estimate:
the only remaining premise is the whole-expression remainder bound named
`primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint : Rat :=
  (886244509673 : Rat) / 500000000000000000000000000000

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth : Rat :=
  (245091005771 : Rat) / 125000000000000000000000000000

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalCoeff
    (_i : Fin 1) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData :
    Step33Sub0CombinedCancellationIntervalCert where
  cellL := 0
  cellU := (1 : Rat) / 10
  center := (1 : Rat) / 20
  degree := 0
  coeff := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalCoeff
  remainderAbs :=
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth
  polyLower :=
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint
  polyUpper :=
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerStageLower
    (_i :
      Fin
        (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.degree +
          1)) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerStageUpper
    (_i :
      Fin
        (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.degree +
          1)) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerRangeData :
    Step33Sub0CombinedCancellationHornerRangeCert
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
    where
  stageLower :=
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerStageLower
  stageUpper :=
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerStageUpper

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp :
    Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
        Step33Sub0CombinedCancellationIntervalCert.poly
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
          eta‖ <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
        Real)

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationHornerRange_valid :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerRangeData.Valid := by
  refine
    { stage_bounds := ?_
      outputLower := ?_
      outputUpper := ?_ }
  · intro i eta hEta
    fin_cases i
    constructor <;>
      simp [
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerRangeData,
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerStageLower,
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerStageUpper,
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData,
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalCoeff,
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint,
        Step33Sub0CombinedCancellationIntervalCert.hornerTail]
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerRangeData,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerStageLower,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint]
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerRangeData,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerStageUpper,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_remainder_nonneg :
    0 <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
        Real) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_budget_lower :
    (step33Sub0CombinedCancellationTargetLower : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.polyLower :
          Real) -
        (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
          Real) := by
  norm_num [
    step33Sub0CombinedCancellationTargetLower,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_budget_upper :
    (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.polyUpper :
        Real) +
        (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
          Real) <=
      (step33Sub0CombinedCancellationTargetUpper : Real) := by
  norm_num [
    step33Sub0CombinedCancellationTargetUpper,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHalfWidth]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_remainder_bound
    (hRemainder :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.Valid := by
  exact
    Step33Sub0CombinedCancellationIntervalCert.Valid.of_horner_range
      (data := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData)
      (range := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationHornerRangeData)
      rfl
      rfl
      primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_remainder_nonneg
      hRemainder
      primaryFiniteRow0Parent0Split100Sub0_combinedCancellationHornerRange_valid
      primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_budget_lower
      primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_budget_upper

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_hCombined_of_remainder_bound
    (hRemainder :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  (primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_remainder_bound
    hRemainder).to_hCombined

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_combinedCancellation_remainder_bound
    (hRemainder :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta ∧
        deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  (primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_remainder_bound
    hRemainder).to_fullTaylor_residual_deriv_interval

end Step33
end PSDpd
end Q3
