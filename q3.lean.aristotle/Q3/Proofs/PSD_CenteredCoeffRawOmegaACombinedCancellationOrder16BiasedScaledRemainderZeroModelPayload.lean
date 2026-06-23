import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderIntervalPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Concrete one-cell zero-model checker for the Step33A.1-A sub0 biased
scaled-remainder interval route.

This file does not prove the analytic scaled-remainder bound.  It proves the
exact checker plumbing around the canonical residual budget:
once a proof-grade bound

`primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`

is supplied, the generated interval payload target is closed by a single
segment with lower/upper `±BiasedResidualRemainderAbs`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- One-cell zero model for the whole signed biased scaled remainder. -/
def primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment :
    Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert where
  cellL := 0
  cellU := (1 : Rat) / 10
  lower :=
    -primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs
  upper :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs
  remainderAbs :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs

/-- The corresponding one-cell interval-family certificate data. -/
def primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily :
    Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert where
  n := 1
  residualAbs :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs
  seg := fun _ =>
    primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment

theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_residualAbs_nonneg :
    (0 : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
        Real) := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs
  exact_mod_cast
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_residualSlack_nonneg_rat

/-- Same analytic remainder, in the nonzero-model source convention. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
    (remainderAbs : Rat) : Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
          eta‖ <=
      (remainderAbs : Real)

theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
        eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
          eta := by
  unfold
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
  symm
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly
      eta

theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderSourceProp_of_nonzeroModelResidual
    {remainderAbs : Rat}
    (hResidual :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
        remainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
      remainderAbs := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual]
  exact hResidual eta hEta

theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_segment_valid
    (hScaled :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment.Valid := by
  refine
    { cellSubset := ?_
      scaledInterval := ?_
      remainderNonneg := ?_
      lowerBudget := ?_
      upperBudget := ?_ }
  · intro eta hEta
    simpa [
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]
      using hEta
  · intro eta hEta
    have hCell :
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]
        using hEta
    have hAbs := hScaled eta hCell
    rw [Real.norm_eq_abs] at hAbs
    have hBound := abs_le.mp hAbs
    constructor
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]
        using hBound.1
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]
        using hBound.2
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]
      using
        primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_residualAbs_nonneg
  · simp [
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]
  · simp [
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]

theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_cover :
    Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCover 1
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily.seg := by
  intro eta hEta
  refine ⟨⟨0, by norm_num⟩, ?_⟩
  simpa [
    primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily,
    primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]
    using hEta

theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_family_valid
    (hScaled :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily.Valid := by
  refine
    { segmentValid := ?_
      segmentBudget := ?_
      cover :=
        primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_cover }
  · intro i
    fin_cases i
    exact
      primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_segment_valid
        hScaled
  · intro i
    fin_cases i
    simp [
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily,
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment]

theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target
    (hScaled :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily := by
  exact
    ⟨primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_family_valid
        hScaled,
      rfl⟩

theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_nonzeroModelResidual
    (hResidual :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily :=
  primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target
    (primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderSourceProp_of_nonzeroModelResidual
      hResidual)

theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_zeroModel
    (hScaled :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
            eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) :=
  primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_interval_payload
    (primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target
      hScaled)

end Step33
end PSDpd
end Q3
