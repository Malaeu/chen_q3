import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Bias-shift bridge from the checked biased-residual segment receiver to the
direct scaled-remainder payload target.

This file does not generate analytic source rows and does not claim
Step33A.1-A closure.  It only records the exact additional budget rows needed
to reuse a proof-grade bound for
`ComponentSource - BiasedNonzeroModelPoly` as a direct bound for
`ComponentSource - NonzeroModelPoly`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- The direct target differs from the biased-residual target by the fixed bias. -/
theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_sub_bias_eq_biasedResidual
    (eta : Real) :
    (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
          eta) -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) =
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModelPoly_eq]
  ring

/--
The direct segment induced by a biased-residual source segment.

If the biased residual is bounded by `biasedAbs`, then the direct residual lies
in the signed interval `bias ± biasedAbs`.  The segment is still budgeted by the
canonical direct remainder constant, so the caller must prove the two explicit
bias-budget rows.
-/
def primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual
    (biasedAbs : Rat)
    (seg : Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert) :
    Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert where
  cellL := seg.cellL
  cellU := seg.cellU
  lower :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat -
      biasedAbs
  upper :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat +
      biasedAbs
  remainderAbs :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs

theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegment_valid_of_biasedResidual
    {biasedAbs : Rat}
    {seg : Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert}
    (hSeg : seg.Valid biasedAbs)
    (hLowerBudget :
      -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) - (biasedAbs : Real))
    (hUpperBudget :
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) + (biasedAbs : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real)) :
    (primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual
      biasedAbs seg).Valid := by
  refine
    { cellSubset := ?_
      directInterval := ?_
      remainderNonneg := ?_
      lowerBudget := ?_
      upperBudget := ?_ }
  · intro eta hEta
    exact hSeg.cellSubset eta hEta
  · intro eta hEta
    have hBound := hSeg.to_residual_bound_on_segment eta hEta
    rw [Real.norm_eq_abs, abs_le] at hBound
    have hShift :=
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_sub_bias_eq_biasedResidual
        eta
    constructor <;>
      simp [
        primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual] <;>
      linarith
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual]
      using
        primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_residualAbs_nonneg
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual]
      using hLowerBudget
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual]
      using hUpperBudget

/--
Any proof of the biased-residual source proposition can be shifted into the
direct nonzero-model source proposition, provided the exact bias-budget rows
fit the canonical direct budget.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_nonzeroModel_sourceProp_of_biasedResidualSourceProp
    {biasedAbs : Rat}
    (hBiased :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
        biasedAbs)
    (hLowerBudget :
      -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) - (biasedAbs : Real))
    (hUpperBudget :
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) + (biasedAbs : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs := by
  intro eta hEta
  have hBound := hBiased eta hEta
  rw [Real.norm_eq_abs, abs_le] at hBound
  have hShift :=
    primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_sub_bias_eq_biasedResidual
      eta
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Direct family obtained from a biased-residual segment cover. -/
def primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamilyOfBiasedResidual
    (n : Nat)
    (biasedAbs : Rat)
    (seg : Fin n -> Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert) :
    Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert where
  n := n
  residualAbs :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs
  seg := fun i =>
    primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual
      biasedAbs (seg i)

theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamily_valid_of_biasedResidual
    {n : Nat}
    {biasedAbs : Rat}
    {seg : Fin n -> Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert}
    (hValid : ∀ i : Fin n, (seg i).Valid biasedAbs)
    (hCover : Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover n seg)
    (hLowerBudget :
      -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) - (biasedAbs : Real))
    (hUpperBudget :
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) + (biasedAbs : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real)) :
    (primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamilyOfBiasedResidual
      n biasedAbs seg).Valid := by
  refine
    { segmentValid := ?_
      segmentBudget := ?_
      cover := ?_ }
  · intro i
    exact
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegment_valid_of_biasedResidual
        (hValid i) hLowerBudget hUpperBudget
  · intro i
    simp [
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamilyOfBiasedResidual,
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual]
  · intro eta hEta
    rcases hCover eta hEta with ⟨i, hEtaSeg⟩
    refine ⟨i, ?_⟩
    simpa [
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamilyOfBiasedResidual,
      primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual]
      using hEtaSeg

theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirect_payloadTarget_of_biasedResidual
    {n : Nat}
    {biasedAbs : Rat}
    {seg : Fin n -> Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert}
    (hValid : ∀ i : Fin n, (seg i).Valid biasedAbs)
    (hCover : Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover n seg)
    (hLowerBudget :
      -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) - (biasedAbs : Real))
    (hUpperBudget :
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) + (biasedAbs : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget
      (primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamilyOfBiasedResidual
        n biasedAbs seg) := by
  exact
    ⟨primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamily_valid_of_biasedResidual
        hValid hCover hLowerBudget hUpperBudget,
      rfl⟩

theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_nonzeroModel_sourceProp_of_biasedResidual
    {n : Nat}
    {biasedAbs : Rat}
    {seg : Fin n -> Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert}
    (hValid : ∀ i : Fin n, (seg i).Valid biasedAbs)
    (hCover : Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover n seg)
    (hLowerBudget :
      -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) - (biasedAbs : Real))
    (hUpperBudget :
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) + (biasedAbs : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload
    (primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirect_payloadTarget_of_biasedResidual
      hValid hCover hLowerBudget hUpperBudget)

/-- The fixed bias is already larger than the canonical direct budget. -/
theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_bias_exceeds_direct_budget_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs <
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat := by
  native_decide

/--
Consequently the biased-residual bridge cannot be spent into the current direct
budget for any nonnegative biased residual error.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_biasShift_upperBudget_impossible_of_nonneg
    {biasedAbs : Rat}
    (hNonneg : 0 <= biasedAbs) :
    ¬
      ((primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) + (biasedAbs : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real)) := by
  intro hUpper
  have hBiasGtRat :=
    primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_bias_exceeds_direct_budget_rat
  have hBiasGt :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) := by
    exact_mod_cast hBiasGtRat
  have hNonnegReal : (0 : Real) <= (biasedAbs : Real) := by
    exact_mod_cast hNonneg
  linarith

end Step33
end PSDpd
end Q3
