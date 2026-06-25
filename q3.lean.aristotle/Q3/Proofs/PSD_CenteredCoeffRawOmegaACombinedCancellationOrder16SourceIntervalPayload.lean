import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SourceIntervalCert

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Whole-cell payload surface for the Step33A.1-A sub0 direct order-16 source
interval route.

This file fixes the concrete one-segment bookkeeping for the existing
zero-model threshold.  The analytic signed interval for the assembled
component source is still an explicit input; no concrete source rows and no
Step33A.1-A closure are claimed here.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- The concrete whole-cell segment used by the zero-model source interval
receiver. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegment :
    Step33Sub0CombinedCancellationOrder16SourceSegmentCert where
  cellL := 0
  cellU := (1 : Rat) / 10
  sourceLower :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower
  sourceUpper :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper

/-- Singleton segment family for the whole active cell. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegments
    (_i : Fin 1) :
    Step33Sub0CombinedCancellationOrder16SourceSegmentCert :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegment

/-- The whole-cell singleton family covers `[0, 1/10]`. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16SourceWholeCell_cover :
    Step33Sub0CombinedCancellationOrder16SourceSegmentCover 1
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegments := by
  intro eta hEta
  refine ⟨⟨0, by decide⟩, ?_⟩
  simpa [
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegments,
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegment]
    using hEta

/--
The whole-cell segment is valid once the missing proof-grade signed interval
for the assembled order-16 source is supplied.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16SourceWholeCell_valid_of_direct_interval
    (hSource :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegment.Valid := by
  refine
    { cellSubset := ?_
      sourceInterval := ?_
      zeroModelBudget := ?_ }
  · intro eta hEta
    simpa [
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegment]
      using hEta
  · intro eta hEta
    exact hSource eta (by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegment]
        using hEta)
  · exact
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_order16_budget

/--
The proof-grade whole-cell direct interval is enough to produce the zero-model
`hRemainder` premise.  This is still conditional on the signed source interval.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_wholeCell_direct_interval
    (hSource :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_segment_cover
      (n := 1)
      (seg :=
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegments)
      ?_
      primaryFiniteRow0Parent0Split100Sub0_combinedOrder16SourceWholeCell_cover
  intro i
  fin_cases i
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16SourceWholeCell_valid_of_direct_interval
      hSource

/--
The same missing signed whole-source interval also gives the full zero-model
direct interval data validity.  This is the final fail-closed receiver before
the absent proof-grade source interval certificate.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_wholeCell_direct_interval
    (hSource :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelIntervalData.Valid := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_remainder
      (primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_wholeCell_direct_interval
        hSource)

end Step33
end PSDpd
end Q3
