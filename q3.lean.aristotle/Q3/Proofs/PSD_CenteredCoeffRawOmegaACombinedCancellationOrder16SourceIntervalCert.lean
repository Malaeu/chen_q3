import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectModelPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Segmented signed whole-source interval checker for the Step33A.1-A sub0
combined-cancellation order-16 source.

This file is an interface only.  It does not emit factor rows, does not prove
any segment source interval, and does not claim Step33A.1-A closure.  It records
the exact receiver shape selected by route review: proof-grade signed intervals
for the whole assembled order-16 component source may be checked segment by
segment and then fed into the existing zero-model `hRemainder` bridge.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
One signed interval row for the assembled order-16 component source on a
subsegment.  The row is data only; `Valid` below is the proof object.
-/
structure Step33Sub0CombinedCancellationOrder16SourceSegmentCert where
  cellL : Rat
  cellU : Rat
  sourceLower : Rat
  sourceUpper : Rat

namespace Step33Sub0CombinedCancellationOrder16SourceSegmentCert

/--
Proof-bearing predicate for one segment.  The hard field is `sourceInterval`,
which must bound the whole assembled source directly; it is not a product-summand
norm estimate.
-/
structure Valid
    (cert : Step33Sub0CombinedCancellationOrder16SourceSegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  sourceInterval :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.sourceLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <=
          (cert.sourceUpper : Real)
  zeroModelBudget :
    -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
        Real) <=
        (cert.sourceLower : Real) ∧
      (cert.sourceUpper : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real)

namespace Valid

/-- A valid segment row gives the zero-model absolute source bound on that
segment. -/
theorem to_componentSource_abs_on_segment
    {cert : Step33Sub0CombinedCancellationOrder16SourceSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real) := by
  intro eta hEta
  have hInterval := h.sourceInterval eta hEta
  have hLower :
      -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real) <=
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta := by
    linarith [h.zeroModelBudget.1, hInterval.1]
  have hUpper :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real) := by
    linarith [h.zeroModelBudget.2, hInterval.2]
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hLower, hUpper⟩

end Valid
end Step33Sub0CombinedCancellationOrder16SourceSegmentCert

/-- A finite segment family covers the active cell. -/
def Step33Sub0CombinedCancellationOrder16SourceSegmentCover
    (n : Nat)
    (seg : Fin n -> Step33Sub0CombinedCancellationOrder16SourceSegmentCert) :
    Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ∃ i : Fin n,
      eta ∈ Set.Icc ((seg i).cellL : Real) ((seg i).cellU : Real)

/--
Segment-row receiver for the zero-model source bound on the full active cell.

This theorem is intentionally conditional on proof-grade per-segment source
intervals and a proof-grade cover.  It does not provide either.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_abs_of_segment_cover
    {n : Nat}
    {seg : Fin n -> Step33Sub0CombinedCancellationOrder16SourceSegmentCert}
    (hValid : ∀ i : Fin n, (seg i).Valid)
    (hCover :
      Step33Sub0CombinedCancellationOrder16SourceSegmentCover n seg) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real) := by
  intro eta hEta
  rcases hCover eta hEta with ⟨i, hEtaSeg⟩
  exact (hValid i).to_componentSource_abs_on_segment eta hEtaSeg

/-- The segmented signed whole-source certificate feeds the existing zero-model
`hRemainder` bridge. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_segment_cover
    {n : Nat}
    {seg : Fin n -> Step33Sub0CombinedCancellationOrder16SourceSegmentCert}
    (hValid : ∀ i : Fin n, (seg i).Valid)
    (hCover :
      Step33Sub0CombinedCancellationOrder16SourceSegmentCover n seg) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_componentSource_abs
      (primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_abs_of_segment_cover
        hValid hCover)

end Step33
end PSDpd
end Q3
