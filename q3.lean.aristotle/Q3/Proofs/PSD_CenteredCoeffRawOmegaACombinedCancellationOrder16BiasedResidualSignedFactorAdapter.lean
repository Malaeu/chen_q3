import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SignedFactorChecker
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Signed-factor adapter for the Step33A.1-A sub0 biased residual route.

This file connects the source-only signed-factor segment checker to the biased
residual source-segment receiver.  It intentionally does not use the old
zero-model budget row from `SignedFactorSegmentCert.Valid`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

namespace Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert

/-- Forget a signed-factor segment to the biased residual source-segment row. -/
def toBiasedResidualSourceSegment
    (cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert where
  cellL := cert.cellL
  cellU := cert.cellU
  sourceLower := cert.sourceLower
  sourceUpper := cert.sourceUpper

namespace SourceIntervalValid

/--
A source-only signed-factor segment becomes a valid biased-residual source
segment once its source interval is spent against the biased-model range.
-/
theorem to_biasedResidualSourceSegmentValid
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    {residualAbs : Rat}
    (h : cert.SourceIntervalValid)
    (hLower :
      -(residualAbs : Real) <=
        (cert.sourceLower : Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
            Real))
    (hUpper :
      (cert.sourceUpper : Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
            Real) <=
        (residualAbs : Real)) :
    cert.toBiasedResidualSourceSegment.Valid residualAbs := by
  refine
    { cellSubset := ?_
      sourceInterval := ?_
      lowerBudget := hLower
      upperBudget := hUpper }
  · intro eta hEta
    exact h.cellSubset eta hEta
  · intro eta hEta
    exact h.to_sourceInterval eta hEta

end SourceIntervalValid
end Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert

/--
A signed-factor segment family covers the active cell for the biased residual
route when the forgotten source-segment family covers it.
-/
def Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentCover
    (n : Nat)
    (seg :
      Fin n ->
        Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Prop :=
  Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover n
    (fun i => (seg i).toBiasedResidualSourceSegment)

/--
Source-only signed-factor rows plus biased-model budget rows feed the live
biased residual source proposition.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover
    {n : Nat}
    {seg :
      Fin n ->
        Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    {residualAbs : Rat}
    (hValid : ∀ i : Fin n, (seg i).SourceIntervalValid)
    (hLower :
      ∀ i : Fin n,
        -(residualAbs : Real) <=
          ((seg i).sourceLower : Real) -
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
              Real))
    (hUpper :
      ∀ i : Fin n,
        ((seg i).sourceUpper : Real) -
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
              Real) <=
          (residualAbs : Real))
    (hCover :
      Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentCover n seg) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      residualAbs := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_segment_cover
      (n := n)
      (seg := fun i => (seg i).toBiasedResidualSourceSegment)
      (fun i =>
        (hValid i).to_biasedResidualSourceSegmentValid
          (hLower i)
          (hUpper i))
      hCover

/--
Source-only signed-factor rows plus biased-model budget rows feed the checked
order-16 biased residual interval data.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_signedFactor_segment_cover
    {n : Nat}
    {seg :
      Fin n ->
        Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    {residualAbs : Rat}
    (hResidualBudget :
      (residualAbs : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
          Real))
    (hValid : ∀ i : Fin n, (seg i).SourceIntervalValid)
    (hLower :
      ∀ i : Fin n,
        -(residualAbs : Real) <=
          ((seg i).sourceLower : Real) -
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
              Real))
    (hUpper :
      ∀ i : Fin n,
        ((seg i).sourceUpper : Real) -
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
              Real) <=
          (residualAbs : Real))
    (hCover :
      Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentCover n seg) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound
    hResidualBudget
    (primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover
      hValid hLower hUpper hCover)

/--
Generator-facing payload for the biased residual signed-factor segment route.

The certificate carries only data.  The proof object is `Valid`, which must
prove source-only signed-factor segment validity, coverage, same-unit
biased-model budget rows, and the global residual slack comparison.
-/
structure Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert where
  n : Nat
  residualAbs : Rat
  seg :
    Fin n ->
      Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert

namespace Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert

/-- Proof-bearing predicate for the biased residual signed-factor segment
payload. -/
structure Valid
    (cert :
      Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert) :
    Prop where
  residualBudget :
    (cert.residualAbs : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
        Real)
  segmentValid :
    ∀ i : Fin cert.n, (cert.seg i).SourceIntervalValid
  lowerBudget :
    ∀ i : Fin cert.n,
      -(cert.residualAbs : Real) <=
        ((cert.seg i).sourceLower : Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
            Real)
  upperBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).sourceUpper : Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
            Real) <=
        (cert.residualAbs : Real)
  cover :
    Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentCover
      cert.n cert.seg

namespace Valid

theorem to_residualSourceProp
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      cert.residualAbs :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover
    (n := cert.n)
    (seg := cert.seg)
    h.segmentValid
    h.lowerBudget
    h.upperBudget
    h.cover

theorem to_order16DirectIntervalValid
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound
    h.residualBudget h.to_residualSourceProp

end Valid
end Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert

end Step33
end PSDpd
end Q3
