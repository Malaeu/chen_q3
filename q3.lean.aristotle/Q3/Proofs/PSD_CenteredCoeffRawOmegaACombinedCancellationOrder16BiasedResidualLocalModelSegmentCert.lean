import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Segment-local biased residual receiver for the Step33A.1-A sub0 order-16 route.

The older source-segment receiver compares a source interval against the global
biased model range.  This file records the tighter proof interface needed by a
segment payload: compare the source and biased model ranges on the same cell,
then transport the resulting residual bound into the existing direct
biased nonzero-model receiver.

This file is interface-only.  It proves no concrete segment rows and claims no
Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/--
One segment-local source/model interval row for the biased residual route.

The payload must prove both source and biased-model ranges on the same cell.
This avoids paying the width of the biased model's whole-cell global range.
-/
structure Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert where
  cellL : Rat
  cellU : Rat
  sourceLower : Rat
  sourceUpper : Rat
  modelLower : Rat
  modelUpper : Rat
  residualAbs : Rat

namespace Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert

/-- Proof-bearing validity predicate for one segment-local residual row. -/
structure Valid
    (cert :
      Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert) :
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
  modelInterval :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.modelLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
            eta <=
          (cert.modelUpper : Real)
  residualNonneg :
    (0 : Real) <= (cert.residualAbs : Real)
  lowerBudget :
    -(cert.residualAbs : Real) <=
      (cert.sourceLower : Real) - (cert.modelUpper : Real)
  upperBudget :
    (cert.sourceUpper : Real) - (cert.modelLower : Real) <=
      (cert.residualAbs : Real)

namespace Valid

theorem to_residual_bound_on_segment
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
            eta‖ <=
        (cert.residualAbs : Real) := by
  intro eta hEta
  have hSource := h.sourceInterval eta hEta
  have hModel := h.modelInterval eta hEta
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · calc
      -(cert.residualAbs : Real) <=
          (cert.sourceLower : Real) - (cert.modelUpper : Real) :=
        h.lowerBudget
      _ <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
              eta :=
        sub_le_sub hSource.1 hModel.2
  · calc
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
              eta <=
          (cert.sourceUpper : Real) - (cert.modelLower : Real) :=
        sub_le_sub hSource.2 hModel.1
      _ <= (cert.residualAbs : Real) := h.upperBudget

end Valid
end Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert

/--
A finite family of segment-local source/model rows covers the active cell.
-/
def Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCover
    (n : Nat)
    (seg : Fin n ->
      Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert) :
    Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ∃ i : Fin n,
      eta ∈ Set.Icc ((seg i).cellL : Real) ((seg i).cellU : Real)

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_local_model_segment_cover
    {n : Nat}
    {seg : Fin n ->
      Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert}
    {residualAbs : Rat}
    (hValid :
      ∀ i : Fin n, (seg i).Valid)
    (hSegmentBudget :
      ∀ i : Fin n, ((seg i).residualAbs : Real) <= (residualAbs : Real))
    (hCover :
      Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCover n seg) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      residualAbs := by
  intro eta hEta
  rcases hCover eta hEta with ⟨i, hEtaSeg⟩
  exact
    le_trans
      ((hValid i).to_residual_bound_on_segment eta hEtaSeg)
      (hSegmentBudget i)

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_local_model_segment_cover
    {n : Nat}
    {seg : Fin n ->
      Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert}
    {residualAbs : Rat}
    (hResidualBudget :
      (residualAbs : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
          Real))
    (hValid :
      ∀ i : Fin n, (seg i).Valid)
    (hSegmentBudget :
      ∀ i : Fin n, ((seg i).residualAbs : Real) <= (residualAbs : Real))
    (hCover :
      Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCover n seg) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound
    hResidualBudget
    (primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_local_model_segment_cover
      hValid hSegmentBudget hCover)

end Step33
end PSDpd
end Q3
