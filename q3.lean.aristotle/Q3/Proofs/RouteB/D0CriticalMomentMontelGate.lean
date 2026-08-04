import Q3.Proofs.RouteB.D0StripMontelRefinement

set_option linter.mathlibStandardSet false

open Complex Filter Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-- The critical-moment ratio supplies the closed-substrip bounds, which
transfer to compact strip-local bounds and hence to the refined Montel gate. -/
theorem exists_refined_montelAnchorGate_of_criticalMomentRatio
    (D : CanonicalData)
    (H2aAt S1At : CentralIndex D.kTrial → Prop)
    (hXi : centeredXi 0 ≠ 0)
    (hRatio :
      CenteredTrialCriticalMomentRatio D.kTrial D.parent) :
    ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
      MontelAnchorGate
        (canonicalApproximation
          (montelRefinement D e he))
        H2aAt S1At 0 := by
  have hclosed :
      SelectedPostAnchorClosedSubstripBounded D :=
    selectedPostAnchorClosedSubstripBounded_of_criticalMomentRatio
      D hRatio
  have hcompact :
      SelectedLocallyBoundedOnCenteredCriticalStrip D :=
    selectedLocallyBoundedOnCenteredCriticalStrip_of_closedSubstripBounded
      D hclosed
  exact
    exists_refined_montelAnchorGate_of_strip_bounds
      D H2aAt S1At hXi hcompact

#print axioms exists_refined_montelAnchorGate_of_criticalMomentRatio

end Q3.RouteB.D0Pstar
