import Q3.Proofs.RouteB.CenteredXiZeroNonzero
import Q3.Proofs.RouteB.D0CriticalMomentMontelGate

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

theorem exists_refined_clusterData_of_criticalMomentRatio
    (D : CanonicalData)
    (hRatio :
      CenteredTrialCriticalMomentRatio D.kTrial D.parent) :
    ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
      Nonempty
        (ClusterData
          (canonicalApproximation
            (montelRefinement D e he))) := by
  have hclosed :
      SelectedPostAnchorClosedSubstripBounded D :=
    selectedPostAnchorClosedSubstripBounded_of_criticalMomentRatio
      D hRatio
  have hcompact :
      SelectedLocallyBoundedOnCenteredCriticalStrip D :=
    selectedLocallyBoundedOnCenteredCriticalStrip_of_closedSubstripBounded
      D hclosed
  exact
    exists_refined_clusterData_of_strip_bounds
      D Q3.RouteB.centeredXi_zero_ne_zero hcompact

#print axioms exists_refined_clusterData_of_criticalMomentRatio

end Q3.RouteB.D0Pstar
