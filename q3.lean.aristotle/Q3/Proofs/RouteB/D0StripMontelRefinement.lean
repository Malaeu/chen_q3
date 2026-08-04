import Q3.Proofs.RouteB.MontelCenteredCriticalStrip

set_option linter.mathlibStandardSet false

open Complex Filter Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-- Strip-local Montel compactness produces a nonzero cluster after its strict
subsequence is absorbed into the existing same-parent extraction. -/
theorem exists_refined_clusterData_of_strip_bounds
    (D : CanonicalData)
    (hXi : centeredXi 0 ≠ 0)
    (hbdd :
      SelectedLocallyBoundedOnCenteredCriticalStrip D) :
    ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
      Nonempty
        (ClusterData
          (canonicalApproximation
            (montelRefinement D e he))) := by
  let C := canonicalApproximation D
  have hdiff :
      ∀ k, DifferentiableOn ℂ
        (selectedFamily C k) centeredCriticalStrip := by
    intro k
    exact (canonicalApproximation_slotH1 D
      (D.parent (D.extract k))).differentiableOn
  have hbdd' :
      ∀ K : Set ℂ, IsCompact K →
        K ⊆ centeredCriticalStrip →
          ∃ M : ℝ, ∀ k : ℕ, ∀ z ∈ K,
            ‖selectedFamily C k z‖ ≤ M := by
    intro K hK hKsub
    obtain ⟨M, _hM, hbound⟩ := hbdd K hK hKsub
    exact ⟨M, hbound⟩
  have hzero : (0 : ℂ) ∈ centeredCriticalStrip := by
    simp [centeredCriticalStrip]
  have hanchor : ∀ k, selectedFamily C k 0 = centeredXi 0 := by
    intro k
    exact centeredPstarFamily_zero D.kTrial (D.parent (D.extract k))
  obtain ⟨e, he, L, hLdiff, hconv, _hLzero, hLne⟩ :=
    Q3.RouteB.montel_centeredCriticalStrip_anchor_nonzero_limit
      (selectedFamily C) 0 (centeredXi 0) hzero hdiff hbdd' hanchor hXi
  refine ⟨e, he, ⟨{
    limit := L
    limitHolomorphicOn := hLdiff
    convergence := ?_
    limitNonzero := hLne
  }⟩⟩
  simpa [C] using hconv

/-- Roof-facing same-parent Montel gate from the explicit strip-local analytic
inputs.  This theorem does not supply `SlotS1`; it packages the already-built
cluster under the four conditional roof premises. -/
theorem exists_refined_montelAnchorGate_of_strip_bounds
    (D : CanonicalData)
    (H2aAt S1At : CentralIndex D.kTrial → Prop)
    (hXi : centeredXi 0 ≠ 0)
    (hbdd :
      SelectedLocallyBoundedOnCenteredCriticalStrip D) :
    ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
      MontelAnchorGate
        (canonicalApproximation
          (montelRefinement D e he))
        H2aAt S1At 0 := by
  obtain ⟨e, he, hcluster⟩ :=
    exists_refined_clusterData_of_strip_bounds D hXi hbdd
  refine ⟨e, he, ?_⟩
  intro _hH1 _hH2a _hanchor _hS1
  exact hcluster

#print axioms exists_refined_clusterData_of_strip_bounds
#print axioms exists_refined_montelAnchorGate_of_strip_bounds

end Q3.RouteB.D0Pstar
