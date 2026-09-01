import Q3.Proofs.RouteB.D0PstarSelectedFerrersEvenTailCutoffObstruction

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Adaptive reuse obstruction for the selected Ferrers finite carrier

The existing explicit source-Weil even-tail theorem begins at
`sourceWeilEvenTailCutoff`.  This file proves that no later cutoff can be at
most the literal selected endpoint `N`.  It kills only reuse of that existing
theorem through an adaptive cutoff; it says nothing about a new source-specific
estimate valid at an earlier cutoff.
-/

/-- No adaptive cutoff that starts at or after the existing explicit
source-Weil tail cutoff can be at most the literal selected endpoint. -/
theorem selectedFerrersPreAnchorIndex_no_tailCutoff_between_fixed_and_N
    (k : ℕ) :
    ¬ ∃ R : ℕ,
      sourceWeilEvenTailCutoff (selectedFerrersPreAnchorIndex k) ≤ R ∧
        R ≤ (selectedFerrersPreAnchorIndex k).N := by
  rintro ⟨R, hfixed, hN⟩
  exact selectedFerrersPreAnchorIndex_not_cutoff_le_N k (hfixed.trans hN)

#print axioms selectedFerrersPreAnchorIndex_no_tailCutoff_between_fixed_and_N

end Q3.RouteB.D0Pstar
