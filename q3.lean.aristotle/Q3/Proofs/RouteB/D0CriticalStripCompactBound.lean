import Q3.Proofs.RouteB.D0CriticalMomentStripBound

set_option linter.mathlibStandardSet false

open Complex Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-- Compact-local boundedness of the exact selected family on the open
centered critical strip. -/
def SelectedLocallyBoundedOnCenteredCriticalStrip
    (D : CanonicalData) : Prop :=
  ∀ K : Set ℂ, IsCompact K →
    K ⊆ centeredCriticalStrip →
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ k : ℕ, ∀ z ∈ K,
          ‖selectedFamily
            (canonicalApproximation D) k z‖ ≤ M

/-- Every compact subset of the open centered critical strip lies in one
strict closed centered substrip. -/
theorem compact_subset_centeredCriticalStrip_contained_in_closed_substrip
    {K : Set ℂ}
    (hK : IsCompact K)
    (hsub : K ⊆ centeredCriticalStrip) :
    ∃ σ : ℝ,
      0 ≤ σ ∧
      σ < 1 / 2 ∧
      ∀ z ∈ K, |z.im| ≤ σ := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, le_rfl, by norm_num, by simp⟩
  · have hcont : ContinuousOn (fun z : ℂ => |z.im|) K :=
      (continuous_abs.comp Complex.continuous_im).continuousOn
    obtain ⟨z₀, hz₀, hz₀max⟩ := hK.exists_isMaxOn hKne hcont
    refine ⟨|z₀.im|, abs_nonneg _, ?_, ?_⟩
    · exact hsub hz₀
    · intro z hz
      exact hz₀max hz

/-- A closed-substrip bound transfers to the compact-local boundedness
quantifier required by a Montel theorem on the open centered strip. -/
theorem selectedLocallyBoundedOnCenteredCriticalStrip_of_closedSubstripBounded
    (D : CanonicalData)
    (hbdd : SelectedPostAnchorClosedSubstripBounded D) :
    SelectedLocallyBoundedOnCenteredCriticalStrip D := by
  intro K hK hsub
  obtain ⟨σ, hσ, hσhalf, hKσ⟩ :=
    compact_subset_centeredCriticalStrip_contained_in_closed_substrip hK hsub
  obtain ⟨M, hM, hbound⟩ := hbdd σ hσ hσhalf
  exact ⟨M, hM, fun k z hz => hbound k z (hKσ z hz)⟩

#print axioms compact_subset_centeredCriticalStrip_contained_in_closed_substrip
#print axioms selectedLocallyBoundedOnCenteredCriticalStrip_of_closedSubstripBounded

end Q3.RouteB.D0Pstar
