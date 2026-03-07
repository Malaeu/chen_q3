import Q3.AxiomsTheorems
import Q3.Proofs.CompatibilityReduction

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical Pointwise

noncomputable section

namespace Q3.Proofs.PaperMainlineAtomRoute

open Q3

/--
Extract a broad-cone compact window `W_K` from a `Weil_cone` test function.

After the 2026-03-07 target-cone audit this belongs to the compiled
background route only; it no longer defines the public RH target.
-/
lemma exists_WK_of_mem_Weil_cone (Φ : ℝ → ℝ) (hΦ : Φ ∈ Weil_cone) :
    ∃ K ≥ 1, Φ ∈ W_K K := by
  rcases hΦ with ⟨hEven, hNonneg, hCompact, hCont⟩
  obtain ⟨R, hRball⟩ :=
    (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hCompact.isCompact.isBounded
  refine ⟨max (R + 1) 1, le_max_right _ _, ?_⟩
  refine ⟨hCont, ?_, hEven, hNonneg⟩
  intro x hx
  have hxt : x ∈ tsupport Φ := subset_tsupport Φ hx
  have hxball : x ∈ Metric.ball 0 R := hRball hxt
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hxball
  have hR_lt : R < max (R + 1) 1 := by
    have hR_lt_succ : R < R + 1 := by linarith
    exact lt_of_lt_of_le hR_lt_succ (le_max_left _ _)
  have habs_lt : |x| < max (R + 1) 1 := lt_trans hxball hR_lt
  have hleft : -max (R + 1) 1 < x := by
    have hneg : -|x| ≤ x := neg_abs_le x
    linarith
  have hright : x < max (R + 1) 1 := by
    exact lt_of_le_of_lt (le_abs_self x) habs_lt
  exact ⟨hleft, hright⟩

/--
Paper-style broad-cone positivity node for the current `t_critical`
shifted-atom route.

This theorem packages the compiled broad-cone route. After the target-cone
audit it should be read as a background export only. Its mathematical honesty
also still depends on the live scalar placeholder inherited from
`Q_nonneg_t_critical`.
-/
theorem Q_nonneg_on_Weil_cone_current_atom_route :
    ∀ Φ ∈ Weil_cone, Q Φ ≥ 0 := by
  intro Φ hΦ
  rcases exists_WK_of_mem_Weil_cone Φ hΦ with ⟨K, hK, hWK⟩
  exact
    Q3.Proofs.CompatibilityReduction.Q_nonneg_on_WK_tcritical_current_atom_route
      K hK Φ hWK

/--
Current RH theorem obtained from the shifted-atom compiled broad-cone route at
`t_critical`.

This theorem bypasses the legacy `τ = 0` cone and uses the broad `Weil_cone`
export, but after the target-cone audit it should be read as background route
structure rather than as the public gate-by-gate RH contract.
-/
theorem RH_of_shifted_atom_route : RH := by
  rw [← Weil_criterion]
  exact Q_nonneg_on_Weil_cone_current_atom_route

end Q3.Proofs.PaperMainlineAtomRoute

namespace Q3

/-- Root-level wrapper for the current compiled broad-cone shifted-atom route. -/
theorem Q_nonneg_on_Weil_cone_current_atom_route :
    ∀ Φ ∈ Weil_cone, Q Φ ≥ 0 :=
  Q3.Proofs.PaperMainlineAtomRoute.Q_nonneg_on_Weil_cone_current_atom_route

/-- Root-level RH wrapper via the current compiled broad-cone route. -/
theorem RH_of_shifted_atom_route : RH :=
  Q3.Proofs.PaperMainlineAtomRoute.RH_of_shifted_atom_route

end Q3
