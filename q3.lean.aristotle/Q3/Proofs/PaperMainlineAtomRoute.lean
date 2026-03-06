import Q3.AxiomsTheorems
import Q3.Proofs.CompatibilityReduction

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical Pointwise

noncomputable section

namespace Q3.Proofs.PaperMainlineAtomRoute

open Q3

/--
Extract a compact window `W_K` from a Weil-cone test function.

This is the only topological step needed to turn compact support into the
compact-by-compact positivity route coming from `CompatibilityReduction`.
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
Paper-style mainline positivity: the current `t_critical` shifted-atom route
already gives nonnegativity of `Q` on the full Weil cone.
-/
theorem Q_nonneg_on_Weil_cone_current_atom_route :
    ∀ Φ ∈ Weil_cone, Q Φ ≥ 0 := by
  intro Φ hΦ
  rcases exists_WK_of_mem_Weil_cone Φ hΦ with ⟨K, hK, hWK⟩
  exact
    Q3.Proofs.CompatibilityReduction.Q_nonneg_on_WK_tcritical_current_atom_route
      K hK Φ hWK

/--
Riemann Hypothesis from the shifted-atom mainline at `t_critical`.

This theorem bypasses the legacy `τ = 0` cone and uses the full Weil criterion.
-/
theorem RH_of_shifted_atom_route : RH := by
  rw [← Weil_criterion]
  exact Q_nonneg_on_Weil_cone_current_atom_route

end Q3.Proofs.PaperMainlineAtomRoute

namespace Q3

/-- Root-level wrapper for the new full-Weil shifted-atom route. -/
theorem Q_nonneg_on_Weil_cone_current_atom_route :
    ∀ Φ ∈ Weil_cone, Q Φ ≥ 0 :=
  Q3.Proofs.PaperMainlineAtomRoute.Q_nonneg_on_Weil_cone_current_atom_route

/-- Root-level RH theorem via the shifted-atom paper mainline. -/
theorem RH_of_shifted_atom_route : RH :=
  Q3.Proofs.PaperMainlineAtomRoute.RH_of_shifted_atom_route

end Q3

