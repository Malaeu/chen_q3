import Q3.Proofs.RouteB.ProlateLayer

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

namespace Q3.RouteB.D0Pstar

/-- An even function with symmetric compact support and a Lipschitz positive
half is measurable.  Endpoint values may be arbitrary: the two endpoints form
a finite measurable exceptional set.

This is a representation lemma only.  It does not construct prolate modes or
prove that a source-defined mode has the required positive-half Lipschitz
bound. -/
theorem measurable_of_even_support_positiveHalfLipschitz
    (f : ℝ → ℂ) (lambda : ℝ) (K : NNReal)
    (heven : Function.Even f)
    (hsupp : Function.support f ⊆ Icc (-lambda) lambda)
    (hlip : LipschitzOnWith K f (Ico (0 : ℝ) lambda)) :
    Measurable f := by
  by_cases hlambda : 0 ≤ lambda
  · have habs_mem : ∀ {x : ℝ}, x ∈ Ioo (-lambda) lambda →
        |x| ∈ Ico (0 : ℝ) lambda := by
      intro x hx
      exact ⟨abs_nonneg x, abs_lt.mpr hx⟩
    have heq_abs : ∀ x : ℝ, f |x| = f x := by
      intro x
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos (le_of_not_ge hx)]
        exact heven x
    have hlipInterior : LipschitzOnWith K f (Ioo (-lambda) lambda) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      calc
        dist (f x) (f y) = dist (f |x|) (f |y|) := by
          rw [heq_abs x, heq_abs y]
        _ ≤ (K : ℝ) * dist |x| |y| :=
          hlip.dist_le_mul |x| (habs_mem hx) |y| (habs_mem hy)
        _ ≤ (K : ℝ) * dist x y := by
          gcongr
          simpa only [Real.dist_eq] using
            abs_abs_sub_abs_le_abs_sub x y
    have hzeroOutside : ∀ x ∈ (Icc (-lambda) lambda)ᶜ, f x = 0 := by
      intro x hx
      by_contra hne
      exact hx (hsupp hne)
    have hcontOutside : ContinuousOn f (Icc (-lambda) lambda)ᶜ :=
      continuousOn_const.congr hzeroOutside
    have hcontUnion : ContinuousOn f
        (Ioo (-lambda) lambda ∪ (Icc (-lambda) lambda)ᶜ) :=
      hlipInterior.continuousOn.union_of_isOpen hcontOutside
        isOpen_Ioo isClosed_Icc.isOpen_compl
    have hset : Ioo (-lambda) lambda ∪ (Icc (-lambda) lambda)ᶜ =
        ({-lambda, lambda} : Set ℝ)ᶜ := by
      ext x
      constructor
      · intro hx
        simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff]
        rintro (rfl | rfl)
        · rcases hx with hx | hx
          · exact (lt_irrefl _ hx.1)
          · exact hx ⟨le_rfl, by linarith⟩
        · rcases hx with hx | hx
          · exact (lt_irrefl _ hx.2)
          · exact hx ⟨by linarith, le_rfl⟩
      · intro hx
        simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff] at hx
        have hxleft : x ≠ -lambda := by
          intro h
          exact hx (Or.inl h)
        have hxright : x ≠ lambda := by
          intro h
          exact hx (Or.inr h)
        by_cases hmem : x ∈ Icc (-lambda) lambda
        · left
          exact ⟨lt_of_le_of_ne hmem.1 hxleft.symm,
            lt_of_le_of_ne hmem.2 hxright⟩
        · exact Or.inr hmem
    rw [hset] at hcontUnion
    exact measurable_of_measurable_on_compl_finite
      ({-lambda, lambda} : Set ℝ) (by simp)
      ((continuousOn_iff_continuous_restrict.mp hcontUnion).measurable)
  · have hzero : f = 0 := by
      funext x
      by_contra hne
      have hx := hsupp hne
      have hneg_le : -lambda ≤ lambda := hx.1.trans hx.2
      exact hlambda (by linarith)
    rw [hzero]
    exact measurable_const

#print axioms measurable_of_even_support_positiveHalfLipschitz

end Q3.RouteB.D0Pstar
