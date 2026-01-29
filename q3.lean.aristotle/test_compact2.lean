import Mathlib

example (f : ℝ → ℝ) (hf : HasCompactSupport f) : 
    ∃ K ≥ 1, Function.support f ⊆ Set.Icc (-K) K := by
  obtain ⟨M, hM⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hf.isCompact.isBounded
  use max M 1
  constructor
  · exact le_max_right M 1
  · intro x hx
    have h1 : x ∈ tsupport f := subset_tsupport f hx
    have h2 : x ∈ Metric.ball 0 M := hM h1
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h2
    have hM1 : M ≤ max M 1 := le_max_left M 1
    constructor
    · linarith [abs_nonneg x, neg_abs_le x]
    · linarith [le_abs_self x]
