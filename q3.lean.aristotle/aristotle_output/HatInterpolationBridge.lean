/-
Bridge file to use Aristotle's hat_interpolation_approx result.

This provides the hat interpolation theorem without exporting FejerKernel,
to avoid name conflicts with Q3/Proofs/A1_density.lean.
-/

import aristotle_output.hat_interpolation_approx

open scoped BigOperators

namespace HatInterpolationBridge

-- The FejerKernel definitions differ only by argument order in max:
-- Aristotle: max (1 - |x| / δ) 0
-- A1_density: max 0 (1 - |x| / B)
-- They are equal by max_comm.

lemma fejer_kernel_comm (δ x : ℝ) : max (1 - |x| / δ) 0 = max 0 (1 - |x| / δ) :=
  max_comm _ _

/-- Main theorem: Hat interpolation with boundary vanishing condition.
    Uses Aristotle's FejerKernel definition internally. -/
theorem hat_interpolation_boundary_vanish (K : ℝ) (hK : K > 0) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc (-K) K))
    (hf_nonneg : ∀ x ∈ Set.Icc (-K) K, 0 ≤ f x)
    (hf_boundary : f (-K) = 0 ∧ f K = 0)
    (ε : ℝ) (hε : ε > 0) :
    ∃ (n : ℕ) (τ : Fin n → ℝ) (δ : ℝ),
      n > 0 ∧ δ > 0 ∧
      (∀ i, τ i ∈ Set.Ioo (-K) K) ∧
      (∀ i, |τ i| + δ ≤ K) ∧
      -- Using max 0 (1 - |x|/δ) form (matches A1_density.FejerKernel)
      (∀ x ∈ Set.Icc (-K) K,
        |∑ i, f (τ i) * max 0 (1 - |x - τ i| / δ) - f x| < ε) ∧
      (∀ x ∈ Set.Icc (-K) K,
        0 ≤ ∑ i, f (τ i) * max 0 (1 - |x - τ i| / δ)) := by
  -- Use Aristotle's theorem
  obtain ⟨n, τ, δ, hn, hδ, hτ_in, hτ_margin, h_approx, h_nonneg⟩ :=
    hat_interpolation_approx_of_boundary_vanish K hK f hf_cont hf_nonneg hf_boundary ε hε
  refine ⟨n, τ, δ, hn, hδ, hτ_in, hτ_margin, ?_, ?_⟩
  -- Convert between FejerKernel definitions using max_comm
  · intro x hx
    have := h_approx x hx
    simp only [FejerKernel] at this
    have heq : ∀ i, max (1 - |x - τ i| / δ) 0 = max 0 (1 - |x - τ i| / δ) := fun i => max_comm _ _
    simp only [heq] at this
    exact this
  · intro x hx
    have := h_nonneg x hx
    simp only [FejerKernel] at this
    have heq : ∀ i, max (1 - |x - τ i| / δ) 0 = max 0 (1 - |x - τ i| / δ) := fun i => max_comm _ _
    simp only [heq] at this
    exact this

end HatInterpolationBridge
