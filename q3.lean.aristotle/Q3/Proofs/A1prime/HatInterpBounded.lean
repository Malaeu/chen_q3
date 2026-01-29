/-
Hat interpolation with bounded mesh size.
This extends HatInterpolation.lean with an additional δ ≤ δ_max constraint,
which is needed to control heat kernel error in the A1' density theorem.

Key insight: exists_suitable_grid already gives δ < δ_target,
so we just need to choose δ_target ≤ δ_max to ensure δ ≤ δ_max.
-/

import Q3.Proofs.HatInterpolation

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HatInterp

/-- Hat interpolation with bounded mesh size.
    Same as hat_interpolation_approx but with additional δ ≤ δ_max constraint.
    This is essential for controlling the heat kernel approximation error. -/
lemma hat_interpolation_approx_bounded (K : ℝ) (hK : K > 0) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc (-K) K))
    (hf_nonneg : ∀ x ∈ Set.Icc (-K) K, 0 ≤ f x)
    (hf_boundary : f (-K) = 0 ∧ f K = 0)
    (ε : ℝ) (hε : ε > 0)
    (δ_max : ℝ) (hδ_max : δ_max > 0) :
    ∃ (n : ℕ) (τ : Fin n → ℝ) (δ : ℝ),
      n > 0 ∧
      δ > 0 ∧
      δ ≤ δ_max ∧  -- NEW: bounded mesh
      (∀ i, τ i ∈ Set.Ioo (-K) K) ∧
      (∀ i, |τ i| + δ ≤ K) ∧
      (∀ x ∈ Set.Icc (-K) K, |∑ i, f (τ i) * FejerKernel δ (x - τ i) - f x| < ε) ∧
      (∀ x ∈ Set.Icc (-K) K, 0 ≤ ∑ i, f (τ i) * FejerKernel δ (x - τ i)) := by
  -- Use the original hat_interpolation_approx with modified δ_target
  -- that includes δ_max in the minimum

  -- Step 1: Get uniform continuity modulus
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ : ∃ δ₀ > 0, ∀ x y, x ∈ Set.Icc (-K) K → y ∈ Set.Icc (-K) K →
      |x - y| < δ₀ → |f x - f y| < ε / 2 := by
    have := Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hf_cont)
            (ε / 2) (half_pos hε)
    aesop

  -- Step 2: Get boundary continuity modulus
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x, x ∈ Set.Icc (-K) K →
      |x + K| < δ₁ ∨ |x - K| < δ₁ → |f x| < ε / 2 := by
    grind

  -- Step 3: Choose δ_target to satisfy BOTH approximation AND bounded mesh
  set δ_target := min δ₀ (min δ₁ (min K δ_max)) with hδ_target_def

  have hδ_target_pos : δ_target > 0 := by
    simp only [δ_target]
    exact lt_min hδ₀_pos (lt_min hδ₁_pos (lt_min hK hδ_max))

  -- Step 4: Use exists_suitable_grid
  obtain ⟨n, δ, hn, hδ, hδ_lt, hδ_eq⟩ := exists_suitable_grid K hK δ_target hδ_target_pos

  -- Step 5: Verify δ ≤ δ_max (key new property)
  have hδ_le_max : δ ≤ δ_max := by
    have h1 : δ < δ_target := hδ_lt
    have h2 : δ_target ≤ min δ₁ (min K δ_max) := min_le_right δ₀ _
    have h3 : min δ₁ (min K δ_max) ≤ min K δ_max := min_le_right δ₁ _
    have h4 : min K δ_max ≤ δ_max := min_le_right K δ_max
    linarith

  -- Step 5b: Also useful: δ < δ₀ and δ < δ₁
  have hδ_lt_δ₀ : δ < δ₀ := by
    have : δ_target ≤ δ₀ := min_le_left _ _
    linarith

  have hδ_lt_δ₁ : δ < δ₁ := by
    have h1 : δ_target ≤ min δ₁ (min K δ_max) := min_le_right δ₀ _
    have h2 : min δ₁ (min K δ_max) ≤ δ₁ := min_le_left _ _
    linarith

  -- Step 6: Construct the grid τ : Fin n → ℝ
  let τ : Fin n → ℝ := fun i => -K + (i + 1) * δ

  -- Helper: i + 1 ≤ n for Fin n
  have hi_bound : ∀ i : Fin n, (i : ℝ) + 1 ≤ n := by
    intro i
    have := Fin.is_lt i
    exact_mod_cast Nat.succ_le_of_lt this

  -- Helper: (n+1)*δ = 2K
  have h_grid_span : (n + 1 : ℝ) * δ = 2 * K := by
    rw [hδ_eq]
    field_simp

  -- Helper: n*δ < 2K (since δ > 0)
  have h_nδ_lt : (n : ℝ) * δ < 2 * K := by
    have : (n : ℝ) < n + 1 := by linarith
    nlinarith [mul_pos (show (0 : ℝ) < n + 1 by linarith) hδ]

  -- Step 7: Verify all properties
  refine ⟨n, τ, δ, hn, hδ, hδ_le_max, ?_, ?_, ?_, ?_⟩

  -- Property 1: τ i ∈ (-K, K)
  · intro i
    simp only [τ, Set.mem_Ioo]
    constructor
    · -- -K < -K + (i+1)*δ
      have hi_pos : (i : ℝ) + 1 > 0 := by positivity
      linarith [mul_pos hi_pos hδ]
    · -- -K + (i+1)*δ < K
      have hi := hi_bound i
      -- (i+1)*δ ≤ n*δ < 2K, so -K + (i+1)*δ < -K + 2K = K
      nlinarith [mul_le_mul_of_nonneg_right hi hδ.le]

  -- Property 2: |τ i| + δ ≤ K
  · intro i
    simp only [τ]
    have hi := hi_bound i
    -- τ i = -K + (i+1)*δ where (i+1) ≤ n, so 0 < (i+1)*δ ≤ n*δ < 2K
    -- Hence -K < τ i < K
    have hτ_lower : -K < -K + (↑i + 1) * δ := by
      have : (i : ℝ) + 1 > 0 := by positivity
      linarith [mul_pos this hδ]
    have hτ_upper : -K + (↑i + 1) * δ < K := by
      nlinarith [mul_le_mul_of_nonneg_right hi hδ.le]
    -- |τ i| + δ ≤ K
    -- Since i+2 ≤ n+1 and (n+1)*δ = 2K, we have (i+2)*δ ≤ 2K
    -- Case: τ i ≥ 0, then |τ i| = τ i, need τ i + δ ≤ K, i.e., (i+2)*δ ≤ 2K
    -- Case: τ i < 0, then |τ i| = -τ i = K - (i+1)*δ, need K - (i+1)*δ + δ ≤ K, i.e., δ ≤ (i+1)*δ (true)
    have hi2 : (i : ℝ) + 2 ≤ n + 1 := by
      have hilt := Fin.is_lt i
      have hilt2 : (i : ℕ) + 1 < n + 1 := Nat.succ_lt_succ hilt
      have : (i : ℝ) + 1 < (n : ℝ) + 1 := by exact_mod_cast hilt2
      linarith
    have h_key : (↑i + 2) * δ ≤ 2 * K := by
      nlinarith [mul_le_mul_of_nonneg_right hi2 hδ.le]
    -- |τ i| + δ ≤ K
    -- Since -K < τ i < K, we split on sign
    by_cases hτ_sign : 0 ≤ -K + (↑i + 1) * δ
    · -- Case τ i ≥ 0: |τ i| = τ i, need τ i + δ ≤ K
      rw [abs_of_nonneg hτ_sign]
      -- -K + (i+1)*δ + δ = -K + (i+2)*δ ≤ -K + 2K = K
      linarith
    · -- Case τ i < 0: |τ i| = -τ i = K - (i+1)*δ
      push_neg at hτ_sign
      rw [abs_of_neg hτ_sign]
      -- -(−K + (i+1)*δ) + δ = K - (i+1)*δ + δ = K - i*δ ≤ K
      have : (i : ℝ) ≥ 0 := Nat.cast_nonneg _
      nlinarith [mul_nonneg this hδ.le]

  -- Property 3: Approximation bound
  · intro x ⟨hx_lo, hx_hi⟩
    -- Use hat_interpolation_verify from HatInterpolation.lean
    have h_approx := hat_interpolation_verify K hK f ε hε n hn τ δ hδ
      (fun i => rfl) hδ_eq
      (fun x y hx hy hxy => hδ₀ x y hx hy (lt_of_le_of_lt hxy hδ_lt_δ₀))
      (fun x hx hx' => hδ₁ x hx (Or.imp
        (fun h => lt_of_lt_of_le h hδ_lt_δ₁.le)
        (fun h => lt_of_lt_of_le h hδ_lt_δ₁.le)
        hx'))
      hf_boundary x ⟨hx_lo, hx_hi⟩
    exact h_approx

  -- Property 4: Nonnegativity
  · intro x ⟨hx_lo, hx_hi⟩
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg
    · -- f (τ i) ≥ 0
      apply hf_nonneg
      simp only [τ, Set.mem_Icc]
      have hi := hi_bound i
      constructor
      · have : (i : ℝ) + 1 > 0 := by positivity
        linarith [mul_pos this hδ]
      · nlinarith [mul_le_mul_of_nonneg_right hi hδ.le]
    · -- FejerKernel δ _ ≥ 0
      exact (fejer_bounds δ hδ _).1

end HatInterp

end
