/-
Heat kernel error bounds for A1' density theorem.

Key insight: On the support of FejerKernel δ (x-τ), we have |x-τ| ≤ δ,
so |Heat(x-τ) - Heat(0)| ≤ L*δ by Lipschitz continuity.

This bounds the error when replacing Heat(x-τ) with H0 = Heat(0) in atom approximation.
-/

import Q3.Proofs.A1_density

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HeatError

/-- On support of Fejér kernel, the argument is bounded by δ -/
lemma FejerKernel_support_bound (δ : ℝ) (hδ : δ > 0) (y : ℝ)
    (hsupp : FejerKernel δ y > 0) : |y| ≤ δ := by
  unfold FejerKernel at hsupp
  -- From max(0, 1 - |y|/δ) > 0, we get 1 - |y|/δ > 0
  by_contra h_neg
  push_neg at h_neg
  have h_le : 1 - |y| / δ ≤ 0 := by
    have hy_pos : |y| > δ := h_neg
    have : |y| / δ > 1 := (one_lt_div hδ).mpr hy_pos
    linarith
  have h_max : max 0 (1 - |y| / δ) = 0 := max_eq_left h_le
  linarith

/-- Heat kernel error on Fejér support: |Heat(y) - Heat(0)| ≤ L*|y| for y in [-R,R] -/
lemma heat_error_bound (t : ℝ) (ht : t > 0) (R : ℝ) (hR : R > 0) :
    ∃ L > 0, ∀ y ∈ Set.Icc (-R) R,
      |HeatKernel t y - HeatKernel t 0| ≤ L * |y| := by
  obtain ⟨L, hL_pos, hL_lip⟩ := HeatKernel_LipschitzOn t ht R hR
  refine ⟨L, hL_pos, ?_⟩
  intro y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-R) R := by
    simp only [Set.mem_Icc]
    constructor <;> linarith
  have := hL_lip y hy 0 h0
  simp only [sub_zero] at this
  exact this

/-- Combined atom-heat error: works for any x, τ, returns bound in terms of L from Lipschitz -/
lemma atom_heat_error_with_L (t δ : ℝ) (ht : t > 0) (hδ : δ > 0) (τ x : ℝ)
    (L : ℝ) (hL_pos : L > 0)
    (hL_lip : ∀ y ∈ Set.Icc (-δ) δ, ∀ z ∈ Set.Icc (-δ) δ,
              |HeatKernel t y - HeatKernel t z| ≤ L * |y - z|) :
    |FejerKernel δ (x - τ) * HeatKernel t (x - τ) - FejerKernel δ (x - τ) * HeatKernel t 0| ≤
      FejerKernel δ (x - τ) * L * δ := by
  by_cases hF : FejerKernel δ (x - τ) > 0
  · -- Case: Fejér > 0, so |x - τ| ≤ δ
    have hsupp := FejerKernel_support_bound δ hδ (x - τ) hF
    -- Factor out Fejér
    have h_factor : FejerKernel δ (x - τ) * HeatKernel t (x - τ) -
        FejerKernel δ (x - τ) * HeatKernel t 0 =
        FejerKernel δ (x - τ) * (HeatKernel t (x - τ) - HeatKernel t 0) := by ring
    rw [h_factor, abs_mul]
    -- Fejér ≥ 0
    have hF_nonneg : 0 ≤ FejerKernel δ (x - τ) := (FejerKernel_bounds δ hδ (x - τ)).1
    rw [abs_of_nonneg hF_nonneg]
    -- Apply Lipschitz
    have h0_in : (0 : ℝ) ∈ Set.Icc (-δ) δ := by
      simp only [Set.mem_Icc]
      constructor <;> linarith
    have hxτ_in : (x - τ) ∈ Set.Icc (-δ) δ := by
      simp only [Set.mem_Icc]
      rw [abs_le] at hsupp
      exact hsupp
    have h_heat_lip := hL_lip (x - τ) hxτ_in 0 h0_in
    simp only [sub_zero] at h_heat_lip
    -- Bound: |Heat(x-τ) - Heat(0)| ≤ L * |x-τ| ≤ L * δ
    calc FejerKernel δ (x - τ) * |HeatKernel t (x - τ) - HeatKernel t 0|
        ≤ FejerKernel δ (x - τ) * (L * |x - τ|) := by
          apply mul_le_mul_of_nonneg_left h_heat_lip hF_nonneg
      _ ≤ FejerKernel δ (x - τ) * (L * δ) := by
          apply mul_le_mul_of_nonneg_left _ hF_nonneg
          apply mul_le_mul_of_nonneg_left hsupp (le_of_lt hL_pos)
      _ = FejerKernel δ (x - τ) * L * δ := by ring
  · -- Case: Fejér ≤ 0, so Fejér = 0
    push_neg at hF
    have hF_nonneg := (FejerKernel_bounds δ hδ (x - τ)).1
    have hF_zero : FejerKernel δ (x - τ) = 0 := le_antisymm hF hF_nonneg
    simp [hF_zero]

/-- Main theorem: total error bound for sum of atoms.
    When we approximate ∑ c_i * Fejér(x-τ_i) * Heat(x-τ_i) by ∑ c_i * Fejér(x-τ_i) * H0,
    the error is bounded by M * L * δ where M = ∑ c_i. -/
theorem total_atom_error (t δ : ℝ) (ht : t > 0) (hδ : δ > 0)
    {n : ℕ} (c : Fin n → ℝ) (hc_nonneg : ∀ i, c i ≥ 0) (τ : Fin n → ℝ) (x : ℝ)
    (L : ℝ) (hL_pos : L > 0)
    (hL_lip : ∀ y ∈ Set.Icc (-δ) δ, ∀ z ∈ Set.Icc (-δ) δ,
              |HeatKernel t y - HeatKernel t z| ≤ L * |y - z|) :
    let H0 := HeatKernel t 0
    let M := ∑ i, c i
    |∑ i, c i * FejerKernel δ (x - τ i) * HeatKernel t (x - τ i) -
     ∑ i, c i * FejerKernel δ (x - τ i) * H0| ≤ M * L * δ := by
  intro H0 M
  -- Rewrite as sum of differences
  have h_diff : ∑ i, c i * FejerKernel δ (x - τ i) * HeatKernel t (x - τ i) -
      ∑ i, c i * FejerKernel δ (x - τ i) * H0 =
      ∑ i, c i * (FejerKernel δ (x - τ i) * HeatKernel t (x - τ i) -
                  FejerKernel δ (x - τ i) * H0) := by
    simp only [← Finset.sum_sub_distrib]
    congr 1
    ext i
    ring
  rw [h_diff]
  -- Bound absolute value of sum by sum of absolute values
  calc |∑ i, c i * (FejerKernel δ (x - τ i) * HeatKernel t (x - τ i) -
                    FejerKernel δ (x - τ i) * H0)|
      ≤ ∑ i, |c i * (FejerKernel δ (x - τ i) * HeatKernel t (x - τ i) -
                      FejerKernel δ (x - τ i) * H0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, c i * |FejerKernel δ (x - τ i) * HeatKernel t (x - τ i) -
                    FejerKernel δ (x - τ i) * H0| := by
        congr 1
        ext i
        rw [abs_mul, abs_of_nonneg (hc_nonneg i)]
    _ ≤ ∑ i, c i * (FejerKernel δ (x - τ i) * L * δ) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hc_nonneg i)
        exact atom_heat_error_with_L t δ ht hδ (τ i) x L hL_pos hL_lip
    _ ≤ ∑ i, c i * (1 * L * δ) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hc_nonneg i)
        apply mul_le_mul_of_nonneg_right _ (by linarith : δ ≥ 0)
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hL_pos)
        exact (FejerKernel_bounds δ hδ (x - τ i)).2
    _ = M * L * δ := by
        simp only [one_mul, M, ← Finset.sum_mul]
        ring

end HeatError

end
