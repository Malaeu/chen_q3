/-
Debug file to find hanging proof - HEAVY parts
Testing P_A_tsum_eq_finite_sum and integral_P_A_eq_arch_term
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.ShiftedWindows
import A3_FLOOR_v22_stage4_floor

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate

-- Start with moderate limit
set_option maxHeartbeats 400000

noncomputable section

namespace Q3.Debug.Heavy

#print "=== HEAVY TEST START ==="

-- Copy needed lemmas
lemma w_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : w B t ξ = 0 := by
  simp only [w]
  have h1 : 1 - |ξ| / B < 0 := by
    have : 1 < |ξ| / B := by rw [one_lt_div hB]; exact h
    linarith
  rw [max_eq_left (le_of_lt h1)]
  ring

lemma g_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : g B t ξ = 0 := by
  simp only [g, w_support B t ξ hB h, mul_zero]

#print "=== CHECKPOINT H1: support lemmas OK ==="

lemma g_shift_zero_of_large_m (B t θ : ℝ) (m : ℤ) (hB : 0 < B)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : (⌈B⌉ : ℤ) + 1 < |m|) : g B t (θ + m) = 0 := by
  apply g_support B t (θ + m) hB
  have h1 : (B : ℝ) + 1 ≤ |m| := by
    have : (⌈B⌉ : ℝ) + 1 < |m| := by exact_mod_cast hm
    have hceil : B ≤ ⌈B⌉ := Int.le_ceil B
    linarith
  have hθ_abs : |θ| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  have h_tri : (|(m : ℝ)| - |θ|) ≤ |θ + (m : ℝ)| := by
    have h1 := abs_sub_abs_le_abs_sub (m : ℝ) (-θ)
    simp only [abs_neg, sub_neg_eq_add] at h1
    calc |(m : ℝ)| - |θ| ≤ |(m : ℝ) + θ| := h1
      _ = |θ + (m : ℝ)| := by ring_nf
  have h_m_bound : (B : ℝ) + 1 ≤ |(m : ℝ)| := by
    have h1 : (⌈B⌉ : ℝ) + 1 < |m| := by exact_mod_cast hm
    have h2 : B ≤ ⌈B⌉ := Int.le_ceil B
    have h3 : (|m| : ℝ) = |(m : ℝ)| := by simp only [Int.cast_abs]
    linarith
  calc B < B + 1/2 := by linarith
    _ ≤ |(m : ℝ)| - 1/2 := by linarith
    _ ≤ |(m : ℝ)| - |θ| := by linarith
    _ ≤ |θ + (m : ℝ)| := h_tri
    _ = |θ + m| := by norm_cast

#print "=== CHECKPOINT H2: g_shift_zero_of_large_m OK ==="

-- THIS IS THE SUSPECT - test it with profiling
set_option maxHeartbeats 600000 in
set_option profiler true in
lemma P_A_tsum_eq_finite_sum (B t θ : ℝ) (hB : 0 < B) (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    ∑' (m : ℤ), g B t (θ + m) =
    ∑ m ∈ Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1), g B t (θ + m) := by
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  have hceil_pos : (0 : ℤ) < ⌈B⌉ + 1 := by
    have : (0 : ℤ) ≤ ⌈B⌉ := Int.ceil_nonneg (le_of_lt hB)
    omega
  have h_large : (⌈B⌉ : ℤ) + 1 < |m| := by
    by_cases h : m < -(⌈B⌉ + 1)
    · have hm_neg : m < 0 := by omega
      simp only [abs_of_neg hm_neg]
      omega
    · push_neg at h
      have := hm h
      have hm_nonneg : 0 ≤ m := by omega
      simp only [abs_of_nonneg hm_nonneg]
      exact this
  exact g_shift_zero_of_large_m B t θ m hB hθ h_large

#print "=== CHECKPOINT H3: P_A_tsum_eq_finite_sum OK ==="

end Q3.Debug.Heavy

#print "=== HEAVY TEST COMPLETE ==="
