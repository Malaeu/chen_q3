/-
Debug file to test integral_P_A_eq_arch_term
This is the MAIN suspect for the hanging build
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.ShiftedWindows
import A3_FLOOR_v22_stage4_floor

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate

set_option maxHeartbeats 400000

noncomputable section

namespace Q3.Debug.Integral

#print "=== INTEGRAL TEST START ==="

-- Copy all needed lemmas first
lemma w_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : w B t ξ = 0 := by
  simp only [w]
  have h1 : 1 - |ξ| / B < 0 := by
    have : 1 < |ξ| / B := by rw [one_lt_div hB]; exact h
    linarith
  rw [max_eq_left (le_of_lt h1)]
  ring

lemma g_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : g B t ξ = 0 := by
  simp only [g, w_support B t ξ hB h, mul_zero]

lemma continuous_w (B t : ℝ) : Continuous (fun ξ => w B t ξ) := by
  unfold w
  continuity

lemma continuous_g (B t : ℝ) : Continuous (fun ξ => g B t ξ) := by
  unfold g
  exact Q3.a_star_continuous.div_const.mul (continuous_w B t)

lemma w_eq_fejer_heat_window (B t ξ : ℝ) : w B t ξ = Q3.fejer_heat_window B t ξ := by
  simp only [w, Q3.fejer_heat_window]

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
    calc B + 1 ≤ ⌈B⌉ + 1 := by linarith [Int.le_ceil B]
      _ < |m| := by exact_mod_cast hm
      _ = |(m : ℝ)| := by simp
  calc B < B + 1/2 := by linarith
    _ ≤ |(m : ℝ)| - 1/2 := by linarith
    _ ≤ |(m : ℝ)| - |θ| := by linarith
    _ ≤ |θ + (m : ℝ)| := h_tri
    _ = |θ + m| := by norm_cast

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
      simp only [abs_of_neg hm_neg]; omega
    · push_neg at h
      have := hm h
      have hm_nonneg : 0 ≤ m := by omega
      simp only [abs_of_nonneg hm_nonneg]; exact this
  exact g_shift_zero_of_large_m B t θ m hB hθ h_large

#print "=== CHECKPOINT I1: Preliminary lemmas OK ==="

lemma arch_term_eq_two_pi_integral_g (B t : ℝ) :
    Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) =
      2 * Real.pi * ∫ ξ, Q3.a ξ * w B t ξ := by
  simp only [Q3.arch_term]
  have hw : ∀ ξ, w B t ξ = Q3.fejer_heat_window B t ξ := w_eq_fejer_heat_window B t
  simp_rw [hw]
  have h : ∀ ξ, Q3.a_star ξ * Q3.fejer_heat_window B t ξ =
      2 * Real.pi * (Q3.a ξ * Q3.fejer_heat_window B t ξ) := by
    intro ξ
    simp only [Q3.a_star]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_mul_left]

#print "=== CHECKPOINT I2: arch_term_eq_two_pi_integral_g OK ==="

-- NOW test the MAIN theorem - break it into pieces
#print "=== TESTING integral_P_A_eq_arch_term - STEP BY STEP ==="

-- Step 1: Test setup
set_option maxHeartbeats 200000 in
set_option profiler true in
lemma integral_setup (B t : ℝ) (hB : 0 < B) :
    let hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
    let s : Finset ℤ := Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1)
    let hsupp : Function.support (fun ξ => g B t ξ) ⊆ Set.Icc (-B) B := by
      refine (Function.support_subset_iff'.2 ?_)
      intro ξ hξ
      by_contra hle
      have hle' : |ξ| ≤ B := le_of_not_gt hle
      have : ξ ∈ Set.Icc (-B) B := abs_le.mp hle'
      exact hξ this
    let hcompact : HasCompactSupport (fun ξ => g B t ξ) :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
    Integrable (fun ξ => g B t ξ) := by
      exact (continuous_g B t).integrable_of_hasCompactSupport hcompact

#print "=== CHECKPOINT I3: integral_setup OK ==="

-- Step 2: Test EqOn
set_option maxHeartbeats 200000 in
set_option profiler true in
lemma integral_eq_tsum (B t : ℝ) (hB : 0 < B) :
    let hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
    let s : Finset ℤ := Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1)
    EqOn (fun θ => ∑' m : ℤ, g B t (θ + m))
      (fun θ => ∑ m ∈ s, g B t (θ + m)) ([[(-1/2 : ℝ), (1/2 : ℝ)]]) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by
      have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
      simpa [Set.uIcc_of_le hab] using hθ
    simpa using P_A_tsum_eq_finite_sum B t θ hB hθ'

#print "=== CHECKPOINT I4: integral_eq_tsum OK ==="

-- Step 3: Test interval integral equality
set_option maxHeartbeats 300000 in
set_option profiler true in
lemma integral_int_eq (B t : ℝ) (hB : 0 < B) :
    let s : Finset ℤ := Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1)
    ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m) =
      ∫ θ in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, g B t (θ + m) := by
    exact intervalIntegral.integral_congr (integral_eq_tsum B t hB)

#print "=== CHECKPOINT I5: integral_int_eq OK ==="

-- Step 4: Test integral_finset_sum
set_option maxHeartbeats 400000 in
set_option profiler true in
lemma integral_sum_swap (B t : ℝ) (hB : 0 < B) :
    let s : Finset ℤ := Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1)
    ∫ θ in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, g B t (θ + m) =
      ∑ m ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + m) := by
    refine intervalIntegral.integral_finset_sum ?_
    intro m hm
    have hcont : Continuous (fun θ => g B t (θ + m)) := by
      exact (continuous_g B t).comp (continuous_id.add continuous_const)
    exact hcont.intervalIntegrable (-1/2 : ℝ) (1/2 : ℝ)

#print "=== CHECKPOINT I6: integral_sum_swap OK ==="

end Q3.Debug.Integral

#print "=== INTEGRAL TEST COMPLETE ==="
