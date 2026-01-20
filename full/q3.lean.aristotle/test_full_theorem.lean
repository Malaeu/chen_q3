/-
Debug: Full integral_P_A_eq_arch_term theorem
Testing with profiler to find the slow step
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.ShiftedWindows
import A3_FLOOR_v22_stage4_floor

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate

-- Use unlimited heartbeats but with profiler
set_option maxHeartbeats 0
set_option profiler true

noncomputable section

namespace Q3.Debug.FullTheorem

-- Copy all needed lemmas
lemma w_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : w B t ξ = 0 := by
  simp only [w]
  have h1 : 1 - |ξ| / B < 0 := by
    have : 1 < |ξ| / B := by rw [one_lt_div hB]; exact h
    linarith
  rw [max_eq_left (le_of_lt h1)]
  ring

lemma g_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : g B t ξ = 0 := by
  simp only [g, w_support B t ξ hB h, mul_zero]

lemma continuous_g (B t : ℝ) : Continuous (fun ξ => g B t ξ) := by
  unfold g w
  continuity

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

#print "=== STARTING MAIN THEOREM ==="

-- THE MAIN THEOREM - with step-by-step tracing
theorem integral_P_A_eq_arch_term (B t : ℝ) (hB : 0 < B) :
    ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ =
      Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) := by
  classical
  trace "Step 1: Setup"
  have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
  let s : Finset ℤ := Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1)

  trace "Step 2: hsupp"
  have hsupp : Function.support (fun ξ => g B t ξ) ⊆ Set.Icc (-B) B := by
    refine (Function.support_subset_iff'.2 ?_)
    intro ξ hξ
    by_contra hle
    have hle' : |ξ| ≤ B := le_of_not_gt hle
    have : ξ ∈ Set.Icc (-B) B := abs_le.mp hle'
    exact hξ this

  trace "Step 3: hcompact"
  have hcompact : HasCompactSupport (fun ξ => g B t ξ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp

  trace "Step 4: hint"
  have hint : Integrable (fun ξ => g B t ξ) :=
    (continuous_g B t).integrable_of_hasCompactSupport hcompact

  trace "Step 5: h_eq_tsum"
  have h_eq_tsum :
      EqOn (fun θ => ∑' m : ℤ, g B t (θ + m))
        (fun θ => ∑ m ∈ s, g B t (θ + m)) ([[(-1/2 : ℝ), (1/2 : ℝ)]]) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by
      simpa [Set.uIcc_of_le hab] using hθ
    simpa [s] using P_A_tsum_eq_finite_sum B t θ hB hθ'

  trace "Step 6: h_int_eq"
  have h_int_eq :
      ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m) =
        ∫ θ in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, g B t (θ + m) :=
    intervalIntegral.integral_congr h_eq_tsum

  trace "Step 7: h_int_sum"
  have h_int_sum :
      ∫ θ in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, g B t (θ + m) =
        ∑ m ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + m) := by
    refine intervalIntegral.integral_finset_sum ?_
    intro m _
    exact (continuous_g B t).comp (continuous_id.add continuous_const) |>.intervalIntegrable _ _

  trace "Step 8: hsum_base"
  have hsum_base :
      HasSum (fun n : ℤ =>
          ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, g B t x)
        (∫ x, g B t x) := by
    simpa using hint.hasSum_intervalIntegral (-1/2 : ℝ)

  trace "Step 9: hsum"
  have hsum :
      HasSum (fun n : ℤ => ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ)))
        (∫ x, g B t x) := by
    refine hsum_base.congr_fun ?_
    intro n
    have hcomp := intervalIntegral.integral_comp_add_right (f:=fun x => g B t x) (n : ℝ) (-1/2 : ℝ) (1/2 : ℝ)
    convert hcomp using 1 <;> ring

  trace "Step 10: hsum_eq"
  have hsum_eq :
      (∑' n : ℤ, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ))) =
        ∑ n ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ)) := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_Icc, not_and, not_le] at hn
    have h_large : (⌈B⌉ : ℤ) + 1 < |n| := by
      by_cases h : n < -(⌈B⌉ + 1)
      · simp [abs_of_neg (by omega : n < 0)]; omega
      · push_neg at h; simp [abs_of_nonneg (by omega : 0 ≤ n)]; exact hn h
    have h_eq0 : EqOn (fun θ => g B t (θ + n)) (fun _ => (0 : ℝ)) ([[(-1/2 : ℝ), (1/2 : ℝ)]]) := by
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by simpa [Set.uIcc_of_le hab] using hθ
      simpa using g_shift_zero_of_large_m B t θ n hB hθ' h_large
    simpa using intervalIntegral.integral_congr h_eq0

  trace "Step 11: hsum_fin"
  have hsum_fin :
      ∑ n ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ)) = ∫ x, g B t x :=
    hsum_eq.symm.trans hsum.tsum_eq

  trace "Step 12: h_integral"
  have h_integral :
      ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m) = ∫ x, g B t x := by
    calc ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m)
        = ∫ θ in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, g B t (θ + m) := h_int_eq
      _ = ∑ m ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + m) := h_int_sum
      _ = ∫ x, g B t x := hsum_fin

  trace "Step 13: Final"
  rw [arch_term_eq_two_pi_integral_g]
  simp [P_A, intervalIntegral.integral_const_mul, h_integral]

#print "=== THEOREM COMPLETE ==="

end Q3.Debug.FullTheorem
