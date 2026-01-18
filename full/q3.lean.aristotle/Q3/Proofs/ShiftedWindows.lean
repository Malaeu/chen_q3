/-
Shifted windows and periodization for tau-shifted atoms.
-/

import Mathlib
import Q3.Axioms
import Q3.Basic.Defs

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate
open MeasureTheory

noncomputable section

namespace Q3

def phi_shift (B t tau : ℝ) (xi : ℝ) : ℝ :=
  fejer_heat_window B t (xi - tau)

def g_shift (B t tau : ℝ) (xi : ℝ) : ℝ :=
  a xi * phi_shift B t tau xi

def P_A_shift (B t tau : ℝ) (theta : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g_shift B t tau (theta + m)

end Q3

namespace Q3.Proofs.ShiftedWindows

open Q3

lemma phi_shift_support (B t tau xi : ℝ) (hB : 0 < B) (h : B < |xi - tau|) :
    Q3.phi_shift B t tau xi = 0 := by
  unfold Q3.phi_shift Q3.fejer_heat_window
  have h1 : 1 - |xi - tau| / B < 0 := by
    have : 1 < |xi - tau| / B := by
      rw [one_lt_div hB]
      exact h
    linarith
  simp [max_eq_left (le_of_lt h1)]

lemma g_shift_support (B t tau xi : ℝ) (hB : 0 < B) (h : B < |xi - tau|) :
    Q3.g_shift B t tau xi = 0 := by
  simp [Q3.g_shift, phi_shift_support B t tau xi hB h]

lemma continuous_a : Continuous Q3.a := by
  -- a(ξ) = a_star(ξ) / (2π), and a_star is continuous
  have hpi : (2 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
  have h : Q3.a = fun xi => Q3.a_star xi / (2 * Real.pi) := by
    funext xi
    simp only [Q3.a_star, Q3.a]
    field_simp [hpi]
  rw [h]
  exact Q3.a_star_continuous.div_const _

lemma continuous_fejer_heat_window (B t : ℝ) :
    Continuous (fun xi => Q3.fejer_heat_window B t xi) := by
  unfold Q3.fejer_heat_window
  refine Continuous.mul ?_ ?_
  · exact continuous_const.max (continuous_const.sub (continuous_abs.div_const B))
  · exact Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))

lemma continuous_phi_shift (B t tau : ℝ) :
    Continuous (fun xi => Q3.phi_shift B t tau xi) := by
  simpa [Q3.phi_shift] using
    (continuous_fejer_heat_window B t).comp (continuous_id.sub continuous_const)

lemma continuous_g_shift (B t tau : ℝ) :
    Continuous (fun xi => Q3.g_shift B t tau xi) := by
  exact continuous_a.mul (continuous_phi_shift B t tau)

lemma phi_shift_support_of_margin (B t tau K : ℝ) (hB : 0 < B) (hK : |tau| + B ≤ K) :
    ∀ xi, K < |xi| → Q3.phi_shift B t tau xi = 0 := by
  intro xi hxi
  -- Triangle inequality: |xi| = |(xi - tau) + tau| ≤ |xi - tau| + |tau|
  have htri : |xi| ≤ |xi - tau| + |tau| := by
    calc |xi| = |(xi - tau) + tau| := by ring_nf
         _ ≤ |xi - tau| + |tau| := abs_add_le _ _
  have h_lower : |xi| - |tau| ≤ |xi - tau| := by linarith
  have hB' : B < |xi - tau| := by
    have : B < |xi| - |tau| := by linarith [hK, hxi]
    linarith [h_lower]
  exact phi_shift_support B t tau xi hB hB'

lemma g_shift_support_of_margin (B t tau K : ℝ) (hB : 0 < B) (hK : |tau| + B ≤ K) :
    ∀ xi, K < |xi| → Q3.g_shift B t tau xi = 0 := by
  intro xi hxi
  simp [Q3.g_shift, phi_shift_support_of_margin B t tau K hB hK xi hxi]

lemma g_shift_zero_of_large_m (B t tau theta : ℝ) (m : ℤ) (hB : 0 < B)
    (htheta : theta ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : (⌈B + |tau|⌉ : ℤ) + 1 < |m|) :
    Q3.g_shift B t tau (theta + m) = 0 := by
  -- When |m| > ceil(B + |tau|) + 1, theta + m is far from tau
  -- Triangle inequality: |theta + m - tau| ≥ |m| - |theta - tau| ≥ |m| - (|tau| + 1/2) > B
  sorry

lemma P_A_shift_tsum_eq_finite_sum (B t tau theta : ℝ) (hB : 0 < B)
    (htheta : theta ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    ∑' (m : ℤ), Q3.g_shift B t tau (theta + m) =
      ∑ m ∈ Finset.Icc (-(⌈B + |tau|⌉ + 1)) (⌈B + |tau|⌉ + 1),
        Q3.g_shift B t tau (theta + m) := by
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  have h_large : (⌈B + |tau|⌉ : ℤ) + 1 < |m| := by
    have hceil_nonneg : (0 : ℤ) ≤ ⌈B + |tau|⌉ := by
      apply Int.ceil_nonneg
      linarith [abs_nonneg tau]
    by_cases h : m < -(⌈B + |tau|⌉ + 1)
    · have hm_neg : m < 0 := by linarith
      rw [abs_of_neg hm_neg]
      linarith
    · push_neg at h
      have hmpos := hm h
      have hm_nonneg : 0 ≤ m := by linarith
      rw [abs_of_nonneg hm_nonneg]
      exact hmpos
  exact g_shift_zero_of_large_m B t tau theta m hB htheta h_large

lemma arch_term_eq_two_pi_integral_g_shift (B t tau : ℝ) :
    Q3.arch_term (fun xi => Q3.phi_shift B t tau xi) =
      2 * Real.pi * ∫ xi, Q3.g_shift B t tau xi := by
  have h :
      ∀ xi, Q3.a_star xi * Q3.phi_shift B t tau xi =
        2 * Real.pi * (Q3.a xi * Q3.phi_shift B t tau xi) := by
    intro xi
    simp [Q3.a_star]
    ring
  simp [Q3.arch_term, Q3.g_shift, h, MeasureTheory.integral_mul_left]

theorem integral_P_A_shift_eq_arch_term (B t tau : ℝ) (hB : 0 < B) :
    ∫ theta in (-1/2 : ℝ)..(1/2), Q3.P_A_shift B t tau theta =
      Q3.arch_term (fun xi => Q3.phi_shift B t tau xi) := by
  -- Periodization identity: ∫₀¹ P_A_shift dθ = arch_term(phi_shift)
  -- P_A_shift(θ) = 2π Σₘ g_shift(θ+m) where g_shift = a · phi_shift
  -- Sum over m collapses by translation invariance of integral
  sorry

end Q3.Proofs.ShiftedWindows
