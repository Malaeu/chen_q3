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
  have hpi : (2 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
  have h :
      (fun xi => Q3.a xi) = fun xi => (1 / (2 * Real.pi)) * Q3.a_star xi := by
    funext xi
    have h' : (1 / (2 * Real.pi)) * Q3.a_star xi = Q3.a xi := by
      calc
        (1 / (2 * Real.pi)) * Q3.a_star xi
            = (1 / (2 * Real.pi)) * (2 * Real.pi * Q3.a xi) := by simp [Q3.a_star]
        _ = Q3.a xi := by
          field_simp [hpi]
    simpa using h'.symm
  have hcont : Continuous (fun xi => (1 / (2 * Real.pi)) * Q3.a_star xi) :=
    continuous_const.mul Q3.a_star_continuous
  simpa [h] using hcont

lemma continuous_fejer_heat_window (B t : ℝ) :
    Continuous (fun xi => Q3.fejer_heat_window B t xi) := by
  unfold Q3.fejer_heat_window
  have h_lin : Continuous (fun xi : ℝ => 1 - |xi| / B) := by
    have h_abs : Continuous (fun xi : ℝ => |xi|) := by
      simpa using (continuous_abs : Continuous fun xi : ℝ => |xi|)
    have h_div : Continuous (fun xi : ℝ => |xi| / B) := by
      simpa [div_eq_mul_inv] using h_abs.mul continuous_const
    exact continuous_const.sub h_div
  have h_max : Continuous (fun xi : ℝ => max (0 : ℝ) (1 - |xi| / B)) :=
    (continuous_const).max h_lin
  have h_pow : Continuous (fun xi : ℝ => xi ^ 2) := by
    simpa using (continuous_pow 2 : Continuous fun xi : ℝ => xi ^ 2)
  have h_poly : Continuous (fun xi : ℝ => (-4 * Real.pi ^ 2 * t) * (xi ^ 2)) :=
    continuous_const.mul h_pow
  have h_exp : Continuous (fun xi : ℝ => Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2)) := by
    simpa [mul_assoc] using (Real.continuous_exp.comp h_poly)
  exact h_max.mul h_exp

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
  have h_lower : |xi| - |tau| ≤ |xi - tau| := by
    exact abs_sub_abs_le_abs_sub xi tau
  have hB' : B < |xi - tau| := by
    have h1 : B ≤ K - |tau| := by linarith [hK]
    have h2 : K - |tau| < |xi| - |tau| := by linarith [hxi]
    have h3 : B < |xi| - |tau| := lt_of_le_of_lt h1 h2
    linarith [h_lower, h3]
  exact phi_shift_support B t tau xi hB hB'

lemma g_shift_support_of_margin (B t tau K : ℝ) (hB : 0 < B) (hK : |tau| + B ≤ K) :
    ∀ xi, K < |xi| → Q3.g_shift B t tau xi = 0 := by
  intro xi hxi
  simp [Q3.g_shift, phi_shift_support_of_margin B t tau K hB hK xi hxi]

lemma g_shift_zero_of_large_m (B t tau theta : ℝ) (m : ℤ) (hB : 0 < B)
    (htheta : theta ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : (⌈B + |tau|⌉ : ℤ) + 1 < |m|) :
    Q3.g_shift B t tau (theta + m) = 0 := by
  have hm_real : B + |tau| + 1 < |(m : ℝ)| := by
    have hm' : (⌈B + |tau|⌉ : ℝ) + 1 < |m| := by exact_mod_cast hm
    have hceil : B + |tau| ≤ (⌈B + |tau|⌉ : ℝ) := Int.le_ceil (B + |tau|)
    have hmid : B + |tau| + 1 < |m| := by linarith [hceil, hm']
    have h_abs : (|m| : ℝ) = |(m : ℝ)| := by simp
    simpa [h_abs] using hmid
  have htheta_abs : |theta| ≤ (1/2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [htheta.1, htheta.2]
  have hthetatau : |theta - tau| ≤ |theta| + |tau| := by
    have h := abs_add_le theta (-tau)
    simpa [sub_eq_add_neg, abs_neg, add_comm, add_left_comm, add_assoc] using h
  have hthetatau' : |theta - tau| ≤ |tau| + (1/2 : ℝ) := by
    linarith [htheta_abs, hthetatau]
  have htri : |(m : ℝ)| - |theta - tau| ≤ |theta + (m : ℝ) - tau| := by
    have h := abs_add_le (theta + (m : ℝ) - tau) (tau - theta)
    have hsum : (theta + (m : ℝ) - tau) + (tau - theta) = (m : ℝ) := by ring_nf
    have h1 : |(m : ℝ)| ≤ |theta + (m : ℝ) - tau| + |tau - theta| := by
      simpa [hsum] using h
    have h2 : |(m : ℝ)| ≤ |theta + (m : ℝ) - tau| + |theta - tau| := by
      simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using h1
    linarith [h2]
  have hB' : B < |theta + (m : ℝ) - tau| := by
    have hmid : B < |(m : ℝ)| - |theta - tau| := by
      linarith [hm_real, hthetatau']
    linarith [htri, hmid]
  exact g_shift_support B t tau (theta + m) hB (by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hB')

lemma P_A_shift_tsum_eq_finite_sum (B t tau theta : ℝ) (hB : 0 < B)
    (htheta : theta ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    ∑' (m : ℤ), Q3.g_shift B t tau (theta + m) =
      ∑ m ∈ Finset.Icc (-(⌈B + |tau|⌉ + 1)) (⌈B + |tau|⌉ + 1),
        Q3.g_shift B t tau (theta + m) := by
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  have hceil_pos : (0 : ℤ) < ⌈B + |tau|⌉ + 1 := by
    have : (0 : ℤ) ≤ ⌈B + |tau|⌉ := by
      exact Int.ceil_nonneg (by nlinarith [abs_nonneg tau, hB])
    omega
  have h_large : (⌈B + |tau|⌉ : ℤ) + 1 < |m| := by
    by_cases h : m < -(⌈B + |tau|⌉ + 1)
    · have hm_neg : m < 0 := by linarith [hceil_pos, h]
      have hneg : (⌈B + |tau|⌉ : ℤ) + 1 < -m := by linarith
      simpa [abs_of_neg hm_neg] using hneg
    · push_neg at h
      have hm' : (⌈B + |tau|⌉ : ℤ) + 1 < m := hm h
      have hm_nonneg : 0 ≤ m := by linarith [hceil_pos, hm']
      simpa [abs_of_nonneg hm_nonneg] using hm'
  exact g_shift_zero_of_large_m B t tau theta m hB htheta h_large

lemma arch_term_eq_two_pi_integral_g_shift (B t tau : ℝ) :
    Q3.arch_term (fun xi => Q3.phi_shift B t tau xi) =
      2 * Real.pi * ∫ xi, Q3.g_shift B t tau xi := by
  have h :
      ∀ xi, Q3.a_star xi * Q3.phi_shift B t tau xi =
        2 * Real.pi * (Q3.a xi * Q3.phi_shift B t tau xi) := by
    intro xi
    simp [Q3.a_star]
    ring_nf
  simp [Q3.arch_term, Q3.g_shift, h, MeasureTheory.integral_const_mul]

theorem integral_P_A_shift_eq_arch_term (B t tau : ℝ) (hB : 0 < B) :
    ∫ theta in (-1/2 : ℝ)..(1/2), Q3.P_A_shift B t tau theta =
      Q3.arch_term (fun xi => Q3.phi_shift B t tau xi) := by
  classical
  have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
  let K : ℝ := B + |tau|
  let s : Finset ℤ := Finset.Icc (-(⌈K⌉ + 1)) (⌈K⌉ + 1)
  have hsupp : Function.support (fun xi => Q3.g_shift B t tau xi) ⊆ Set.Icc (-K) K := by
    refine Function.support_subset_iff'.2 ?_
    intro xi hxi
    have hnot_abs : ¬ |xi| ≤ K := by
      intro habs
      have h' : -K ≤ xi ∧ xi ≤ K := (abs_le.mp habs)
      exact hxi h'
    have hK : K < |xi| := lt_of_not_ge hnot_abs
    exact g_shift_support_of_margin B t tau K hB (by simp [K, add_comm]) xi hK
  have hcompact : HasCompactSupport (fun xi => Q3.g_shift B t tau xi) := by
    exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hint : Integrable (fun xi => Q3.g_shift B t tau xi) := by
    exact (continuous_g_shift B t tau).integrable_of_hasCompactSupport hcompact

  have h_eq_tsum :
      Set.EqOn (fun theta => ∑' m : ℤ, Q3.g_shift B t tau (theta + m))
        (fun theta => ∑ m ∈ s, Q3.g_shift B t tau (theta + m))
        (Set.uIcc (-1/2 : ℝ) (1/2 : ℝ)) := by
    intro theta htheta
    have htheta' : theta ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by
      have htheta' : (-1/2 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ) := by
        rcases Set.mem_uIcc.mp htheta with hθ | hθ
        · exact hθ
        · exfalso
          linarith [hθ.1, hθ.2, hab]
      exact htheta'
    simpa [s, K] using P_A_shift_tsum_eq_finite_sum B t tau theta hB htheta'

  have h_int_eq :
      ∫ theta in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, Q3.g_shift B t tau (theta + m) =
        ∫ theta in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, Q3.g_shift B t tau (theta + m) := by
    exact intervalIntegral.integral_congr h_eq_tsum

  have h_int_sum :
      ∫ theta in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, Q3.g_shift B t tau (theta + m) =
        ∑ m ∈ s, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + m) := by
    refine intervalIntegral.integral_finset_sum ?_
    intro m hm
    have hcont : Continuous (fun theta => Q3.g_shift B t tau (theta + m)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (continuous_g_shift B t tau).comp (continuous_id.add continuous_const)
    exact hcont.intervalIntegrable (μ:=volume) (-1/2 : ℝ) (1/2 : ℝ)

  have hsum_base :
      HasSum (fun n : ℤ =>
          ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, Q3.g_shift B t tau x)
        (∫ x, Q3.g_shift B t tau x) := by
    simpa using
      (MeasureTheory.Integrable.hasSum_intervalIntegral (μ:=volume)
        (f:=fun x => Q3.g_shift B t tau x) (y:=(-1/2 : ℝ)) hint)

  have hsum :
      HasSum (fun n : ℤ => ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + (n : ℝ)))
        (∫ x, Q3.g_shift B t tau x) := by
    refine (HasSum.congr_fun hsum_base ?_)
    intro n
    have hcomp :=
      intervalIntegral.integral_comp_add_right (f:=fun x => Q3.g_shift B t tau x) (d:=(n : ℝ))
        (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ))
    convert hcomp using 1
    ring_nf

  have hsum_eq :
      (∑' n : ℤ, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + (n : ℝ))) =
        ∑ n ∈ s, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + (n : ℝ)) := by
    apply tsum_eq_sum
    intro n hn
    have hn' : ¬ (-(⌈K⌉ + 1) ≤ n ∧ n ≤ ⌈K⌉ + 1) := by
      simpa [s, Finset.mem_Icc] using hn
    have hceil_pos : (0 : ℤ) < ⌈K⌉ + 1 := by
      have hK0 : 0 ≤ K := by nlinarith [abs_nonneg tau, hB]
      have : (0 : ℤ) ≤ ⌈K⌉ := Int.ceil_nonneg hK0
      omega
    have h_large : (⌈K⌉ : ℤ) + 1 < |n| := by
      by_cases h : n < -(⌈K⌉ + 1)
      · have hn_neg : n < 0 := by linarith [hceil_pos, h]
        have hneg : (⌈K⌉ : ℤ) + 1 < -n := by linarith
        simpa [abs_of_neg hn_neg] using hneg
      · push_neg at h
        have hnot : ¬ n ≤ ⌈K⌉ + 1 := by
          intro hle
          exact hn' ⟨h, hle⟩
        have hn'' : (⌈K⌉ : ℤ) + 1 < n := lt_of_not_ge hnot
        have hn_nonneg : 0 ≤ n := by linarith [hceil_pos, hn'']
        simpa [abs_of_nonneg hn_nonneg] using hn''
    have h_eq0 :
        Set.EqOn (fun theta => Q3.g_shift B t tau (theta + n)) (fun _ => (0 : ℝ))
          (Set.uIcc (-1/2 : ℝ) (1/2 : ℝ)) := by
      intro theta htheta
      have htheta' : theta ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by
        have htheta' : (-1/2 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ) := by
          rcases Set.mem_uIcc.mp htheta with hθ | hθ
          · exact hθ
          · exfalso
            linarith [hθ.1, hθ.2, hab]
        exact htheta'
      simpa [K] using g_shift_zero_of_large_m B t tau theta n hB htheta' h_large
    have h_integral_zero :
        ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + n) =
          ∫ theta in (-1/2 : ℝ)..(1/2), (0 : ℝ) := by
      exact intervalIntegral.integral_congr h_eq0
    simpa using h_integral_zero

  have hsum_fin :
      ∑ n ∈ s, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + (n : ℝ)) =
        ∫ x, Q3.g_shift B t tau x := by
    exact hsum_eq.symm.trans hsum.tsum_eq

  have h_integral :
      ∫ theta in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, Q3.g_shift B t tau (theta + m) =
        ∫ x, Q3.g_shift B t tau x := by
    calc
      ∫ theta in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, Q3.g_shift B t tau (theta + m)
          = ∫ theta in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, Q3.g_shift B t tau (theta + m) := h_int_eq
      _ = ∑ m ∈ s, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + m) := h_int_sum
      _ = ∫ x, Q3.g_shift B t tau x := hsum_fin

  have h_integral' :
      ∫ theta in (-1/2 : ℝ)..(2⁻¹), ∑' m : ℤ, Q3.g_shift B t tau (theta + m) =
        ∫ x, Q3.g_shift B t tau x := by
    simpa [one_div] using h_integral

  rw [arch_term_eq_two_pi_integral_g_shift]
  simp [Q3.P_A_shift, intervalIntegral.integral_const_mul, h_integral']

end Q3.Proofs.ShiftedWindows
