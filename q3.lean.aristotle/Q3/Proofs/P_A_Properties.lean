/-
Basic properties of `P_A(B_min,t,·)` for arbitrary `t`.

This is infrastructure for the one-scale bridge: it lets us use the Fourier Toeplitz
Rayleigh lower bound for any fixed `t` once we have a floor estimate.
-/

import Mathlib
import Q3.Proofs.A3_Floor_Main  -- defines `g`, `P_A`, `B_min`, `w`

open scoped BigOperators Real Classical
open Real Set Filter

set_option linter.mathlibStandardSet false

noncomputable section

/-- `g(B_min,t,·)` has compact support uniformly in `t`: it vanishes for `|ξ| ≥ B_min`.
This is because the Fejér factor `max 0 (1 - |ξ|/B_min)` is zero there. -/
lemma g_support_B_min_of_t (t ξ : ℝ) (h : B_min ≤ |ξ|) : g B_min t ξ = 0 := by
  simp only [g, w]
  have hB : (0 : ℝ) < B_min := by norm_num [B_min]
  have h_lin : 1 - |ξ| / B_min ≤ 0 := by
    have h1 : 1 ≤ |ξ| / B_min := by
      rw [one_le_div hB]
      exact h
    linarith
  simp [max_eq_left h_lin, zero_mul, mul_zero]

/-- Local finiteness: near any `θ₀`, the periodized sum defining `P_A(B_min,t,θ)` is finite. -/
lemma P_A_locally_finite_sum_of_t (t θ₀ : ℝ) :
    ∃ N : ℕ, ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2),
      P_A B_min t θ =
        2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, g B_min t (θ + m) := by
  -- identical to `A3_Floor_Main.P_A_locally_finite_sum`, but with `t` as a parameter
  use Nat.ceil |θ₀| + 4
  intro θ hθ
  unfold P_A
  congr 1
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  have h_large : B_min ≤ |θ + m| := by
    have hθ_bound : |θ| < |θ₀| + 1/2 := by
      have h1 : θ₀ - 1/2 < θ := hθ.1
      have h2 : θ < θ₀ + 1/2 := hθ.2
      rw [abs_lt]
      constructor
      · by_cases hθ₀_neg : θ₀ ≤ 0
        · have : |θ₀| = -θ₀ := abs_of_nonpos hθ₀_neg
          linarith
        · push_neg at hθ₀_neg
          have : |θ₀| = θ₀ := abs_of_pos hθ₀_neg
          linarith
      · by_cases hθ₀_neg : θ₀ ≤ 0
        · have : |θ₀| = -θ₀ := abs_of_nonpos hθ₀_neg
          linarith
        · push_neg at hθ₀_neg
          have : |θ₀| = θ₀ := abs_of_pos hθ₀_neg
          linarith
    have hN : (Nat.ceil |θ₀| : ℤ) + 4 < |m| := by
      by_cases h : m < -((Nat.ceil |θ₀| : ℤ) + 4)
      · have hm_neg : m < 0 := by omega
        simp only [abs_of_neg hm_neg]
        omega
      · push_neg at h
        have := hm h
        have hm_nonneg : 0 ≤ m := by omega
        simp only [abs_of_nonneg hm_nonneg]
        exact this
    have h_m_real : |θ₀| + 4 < |(m : ℝ)| := by
      have h1 : (Nat.ceil |θ₀| : ℝ) + 4 < |m| := by exact_mod_cast hN
      calc |θ₀| + 4 ≤ (Nat.ceil |θ₀| : ℝ) + 4 := by linarith
        _ < |m| := h1
        _ = |(m : ℝ)| := by simp [Int.cast_abs]
    have h_tri : |(m : ℝ)| - |θ| ≤ |θ + (m : ℝ)| := by
      have h1 := abs_sub_abs_le_abs_sub (m : ℝ) (-θ)
      simp only [abs_neg, sub_neg_eq_add] at h1
      calc |(m : ℝ)| - |θ| ≤ |(m : ℝ) + θ| := h1
        _ = |θ + (m : ℝ)| := by ring_nf
    have h_final : (B_min : ℝ) < |θ + (m : ℝ)| := by
      calc (B_min : ℝ) = 3 := by norm_num [B_min]
        _ < 3.5 := by norm_num
        _ = |θ₀| + 4 - (|θ₀| + 1/2) := by ring
        _ < |(m : ℝ)| - |θ| := by linarith [h_m_real, hθ_bound]
        _ ≤ |θ + (m : ℝ)| := h_tri
    have h_eq : |θ + (m : ℝ)| = |θ + m| := by norm_cast
    have : (B_min : ℝ) < |θ + m| := by
      -- rewrite using `h_eq`
      simpa [h_eq] using h_final
    linarith [this]
  exact g_support_B_min_of_t (t := t) (ξ := θ + m) h_large

/-- Continuity of `g(B_min,t,·)` for any fixed `t`. -/
lemma continuous_g_B_min_of_t (t : ℝ) : Continuous (fun ξ => g B_min t ξ) := by
  simp only [g]
  have ha : Continuous Q3.a := by
    have hpi : (2 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
    have h_eq : Q3.a = (fun ξ => (1 / (2 * Real.pi)) * Q3.a_star ξ) := by
      ext ξ
      simp only [Q3.a_star]
      field_simp [hpi]
    rw [h_eq]
    exact continuous_const.mul Q3.a_star_continuous
  have hw : Continuous (fun ξ => w B_min t ξ) := by
    simp only [w]
    have h_lin : Continuous (fun ξ => 1 - |ξ| / B_min) :=
      continuous_const.sub (continuous_abs.div_const B_min)
    have h_max : Continuous (fun ξ => max (0 : ℝ) (1 - |ξ| / B_min)) :=
      continuous_const.max h_lin
    have h_exp : Continuous (fun ξ => Real.exp (-4 * Real.pi ^ 2 * t * ξ ^ 2)) := by
      have h1 : Continuous (fun ξ => -4 * Real.pi ^ 2 * t * ξ ^ 2) :=
        continuous_const.mul (continuous_pow 2)
      exact Real.continuous_exp.comp h1
    exact h_max.mul h_exp
  exact ha.mul hw

/-- Continuity of the periodized symbol `P_A(B_min,t,·)` for any fixed `t`. -/
theorem P_A_continuous_of_t (t : ℝ) : Continuous (P_A B_min t) := by
  rw [continuous_iff_continuousAt]
  intro θ₀
  obtain ⟨N, hN⟩ := P_A_locally_finite_sum_of_t (t := t) (θ₀ := θ₀)
  let f := fun θ => 2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, g B_min t (θ + m)
  have h_sum_cont : Continuous f := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro m _
    exact (continuous_g_B_min_of_t t).comp (continuous_id.add continuous_const)
  have h_mem : Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2) ∈ nhds θ₀ := by
    apply Ioo_mem_nhds <;> linarith
  have h_eq : ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2), P_A B_min t θ = f θ := hN
  have h_f_cont : ContinuousAt f θ₀ := h_sum_cont.continuousAt
  have h_eq_f : P_A B_min t =ᶠ[nhds θ₀] f := by
    apply Filter.eventuallyEq_of_mem h_mem
    intro θ hθ
    exact h_eq θ hθ
  exact h_f_cont.congr h_eq_f.symm
