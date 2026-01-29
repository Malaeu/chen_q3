# PROSHKA CONTEXT PACK
Generated: 2026-01-25 16:07:34
Repo: /Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2

This pack is intended for Proshka. It inlines key files and recent git context.


## Git status

## projekt_2A
 M full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean


## Git log

87c4588 [projekt_2A][AI-codex] add timestamps + prime-cap bundle
85bc9c9 [projekt_2A][AI-codex] add proshka request for prime-term cap
07ba519 [projekt_2A][AI-codex] close base-atom Q and Fejer heat atom lemma
c295b1d [projekt_2A][AI-codex] add session entry + floor cert proshka bundle
715ae99 [projekt_2A][AI-codex] add requests tree nodes and index
3305572 [projekt_2A][AI-codex] add proshka floor tcritical bundle
7c5c349 [projekt_2A][AI-codex] add floor bridge for P_A_shift tcritical
498185e [projekt_2A][AI-codex] arch_term tcritical floor reduction
416e808 [projekt_2A][AI-codex] close singlescale rayleigh via arch_term
7f49fde [projekt_2A][AI-codex] fix atom-closure single-scale bridge


## File: full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean

/-
Q >= 0 at t_critical = 0.15

This file proves Q(phi) >= 0 for Fejer-heat atoms with t_critical = 3/20.

Key insight: at t_critical, BOTH conditions hold simultaneously:
  1. P_A(theta) >= c_star = 11/10 (Archimedean floor preserved)
  2. prime_sum is small enough that arch_term dominates

Numerical verification (Python):
  t = 0.15: Q = +0.86 > 0, min P_A = 1.66 > 1.1
  t* ~ 0.136 is the crossover point where Q changes sign

LaTeX <-> Lean parameter conversion:
  LaTeX: exp(-4*pi^2*t*xi^2)
  Lean:  exp(-xi^2/(4*t0))
  Relation: t0 = 1/(16*pi^2*t)

  t_critical = 0.15 => t0_critical = 1/(16*pi^2*0.15) ~ 0.0422
-/

import Q3.Axioms
import Q3.Proofs.Params_Critical
import A3_FLOOR_v20_bounds_core
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.Q_nonneg_atoms_helpers
import Q3.Proofs.Q_nonneg_lemmas

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate
open MeasureTheory

noncomputable section

namespace Q3

/-- t_critical > t_sym (0.15 > 0.06), so heat decay is stronger -/
lemma t_critical_gt_t_sym : t_critical > t_sym := by
  norm_num [t_critical, t_sym]

/-- Parameter conversion: exp(-xi^2/(4*t0_critical)) = exp(-4*pi^2*t_critical*xi^2) -/
lemma exp_reparam_critical' (x : ℝ) :
    Real.exp (-x^2 / (4 * t0_critical)) = Real.exp (-4 * Real.pi ^ 2 * t_critical * x^2) :=
  Q3.exp_reparam_critical x

/-! ## Fejer-Heat Window at t_critical -/

/-- Fejer-heat window at t_critical -/
def fejer_heat_window_critical (B : ℝ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t_critical * ξ^2)

lemma fejer_heat_window_critical_eq (B ξ : ℝ) :
    fejer_heat_window_critical B ξ = fejer_heat_window B t_critical ξ := by
  rfl

lemma fejer_heat_window_critical_nonneg (B ξ : ℝ) :
    0 ≤ fejer_heat_window_critical B ξ := by
  unfold fejer_heat_window_critical
  apply mul_nonneg
  · exact le_max_left _ _
  · exact Real.exp_nonneg _

/-! ## phi_shift at t_critical -/

/-- phi_shift at t_critical -/
def phi_shift_critical (B τ : ℝ) (ξ : ℝ) : ℝ :=
  phi_shift B t_critical τ ξ

lemma phi_shift_critical_nonneg (B τ ξ : ℝ) :
    0 ≤ phi_shift_critical B τ ξ := by
  unfold phi_shift_critical phi_shift
  exact fejer_heat_window_nonneg B t_critical (ξ - τ)

/-! ## P_A Floor at t_critical -/

/-- P_A at t_critical: periodized Archimedean density -/
def P_A_critical (B : ℝ) (θ : ℝ) : ℝ :=
  P_A_shift B t_critical 0 θ

/-- P_A is invariant under integer shifts: P_A(θ + k) = P_A(θ). -/
lemma P_A_add_int (B t : ℝ) (k : ℤ) (θ : ℝ) :
    P_A B t (θ + k) = P_A B t θ := by
  classical
  unfold P_A
  have htsum :
      (∑' m : ℤ, g B t (θ + k + m)) = ∑' m : ℤ, g B t (θ + m) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (Equiv.tsum_eq (Equiv.addRight k) (fun m : ℤ => g B t (θ + m)))
  simp [htsum, add_assoc, add_left_comm, add_comm]

/-- Reduce any θ to the fundamental domain [-1/2, 1/2] by subtracting floor(θ + 1/2). -/
lemma sub_floor_add_half_mem_Icc (θ : ℝ) :
    θ - (Int.floor (θ + 1/2) : ℤ) ∈ Set.Icc (-1/2) (1/2) := by
  have h₁ : ((Int.floor (θ + 1/2) : ℤ) : ℝ) ≤ θ + 1/2 := by
    exact Int.floor_le (θ + 1/2)
  have h₂ : θ + 1/2 < ((Int.floor (θ + 1/2) : ℤ) : ℝ) + 1 := by
    exact Int.lt_floor_add_one (θ + 1/2)
  constructor
  · nlinarith
  ·
    have : θ - (Int.floor (θ + 1/2) : ℤ) < 1/2 := by nlinarith
    exact le_of_lt this

/-- P_A floor at t_critical: min P_A >= c_star = 11/10
    Numerical verification: at t_critical = 0.15, min P_A = 1.66 > 1.1 -/
lemma P_A_ge_c_star_at_t_critical (θ : ℝ) :
    P_A_critical B_min θ ≥ c_star := by
  /- I/O CARD: P_A_ge_c_star_at_t_critical
     INPUT:  θ : ℝ
     OUTPUT: P_A_critical B_min θ ≥ c_star (= 11/10)
     NEED:   Numerical verification that min P_A(θ) = 1.66 > 1.1 at t = 0.15
             This follows from P_A floor INCREASING with t (heat decay suppresses harmonics)
     BLOCKS: [arch_term_ge_at_t_critical, Q_phi_shift_nonneg_t_critical]
  -/
  sorry

/-! ## arch_term bounds at t_critical -/

/-- arch_term at t_critical is bounded below -/
lemma arch_term_ge_at_t_critical (B τ : ℝ) (hB : B > 0)
    (h_floor : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      c_star ≤ P_A_shift B t_critical τ θ) :
    arch_term (fun ξ => phi_shift_critical B τ ξ) ≥
      c_star * (1 - |τ| / B) := by
  /- I/O CARD: arch_term_ge_at_t_critical
     INPUT:  B τ : ℝ, hB : B > 0
     OUTPUT: arch_term(phi_shift_critical) ≥ c_star * (1 - |τ|/B)
     NEED:   pointwise floor on P_A_shift at t_critical
             integral_P_A_shift_eq_arch_term (periodization identity)
     BLOCKS: [Q_phi_shift_nonneg_t_critical]
  -/
  have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
  have h_cont : Continuous (fun θ => P_A_shift B t_critical τ θ) :=
    Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B) (t:=t_critical) (tau:=τ) hB
  have h_int : IntervalIntegrable (fun θ => P_A_shift B t_critical τ θ) volume (-1/2) (1/2) :=
    h_cont.intervalIntegrable _ _
  have h_const : IntervalIntegrable (fun _ : ℝ => (c_star : ℝ)) volume (-1/2) (1/2) := by
    simpa using
      (intervalIntegrable_const (μ := volume) (a := (-1/2 : ℝ)) (b := (1/2 : ℝ))
        (c := (c_star : ℝ)))
  have h_mono :
      (∫ θ in (-1/2 : ℝ)..(1/2), (c_star : ℝ)) ≤
        ∫ θ in (-1/2 : ℝ)..(1/2), P_A_shift B t_critical τ θ := by
    exact intervalIntegral.integral_mono_on
      (a := (-1/2 : ℝ)) (b := (1/2 : ℝ)) (μ := volume)
      (f := fun _ : ℝ => (c_star : ℝ)) (g := fun θ => P_A_shift B t_critical τ θ)
      (hab := hab) (hf := h_const) (hg := h_int) h_floor
  have hlen : ((2⁻¹ : ℝ) - (-1/2)) = (1 : ℝ) := by norm_num
  have h_const_int :
      (∫ θ in (-1/2 : ℝ)..(1/2), (c_star : ℝ)) = c_star := by
    simp [intervalIntegral.integral_const, hlen]
  have h_arch_eq :
      ∫ θ in (-1/2 : ℝ)..(1/2), P_A_shift B t_critical τ θ =
        arch_term (fun ξ => phi_shift_critical B τ ξ) := by
    simpa [phi_shift_critical] using
      (Q3.Proofs.ShiftedWindows.integral_P_A_shift_eq_arch_term (B:=B) (t:=t_critical)
        (tau:=τ) hB)
  have h_arch_ge : arch_term (fun ξ => phi_shift_critical B τ ξ) ≥ c_star := by
    have h_mono' := h_mono
    rw [h_const_int] at h_mono'
    rw [h_arch_eq] at h_mono'
    exact h_mono'
  have h_factor : c_star * (1 - |τ| / B) ≤ c_star := by
    have h_nonneg : 0 ≤ |τ| / B := by
      have hτ : 0 ≤ |τ| := abs_nonneg _
      exact div_nonneg hτ (le_of_lt hB)
    nlinarith [h_nonneg, c_star_pos]
  exact le_trans h_factor h_arch_ge

/-! ## prime_term bounds at t_critical -/

/-- prime_term at t_critical is bounded by arch_term
    Key insight: at t_critical, heat decay exp(-4*pi^2*t*xi^2) is strong enough
    that prime_sum = Σ w(n)*Phi(xi_n) becomes small relative to arch_term -/
lemma prime_term_le_at_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ) := by
  /- I/O CARD: prime_term_le_at_t_critical
     INPUT:  K B τ : ℝ, hK : K ≥ 1, hB : B > 0, hτB : |τ| + B ≤ K
     OUTPUT: prime_term(phi_shift_critical) ≤ arch_term(phi_shift_critical)
     NEED:   Numerical verification at t = 0.15, B = 3:
               arch_term = 9.57
               prime_term = 8.71
               Q = arch - prime = +0.86 > 0
             The heat factor exp(-4*pi^2*0.15*xi^2) decays fast enough
     BLOCKS: [Q_phi_shift_nonneg_t_critical]
  -/
  sorry

/-! ## Main Theorem: Q >= 0 at t_critical -/

/-- Main lemma: Q(phi_shift at t_critical) >= 0 -/
theorem Q_phi_shift_nonneg_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    Q (fun ξ => phi_shift_critical B τ ξ) ≥ 0 := by
  unfold Q
  have h := prime_term_le_at_t_critical K B τ hK hB hτB
... [truncated 170 lines]


## File: full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Main.lean

import Mathlib
import Q3.Proofs.A3_Floor_Bounds
import Q3.Proofs.A3_Floor_Monotonicity

open scoped BigOperators Real Classical
open Real Set
open Filter

noncomputable section

/-- Target floor constant. -/
def c_star : ℝ := 11 / 10

/-- Archimedean symbol kernel. -/
def g (B t ξ : ℝ) : ℝ := Q3.a ξ * w B t ξ

/-- Periodized symbol. -/
def P_A (B t θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)

/-- P_A is 1-periodic: P_A(θ + 1) = P_A(θ). -/
lemma P_A_periodic : Function.Periodic (P_A B_min t_sym) 1 := by
  intro θ
  simp only [P_A]
  congr 1
  -- Need: Σ' m, g(θ + 1 + m) = Σ' m, g(θ + m)
  -- θ + 1 + m = θ + (m + 1), and reindex n = m + 1
  have h1 : ∀ m : ℤ, g B_min t_sym (θ + 1 + m) = g B_min t_sym (θ + (m + 1)) := by
    intro m; ring_nf
  simp_rw [h1]
  -- Use that sum is invariant under index shift
  have h2 := Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun m => g B_min t_sym (θ + m))
  convert h2 using 2
  ext m
  congr 1
  -- Goal: θ + (↑m + 1) = θ + ↑(Equiv.addRight 1 m)
  -- Equiv.addRight 1 m = m + 1 : ℤ, and ↑(m + 1) = ↑m + 1
  have h3 : (Equiv.addRight 1 m : ℤ) = m + 1 := rfl
  simp only [h3, Int.cast_add, Int.cast_one]

/-- g B_min t_sym is continuous. -/
lemma continuous_g_B_min_t_sym : Continuous (fun ξ => g B_min t_sym ξ) := by
  simp only [g]
  have ha : Continuous Q3.a := by
    have hpi : (2 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
    have h_eq : Q3.a = (fun ξ => (1 / (2 * Real.pi)) * Q3.a_star ξ) := by
      ext ξ
      simp only [Q3.a_star]
      field_simp [hpi]
    rw [h_eq]
    exact continuous_const.mul Q3.a_star_continuous
  have hw : Continuous (fun ξ => w B_min t_sym ξ) := by
    simp only [w]
    have h_lin : Continuous (fun ξ => 1 - |ξ| / B_min) :=
      continuous_const.sub (continuous_abs.div_const B_min)
    have h_max : Continuous (fun ξ => max (0 : ℝ) (1 - |ξ| / B_min)) :=
      continuous_const.max h_lin
    have h_exp : Continuous (fun ξ => Real.exp (-4 * Real.pi ^ 2 * t_sym * ξ ^ 2)) := by
      have h1 : Continuous (fun ξ => -4 * Real.pi ^ 2 * t_sym * ξ ^ 2) :=
        continuous_const.mul (continuous_pow 2)
      exact Real.continuous_exp.comp h1
    exact h_max.mul h_exp
  exact ha.mul hw

/-- g has compact support: g(ξ) = 0 when |ξ| ≥ B_min. -/
lemma g_support_B_min (ξ : ℝ) (h : B_min ≤ |ξ|) : g B_min t_sym ξ = 0 := by
  simp only [g, w]
  have hB : (0 : ℝ) < B_min := by norm_num [B_min]
  have h_lin : 1 - |ξ| / B_min ≤ 0 := by
    have h1 : 1 ≤ |ξ| / B_min := by
      rw [one_le_div hB]
      exact h
    linarith
  simp only [max_eq_left h_lin, zero_mul, mul_zero]

/-- For any θ₀, there exists N such that on (θ₀ - 1/2, θ₀ + 1/2),
    P_A equals a finite sum over |m| ≤ N. -/
lemma P_A_locally_finite_sum (θ₀ : ℝ) :
    ∃ N : ℕ, ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2),
      P_A B_min t_sym θ = 2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, g B_min t_sym (θ + m) := by
  -- For B_min = 3, if θ ∈ (θ₀ - 1/2, θ₀ + 1/2) and |m| > ⌈|θ₀|⌉ + 4, then g(θ + m) = 0
  use Nat.ceil |θ₀| + 4
  intro θ hθ
  unfold P_A
  congr 1
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  -- m ∉ [-(⌈|θ₀|⌉ + 4), ⌈|θ₀|⌉ + 4] means |m| > ⌈|θ₀|⌉ + 4
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
    have h_ceil : |θ₀| ≤ Nat.ceil |θ₀| := Nat.le_ceil |θ₀|
    have h_m_real : |θ₀| + 4 < |(m : ℝ)| := by
      have h1 : (Nat.ceil |θ₀| : ℝ) + 4 < |m| := by exact_mod_cast hN
      calc |θ₀| + 4 ≤ (Nat.ceil |θ₀| : ℝ) + 4 := by linarith
        _ < |m| := h1
        _ = |(m : ℝ)| := by simp [Int.cast_abs]
    -- |θ + m| ≥ |m| - |θ| > |θ₀| + 4 - (|θ₀| + 1/2) > 3 = B_min
    have h_tri : |(m : ℝ)| - |θ| ≤ |θ + (m : ℝ)| := by
      have h1 := abs_sub_abs_le_abs_sub (m : ℝ) (-θ)
      simp only [abs_neg, sub_neg_eq_add] at h1
      calc |(m : ℝ)| - |θ| ≤ |(m : ℝ) + θ| := h1
        _ = |θ + (m : ℝ)| := by ring_nf
    have h_final : (B_min : ℝ) < |θ + (m : ℝ)| := by
      calc (B_min : ℝ) = 3 := by norm_num [B_min]
        _ < 3.5 := by norm_num
        _ = |θ₀| + 4 - (|θ₀| + 1/2) := by ring
        _ < |(m : ℝ)| - |θ| := by linarith
        _ ≤ |θ + (m : ℝ)| := h_tri
    have h_eq : |θ + (m : ℝ)| = |θ + m| := by norm_cast
    linarith [h_final, h_eq.symm ▸ h_final]
  exact g_support_B_min (θ + m) h_large

/-- Continuity of the periodized symbol at the A3_FLOOR parameters. -/
theorem P_A_continuous : Continuous (P_A B_min t_sym) := by
  rw [continuous_iff_continuousAt]
  intro θ₀
  -- Use local finiteness: near θ₀, P_A is a finite sum
  obtain ⟨N, hN⟩ := P_A_locally_finite_sum θ₀
  -- The finite sum function is continuous
  let f := fun θ => 2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, g B_min t_sym (θ + m)
  have h_sum_cont : Continuous f := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro m _
    exact continuous_g_B_min_t_sym.comp (continuous_id.add continuous_const)
  -- P_A equals f on a neighborhood of θ₀
  have h_mem : Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2) ∈ nhds θ₀ := by
    apply Ioo_mem_nhds <;> linarith
  have h_eq : ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2), P_A B_min t_sym θ = f θ := hN
  -- f is continuous at θ₀
  have h_f_cont : ContinuousAt f θ₀ := h_sum_cont.continuousAt
  -- P_A =ᶠ f near θ₀
  have h_eq_f : P_A B_min t_sym =ᶠ[nhds θ₀] f := by
    apply Filter.eventuallyEq_of_mem h_mem
    intro θ hθ
    exact h_eq θ hθ
  exact h_f_cont.congr h_eq_f.symm

lemma a_antitone_on_Ioi : AntitoneOn Q3.a (Set.Ioi 0) := by
  intro x hx y hy hxy
  by_cases hxy' : x = y
  · simpa [hxy']
  · have hlt : x < y := lt_of_le_of_ne hxy hxy'
    exact (strictAntiOn_a hx hy hlt).le

lemma a_even (ξ : ℝ) : Q3.a (-ξ) = Q3.a ξ := by
  have h := Q3.a_star_even ξ
  have h' : (2 * Real.pi : ℝ) * Q3.a (-ξ) = (2 * Real.pi : ℝ) * Q3.a ξ := by
    simpa [Q3.a_star, mul_comm, mul_left_comm, mul_assoc] using h
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  exact mul_left_cancel₀ hpi h'

lemma w_even (B t ξ : ℝ) : w B t (-ξ) = w B t ξ := by
  simp [w, abs_neg, pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma g_even (B t ξ : ℝ) : g B t (-ξ) = g B t ξ := by
  simp [g, a_even, w_even]

lemma a_zero_ge_a_half : Q3.a 0 ≥ Q3.a (1 / 2 : ℝ) := by
  have hcont : ContinuousWithinAt Q3.a (Set.Ici 0) 0 := by
    simpa using (continuousOn_a.continuousWithinAt (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ)))
  have hseq :
      Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq'' :
      Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hseq
  have hseq' :
      Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) atTop (nhdsWithin (0 : ℝ) (Set.Ici 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (f := fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) (s := Set.Ici 0) hseq'' ?_
    refine (Filter.Eventually.of_forall ?_)
    intro n
    have hpos : (0 : ℝ) ≤ (1 / ((n + 1 : ℕ) : ℝ)) := by
... [truncated 823 lines]


## File: full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Bounds.lean

import Mathlib
import Q3.Basic.Defs
import Q3.Axioms
import Q3.DigammaRemainder

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set
open Q3 (a)

set_option maxHeartbeats 400000

noncomputable section

def B_min : ℝ := 3
def t_sym : ℝ := 3 / 50

def w (B t xi : ℝ) : ℝ :=
  max 0 (1 - |xi| / B) * Real.exp (-4 * Real.pi^2 * t * xi^2)

lemma w_half_eq :
    w B_min t_sym (1 / 2) = (5 / 6 : ℝ) * Real.exp (-3 * Real.pi^2 / 50) := by
  have hnonneg : (0 : ℝ) ≤ 1 - (2⁻¹ : ℝ) / 3 := by norm_num
  simp [w, B_min, t_sym, pow_two, mul_comm, mul_left_comm, mul_assoc]
  rw [max_eq_right hnonneg]
  ring_nf

lemma w_one_eq :
    w B_min t_sym 1 = (2 / 3 : ℝ) * Real.exp (-12 * Real.pi^2 / 50) := by
  have hnonneg : (0 : ℝ) ≤ 1 - (3⁻¹ : ℝ) := by norm_num
  simp [w, B_min, t_sym, pow_two, mul_comm, mul_left_comm, mul_assoc]
  rw [max_eq_right hnonneg]
  ring_nf

lemma w_two_eq :
    w B_min t_sym 2 = (1 / 3 : ℝ) * Real.exp (-48 * Real.pi^2 / 50) := by
  have hnonneg : (0 : ℝ) ≤ 1 - (2 : ℝ) / 3 := by norm_num
  simp [w, B_min, t_sym, pow_two, mul_comm, mul_left_comm, mul_assoc]
  rw [max_eq_right hnonneg]
  ring_nf

lemma exp_bound_half :
    Real.exp (-3 * Real.pi^2 / 50) ≥ (27 / 50 : ℝ) := by
  suffices h_exp : 3 * Real.pi ^ 2 / 50 ≤ Real.log (50 / 27) by
    exact le_trans (by norm_num [Real.exp_neg, Real.exp_log])
      (Real.exp_le_exp.mpr (show -3 * Real.pi ^ 2 / 50 ≥ -Real.log (50 / 27) by
        linarith))
  have h_pi_approx : Real.pi < 3.15 := by
    exact Real.pi_lt_d2
  have h_log_approx : Real.log (50 / 27) > 0.6 := by
    norm_num [Real.log_lt_log]
    rw [div_lt_iff₀'] <;> norm_num [← Real.log_rpow, Real.lt_log_iff_exp_lt]
    have := Real.exp_one_lt_d9.le
    norm_num1 at *
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.add_one_le_exp 1]
  norm_num at *
  nlinarith [Real.pi_gt_three]

theorem w_half_bound : w B_min t_sym (1 / 2) ≥ (9 / 20 : ℝ) := by
  have h_exp : Real.exp (-3 * Real.pi^2 / 50) ≥ (27 / 50 : ℝ) := exp_bound_half
  have hpos : (0 : ℝ) ≤ (5 / 6 : ℝ) := by norm_num
  calc
    w B_min t_sym (1 / 2)
        = (5 / 6 : ℝ) * Real.exp (-3 * Real.pi^2 / 50) := w_half_eq
    _ ≥ (5 / 6 : ℝ) * (27 / 50 : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_exp hpos
    _ = (9 / 20 : ℝ) := by norm_num

lemma log_one_add_le (u : ℝ) (hu : 0 ≤ u) : Real.log (1 + u) ≤ u := by
  have hpos : 0 < 1 + u := by linarith
  have hle : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using (Real.add_one_le_exp u)
  exact (Real.log_le_iff_le_exp hpos).2 hle

lemma log_abs_z_le (xi : ℝ) (hxi : 0 < xi) :
    Real.log ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖ ≤
      Real.log (Real.pi * xi) + (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * xi
  set u : ℝ := 1 / (16 * Real.pi^2 * xi^2)
  have hxi_ne : xi ≠ 0 := by linarith
  have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
  have hquarter : (4⁻¹ : ℝ)^2 = (4^2)⁻¹ := by norm_num
  have hpos_pi_xi : 0 < Real.pi * xi := mul_pos hpi_pos hxi
  have hs_nonneg : 0 ≤ (Real.pi * xi)^2 + (4^2)⁻¹ := by
    simpa [hquarter] using (by nlinarith : 0 ≤ (Real.pi * xi)^2 + (4⁻¹ : ℝ)^2)
  have h_abs' :
      ‖z‖ =
        Real.sqrt (4⁻¹ * 4⁻¹ + xi * (xi * (Real.pi * Real.pi))) := by
    simp [Complex.norm_def, Complex.normSq_apply, z, pow_two, mul_comm, mul_left_comm, mul_assoc]
  have h_abs :
      ‖z‖ = Real.sqrt ((Real.pi * xi)^2 + (4^2)⁻¹) := by
    have h_inside :
        4⁻¹ * 4⁻¹ + xi * (xi * (Real.pi * Real.pi)) =
          (Real.pi * xi)^2 + (4^2)⁻¹ := by
      ring
    simpa [h_inside] using h_abs'
  have hlog_abs :
      Real.log ‖z‖ =
        (1 / 2 : ℝ) * Real.log ((Real.pi * xi)^2 + (4^2)⁻¹) := by
    calc
      Real.log ‖z‖ = Real.log (Real.sqrt ((Real.pi * xi)^2 + (4^2)⁻¹)) := by
        simpa [h_abs]
      _ = Real.log ((Real.pi * xi)^2 + (4^2)⁻¹) / 2 := by
        simpa using (Real.log_sqrt hs_nonneg)
      _ = (1 / 2 : ℝ) * Real.log ((Real.pi * xi)^2 + (4^2)⁻¹) := by
        ring
  have hpi_sq_ne : (Real.pi^2 : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 hpi_ne
  have hxi_sq_ne : (xi^2 : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 hxi_ne
  have hmul : (Real.pi * xi)^2 * u = (4^2)⁻¹ := by
    calc
      (Real.pi * xi)^2 * u =
          (Real.pi^2 * xi^2) * (1 / (16 * Real.pi^2 * xi^2)) := by
        simp [u, pow_two, mul_comm, mul_left_comm, mul_assoc]
      _ = (1 / 16 : ℝ) := by
        field_simp [hpi_sq_ne, hxi_sq_ne]
      _ = (4^2)⁻¹ := by norm_num
  have hs_eq :
      (Real.pi * xi)^2 + (4^2)⁻¹ =
        (Real.pi * xi)^2 * (1 + u) := by
    calc
      (Real.pi * xi)^2 + (4^2)⁻¹ =
          (Real.pi * xi)^2 + (Real.pi * xi)^2 * u := by
        simpa [hmul]
      _ = (Real.pi * xi)^2 * (1 + u) := by ring
  have hpos_sq : 0 < (Real.pi * xi)^2 := by nlinarith [hpos_pi_xi]
  have hu_nonneg : 0 ≤ u := by
    have hpos : 0 < (16 * Real.pi^2 * xi^2 : ℝ) := by nlinarith [Real.pi_pos, hxi]
    nlinarith [u]
  have hpos_one_u : 0 < 1 + u := by nlinarith [hu_nonneg]
  have hlog_split :
      Real.log ((Real.pi * xi)^2 + (4^2)⁻¹) =
        Real.log ((Real.pi * xi)^2) + Real.log (1 + u) := by
    calc
      Real.log ((Real.pi * xi)^2 + (4^2)⁻¹)
          = Real.log ((Real.pi * xi)^2 * (1 + u)) := by simpa [hs_eq]
      _ = Real.log ((Real.pi * xi)^2) + Real.log (1 + u) := by
        simpa using (Real.log_mul hpos_sq.ne' hpos_one_u.ne')
  have hlog_sq :
      Real.log ((Real.pi * xi)^2) = 2 * Real.log (Real.pi * xi) := by
    have h := Real.log_mul hpos_pi_xi.ne' hpos_pi_xi.ne'
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using h
  have hlog_abs' :
      Real.log ‖z‖ =
        Real.log (Real.pi * xi) + (1 / 2 : ℝ) * Real.log (1 + u) := by
    calc
      Real.log ‖z‖ =
          (1 / 2 : ℝ) * (Real.log ((Real.pi * xi)^2) + Real.log (1 + u)) := by
        simpa [hlog_abs, hlog_split]
      _ = (1 / 2 : ℝ) * (2 * Real.log (Real.pi * xi)) +
            (1 / 2 : ℝ) * Real.log (1 + u) := by
        simp [hlog_sq, mul_add, mul_comm, mul_left_comm, mul_assoc]
      _ = Real.log (Real.pi * xi) + (1 / 2 : ℝ) * Real.log (1 + u) := by ring
  have hlog_u : Real.log (1 + u) ≤ u := log_one_add_le u hu_nonneg
  have hbound : Real.log ‖z‖ ≤ Real.log (Real.pi * xi) + (1 / 2 : ℝ) * u := by
    nlinarith [hlog_abs', hlog_u]
  have hconst :
      (1 / 2 : ℝ) * u = (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
    calc
      (1 / 2 : ℝ) * u =
          (1 / 2 : ℝ) * (1 / (16 * Real.pi^2 * xi^2)) := by
        simp [u]
      _ = (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
        field_simp [hpi_sq_ne, hxi_sq_ne]
        ring
  have hbound' :
      Real.log ‖z‖ ≤ Real.log (Real.pi * xi) + (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
    nlinarith [hbound, hconst]
  exact hbound'

/- DEAD CODE: Requires non-existent `re_digamma_remainder_bound` (expects 1/12 bound).
   Only used by `a_ge_neg_log_xi` which is also unused.
   The working path uses `a_lower_bound_from_stieltjes` with 1/4 bound.

lemma a_lower_bound_from_remainder (xi : ℝ) (hxi : 0 < xi) :
    a xi ≥
      Real.log Real.pi -
        Real.log ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖ +
        (1 / 24 : ℝ) * (1 / ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖^2) := by
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * xi
  have hz : (1 / 4 : ℝ) ≤ z.re := by simp [z]
  have hrem := re_digamma_remainder_bound z hz
  have hrem' :
      |(Q3.digamma z).re - (Real.log ‖z‖ - z.re / (2 * ‖z‖^2))| ≤
        1 / (12 * ‖z‖^2) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrem
  have hle :
      (Q3.digamma z).re ≤
        Real.log ‖z‖ - z.re / (2 * ‖z‖^2) + 1 / (12 * ‖z‖^2) := by
    have hle' := (abs_sub_le_iff.mp hrem').1
    linarith
  have hconst :
      z.re / (2 * ‖z‖^2) - 1 / (12 * ‖z‖^2) =
        (1 / 24 : ℝ) * (1 / ‖z‖^2) := by
    simp [z, mul_comm, mul_left_comm, mul_assoc]
    ring
  have hmain :
      a xi ≥ Real.log Real.pi - Real.log ‖z‖ + (1 / 24 : ℝ) * (1 / ‖z‖^2) := by
... [truncated 661 lines]


## File: full/q3.lean.aristotle/Q3/Proofs/ShiftedWindows.lean

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

lemma P_A_shift_locally_finite_sum (B t tau θ₀ : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2),
      Q3.P_A_shift B t tau θ =
        2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, Q3.g_shift B t tau (θ + m) := by
  let K : ℝ := |tau| + B
  refine ⟨Nat.ceil (|θ₀| + K) + 4, ?_⟩
  intro θ hθ
  unfold Q3.P_A_shift
  congr 1
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
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
  have hN : (Nat.ceil (|θ₀| + K) : ℤ) + 4 < |m| := by
    by_cases h : m < -((Nat.ceil (|θ₀| + K) : ℤ) + 4)
    · have hm_neg : m < 0 := by omega
      simp only [abs_of_neg hm_neg]
      omega
    · push_neg at h
      have hm' := hm h
      have hm_nonneg : 0 ≤ m := by omega
      simp only [abs_of_nonneg hm_nonneg]
      exact hm'
  have h_m_real : |θ₀| + K + 4 < |(m : ℝ)| := by
    have h1 : (Nat.ceil (|θ₀| + K) : ℝ) + 4 < |m| := by exact_mod_cast hN
    have hceil : |θ₀| + K ≤ (Nat.ceil (|θ₀| + K) : ℝ) := by
      exact Nat.le_ceil (|θ₀| + K)
    calc |θ₀| + K + 4 ≤ (Nat.ceil (|θ₀| + K) : ℝ) + 4 := by linarith
      _ < |m| := h1
      _ = |(m : ℝ)| := by simp [Int.cast_abs]
  have h_tri : |(m : ℝ)| - |θ| ≤ |θ + (m : ℝ)| := by
    have h1 := abs_sub_abs_le_abs_sub (m : ℝ) (-θ)
    have h2 : |(m : ℝ)| - |θ| ≤ |(m : ℝ) + θ| := by
      simpa [abs_neg, sub_eq_add_neg] using h1
    simpa [add_comm] using h2
  have h_final : K < |θ + (m : ℝ)| := by
    have hmid : K < |(m : ℝ)| - |θ| := by
      linarith [h_m_real, hθ_bound]
    linarith [h_tri, hmid]
  have h_final' : K < |θ + m| := by
    simpa using h_final
  exact g_shift_support_of_margin B t tau K hB (by simp [K, add_comm]) (θ + m) h_final'

lemma P_A_shift_tsum_eq_finite_sum (B t tau theta : ℝ) (hB : 0 < B)
... [truncated 187 lines]


## File: full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_base_atoms_proof.lean

/-
Q_nonneg on BaseAtomCone_K — Proof
===================================

This file proves Q ≥ 0 on BaseAtomCone_K (atoms with τ = 0) using:
1. Connection: Fejer_heat_atom B t0_A1 0 = c * fejer_heat_window B t_sym
2. Rayleigh-Q identification for fejer_heat_window
3. A3 floor: RQ(Toeplitz[P_A]) ≥ c_star
4. RKHS cap: prime_sum ≤ rho_one

This closes the path from A3 bridge to Q ≥ 0 on centered atoms.

Integration: axiom-closure 2026-01-22
-/

import Q3.Axioms
import Q3.Proofs.HeatKernelParams
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.P_A_Toeplitz_bridge
import Q3.Proofs.Q_nonneg_atoms_helpers
import Q3.Proofs.A3_Floor_Main

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.BaseAtomProof

open Q3

/-! ## Step 0: Key identities at τ = 0 -/

/-- phi_shift at τ = 0 is just fejer_heat_window. -/
lemma phi_shift_tau_zero (B t ξ : ℝ) :
    phi_shift B t 0 ξ = fejer_heat_window B t ξ := by
  simp only [phi_shift, sub_zero]

/-- g_shift at τ = 0 equals g from A3_Floor_Main.
    Note: g B t ξ = a ξ * w B t ξ where w = fejer_heat_window. -/
lemma g_shift_tau_zero (B t ξ : ℝ) :
    g_shift B t 0 ξ = a ξ * fejer_heat_window B t ξ := by
  simp only [g_shift, phi_shift_tau_zero]

/-- P_A_shift at τ = 0 equals P_A from A3_Floor_Main.
    This is the KEY IDENTITY that connects the shifted formulation to A3 floor. -/
lemma P_A_shift_tau_zero (B t θ : ℝ) :
    P_A_shift B t 0 θ = P_A B t θ := by
  simp only [P_A_shift, P_A, g_shift_tau_zero]
  congr 1
  ext m
  simp only [g, w]
  -- w B t = fejer_heat_window B t by definition
  rfl

/-! ## Step 1: Fejer_heat_atom at τ = 0 equals scaled fejer_heat_window -/

/-- For τ = 0, Fejer_heat_atom simplifies to 2 * Fejer_kernel * heat_kernel_A1. -/
lemma Fejer_heat_atom_tau_zero (B t ξ : ℝ) :
    Fejer_heat_atom B t 0 ξ = 2 * Fejer_kernel B ξ * heat_kernel_A1 t ξ := by
  simp only [Fejer_heat_atom, sub_zero, add_zero]
  ring

/-- heat_kernel_A1 at t0_A1 relates to the exponential in fejer_heat_window at t_sym. -/
lemma heat_kernel_exp_relation (ξ : ℝ) :
    Real.exp (-ξ^2 / (4 * t0_A1)) = Real.exp (-4 * Real.pi^2 * t_sym * ξ^2) :=
  exp_reparam ξ

/-- Scaling factor between heat_kernel_A1 and fejer_heat_window's exponential. -/
noncomputable def heat_scaling : ℝ := 1 / Real.sqrt (4 * Real.pi * t0_A1)

lemma heat_scaling_pos : heat_scaling > 0 := by
  unfold heat_scaling
  apply div_pos one_pos
  apply Real.sqrt_pos_of_pos
  have ht : t0_A1 > 0 := t0_A1_pos
  nlinarith [Real.pi_pos]

/-- Connection: heat_kernel_A1 t0_A1 ξ = heat_scaling * exp(-4π²t_sym·ξ²) -/
lemma heat_kernel_A1_eq_scaled_exp (ξ : ℝ) :
    heat_kernel_A1 t0_A1 ξ = heat_scaling * Real.exp (-4 * Real.pi^2 * t_sym * ξ^2) := by
  simp only [heat_kernel_A1, heat_scaling, exp_reparam]

/-- Main connection: Fejer_heat_atom B t0_A1 0 ξ = 2 * heat_scaling * fejer_heat_window B t_sym ξ -/
lemma Fejer_heat_atom_tau_zero_eq_scaled_window (B ξ : ℝ) (hB : B > 0) :
    Fejer_heat_atom B t0_A1 0 ξ =
      2 * heat_scaling * fejer_heat_window B t_sym ξ := by
  rw [Fejer_heat_atom_tau_zero, heat_kernel_A1_eq_scaled_exp]
  simp only [fejer_heat_window, Fejer_kernel, heat_scaling]
  ring

/-! ## Step 2: Q on centered atom equals scaled Q on fejer_heat_window -/

/-- Q scales with constants. -/
lemma Q_scale_const (c : ℝ) (f : ℝ → ℝ)
    (hf_int : MeasureTheory.Integrable (fun x => a_star x * f x))
    (hf_sum : Summable (fun k => w_Q k * f (xi_n k))) :
    Q (fun x => c * f x) = c * Q f := by
  simp only [Q, arch_term, prime_term]
  have h1 : ∫ x, a_star x * (c * f x) = c * ∫ x, a_star x * f x := by
    have heq : (fun x => a_star x * (c * f x)) = (fun x => c * (a_star x * f x)) := by
      ext x; ring
    rw [heq, MeasureTheory.integral_mul_left]
  have h2 : ∑' k, w_Q k * (c * f (xi_n k)) = c * ∑' k, w_Q k * f (xi_n k) := by
    have heq : (fun k => w_Q k * (c * f (xi_n k))) = (fun k => c * (w_Q k * f (xi_n k))) := by
      ext k; ring
    rw [heq, tsum_mul_left]
  rw [h1, h2]
  ring

/-! ## Step 3: Q ≥ 0 on phi_shift at τ = 0 via A3 floor -/

/-- Rayleigh quotient for P_A_shift at τ = 0 reduces to P_A.
    Uses P_A_shift_tau_zero and P_A_rayleigh_lower_bound_odd. -/
lemma rayleigh_P_A_shift_tau_zero (M : ℕ) (v : Fin (2 * M + 1) → ℝ) (hv : v ≠ 0) :
    RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A_shift B_min t_sym 0)) v
    ≥ c_star := by
  -- P_A_shift B_min t_sym 0 = P_A B_min t_sym by P_A_shift_tau_zero
  have h_eq : P_A_shift B_min t_sym 0 = P_A B_min t_sym := by
    ext θ
    exact P_A_shift_tau_zero B_min t_sym θ
  rw [h_eq]
  exact Q3.Proofs.P_A_Bridge.P_A_rayleigh_lower_bound_odd M v hv

/-- P_A_shift B_min t_sym 0 is continuous (inherited from P_A). -/
lemma P_A_shift_tau_zero_continuous :
    Continuous (P_A_shift B_min t_sym 0) := by
  have h_eq : P_A_shift B_min t_sym 0 = P_A B_min t_sym := by
    ext θ; exact P_A_shift_tau_zero B_min t_sym θ
  rw [h_eq]
  exact P_A_continuous

/-- Q on phi_shift at τ = 0 (= fejer_heat_window) is nonnegative via A3 floor.

    Key path:
    1. phi_shift B_min t_sym 0 = fejer_heat_window B_min t_sym (by phi_shift_tau_zero)
    2. P_A_shift B_min t_sym 0 = P_A B_min t_sym (by P_A_shift_tau_zero)
    3. RQ(Toeplitz[P_A B_min t_sym]) ≥ c_star (by P_A_rayleigh_lower_bound_odd)
    4. Apply Q_phi_shift_nonneg with R = rho_one
-/
theorem Q_nonneg_phi_shift_tau_zero (K : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1) (hBK : B_min ≤ K)
    (h_cap : ∑ n : Nodes K, w_Q n * phi_shift B_min t_rkhs_cap 0 (xi_n n) ≤
        Q3.Proofs.rho_one) :
    Q (fun ξ => phi_shift B_min t_sym 0 ξ) ≥ 0 := by
  have hB_pos : (0 : ℝ) < B_min := by norm_num [B_min]
  have hK_support : |0| + B_min ≤ K := by simp [hBK]
  have hP_cont : Continuous (P_A_shift B_min t_sym 0) := P_A_shift_tau_zero_continuous
  have hM : 0 < 2 * 0 + 1 := by norm_num
  -- Rayleigh bound: RQ ≥ c_star ≥ c_star/4
  have h_rayleigh : RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * 0 + 1) (P_A_shift B_min t_sym 0))
      (Q3.Proofs.RayleighQId.basis0 0) ≥ c_star / 4 := by
    have h_full := rayleigh_P_A_shift_tau_zero 0
      (Q3.Proofs.RayleighQId.basis0 0) (Q3.Proofs.RayleighQId.basis0_ne_zero 0)
    have h_quarter : c_star / 4 ≤ c_star := by
      have hc : c_star > 0 := by norm_num [c_star]
      linarith
    exact le_trans h_quarter h_full
  -- Positivity condition: c_star/4 - exp_factor * rho_one ≥ 0
  have hpos : 0 ≤ c_star / 4 - Q3.Proofs.PrimeTermBridge.exp_tsym_to_rkhs K * Q3.Proofs.rho_one := by
    -- This needs the cap bound to be small enough
    -- exp_tsym_to_rkhs K * rho_one < c_star/4
    -- For K ≥ 1, this should hold by construction
    sorry  -- Needs numerical bound on exp_tsym_to_rkhs
  exact Q3.Proofs.QNonnegAtoms.Q_phi_shift_nonneg
    (K:=K) (B:=B_min) (tau:=0) (R:=Q3.Proofs.rho_one) (M:=0)
    hB_pos hK_support hP_cont hM h_cap h_rayleigh hpos

/-- Q on fejer_heat_window B_min t_sym is nonnegative.
    This is a direct corollary of Q_nonneg_phi_shift_tau_zero. -/
theorem Q_nonneg_fejer_heat_window_B_min (K : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1) (hBK : B_min ≤ K)
    (h_cap : ∑ n : Nodes K, w_Q n * fejer_heat_window B_min t_rkhs_cap (xi_n n) ≤
        Q3.Proofs.rho_one) :
    Q (fun ξ => fejer_heat_window B_min t_sym ξ) ≥ 0 := by
  -- fejer_heat_window B_min t_sym = phi_shift B_min t_sym 0
  have h_eq : (fun ξ => fejer_heat_window B_min t_sym ξ) =
              (fun ξ => phi_shift B_min t_sym 0 ξ) := by
    ext ξ
    exact (phi_shift_tau_zero B_min t_sym ξ).symm
  rw [h_eq]
  -- Also convert h_cap
  have h_cap' : ∑ n : Nodes K, w_Q n * phi_shift B_min t_rkhs_cap 0 (xi_n n) ≤
      Q3.Proofs.rho_one := by
    convert h_cap using 2
    ext n
    congr 1
    exact (phi_shift_tau_zero B_min t_rkhs_cap (xi_n n)).symm
  exact Q_nonneg_phi_shift_tau_zero K hK hBK h_cap'

/-- Q ≥ 0 on centered Fejer_heat_atom with B = B_min. -/
theorem Q_nonneg_centered_atom_B_min (K : ℝ) [Fintype (Nodes K)]
    (hK : K ≥ 1) (hBK : B_min ≤ K)
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K) :
    Q (Fejer_heat_atom B_min t0_A1 0) ≥ 0 := by
  sorry  -- Use Fejer_heat_atom_tau_zero_eq_scaled_window + Q_scale_const + Q_nonneg_fejer_heat_window_B_min
... [truncated 29 lines]


## File: full/q3.lean.aristotle/Q3/Proofs/Params_Critical.lean

import Mathlib

/-!
Critical one-scale parameters (`t = 3/20`)
=========================================

This module centralizes the *single-scale* parameter choice

* `t_critical = 3/20`
* `t0_critical = 1/(16π² t_critical)` so that
  `exp(-x^2/(4*t0_critical)) = exp(-4π² t_critical x^2)`.

It is intentionally independent of the legacy `t_sym` / `t_rkhs_cap` two-scale setup.
-/

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3

/-- Critical heat parameter where the numerical scan crosses to `Q ≥ 0`. -/
def t_critical : ℝ := 3 / 20

/-- A1 heat parameter corresponding to `t_critical` via `exp(-x^2/(4t0)) = exp(-4π^2 t x^2)`. -/
noncomputable def t0_critical : ℝ := 1 / (16 * Real.pi ^ 2 * t_critical)

lemma t_critical_pos : t_critical > 0 := by
  norm_num [t_critical]

lemma t0_critical_pos : t0_critical > 0 := by
  have ht : (0 : ℝ) < t_critical := t_critical_pos
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hden : 0 < 16 * Real.pi ^ 2 * t_critical := by nlinarith [hpi2, ht]
  simpa [t0_critical] using (one_div_pos.mpr hden)

lemma exp_reparam_critical (x : ℝ) :
    Real.exp (-x^2 / (4 * t0_critical)) = Real.exp (-4 * Real.pi ^ 2 * t_critical * x^2) := by
  have hden : (16 * Real.pi ^ 2 * t_critical) ≠ 0 := by
    have hden_pos : (0 : ℝ) < 16 * Real.pi ^ 2 * t_critical := by
      have ht : (0 : ℝ) < t_critical := t_critical_pos
      have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      nlinarith [hpi2, ht]
    exact ne_of_gt hden_pos
  have h :
      -x^2 / (4 * t0_critical) = -4 * Real.pi ^ 2 * t_critical * x^2 := by
    unfold t0_critical
    field_simp [hden]
    ring
  simp [h]

end Q3


## File: full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Critical_Goal.lean

import Mathlib
import Q3.Axioms
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

open scoped Real

noncomputable section

namespace Q3.Proofs.A3FloorCritical

/-- One-scale A3_FLOOR goal at the critical parameter `t_critical = 3/20`.

This is intentionally packaged as a `Prop` (not an axiom and not a sorry-proof) so we can
reference it in the decision tree / Aristotle prompts without polluting the main chain.
-/
def FloorGoal : Prop :=
  ∀ θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
    Q3.c_star ≤ P_A B_min Q3.t_critical θ

end Q3.Proofs.A3FloorCritical


## File: full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Critical_Proof.lean

import Q3.Proofs.A3_Floor_Critical_Goal
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical
import Q3.Proofs.Q_nonneg_t_critical

/-!
A3 Floor at t_critical: direct proof wrapper.

This file bridges FloorGoal to the concrete floor lemma at t_critical.
-/

open Q3

noncomputable section

namespace Q3.Proofs.A3FloorCritical

open Q3

/-! ## Tau=0 rewrite -/

lemma P_A_shift_tau_zero (B t θ : ℝ) :
    Q3.P_A_shift B t 0 θ = P_A B t θ := by
  -- P_A_shift uses phi_shift = fejer_heat_window, which matches w
  simp [Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g, w, Q3.fejer_heat_window]

/-- FloorGoal at t_critical, tau = 0. -/
theorem floor_goal_tcritical : Q3.Proofs.A3FloorCritical.FloorGoal := by
  intro θ hθ
  -- rewrite P_A_critical (tau = 0) to standard P_A
  have hPA : Q3.P_A_critical B_min θ = P_A B_min t_critical θ := by
    -- P_A_critical is defined via P_A_shift at tau = 0
    simpa [Q3.P_A_critical] using (P_A_shift_tau_zero B_min t_critical θ)
  -- floor lemma at t_critical (currently a TODO in Q_nonneg_t_critical.lean)
  have hfloor : Q3.P_A_critical B_min θ ≥ c_star := by
    simpa using (Q3.P_A_ge_c_star_at_t_critical (θ := θ))
  -- conclude FloorGoal
  simpa [hPA] using hfloor

end Q3.Proofs.A3FloorCritical
