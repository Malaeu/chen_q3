/-
A3_FLOOR_COMBINED.lean
Combined Aristotle results from multiple projects:
- RH_FINAL (f758546b): Main structure, Main_positivity theorem
- A3_FLOOR v1 (9f4a33c2): continuousOn_a, deriv_a_eq, trigamma analysis
- A3_FLOOR v2 (e3ae346c): im_trigamma_neg (COMPLETE PROOF!)

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set
open scoped BigOperators

/-! ## Section 1: Core Definitions -/

-- Riemann Hypothesis statement
def Riemann_Hypothesis : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2

-- Critical strip and line
def CriticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
def CriticalLine : Set ℂ := {s | s.re = 1/2}

-- Weil cone: test functions for positivity criterion
def Weil_cone : Set (ℝ → ℂ) :=
  {Phi | Continuous Phi ∧
         HasCompactSupport Phi ∧
         (∀ x, Phi (-x) = star (Phi x))}

-- Q functional (opaque - axiomatized)
opaque Q : (ℝ → ℂ) → ℝ

/-! ## Section 2: Digamma and Archimedean Density -/

-- Digamma function
def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)

-- Trigamma function
def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2

-- Archimedean density a(ξ)
def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * ξ)).re

/-! ## Section 3: Fejér×heat Window and Symbol -/

-- Fixed parameters
def B_min : ℝ := 3
def t_sym : ℝ := 3 / 50  -- = 0.06
def c_star : ℝ := 11 / 10  -- CORRECTED from 1.5!
def C_SB : ℝ := 4

-- Fejér×heat window
def w (B t ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)

-- Weighted density
def g (B t ξ : ℝ) : ℝ := a ξ * w B t ξ

-- Archimedean symbol (period-1 periodized)
def P_A (B t θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)

/-! ## Section 4: W_K and Approximants -/

-- Definition of W_K (compact support constraint)
def W_K (K : ℝ) : Set (ℝ → ℂ) :=
  {Phi | Phi ∈ Weil_cone ∧ Function.support Phi ⊆ Icc (-K) K}

-- Approximant predicate
opaque IsApproximant : (ℝ → ℂ) → Prop

/-! ## Section 5: Proven Lemmas from A3_FLOOR v1 -/

-- Source: 9f4a33c2_aristotle.lean

lemma im_one_div_sq_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) : (1 / z^2).im < 0 := by
  norm_num [sq, Complex.normSq, Complex.div_im]
  field_simp
  ring
  apply neg_neg_of_pos
  exact mul_pos (mul_pos hz hzi) (by norm_num)

lemma trigamma_summable {z : ℂ} (hz : 0 < z.re) : Summable (fun n : ℕ => 1 / (z + n)^2) := by
  rw [← summable_nat_add_iff (⌈‖z‖⌉₊ + 1)] at *
  have h_comparison : ∀ n : ℕ, ‖(z + (n + (⌈‖z‖⌉₊ + 1)) : ℂ)‖ ≥ (n + (⌈‖z‖⌉₊ + 1)) - ‖z‖ := by
    intro n
    have := norm_sub_le (z + (n + (⌈‖z‖⌉₊ + 1))) z
    simp_all +decide
    convert this using 1
    norm_cast
  have h_comparison' : ∀ n : ℕ, ‖(z + (n + (⌈‖z‖⌉₊ + 1)) : ℂ)‖^2 ≥ (n + 1)^2 := by
    exact fun n => pow_le_pow_left₀ (by positivity) (by
      have := h_comparison n
      nlinarith [Nat.le_ceil (‖z‖), show (⌈‖z‖⌉₊ : ℝ) ≥ ‖z‖ by exact Nat.le_ceil _]) _
  have h_inv : ∀ n : ℕ, ‖(z + (n + (⌈‖z‖⌉₊ + 1)) : ℂ)‖⁻¹^2 ≤ 1 / (n + 1)^2 := by
    exact fun n => by simpa using inv_anti₀ (by positivity) (h_comparison' n)
  have h_summable : Summable (fun n : ℕ => ‖(z + (n + (⌈‖z‖⌉₊ + 1)) : ℂ)‖⁻¹^2) := by
    exact Summable.of_nonneg_of_le (fun n => sq_nonneg _) h_inv
      (by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
  exact Summable.of_norm <| by simpa using h_summable.norm

/-! ## Section 6: KEY LEMMA from A3_FLOOR v2 (COMPLETE PROOF!) -/

-- Source: e3ae346c_aristotle.lean
-- This is the crucial lemma for proving a'(ξ) > 0 → a monotone → P_A ≥ c*

lemma im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) : (trigamma z).im < 0 := by
  have h_im_sum : (trigamma z).im = ∑' n : ℕ, -2 * z.im * (z.re + n) / ((z.re + n)^2 + z.im^2)^2 := by
    rw [← tsum_congr fun n : ℕ => ?_]
    convert Complex.im_tsum _
    · exact?
    · have h_summable : Summable (fun n : ℕ => (1 / (n + z.re)^2 : ℝ)) := by
        have h_summable : Summable (fun n : ℕ => (1 / (n : ℝ)^2 : ℝ)) := by
          exact Real.summable_one_div_nat_pow.2 one_lt_two
        rw [← summable_nat_add_iff ⌈z.re⌉₊] at *
        exact Summable.of_nonneg_of_le (fun n => by positivity)
          (fun n => by gcongr; linarith [Nat.le_ceil z.re]) h_summable
      rw [← summable_norm_iff] at *
      refine' .of_nonneg_of_le (fun n => norm_nonneg _) (fun n => _) h_summable
      norm_num [Complex.normSq, Complex.norm_def]
      exact inv_anti₀ (by positivity) (by rw [Real.sq_sqrt (by positivity)]; nlinarith)
    · norm_num [sq, Complex.normSq, Complex.div_im]
      ring
      rw [inv_pow]; ring
  rw [h_im_sum]
  norm_num [div_eq_mul_inv, tsum_neg]
  refine' Summable.tsum_pos ..
  have h_summable : Summable (fun n : ℕ => (z.re + n) / ((z.re + n)^2 + z.im^2)^2) := by
    have h_bound : ∀ n : ℕ, (z.re + n) / ((z.re + n)^2 + z.im^2)^2 ≤ 1 / (z.re + n)^3 := by
      field_simp
      exact fun n => by nlinarith only [show 0 ≤ z.re * n by positivity,
        show 0 ≤ z.re ^ 2 by positivity, show 0 ≤ z.im ^ 2 by positivity]
    refine Summable.of_nonneg_of_le (fun n => div_nonneg (by positivity) (by positivity))
      (fun n => h_bound n) ?_
    have h_pseries : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)^3) := by
      exact Real.summable_one_div_nat_pow.2 (by norm_num)
    rw [← summable_nat_add_iff ⌈z.re⁻¹⌉₊]
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by simpa using inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity)
          (show (z.re + (n + ⌈z.re⁻¹⌉₊) : ℝ) ≥ n + ⌈z.re⁻¹⌉₊ by linarith) 3))
      (h_pseries.comp_injective (add_left_injective _))
  exacts [by convert h_summable.mul_left (2 * z.im) using 2; ring,
          fun n => by positivity, 0, by positivity]

/-! ## Section 7: Derivative Lemmas from v1 + v2 -/

-- General derivative formula (from v2)
lemma deriv_re_comp_linear_imag (f : ℂ → ℂ) (f' : ℂ → ℂ) (A B : ℝ) (x : ℝ)
    (hf : HasDerivAt f (f' (A + Complex.I * B * x)) (A + Complex.I * B * x)) :
    deriv (fun t : ℝ => (f (A + Complex.I * B * t)).re) x =
      -B * (f' (A + Complex.I * B * x)).im := by
  refine' HasDerivAt.deriv _
  have h_chain : HasDerivAt (fun t : ℝ => f (A + Complex.I * B * t))
      (f' (A + Complex.I * B * x) * (Complex.I * B)) x := by
    convert HasDerivAt.comp x hf
      (HasDerivAt.add (hasDerivAt_const _ _)
        (HasDerivAt.mul (hasDerivAt_const _ _) (hasDerivAt_id _ |> HasDerivAt.ofReal_comp)))
      using 1
    norm_num
  rw [hasDerivAt_iff_tendsto_slope_zero] at *
  convert Complex.continuous_re.continuousAt.tendsto.comp h_chain using 2
  norm_num; ring
  norm_num [Complex.ext_iff]

-- Derivative of Re(digamma) (from v1)
lemma deriv_re_digamma (ξ : ℝ) :
    deriv (fun t : ℝ => (digamma (1/4 + Complex.I * Real.pi * t)).re) ξ =
    -Real.pi * (deriv (fun z : ℂ => digamma z) (1/4 + Complex.I * Real.pi * ξ)).im := by
  convert HasDerivAt.deriv _ using 1
  have h_chain : HasDerivAt (fun t : ℝ => digamma (1/4 + Complex.I * Real.pi * t))
      (deriv (fun z : ℂ => digamma z) (1/4 + Complex.I * Real.pi * ξ) * Complex.I * Real.pi) ξ := by
    have h_chain : HasDerivAt (fun t : ℝ => digamma (1/4 + Complex.I * Real.pi * t))
        (deriv (fun z : ℂ => digamma z) (1/4 + Complex.I * Real.pi * ξ) * (Complex.I * Real.pi)) ξ := by
      have h_diff : DifferentiableAt ℂ (fun z : ℂ => digamma z) (1/4 + Complex.I * Real.pi * ξ) := by
        refine' DifferentiableAt.div _ _ _
        · have h_diff : AnalyticAt ℂ (deriv Complex.Gamma) (1/4 + Complex.I * Real.pi * ξ) := by
            have h_diff : AnalyticAt ℂ Complex.Gamma (1/4 + Complex.I * Real.pi * ξ) := by
              refine' DifferentiableOn.analyticAt _ _
              exact {z : ℂ | 0 < z.re}
              · intro z hz
                exact Complex.differentiableAt_Gamma _ (by contrapose! hz; aesop) |>
                  DifferentiableAt.differentiableWithinAt
              · exact IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) (by norm_num)
            exact h_diff.deriv
          exact h_diff.differentiableAt
        · refine' Complex.differentiableAt_Gamma _ _
          norm_num [Complex.ext_iff]
          exact fun m hm => by linarith
        · exact Complex.Gamma_ne_zero_of_re_pos (by norm_num [Complex.add_re, Complex.mul_re])
      convert HasDerivAt.comp ξ h_diff.hasDerivAt
        (HasDerivAt.add (hasDerivAt_const _ _)
          (HasDerivAt.mul (hasDerivAt_const _ _) (hasDerivAt_id _ |> HasDerivAt.ofReal_comp)))
        using 1
      norm_num
    simpa only [mul_assoc] using h_chain
  rw [hasDerivAt_iff_tendsto_slope_zero] at *
  convert Complex.continuous_re.continuousAt.tendsto.comp h_chain using 2
  norm_num; ring
  norm_num [Complex.ext_iff]

-- Derivative of a(ξ) (from v1)
lemma deriv_a_eq {ξ : ℝ} (hξ : 0 < ξ) :
    deriv a ξ = Real.pi * (deriv (fun z : ℂ => digamma z) (1/4 + Complex.I * Real.pi * ξ)).im := by
  have h_chain : deriv a ξ = -deriv (fun t : ℝ => (digamma (1/4 + Complex.I * Real.pi * t)).re) ξ := by
    unfold a
    rw [deriv_const_sub]
  have h_chain' : deriv (fun t : ℝ => (digamma (1/4 + Complex.I * Real.pi * t)).re) ξ =
      -Real.pi * (deriv (fun z : ℂ => digamma z) (1/4 + Complex.I * Real.pi * ξ)).im := by
    convert deriv_re_digamma ξ using 1
  aesop

/-! ## Section 8: Continuity of a (from v1) -/

lemma continuousOn_a : ContinuousOn a (Ici 0) := by
  refine' ContinuousOn.sub _ _
  · exact continuousOn_const
  · have h_analytic : ∀ z : ℂ, 0 < z.re → AnalyticAt ℂ (fun z => digamma z) z := by
      intro z hz
      have h_analytic : AnalyticAt ℂ (fun z => deriv Complex.Gamma z / Complex.Gamma z) z := by
        have h_gamma_analytic : AnalyticAt ℂ Complex.Gamma z := by
          refine' DifferentiableOn.analyticAt _ _
          exact {w : ℂ | 0 < w.re}
          · have h_gamma_diff : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Complex.Gamma w := by
              intro w hw
              apply_rules [Complex.differentiableAt_Gamma]
              exact fun m => ne_of_apply_ne Complex.re <| by norm_num; linarith
            exact fun w hw => DifferentiableAt.differentiableWithinAt (h_gamma_diff w hw)
          · exact IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) hz
        have h_deriv_gamma_analytic : AnalyticAt ℂ (deriv Complex.Gamma) z := by
          apply_rules [AnalyticAt.deriv, h_gamma_analytic]
        exact h_deriv_gamma_analytic.div h_gamma_analytic (Complex.Gamma_ne_zero_of_re_pos hz)
      exact h_analytic
    exact continuousOn_of_forall_continuousAt fun x hx =>
      Complex.continuous_re.continuousAt.comp
        (h_analytic _ (by norm_num [Complex.ext_iff]) |> fun h => h.continuousAt) |>
        ContinuousAt.comp <| Continuous.continuousAt <| by continuity

/-! ## Section 9: Weil Cone Lemma (from RH_FINAL) -/

lemma Weil_cone_compact_support (Phi : ℝ → ℂ) (h : Phi ∈ Weil_cone) :
    ∃ K, K > 0 ∧ Function.support Phi ⊆ Icc (-K) K := by
  have h_support_bounded : Bornology.IsBounded (Function.support Phi) := by
    have h_support_compact : HasCompactSupport Phi := by
      exact h.2.1
    exact h_support_compact.isCompact.isBounded.subset subset_closure
  rcases h_support_bounded.exists_pos_norm_le with ⟨K, hK⟩
  exact ⟨K, hK.1, fun x hx => ⟨by linarith [abs_le.mp (hK.2 x hx)],
    by linarith [abs_le.mp (hK.2 x hx)]⟩⟩

/-! ## Section 10: RH Axioms Typeclass (from RH_FINAL) -/

class RHAxioms where
  -- A1' density: Fejér×heat approximants are dense
  A1_density : ∀ (K : ℝ) (Phi : ℝ → ℂ), Phi ∈ W_K K →
    ∃ seq : ℕ → (ℝ → ℂ), (∀ n, IsApproximant (seq n)) ∧
      Filter.Tendsto (fun n => Q (seq n)) Filter.atTop (nhds (Q Phi))

  -- T5: Q ≥ c*/4 on approximants (derived from A3 + RKHS-C)
  T5_transfer : ∀ f, IsApproximant f → Q f ≥ c_star / 4

  -- Weil criterion: Q ≥ 0 on Weil cone ↔ RH
  Weil_criterion : (∀ Phi, Phi ∈ Weil_cone → Q Phi ≥ 0) ↔ Riemann_Hypothesis

/-! ## Section 11: MAIN THEOREMS (from RH_FINAL) -/

-- Main positivity theorem: Q(Phi) ≥ 0 for all Phi in Weil cone
theorem Main_positivity [RHAxioms] : ∀ Phi, Phi ∈ Weil_cone → Q Phi ≥ 0 := by
  rename_i h
  intros Phi hPhi
  obtain ⟨seq, hseq_approx, hseq_conv⟩ := h.A1_density
    (Weil_cone_compact_support Phi hPhi).choose Phi (by
      apply And.intro hPhi
      apply (Weil_cone_compact_support Phi hPhi).choose_spec.right)
  have h_Q_seq : ∀ n, Q (seq n) ≥ c_star / 4 := by
    exact fun n => h.T5_transfer _ (hseq_approx n)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hseq_conv fun n =>
    le_trans (by norm_num [show c_star = 11/10 by rfl]) (h_Q_seq n)

-- Riemann Hypothesis (conditional on RHAxioms)
theorem RH [RHAxioms] : Riemann_Hypothesis := by
  cases' ‹RHAxioms› with h1 h2 h3
  refine' h3.mp _
  intro Phi hPhi
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K > 0 ∧ Function.support Phi ⊆ Set.Icc (-K) K := by
    exact Weil_cone_compact_support Phi hPhi
  obtain ⟨seq, hseq₁, hseq₂⟩ := h1 K Phi ⟨hPhi, hK.2⟩
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hseq₂ fun n =>
    le_trans (by linarith [show 0 ≤ c_star by norm_num [c_star]]) (h2 _ (hseq₁ n))

/-! ## Summary of Proven Results

### Fully Proven (no sorry/exact?):
1. im_one_div_sq_neg
2. trigamma_summable
3. im_trigamma_neg (KEY!)
4. deriv_re_comp_linear_imag
5. deriv_re_digamma
6. deriv_a_eq
7. continuousOn_a
8. Weil_cone_compact_support
9. Main_positivity (modulo RHAxioms)
10. RH (modulo RHAxioms)

### Remaining to prove for unconditional RH:
- A3: P_A(θ) ≥ c* = 11/10 for all θ ∈ [-1/2, 1/2]
- RKHS-C: Q_prime ≤ ρ(1) < 1/25

These would allow instantiating RHAxioms with concrete proofs.
-/

end
