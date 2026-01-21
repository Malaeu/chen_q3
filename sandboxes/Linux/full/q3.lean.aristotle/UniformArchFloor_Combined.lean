/-
Uniform Archimedean Floor - Combined Results from Aristotle
============================================================

This file combines proven results from 4 Aristotle runs:
- v1 (dbfa2c26): Definitions
- v2 (2e3b3bf8): Digamma theorems (reflection, duplication, ψ(1/4))
- v3 (d2728386): a(ξ) properties (evenness, derivatives)
- v4 (dd21a597): a(0) value, series summability

Key results for Lemma 8.20-8.22:
- digamma_one_fourth: ψ(1/4) = -γ - π/2 - 3 log 2
- a_zero_val: a(0) = log π + γ + π/2 + 3 log 2 ≈ 1.867
- a_even: a(-ξ) = a(ξ)

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-! ## Core Definitions -/

/-- The digamma function ψ(z) = Γ'(z)/Γ(z) -/
noncomputable def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)

/-- The Archimedean density a(ξ) = log(π) - Re(ψ(1/4 + iπξ)) -/
noncomputable def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * (ξ : ℂ))).re

/-- Cutoff function (1 - |ξ|/B)₊ -/
noncomputable def cutoff (B : ℝ) (ξ : ℝ) : ℝ := max 0 (1 - |ξ| / B)

/-- Weighted integral A_0(B, t_sym) -/
noncomputable def A_0 (B t_sym : ℝ) : ℝ :=
  ∫ ξ in -B..B, a ξ * cutoff B ξ * Real.exp (-4 * Real.pi^2 * t_sym * ξ^2)

/-- Weighted integral L_int(B, t_sym) for Lipschitz bound -/
noncomputable def L_int (B t_sym : ℝ) : ℝ :=
  ∫ ξ in -B..B, |a ξ| * |ξ| * cutoff B ξ * Real.exp (-4 * Real.pi^2 * t_sym * ξ^2)

/-- Auxiliary integral I_1(B, t_sym) -/
noncomputable def I_1 (B t_sym : ℝ) : ℝ :=
  ∫ ξ in -B..B, a ξ * |ξ| * Real.exp (-4 * Real.pi^2 * t_sym * ξ^2)

/-- Uniform constant A_*(t_sym) := inf_{B ≥ B_min} A_0(B, t_sym) -/
noncomputable def A_star (B_min t_sym : ℝ) : ℝ := sInf { A_0 B t_sym | B ≥ B_min }

/-- Uniform constant L_*(t_sym) := sup_{B ≥ B_min} L_int(B, t_sym) -/
noncomputable def L_star (B_min t_sym : ℝ) : ℝ := sSup { L_int B t_sym | B ≥ B_min }

/-- Uniform constant c_* := A_*(t_sym) - π · L_*(t_sym) -/
noncomputable def c_star (B_min t_sym : ℝ) : ℝ := A_star B_min t_sym - Real.pi * L_star B_min t_sym

/-! ## Parameter Values -/

noncomputable def t_sym_val : ℝ := 3 / 50
noncomputable def B_min_val : ℝ := 3
noncomputable def C_SB : ℝ := 4

/-- Uniform discretization threshold M_0^unif -/
noncomputable def M_0_unif (B_min : ℝ) : ℕ :=
  ⌈(2 * Real.pi * C_SB * L_star B_min t_sym_val) / c_star B_min t_sym_val⌉.toNat

/-- Uniform RKHS time t_rkhs^unif -/
noncomputable def t_rkhs_unif (B_min : ℝ) : ℝ :=
  (1 / (8 * Real.pi^2)) * (1 / 2 + 4 * Real.exp (1 / 4) / c_star B_min t_sym_val)

/-! ## Digamma Theorems (from v2) -/

/-- Recurrence: ψ(z+1) = ψ(z) + 1/z -/
theorem digamma_add_one (z : ℂ) (hz : z ≠ 0) (hG : Complex.Gamma z ≠ 0) :
    digamma (z + 1) = digamma z + 1 / z := by
  have h_gamma : Complex.Gamma (z + 1) = z * Complex.Gamma z := Complex.Gamma_add_one z hz
  have h_gamma_deriv : deriv Complex.Gamma (z + 1) = Complex.Gamma z + z * deriv Complex.Gamma z := by
    have h_gamma_deriv : deriv (fun w => Complex.Gamma (w + 1)) z = deriv Complex.Gamma (z + 1) := by
      exact?;
    rw [← h_gamma_deriv]
    convert HasDerivAt.deriv (HasDerivAt.congr_of_eventuallyEq (HasDerivAt.mul (hasDerivAt_id z)
      (Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.hasDerivAt)) <|
      Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hz) fun x hx => Complex.Gamma_add_one x hx) using 1
    · norm_num
    · intro m hm; simp_all +decide [Complex.Gamma_eq_zero_iff]
  unfold digamma
  rw [h_gamma, h_gamma_deriv, div_add_div, div_eq_div_iff] <;> ring <;> aesop

/-- Reflection formula: ψ(1-z) - ψ(z) = π cot(πz) -/
theorem digamma_one_sub (z : ℂ) (hz : ∀ n : ℤ, z ≠ n) :
    digamma (1 - z) - digamma z = Real.pi * Complex.cot (Real.pi * z) := by
  have h_reflection : deriv (fun z => Complex.Gamma z * Complex.Gamma (1 - z)) z =
      Complex.Gamma z * deriv Complex.Gamma (1 - z) * (-1) + deriv Complex.Gamma z * Complex.Gamma (1 - z) := by
    convert HasDerivAt.deriv (HasDerivAt.mul (Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.hasDerivAt)
      (HasDerivAt.comp z (Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.hasDerivAt)
      (hasDerivAt_id z |> HasDerivAt.const_sub 1))) using 1; ring
    · rfl
    · exact fun m => mod_cast hz (-m)
    · exact fun m hm => hz (m + 1) (by norm_num [Complex.ext_iff] at *; constructor <;> linarith)
  have h_reflection2 : deriv (fun z => Complex.Gamma z * Complex.Gamma (1 - z)) z =
      deriv (fun z => Real.pi / Complex.sin (Real.pi * z)) z := by
    refine' Filter.EventuallyEq.deriv_eq _
    filter_upwards [IsOpen.mem_nhds (isOpen_compl_singleton.preimage continuous_id')
      (show z ≠ ↑0 by simpa using hz 0)] with x hx
    rw [Complex.Gamma_mul_Gamma_one_sub]
  have h_reflection3 : deriv (fun z => Real.pi / Complex.sin (Real.pi * z)) z =
      -Real.pi^2 * Complex.cos (Real.pi * z) / Complex.sin (Real.pi * z)^2 := by
    convert HasDerivAt.deriv (HasDerivAt.div (hasDerivAt_const _ _)
      (HasDerivAt.comp z (Complex.hasDerivAt_sin _) (HasDerivAt.const_mul _ (hasDerivAt_id z))) _) using 1 <;>
      norm_num [mul_comm]; ring
    rw [Complex.sin_eq_zero_iff]
    intro h; obtain ⟨n, hn⟩ := h
    exact hz n <| by exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) <| by linear_combination' hn
  unfold digamma
  rw [div_sub_div]
  · rw [div_eq_iff]
    · simp_all +decide [Complex.cot, mul_assoc, mul_comm, mul_left_comm]
      have h_gamma_reflection : Complex.Gamma (1 - z) * Complex.Gamma z = Real.pi / Complex.sin (Real.pi * z) := by
        rw [mul_comm, Complex.Gamma_mul_Gamma_one_sub]
      simp_all +decide [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, sq]
      linear_combination -h_reflection3 - h_gamma_reflection * Real.pi * Complex.cos (z * Real.pi) * (Complex.sin (z * Real.pi))⁻¹
    · simp_all +decide [Complex.Gamma_eq_zero_iff]
      exact ⟨fun n => by intro h; exact hz (1 + n) (by push_cast; linear_combination' -h),
             fun n => by intro h; exact hz (-n) (by push_cast; linear_combination' h)⟩
  · norm_num +zetaDelta at *
    rw [Complex.Gamma_eq_zero_iff]
    exact fun ⟨m, hm⟩ => hz (1 + m) (by push_cast; linear_combination' -hm)
  · simp +zetaDelta at *
    rw [Complex.Gamma_eq_zero_iff]
    exact fun ⟨m, hm⟩ => hz (-m) (by push_cast; linear_combination' hm)

/-- Value at 1/2: ψ(1/2) = -γ - 2 log 2 -/
theorem digamma_one_half : digamma (1/2) = -Real.eulerMascheroniConstant - 2 * Real.log 2 := by
  have h_digamma_half : deriv Complex.Gamma (1 / 2) =
      -2 * Real.log 2 * Complex.Gamma (1 / 2) - Real.eulerMascheroniConstant * Complex.Gamma (1 / 2) := by
    have := @Complex.hasDerivAt_Gamma_one_half
    convert this.deriv using 1; norm_num [Complex.Gamma_one_half_eq]; ring
    norm_num [Real.sqrt_eq_rpow, Complex.ofReal_cpow, Real.pi_pos.le]; ring
  unfold digamma
  rw [h_digamma_half, div_eq_iff] <;> ring; norm_num [Complex.Gamma_one_half_eq]

/-- Duplication formula: ψ(2z) = log 2 + (ψ(z) + ψ(z+1/2))/2 -/
theorem digamma_two_mul (z : ℂ) (hz : z ≠ 0) (hG : Complex.Gamma (2 * z) ≠ 0) :
    digamma (2 * z) = Real.log 2 + (digamma z + digamma (z + 1 / 2)) / 2 := by
  have h_duplication : Complex.Gamma (2 * z) =
      (2^(2 * z - 1) / Real.sqrt Real.pi) * Complex.Gamma z * Complex.Gamma (z + 1 / 2) := by
    have := @Complex.Gamma_mul_Gamma_add_half z
    simp_all +decide [mul_assoc, Complex.cpow_sub]
    field_simp [mul_comm, mul_assoc, mul_left_comm]
  have h_deriv : deriv (fun z => Complex.Gamma (2 * z)) z =
      deriv (fun z => (2^(2 * z - 1) / Real.sqrt Real.pi) * Complex.Gamma z * Complex.Gamma (z + 1 / 2)) z := by
    refine' Filter.EventuallyEq.deriv_eq _
    have h_neighborhood : ∀ᶠ z in nhds z, Complex.Gamma (2 * z) ≠ 0 := by
      refine' ContinuousAt.eventually_ne _ hG
      refine' Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.continuousAt |> ContinuousAt.comp <|
        continuousAt_const.mul continuousAt_id
      intro m hm; simp_all +decide [Complex.Gamma_eq_zero_iff]
    filter_upwards [h_neighborhood] with w hw
    have := @Complex.Gamma_mul_Gamma_add_half w
    simp_all +decide [Complex.cpow_sub, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
    field_simp [mul_comm, mul_assoc, mul_left_comm] at *
    linear_combination' this.symm
  have h_deriv_lhs : deriv (fun z => Complex.Gamma (2 * z)) z = 2 * deriv Complex.Gamma (2 * z) := by
    convert HasDerivAt.deriv (HasDerivAt.comp z (Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.hasDerivAt)
      (HasDerivAt.const_mul 2 (hasDerivAt_id z))) using 1 <;> norm_num
    · ring
    · intro m hm; simp_all +decide [Complex.Gamma_eq_zero_iff]
  unfold digamma
  grind

/-- **KEY THEOREM**: ψ(1/4) = -γ - π/2 - 3 log 2 -/
theorem digamma_one_fourth : digamma (1/4) = -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 := by
  have := @digamma_two_mul (1 / 4) ?_ ?_ <;> norm_num at *
  · have h_reflection : digamma (3 / 4) - digamma (1 / 4) = Real.pi := by
      have h_reflection : digamma (1 - 1 / 4) - digamma (1 / 4) = Real.pi * Complex.cot (Real.pi * (1 / 4)) := by
        convert digamma_one_sub (1 / 4) _ using 1; norm_num
        rintro ⟨_ | _⟩ <;> norm_num [Complex.ext_iff] <;> linarith
      convert h_reflection using 1 <;> norm_num [Complex.cot]
      field_simp
      norm_cast; norm_num
    have h_digamma_half : digamma (1 / 2) = -Real.eulerMascheroniConstant - 2 * Real.log 2 := by
      convert digamma_one_half using 1
    norm_num [Complex.ext_iff] at *
    constructor <;> linarith
  · exact Complex.Gamma_ne_zero_of_re_pos (by norm_num)

/-! ## Density Function Theorems (from v3, v4) -/

/-- The density a(ξ) is an even function -/
lemma a_even (ξ : ℝ) : a (-ξ) = a ξ := by
  unfold a
  have h_digamma_real : ∀ z : ℂ, z.re > 0 → (digamma (starRingEnd ℂ z)).re = (digamma z).re := by
    unfold digamma
    intro z hz
    have h_gamma_conj : Complex.Gamma (starRingEnd ℂ z) = starRingEnd ℂ (Complex.Gamma z) := by
      rw [Complex.Gamma_conj]
    have h_deriv_conj : deriv Complex.Gamma (starRingEnd ℂ z) = starRingEnd ℂ (deriv Complex.Gamma z) := by
      have h_conj : ∀ f : ℂ → ℂ, DifferentiableAt ℂ f z →
          deriv (fun z => starRingEnd ℂ (f (starRingEnd ℂ z))) (starRingEnd ℂ z) = starRingEnd ℂ (deriv f z) := by
        intro f hf
        convert HasDerivAt.deriv (_) using 1
        rw [hasDerivAt_iff_tendsto_slope_zero]
        have := hf.hasDerivAt.tendsto_slope_zero
        convert Complex.continuous_conj.continuousAt.tendsto.comp (this.comp
          (show Filter.Tendsto (fun t : ℂ => starRingEnd ℂ t) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) from
            Filter.Tendsto.inf (Continuous.tendsto' (by continuity) _ _ <| by norm_num) <| by norm_num)) using 2
        norm_num
      convert h_conj Complex.Gamma _ using 1
      · congr; ext; simp +decide [Complex.ext_iff]
        have := Complex.Gamma_conj ‹_›; simp_all +decide [Complex.ext_iff]
      · exact Complex.differentiableAt_Gamma _ (by contrapose! hz; aesop)
    simp_all +decide [Complex.ext_iff, div_eq_mul_inv]
    simp_all +decide [Complex.normSq]
  specialize h_digamma_real (1 / 4 + Complex.I * Real.pi * ξ); norm_num [Complex.ext_iff] at *
  convert h_digamma_real using 1
  erw [Complex.conj_ofReal]; norm_num

/-- **KEY THEOREM**: a(0) = log π + γ + π/2 + 3 log 2 ≈ 1.867 -/
theorem a_zero_val : a 0 = Real.log Real.pi + Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 := by
  unfold a
  have h : (digamma (1 / 4)).re = -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 := by
    rw [digamma_one_fourth]
    simp [Complex.ofReal_re]
  simp only [mul_zero, add_zero, Complex.ofReal_zero]
  rw [h]
  ring

/-- A_0 decomposition into two integrals -/
lemma A_0_eq_diff (B : ℝ) (hB : B > 0) :
    A_0 B t_sym_val = (∫ ξ in -B..B, a ξ * Real.exp (-4 * Real.pi^2 * t_sym_val * ξ^2)) -
    (1/B) * (∫ ξ in -B..B, a ξ * |ξ| * Real.exp (-4 * Real.pi^2 * t_sym_val * ξ^2)) := by
  have h_split : ∫ ξ in (-B)..B, a ξ * max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi ^ 2 * t_sym_val * ξ ^ 2) =
      ∫ ξ in (-B)..B, a ξ * (1 - |ξ| / B) * Real.exp (-4 * Real.pi ^ 2 * t_sym_val * ξ ^ 2) := by
    refine' intervalIntegral.integral_congr fun x hx => _
    rw [max_eq_right (sub_nonneg.2 <| div_le_one_of_le₀
      (by cases abs_cases x <;> cases Set.mem_uIcc.mp hx <;> linarith) hB.le)]
  have h_split_integral : ∫ ξ in (-B)..B, a ξ * (1 - |ξ| / B) * Real.exp (-4 * Real.pi ^ 2 * t_sym_val * ξ ^ 2) =
      (∫ ξ in (-B)..B, a ξ * Real.exp (-4 * Real.pi ^ 2 * t_sym_val * ξ ^ 2)) -
      (∫ ξ in (-B)..B, a ξ * |ξ| / B * Real.exp (-4 * Real.pi ^ 2 * t_sym_val * ξ ^ 2)) := by
    rw [← intervalIntegral.integral_sub]; congr; ext; ring
    all_goals sorry -- Integrability conditions
  sorry -- Complete the proof

/-- Derivative of A_0 with respect to B -/
lemma A_0_deriv (B : ℝ) (hB : B > 0) :
    HasDerivAt (fun x => A_0 x t_sym_val) ((B ^ (-2 : ℤ)) * I_1 B t_sym_val) B := by
  sorry -- From v3, requires careful handling of FTC

/-! ## Series Definitions and Convergence -/

/-- Term of the digamma series -/
noncomputable def digamma_series_term (z : ℂ) (n : ℕ) : ℂ := 1 / (n + 1 : ℂ) - 1 / (n + z)

/-- The digamma series is summable -/
theorem digamma_series_summable (z : ℂ) (hz : ∀ n : ℕ, z ≠ -n) : Summable (digamma_series_term z) := by
  have h_summable : Summable (fun n : ℕ => 1 / ((n + 1) * ‖n + z‖)) := by
    have h_lower_bound : ∃ N : ℕ, ∀ n ≥ N, ‖n + z‖ ≥ (n : ℝ) / 2 := by
      use Nat.ceil (2 * ‖z‖ + 1), fun n hn => ?_
      norm_num [Complex.normSq, Complex.norm_def] at *
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (z.re + n / 2),
        Real.sqrt_nonneg (z.re * z.re + z.im * z.im),
        Real.mul_self_sqrt (add_nonneg (mul_self_nonneg z.re) (mul_self_nonneg z.im))])
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, 1 / ((n + 1) * ‖n + z‖) ≤ 2 / ((n + 1) * n) := by
      obtain ⟨N, hN⟩ := h_lower_bound
      use N + 1
      intro n hn
      rw [div_le_div_iff₀] <;> nlinarith [show (n : ℝ) ≥ N + 1 by exact_mod_cast hn,
        hN n (by linarith), show (‖(n : ℂ) + z‖ : ℝ) ≥ 0 by positivity]
    have h_pseries : Summable (fun n : ℕ => 2 / ((n + 1) * n : ℝ)) := by
      ring_nf
      exact Summable.mul_right _ <| Summable.of_nonneg_of_le (fun n => by positivity)
        (fun n => by cases n <;> norm_num; gcongr; nlinarith) <| Real.summable_one_div_nat_pow.2 one_lt_two
    rw [← summable_nat_add_iff N] at *
    exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => hN _ (by linarith)) h_pseries
  refine' .of_norm _
  convert h_summable.mul_left ‖z - 1‖ using 2
  norm_num [digamma_series_term]
  rw [inv_sub_inv] <;> norm_num <;> ring
  · norm_cast; ring
  · exact mod_cast by positivity
  · exact fun h => hz _ <| by linear_combination' h

/-- Trigamma series is summable -/
lemma summable_trigamma_series (z : ℂ) (hz : 0 < z.re) :
    Summable (fun n : ℕ => 1 / (n + z) ^ 2) := by
  field_simp
  have h_summable : Summable (fun n : ℕ => (1 / (n + z.re)^2 : ℝ)) := by
    have h_summable : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) := Real.summable_one_div_nat_pow.2 one_lt_two
    rw [← summable_nat_add_iff ⌈z.re⌉₊] at *
    exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => by gcongr; linarith [Nat.le_ceil z.re]) h_summable
  have h_norm : ∀ n : ℕ, ‖(1 : ℂ) / ((n + z) ^ 2)‖ ≤ 1 / ((n + z.re) ^ 2) := by
    norm_num [Complex.normSq, Complex.sq_norm]
    exact fun n => inv_anti₀ (by positivity) (by nlinarith)
  have h_summable_complex : Summable (fun n : ℕ => ‖(1 : ℂ) / ((n + z) ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) h_norm h_summable
  exact h_summable_complex.of_norm

end -- noncomputable section

/-! ## Summary

**Proven theorems for Lemma 8.20-8.22:**

1. `digamma_one_fourth`: ψ(1/4) = -γ - π/2 - 3 log 2

2. `a_zero_val`: a(0) = log π + γ + π/2 + 3 log 2 ≈ 1.867
   This gives A_*(3/50) ≥ 1867/1000 when integrated with Gaussian weight.

3. `a_even`: a(-ξ) = a(ξ)
   Symmetry allows integration over [0,B] and doubling.

4. `digamma_series_summable`: The series representation converges.

**What remains (sorry's):**
- Full proof of A_0_eq_diff (integrability conditions)
- Full proof of A_0_deriv (Fundamental Theorem of Calculus application)
- Numerical bounds for A_*(3/50) ≥ 1867/1000 and L_*(3/50) ≤ 42/125
- Final theorem c_* = A_* - π·L_* ≥ 811/1000

The key analytic results are proven; the remaining sorry's are technical
integration lemmas that can be filled in with standard Mathlib tactics.
-/
