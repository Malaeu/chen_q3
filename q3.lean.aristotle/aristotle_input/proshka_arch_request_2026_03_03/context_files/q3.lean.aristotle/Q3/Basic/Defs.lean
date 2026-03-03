/-
Q3 Formalization: Core Definitions
==================================

This file contains the fundamental definitions for the Q3 proof of RH.
All other modules import this file.

References:
- Q3 Paper: Chen et al. "A Spectral Approach to the Riemann Hypothesis"
- Weil (1952): "Sur les 'formules explicites' de la théorie des nombres premiers"
- Guinand (1948): "A summation formula in the theory of prime numbers"
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Pointwise
open scoped ComplexConjugate
open MeasureTheory

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

namespace Q3

/-! ## Prime Nodes -/

/-- Prime spectral coordinate: ξ_n = log(n)/(2π) -/
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

/-- Node set for compact K: all ξ_n in [-K, K] -/
def Nodes (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

/-! ## Prime Weights -/

/-- Q-functional weight (doubled for even functions): w_Q(n) = 2·Λ(n)/√n -/
def w_Q (n : ℕ) : ℝ := 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- RKHS operator weight (undoubled): w_RKHS(n) = Λ(n)/√n -/
def w_RKHS (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- Maximum weight: sup_n w_RKHS(n) = 2/e ≈ 0.7358 -/
def w_max : ℝ := 2 / Real.exp 1

/-- ActiveNodes is alias for Nodes (for compatibility with axiom naming) -/
abbrev ActiveNodes (K : ℝ) : Set ℕ := Nodes K

/-- Sum of weights over active nodes -/
noncomputable def W_sum (K : ℝ) : ℝ := ∑' n, if n ∈ Nodes K then w_Q n else 0

/-! ## Archimedean Kernel -/

/-- Digamma function (logarithmic derivative of Gamma)
    Note: This is a simplified definition; Mathlib has Complex.Gamma but not digamma directly -/
def digamma (s : ℂ) : ℂ := deriv Complex.Gamma s / Complex.Gamma s

/-- Archimedean kernel: a(ξ) = log(π) - Re(ψ(1/4 + iπξ)) -/
def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * ξ)).re

/-- Scaled archimedean kernel: a*(ξ) = 2π·a(ξ) -/
def a_star (ξ : ℝ) : ℝ := 2 * Real.pi * a ξ

/-! ## Heat and Fejér Kernels -/

/-- Heat kernel: ρ_t(x) = (4πt)^(-1/2) · exp(-x²/(4t)) -/
def heat_kernel (t : ℝ) (x : ℝ) : ℝ :=
  if t > 0 then (4 * Real.pi * t)⁻¹ ^ (1/2 : ℝ) * Real.exp (-x^2 / (4*t)) else 0

/-- Fejér kernel (triangular): Λ_B(x) = (1 - |x|/B)₊ -/
def fejer_kernel (B : ℝ) (x : ℝ) : ℝ :=
  if B > 0 then max (1 - |x| / B) 0 else 0

/-- Fejér × Heat product -/
def fejer_heat (B t : ℝ) (x : ℝ) : ℝ := fejer_kernel B x * heat_kernel t x

/-! ## Prime Operator (Compression) -/

/-- Fejer-heat window used in the A3 Rayleigh bridge: Phi_{B,t}(xi). -/
def fejer_heat_window (B t : ℝ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)

lemma fejer_heat_window_nonneg (B t ξ : ℝ) : 0 ≤ fejer_heat_window B t ξ := by
  have h0 : 0 ≤ max (0 : ℝ) (1 - |ξ| / B) := by
    exact le_max_left _ _
  exact mul_nonneg h0 (Real.exp_nonneg _)

/-- Fourier index for i in Fin (2*M+1): maps 0..2M to -M..M. -/
def fourier_index (M : ℕ) (i : Fin (2 * M + 1)) : ℤ :=
  (i.val : ℤ) - (M : ℤ)

/-- Normalized evaluation vector v_n^{(M)} at frequency xi. -/
def prime_vec (M : ℕ) (ξ : ℝ) : Fin (2 * M + 1) → ℂ :=
  fun i =>
    ((1 / Real.sqrt (2 * M + 1 : ℝ)) : ℂ) *
      Complex.exp
        (-2 * Real.pi * Complex.I * ((fourier_index M i : ℤ) : ℂ) * (ξ : ℂ))

/-- Compression prime operator T_P^{(M)} as a rank-one sum over Nodes K. -/
noncomputable def T_P_comp (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℂ :=
  fun i j =>
    ∑ n : Nodes K,
      ((w_Q n * fejer_heat_window B t (xi_n n)) : ℂ) *
        prime_vec M (xi_n n) i * conj (prime_vec M (xi_n n) j)

/-- Real part of the compression prime operator (for real Rayleigh quotients). -/
noncomputable def T_P_comp_real (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ :=
  fun i j => (T_P_comp K B t M i j).re

/-! ## Q Functional -/

/-- Archimedean term: ∫ a*(ξ)·Φ(ξ) dξ -/
def arch_term (Φ : ℝ → ℝ) : ℝ := ∫ ξ, a_star ξ * Φ ξ

/-- Prime term: Σ w_Q(n)·Φ(ξ_n) over n ≥ 2 -/
def prime_term (Φ : ℝ → ℝ) : ℝ := ∑' n, w_Q n * Φ (xi_n n)

/-- Q functional: Q(Φ) = arch_term(Φ) - prime_term(Φ)
    This is the Guinand-Weil functional in normalized form -/
def Q (Φ : ℝ → ℝ) : ℝ := arch_term Φ - prime_term Φ

/-! ## Weil Cone -/

/-- A function is even if Φ(-x) = Φ(x) -/
def IsEven (Φ : ℝ → ℝ) : Prop := ∀ x, Φ (-x) = Φ x

/-- A function is nonnegative if Φ(x) ≥ 0 for all x -/
def IsNonneg (Φ : ℝ → ℝ) : Prop := ∀ x, 0 ≤ Φ x

/-- Weil cone: even, nonnegative, continuous functions with compact support
    Note: Continuous is required for test functions (Schwartz class, etc.) -/
def Weil_cone : Set (ℝ → ℝ) :=
  {Φ | IsEven Φ ∧ IsNonneg Φ ∧ HasCompactSupport Φ ∧ Continuous Φ}

/-- Weil cone restricted to support in [-K, K] -/
def Weil_cone_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | IsEven Φ ∧ IsNonneg Φ ∧ Function.support Φ ⊆ Set.Icc (-K) K}

/-- W_K: space for T5 transfer theorem
    This matches the paper: compactly supported continuous tests on [-K, K]. -/
def W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | Continuous Φ ∧
       Function.support Φ ⊆ Set.Ioo (-K) K ∧
       IsEven Φ ∧
       IsNonneg Φ}

/-- W_K implies Weil_cone_K (but not conversely - W_K requires continuity) -/
lemma W_K_subset_Weil_cone_K (K : ℝ) : W_K K ⊆ Weil_cone_K K := by
  intro Φ ⟨_, hsupp, heven, hnonneg⟩
  exact ⟨heven, hnonneg, Set.Subset.trans hsupp Set.Ioo_subset_Icc_self⟩

/-! ## Riemann Hypothesis -/

/-- Riemann Hypothesis: all nontrivial zeros of ζ(s) have Re(s) = 1/2 -/
def RH : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2

/-! ## Basic Lemmas -/

lemma w_RKHS_nonneg (n : ℕ) : 0 ≤ w_RKHS n := by
  unfold w_RKHS
  apply div_nonneg
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact Real.sqrt_nonneg n

lemma w_Q_nonneg (n : ℕ) : 0 ≤ w_Q n := by
  unfold w_Q
  apply div_nonneg
  · apply mul_nonneg
    · norm_num
    · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact Real.sqrt_nonneg n

/-- Key lemma: log(n)/√n ≤ 2/e for n ≥ 2 -/
lemma log_div_sqrt_le (n : ℕ) (hn : n ≥ 2) : Real.log n / Real.sqrt n ≤ 2 / Real.exp 1 := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn_nonneg : (0 : ℝ) ≤ n := le_of_lt hn_pos
  have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  rw [div_le_iff₀ h_sqrt_pos]
  -- Goal: Real.log n ≤ 2 / Real.exp 1 * √n
  -- Use: log(√n/e) ≤ √n/e - 1
  have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt n / Real.exp 1 by positivity)
  rw [Real.log_div (by positivity) (by positivity),
      Real.log_sqrt hn_nonneg, Real.log_exp] at h1
  -- h1: (1/2) * log n - 1 ≤ √n / e - 1
  -- So: (1/2) * log n ≤ √n / e
  -- So: log n ≤ 2 * √n / e = (2/e) * √n
  have h_key : Real.log n / 2 ≤ Real.sqrt n / Real.exp 1 := by linarith
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  calc Real.log n = 2 * (Real.log n / 2) := by ring
    _ ≤ 2 * (Real.sqrt n / Real.exp 1) := by linarith
    _ = 2 / Real.exp 1 * Real.sqrt n := by ring

/-- Key bound: w_RKHS(n) ≤ w_max = 2/e for all n -/
lemma w_RKHS_le_w_max (n : ℕ) : w_RKHS n ≤ w_max := by
  unfold w_RKHS w_max
  rcases le_or_gt n 1 with hn | hn
  · interval_cases n <;> simp [ArithmeticFunction.vonMangoldt] <;> positivity
  · have h_log_bound : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
    calc ArithmeticFunction.vonMangoldt n / Real.sqrt n
        ≤ Real.log n / Real.sqrt n := by gcongr
      _ ≤ 2 / Real.exp 1 := log_div_sqrt_le n hn

/-- w_max < 1 (strict contraction possible) -/
lemma w_max_lt_one : w_max < 1 := by
  unfold w_max
  rw [div_lt_one (Real.exp_pos _)]
  have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  linarith

/-! ## Prime Vector Bounds -/

lemma prime_vec_norm (M : ℕ) (ξ : ℝ) (i : Fin (2 * M + 1)) :
    ‖prime_vec M ξ i‖ = 1 / Real.sqrt (2 * M + 1 : ℝ) := by
  simp [prime_vec, Complex.norm_exp]

lemma prime_vec_mul_conj_norm (M : ℕ) (ξ : ℝ)
    (i j : Fin (2 * M + 1)) :
    ‖prime_vec M ξ i * conj (prime_vec M ξ j)‖ =
      (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
  calc
    ‖prime_vec M ξ i * conj (prime_vec M ξ j)‖
        = ‖prime_vec M ξ i‖ * ‖conj (prime_vec M ξ j)‖ := by
            simp
    _ = ‖prime_vec M ξ i‖ * ‖prime_vec M ξ j‖ := by simp
    _ = (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
            simp [prime_vec_norm, pow_two, mul_comm]

lemma prime_vec_norm_sq_sum (M : ℕ) (ξ : ℝ) :
    (∑ i : Fin (2 * M + 1), ‖prime_vec M ξ i‖^2) = 1 := by
  have hconst :
      ∀ i : Fin (2 * M + 1),
        ‖prime_vec M ξ i‖^2 = (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
    intro i
    simp [prime_vec, Complex.norm_exp]
  classical
  calc
    (∑ i : Fin (2 * M + 1), ‖prime_vec M ξ i‖^2)
        = ∑ i : Fin (2 * M + 1), (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
            simp [hconst]
    _ = (2 * M + 1) * (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
            simp
    _ = 1 := by
            have hpos : (0 : ℝ) < (2 * M + 1 : ℝ) := by positivity
            have hsqrt :
                (Real.sqrt (2 * M + 1 : ℝ))^2 = (2 * M + 1 : ℝ) := by
              simpa [pow_two] using
                (Real.sq_sqrt (show 0 ≤ (2 * M + 1 : ℝ) by positivity))
            calc
              (2 * M + 1) * (1 / Real.sqrt (2 * M + 1 : ℝ))^2
                  = (2 * M + 1) * (1 / (Real.sqrt (2 * M + 1 : ℝ))^2) := by
                      simp [pow_two, mul_comm]
              _ = (2 * M + 1) * (1 / (2 * M + 1 : ℝ)) := by simp [hsqrt]
              _ = 1 := by field_simp [hpos.ne']

/-! ## RKHS Technical Definitions -/

/-- Maximum node index: N_K = ⌊exp(2πK)⌋
    This bounds the number of nodes in [-K, K] -/
def N_K (K : ℝ) : ℕ := Nat.floor (Real.exp (2 * Real.pi * K))

/-- Node separation: δ_K = 1/(2π·(N_K+1))
    Minimum spacing between spectral coordinates of nodes -/
def delta_K (K : ℝ) : ℝ :=
  1 / (2 * Real.pi * (N_K K + 1))

/-- Heat parameter minimum for contraction -/
def t_min (K η : ℝ) : ℝ :=
  (delta_K K)^2 / (4 * Real.log ((2 + η) / η))

/-- Off-diagonal geometric series bound -/
def S_K (K t : ℝ) : ℝ :=
  2 * Real.exp (-(delta_K K)^2 / (4 * t)) / (1 - Real.exp (-(delta_K K)^2 / (4 * t)))

end Q3

end
