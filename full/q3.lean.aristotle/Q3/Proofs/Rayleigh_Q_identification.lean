/-
Rayleigh-Q Identification (Theorem 3.3)

This module proves that the Rayleigh quotient at basis0 equals Q functional.

**Correct formula:**
  Q(Φ) = RQ(Toeplitz[P_A], basis0) - (2M+1) · RQ(T_P_comp, basis0)

Where:
- RQ(Toeplitz[P_A], basis0) = ∫ P_A dθ = arch_term(Φ)
- (2M+1) · RQ(T_P_comp, basis0) = Σ w_Q(n)·Φ(ξ_n) = prime_term(Φ)

Note: The naive formula `(2M+1) · RQ(Toeplitz - T_P_comp, basis0)` is WRONG because
it multiplies both arch and prime parts by (2M+1). Only the prime part needs rescaling
due to the 1/√(2M+1) normalization in prime_vec.

Integration: change-durch: claude-code 2026-01-17 Rayleigh_Q_identification
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.A3_Floor_Main

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate
open MeasureTheory Set

-- PERFORMANCE FIX: integral_P_A_eq_arch_term requires extensive typeclass resolution
-- for interval integrals and HasSum. Using very high heartbeat limit.
-- Performance tuning: rewritten proofs to avoid expensive simpa unification
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 50000

noncomputable section

namespace Q3

noncomputable def T_P_comp_shift (K B t tau : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℂ :=
  fun i j =>
    ∑ n : Nodes K,
      ((w_Q n * phi_shift B t tau (xi_n n)) : ℂ) *
        prime_vec M (xi_n n) i * conj (prime_vec M (xi_n n) j)

noncomputable def T_P_comp_real_shift (K B t tau : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ :=
  fun i j => (T_P_comp_shift K B t tau M i j).re

end Q3

namespace Q3.Proofs.RayleighQId

/-! ## Toeplitz Diagonal Lemmas -/

/-- Diagonal entry of Toeplitz matrix equals integral of symbol.
    ToeplitzEntry P i i = ∫_{-1/2}^{1/2} P(θ) dθ because exp(2πi·0·θ) = 1. -/
lemma ToeplitzEntry_diag (P : ℝ → ℝ) (i : ℕ) :
    RayleighFourier.ToeplitzEntry P i i = ∫ θ in (-1/2 : ℝ)..(1/2), (P θ : ℂ) := by
  simp only [RayleighFourier.ToeplitzEntry]
  congr 1
  ext θ
  simp [Complex.exp_zero]

/-- Real part of diagonal equals integral (for real-valued P). -/
lemma ToeplitzEntry_diag_re (P : ℝ → ℝ) (_hP : Continuous P) (i : ℕ) :
    (RayleighFourier.ToeplitzEntry P i i).re = ∫ θ in (-1/2 : ℝ)..(1/2), P θ := by
  rw [ToeplitzEntry_diag]
  rw [intervalIntegral.integral_ofReal]
  simp

/-- ToeplitzMatrix_Fourier_real diagonal at i0. -/
lemma ToeplitzMatrix_Fourier_real_diag (M : ℕ) (P : ℝ → ℝ) (hP : Continuous P) :
    RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) P (i0 M) (i0 M) =
      ∫ θ in (-1/2 : ℝ)..(1/2), P θ := by
  simp only [RayleighFourier.ToeplitzMatrix_Fourier_real]
  exact ToeplitzEntry_diag_re P hP (i0 M).val

/-! ## T_P_comp Diagonal Lemmas -/

/-- At i0, the Fourier index is 0. -/
lemma fourier_index_i0 (M : ℕ) : Q3.fourier_index M (i0 M) = 0 := by
  simp [Q3.fourier_index, i0]

/-- At i0, prime_vec evaluates to 1/√(2M+1).
    This is because exp(-2πi·0·ξ) = 1. -/
lemma prime_vec_i0 (M : ℕ) (ξ : ℝ) :
    Q3.prime_vec M ξ (i0 M) = (1 / Real.sqrt (2 * M + 1 : ℝ) : ℂ) := by
  unfold Q3.prime_vec
  simp only [fourier_index_i0, Int.cast_zero, mul_zero]
  simp only [zero_mul, Complex.exp_zero, mul_one]

/-- The norm squared of prime_vec at i0 equals 1/(2M+1). -/
lemma prime_vec_i0_norm_sq (M : ℕ) (ξ : ℝ) (_hM : 0 < 2 * M + 1) :
    Q3.prime_vec M ξ (i0 M) * conj (Q3.prime_vec M ξ (i0 M)) =
      (1 / (2 * M + 1 : ℝ) : ℂ) := by
  rw [prime_vec_i0]
  -- prime_vec at i0 is (1/√(2M+1) : ℂ), which is real
  have h_N_pos : (0 : ℝ) < 2 * M + 1 := by linarith
  have h_sqrt_pos : 0 < Real.sqrt (2 * M + 1 : ℝ) := Real.sqrt_pos.mpr h_N_pos
  have h_sqrt_ne : (Real.sqrt (2 * M + 1 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact h_sqrt_pos.ne'
  -- Goal: (1/√N : ℂ) * conj(1/√N : ℂ) = (1/N : ℂ)
  -- Use: conj(1/z) = 1/conj(z) and conj(r : ℂ) = r for r : ℝ
  rw [map_div₀, map_one, Complex.conj_ofReal]
  -- Now: 1/√N * (1/√N) = 1/N
  rw [div_mul_div_comm, one_mul, ← sq]
  congr 1
  rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt h_N_pos.le]

/-- T_P_comp_real diagonal at i0.
    T_P_comp_real[i0,i0] = (1/(2M+1)) * Σ_n w_Q(n) * φ(ξ_n).
    This follows from prime_vec(i0) = 1/√(2M+1), so |prime_vec(i0)|² = 1/(2M+1). -/
lemma T_P_comp_real_diag (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] (hM : 0 < 2 * M + 1) :
    Q3.T_P_comp_real K B t M (i0 M) (i0 M) =
      (1 / (2 * M + 1 : ℝ)) *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  simp only [Q3.T_P_comp_real, Q3.T_P_comp]
  -- Normalize: (a : ℂ) * (b : ℂ) vs ((a * b) : ℂ)
  simp only [← Complex.ofReal_mul]
  -- Rewrite using prime_vec_i0_norm_sq: |prime_vec(i0)|² = 1/(2M+1)
  have h_factor : ∀ n : Q3.Nodes K,
      ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) : ℝ) : ℂ) *
        Q3.prime_vec M (Q3.xi_n n) (i0 M) * conj (Q3.prime_vec M (Q3.xi_n n) (i0 M)) =
      ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) : ℝ) : ℂ) * (1 / (2 * M + 1 : ℝ)) := by
    intro n
    rw [mul_assoc, prime_vec_i0_norm_sq M (Q3.xi_n n) hM]
  -- Rewrite each summand using h_factor
  have h_sum_eq : (∑ n : Q3.Nodes K,
        ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) : ℝ) : ℂ) *
          Q3.prime_vec M (Q3.xi_n n) (i0 M) * conj (Q3.prime_vec M (Q3.xi_n n) (i0 M))) =
      ∑ n : Q3.Nodes K, ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) : ℝ) : ℂ) *
        (1 / (2 * M + 1 : ℝ)) := by
    congr 1
    ext n
    exact h_factor n
  rw [h_sum_eq, ← Finset.sum_mul]
  -- Both sum and 1/(2M+1) are real, so (sum * (1/(2M+1))).re = sum_real * (1/(2M+1))
  -- ∑ (↑r_n : ℂ) = ↑(∑ r_n) by Complex.ofReal_sum.symm
  rw [← Complex.ofReal_sum]
  -- 1 / ↑(2*M+1) = ↑(1/(2*M+1)) by Complex.ofReal_div
  rw [one_div, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-! ## Periodization and Rayleigh-Q Identification -/

/-! ### Compact support lemmas -/

/-- The window w has compact support: w(ξ) = 0 when |ξ| > B. -/
lemma w_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : w B t ξ = 0 := by
  simp only [w]
  have h1 : 1 - |ξ| / B < 0 := by
    have : 1 < |ξ| / B := by
      rw [one_lt_div hB]
      exact h
    linarith
  rw [max_eq_left (le_of_lt h1)]
  ring

/-- The kernel g has compact support: g(ξ) = 0 when |ξ| > B. -/
lemma g_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : g B t ξ = 0 := by
  simp only [g, w_support B t ξ hB h, mul_zero]

lemma continuous_w (B t : ℝ) : Continuous (fun ξ => w B t ξ) := by
  unfold w
  apply Continuous.mul
  · exact continuous_const.max (continuous_const.sub (continuous_abs.div_const B))
  · exact Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))

lemma continuous_g (B t : ℝ) : Continuous (fun ξ => g B t ξ) := by
  unfold g
  have ha : Continuous (fun ξ => Q3.a ξ) := by
    have hpi : (2 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
    have heq : ∀ ξ, Q3.a ξ = (1 / (2 * Real.pi)) * Q3.a_star ξ := by
      intro ξ
      simp only [Q3.a_star]
      field_simp [hpi]
    simp_rw [heq]
    exact continuous_const.mul Q3.a_star_continuous
  exact ha.mul (continuous_w B t)

/-- w equals fejer_heat_window (same definition). -/
lemma w_eq_fejer_heat_window (B t ξ : ℝ) : w B t ξ = Q3.fejer_heat_window B t ξ := by
  simp only [w, Q3.fejer_heat_window]

/-- Key support bound: for θ ∈ [-1/2, 1/2] and |m| > ⌈B⌉ + 1, we have g(θ+m) = 0. -/
lemma g_shift_zero_of_large_m (B t θ : ℝ) (m : ℤ) (hB : 0 < B)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : (⌈B⌉ : ℤ) + 1 < |m|) : g B t (θ + m) = 0 := by
  apply g_support B t (θ + m) hB
  -- Need: B < |θ + m|
  -- From hθ: -1/2 ≤ θ ≤ 1/2
  -- From hm: |m| > ⌈B⌉ + 1 ≥ B + 1
  have h1 : (B : ℝ) + 1 ≤ |m| := by
    have : (⌈B⌉ : ℝ) + 1 < |m| := by exact_mod_cast hm
    have hceil : B ≤ ⌈B⌉ := Int.le_ceil B
    linarith
  -- |θ + m| ≥ |m| - |θ| ≥ |m| - 1/2 > B + 1 - 1/2 > B
  have hθ_abs : |θ| ≤ 1/2 := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  -- Use reverse triangle inequality: ||a| - |b|| ≤ |a - b| (Mathlib form)
  -- abs_sub_abs_le_abs_sub (m : ℝ) θ gives: ||(m:ℝ)| - |θ|| ≤ |(m:ℝ) - θ|
  -- We need for (m + θ), so apply to m and (-θ):
  -- abs_sub_abs_le_abs_sub (m : ℝ) (-θ) gives: ||(m:ℝ)| - |-θ|| ≤ |(m:ℝ) - (-θ)| = |m + θ|
  have h_abs_m : |(m : ℝ)| = |m| := by
    simp only [Int.cast_abs]
  have h_tri : (|(m : ℝ)| - |θ|) ≤ |θ + (m : ℝ)| := by
    have h1 := abs_sub_abs_le_abs_sub (m : ℝ) (-θ)
    simp only [abs_neg, sub_neg_eq_add] at h1
    -- h1 : |↑m| - |θ| ≤ |↑m + θ|, need to reorder to |θ + ↑m|
    calc |(m : ℝ)| - |θ| ≤ |(m : ℝ) + θ| := h1
      _ = |θ + (m : ℝ)| := by ring_nf
  -- Now chain the inequalities
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

/-- The tsum defining P_A is actually a finite sum over |m| ≤ ⌈B⌉ + 1. -/
lemma P_A_tsum_eq_finite_sum (B t θ : ℝ) (hB : 0 < B) (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    ∑' (m : ℤ), g B t (θ + m) =
    ∑ m ∈ Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1), g B t (θ + m) := by
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  -- m ∉ [-⌈B⌉-1, ⌈B⌉+1] means |m| > ⌈B⌉ + 1
  -- ⌈B⌉ + 1 ≥ 1 since B > 0 implies ⌈B⌉ ≥ 0
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

/-- Both sides of the periodization identity equal 2π · ∫ g.
    This lemma establishes the connection through definitional unfolding. -/
lemma arch_term_eq_two_pi_integral_g (B t : ℝ) :
    Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) =
      2 * Real.pi * ∫ ξ, Q3.a ξ * w B t ξ := by
  simp only [Q3.arch_term]
  -- Now goal: ∫ ξ, Q3.a_star ξ * Q3.fejer_heat_window B t ξ = 2 * π * ∫ ξ, Q3.a ξ * w B t ξ
  -- Since w = fejer_heat_window by definition:
  have hw : ∀ ξ, w B t ξ = Q3.fejer_heat_window B t ξ := w_eq_fejer_heat_window B t
  simp_rw [hw]
  -- Now both sides have fejer_heat_window
  -- arch_term = ∫ a_star · Φ = ∫ (2π·a) · Φ = 2π · ∫ a · Φ
  have h : ∀ ξ, Q3.a_star ξ * Q3.fejer_heat_window B t ξ =
      2 * Real.pi * (Q3.a ξ * Q3.fejer_heat_window B t ξ) := by
    intro ξ
    simp only [Q3.a_star]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_mul_left]

/-- Periodization theorem: integral of P_A over one period equals arch_term.

    **Mathematical content:**
    Since w has compact support in [-B, B], the periodization sum
    ∑'_m g(θ+m) is actually finite (only |m| ≤ ⌈B⌉+1 contribute).

    Then: ∫_{-1/2}^{1/2} P_A dθ
        = 2π · ∑_m ∫_{-1/2}^{1/2} g(θ+m) dθ
        = 2π · ∑_m ∫_{m-1/2}^{m+1/2} g(ξ) dξ    (substitution ξ = θ+m)
        = 2π · ∫_ℝ g(ξ) dξ                       (disjoint intervals)
        = ∫_ℝ a_star(ξ) · w(ξ) dξ               (a_star = 2π·a, g = a·w)
        = arch_term(w)

    **Key identity used:** Both sides equal 2π · ∫_ℝ g dξ where g = a·w.

    **Proof status:** Completed using finite-support truncation and interval integrals.
    The mathematical content is standard harmonic analysis (Poisson summation formula
    for compactly supported functions). -/
theorem integral_P_A_eq_arch_term (B t : ℝ) (hB : 0 < B) :
    ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ =
      Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) := by
  classical
  /-
  Strategy: Show both sides equal 2π · ∫_ℝ g dξ where g = a · w.

  LHS = ∫_{-1/2}^{1/2} P_A dθ
      = ∫_{-1/2}^{1/2} 2π · ∑'_m g(θ+m) dθ
      = 2π · ∫_ℝ g dξ                       (periodization identity)

  RHS = arch_term(w)
      = ∫_ℝ a_star · w dξ
      = ∫_ℝ (2π·a) · w dξ
      = 2π · ∫_ℝ a·w dξ
      = 2π · ∫_ℝ g dξ
  -/
  have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
  let s : Finset ℤ := Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1)
  have hsupp : Function.support (fun ξ => g B t ξ) ⊆ Set.Icc (-B) B := by
    intro ξ hξ
    simp only [Function.mem_support, ne_eq] at hξ
    rw [Set.mem_Icc, ← abs_le]
    by_contra h_not_le
    push_neg at h_not_le
    exact hξ (g_support B t ξ hB h_not_le)
  have hcompact : HasCompactSupport (fun ξ => g B t ξ) := by
    exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hint : Integrable (fun ξ => g B t ξ) := by
    exact (continuous_g B t).integrable_of_hasCompactSupport hcompact

  have h_eq_tsum :
      EqOn (fun θ => ∑' m : ℤ, g B t (θ + m))
        (fun θ => ∑ m ∈ s, g B t (θ + m)) (Set.uIcc (-1/2 : ℝ) (1/2 : ℝ)) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by
      rwa [Set.uIcc_of_le hab] at hθ
    simpa [s] using P_A_tsum_eq_finite_sum B t θ hB hθ'

  have h_int_eq :
      ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m) =
        ∫ θ in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, g B t (θ + m) := by
    exact intervalIntegral.integral_congr h_eq_tsum

  have h_int_sum :
      ∫ θ in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, g B t (θ + m) =
        ∑ m ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + m) := by
    refine intervalIntegral.integral_finset_sum ?_
    intro m _
    have hcont : Continuous (fun θ => g B t (θ + (m : ℝ))) :=
      (continuous_g B t).comp (continuous_add_right (m : ℝ))
    exact hcont.intervalIntegrable (-1/2 : ℝ) (1/2 : ℝ)

  have hsum_base :
      HasSum (fun n : ℤ =>
          ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, g B t x)
        (∫ x, g B t x) := by
    have h := MeasureTheory.Integrable.hasSum_intervalIntegral (μ := volume)
      (f := fun x => g B t x) (y := (-1/2 : ℝ)) hint
    convert h using 2

  have hsum :
      HasSum (fun n : ℤ => ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ)))
        (∫ x, g B t x) := by
    refine (HasSum.congr_fun hsum_base ?_)
    intro n
    have hcomp :=
      intervalIntegral.integral_comp_add_right (f:=fun x => g B t x) (d:=(n : ℝ))
        (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ))
    convert hcomp using 1 <;> ring

  have hsum_eq :
      (∑' n : ℤ, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ))) =
        ∑ n ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ)) := by
    apply tsum_eq_sum
    intro n hn
    -- n ∉ s means n < -(⌈B⌉ + 1) or n > ⌈B⌉ + 1
    simp only [s, Finset.mem_Icc, not_and, not_le] at hn
    have h_large : (⌈B⌉ : ℤ) + 1 < |n| := by
      by_cases h : n ≤ -(⌈B⌉ + 1)
      · have hn_neg : n < 0 := by
          have hceil : 0 ≤ ⌈B⌉ := Int.ceil_nonneg (le_of_lt hB)
          omega
        rw [abs_of_neg hn_neg]
        omega
      · push_neg at h
        have h2 : ⌈B⌉ + 1 < n := hn (le_of_lt h)
        have hn_nonneg : 0 ≤ n := by omega
        rw [abs_of_nonneg hn_nonneg]
        exact h2
    have h_eq0 :
        EqOn (fun θ => g B t (θ + n)) (fun _ => (0 : ℝ))
          (Set.uIcc (-1/2 : ℝ) (1/2 : ℝ)) := by
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by
        rwa [Set.uIcc_of_le hab] at hθ
      simpa using g_shift_zero_of_large_m B t θ n hB hθ' h_large
    have h_integral_zero :
        ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + n) =
          ∫ θ in (-1/2 : ℝ)..(1/2), (0 : ℝ) := by
      exact intervalIntegral.integral_congr h_eq0
    simpa using h_integral_zero

  have hsum_fin :
      ∑ n ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ)) =
        ∫ x, g B t x := by
    exact hsum_eq.symm.trans hsum.tsum_eq

  have h_integral :
      ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m) =
        ∫ x, g B t x := by
    calc
      ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m)
          = ∫ θ in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, g B t (θ + m) := h_int_eq
      _ = ∑ m ∈ s, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + m) := h_int_sum
      _ = ∫ x, g B t x := hsum_fin

  -- RHS simplification
  rw [arch_term_eq_two_pi_integral_g]
  -- LHS: expand P_A and use periodization
  simp only [P_A]
  rw [intervalIntegral.integral_const_mul, h_integral]
  -- g = a * w by definition
  simp only [g]

/-- Arch side: Rayleigh quotient of Toeplitz[P_A] at basis0 = arch_term.
    This follows because RQ(A, basis0) = A[i0,i0] for unit-norm basis vector,
    and Toeplitz diagonal = ∫ P dθ. -/
theorem arch_rayleigh_eq (B t : ℝ) (M : ℕ) (hP : Continuous (P_A B t)) (hB : 0 < B) :
    Q3.RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t)) (basis0 M) =
    Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) := by
  rw [rayleigh_basis0, ToeplitzMatrix_Fourier_real_diag M (P_A B t) hP]
  exact integral_P_A_eq_arch_term B t hB

/-- Prime side: (2M+1) × Rayleigh quotient of T_P_comp at basis0 = prime_term.
    This follows because T_P_comp[i0,i0] = (1/(2M+1))·Σ w_Q·Φ(ξ_n),
    so multiplying by (2M+1) cancels the normalization factor. -/
theorem prime_rayleigh_eq (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] (hM : 0 < 2 * M + 1) :
    (2 * M + 1 : ℝ) * Q3.RayleighQuotient (Q3.T_P_comp_real K B t M) (basis0 M) =
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  rw [rayleigh_basis0, T_P_comp_real_diag K B t M hM]
  field_simp

/-- **The "Honest Formula"** (natural matrix form):

    RQ(Toeplitz - T_P_comp, basis0) = arch_term(Φ) - (1/(2M+1))·prime_sum

    This is what the matrix naturally produces. The factor 1/(2M+1) on the prime term
    comes from the normalized prime_vec: |⟨p, v_n⟩|² = |p(ξ_n)|²/(2M+1).

    For spectral bounds (A3 bridge), this is the clean form:
    - If P_A ≥ c_star (A3 floor), then Toeplitz eigenvalues ≥ c_star
    - If ‖T_P_comp‖ ≤ ρ₁ (RKHS cap), then RQ(T_P_comp) ≤ ρ₁
    - Therefore RQ(Toeplitz - T_P_comp) ≥ c_star - ρ₁ > 0 -/
theorem honest_formula (B t K : ℝ) (M : ℕ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hP : Continuous (P_A B t)) (hM : 0 < 2 * M + 1) :
    Q3.RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
       Q3.T_P_comp_real K B t M) (basis0 M) =
    Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) -
    (1 / (2 * M + 1 : ℝ)) * ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  rw [rayleigh_basis0_sub]
  rw [ToeplitzMatrix_Fourier_real_diag M (P_A B t) hP]
  rw [integral_P_A_eq_arch_term B t hB]
  rw [T_P_comp_real_diag K B t M hM]

/-- Main Rayleigh-Q identification theorem (rescaled form).

    RQ(Toeplitz, basis0) - (2M+1)·RQ(T_P_comp, basis0) = arch_term - prime_sum

    This recovers the structure of Q(Φ) = arch_term - prime_term by applying
    the (2M+1) factor to compensate the prime_vec normalization.

    Equivalently: Q_finite(Φ) where prime_term is summed over Nodes K only.

    Connection to the full prime_term (tsum) is completed below via
    `prime_term_eq_nodes_sum` and `rayleigh_Q_eq_Q`. -/
theorem rayleigh_Q_identification (B t K : ℝ) (M : ℕ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hP : Continuous (P_A B t)) (hM : 0 < 2 * M + 1) :
    Q3.RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t)) (basis0 M) -
    (2 * M + 1 : ℝ) * Q3.RayleighQuotient (Q3.T_P_comp_real K B t M) (basis0 M) =
    Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) -
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  rw [arch_rayleigh_eq B t M hP hB, prime_rayleigh_eq K B t M hM]

/-! ## Bridge: Finite Sum → prime_term (tsum)

For functions with compact support, prime_term (tsum over all n) equals
the finite sum over Nodes K when K is large enough.
-/

/-- fejer_heat_window has compact support: vanishes when |ξ| > B. -/
lemma fejer_heat_window_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) :
    Q3.fejer_heat_window B t ξ = 0 := by
  rw [← w_eq_fejer_heat_window]
  exact w_support B t ξ hB h

/-- w_Q n = 0 for n < 2 (vonMangoldt vanishes at 0 and 1). -/
lemma w_Q_zero_of_lt_two (n : ℕ) (hn : n < 2) : Q3.w_Q n = 0 := by
  simp only [Q3.w_Q]
  interval_cases n
  · -- n = 0: vonMangoldt 0 = 0
    simp only [ArithmeticFunction.map_zero, zero_div, mul_zero]
  · -- n = 1: vonMangoldt 1 = 0
    simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, mul_zero]

/-- Generic bridge: if Φ vanishes outside [-K, K], then the prime_term (tsum)
    equals the finite sum over Nodes K. -/
theorem prime_term_eq_nodes_of_support (Φ : ℝ → ℝ) (K : ℝ) [Fintype (Q3.Nodes K)]
    (hΦ : ∀ ξ, K < |ξ| → Φ ξ = 0) :
    Q3.prime_term Φ = ∑ n : Q3.Nodes K, Q3.w_Q n * Φ (Q3.xi_n n) := by
  classical
  have h_zero_outside : ∀ n : ℕ, n ∉ Q3.Nodes K →
      Q3.w_Q n * Φ (Q3.xi_n n) = 0 := by
    intro n hn
    simp only [Q3.Nodes, Set.mem_setOf_eq, not_and_or, not_le] at hn
    rcases hn with h_outside | hn2
    · -- Case: |xi_n n| > K, so Φ vanishes
      simp [hΦ (Q3.xi_n n) h_outside]
    · -- Case: n < 2, so w_Q n = 0
      simp [w_Q_zero_of_lt_two n hn2]
  have hsupport :
      Function.support (fun n => Q3.w_Q n * Φ (Q3.xi_n n)) ⊆ Q3.Nodes K := by
    refine Function.support_subset_iff'.2 ?_
    intro n hn
    exact h_zero_outside n hn
  have htsum :
      (∑' n : ℕ, Q3.w_Q n * Φ (Q3.xi_n n)) =
        ∑' n : Q3.Nodes K, Q3.w_Q n * Φ (Q3.xi_n n) :=
    (tsum_subtype_eq_of_support_subset hsupport).symm
  simpa [Q3.prime_term, tsum_fintype] using htsum

/-- Key bridge: For Φ with support in [-B, B] and K ≥ B, the prime_term (tsum)
    equals the finite sum over Nodes K.

    This connects rayleigh_Q_identification to Q3.Q. -/
theorem prime_term_eq_nodes_sum (B t K : ℝ) [Fintype (Q3.Nodes K)]
    (hB : 0 < B) (hK : B ≤ K) :
    Q3.prime_term (fun ξ => Q3.fejer_heat_window B t ξ) =
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  have hΦ : ∀ ξ, K < |ξ| → Q3.fejer_heat_window B t ξ = 0 := by
    intro ξ hξ
    have h_support : B < |ξ| := lt_of_le_of_lt hK hξ
    exact fejer_heat_window_support B t ξ hB h_support
  simpa using (prime_term_eq_nodes_of_support (Φ := fun ξ => Q3.fejer_heat_window B t ξ) (K := K) hΦ)

/-- **Final Q3.Q identification**: Combining rayleigh_Q_identification with
    prime_term_eq_nodes_sum gives the connection to Q3.Q.

    RQ(Toeplitz) − (2M+1)·RQ(T_P_comp) = Q3.Q(Φ)

    where Φ = fejer_heat_window B t with K ≥ B. -/
theorem rayleigh_Q_eq_Q (B t K : ℝ) (M : ℕ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hK : B ≤ K)
    (hP : Continuous (P_A B t)) (hM : 0 < 2 * M + 1) :
    Q3.RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t)) (basis0 M) -
    (2 * M + 1 : ℝ) * Q3.RayleighQuotient (Q3.T_P_comp_real K B t M) (basis0 M) =
    Q3.Q (fun ξ => Q3.fejer_heat_window B t ξ) := by
  rw [rayleigh_Q_identification B t K M hB hP hM]
  simp only [Q3.Q]
  congr 1
  exact (prime_term_eq_nodes_sum B t K hB hK).symm

/-- Diagonal of shifted T_P_comp_real at basis0. -/
lemma T_P_comp_real_shift_diag (K B t tau : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] (hM : 0 < 2 * M + 1) :
    Q3.T_P_comp_real_shift K B t tau M (i0 M) (i0 M) =
      (1 / (2 * M + 1 : ℝ)) *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n) := by
  simp only [Q3.T_P_comp_real_shift, Q3.T_P_comp_shift]
  -- Factor out the norm squared of prime_vec at i0
  have h_factor : ∀ n : Q3.Nodes K,
      ((Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n)) : ℂ) *
        Q3.prime_vec M (Q3.xi_n n) (i0 M) * conj (Q3.prime_vec M (Q3.xi_n n) (i0 M)) =
      ((Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n)) : ℂ) * (1 / (2 * M + 1 : ℝ)) := by
    intro n
    rw [mul_assoc, prime_vec_i0_norm_sq M (Q3.xi_n n) hM]
  -- Rewrite the sum using h_factor
  have h_sum_eq : (∑ n : Q3.Nodes K,
        ((Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n)) : ℂ) *
          Q3.prime_vec M (Q3.xi_n n) (i0 M) * conj (Q3.prime_vec M (Q3.xi_n n) (i0 M))) =
      ∑ n : Q3.Nodes K, ((Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n)) : ℂ) *
        (1 / (2 * M + 1 : ℝ)) := Finset.sum_congr rfl (fun n _ => h_factor n)
  rw [h_sum_eq]
  -- Now simplify the sum with constant factor
  rw [← Finset.sum_mul]
  simp only [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum]
  rw [one_div, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem arch_rayleigh_eq_shift (B t tau : ℝ) (M : ℕ)
    (hP : Continuous (Q3.P_A_shift B t tau)) (hB : 0 < B) :
    Q3.RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t tau)) (basis0 M) =
    Q3.arch_term (fun ξ => Q3.phi_shift B t tau ξ) := by
  rw [rayleigh_basis0, ToeplitzMatrix_Fourier_real_diag M (Q3.P_A_shift B t tau) hP]
  exact Q3.Proofs.ShiftedWindows.integral_P_A_shift_eq_arch_term B t tau hB

theorem prime_rayleigh_eq_shift (K B t tau : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] (hM : 0 < 2 * M + 1) :
    (2 * M + 1 : ℝ) * Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t tau M) (basis0 M) =
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n) := by
  rw [rayleigh_basis0, T_P_comp_real_shift_diag K B t tau M hM]
  field_simp

theorem rayleigh_Q_identification_shift (B t tau K : ℝ) (M : ℕ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hP : Continuous (Q3.P_A_shift B t tau)) (hM : 0 < 2 * M + 1) :
    Q3.RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t tau)) (basis0 M) -
    (2 * M + 1 : ℝ) * Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t tau M) (basis0 M) =
    Q3.arch_term (fun ξ => Q3.phi_shift B t tau ξ) -
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n) := by
  rw [arch_rayleigh_eq_shift B t tau M hP hB, prime_rayleigh_eq_shift K B t tau M hM]

theorem prime_term_eq_nodes_sum_shift (B t tau K : ℝ) [Fintype (Q3.Nodes K)]
    (hB : 0 < B) (hK : |tau| + B ≤ K) :
    Q3.prime_term (fun ξ => Q3.phi_shift B t tau ξ) =
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n) := by
  have hPhi : ∀ ξ, K < |ξ| → Q3.phi_shift B t tau ξ = 0 := by
    intro ξ hξ
    exact Q3.Proofs.ShiftedWindows.phi_shift_support_of_margin B t tau K hB hK ξ hξ
  simpa using (prime_term_eq_nodes_of_support (Φ := fun ξ => Q3.phi_shift B t tau ξ) (K := K) hPhi)

theorem rayleigh_Q_eq_Q_shift (B t tau K : ℝ) (M : ℕ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hK : |tau| + B ≤ K)
    (hP : Continuous (Q3.P_A_shift B t tau)) (hM : 0 < 2 * M + 1) :
    Q3.RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t tau)) (basis0 M) -
    (2 * M + 1 : ℝ) * Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t tau M) (basis0 M) =
    Q3.Q (fun ξ => Q3.phi_shift B t tau ξ) := by
  rw [rayleigh_Q_identification_shift B t tau K M hB hP hM]
  simp only [Q3.Q]
  congr 1
  exact (prime_term_eq_nodes_sum_shift B t tau K hB hK).symm

end Q3.Proofs.RayleighQId
