/-
Q_Lipschitz Prime Term Bridge
=============================

This file proves the prime_term Lipschitz bound used in Q_Lipschitz.lean.
Closes the axiom prime_term_Lipschitz_bridge.

Mathematical content:
  |prime_term Φ₁ - prime_term Φ₂| ≤ W_sum · ‖Φ₁ - Φ₂‖_∞

Proof:
  prime_term Φ = Σ w_Q(n) · Φ(ξ_n)
  prime_term Φ₁ - prime_term Φ₂ = Σ w_Q(n) · (Φ₁ - Φ₂)(ξ_n)  (linearity of tsum)
  |Σ w_Q(n) · (Φ₁ - Φ₂)(ξ_n)| ≤ Σ |w_Q(n)| · |(Φ₁ - Φ₂)(ξ_n)|  (triangle)
                               = Σ w_Q(n) · |(Φ₁ - Φ₂)(ξ_n)|     (w_Q ≥ 0)
                               ≤ Σ w_Q(n) · ‖Φ₁ - Φ₂‖_∞          (pointwise ≤ sup)
                               = W_sum · ‖Φ₁ - Φ₂‖_∞
-/

import Q3.Basic.Defs
import Q3.Axioms

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Nat Classical Pointwise
open MeasureTheory

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

namespace Q3.Proofs.QLipschitzPrimeBridge

open Q3

/-! ## Definitions (must match Q_Lipschitz.lean) -/

/-- Active prime nodes: n ≥ 2 with |ξ_n| ≤ K -/
def ActiveNodes_local (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

/-- Sum of weights over active nodes -/
def W_sum_local (K : ℝ) : ℝ :=
  ∑' n, if n ∈ ActiveNodes_local K then w_Q n else 0

/-- Local prime_term -/
def prime_term_local (Φ : ℝ → ℝ) : ℝ := ∑' n, w_Q n * Φ (xi_n n)

/-- w_Q is nonnegative -/
lemma w_Q_nonneg (n : ℕ) : 0 ≤ w_Q n := by
  unfold w_Q
  apply div_nonneg
  · apply mul_nonneg
    · norm_num
    · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact Real.sqrt_nonneg _

/-- w_Q(2) is positive: w_Q(2) = 2·log(2)/√2 > 0 -/
lemma w_Q_two_pos : w_Q 2 > 0 := by
  unfold w_Q
  apply div_pos
  · apply mul_pos
    · norm_num
    · -- vonMangoldt(2) = log(2) > 0
      simp only [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

/-- xi_n(2) = log(2)/(2π) < 1 -/
lemma xi_n_two_lt_one : xi_n 2 < 1 := by
  unfold xi_n
  simp only [Nat.cast_ofNat]
  rw [div_lt_one (by positivity : 2 * Real.pi > 0)]
  calc Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    _ < 2 * Real.pi := by have := Real.pi_gt_three; linarith

/-- xi_n 2 > 0 -/
lemma xi_n_two_pos : xi_n 2 > 0 := by
  unfold xi_n
  apply div_pos
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  · positivity

/-- 2 is in ActiveNodes_local K for any K ≥ 1 -/
lemma two_mem_ActiveNodes (K : ℝ) (hK : K ≥ 1) : (2 : ℕ) ∈ ActiveNodes_local K := by
  simp only [ActiveNodes_local, Set.mem_setOf_eq]
  constructor
  · -- |xi_n 2| ≤ K
    rw [abs_of_pos xi_n_two_pos]
    have h1 : xi_n 2 < 1 := xi_n_two_lt_one
    linarith
  · norm_num

/-- ActiveNodes_local K is finite (n ≥ 2 and |xi_n n| ≤ K means n ≤ exp(2πK)) -/
lemma ActiveNodes_local_finite (K : ℝ) (hK : K ≥ 1) : Set.Finite (ActiveNodes_local K) := by
  -- ActiveNodes_local K ⊆ {n | n ≤ Nat.ceil (exp(2πK))} which is finite
  apply Set.Finite.subset (Set.finite_Icc 0 (Nat.ceil (Real.exp (2 * Real.pi * K))))
  intro n hn
  simp only [ActiveNodes_local, Set.mem_setOf_eq] at hn
  simp only [Set.mem_Icc]
  constructor
  · exact Nat.zero_le n
  · -- n ≥ 2 and |xi_n n| ≤ K, so log(n)/(2π) ≤ K, so log(n) ≤ 2πK, so n ≤ exp(2πK)
    have h_xi : xi_n n ≤ K := by
      have h1 := hn.1
      rw [abs_le] at h1
      exact h1.2
    have hn2 : (n : ℝ) ≥ 2 := by exact_mod_cast hn.2
    have hn_pos : (n : ℝ) > 0 := by linarith
    -- xi_n n = log(n)/(2π), so log(n) ≤ 2πK
    have h_log : Real.log n ≤ 2 * Real.pi * K := by
      unfold xi_n at h_xi
      have h2pi : 2 * Real.pi > 0 := by positivity
      calc Real.log n = xi_n n * (2 * Real.pi) := by unfold xi_n; field_simp
        _ ≤ K * (2 * Real.pi) := by apply mul_le_mul_of_nonneg_right h_xi (le_of_lt h2pi)
        _ = 2 * Real.pi * K := by ring
    -- So n ≤ exp(2πK), hence n ≤ ⌈exp(2πK)⌉
    have h_n_le_exp : (n : ℝ) ≤ Real.exp (2 * Real.pi * K) :=
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn_pos).symm
        _ ≤ Real.exp (2 * Real.pi * K) := Real.exp_le_exp_of_le h_log
    -- n = ⌈(n:ℝ)⌉ ≤ ⌈exp(2πK)⌉
    have h_ceil : Nat.ceil (n : ℝ) = n := Nat.ceil_natCast n
    calc n = Nat.ceil (n : ℝ) := h_ceil.symm
      _ ≤ Nat.ceil (Real.exp (2 * Real.pi * K)) := Nat.ceil_mono h_n_le_exp

/-- W_sum_local is positive for K ≥ 1 (it includes n=2). -/
lemma W_sum_local_pos (K : ℝ) (hK : K ≥ 1) : W_sum_local K > 0 := by
  unfold W_sum_local
  have h2 : (2 : ℕ) ∈ ActiveNodes_local K := two_mem_ActiveNodes K hK
  have h_fin := ActiveNodes_local_finite K hK
  -- Summability from finiteness
  have h_summable : Summable (fun n => if n ∈ ActiveNodes_local K then w_Q n else 0) := by
    apply summable_of_ne_finset_zero (s := h_fin.toFinset)
    intro n hn
    simp only [Set.Finite.mem_toFinset] at hn
    simp only [if_neg hn]
  -- Nonnegativity
  have h_nonneg : ∀ j, j ≠ 2 → 0 ≤ (if j ∈ ActiveNodes_local K then w_Q j else 0) := by
    intro j _
    by_cases h : j ∈ ActiveNodes_local K <;> simp [h, w_Q_nonneg j]
  -- Lower bound by single term
  calc ∑' n, (if n ∈ ActiveNodes_local K then w_Q n else 0)
      ≥ (if (2 : ℕ) ∈ ActiveNodes_local K then w_Q 2 else 0) := h_summable.le_tsum 2 h_nonneg
    _ = w_Q 2 := by simp only [if_pos h2]
    _ > 0 := w_Q_two_pos

/-! ## Helper lemmas -/

/-- For Φ with support in [-K, K], if |ξ_n| > K then Φ(ξ_n) = 0 -/
lemma Phi_zero_outside_support (K : ℝ) (Φ : ℝ → ℝ)
    (hsupp : Function.support Φ ⊆ Set.Icc (-K) K) (n : ℕ) (hn : |xi_n n| > K) :
    Φ (xi_n n) = 0 := by
  by_contra h
  have hmem : xi_n n ∈ Function.support Φ := h
  have hIcc : xi_n n ∈ Set.Icc (-K) K := hsupp hmem
  rw [Set.mem_Icc] at hIcc
  -- hIcc : -K ≤ xi_n n ∧ xi_n n ≤ K implies |xi_n n| ≤ K
  have habs : |xi_n n| ≤ K := abs_le.mpr hIcc
  linarith

/-- The set {n | |ξ_n| ≤ K ∧ n ≥ 2} is finite -/
lemma active_nodes_finite (K : ℝ) : Set.Finite {n : ℕ | |xi_n n| ≤ K ∧ n ≥ 2} := by
  -- Bound: if n > exp(2πK) then ξ_n = log(n)/(2π) > K
  have hbound : ∀ n : ℕ, n ∈ {n : ℕ | |xi_n n| ≤ K ∧ n ≥ 2} →
      n ≤ Nat.ceil (Real.exp (2 * Real.pi * K)) := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra h_big
    push_neg at h_big
    have h_xi : xi_n n > K := by
      unfold xi_n
      have hpi : (2 : ℝ) * Real.pi > 0 := by positivity
      rw [gt_iff_lt, lt_div_iff₀' hpi]
      have h1 : (n : ℝ) > Real.exp (2 * Real.pi * K) := by
        calc (n : ℝ) ≥ Nat.ceil (Real.exp (2 * Real.pi * K)) + 1 := by
              exact_mod_cast h_big
           _ > Real.exp (2 * Real.pi * K) := by
              have := Nat.le_ceil (Real.exp (2 * Real.pi * K))
              linarith
      calc Real.log n > Real.log (Real.exp (2 * Real.pi * K)) := by
            apply Real.log_lt_log (Real.exp_pos _) h1
         _ = 2 * Real.pi * K := Real.log_exp _
    have h_abs : |xi_n n| > K := by
      rw [abs_of_nonneg]
      · exact h_xi
      · unfold xi_n; exact div_nonneg (Real.log_natCast_nonneg n) (by positivity)
    linarith [hn.1]
  -- Use that bounded subset of ℕ is finite
  refine Set.Finite.subset (Set.finite_Icc 0 (Nat.ceil (Real.exp (2 * Real.pi * K)))) ?_
  intro n hn
  simp only [Set.mem_Icc, zero_le, true_and]
  exact hbound n hn

/-- Summable helper: w_Q n * Φ(ξ_n) is summable when Φ has compact support -/
lemma summable_w_Q_Phi (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ)
    (hsupp : Function.support Φ ⊆ Set.Icc (-K) K) :
    Summable (fun n => w_Q n * Φ (xi_n n)) := by
  -- The sum is finite because only finitely many n have |ξ_n| ≤ K
  have h_finite : Set.Finite {n : ℕ | w_Q n * Φ (xi_n n) ≠ 0} := by
    apply Set.Finite.subset (active_nodes_finite K)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    constructor
    · -- |ξ_n| ≤ K (otherwise Φ(ξ_n) = 0)
      by_contra h_abs
      push_neg at h_abs
      have := Phi_zero_outside_support K Φ hsupp n h_abs
      simp only [this, mul_zero, ne_eq, not_true_eq_false] at hn
    · -- n ≥ 2 (otherwise w_Q n = 0)
      by_contra h_small
      push_neg at h_small
      interval_cases n
      · -- n = 0: vonMangoldt 0 = 0
        unfold w_Q at hn
        simp only [CharP.cast_eq_zero, Real.sqrt_zero, div_zero, zero_mul, ne_eq,
          not_true_eq_false] at hn
      · -- n = 1: vonMangoldt 1 = 0
        unfold w_Q at hn
        have hvm : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
        simp only [Nat.cast_one, hvm, mul_zero, Real.sqrt_one, zero_div, zero_mul, ne_eq,
          not_true_eq_false] at hn
  exact summable_of_ne_finset_zero (s := h_finite.toFinset)
    (fun n hn => by simp only [Set.Finite.mem_toFinset] at hn; exact Classical.not_not.mp hn)

/-! ## Main theorem -/

/-- D is bddAbove when Φ₁, Φ₂ continuous on compact [-K,K] -/
lemma D_bddAbove (K : ℝ) (hK : K > 0) (Φ₁ Φ₂ : ℝ → ℝ)
    (hcont₁ : ContinuousOn Φ₁ (Set.Icc (-K) K))
    (hcont₂ : ContinuousOn Φ₂ (Set.Icc (-K) K)) :
    BddAbove {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by
  have hcomp : IsCompact (Set.Icc (-K) K) := isCompact_Icc
  have hcont_diff : ContinuousOn (fun x => |Φ₁ x - Φ₂ x|) (Set.Icc (-K) K) :=
    ContinuousOn.abs (hcont₁.sub hcont₂)
  exact (hcomp.image_of_continuousOn hcont_diff).bddAbove

/-- Prime term Lipschitz bound.
    |prime_term Φ₁ - prime_term Φ₂| ≤ W_sum_local K · ‖Φ₁ - Φ₂‖_∞ -/
theorem prime_term_Lipschitz (K : ℝ) (hK : K > 0) (Φ₁ Φ₂ : ℝ → ℝ)
    (hcont₁ : ContinuousOn Φ₁ (Set.Icc (-K) K))
    (hcont₂ : ContinuousOn Φ₂ (Set.Icc (-K) K))
    (hsupp₁ : Function.support Φ₁ ⊆ Set.Icc (-K) K)
    (hsupp₂ : Function.support Φ₂ ⊆ Set.Icc (-K) K) :
    |prime_term_local Φ₁ - prime_term_local Φ₂| ≤
      W_sum_local K * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by
  -- Let D = sup norm of difference
  set D := sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} with hD_def

  -- D ≥ 0
  have hD_nonneg : D ≥ 0 := by
    apply Real.sSup_nonneg
    intro y hy
    obtain ⟨x, _, rfl⟩ := hy
    exact abs_nonneg _

  -- Summability
  have hsum₁ := summable_w_Q_Phi K hK Φ₁ hsupp₁
  have hsum₂ := summable_w_Q_Phi K hK Φ₂ hsupp₂

  -- prime_term_local Φ₁ - prime_term_local Φ₂ = Σ w_Q(n) * (Φ₁ - Φ₂)(ξ_n)
  have h_diff : prime_term_local Φ₁ - prime_term_local Φ₂ =
      ∑' n, w_Q n * (Φ₁ (xi_n n) - Φ₂ (xi_n n)) := by
    unfold prime_term_local
    rw [← Summable.tsum_sub hsum₁ hsum₂]
    congr 1
    ext n
    ring

  rw [h_diff]

  -- |Σ ...| ≤ Σ |...|
  have h_summable_diff : Summable (fun n => w_Q n * (Φ₁ (xi_n n) - Φ₂ (xi_n n))) := by
    have : (fun n => w_Q n * (Φ₁ (xi_n n) - Φ₂ (xi_n n))) =
           (fun n => w_Q n * Φ₁ (xi_n n) - w_Q n * Φ₂ (xi_n n)) := by
      ext n; ring
    rw [this]
    exact Summable.sub hsum₁ hsum₂

  have h_summable_abs : Summable (fun n => |w_Q n * (Φ₁ (xi_n n) - Φ₂ (xi_n n))|) :=
    h_summable_diff.abs

  calc |∑' n, w_Q n * (Φ₁ (xi_n n) - Φ₂ (xi_n n))|
      ≤ ∑' n, |w_Q n * (Φ₁ (xi_n n) - Φ₂ (xi_n n))| := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm h_summable_abs
    _ = ∑' n, |w_Q n| * |Φ₁ (xi_n n) - Φ₂ (xi_n n)| := by
        congr 1; ext n; exact abs_mul _ _
    _ = ∑' n, w_Q n * |Φ₁ (xi_n n) - Φ₂ (xi_n n)| := by
        congr 1; ext n; rw [abs_of_nonneg (w_Q_nonneg n)]
    _ ≤ W_sum_local K * D := by
        -- Key insight: only finitely many n contribute (those with |ξ_n| ≤ K and n ≥ 2)
        -- For other n: either w_Q n = 0 (n < 2) or Φ(ξ_n) = 0 (|ξ_n| > K)

        -- Bound each term: w_Q n * |Φ₁(ξ_n) - Φ₂(ξ_n)| ≤ w_Q n * D (if active) or = 0 (if not)
        have h_term_bound : ∀ n, w_Q n * |Φ₁ (xi_n n) - Φ₂ (xi_n n)| ≤
            (if n ∈ ActiveNodes_local K then w_Q n else 0) * D := by
          intro n
          by_cases h_active : n ∈ ActiveNodes_local K
          · -- Active node: |ξ_n| ≤ K and n ≥ 2
            simp only [h_active, ite_true]
            apply mul_le_mul_of_nonneg_left _ (w_Q_nonneg n)
            -- |Φ₁(ξ_n) - Φ₂(ξ_n)| ≤ D
            apply le_csSup (D_bddAbove K hK Φ₁ Φ₂ hcont₁ hcont₂)
            use xi_n n
            constructor
            · exact abs_le.mp h_active.1
            · rfl
          · -- Not active: either n < 2 (so w_Q = 0) or |ξ_n| > K (so Φ = 0)
            simp only [h_active, ite_false, zero_mul]
            unfold ActiveNodes_local at h_active
            simp only [Set.mem_setOf_eq] at h_active
            -- h_active : ¬(|xi_n n| ≤ K ∧ n ≥ 2)
            -- This means: |xi_n n| > K ∨ n < 2
            rw [not_and_or] at h_active
            rcases h_active with h_out | hn_small
            · -- |ξ_n| > K (from ¬(|xi_n n| ≤ K))
              rw [not_le] at h_out
              have h1 := Phi_zero_outside_support K Φ₁ hsupp₁ n h_out
              have h2 := Phi_zero_outside_support K Φ₂ hsupp₂ n h_out
              simp only [h1, h2, sub_zero, abs_zero, mul_zero, le_refl]
            · -- n < 2, so w_Q n = 0
              rw [not_le] at hn_small
              interval_cases n
              · unfold w_Q
                simp only [CharP.cast_eq_zero, Real.sqrt_zero, div_zero, zero_mul, le_refl]
              · unfold w_Q
                have hvm : ArithmeticFunction.vonMangoldt 1 = 0 :=
                  ArithmeticFunction.vonMangoldt_apply_one
                simp only [Nat.cast_one, hvm, mul_zero, Real.sqrt_one, zero_div, zero_mul, le_refl]

        -- Summability of (if active then w_Q else 0) * D
        have h_summable_bound : Summable (fun n => (if n ∈ ActiveNodes_local K then w_Q n else 0) * D) := by
          apply Summable.mul_right
          -- Summable of indicator * w_Q
          have h_fin : Set.Finite (ActiveNodes_local K) := active_nodes_finite K
          refine summable_of_ne_finset_zero (s := h_fin.toFinset) ?_
          intro n hn
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn
          simp only [hn, ite_false]

        -- Summability of LHS
        have h_summable_lhs : Summable (fun n => w_Q n * |Φ₁ (xi_n n) - Φ₂ (xi_n n)|) := by
          apply Summable.of_nonneg_of_le
          · intro n; exact mul_nonneg (w_Q_nonneg n) (abs_nonneg _)
          · exact h_term_bound
          · exact h_summable_bound

        -- Now use tsum_le_tsum
        calc ∑' n, w_Q n * |Φ₁ (xi_n n) - Φ₂ (xi_n n)|
            ≤ ∑' n, (if n ∈ ActiveNodes_local K then w_Q n else 0) * D :=
              Summable.tsum_le_tsum h_term_bound h_summable_lhs h_summable_bound
          _ = (∑' n, if n ∈ ActiveNodes_local K then w_Q n else 0) * D := tsum_mul_right
          _ = W_sum_local K * D := by unfold W_sum_local; rfl

end Q3.Proofs.QLipschitzPrimeBridge

end
