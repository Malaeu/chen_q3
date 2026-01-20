/-
Q_Lipschitz Bridge
==================

This file bridges the local proofs (prime_bridge, arch_bridge) to prove
Q_Lipschitz_on_W_K (the axiom in Q3.Axioms).

Main result:
  |Q Φ₁ - Q Φ₂| ≤ L · ‖Φ₁ - Φ₂‖_∞  for Φ₁, Φ₂ ∈ W_K K

where L = 2K·M_a + W_sum.

Proof outline:
  Q = arch_term - prime_term
  |Q Φ₁ - Q Φ₂| = |(arch Φ₁ - prime Φ₁) - (arch Φ₂ - prime Φ₂)|
                ≤ |arch Φ₁ - arch Φ₂| + |prime Φ₁ - prime Φ₂|   (triangle)
                ≤ (2K·M_a + W_sum) · D
-/

import Q3.Basic.Defs
import Q3.Axioms
import Q3.Proofs.Q_Lipschitz_prime_bridge
import Q3.Proofs.Q_Lipschitz_arch_bridge

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Nat Classical Pointwise
open MeasureTheory

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

namespace Q3.Proofs.QLipschitzBridge

open Q3
open Q3.Proofs.QLipschitzPrimeBridge (W_sum_local W_sum_local_pos prime_term_Lipschitz)
open Q3.Proofs.QLipschitzArchBridge (M_a_local M_a_local_pos arch_term_local arch_term_Lipschitz)

/-! ## Connecting local to global terms -/

/-- For functions with support in [-K, K], prime_term = prime_term_local -/
lemma prime_term_eq_local (Φ : ℝ → ℝ) :
    Q3.prime_term Φ = QLipschitzPrimeBridge.prime_term_local Φ := rfl

/-- For functions with support in [-K, K], arch_term equals arch_term_local -/
lemma arch_term_eq_local (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ)
    (hsupp : Function.support Φ ⊆ Set.Icc (-K) K) :
    Q3.arch_term Φ = arch_term_local K Φ := by
  unfold Q3.arch_term arch_term_local
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro ξ hξ
  simp only [Set.mem_Icc, not_and, not_le] at hξ
  by_cases h_neg : ξ < -K
  · have h : Φ ξ = 0 := by
      by_contra hne
      have := hsupp hne
      simp only [Set.mem_Icc] at this
      linarith
    simp [h]
  · push_neg at h_neg
    have h_big : ξ > K := hξ h_neg
    have h : Φ ξ = 0 := by
      by_contra hne
      have := hsupp hne
      simp only [Set.mem_Icc] at this
      linarith
    simp [h]

/-! ## Main theorem -/

/-- Lipschitz constant for Q on W_K -/
def L_Q (K : ℝ) : ℝ := 2 * K * M_a_local K + W_sum_local K

/-- L_Q is positive for K ≥ 1 -/
lemma L_Q_pos (K : ℝ) (hK : K ≥ 1) : L_Q K > 0 := by
  unfold L_Q
  have hK_pos : K > 0 := by linarith
  apply add_pos
  · apply mul_pos
    · apply mul_pos
      · linarith
      · exact hK_pos
    · exact M_a_local_pos K hK_pos
  · exact W_sum_local_pos K hK

/-- Q is Lipschitz on W_K for K ≥ 1.
    This closes the Q_Lipschitz_on_W_K axiom for the relevant case K ≥ 1. -/
theorem Q_Lipschitz_on_W_K_bridge (K : ℝ) (hK : K ≥ 1) :
    ∃ L > 0, ∀ Φ₁, Φ₁ ∈ W_K K → ∀ Φ₂, Φ₂ ∈ W_K K →
      |Q Φ₁ - Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by
  have hK_pos : K > 0 := by linarith
  use L_Q K, L_Q_pos K hK
  intro Φ₁ hΦ₁ Φ₂ hΦ₂

  -- Extract properties from W_K membership
  -- W_K K = {Φ | Continuous ∧ support ⊆ Icc ∧ IsEven ∧ IsNonneg}
  have hcont₁ : ContinuousOn Φ₁ (Set.Icc (-K) K) := hΦ₁.1.continuousOn
  have hcont₂ : ContinuousOn Φ₂ (Set.Icc (-K) K) := hΦ₂.1.continuousOn
  have hsupp₁ : Function.support Φ₁ ⊆ Set.Icc (-K) K := hΦ₁.2.1
  have hsupp₂ : Function.support Φ₂ ⊆ Set.Icc (-K) K := hΦ₂.2.1

  -- Let D = sup norm
  set D := sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} with hD_def

  -- Q = arch - prime
  have hQ₁ : Q Φ₁ = arch_term Φ₁ - prime_term Φ₁ := rfl
  have hQ₂ : Q Φ₂ = arch_term Φ₂ - prime_term Φ₂ := rfl

  -- Rewrite using local terms
  have h_arch_eq₁ : arch_term Φ₁ = arch_term_local K Φ₁ :=
    arch_term_eq_local K hK_pos Φ₁ hsupp₁
  have h_arch_eq₂ : arch_term Φ₂ = arch_term_local K Φ₂ :=
    arch_term_eq_local K hK_pos Φ₂ hsupp₂

  -- Triangle inequality
  calc |Q Φ₁ - Q Φ₂|
      = |(arch_term Φ₁ - prime_term Φ₁) - (arch_term Φ₂ - prime_term Φ₂)| := rfl
    _ = |(arch_term Φ₁ - arch_term Φ₂) - (prime_term Φ₁ - prime_term Φ₂)| := by ring_nf
    _ ≤ |arch_term Φ₁ - arch_term Φ₂| + |prime_term Φ₁ - prime_term Φ₂| :=
        abs_sub _ _
    _ = |arch_term_local K Φ₁ - arch_term_local K Φ₂| + |prime_term Φ₁ - prime_term Φ₂| := by
        rw [h_arch_eq₁, h_arch_eq₂]
    _ ≤ (2 * K * M_a_local K * D) + (W_sum_local K * D) := by
        apply add_le_add
        · exact arch_term_Lipschitz K hK_pos Φ₁ Φ₂ hcont₁ hcont₂
        · exact prime_term_Lipschitz K hK_pos Φ₁ Φ₂ hcont₁ hcont₂ hsupp₁ hsupp₂
    _ = (2 * K * M_a_local K + W_sum_local K) * D := by ring
    _ = L_Q K * D := rfl

end Q3.Proofs.QLipschitzBridge

end
