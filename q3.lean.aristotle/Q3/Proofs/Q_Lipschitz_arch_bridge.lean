/-
Q_Lipschitz Arch Term Bridge
============================

This file proves the arch_term Lipschitz bound used in Q_Lipschitz.lean.
Closes the axiom arch_term_Lipschitz_bridge.

Mathematical content:
  |arch_term Φ₁ - arch_term Φ₂| ≤ 2K · M_a · ‖Φ₁ - Φ₂‖_∞

Approach: Work exclusively with set integrals on [-K, K] to avoid
integrability issues with the full integral. Since the functions have
support in [-K, K], the full integral equals the set integral.
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

namespace Q3.Proofs.QLipschitzArchBridge

open Q3

/-! ## Definitions (must match Q_Lipschitz.lean) -/

/-- Sup of |a_star| on [-K, K] (absolute value for correct Lipschitz bound) -/
def M_a_local (K : ℝ) : ℝ := sSup ((fun ξ => |a_star ξ|) '' Set.Icc (-K) K)

/-- Local arch_term as SET INTEGRAL on [-K, K] -/
def arch_term_local (K : ℝ) (Φ : ℝ → ℝ) : ℝ := ∫ ξ in Set.Icc (-K) K, a_star ξ * Φ ξ

/-! ## Helper lemmas -/

/-- |a_star| is bounded above on compacts -/
lemma abs_a_star_bdd_above_on_Icc (K : ℝ) (hK : K > 0) :
    BddAbove ((fun ξ => |a_star ξ|) '' Set.Icc (-K) K) := by
  -- |a_star| is continuous on compact, hence bounded
  have hcont : ContinuousOn (fun ξ => |a_star ξ|) (Set.Icc (-K) K) :=
    a_star_continuous.abs.continuousOn
  have hcompact : IsCompact (Set.Icc (-K) K) := isCompact_Icc
  exact (hcompact.image_of_continuousOn hcont).bddAbove

/-- |a_star| image on [-K, K] is nonempty -/
lemma abs_a_star_image_nonempty (K : ℝ) (hK : K > 0) :
    ((fun ξ => |a_star ξ|) '' Set.Icc (-K) K).Nonempty := by
  refine ⟨|a_star 0|, 0, ?_, rfl⟩
  constructor <;> linarith

/-- M_a_local K > 0 (since |a_star 0| > 0) -/
lemma M_a_local_pos (K : ℝ) (hK : K > 0) : M_a_local K > 0 := by
  unfold M_a_local
  have h_bdd := abs_a_star_bdd_above_on_Icc K hK
  have h_pos : |a_star 0| > 0 := abs_pos.mpr (ne_of_gt a_star_pos)
  have h_mem : |a_star 0| ∈ (fun ξ => |a_star ξ|) '' Set.Icc (-K) K := by
    refine ⟨0, ?_, rfl⟩
    constructor <;> linarith
  exact lt_of_lt_of_le h_pos (le_csSup h_bdd h_mem)

/-- |a_star ξ| ≤ M_a_local K for ξ ∈ [-K, K] -/
lemma abs_le_M_a_local (K : ℝ) (hK : K > 0) (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-K) K) :
    |a_star ξ| ≤ M_a_local K := by
  unfold M_a_local
  apply le_csSup (abs_a_star_bdd_above_on_Icc K hK)
  exact ⟨ξ, hξ, rfl⟩

/-- D is bddAbove when Φ₁, Φ₂ continuous on compact [-K,K] -/
lemma D_bddAbove (K : ℝ) (hK : K > 0) (Φ₁ Φ₂ : ℝ → ℝ)
    (hcont₁ : ContinuousOn Φ₁ (Set.Icc (-K) K))
    (hcont₂ : ContinuousOn Φ₂ (Set.Icc (-K) K)) :
    BddAbove {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by
  have hcomp : IsCompact (Set.Icc (-K) K) := isCompact_Icc
  have hcont_diff : ContinuousOn (fun x => |Φ₁ x - Φ₂ x|) (Set.Icc (-K) K) :=
    ContinuousOn.abs (hcont₁.sub hcont₂)
  exact (hcomp.image_of_continuousOn hcont_diff).bddAbove

/-- D set is nonempty -/
lemma D_nonempty (K : ℝ) (hK : K > 0) (Φ₁ Φ₂ : ℝ → ℝ) :
    {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K}.Nonempty := by
  refine ⟨|Φ₁ 0 - Φ₂ 0|, 0, ?_, rfl⟩
  simp only [Set.mem_Icc]
  constructor <;> linarith

/-- Measure of [-K, K] equals 2K -/
lemma volume_real_Icc (K : ℝ) (hK : K > 0) :
    volume.real (Set.Icc (-K) K) = 2 * K := by
  rw [Measure.real_def, Real.volume_Icc]
  simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ K - (-K))]
  ring

/-! ## Main theorem -/

/-- Arch term Lipschitz bound.
    |arch_term Φ₁ - arch_term Φ₂| ≤ 2K · M_a · ‖Φ₁ - Φ₂‖_∞

    Proof using set integrals only (avoids global integrability issues).
-/
theorem arch_term_Lipschitz (K : ℝ) (hK : K > 0) (Φ₁ Φ₂ : ℝ → ℝ)
    (hcont₁ : ContinuousOn Φ₁ (Set.Icc (-K) K))
    (hcont₂ : ContinuousOn Φ₂ (Set.Icc (-K) K)) :
    |arch_term_local K Φ₁ - arch_term_local K Φ₂| ≤
      2 * K * M_a_local K * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by
  -- Let D = sup norm of difference
  set D := sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} with hD_def

  -- D ≥ 0
  have hD_nonneg : D ≥ 0 := by
    apply Real.sSup_nonneg
    intro y hy
    obtain ⟨x, _, rfl⟩ := hy
    exact abs_nonneg _

  -- D bddAbove
  have hD_bdd : BddAbove {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} :=
    D_bddAbove K hK Φ₁ Φ₂ hcont₁ hcont₂

  -- D set nonempty
  have hD_ne : {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K}.Nonempty :=
    D_nonempty K hK Φ₁ Φ₂

  -- arch_term difference = set integral of a* * (Φ₁ - Φ₂)
  have h_diff : arch_term_local K Φ₁ - arch_term_local K Φ₂ =
      ∫ ξ in Set.Icc (-K) K, a_star ξ * (Φ₁ ξ - Φ₂ ξ) := by
    unfold arch_term_local
    rw [← MeasureTheory.integral_sub]
    · congr 1; ext ξ; ring
    · -- Integrability of a_star * Φ₁ on Icc
      apply ContinuousOn.integrableOn_Icc
      exact a_star_continuous.continuousOn.mul hcont₁
    · -- Integrability of a_star * Φ₂ on Icc
      apply ContinuousOn.integrableOn_Icc
      exact a_star_continuous.continuousOn.mul hcont₂

  -- Integrability for the bound calculation
  have h_int_diff : IntegrableOn (fun ξ => a_star ξ * (Φ₁ ξ - Φ₂ ξ)) (Set.Icc (-K) K) := by
    apply ContinuousOn.integrableOn_Icc
    exact a_star_continuous.continuousOn.mul (hcont₁.sub hcont₂)

  have h_int_abs : IntegrableOn (fun ξ => |a_star ξ * (Φ₁ ξ - Φ₂ ξ)|) (Set.Icc (-K) K) := by
    apply ContinuousOn.integrableOn_Icc
    exact (a_star_continuous.continuousOn.mul (hcont₁.sub hcont₂)).abs

  -- Main calculation
  calc |arch_term_local K Φ₁ - arch_term_local K Φ₂|
      = |∫ ξ in Set.Icc (-K) K, a_star ξ * (Φ₁ ξ - Φ₂ ξ)| := by rw [h_diff]
    _ ≤ ∫ ξ in Set.Icc (-K) K, |a_star ξ * (Φ₁ ξ - Φ₂ ξ)| := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ = ∫ ξ in Set.Icc (-K) K, |a_star ξ| * |Φ₁ ξ - Φ₂ ξ| := by
        congr 1; ext ξ
        rw [abs_mul]
    _ ≤ ∫ ξ in Set.Icc (-K) K, M_a_local K * D := by
        apply MeasureTheory.setIntegral_mono_on
        · -- Integrability of |a*| |Φ₁ - Φ₂|
          apply ContinuousOn.integrableOn_Icc
          exact (a_star_continuous.abs.continuousOn).mul (ContinuousOn.abs (hcont₁.sub hcont₂))
        · -- Integrability of constant
          exact integrableOn_const (hs := measure_Icc_lt_top.ne) (hC := ENNReal.coe_ne_top)
        · exact measurableSet_Icc
        · intro ξ hξ
          apply mul_le_mul
          · -- |a_star ξ| ≤ M_a_local K
            exact abs_le_M_a_local K hK ξ hξ
          · apply le_csSup hD_bdd
            exact ⟨ξ, hξ, rfl⟩
          · exact abs_nonneg _
          · exact le_of_lt (M_a_local_pos K hK)
    _ = M_a_local K * D * volume.real (Set.Icc (-K) K) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
    _ = M_a_local K * D * (2 * K) := by rw [volume_real_Icc K hK]
    _ = 2 * K * M_a_local K * D := by ring

end Q3.Proofs.QLipschitzArchBridge

end
