/-
Debug file to test HasSum parts of integral_P_A_eq_arch_term
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.ShiftedWindows
import A3_FLOOR_v22_stage4_floor

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate

set_option maxHeartbeats 400000

noncomputable section

namespace Q3.Debug.HasSum

#print "=== HASSUM TEST START ==="

-- Needed lemmas
lemma continuous_g (B t : ℝ) : Continuous (fun ξ => g B t ξ) := by
  unfold g w
  continuity

lemma g_integrable (B t : ℝ) (hB : 0 < B) : Integrable (fun ξ => g B t ξ) := by
  have hsupp : Function.support (fun ξ => g B t ξ) ⊆ Set.Icc (-B) B := by
    refine (Function.support_subset_iff'.2 ?_)
    intro ξ hξ
    unfold g w
    by_contra hle
    push_neg at hle
    have hle' : |ξ| ≤ B := le_of_not_gt hle
    have : ξ ∈ Set.Icc (-B) B := abs_le.mp hle'
    have h1 : 1 - |ξ| / B ≥ 0 := by
      have : |ξ| / B ≤ 1 := by rw [div_le_one hB]; exact hle'
      linarith
    have hne : max 0 (1 - |ξ| / B) ≠ 0 := by
      rw [max_eq_right h1]
      linarith [hle']
    simp only [ne_eq, mul_eq_zero, not_or] at hξ
    exact hξ.2 (by simp [max_eq_right h1, mul_eq_zero, Real.exp_ne_zero])
  have hcompact : HasCompactSupport (fun ξ => g B t ξ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  exact (continuous_g B t).integrable_of_hasCompactSupport hcompact

#print "=== CHECKPOINT HS1: g_integrable OK ==="

-- Test hasSum_intervalIntegral
set_option maxHeartbeats 600000 in
set_option profiler true in
lemma hsum_base_test (B t : ℝ) (hB : 0 < B) :
    HasSum (fun n : ℤ =>
        ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, g B t x)
      (∫ x, g B t x) := by
  have hint := g_integrable B t hB
  simpa using (MeasureTheory.Integrable.hasSum_intervalIntegral hint (-1/2 : ℝ))

#print "=== CHECKPOINT HS2: hsum_base_test OK ==="

-- Test the conversion
set_option maxHeartbeats 600000 in
set_option profiler true in
lemma hsum_convert_test (B t : ℝ) (hB : 0 < B) :
    HasSum (fun n : ℤ => ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + (n : ℝ)))
      (∫ x, g B t x) := by
  have hsum_base := hsum_base_test B t hB
  refine (HasSum.congr_fun hsum_base ?_)
  intro n
  have hcomp :=
    intervalIntegral.integral_comp_add_right (f:=fun x => g B t x) (d:=(n : ℝ))
      (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ))
  convert hcomp using 1 <;> ring

#print "=== CHECKPOINT HS3: hsum_convert_test OK ==="

end Q3.Debug.HasSum

#print "=== HASSUM TEST COMPLETE ==="
