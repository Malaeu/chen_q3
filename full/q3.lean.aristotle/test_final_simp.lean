/-
Debug file to test the FINAL simp in integral_P_A_eq_arch_term
This is the MOST LIKELY culprit!
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.A3_Floor_Main

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate

set_option maxHeartbeats 200000

noncomputable section

namespace Q3.Debug.FinalSimp

#print "=== FINAL SIMP TEST START ==="

-- Check what P_A unfolds to
#check P_A
#print P_A

-- Test: Does simp with P_A cause problems?
set_option maxHeartbeats 100000 in
set_option profiler true in
example (B t : ℝ) (θ : ℝ) : P_A B t θ = 2 * Real.pi * ∑' (m : ℤ), g B t (θ + m) := by
  rfl

#print "=== CHECKPOINT F1: P_A definition OK ==="

-- Test simp [P_A] alone
set_option maxHeartbeats 200000 in
set_option profiler true in
example (B t : ℝ) (x : ℝ) : (P_A B t x) * 1 = P_A B t x := by
  simp [P_A]

#print "=== CHECKPOINT F2: simp [P_A] simple OK ==="

-- Test the exact final goal pattern
-- Goal after rw [arch_term_eq_two_pi_integral_g]:
-- ∫ θ in (-1/2)..(1/2), P_A B t θ = 2 * π * ∫ ξ, a ξ * w B t ξ
-- After simp [P_A, ...]:
-- Need to show: ∫ θ, 2π * ∑' m, g(θ+m) = 2π * ∫ ξ, g ξ

-- Let's test if intervalIntegral.integral_const_mul is the issue
set_option maxHeartbeats 200000 in
set_option profiler true in
example (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in a..b, c * f x = c * ∫ x in a..b, f x := by
  exact intervalIntegral.integral_const_mul c f

#print "=== CHECKPOINT F3: integral_const_mul OK ==="

-- The REAL test: simulate the exact final simp
-- Assuming h_integral : ∫ θ, ∑' m, g(θ+m) = ∫ x, g x
-- Goal: ∫ θ, P_A θ = 2π * ∫ ξ, a ξ * w ξ

-- Since P_A θ = 2π * ∑' m, g(θ+m), we need:
-- ∫ θ, 2π * ∑' m, g(θ+m) = 2π * ∫ x, g x
-- = 2π * ∫ θ, ∑' m, g(θ+m)  (by integral_const_mul)
-- = 2π * ∫ x, g x           (by h_integral)

-- And g = a * w, so this should match RHS

set_option maxHeartbeats 300000 in
set_option profiler true in
lemma test_final_step (B t : ℝ) (h_integral : ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m) = ∫ x, g B t x) :
    ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ = 2 * Real.pi * ∫ ξ, g B t ξ := by
  -- Don't use simp [P_A], use rw instead
  unfold P_A
  rw [intervalIntegral.integral_const_mul]
  rw [h_integral]

#print "=== CHECKPOINT F4: test_final_step without simp OK ==="

-- NOW test with simp
set_option maxHeartbeats 600000 in
set_option profiler true in
lemma test_final_step_simp (B t : ℝ) (h_integral : ∫ θ in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, g B t (θ + m) = ∫ x, g B t x) :
    ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ = 2 * Real.pi * ∫ ξ, g B t ξ := by
  simp only [P_A, intervalIntegral.integral_const_mul, h_integral]

#print "=== CHECKPOINT F5: test_final_step WITH simp OK ==="

end Q3.Debug.FinalSimp

#print "=== FINAL SIMP TEST COMPLETE ==="
