/-
Debug file to find hanging proof in Rayleigh_Q_identification.lean
Strategy: Copy sections one by one and see which one times out
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.ShiftedWindows
import A3_FLOOR_v22_stage4_floor

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate

-- Use a reasonable heartbeat limit to detect issues
set_option maxHeartbeats 400000

noncomputable section

namespace Q3.Debug

#print "=== CHECKPOINT 1: Imports successful ==="

-- Copy definitions from Rayleigh_Q_identification.lean
noncomputable def T_P_comp_shift (K B t tau : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℂ :=
  fun i j =>
    ∑ n : Q3.Nodes K,
      ((Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n)) : ℂ) *
        Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)

noncomputable def T_P_comp_real_shift (K B t tau : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ :=
  fun i j => (T_P_comp_shift K B t tau M i j).re

#print "=== CHECKPOINT 2: Definitions successful ==="

end Q3.Debug

namespace Q3.Debug.Toeplitz

-- Test ToeplitzEntry_diag
lemma ToeplitzEntry_diag (P : ℝ → ℝ) (i : ℕ) :
    RayleighFourier.ToeplitzEntry P i i = ∫ θ in (-1/2 : ℝ)..(1/2), (P θ : ℂ) := by
  simp only [RayleighFourier.ToeplitzEntry]
  congr 1
  ext θ
  simp [Complex.exp_zero]

#print "=== CHECKPOINT 3: ToeplitzEntry_diag successful ==="

lemma ToeplitzEntry_diag_re (P : ℝ → ℝ) (_hP : Continuous P) (i : ℕ) :
    (RayleighFourier.ToeplitzEntry P i i).re = ∫ θ in (-1/2 : ℝ)..(1/2), P θ := by
  rw [ToeplitzEntry_diag]
  rw [intervalIntegral.integral_ofReal]
  simp

#print "=== CHECKPOINT 4: ToeplitzEntry_diag_re successful ==="

end Q3.Debug.Toeplitz

namespace Q3.Debug.PrimeVec

open Q3.Proofs.RayleighQId in
lemma fourier_index_i0 (M : ℕ) : Q3.fourier_index M (i0 M) = 0 := by
  simp [Q3.fourier_index, i0]

#print "=== CHECKPOINT 5: fourier_index_i0 successful ==="

open Q3.Proofs.RayleighQId in
lemma prime_vec_i0 (M : ℕ) (ξ : ℝ) :
    Q3.prime_vec M ξ (i0 M) = (1 / Real.sqrt (2 * M + 1 : ℝ) : ℂ) := by
  unfold Q3.prime_vec
  simp only [fourier_index_i0, Int.cast_zero, mul_zero]
  simp only [zero_mul, Complex.exp_zero, mul_one]

#print "=== CHECKPOINT 6: prime_vec_i0 successful ==="

end Q3.Debug.PrimeVec

namespace Q3.Debug.Support

-- Test w_support
lemma w_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : w B t ξ = 0 := by
  simp only [w]
  have h1 : 1 - |ξ| / B < 0 := by
    have : 1 < |ξ| / B := by
      rw [one_lt_div hB]
      exact h
    linarith
  rw [max_eq_left (le_of_lt h1)]
  ring

#print "=== CHECKPOINT 7: w_support successful ==="

lemma g_support (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) : g B t ξ = 0 := by
  simp only [g, w_support B t ξ hB h, mul_zero]

#print "=== CHECKPOINT 8: g_support successful ==="

lemma continuous_w (B t : ℝ) : Continuous (fun ξ => w B t ξ) := by
  unfold w
  have h_lin : Continuous (fun ξ => 1 - |ξ| / B) := by
    have h_abs : Continuous (fun ξ => |ξ|) := by simpa using (continuous_abs : Continuous fun ξ : ℝ => |ξ|)
    have h_div : Continuous (fun ξ => |ξ| / B) := by
      simpa [div_eq_mul_inv] using h_abs.mul continuous_const
    exact continuous_const.sub h_div
  have h_max : Continuous (fun ξ => max (0 : ℝ) (1 - |ξ| / B)) :=
    (continuous_const).max h_lin
  have h_pow : Continuous (fun ξ => ξ ^ 2) := continuous_pow 2
  have h_poly : Continuous (fun ξ => (-4 * Real.pi ^ 2 * t) * (ξ ^ 2)) := continuous_const.mul h_pow
  have h_exp : Continuous (fun ξ => Real.exp (-4 * Real.pi ^ 2 * t * ξ ^ 2)) := by
    simpa [mul_assoc] using (Real.continuous_exp.comp h_poly)
  exact h_max.mul h_exp

#print "=== CHECKPOINT 9: continuous_w successful ==="

lemma continuous_g (B t : ℝ) : Continuous (fun ξ => g B t ξ) := by
  unfold g
  have ha : Continuous (fun ξ => Q3.a ξ) := by
    have hpi : (2 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
    have h :
        (fun ξ => Q3.a ξ) = fun ξ => (1 / (2 * Real.pi)) * Q3.a_star ξ := by
      funext ξ
      calc
        (1 / (2 * Real.pi)) * Q3.a_star ξ
            = (1 / (2 * Real.pi)) * (2 * Real.pi * Q3.a ξ) := by simp [Q3.a_star]
        _ = Q3.a ξ := by field_simp [hpi]; ring
    simpa [h] using (Q3.a_star_continuous.const_mul (1 / (2 * Real.pi)))
  exact ha.mul (continuous_w B t)

#print "=== CHECKPOINT 10: continuous_g successful ==="

end Q3.Debug.Support

#print "=== ALL CHECKPOINTS PASSED - Testing periodization next ==="

-- Now test the heavy periodization theorem separately
namespace Q3.Debug.Periodization

lemma w_eq_fejer_heat_window (B t ξ : ℝ) : w B t ξ = Q3.fejer_heat_window B t ξ := by
  simp only [w, Q3.fejer_heat_window]

#print "=== CHECKPOINT 11: w_eq_fejer_heat_window successful ==="

-- This is likely the problematic one - test with lower heartbeats first
set_option maxHeartbeats 200000 in
lemma g_shift_zero_of_large_m (B t θ : ℝ) (m : ℤ) (hB : 0 < B)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : (⌈B⌉ : ℤ) + 1 < |m|) : g B t (θ + m) = 0 := by
  apply Q3.Debug.Support.g_support B t (θ + m) hB
  have h1 : (B : ℝ) + 1 ≤ |m| := by
    have : (⌈B⌉ : ℝ) + 1 < |m| := by exact_mod_cast hm
    have hceil : B ≤ ⌈B⌉ := Int.le_ceil B
    linarith
  have hθ_abs : |θ| ≤ 1/2 := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  have h_abs_m : |(m : ℝ)| = |m| := by simp only [Int.cast_abs]
  have h_tri : (|(m : ℝ)| - |θ|) ≤ |θ + (m : ℝ)| := by
    have h1 := abs_sub_abs_le_abs_sub (m : ℝ) (-θ)
    simp only [abs_neg, sub_neg_eq_add] at h1
    calc |(m : ℝ)| - |θ| ≤ |(m : ℝ) + θ| := h1
      _ = |θ + (m : ℝ)| := by ring_nf
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

#print "=== CHECKPOINT 12: g_shift_zero_of_large_m successful ==="

end Q3.Debug.Periodization

#print "=== DEBUG FILE COMPLETE ==="
