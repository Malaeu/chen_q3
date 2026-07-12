import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace Q3.RouteB

/-- A finite Fourier trial on one logarithmic period of length `L`. -/
def finiteLogFourierTrial
    (L : ℝ) (S : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt L : ℂ)⁻¹ *
    ∑ n ∈ S, c n *
      Complex.exp (((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ)) * (x : ℂ))

/-- The central Mellin/Fourier value is the constant Fourier mode. -/
theorem Fplus_zero_eq_sqrt_mul_c0
    (L : ℝ) (S : Finset ℤ) (c : ℤ → ℂ)
    (hL : 0 < L) (h0 : 0 ∈ S) :
    (∫ x : ℝ in 0..L, finiteLogFourierTrial L S c x) =
      (Real.sqrt L : ℂ) * c 0 := by
  have hmode : ∀ n : ℤ,
      (∫ x : ℝ in 0..L,
        Complex.exp (((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ)) *
          (x : ℂ))) = if n = 0 then (L : ℂ) else 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hcoeff :
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ) ≠ 0 := by
        have htwoPi : (2 * (Real.pi : ℂ)) ≠ 0 :=
          mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        exact div_ne_zero (mul_ne_zero hnC (mul_ne_zero htwoPi Complex.I_ne_zero)) hLc
      rw [integral_exp_mul_complex hcoeff]
      have hcancel :
          ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ)) * (L : ℂ) =
            (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp [hLc]
      rw [hcancel, Complex.exp_int_mul_two_pi_mul_I]
      simp [hn]
  unfold finiteLogFourierTrial
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul, hmode]
    simp [h0]
    have hs : (Real.sqrt L : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
    field_simp [hs]
    have hsquare : (Real.sqrt L : ℂ) ^ 2 = (L : ℂ) := by
      norm_cast
      exact Real.sq_sqrt hL.le
    rw [hsquare]
    ring
  · intro n _hn
    have hcont : Continuous (fun x : ℝ =>
        c n * Complex.exp
          (((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ)) * (x : ℂ))) := by
      fun_prop
    exact hcont.intervalIntegrable 0 L

#print axioms Fplus_zero_eq_sqrt_mul_c0

end Q3.RouteB
