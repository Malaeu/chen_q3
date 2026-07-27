import Q3.Proofs.RouteB.CompletedTrackerScope
import Q3.Proofs.RouteB.ClassicalXiInterface

set_option linter.mathlibStandardSet false

open Complex Set

noncomputable section
namespace Q3.RouteB

/-- The SOFT completion factor.  For a positive real scale `lambda`, the
notation `lambda^(-i z)` is fixed to the single-valued exponential
`exp((-i z) log lambda)`. -/
def gammaSoft (lambda : ℝ) (z : ℂ) : ℂ :=
  gammaC ((1 / 2 : ℂ) + Complex.I * z) *
    Complex.exp ((-Complex.I * z) * Real.log lambda)

theorem centered_argument_re_pos {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    0 < ((1 / 2 : ℂ) + Complex.I * z).re := by
  change |z.im| < 1 / 2 at hz
  rw [centered_argument_re]
  have h := (abs_lt.mp hz).2
  linarith

theorem centered_argument_re_lt_one {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    ((1 / 2 : ℂ) + Complex.I * z).re < 1 := by
  change |z.im| < 1 / 2 at hz
  rw [centered_argument_re]
  have h := (abs_lt.mp hz).1
  linarith

/-- On the open centered critical strip, the completed factor `gammaC` has no
zeros.  The boundary zeros at `z = plus or minus i/2` are deliberately outside the
domain. -/
theorem gammaC_centered_ne_zero {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    gammaC ((1 / 2 : ℂ) + Complex.I * z) ≠ 0 := by
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * z
  have hspos : 0 < s.re := centered_argument_re_pos hz
  have hslt : s.re < 1 := centered_argument_re_lt_one hz
  have hs0 : s ≠ 0 := by
    intro h
    have hre : s.re = 0 := congrArg Complex.re h
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hs_eq : s = 1 := sub_eq_zero.mp h
    have hre : s.re = 1 := congrArg Complex.re hs_eq
    linarith
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
  have hGamma : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simpa using half_pos hspos
  unfold gammaC
  change (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) *
      Complex.Gamma (s / 2) ≠ 0
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1) hpi) hGamma

/-- Source-locked zero-freeness of the full SOFT completion factor on the
open centered critical strip. -/
theorem gammaSoft_ne_zero {lambda : ℝ} (hlambda : 0 < lambda) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    gammaSoft lambda z ≠ 0 := by
  by_cases hpositive : 0 < lambda
  · unfold gammaSoft
    exact mul_ne_zero (gammaC_centered_ne_zero hz) (Complex.exp_ne_zero _)
  · exact (hpositive hlambda).elim

#print axioms gammaC_centered_ne_zero
#print axioms gammaSoft_ne_zero

end Q3.RouteB
