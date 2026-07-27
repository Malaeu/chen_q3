import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- The completion factor ratified in the D0.7e owner input. -/
def gammaC (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
    (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The owner-input completed trial tracker, abstracting only its raw entire
trial factor. -/
def completedTrialTracker (Fplus : ℂ → ℂ) (z : ℂ) : ℂ :=
  gammaC ((1 / 2 : ℂ) + Complex.I * z) * Fplus z

@[simp] theorem gammaC_one : gammaC 1 = 0 := by
  simp [gammaC]

@[simp] theorem centered_argument_neg_I_div_two :
    (1 / 2 : ℂ) + Complex.I * (-Complex.I / 2) = 1 := by
  calc
    (1 / 2 : ℂ) + Complex.I * (-Complex.I / 2) =
        (1 / 2 : ℂ) - (Complex.I * Complex.I) / 2 := by ring
    _ = 1 := by rw [Complex.I_mul_I]; ring

/-- The completed tracker has a fixed non-real zero, independently of the raw
trial transform.  Hence it cannot satisfy the current global H2 contract. -/
theorem completedTrialTracker_neg_I_div_two_zero (Fplus : ℂ → ℂ) :
    completedTrialTracker Fplus (-Complex.I / 2) = 0 := by
  unfold completedTrialTracker
  rw [centered_argument_neg_I_div_two, gammaC_one, zero_mul]

theorem neg_I_div_two_not_real :
    (-Complex.I / 2 : ℂ).im ≠ 0 := by
  norm_num

#print axioms completedTrialTracker_neg_I_div_two_zero
#print axioms neg_I_div_two_not_real

end Q3.RouteB
