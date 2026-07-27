import Q3.Proofs.RouteB.D0CenteredCriticalMoment

set_option linter.mathlibStandardSet false

open Complex
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Exact no-go for a generic centered-density square factorization

`centeredTrialDensity` is linear in the projected coefficient row.  The
current `CoefficientFamily` contract imposes no autocorrelation/Toeplitz
positivity condition.  The exact one-mode row below therefore gives a
positive centered density and kills any generic theorem asserting that every
such density is the negative of a squared norm.
-/

/-- The exact admissible pair `(m,N)=(2,0)`. -/
def centeredDensityNoGoIndex : PairIndex where
  m := 2
  N := 0
  hm := by norm_num

/-- A coefficient row supported only at the constant mode. -/
def centeredDensityPositiveConstantRow : CoefficientFamily where
  kTrial := fun _ n => if n = 0 then 1 else 0

/-- The centered density of the positive constant row is strictly positive at
zero.  This is an exact algebraic counterexample to a generic
`centeredTrialDensity = -(1/sqrt L) * ‖amplitude‖²` theorem. -/
theorem centeredTrialDensity_positive_constant_counterexample :
    0 <
      (centeredTrialDensity centeredDensityPositiveConstantRow
        centeredDensityNoGoIndex 0).re := by
  simp [centeredTrialDensity, centeredDensityPositiveConstantRow,
    centeredDensityNoGoIndex, modeSet, L_m, logLength]
  exact Real.log_pos (show (1 : ℝ) < 2 by norm_num)

#print axioms centeredTrialDensity_positive_constant_counterexample

end Q3.RouteB.D0Pstar
