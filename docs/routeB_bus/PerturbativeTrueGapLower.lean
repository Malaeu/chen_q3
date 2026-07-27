import Mathlib

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- If the lower true endpoint can move upward by `errLow`, the upper true
endpoint can move downward by `errHigh`, and the model gap has enough budget
left after both errors, then the remaining floor is a lower bound for the true
gap.  This is scalar bookkeeping; it does not prove either endpoint estimate. -/
theorem true_gap_lower_of_endpoint_perturbation_budget
    {modelLow modelHigh trueLow trueHigh errLow errHigh floor : ℝ}
    (hlow : trueLow ≤ modelLow + errLow)
    (hhigh : modelHigh - errHigh ≤ trueHigh)
    (hbudget : floor + errLow + errHigh ≤ modelHigh - modelLow) :
    floor ≤ trueHigh - trueLow := by
  linarith

/-- Two absolute endpoint perturbation bounds feed the one-sided gap budget. -/
theorem true_gap_lower_of_abs_endpoint_perturbations
    {modelLow modelHigh trueLow trueHigh errLow errHigh floor : ℝ}
    (hlow : |trueLow - modelLow| ≤ errLow)
    (hhigh : |trueHigh - modelHigh| ≤ errHigh)
    (hbudget : floor + errLow + errHigh ≤ modelHigh - modelLow) :
    floor ≤ trueHigh - trueLow := by
  have hlow' : trueLow ≤ modelLow + errLow := by
    have := (abs_le.mp hlow).2
    linarith
  have hhigh' : modelHigh - errHigh ≤ trueHigh := by
    have := (abs_le.mp hhigh).1
    linarith
  exact
    true_gap_lower_of_endpoint_perturbation_budget
      hlow' hhigh' hbudget

/-- A positive surviving floor gives strict positivity of the true gap. -/
theorem true_gap_pos_of_abs_endpoint_perturbations
    {modelLow modelHigh trueLow trueHigh errLow errHigh floor : ℝ}
    (hfloor : 0 < floor)
    (hlow : |trueLow - modelLow| ≤ errLow)
    (hhigh : |trueHigh - modelHigh| ≤ errHigh)
    (hbudget : floor + errLow + errHigh ≤ modelHigh - modelLow) :
    0 < trueHigh - trueLow :=
  hfloor.trans_le
    (true_gap_lower_of_abs_endpoint_perturbations hlow hhigh hbudget)

/-- Filter-level wrapper.  `[NeBot l]` excludes a certificate obtained only
from the bottom filter. -/
theorem eventually_true_gap_lower_of_abs_endpoint_perturbations
    {ι : Type*} {l : Filter ι} [NeBot l]
    (modelLow modelHigh trueLow trueHigh errLow errHigh floor : ι → ℝ)
    (hlow : ∀ᶠ i in l,
      |trueLow i - modelLow i| ≤ errLow i)
    (hhigh : ∀ᶠ i in l,
      |trueHigh i - modelHigh i| ≤ errHigh i)
    (hbudget : ∀ᶠ i in l,
      floor i + errLow i + errHigh i ≤ modelHigh i - modelLow i) :
    ∀ᶠ i in l, floor i ≤ trueHigh i - trueLow i := by
  filter_upwards [hlow, hhigh, hbudget] with i hli hhi hbi
  exact true_gap_lower_of_abs_endpoint_perturbations hli hhi hbi

/-- A positive model gap by itself says nothing about the true gap when no
endpoint perturbation control is supplied. -/
theorem positive_model_gap_without_endpoint_control_does_not_force_true_gap :
    let modelLow : ℝ := 0
    let modelHigh : ℝ := 1
    let trueLow : ℝ := 0
    let trueHigh : ℝ := 0
    0 < modelHigh - modelLow ∧ ¬ 0 < trueHigh - trueLow := by
  norm_num

/-- Endpoint errors can consume the entire model gap.  Hence strict positivity
requires a strictly positive surviving budget, not merely a positive model
gap and non-strict perturbation estimates. -/
theorem endpoint_errors_can_consume_entire_model_gap :
    let modelLow : ℝ := 0
    let modelHigh : ℝ := 1
    let trueLow : ℝ := 0
    let trueHigh : ℝ := 0
    let errLow : ℝ := 0
    let errHigh : ℝ := 1
    |trueLow - modelLow| ≤ errLow ∧
      |trueHigh - modelHigh| ≤ errHigh ∧
      errLow + errHigh = modelHigh - modelLow ∧
      trueHigh - trueLow = 0 := by
  norm_num

#print axioms true_gap_lower_of_endpoint_perturbation_budget
#print axioms true_gap_lower_of_abs_endpoint_perturbations
#print axioms true_gap_pos_of_abs_endpoint_perturbations
#print axioms eventually_true_gap_lower_of_abs_endpoint_perturbations
#print axioms positive_model_gap_without_endpoint_control_does_not_force_true_gap
#print axioms endpoint_errors_can_consume_entire_model_gap

end Q3.RouteB
