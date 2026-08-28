import Mathlib

open Set

noncomputable section

namespace Q3.RouteB

/-- The exact finite-parameter mass of the smooth oriented source model from
Goal 058.  This definition does not identify the model with the literal prime
source; their difference remains the Stieltjes discrepancy. -/
def goal058OrientedSmoothModelMass (r : ℝ) : ℝ :=
  (2 / Real.pi) * (1 - r) * (3 - 2 * r)

/-- On the cofinal parameter range the smooth model mass is bounded above by
`6 / pi`.  The theorem is an upper bound, not a finite-parameter equality. -/
theorem goal058OrientedSmoothModelMass_le_six_div_pi
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    goal058OrientedSmoothModelMass r ≤ 6 / Real.pi := by
  rw [goal058OrientedSmoothModelMass]
  rw [show 2 / Real.pi * (1 - r) * (3 - 2 * r) =
      (2 * (1 - r) * (3 - 2 * r)) / Real.pi by ring]
  apply (div_le_div_iff_of_pos_right Real.pi_pos).2
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]

/-- The smooth model mass decreases as `r` increases on `[0, 1]`. -/
theorem goal058OrientedSmoothModelMass_antitoneOn :
    AntitoneOn goal058OrientedSmoothModelMass (Set.Icc 0 1) := by
  intro r hr s hs hrs
  rw [goal058OrientedSmoothModelMass, goal058OrientedSmoothModelMass]
  rw [show 2 / Real.pi * (1 - s) * (3 - 2 * s) =
      (2 * (1 - s) * (3 - 2 * s)) / Real.pi by ring,
    show 2 / Real.pi * (1 - r) * (3 - 2 * r) =
      (2 * (1 - r) * (3 - 2 * r)) / Real.pi by ring]
  apply (div_le_div_iff_of_pos_right Real.pi_pos).2
  have hfactor : 0 ≤ 5 - 2 * (r + s) := by
    nlinarith [hr.2, hs.2]
  have hprod : 0 ≤ (s - r) * (5 - 2 * (r + s)) :=
    mul_nonneg (sub_nonneg.mpr hrs) hfactor
  nlinarith

#print axioms goal058OrientedSmoothModelMass_le_six_div_pi
#print axioms goal058OrientedSmoothModelMass_antitoneOn

end Q3.RouteB
