import Mathlib

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- The scalar values realized by `A = diag(0,1)` and
`u = (e₁+e₂)/sqrt 2` falsify the registered generic bridge
`sqrt(alpha/DeltaE) <= eta/DeltaE`. -/
theorem residual_bridge_direction_counterexample :
    ¬ Real.sqrt ((1 / 2 : ℝ) / 1) ≤ (1 / 2 : ℝ) / 1 := by
  intro h
  have hsqrt : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = 1 / 2 :=
    Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg _
  have h' : Real.sqrt (1 / 2 : ℝ) ≤ 1 / 2 := by
    simpa only [div_one] using h
  nlinarith

/-- A cofinal scale on which `|b| * sqrt(lambda)` is exactly one while `b`
tends to zero. -/
def lowerProductB (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

def lowerProductLambda (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2

theorem lowerProductB_tendsto_zero :
    Tendsto lowerProductB atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem lowerProductB_sqrt_lambda_eq_one (n : ℕ) :
    |lowerProductB n| * Real.sqrt (lowerProductLambda n) = 1 := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  rw [lowerProductB, lowerProductLambda, Real.sqrt_sq_eq_abs,
    abs_of_pos hpos, abs_of_pos (one_div_pos.mpr hpos)]
  field_simp

/-- The corrected exponent margin in Contract v2 is strictly negative. -/
theorem safe_rate_exponent_neg
    {q_b r_alpha r_Delta : ℝ}
    (hmargin : r_Delta - r_alpha > 2 * q_b + 1) :
    q_b + (1 + r_alpha - r_Delta) / 2 < 0 := by
  linarith

/-- A negative real power along the natural cofinal scale tends to zero. -/
theorem tendsto_nat_rpow_zero_of_neg {p : ℝ} (hp : p < 0) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (neg_pos.mpr hp)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  ext n
  congr 1
  linarith

/-- Contract-v2's strict rate margin gives decay of its polynomial exponent.
This is only the generic exponent core, not the exact SafeRateAssembly. -/
theorem safe_rate_polynomial_core
    {q_b r_alpha r_Delta : ℝ}
    (hmargin : r_Delta - r_alpha > 2 * q_b + 1) :
    Tendsto
      (fun n : ℕ => (n : ℝ) ^ (q_b + (1 + r_alpha - r_Delta) / 2))
      atTop (𝓝 0) :=
  tendsto_nat_rpow_zero_of_neg (safe_rate_exponent_neg hmargin)

#print axioms residual_bridge_direction_counterexample
#print axioms lowerProductB_tendsto_zero
#print axioms lowerProductB_sqrt_lambda_eq_one
#print axioms safe_rate_polynomial_core

end Q3.RouteB
