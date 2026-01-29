/-
Sandbox Test: Pure Mathlib, NO custom axioms
-/

import Mathlib

open Real

/-! ## Test theorems — prove these using Mathlib -/

/-- Simple: 2 + 2 = 4 -/
theorem two_plus_two : (2 : ℕ) + 2 = 4 := by sorry

/-- Medium: For positive reals, x + x > x -/
theorem add_self_gt (x : ℝ) (hx : x > 0) : x + x > x := by sorry

/-- Medium: Limit of 1/n as n → ∞ is 0 -/
theorem inv_tendsto_zero : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop (nhds 0) := by sorry
