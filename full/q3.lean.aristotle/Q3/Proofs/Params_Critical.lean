import Mathlib

/-!
Critical one-scale parameters (`t = 3/20`)
=========================================

This module centralizes the *single-scale* parameter choice

* `t_critical = 3/20`
* `t0_critical = 1/(16π² t_critical)` so that
  `exp(-x^2/(4*t0_critical)) = exp(-4π² t_critical x^2)`.

It is intentionally independent of the legacy `t_sym` / `t_rkhs_cap` two-scale setup.
-/

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3

/-- Critical heat parameter where the numerical scan crosses to `Q ≥ 0`. -/
def t_critical : ℝ := 3 / 20

/-- A1 heat parameter corresponding to `t_critical` via `exp(-x^2/(4t0)) = exp(-4π^2 t x^2)`. -/
noncomputable def t0_critical : ℝ := 1 / (16 * Real.pi ^ 2 * t_critical)

lemma t_critical_pos : t_critical > 0 := by
  norm_num [t_critical]

lemma t0_critical_pos : t0_critical > 0 := by
  have ht : (0 : ℝ) < t_critical := t_critical_pos
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hden : 0 < 16 * Real.pi ^ 2 * t_critical := by nlinarith [hpi2, ht]
  simpa [t0_critical] using (one_div_pos.mpr hden)

lemma exp_reparam_critical (x : ℝ) :
    Real.exp (-x^2 / (4 * t0_critical)) = Real.exp (-4 * Real.pi ^ 2 * t_critical * x^2) := by
  have hden : (16 * Real.pi ^ 2 * t_critical) ≠ 0 := by
    have hden_pos : (0 : ℝ) < 16 * Real.pi ^ 2 * t_critical := by
      have ht : (0 : ℝ) < t_critical := t_critical_pos
      have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      nlinarith [hpi2, ht]
    exact ne_of_gt hden_pos
  have h :
      -x^2 / (4 * t0_critical) = -4 * Real.pi ^ 2 * t_critical * x^2 := by
    unfold t0_critical
    field_simp [hden]
    ring
  simp [h]

end Q3
