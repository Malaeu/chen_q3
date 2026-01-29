/-
Parameter bridge between A1 heat kernel and A3 window.
-/

import Q3.Proofs.A3_Floor_Bounds

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3

/-- A1 heat parameter corresponding to A3 t_sym via exp(-x^2/(4t0)) = exp(-4π^2 t_sym x^2). -/
noncomputable def t0_A1 : ℝ := 1 / (16 * Real.pi ^ 2 * t_sym)

lemma t0_A1_pos : t0_A1 > 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have ht : (0 : ℝ) < t_sym := by norm_num [t_sym]
  have hden : 0 < 16 * Real.pi ^ 2 * t_sym := by
    have hpi2 : 0 < Real.pi ^ 2 := by
      have : (0 : ℝ) < Real.pi := hpi
      exact sq_pos_of_pos this
    nlinarith [hpi2, ht]
  unfold t0_A1
  exact one_div_pos.mpr hden

lemma exp_reparam (x : ℝ) :
    Real.exp (-x^2 / (4 * t0_A1)) = Real.exp (-4 * Real.pi ^ 2 * t_sym * x^2) := by
  have hden : (16 * Real.pi ^ 2 * t_sym) ≠ 0 := by
    have hden_pos : (0 : ℝ) < 16 * Real.pi ^ 2 * t_sym := by
      have hpi2 : 0 < Real.pi ^ 2 := by
        have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
        exact sq_pos_of_pos hpi
      have ht : (0 : ℝ) < t_sym := by norm_num [t_sym]
      nlinarith [hpi2, ht]
    exact ne_of_gt hden_pos
  have h :
      -x^2 / (4 * t0_A1) = -4 * Real.pi ^ 2 * t_sym * x^2 := by
    unfold t0_A1
    field_simp [hden]
    ring
  simp [h]

lemma exp_reparam_mul (x : ℝ) :
    Real.exp (-x^2 / (t0_A1 * 4)) =
      Real.exp (-(t_sym * (Real.pi ^ 2 * (x^2 * 4)))) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using (exp_reparam x)

end Q3
