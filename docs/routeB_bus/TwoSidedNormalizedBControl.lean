import Mathlib

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- The Contract-v2 two-sided normalized `b` bound gives pointwise
nonvanishing, the direct polynomial upper bound, and the scale-dependent
reciprocal bound. It does not assert a uniform positive lower bound for
`|b|`. -/
theorem two_sided_normalized_b_control_pointwise
    {scale b c_b C_b q_b : ℝ}
    (hscale : 0 < scale)
    (hcb : 0 < c_b)
    (hlower : c_b ≤ |b| * scale ^ (-q_b))
    (hupper : |b| * scale ^ (-q_b) ≤ C_b) :
    b ≠ 0 ∧
      |b| ≤ C_b * scale ^ q_b ∧
      |b|⁻¹ ≤ c_b⁻¹ * scale ^ (-q_b) := by
  have hsq :
      0 < scale ^ q_b :=
    Real.rpow_pos_of_pos hscale _
  have hcancel :
      scale ^ (-q_b) * scale ^ q_b = 1 := by
    rw [Real.rpow_neg hscale.le]
    exact inv_mul_cancel₀ hsq.ne'
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    simp at hlower
    linarith
  have hlower' :
      c_b * scale ^ q_b ≤ |b| := by
    have h :=
      mul_le_mul_of_nonneg_right hlower hsq.le
    calc
      c_b * scale ^ q_b ≤
          (|b| * scale ^ (-q_b)) * scale ^ q_b :=
        h
      _ = |b| := by
        rw [mul_assoc, hcancel, mul_one]
  have hupper' :
      |b| ≤ C_b * scale ^ q_b := by
    have h :=
      mul_le_mul_of_nonneg_right hupper hsq.le
    calc
      |b| =
          (|b| * scale ^ (-q_b)) * scale ^ q_b := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ C_b * scale ^ q_b :=
        h
  have hrecip_raw :
      1 / |b| ≤ 1 / (c_b * scale ^ q_b) :=
    one_div_le_one_div_of_le
      (mul_pos hcb hsq) hlower'
  have hrecip :
      |b|⁻¹ ≤ c_b⁻¹ * scale ^ (-q_b) := by
    simpa only [
      one_div,
      mul_inv,
      Real.rpow_neg hscale.le,
      mul_comm
    ] using hrecip_raw
  exact ⟨hb0, hupper', hrecip⟩

/-- Filter version of the Contract-v2 two-sided normalized `b` control.
`[NeBot l]` excludes a vacuous bottom-filter certificate. -/
theorem two_sided_normalized_b_control_eventually
    {ι : Type*} {l : Filter ι} [NeBot l]
    (scale b : ι → ℝ)
    (c_b C_b q_b : ℝ)
    (hcb : 0 < c_b)
    (hscale : ∀ᶠ i in l, 0 < scale i)
    (hlower : ∀ᶠ i in l,
      c_b ≤ |b i| * scale i ^ (-q_b))
    (hupper : ∀ᶠ i in l,
      |b i| * scale i ^ (-q_b) ≤ C_b) :
    (∀ᶠ i in l, b i ≠ 0) ∧
      (∀ᶠ i in l,
        |b i| ≤ C_b * scale i ^ q_b) ∧
      (∀ᶠ i in l,
        |b i|⁻¹ ≤ c_b⁻¹ * scale i ^ (-q_b)) := by
  have hcontrol : ∀ᶠ i in l,
      b i ≠ 0 ∧
        |b i| ≤ C_b * scale i ^ q_b ∧
        |b i|⁻¹ ≤ c_b⁻¹ * scale i ^ (-q_b) := by
    filter_upwards
      [hscale, hlower, hupper] with
      i hsi hli hui
    exact
      two_sided_normalized_b_control_pointwise
        hsi hcb hli hui
  exact
    ⟨hcontrol.mono (fun _ h => h.1),
      hcontrol.mono (fun _ h => h.2.1),
      hcontrol.mono (fun _ h => h.2.2)⟩

/-- A scale-dependent reciprocal `b` estimate transfers an absolute
nonnegative error bound to the corresponding normalized error bound. -/
theorem normalized_error_le_of_reciprocal_b_control
    {scale b err c_b q_b : ℝ}
    (herr : 0 ≤ err)
    (hrecip :
      |b|⁻¹ ≤ c_b⁻¹ * scale ^ (-q_b)) :
    err / |b| ≤
      c_b⁻¹ * scale ^ (-q_b) * err := by
  rw [div_eq_mul_inv]
  simpa only [
    mul_comm,
    mul_left_comm,
    mul_assoc
  ] using
    (mul_le_mul_of_nonneg_left hrecip herr)

#print axioms two_sided_normalized_b_control_pointwise
#print axioms two_sided_normalized_b_control_eventually
#print axioms normalized_error_le_of_reciprocal_b_control

end Q3.RouteB
