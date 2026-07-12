import Q3.Proofs.RouteB.WeightedSpectralTempleCore

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- A Temple residual-square envelope carrying two copies of the common
exponential envelope, divided by a true-gap lower envelope carrying one copy,
yields the single-envelope SafeAlphaUpper rate. -/
theorem safe_alpha_envelope_of_temple_residual_gap_bounds
    {scale envelope alpha etaSq gap C_eta c_Delta r_eta r_Delta : ℝ}
    (hscale : 0 < scale)
    (henvelope : 0 < envelope)
    (hCeta : 0 ≤ C_eta)
    (hcDelta : 0 < c_Delta)
    (halpha : 0 ≤ alpha)
    (hhalf : 2 * alpha ≤ gap)
    (htemple : alpha * (gap - alpha) ≤ etaSq)
    (heta : etaSq ≤ C_eta * scale ^ r_eta * envelope ^ 2)
    (hgap : c_Delta * scale ^ r_Delta * envelope ≤ gap) :
    alpha ≤
      (2 * C_eta / c_Delta) *
        scale ^ (r_eta - r_Delta) * envelope := by
  have hden : 0 < c_Delta * scale ^ r_Delta * envelope := by
    positivity
  have hgap_pos : 0 < gap := hden.trans_le hgap
  have htemple_bound : alpha ≤ 2 * etaSq / gap :=
    rayleigh_excess_le_two_mul_residual_sq_div_gap
      halpha hgap_pos hhalf htemple
  have hnum_nonneg :
      0 ≤ C_eta * scale ^ r_eta * envelope ^ 2 := by
    positivity
  have hratio :
      etaSq / gap ≤
        (C_eta * scale ^ r_eta * envelope ^ 2) /
          (c_Delta * scale ^ r_Delta * envelope) :=
    div_le_div₀ hnum_nonneg heta hden hgap
  calc
    alpha ≤ 2 * etaSq / gap := htemple_bound
    _ = 2 * (etaSq / gap) := by ring
    _ ≤ 2 *
        ((C_eta * scale ^ r_eta * envelope ^ 2) /
          (c_Delta * scale ^ r_Delta * envelope)) := by
      gcongr
    _ = (2 * C_eta / c_Delta) *
        scale ^ (r_eta - r_Delta) * envelope := by
      rw [Real.rpow_sub hscale]
      field_simp

/-- Nonvacuous one-filter form of the Temple residual/gap envelope transfer. -/
theorem eventually_safe_alpha_envelope_of_temple_residual_gap_bounds
    {ι : Type*} {l : Filter ι} [NeBot l]
    (scale envelope alpha etaSq gap : ι → ℝ)
    (C_eta c_Delta r_eta r_Delta : ℝ)
    (hCeta : 0 ≤ C_eta)
    (hcDelta : 0 < c_Delta)
    (hscale : ∀ᶠ i in l, 0 < scale i)
    (henvelope : ∀ᶠ i in l, 0 < envelope i)
    (halpha : ∀ᶠ i in l, 0 ≤ alpha i)
    (hhalf : ∀ᶠ i in l, 2 * alpha i ≤ gap i)
    (htemple : ∀ᶠ i in l,
      alpha i * (gap i - alpha i) ≤ etaSq i)
    (heta : ∀ᶠ i in l,
      etaSq i ≤ C_eta * scale i ^ r_eta * envelope i ^ 2)
    (hgap : ∀ᶠ i in l,
      c_Delta * scale i ^ r_Delta * envelope i ≤ gap i) :
    ∀ᶠ i in l,
      alpha i ≤
        (2 * C_eta / c_Delta) *
          scale i ^ (r_eta - r_Delta) * envelope i := by
  filter_upwards
    [hscale, henvelope, halpha, hhalf, htemple, heta, hgap] with
    i hsi hei hai hhi hti heti hgi
  exact safe_alpha_envelope_of_temple_residual_gap_bounds
    hsi hei hCeta hcDelta hai hhi hti heti hgi

/-- A single-envelope residual-square estimate cannot replace the required
squared-envelope estimate.  All Temple/half-gap and lower-gap premises below
hold, but `alpha ≤ envelope` fails. -/
theorem one_envelope_residual_gap_bounds_do_not_force_safe_alpha :
    let envelope : ℝ := 1 / 16
    let gap : ℝ := 1 / 4
    let alpha : ℝ := 1 / 8
    let etaSq : ℝ := 1 / 64
    0 < envelope ∧
      0 ≤ alpha ∧
      2 * alpha ≤ gap ∧
      alpha * (gap - alpha) ≤ etaSq ∧
      etaSq ≤ envelope ∧
      envelope ≤ gap ∧
      ¬ alpha ≤ envelope := by
  norm_num

#print axioms safe_alpha_envelope_of_temple_residual_gap_bounds
#print axioms eventually_safe_alpha_envelope_of_temple_residual_gap_bounds
#print axioms one_envelope_residual_gap_bounds_do_not_force_safe_alpha

end Q3.RouteB
