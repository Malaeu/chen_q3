import Mathlib

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- Contract-v2 SAFE upper/lower bounds plus an independently supplied
WPrime identity yield the exact squared polynomial envelope used by H4d1. -/
theorem safe_bounds_to_square_envelope_pointwise
    {scale envelope alpha gap b W
      C_b C_alpha c_Delta q_b r_alpha r_Delta : ℝ}
    (hscale : 0 < scale)
    (henvelope : 0 < envelope)
    (hCb : 0 ≤ C_b)
    (hCa : 0 ≤ C_alpha)
    (hcD : 0 < c_Delta)
    (ha0 : 0 ≤ alpha)
    (ha : alpha ≤ C_alpha * scale ^ r_alpha * envelope)
    (hg : c_Delta * scale ^ r_Delta * envelope ≤ gap)
    (hb : |b| ≤ C_b * scale ^ q_b)
    (hW : W ^ 2 = |b| ^ 2 * scale * alpha / gap) :
    W ^ 2 ≤
      (C_b * Real.sqrt (C_alpha / c_Delta) *
        scale ^ (q_b + (1 + r_alpha - r_Delta) / 2)) ^ 2 := by
  have hden :
      0 < c_Delta * scale ^ r_Delta * envelope := by
    positivity
  have hgap : 0 < gap :=
    hden.trans_le hg
  have hupper_nonneg :
      0 ≤ C_alpha * scale ^ r_alpha * envelope := by
    positivity
  have hratio_raw :
      alpha / gap ≤
        (C_alpha * scale ^ r_alpha * envelope) /
          (c_Delta * scale ^ r_Delta * envelope) :=
    div_le_div₀ hupper_nonneg ha hden hg
  have hratio :
      alpha / gap ≤
        (C_alpha / c_Delta) *
          scale ^ (r_alpha - r_Delta) := by
    calc
      alpha / gap ≤
          (C_alpha * scale ^ r_alpha * envelope) /
            (c_Delta * scale ^ r_Delta * envelope) :=
        hratio_raw
      _ = (C_alpha / c_Delta) *
          scale ^ (r_alpha - r_Delta) := by
        rw [Real.rpow_sub hscale]
        field_simp
  have hb_rhs_nonneg :
      0 ≤ C_b * scale ^ q_b := by
    positivity
  have hbsq :
      |b| ^ 2 ≤ (C_b * scale ^ q_b) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg b) hb_rhs_nonneg).2 hb
  have hratio_nonneg :
      0 ≤ alpha / gap :=
    div_nonneg ha0 hgap.le
  have hratio_rhs_nonneg :
      0 ≤
        (C_alpha / c_Delta) *
          scale ^ (r_alpha - r_Delta) := by
    positivity
  calc
    W ^ 2 =
        |b| ^ 2 * scale * (alpha / gap) := by
      rw [hW]
      ring
    _ ≤
        (C_b * scale ^ q_b) ^ 2 * scale *
          ((C_alpha / c_Delta) *
            scale ^ (r_alpha - r_Delta)) := by
      gcongr
    _ =
        (C_b * Real.sqrt (C_alpha / c_Delta) *
          scale ^
            (q_b + (1 + r_alpha - r_Delta) / 2)) ^ 2 := by
      have hcad :
          0 ≤ C_alpha / c_Delta :=
        div_nonneg hCa hcD.le
      simp only [mul_pow]
      rw [Real.sq_sqrt hcad]
      have hpow_half :
          (scale ^
              (q_b + (1 + r_alpha - r_Delta) / 2)) ^ 2 =
            scale ^
              (2 * q_b + 1 + r_alpha - r_Delta) := by
        rw [← Real.rpow_mul_natCast hscale.le]
        congr 1
        ring
      rw [hpow_half]
      rw [show
        2 * q_b + 1 + r_alpha - r_Delta =
          (q_b + q_b) + 1 + (r_alpha - r_Delta) by
        ring]
      rw [Real.rpow_add hscale
        ((q_b + q_b) + 1) (r_alpha - r_Delta)]
      rw [Real.rpow_add hscale (q_b + q_b) 1]
      rw [Real.rpow_add hscale q_b q_b]
      rw [Real.rpow_one]
      ring

theorem safe_bounds_to_square_envelope_eventually
    {ι : Type*} {l : Filter ι} [NeBot l]
    (scale envelope alpha gap b W : ι → ℝ)
    (C_b C_alpha c_Delta q_b r_alpha r_Delta : ℝ)
    (hCb : 0 ≤ C_b)
    (hCa : 0 ≤ C_alpha)
    (hcD : 0 < c_Delta)
    (hscale : ∀ᶠ i in l, 0 < scale i)
    (henvelope : ∀ᶠ i in l, 0 < envelope i)
    (ha0 : ∀ᶠ i in l, 0 ≤ alpha i)
    (ha : ∀ᶠ i in l,
      alpha i ≤
        C_alpha * scale i ^ r_alpha * envelope i)
    (hg : ∀ᶠ i in l,
      c_Delta * scale i ^ r_Delta * envelope i ≤
        gap i)
    (hb : ∀ᶠ i in l,
      |b i| ≤ C_b * scale i ^ q_b)
    (hW : ∀ᶠ i in l,
      W i ^ 2 =
        |b i| ^ 2 * scale i * alpha i / gap i) :
    ∀ᶠ i in l,
      W i ^ 2 ≤
        (C_b * Real.sqrt (C_alpha / c_Delta) *
          scale i ^
            (q_b + (1 + r_alpha - r_Delta) / 2)) ^ 2 := by
  filter_upwards
    [hscale, henvelope, ha0, ha, hg, hb, hW] with
    i hsi hei hai0 hai hgi hbi hWi
  exact
    safe_bounds_to_square_envelope_pointwise
      hsi hei hCb hCa hcD hai0 hai hgi hbi hWi

#print axioms safe_bounds_to_square_envelope_pointwise
#print axioms safe_bounds_to_square_envelope_eventually

end Q3.RouteB
