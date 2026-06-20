import Mathlib
import Q3.Basic.Defs
import Q3.DigammaSeries

open scoped Real Topology ComplexOrder BigOperators
open Filter MeasureTheory Real Set

noncomputable section

namespace Q3

/-!
Stieltjes / Euler-Maclaurin remainder for digamma (N=1).
Reference: Johansson (Maple Trans. 2023), equations (21) and (23),
specialized to N=1 and differentiated to obtain the digamma identity.

Proof skeleton and the arithmetic chain to the tail bound are recorded
in `PROWKA_RESPONSE_3.md`.
-/

open scoped BigOperators

/-- Bernoulli polynomial B2(t) = t^2 - t + 1/6. -/
def bernoulli2 (t : ℝ) : ℝ := t ^ 2 - t + (6 : ℝ)⁻¹

/-- B2 applied to the fractional part. -/
def bernoulli2Fract (x : ℝ) : ℝ := bernoulli2 (Int.fract x)

/-- Bernoulli gap term: 1/6 - B2(fract x). -/
def bernoulli2Diff (x : ℝ) : ℝ := (6 : ℝ)⁻¹ - bernoulli2 (Int.fract x)

/-- Bernoulli polynomial B4(t) = t^4 - 2t^3 + t^2 - 1/30. -/
def bernoulli4 (t : ℝ) : ℝ := t ^ 4 - 2 * t ^ 3 + t ^ 2 - (30 : ℝ)⁻¹

/-- B4 applied to the fractional part.  This is the next periodic Bernoulli
kernel needed after the existing N=1 Stieltjes/Euler-Maclaurin layer. -/
def bernoulli4Fract (x : ℝ) : ℝ := bernoulli4 (Int.fract x)

/-- Repository-normalized B4 periodic kernel for the next Stieltjes lift.

Unlike `bernoulli2Diff`, this is the signed periodic Bernoulli polynomial
itself, because the power-3 to power-5 step first splits
`bernoulli2Diff = 1/6 - B2(fract)` and then integrates the `B2(fract)` term
twice. -/
def bernoulli4Diff (x : ℝ) : ℝ := bernoulli4Fract x

/-- Bernoulli polynomial B6(t) = t^6 - 3t^5 + (5/2)t^4 - (1/2)t^2 + 1/42. -/
def bernoulli6 (t : ℝ) : ℝ :=
  t ^ 6 - 3 * t ^ 5 + (5 / 2 : ℝ) * t ^ 4 - (1 / 2 : ℝ) * t ^ 2 +
    (42 : ℝ)⁻¹

/-- B6 applied to the fractional part, prepared for the next one-order
Euler-Maclaurin lift from the B4/power-5 surface. -/
def bernoulli6Fract (x : ℝ) : ℝ := bernoulli6 (Int.fract x)

/-- Repository-normalized B6 periodic kernel for the B4-to-B6 Stieltjes lift. -/
def bernoulli6Diff (x : ℝ) : ℝ := bernoulli6Fract x

/-- Bernoulli polynomial B8(t) =
`t^8 - 4t^7 + (14/3)t^6 - (7/3)t^4 + (2/3)t^2 - 1/30`. -/
def bernoulli8 (t : ℝ) : ℝ :=
  t ^ 8 - 4 * t ^ 7 + (14 / 3 : ℝ) * t ^ 6 -
    (7 / 3 : ℝ) * t ^ 4 + (2 / 3 : ℝ) * t ^ 2 - (30 : ℝ)⁻¹

/-- B8 applied to the fractional part, prepared for the next one-order
Euler-Maclaurin lift from the B6/power-7 surface. -/
def bernoulli8Fract (x : ℝ) : ℝ := bernoulli8 (Int.fract x)

/-- Repository-normalized B8 periodic kernel for the B6-to-B8 Stieltjes lift. -/
def bernoulli8Diff (x : ℝ) : ℝ := bernoulli8Fract x

/-- Bernoulli polynomial B10(t) =
`t^10 - 5t^9 + (15/2)t^8 - 7t^6 + 5t^4 - (3/2)t^2 + 5/66`. -/
def bernoulli10 (t : ℝ) : ℝ :=
  t ^ 10 - 5 * t ^ 9 + (15 / 2 : ℝ) * t ^ 8 - 7 * t ^ 6 +
    5 * t ^ 4 - (3 / 2 : ℝ) * t ^ 2 + (5 / 66 : ℝ)

/-- B10 applied to the fractional part, prepared for the next one-order
Euler-Maclaurin lift from the B8/power-9 surface. -/
def bernoulli10Fract (x : ℝ) : ℝ := bernoulli10 (Int.fract x)

/-- Repository-normalized B10 periodic kernel for the B8-to-B10 Stieltjes lift. -/
def bernoulli10Diff (x : ℝ) : ℝ := bernoulli10Fract x

/-- Bernoulli polynomial B1(t) = t - 1/2. -/
def bernoulli1 (t : ℝ) : ℝ := t - (1 / 2 : ℝ)

/-- B1 applied to the fractional part. -/
def bernoulli1Fract (x : ℝ) : ℝ := bernoulli1 (Int.fract x)

@[measurability]
lemma measurable_bernoulli2 : Measurable bernoulli2 := by
  -- bernoulli2 t = t^2 - t + 1/6
  have h1 : Measurable fun t : ℝ => t ^ 2 := by
    simpa using (measurable_id.pow_const 2)
  have h2 : Measurable fun t : ℝ => t := measurable_id
  have h3 : Measurable fun t : ℝ => (1 / 6 : ℝ) := measurable_const
  have h4 : Measurable fun t : ℝ => t ^ 2 - t := h1.sub h2
  have h5 : Measurable fun t : ℝ => t ^ 2 - t + (1 / 6 : ℝ) := h4.add h3
  simpa [bernoulli2, one_div] using h5

@[measurability]
lemma measurable_bernoulli2Diff : Measurable bernoulli2Diff := by
  have hfract : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  simpa [bernoulli2Diff] using (measurable_const.sub (measurable_bernoulli2.comp hfract))

@[measurability]
lemma measurable_bernoulli2Fract : Measurable bernoulli2Fract := by
  have hfract : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  simpa [bernoulli2Fract] using measurable_bernoulli2.comp hfract

@[measurability]
lemma measurable_bernoulli4 : Measurable bernoulli4 := by
  have h4 : Measurable fun t : ℝ => t ^ 4 := by
    simpa using (measurable_id.pow_const 4)
  have h3 : Measurable fun t : ℝ => t ^ 3 := by
    simpa using (measurable_id.pow_const 3)
  have h2 : Measurable fun t : ℝ => t ^ 2 := by
    simpa using (measurable_id.pow_const 2)
  have hconst : Measurable fun _ : ℝ => (30 : ℝ)⁻¹ := measurable_const
  simpa [bernoulli4] using ((h4.sub (measurable_const.mul h3)).add h2).sub hconst

@[measurability]
lemma measurable_bernoulli4Fract : Measurable bernoulli4Fract := by
  have hfract : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  simpa [bernoulli4Fract] using measurable_bernoulli4.comp hfract

@[measurability]
lemma measurable_bernoulli4Diff : Measurable bernoulli4Diff := by
  simpa [bernoulli4Diff] using measurable_bernoulli4Fract

@[measurability]
lemma measurable_bernoulli6 : Measurable bernoulli6 := by
  have h6 : Measurable fun t : ℝ => t ^ 6 := by
    simpa using (measurable_id.pow_const 6)
  have h5 : Measurable fun t : ℝ => t ^ 5 := by
    simpa using (measurable_id.pow_const 5)
  have h4 : Measurable fun t : ℝ => t ^ 4 := by
    simpa using (measurable_id.pow_const 4)
  have h2 : Measurable fun t : ℝ => t ^ 2 := by
    simpa using (measurable_id.pow_const 2)
  have hconst : Measurable fun _ : ℝ => (42 : ℝ)⁻¹ := measurable_const
  simpa [bernoulli6] using
    ((((h6.sub (measurable_const.mul h5)).add
      (measurable_const.mul h4)).sub (measurable_const.mul h2)).add hconst)

@[measurability]
lemma measurable_bernoulli6Fract : Measurable bernoulli6Fract := by
  have hfract : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  simpa [bernoulli6Fract] using measurable_bernoulli6.comp hfract

@[measurability]
lemma measurable_bernoulli6Diff : Measurable bernoulli6Diff := by
  simpa [bernoulli6Diff] using measurable_bernoulli6Fract

@[measurability]
lemma measurable_bernoulli8 : Measurable bernoulli8 := by
  have h8 : Measurable fun t : ℝ => t ^ 8 := by
    simpa using (measurable_id.pow_const 8)
  have h7 : Measurable fun t : ℝ => t ^ 7 := by
    simpa using (measurable_id.pow_const 7)
  have h6 : Measurable fun t : ℝ => t ^ 6 := by
    simpa using (measurable_id.pow_const 6)
  have h4 : Measurable fun t : ℝ => t ^ 4 := by
    simpa using (measurable_id.pow_const 4)
  have h2 : Measurable fun t : ℝ => t ^ 2 := by
    simpa using (measurable_id.pow_const 2)
  have hconst : Measurable fun _ : ℝ => (30 : ℝ)⁻¹ := measurable_const
  simpa [bernoulli8] using
    (((((h8.sub (measurable_const.mul h7)).add
      (measurable_const.mul h6)).sub
      (measurable_const.mul h4)).add (measurable_const.mul h2)).sub hconst)

@[measurability]
lemma measurable_bernoulli8Fract : Measurable bernoulli8Fract := by
  have hfract : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  simpa [bernoulli8Fract] using measurable_bernoulli8.comp hfract

@[measurability]
lemma measurable_bernoulli8Diff : Measurable bernoulli8Diff := by
  simpa [bernoulli8Diff] using measurable_bernoulli8Fract

@[measurability]
lemma measurable_bernoulli10 : Measurable bernoulli10 := by
  have h10 : Measurable fun t : ℝ => t ^ 10 := by
    simpa using (measurable_id.pow_const 10)
  have h9 : Measurable fun t : ℝ => t ^ 9 := by
    simpa using (measurable_id.pow_const 9)
  have h8 : Measurable fun t : ℝ => t ^ 8 := by
    simpa using (measurable_id.pow_const 8)
  have h6 : Measurable fun t : ℝ => t ^ 6 := by
    simpa using (measurable_id.pow_const 6)
  have h4 : Measurable fun t : ℝ => t ^ 4 := by
    simpa using (measurable_id.pow_const 4)
  have h2 : Measurable fun t : ℝ => t ^ 2 := by
    simpa using (measurable_id.pow_const 2)
  have hconst : Measurable fun _ : ℝ => (5 / 66 : ℝ) := measurable_const
  simpa [bernoulli10] using
    ((((((h10.sub (measurable_const.mul h9)).add
      (measurable_const.mul h8)).sub
      (measurable_const.mul h6)).add
      (measurable_const.mul h4)).sub (measurable_const.mul h2)).add hconst)

@[measurability]
lemma measurable_bernoulli10Fract : Measurable bernoulli10Fract := by
  have hfract : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  simpa [bernoulli10Fract] using measurable_bernoulli10.comp hfract

@[measurability]
lemma measurable_bernoulli10Diff : Measurable bernoulli10Diff := by
  simpa [bernoulli10Diff] using measurable_bernoulli10Fract

lemma bernoulli2Fract_eq_const_sub_diff (x : ℝ) :
    bernoulli2Fract x = (6 : ℝ)⁻¹ - bernoulli2Diff x := by
  simp [bernoulli2Fract, bernoulli2Diff]

lemma bernoulli2Diff_eq_const_sub_fract (x : ℝ) :
    bernoulli2Diff x = (6 : ℝ)⁻¹ - bernoulli2Fract x := by
  simp [bernoulli2Fract, bernoulli2Diff]

lemma bernoulli2Diff_eq_mul (x : ℝ) :
    bernoulli2Diff x = Int.fract x * (1 - Int.fract x) := by
  simp [bernoulli2Diff, bernoulli2]
  ring_nf

lemma bernoulli4_eq_sq_sub_inv (t : ℝ) :
    bernoulli4 t = (t * (1 - t)) ^ 2 - (30 : ℝ)⁻¹ := by
  simp [bernoulli4]
  ring

lemma bernoulli2Diff_bounds (x : ℝ) :
    0 ≤ bernoulli2Diff x ∧ bernoulli2Diff x ≤ (1 / 4 : ℝ) := by
  set t : ℝ := Int.fract x
  have ht0 : 0 ≤ t := Int.fract_nonneg x
  have ht1 : t ≤ 1 := (le_of_lt (Int.fract_lt_one x))
  have hquad : 0 ≤ (t - (1 / 2 : ℝ)) ^ 2 := by nlinarith
  have hupper : t * (1 - t) ≤ (1 / 4 : ℝ) := by
    -- Expand (t - 1/2)^2 >= 0
    nlinarith
  have hnonneg : 0 ≤ t * (1 - t) := by nlinarith [ht0, ht1]
  have hmul : bernoulli2Diff x = t * (1 - t) := by
    simpa [t] using (bernoulli2Diff_eq_mul x)
  refine ⟨?_, ?_⟩
  · simpa [hmul] using hnonneg
  · simpa [hmul] using hupper

lemma bernoulli2Diff_norm_le (x : ℝ) :
    ‖(bernoulli2Diff x : ℂ)‖ ≤ (1 / 4 : ℝ) := by
  have hb0 : 0 ≤ bernoulli2Diff x := (bernoulli2Diff_bounds x).1
  have hb1 : bernoulli2Diff x ≤ (1 / 4 : ℝ) := (bernoulli2Diff_bounds x).2
  have habs : |bernoulli2Diff x| = bernoulli2Diff x := by
    simp [abs_of_nonneg hb0]
  have hnorm : ‖(bernoulli2Diff x : ℂ)‖ = |bernoulli2Diff x| := by
    simp
  simpa [hnorm, habs] using hb1

lemma bernoulli4Fract_bounds (x : ℝ) :
    -(1 / 30 : ℝ) ≤ bernoulli4Fract x ∧
      bernoulli4Fract x ≤ (7 / 240 : ℝ) := by
  let p : ℝ := Int.fract x * (1 - Int.fract x)
  have hp0 : 0 ≤ p := by
    have hb0 := (bernoulli2Diff_bounds x).1
    have hmul := bernoulli2Diff_eq_mul x
    simpa [p, hmul] using hb0
  have hp1 : p ≤ (1 / 4 : ℝ) := by
    have hb1 := (bernoulli2Diff_bounds x).2
    have hmul := bernoulli2Diff_eq_mul x
    simpa [p, hmul] using hb1
  have hpSq0 : 0 ≤ p ^ 2 := by nlinarith
  have hpSq1 : p ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  have hrepr : bernoulli4Fract x = p ^ 2 - (1 / 30 : ℝ) := by
    simp [bernoulli4Fract, bernoulli4_eq_sq_sub_inv, p]
  constructor
  · nlinarith
  · nlinarith

lemma bernoulli4Fract_abs_le (x : ℝ) :
    |bernoulli4Fract x| ≤ (1 / 30 : ℝ) := by
  have hb := bernoulli4Fract_bounds x
  exact abs_le.2 ⟨by nlinarith [hb.1], by nlinarith [hb.2]⟩

lemma bernoulli4Fract_norm_le (x : ℝ) :
    ‖(bernoulli4Fract x : ℂ)‖ ≤ (1 / 30 : ℝ) := by
  have hb := bernoulli4Fract_abs_le x
  have hnorm : ‖(bernoulli4Fract x : ℂ)‖ = |bernoulli4Fract x| := by
    simp
  simpa [hnorm] using hb

lemma bernoulli4Diff_bounds (x : ℝ) :
    -(1 / 30 : ℝ) ≤ bernoulli4Diff x ∧
      bernoulli4Diff x ≤ (7 / 240 : ℝ) := by
  simpa [bernoulli4Diff] using bernoulli4Fract_bounds x

lemma bernoulli4Diff_abs_le (x : ℝ) :
    |bernoulli4Diff x| ≤ (1 / 30 : ℝ) := by
  simpa [bernoulli4Diff] using bernoulli4Fract_abs_le x

lemma bernoulli4Diff_norm_le (x : ℝ) :
    ‖(bernoulli4Diff x : ℂ)‖ ≤ (1 / 30 : ℝ) := by
  simpa [bernoulli4Diff] using bernoulli4Fract_norm_le x

lemma bernoulli6Diff_abs_le (x : ℝ) :
    |bernoulli6Diff x| ≤ (8 : ℝ) := by
  set t : ℝ := Int.fract x
  have ht0 : 0 ≤ t := by
    simpa [t] using Int.fract_nonneg x
  have ht1 : t ≤ 1 := by
    simpa [t] using le_of_lt (Int.fract_lt_one x)
  have ht2_nonneg : 0 ≤ t ^ 2 := pow_nonneg ht0 2
  have ht4_nonneg : 0 ≤ t ^ 4 := pow_nonneg ht0 4
  have ht5_nonneg : 0 ≤ t ^ 5 := pow_nonneg ht0 5
  have ht6_nonneg : 0 ≤ t ^ 6 := pow_nonneg ht0 6
  have ht2_le : t ^ 2 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht4_le : t ^ 4 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht5_le : t ^ 5 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht6_le : t ^ 6 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have hbounds :
      -(8 : ℝ) ≤
          t ^ 6 - 3 * t ^ 5 + (5 / 2 : ℝ) * t ^ 4 -
            (1 / 2 : ℝ) * t ^ 2 + (42 : ℝ)⁻¹ ∧
        t ^ 6 - 3 * t ^ 5 + (5 / 2 : ℝ) * t ^ 4 -
            (1 / 2 : ℝ) * t ^ 2 + (42 : ℝ)⁻¹ ≤ (8 : ℝ) := by
    constructor
    · nlinarith [ht6_nonneg, ht5_le, ht4_nonneg, ht2_le]
    · nlinarith [ht6_le, ht5_nonneg, ht4_le, ht2_nonneg]
  simpa [bernoulli6Diff, bernoulli6Fract, bernoulli6, t] using abs_le.2 hbounds

lemma bernoulli6Diff_norm_le (x : ℝ) :
    ‖(bernoulli6Diff x : ℂ)‖ ≤ (8 : ℝ) := by
  have hb := bernoulli6Diff_abs_le x
  have hnorm : ‖(bernoulli6Diff x : ℂ)‖ = |bernoulli6Diff x| := by
    simp
  simpa [hnorm] using hb

lemma bernoulli8Diff_abs_le (x : ℝ) :
    |bernoulli8Diff x| ≤ (8 : ℝ) := by
  set t : ℝ := Int.fract x
  have ht0 : 0 ≤ t := by
    simpa [t] using Int.fract_nonneg x
  have ht1 : t ≤ 1 := by
    simpa [t] using le_of_lt (Int.fract_lt_one x)
  have ht2_nonneg : 0 ≤ t ^ 2 := pow_nonneg ht0 2
  have ht4_nonneg : 0 ≤ t ^ 4 := pow_nonneg ht0 4
  have ht6_nonneg : 0 ≤ t ^ 6 := pow_nonneg ht0 6
  have ht7_nonneg : 0 ≤ t ^ 7 := pow_nonneg ht0 7
  have ht8_nonneg : 0 ≤ t ^ 8 := pow_nonneg ht0 8
  have ht2_le : t ^ 2 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht4_le : t ^ 4 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht6_le : t ^ 6 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht7_le : t ^ 7 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht8_le : t ^ 8 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have hbounds :
      -(8 : ℝ) ≤
          t ^ 8 - 4 * t ^ 7 + (14 / 3 : ℝ) * t ^ 6 -
            (7 / 3 : ℝ) * t ^ 4 + (2 / 3 : ℝ) * t ^ 2 - (30 : ℝ)⁻¹ ∧
        t ^ 8 - 4 * t ^ 7 + (14 / 3 : ℝ) * t ^ 6 -
            (7 / 3 : ℝ) * t ^ 4 + (2 / 3 : ℝ) * t ^ 2 - (30 : ℝ)⁻¹ ≤
          (8 : ℝ) := by
    constructor
    · nlinarith [ht8_nonneg, ht7_le, ht6_nonneg, ht4_le, ht2_nonneg]
    · nlinarith [ht8_le, ht7_nonneg, ht6_le, ht4_nonneg, ht2_le]
  simpa [bernoulli8Diff, bernoulli8Fract, bernoulli8, t] using abs_le.2 hbounds

lemma bernoulli8Diff_norm_le (x : ℝ) :
    ‖(bernoulli8Diff x : ℂ)‖ ≤ (8 : ℝ) := by
  have hb := bernoulli8Diff_abs_le x
  have hnorm : ‖(bernoulli8Diff x : ℂ)‖ = |bernoulli8Diff x| := by
    simp
  simpa [hnorm] using hb

lemma bernoulli10Diff_abs_le (x : ℝ) :
    |bernoulli10Diff x| ≤ (32 : ℝ) := by
  set t : ℝ := Int.fract x
  have ht0 : 0 ≤ t := by
    simpa [t] using Int.fract_nonneg x
  have ht1 : t ≤ 1 := by
    simpa [t] using le_of_lt (Int.fract_lt_one x)
  have ht2_nonneg : 0 ≤ t ^ 2 := pow_nonneg ht0 2
  have ht4_nonneg : 0 ≤ t ^ 4 := pow_nonneg ht0 4
  have ht6_nonneg : 0 ≤ t ^ 6 := pow_nonneg ht0 6
  have ht8_nonneg : 0 ≤ t ^ 8 := pow_nonneg ht0 8
  have ht9_nonneg : 0 ≤ t ^ 9 := pow_nonneg ht0 9
  have ht10_nonneg : 0 ≤ t ^ 10 := pow_nonneg ht0 10
  have ht2_le : t ^ 2 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht4_le : t ^ 4 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht6_le : t ^ 6 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht8_le : t ^ 8 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht9_le : t ^ 9 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have ht10_le : t ^ 10 ≤ 1 := by
    exact pow_le_one₀ ht0 ht1
  have hbounds :
      -(32 : ℝ) ≤
          t ^ 10 - 5 * t ^ 9 + (15 / 2 : ℝ) * t ^ 8 -
            7 * t ^ 6 + 5 * t ^ 4 - (3 / 2 : ℝ) * t ^ 2 + (5 / 66 : ℝ) ∧
        t ^ 10 - 5 * t ^ 9 + (15 / 2 : ℝ) * t ^ 8 -
            7 * t ^ 6 + 5 * t ^ 4 - (3 / 2 : ℝ) * t ^ 2 + (5 / 66 : ℝ) ≤
          (32 : ℝ) := by
    constructor
    · nlinarith [ht10_nonneg, ht9_le, ht8_nonneg, ht6_le, ht4_nonneg, ht2_le]
    · nlinarith [ht10_le, ht9_nonneg, ht8_le, ht6_nonneg, ht4_le, ht2_nonneg]
  simpa [bernoulli10Diff, bernoulli10Fract, bernoulli10, t] using abs_le.2 hbounds

lemma bernoulli10Diff_norm_le (x : ℝ) :
    ‖(bernoulli10Diff x : ℂ)‖ ≤ (32 : ℝ) := by
  have hb := bernoulli10Diff_abs_le x
  have hnorm : ‖(bernoulli10Diff x : ℂ)‖ = |bernoulli10Diff x| := by
    simp
  simpa [hnorm] using hb

lemma bernoulli2Fract_int (n : ℤ) : bernoulli2Fract (n : ℝ) = (6 : ℝ)⁻¹ := by
  simp [bernoulli2Fract, bernoulli2]

lemma bernoulli2Diff_int (n : ℤ) : bernoulli2Diff (n : ℝ) = 0 := by
  simp [bernoulli2Diff, bernoulli2]

lemma bernoulli4Diff_int (n : ℤ) : bernoulli4Diff (n : ℝ) = -(30 : ℝ)⁻¹ := by
  simp [bernoulli4Diff, bernoulli4Fract, bernoulli4]

lemma fract_eq_sub_nat_on_Ioo (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    Int.fract x = x - n := by
  have hx0 : 0 ≤ x - n := by nlinarith [hx.1]
  have hx1 : x - n < 1 := by nlinarith [hx.2]
  have hfract : Int.fract (x - n) = x - n := by
    exact (Int.fract_eq_self).2 ⟨hx0, hx1⟩
  have hshift : Int.fract x = Int.fract (x - n) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Int.fract_add_natCast (a := x - n) (m := n))
  calc
    Int.fract x = Int.fract (x - n) := hshift
    _ = x - n := hfract

lemma bernoulli1Fract_eq_on_Ioo (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    bernoulli1Fract x = x - n - (1 / 2 : ℝ) := by
  simp [bernoulli1Fract, bernoulli1, fract_eq_sub_nat_on_Ioo n hx, sub_eq_add_neg, add_assoc]

lemma bernoulli2Diff_eq_on_Ioo (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    bernoulli2Diff x = (x - n) - (x - n) ^ 2 := by
  have hfract : Int.fract x = x - n := fract_eq_sub_nat_on_Ioo n hx
  simp [bernoulli2Diff, bernoulli2, hfract, pow_two, sub_eq_add_neg, add_assoc]

lemma bernoulli2Fract_eq_on_Ioo (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    bernoulli2Fract x = (x - n) ^ 2 - (x - n) + (6 : ℝ)⁻¹ := by
  have hfract : Int.fract x = x - n := fract_eq_sub_nat_on_Ioo n hx
  simp [bernoulli2Fract, bernoulli2, hfract, sub_eq_add_neg, add_assoc]

lemma bernoulli2Fract_eq_cell_on_Icc (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) :
    bernoulli2Fract x = (x - n) ^ 2 - (x - n) + (6 : ℝ)⁻¹ := by
  by_cases hx0 : x = n
  · subst hx0
    simp [bernoulli2Fract, bernoulli2]
  by_cases hx1 : x = n + 1
  · subst hx1
    norm_num [bernoulli2Fract, bernoulli2, Nat.cast_add, Nat.cast_one]
  have hx' : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
    · exact lt_of_le_of_ne hx.2 hx1
  exact bernoulli2Fract_eq_on_Ioo n hx'

lemma bernoulli4Diff_eq_on_Ioo (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    bernoulli4Diff x =
      (x - n) ^ 4 - 2 * (x - n) ^ 3 + (x - n) ^ 2 - (30 : ℝ)⁻¹ := by
  have hfract : Int.fract x = x - n := fract_eq_sub_nat_on_Ioo n hx
  simp [bernoulli4Diff, bernoulli4Fract, bernoulli4, hfract, sub_eq_add_neg, add_assoc]

lemma bernoulli4Diff_eq_cell_on_Icc (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) :
    bernoulli4Diff x =
      (x - n) ^ 4 - 2 * (x - n) ^ 3 + (x - n) ^ 2 - (30 : ℝ)⁻¹ := by
  by_cases hx0 : x = n
  · subst hx0
    simp [bernoulli4Diff, bernoulli4Fract, bernoulli4]
  by_cases hx1 : x = n + 1
  · subst hx1
    norm_num [bernoulli4Diff, bernoulli4Fract, bernoulli4, Nat.cast_add, Nat.cast_one]
  have hx' : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
    · exact lt_of_le_of_ne hx.2 hx1
  exact bernoulli4Diff_eq_on_Ioo n hx'

/-- Cell derivative of the B4 polynomial.  This helper is the local polynomial
surface needed before the intervalwise integration-by-parts lift to kernel
power 5. -/
def bernoulli4DiffCellDeriv (n : ℕ) (x : ℝ) : ℝ :=
  4 * (x - n) ^ 3 - 6 * (x - n) ^ 2 + 2 * (x - n)

lemma bernoulli4DiffCellDeriv_left (n : ℕ) :
    bernoulli4DiffCellDeriv n (n : ℝ) = 0 := by
  simp [bernoulli4DiffCellDeriv]

lemma bernoulli4DiffCellDeriv_right (n : ℕ) :
    bernoulli4DiffCellDeriv n (n + 1 : ℝ) = 0 := by
  norm_num [bernoulli4DiffCellDeriv, Nat.cast_add, Nat.cast_one]

lemma bernoulli4DiffCellDeriv_hasDerivAt
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    HasDerivAt (fun y : ℝ => bernoulli4DiffCellDeriv n y)
      (12 * bernoulli2Fract x) x := by
  have hderiv :
      HasDerivAt (fun y : ℝ => bernoulli4DiffCellDeriv n y)
        (12 * (x - n) ^ 2 - 12 * (x - n) + 2) x := by
    have hbase : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (n : ℝ)
    have hcube :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 3)
          (3 * (x - (n : ℝ)) ^ 2) x := by
      simpa using hbase.pow 3
    have hsquare :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 2)
          (2 * (x - (n : ℝ))) x := by
      simpa using hbase.pow 2
    have hpoly :=
      ((hcube.const_mul (4 : ℝ)).sub (hsquare.const_mul (6 : ℝ))).add
        (hbase.const_mul (2 : ℝ))
    convert hpoly using 1
    ring
  have hcoef :
      12 * bernoulli2Fract x =
        12 * (x - n) ^ 2 - 12 * (x - n) + 2 := by
    have hcell := bernoulli2Fract_eq_on_Ioo n hx
    nlinarith [hcell]
  simpa [hcoef] using hderiv

lemma bernoulli6Diff_eq_on_Ioo (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    bernoulli6Diff x =
      (x - n) ^ 6 - 3 * (x - n) ^ 5 +
        (5 / 2 : ℝ) * (x - n) ^ 4 -
        (1 / 2 : ℝ) * (x - n) ^ 2 + (42 : ℝ)⁻¹ := by
  have hfract : Int.fract x = x - n := fract_eq_sub_nat_on_Ioo n hx
  simp [bernoulli6Diff, bernoulli6Fract, bernoulli6, hfract, sub_eq_add_neg,
    add_assoc]

lemma bernoulli6Diff_eq_cell_on_Icc (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) :
    bernoulli6Diff x =
      (x - n) ^ 6 - 3 * (x - n) ^ 5 +
        (5 / 2 : ℝ) * (x - n) ^ 4 -
        (1 / 2 : ℝ) * (x - n) ^ 2 + (42 : ℝ)⁻¹ := by
  by_cases hx0 : x = n
  · subst hx0
    simp [bernoulli6Diff, bernoulli6Fract, bernoulli6]
  by_cases hx1 : x = n + 1
  · subst hx1
    norm_num [bernoulli6Diff, bernoulli6Fract, bernoulli6, Nat.cast_add, Nat.cast_one]
  have hx' : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
    · exact lt_of_le_of_ne hx.2 hx1
  exact bernoulli6Diff_eq_on_Ioo n hx'

/-- Cell derivative of the B6 polynomial.  This is the next local polynomial
surface for the B4/power-5 to B6/power-7 Euler-Maclaurin lift. -/
def bernoulli6DiffCellDeriv (n : ℕ) (x : ℝ) : ℝ :=
  6 * (x - n) ^ 5 - 15 * (x - n) ^ 4 + 10 * (x - n) ^ 3 - (x - n)

lemma bernoulli6DiffCellDeriv_left (n : ℕ) :
    bernoulli6DiffCellDeriv n (n : ℝ) = 0 := by
  simp [bernoulli6DiffCellDeriv]

lemma bernoulli6DiffCellDeriv_right (n : ℕ) :
    bernoulli6DiffCellDeriv n (n + 1 : ℝ) = 0 := by
  norm_num [bernoulli6DiffCellDeriv, Nat.cast_add, Nat.cast_one]

lemma bernoulli6DiffCellDeriv_hasDerivAt
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    HasDerivAt (fun y : ℝ => bernoulli6DiffCellDeriv n y)
      (30 * bernoulli4Diff x) x := by
  have hderiv :
      HasDerivAt (fun y : ℝ => bernoulli6DiffCellDeriv n y)
        (30 * (x - n) ^ 4 - 60 * (x - n) ^ 3 + 30 * (x - n) ^ 2 - 1) x := by
    have hbase : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (n : ℝ)
    have hfive :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 5)
          (5 * (x - (n : ℝ)) ^ 4) x := by
      simpa using hbase.pow 5
    have hfour :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 4)
          (4 * (x - (n : ℝ)) ^ 3) x := by
      simpa using hbase.pow 4
    have hcube :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 3)
          (3 * (x - (n : ℝ)) ^ 2) x := by
      simpa using hbase.pow 3
    have hpoly :=
      (((hfive.const_mul (6 : ℝ)).sub (hfour.const_mul (15 : ℝ))).add
        (hcube.const_mul (10 : ℝ))).sub hbase
    convert hpoly using 1
    ring
  have hcoef :
      30 * bernoulli4Diff x =
      30 * (x - n) ^ 4 - 60 * (x - n) ^ 3 + 30 * (x - n) ^ 2 - 1 := by
    have hcell := bernoulli4Diff_eq_on_Ioo n hx
    nlinarith [hcell]
  simpa [hcoef] using hderiv

lemma bernoulli8Diff_eq_on_Ioo (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    bernoulli8Diff x =
      (x - n) ^ 8 - 4 * (x - n) ^ 7 +
        (14 / 3 : ℝ) * (x - n) ^ 6 -
        (7 / 3 : ℝ) * (x - n) ^ 4 +
        (2 / 3 : ℝ) * (x - n) ^ 2 - (30 : ℝ)⁻¹ := by
  have hfract : Int.fract x = x - n := fract_eq_sub_nat_on_Ioo n hx
  simp [bernoulli8Diff, bernoulli8Fract, bernoulli8, hfract, sub_eq_add_neg,
    add_assoc]

lemma bernoulli8Diff_eq_cell_on_Icc (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) :
    bernoulli8Diff x =
      (x - n) ^ 8 - 4 * (x - n) ^ 7 +
        (14 / 3 : ℝ) * (x - n) ^ 6 -
        (7 / 3 : ℝ) * (x - n) ^ 4 +
        (2 / 3 : ℝ) * (x - n) ^ 2 - (30 : ℝ)⁻¹ := by
  by_cases hx0 : x = n
  · subst hx0
    simp [bernoulli8Diff, bernoulli8Fract, bernoulli8]
  by_cases hx1 : x = n + 1
  · subst hx1
    norm_num [bernoulli8Diff, bernoulli8Fract, bernoulli8, Nat.cast_add, Nat.cast_one]
  have hx' : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
    · exact lt_of_le_of_ne hx.2 hx1
  exact bernoulli8Diff_eq_on_Ioo n hx'

/-- Cell derivative of the B8 polynomial.  This is the local polynomial
surface for the B6/power-7 to B8/power-9 Euler-Maclaurin lift. -/
def bernoulli8DiffCellDeriv (n : ℕ) (x : ℝ) : ℝ :=
  8 * (x - n) ^ 7 - 28 * (x - n) ^ 6 + 28 * (x - n) ^ 5 -
    (28 / 3 : ℝ) * (x - n) ^ 3 + (4 / 3 : ℝ) * (x - n)

lemma bernoulli8DiffCellDeriv_left (n : ℕ) :
    bernoulli8DiffCellDeriv n (n : ℝ) = 0 := by
  simp [bernoulli8DiffCellDeriv]

lemma bernoulli8DiffCellDeriv_right (n : ℕ) :
    bernoulli8DiffCellDeriv n (n + 1 : ℝ) = 0 := by
  norm_num [bernoulli8DiffCellDeriv, Nat.cast_add, Nat.cast_one]

lemma bernoulli8DiffCellDeriv_hasDerivAt
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    HasDerivAt (fun y : ℝ => bernoulli8DiffCellDeriv n y)
      (56 * bernoulli6Diff x) x := by
  have hderiv :
      HasDerivAt (fun y : ℝ => bernoulli8DiffCellDeriv n y)
        (56 * (x - n) ^ 6 - 168 * (x - n) ^ 5 +
          140 * (x - n) ^ 4 - 28 * (x - n) ^ 2 + (4 / 3 : ℝ)) x := by
    have hbase : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (n : ℝ)
    have hseven :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 7)
          (7 * (x - (n : ℝ)) ^ 6) x := by
      simpa using hbase.pow 7
    have hsix :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 6)
          (6 * (x - (n : ℝ)) ^ 5) x := by
      simpa using hbase.pow 6
    have hfive :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 5)
          (5 * (x - (n : ℝ)) ^ 4) x := by
      simpa using hbase.pow 5
    have hthree :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 3)
          (3 * (x - (n : ℝ)) ^ 2) x := by
      simpa using hbase.pow 3
    have hpoly :=
      ((((hseven.const_mul (8 : ℝ)).sub (hsix.const_mul (28 : ℝ))).add
        (hfive.const_mul (28 : ℝ))).sub
        (hthree.const_mul (28 / 3 : ℝ))).add (hbase.const_mul (4 / 3 : ℝ))
    convert hpoly using 1
    ring
  have hcoef :
      56 * bernoulli6Diff x =
        56 * (x - n) ^ 6 - 168 * (x - n) ^ 5 +
          140 * (x - n) ^ 4 - 28 * (x - n) ^ 2 + (4 / 3 : ℝ) := by
    have hcell := bernoulli6Diff_eq_on_Ioo n hx
    nlinarith [hcell]
  simpa [hcoef] using hderiv

lemma bernoulli10Diff_eq_on_Ioo (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    bernoulli10Diff x =
      (x - n) ^ 10 - 5 * (x - n) ^ 9 +
        (15 / 2 : ℝ) * (x - n) ^ 8 -
        7 * (x - n) ^ 6 + 5 * (x - n) ^ 4 -
        (3 / 2 : ℝ) * (x - n) ^ 2 + (5 / 66 : ℝ) := by
  have hfract : Int.fract x = x - n := fract_eq_sub_nat_on_Ioo n hx
  simp [bernoulli10Diff, bernoulli10Fract, bernoulli10, hfract, sub_eq_add_neg,
    add_assoc]

lemma bernoulli10Diff_eq_cell_on_Icc (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) :
    bernoulli10Diff x =
      (x - n) ^ 10 - 5 * (x - n) ^ 9 +
        (15 / 2 : ℝ) * (x - n) ^ 8 -
        7 * (x - n) ^ 6 + 5 * (x - n) ^ 4 -
        (3 / 2 : ℝ) * (x - n) ^ 2 + (5 / 66 : ℝ) := by
  by_cases hx0 : x = n
  · subst hx0
    simp [bernoulli10Diff, bernoulli10Fract, bernoulli10]
  by_cases hx1 : x = n + 1
  · subst hx1
    norm_num [bernoulli10Diff, bernoulli10Fract, bernoulli10, Nat.cast_add, Nat.cast_one]
  have hx' : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
    · exact lt_of_le_of_ne hx.2 hx1
  exact bernoulli10Diff_eq_on_Ioo n hx'

/-- Cell derivative of the B10 polynomial.  This is the local polynomial
surface for the B8/power-9 to B10/power-11 Euler-Maclaurin lift. -/
def bernoulli10DiffCellDeriv (n : ℕ) (x : ℝ) : ℝ :=
  10 * (x - n) ^ 9 - 45 * (x - n) ^ 8 + 60 * (x - n) ^ 7 -
    42 * (x - n) ^ 5 + 20 * (x - n) ^ 3 - 3 * (x - n)

lemma bernoulli10DiffCellDeriv_left (n : ℕ) :
    bernoulli10DiffCellDeriv n (n : ℝ) = 0 := by
  simp [bernoulli10DiffCellDeriv]

lemma bernoulli10DiffCellDeriv_right (n : ℕ) :
    bernoulli10DiffCellDeriv n (n + 1 : ℝ) = 0 := by
  norm_num [bernoulli10DiffCellDeriv, Nat.cast_add, Nat.cast_one]

lemma bernoulli10DiffCellDeriv_hasDerivAt
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ)) :
    HasDerivAt (fun y : ℝ => bernoulli10DiffCellDeriv n y)
      (90 * bernoulli8Diff x) x := by
  have hderiv :
      HasDerivAt (fun y : ℝ => bernoulli10DiffCellDeriv n y)
        (90 * (x - n) ^ 8 - 360 * (x - n) ^ 7 +
          420 * (x - n) ^ 6 - 210 * (x - n) ^ 4 +
          60 * (x - n) ^ 2 - 3) x := by
    have hbase : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (n : ℝ)
    have hnine :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 9)
          (9 * (x - (n : ℝ)) ^ 8) x := by
      simpa using hbase.pow 9
    have height :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 8)
          (8 * (x - (n : ℝ)) ^ 7) x := by
      simpa using hbase.pow 8
    have hseven :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 7)
          (7 * (x - (n : ℝ)) ^ 6) x := by
      simpa using hbase.pow 7
    have hfive :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 5)
          (5 * (x - (n : ℝ)) ^ 4) x := by
      simpa using hbase.pow 5
    have hthree :
        HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 3)
          (3 * (x - (n : ℝ)) ^ 2) x := by
      simpa using hbase.pow 3
    have hpoly :=
      (((((hnine.const_mul (10 : ℝ)).sub (height.const_mul (45 : ℝ))).add
        (hseven.const_mul (60 : ℝ))).sub
        (hfive.const_mul (42 : ℝ))).add
        (hthree.const_mul (20 : ℝ))).sub (hbase.const_mul (3 : ℝ))
    convert hpoly using 1
    ring
  have hcoef :
      90 * bernoulli8Diff x =
        90 * (x - n) ^ 8 - 360 * (x - n) ^ 7 +
          420 * (x - n) ^ 6 - 210 * (x - n) ^ 4 +
          60 * (x - n) ^ 2 - 3 := by
    have hcell := bernoulli8Diff_eq_on_Ioo n hx
    nlinarith [hcell]
  simpa [hcoef] using hderiv

lemma add_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + z ≠ 0 := by
  intro hzero
  have hrew : ((x : ℂ) + z).re = x + z.re := by simp
  have hzero' : x + z.re = 0 := by
    simpa [hrew] using congrArg Complex.re hzero
  have hpos : 0 < x + z.re := by nlinarith [hz, hx]
  linarith

lemma add_mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + z ∈ Complex.slitPlane := by
  have hnot : ¬ (x : ℂ) + z ≤ 0 := by
    intro hle
    have hrew : ((x : ℂ) + z).re = x + z.re := by simp
    have hle' : x + z.re ≤ 0 := by
      simpa [hrew] using (Complex.re_le_re hle)
    have hpos : 0 < x + z.re := by nlinarith [hz, hx]
    linarith
  exact (Complex.mem_slitPlane_iff_not_le_zero).2 hnot

lemma hasDerivAt_inv_add (z : ℂ) {x : ℝ} (hx : (x : ℂ) + z ≠ 0) :
    HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
  have h_ofReal : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
    simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
  have h_add : HasDerivAt (fun w : ℂ => w + z) (1 : ℂ) (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).add_const z
  have h_inv : HasDerivAt (fun w : ℂ => (w + z)⁻¹)
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) (x : ℂ) := by
    simpa [one_div] using (h_add.inv hx)
  simpa using (h_inv.comp x h_ofReal)

lemma hasDerivAt_log_add (z : ℂ) {x : ℝ} (hx : (x : ℂ) + z ∈ Complex.slitPlane) :
    HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + z)) (((x : ℂ) + z)⁻¹) x := by
  have h_ofReal : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
    simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
  have h_add : HasDerivAt (fun x : ℝ => (x : ℂ) + z) (1 : ℂ) x := by
    simpa using h_ofReal.add_const z
  have h_log : HasDerivAt (fun w : ℂ => Complex.log w) (((x : ℂ) + z)⁻¹) ((x : ℂ) + z) :=
    Complex.hasDerivAt_log hx
  simpa using (h_log.comp x h_add)

lemma stieltjes_interval_identity (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ), ((x : ℂ) + z)⁻¹ =
      (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) -
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * (-(((x : ℂ) + z) ^ 2)⁻¹)) := by
  classical
  let u : ℝ → ℂ := fun x => (x - (n : ℝ) - (1 / 2 : ℝ) : ℂ)
  let u' : ℝ → ℂ := fun _ => (1 : ℂ)
  let v : ℝ → ℂ := fun x => ((x : ℂ) + z)⁻¹
  let v' : ℝ → ℂ := fun x => -(((x : ℂ) + z) ^ 2)⁻¹
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    simpa [u, u', sub_eq_add_neg, add_assoc] using h1.sub_const (1 / 2 : ℂ)
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    simpa [v, v', one_div, div_eq_mul_inv] using (hasDerivAt_inv_add z hneq)
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    simpa [u'] using
      (intervalIntegrable_const (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume) (c := (1 : ℂ)))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne : ((x : ℂ) + z) ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 hneq
      have hcont_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow hne)
      have hcont_neg :
          ContinuousAt (fun x : ℝ => -(((x : ℂ) + z) ^ 2)⁻¹) x := hcont_inv.neg
      have hrewrite : (fun x : ℝ => -(((x : ℂ) + z) ^ 2)⁻¹) = v' := by
        rfl
      simpa [hrewrite] using hcont_neg.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have hsum :
      (∫ x in (n : ℝ)..(n + 1 : ℝ), v x) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) := by
    have hparts' := (eq_sub_iff_add_eq).1 hparts
    simpa [u', add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hparts'
  have hfinal :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), v x =
        u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    refine (eq_sub_iff_add_eq).2 ?_
    simpa [add_comm, add_left_comm, add_assoc] using hsum
  have hu_left : u (n : ℝ) = (-(2 : ℂ)⁻¹) := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = (2 : ℂ)⁻¹ := by
    simp [u]
    norm_num
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ), v x
        = u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
            ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hfinal
    _ = (1 / 2 : ℂ) * (v (n : ℝ) + v (n + 1 : ℝ)) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
      simp [hu_left, hu_right, add_comm, add_left_comm, add_assoc, mul_add, sub_eq_add_neg, one_div]
    _ = (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
      simp [v, add_comm, add_left_comm, add_assoc]
    _ = (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * (-(((x : ℂ) + z) ^ 2)⁻¹)) := by
      simp [u, v']

lemma stieltjes_interval_identity_pos (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ), ((x : ℂ) + z)⁻¹ =
      (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * (((x : ℂ) + z) ^ 2)⁻¹) := by
  have h := stieltjes_interval_identity z hz n
  -- move the negative sign inside the integral
  simpa [sub_eq_add_neg, mul_neg, neg_mul, one_div] using h

lemma stieltjes_interval_B1_to_B2 (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * ((1 : ℂ) / ((x : ℂ) + z) ^ 2)) =
      -∫ x in (n : ℝ)..(n + 1 : ℝ),
          (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3 := by
  classical
  let u : ℝ → ℂ := fun x =>
    (x : ℂ) + -(n : ℂ) + -(((x : ℂ) + -(n : ℂ)) ^ 2)
  let u' : ℝ → ℂ := fun x => (1 : ℂ) - (2 : ℂ) * ((x : ℂ) - (n : ℂ))
  let v : ℝ → ℂ := fun x => (1 : ℂ) / ((x : ℂ) + z) ^ 2
  let v' : ℝ → ℂ := fun x => -(2 : ℂ) * (((x : ℂ) + z) ^ 3)⁻¹
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_sq :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2)
          ((2 : ℂ) * ((x : ℂ) - (n : ℂ))) x := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using (h_sub.pow 2)
    have h := h_sub.sub h_sq
    -- rewrite the function and derivative to match `u` and `u'`
    convert h using 1 <;>
      simp [u, u', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    have h_pow :
        HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ 2)
          ((2 : ℂ) * ((x : ℂ) + z)⁻¹ * (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)) x := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, one_div] using (h_inv.pow 2)
    have hrewrite :
        (2 : ℂ) * ((x : ℂ) + z)⁻¹ * (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) =
          -(2 : ℂ) / ((x : ℂ) + z) ^ 3 := by
      field_simp [hneq]
    have hpow' :
        HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ 2) (-(2 : ℂ) / ((x : ℂ) + z) ^ 3) x := by
      simpa [hrewrite] using h_pow
    simpa [v, v', pow_two, one_div, div_eq_mul_inv] using hpow'
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_mul : Continuous fun x : ℝ => (2 : ℂ) * ((x : ℂ) - (n : ℂ)) :=
        continuous_const.mul hcont_sub
      simpa [u', sub_eq_add_neg] using (continuous_const.sub hcont_mul)
    simpa [u'] using (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 3) x := hcont_add.pow 3
      have hne : ((x : ℂ) + z) ^ 3 ≠ 0 := by
        exact pow_ne_zero 3 hneq
      have hcont_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 3)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow hne)
      have hcont_mul :
          ContinuousAt (fun x : ℝ => (2 : ℂ) * (((x : ℂ) + z) ^ 3)⁻¹) x := by
        simpa using hcont_inv.const_mul (2 : ℂ)
      have hcont_neg :
          ContinuousAt (fun x : ℝ => -(2 * (((x : ℂ) + z) ^ 3)⁻¹)) x := by
        simpa using hcont_mul.neg
      have hrewrite : (fun x : ℝ => -(2 * (((x : ℂ) + z) ^ 3)⁻¹)) = v' := by
        ext x
        simp [v', neg_mul, mul_comm, mul_left_comm, mul_assoc]
      simpa [hrewrite] using hcont_neg.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have hu_left : u (n : ℝ) = 0 := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = 0 := by
    simp [u, pow_two, add_assoc, add_left_comm, add_comm]
  have hparts' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    simpa [hu_left, hu_right] using hparts
  have h_u' :
      ∀ x, u' x = -(2 : ℂ) * (x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) := by
    intro x
    simp [u', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    ring_nf
  have h_u'v :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        (-(2 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * v x) := by
    have hfun :
        (fun x : ℝ => u' x * v x) =
          fun x : ℝ => (-(2 : ℂ)) * ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * v x) := by
      ext x
      simp [h_u' x, mul_assoc, mul_left_comm, mul_comm]
    simpa [hfun] using
      (intervalIntegral.integral_const_mul (c := (-(2 : ℂ)))
        (f := fun x : ℝ => ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * v x))
        (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(2 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          u x / ((x : ℂ) + z) ^ 3 := by
    have hfun :
        (fun x : ℝ => u x * v' x) =
          fun x : ℝ => (-(2 : ℂ)) * (u x / ((x : ℂ) + z) ^ 3) := by
      ext x
      simp [v', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    simpa [hfun] using
      (intervalIntegral.integral_const_mul (c := (-(2 : ℂ)))
        (f := fun x : ℝ => u x / ((x : ℂ) + z) ^ 3)
        (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hrel :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * v x) =
        -∫ x in (n : ℝ)..(n + 1 : ℝ),
          u x / ((x : ℂ) + z) ^ 3 := by
    have htmp := congrArg (fun t => (-(1 / 2 : ℂ)) * t) hparts'
    simp [h_u'v, h_uv', mul_add, mul_comm, mul_left_comm, mul_assoc] at htmp
    have htmp' := congrArg (fun t => -t) htmp.symm
    simpa [mul_comm, mul_left_comm, mul_assoc] using htmp'
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * v x)
        = -∫ x in (n : ℝ)..(n + 1 : ℝ),
            u x / ((x : ℂ) + z) ^ 3 := by
              simpa [v] using hrel
    _ = -∫ x in (n : ℝ)..(n + 1 : ℝ),
          (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3 := by
          simp [u, sub_eq_add_neg, div_eq_mul_inv, pow_succ, pow_two, add_assoc, add_left_comm,
            add_comm, mul_comm, mul_left_comm, mul_assoc]

lemma stieltjes_interval_B1_to_B2Diff (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * (((x : ℂ) + z) ^ 2)⁻¹) =
      -∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
  have h :=
    (stieltjes_interval_B1_to_B2 z hz n)
  have h' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * (((x : ℂ) + z) ^ 2)⁻¹) =
        -∫ x in (n : ℝ)..(n + 1 : ℝ),
            (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3 := by
    simpa [one_div] using h
  have h_eq :
      EqOn
        (fun x : ℝ => (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ))
        (fun x : ℝ => (bernoulli2Diff x : ℂ))
        (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    by_cases hx0 : x = n
    · simp [hx0, bernoulli2Diff, bernoulli2]
    by_cases hx1 : x = n + 1
    · simp [hx1, bernoulli2Diff, bernoulli2]
    have hx' : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
      refine ⟨?_, ?_⟩
      · exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
      · exact lt_of_le_of_ne hx.2 hx1
    have hreal : bernoulli2Diff x = (x - n) - (x - n) ^ 2 :=
      bernoulli2Diff_eq_on_Ioo n hx'
    simpa [hreal]
  have h_int :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa using hx
    have h' := h_eq hx'
    simpa [h'] 
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * (((x : ℂ) + z) ^ 2)⁻¹)
        = -∫ x in (n : ℝ)..(n + 1 : ℝ),
            (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3 := h'
    _ = -∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
          simpa using (congrArg (fun t => -t) h_int)

lemma stieltjes_interval_B2_poly_to_B4CellDeriv (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
          ((x : ℂ) + z) ^ 3 =
      (1 / 4 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4 := by
  classical
  let u : ℝ → ℂ := fun x =>
    (12 : ℂ)⁻¹ * ((4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
        (6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 +
        (2 : ℂ) * ((x : ℂ) - (n : ℂ)))
  let u' : ℝ → ℂ := fun x =>
    ((x : ℂ) - (n : ℂ)) ^ 2 - ((x : ℂ) - (n : ℂ)) + (6 : ℂ)⁻¹
  let v : ℝ → ℂ := (fun x : ℝ => ((x : ℂ) + z)⁻¹) ^ 3
  let v' : ℝ → ℂ := fun x =>
    (3 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (3 - 1) *
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_cube :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3)
          ((3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2) x := by
      simpa using h_sub.pow 3
    have h_square :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2)
          ((2 : ℂ) * ((x : ℂ) - (n : ℂ))) x := by
      simpa using h_sub.pow 2
    have h_poly :
        HasDerivAt
          (fun x : ℝ =>
            (4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
              (6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 +
              (2 : ℂ) * ((x : ℂ) - (n : ℂ)))
          ((12 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 -
            (12 : ℂ) * ((x : ℂ) - (n : ℂ)) + (2 : ℂ)) x := by
      have h :=
        ((h_cube.const_mul (4 : ℂ)).sub (h_square.const_mul (6 : ℂ))).add
          (h_sub.const_mul (2 : ℂ))
      convert h using 1 <;> ring
    have h_scaled := h_poly.const_mul ((12 : ℂ)⁻¹)
    have hderiv :
        (12 : ℂ)⁻¹ *
            ((12 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 -
              (12 : ℂ) * ((x : ℂ) - (n : ℂ)) + (2 : ℂ)) =
          u' x := by
      field_simp [u']
      ring
    simpa [u, hderiv] using h_scaled
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    simpa [v, v'] using h_inv.pow 3
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_sq : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2 :=
        hcont_sub.pow 2
      simpa [u', sub_eq_add_neg] using (hcont_sq.sub hcont_sub).add continuous_const
    simpa [u'] using
      (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_inv_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ (3 - 1)) x :=
        hcont_inv.pow (3 - 1)
      have hcont_pow2 :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne2 : ((x : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
      have hcont_pow2_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow2 hne2)
      have hcont_neg_div :
          ContinuousAt (fun x : ℝ => -(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
        simpa [div_eq_mul_inv] using hcont_pow2_inv.const_mul (-(1 : ℂ))
      have hcont_left :
          ContinuousAt (fun x : ℝ => (3 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (3 - 1)) x :=
        continuous_const.continuousAt.mul hcont_inv_pow
      have hcont_mul := hcont_left.mul hcont_neg_div
      simpa [v', mul_assoc] using hcont_mul.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have hu_left : u (n : ℝ) = 0 := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = 0 := by
    norm_num [u, Nat.cast_add, Nat.cast_one]
  have hparts' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    simpa [hu_left, hu_right] using hparts
  have hrel :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    rw [hparts']
    simp
  have h_left :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 3 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [u', v, div_eq_mul_inv]
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(1 / 4 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4 := by
    have h_int :
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (-(1 / 4 : ℂ)) *
              ((bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        simpa using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      simp [u, v', bernoulli4DiffCellDeriv, div_eq_mul_inv, one_div]
      field_simp [hneq]
      ring
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x
          = ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (-(1 / 4 : ℂ)) *
                ((bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4) := h_int
      _ = (-(1 / 4 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4 := by
        simpa using
          (intervalIntegral.integral_const_mul (c := (-(1 / 4 : ℂ)))
            (f := fun x : ℝ => (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4)
            (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
          ((x : ℂ) + z) ^ 3
        = ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := h_left
    _ = -∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hrel
    _ = (1 / 4 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4 := by
          rw [h_uv']
          ring

lemma stieltjes_interval_B2Fract_to_B4CellDeriv (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3 =
      (1 / 4 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4 := by
  have h_eq :
      EqOn
        (fun x : ℝ => (bernoulli2Fract x : ℂ))
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ))
        (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    by_cases hx0 : x = n
    · simp [hx0, bernoulli2Fract, bernoulli2]
    by_cases hx1 : x = n + 1
    · simp [hx1, bernoulli2Fract, bernoulli2]
    have hx' : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
      refine ⟨?_, ?_⟩
      · exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
      · exact lt_of_le_of_ne hx.2 hx1
    have hreal := bernoulli2Fract_eq_on_Ioo n hx'
    simpa [hreal]
  have h_int :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 3 := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa using hx
    have h' := h_eq hx'
    simpa [h']
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3
        =
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
          ((x : ℂ) + z) ^ 3 := h_int
    _ = (1 / 4 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4 :=
      stieltjes_interval_B2_poly_to_B4CellDeriv z hz n

lemma stieltjes_interval_B4CellDeriv_to_B4Diff (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4 =
      (-(30 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 4 - (((n : ℂ) + z)⁻¹) ^ 4) +
        (4 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
  classical
  let u : ℝ → ℂ := fun x =>
    ((x : ℂ) - (n : ℂ)) ^ 4 -
      (2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
      ((x : ℂ) - (n : ℂ)) ^ 2 - (30 : ℂ)⁻¹
  let u' : ℝ → ℂ := fun x => (bernoulli4DiffCellDeriv n x : ℂ)
  let v : ℝ → ℂ := (fun x : ℝ => ((x : ℂ) + z)⁻¹) ^ 4
  let v' : ℝ → ℂ := fun x =>
    (4 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (4 - 1) *
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_four :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4)
          ((4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3) x := by
      simpa using h_sub.pow 4
    have h_cube :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3)
          ((3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2) x := by
      simpa using h_sub.pow 3
    have h_square :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2)
          ((2 : ℂ) * ((x : ℂ) - (n : ℂ))) x := by
      simpa using h_sub.pow 2
    have h_poly :=
      ((h_four.sub (h_cube.const_mul (2 : ℂ))).add h_square).sub_const (30 : ℂ)⁻¹
    convert h_poly using 1 <;>
      simp [u, u', bernoulli4DiffCellDeriv, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] <;> ring
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    simpa [v, v'] using h_inv.pow 4
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_cube : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3 :=
        hcont_sub.pow 3
      have hcont_square : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2 :=
        hcont_sub.pow 2
      have hcont_poly :
          Continuous fun x : ℝ =>
            (4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
              (6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 +
              (2 : ℂ) * ((x : ℂ) - (n : ℂ)) := by
        exact ((continuous_const.mul hcont_cube).sub
          (continuous_const.mul hcont_square)).add (continuous_const.mul hcont_sub)
      simpa [u', bernoulli4DiffCellDeriv, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hcont_poly
    simpa [u'] using
      (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_inv_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ (4 - 1)) x :=
        hcont_inv.pow (4 - 1)
      have hcont_pow2 :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne2 : ((x : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
      have hcont_pow2_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow2 hne2)
      have hcont_neg_div :
          ContinuousAt (fun x : ℝ => -(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
        simpa [div_eq_mul_inv] using hcont_pow2_inv.const_mul (-(1 : ℂ))
      have hcont_left :
          ContinuousAt (fun x : ℝ => (4 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (4 - 1)) x :=
        continuous_const.continuousAt.mul hcont_inv_pow
      have hcont_mul := hcont_left.mul hcont_neg_div
      simpa [v', mul_assoc] using hcont_mul.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have h_left :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [u', v, div_eq_mul_inv]
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(4 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
    have h_int :
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (-(4 : ℂ)) * ((bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        simpa using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcell := bernoulli4Diff_eq_cell_on_Icc n hx'
      simp [u, v', hcell, div_eq_mul_inv, one_div]
      field_simp [hneq]
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x
          = ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (-(4 : ℂ)) * ((bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5) := h_int
      _ = (-(4 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
        simpa using
          (intervalIntegral.integral_const_mul (c := (-(4 : ℂ)))
            (f := fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
            (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hu_left : u (n : ℝ) = (-(30 : ℂ)⁻¹) := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = (-(30 : ℂ)⁻¹) := by
    norm_num [u, Nat.cast_add, Nat.cast_one]
  have hsum_parts :
      (∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
          u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) := by
    have hparts' := (eq_sub_iff_add_eq).1 hparts
    simpa [add_comm, add_left_comm, add_assoc] using hparts'
  have hparts_rev :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    refine (eq_sub_iff_add_eq).2 ?_
    simpa [add_comm, add_left_comm, add_assoc] using hsum_parts
  have hboundary :
      u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) =
        (-(30 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 4 - (((n : ℂ) + z)⁻¹) ^ 4) := by
    rw [hu_right, hu_left]
    simp [v, sub_eq_add_neg, mul_sub, mul_add, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc]
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4
        = ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := h_left
    _ = u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hparts_rev
    _ = (-(30 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 4 - (((n : ℂ) + z)⁻¹) ^ 4) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
          rw [hboundary]
    _ = (-(30 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 4 - (((n : ℂ) + z)⁻¹) ^ 4) +
        (4 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
          rw [h_uv']
          ring

lemma stieltjes_interval_B4Diff_to_B6CellDeriv (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 =
      (1 / 6 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6 := by
  classical
  let u : ℝ → ℂ := fun x =>
    (30 : ℂ)⁻¹ *
      ((6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 -
        (15 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
        (10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
        ((x : ℂ) - (n : ℂ)))
  let u' : ℝ → ℂ := fun x =>
    ((x : ℂ) - (n : ℂ)) ^ 4 -
      (2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
      ((x : ℂ) - (n : ℂ)) ^ 2 - (30 : ℂ)⁻¹
  let v : ℝ → ℂ := (fun x : ℝ => ((x : ℂ) + z)⁻¹) ^ 5
  let v' : ℝ → ℂ := fun x =>
    (5 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (5 - 1) *
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_five :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 5)
          ((5 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4) x := by
      simpa using h_sub.pow 5
    have h_four :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4)
          ((4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3) x := by
      simpa using h_sub.pow 4
    have h_cube :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3)
          ((3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2) x := by
      simpa using h_sub.pow 3
    have h_poly :
        HasDerivAt
          (fun x : ℝ =>
            (6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 -
              (15 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
              (10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
              ((x : ℂ) - (n : ℂ)))
          ((30 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
            (60 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
            (30 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 - (1 : ℂ)) x := by
      have h :=
        (((h_five.const_mul (6 : ℂ)).sub (h_four.const_mul (15 : ℂ))).add
          (h_cube.const_mul (10 : ℂ))).sub h_sub
      convert h using 1 <;> ring
    have h_scaled := h_poly.const_mul ((30 : ℂ)⁻¹)
    have hderiv :
        (30 : ℂ)⁻¹ *
            ((30 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
              (60 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
              (30 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 - (1 : ℂ)) =
          u' x := by
      field_simp [u']
      ring
    simpa [u, hderiv] using h_scaled
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    simpa [v, v'] using h_inv.pow 5
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_four : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4 :=
        hcont_sub.pow 4
      have hcont_cube : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3 :=
        hcont_sub.pow 3
      have hcont_square : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2 :=
        hcont_sub.pow 2
      have hcont_poly :
          Continuous fun x : ℝ =>
            ((x : ℂ) - (n : ℂ)) ^ 4 -
              (2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
              ((x : ℂ) - (n : ℂ)) ^ 2 - (30 : ℂ)⁻¹ := by
        exact ((hcont_four.sub (continuous_const.mul hcont_cube)).add
          hcont_square).sub continuous_const
      simpa [u', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcont_poly
    simpa [u'] using
      (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_inv_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ (5 - 1)) x :=
        hcont_inv.pow (5 - 1)
      have hcont_pow2 :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne2 : ((x : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
      have hcont_pow2_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow2 hne2)
      have hcont_neg_div :
          ContinuousAt (fun x : ℝ => -(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
        simpa [div_eq_mul_inv] using hcont_pow2_inv.const_mul (-(1 : ℂ))
      have hcont_left :
          ContinuousAt (fun x : ℝ => (5 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (5 - 1)) x :=
        continuous_const.continuousAt.mul hcont_inv_pow
      have hcont_mul := hcont_left.mul hcont_neg_div
      simpa [v', mul_assoc] using hcont_mul.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have hu_left : u (n : ℝ) = 0 := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = 0 := by
    norm_num [u, Nat.cast_add, Nat.cast_one]
  have hparts' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    simpa [hu_left, hu_right] using hparts
  have hrel :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    rw [hparts']
    simp
  have h_left :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa using hx
    have hcell := bernoulli4Diff_eq_cell_on_Icc n hx'
    simp [u', v, hcell, div_eq_mul_inv]
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(1 / 6 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6 := by
    have h_int :
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (-(1 / 6 : ℂ)) *
              ((bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        simpa using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      simp [u, v', bernoulli6DiffCellDeriv, div_eq_mul_inv, one_div]
      field_simp [hneq]
      ring
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x
          = ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (-(1 / 6 : ℂ)) *
                ((bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6) := h_int
      _ = (-(1 / 6 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6 := by
        simpa using
          (intervalIntegral.integral_const_mul (c := (-(1 / 6 : ℂ)))
            (f := fun x : ℝ => (bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6)
            (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5
        = ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := h_left
    _ = -∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hrel
    _ = (1 / 6 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6 := by
          rw [h_uv']
          ring

lemma stieltjes_interval_B6Diff_to_B8CellDeriv (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 =
      (1 / 8 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8 := by
  classical
  let u : ℝ → ℂ := fun x =>
    (56 : ℂ)⁻¹ *
      ((8 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 -
        (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 +
        (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 -
        (28 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
        (4 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)))
  let u' : ℝ → ℂ := fun x =>
    ((x : ℂ) - (n : ℂ)) ^ 6 -
      (3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
      (5 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
      (1 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 + (42 : ℂ)⁻¹
  let v : ℝ → ℂ := (fun x : ℝ => ((x : ℂ) + z)⁻¹) ^ 7
  let v' : ℝ → ℂ := fun x =>
    (7 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (7 - 1) *
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_seven :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 7)
          ((7 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6) x := by
      simpa using h_sub.pow 7
    have h_six :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 6)
          ((6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5) x := by
      simpa using h_sub.pow 6
    have h_five :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 5)
          ((5 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4) x := by
      simpa using h_sub.pow 5
    have h_cube :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3)
          ((3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2) x := by
      simpa using h_sub.pow 3
    have h_poly :
        HasDerivAt
          (fun x : ℝ =>
            (8 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 -
              (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 +
              (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 -
              (28 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
              (4 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)))
          ((56 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 -
            (168 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
            (140 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
            (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 + (4 / 3 : ℂ)) x := by
      have h :=
        ((((h_seven.const_mul (8 : ℂ)).sub (h_six.const_mul (28 : ℂ))).add
          (h_five.const_mul (28 : ℂ))).sub
          (h_cube.const_mul (28 / 3 : ℂ))).add (h_sub.const_mul (4 / 3 : ℂ))
      convert h using 1 <;> ring
    have h_scaled := h_poly.const_mul ((56 : ℂ)⁻¹)
    have hderiv :
        (56 : ℂ)⁻¹ *
            ((56 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 -
              (168 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
              (140 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
              (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 + (4 / 3 : ℂ)) =
          u' x := by
      field_simp [u']
      ring
    simpa [u, hderiv] using h_scaled
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    simpa [v, v'] using h_inv.pow 7
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_six : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 6 :=
        hcont_sub.pow 6
      have hcont_five : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 5 :=
        hcont_sub.pow 5
      have hcont_four : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4 :=
        hcont_sub.pow 4
      have hcont_square : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2 :=
        hcont_sub.pow 2
      have hcont_poly :
          Continuous fun x : ℝ =>
            ((x : ℂ) - (n : ℂ)) ^ 6 -
              (3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
              (5 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
              (1 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 + (42 : ℂ)⁻¹ := by
        exact ((((hcont_six.sub (continuous_const.mul hcont_five)).add
          (continuous_const.mul hcont_four)).sub
          (continuous_const.mul hcont_square)).add continuous_const)
      simpa [u', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcont_poly
    simpa [u'] using
      (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_inv_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ (7 - 1)) x :=
        hcont_inv.pow (7 - 1)
      have hcont_pow2 :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne2 : ((x : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
      have hcont_pow2_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow2 hne2)
      have hcont_neg_div :
          ContinuousAt (fun x : ℝ => -(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
        simpa [div_eq_mul_inv] using hcont_pow2_inv.const_mul (-(1 : ℂ))
      have hcont_left :
          ContinuousAt (fun x : ℝ => (7 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (7 - 1)) x :=
        continuous_const.continuousAt.mul hcont_inv_pow
      have hcont_mul := hcont_left.mul hcont_neg_div
      simpa [v', mul_assoc] using hcont_mul.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have hu_left : u (n : ℝ) = 0 := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = 0 := by
    norm_num [u, Nat.cast_add, Nat.cast_one]
  have hparts' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    simpa [hu_left, hu_right] using hparts
  have hrel :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    rw [hparts']
    simp
  have h_left :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa using hx
    have hcell := bernoulli6Diff_eq_cell_on_Icc n hx'
    simp [u', v, hcell, div_eq_mul_inv]
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(1 / 8 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8 := by
    have h_int :
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (-(1 / 8 : ℂ)) *
              ((bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        simpa using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      simp [u, v', bernoulli8DiffCellDeriv, div_eq_mul_inv, one_div]
      field_simp [hneq]
      ring
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x
          = ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (-(1 / 8 : ℂ)) *
                ((bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8) := h_int
      _ = (-(1 / 8 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8 := by
        simpa using
          (intervalIntegral.integral_const_mul (c := (-(1 / 8 : ℂ)))
            (f := fun x : ℝ => (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8)
            (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
        = ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := h_left
    _ = -∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hrel
    _ = (1 / 8 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8 := by
          rw [h_uv']
          ring

lemma stieltjes_interval_B8Diff_to_B10CellDeriv (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 =
      (1 / 10 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10 := by
  classical
  let u : ℝ → ℂ := fun x =>
    (90 : ℂ)⁻¹ *
      ((10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 9 -
        (45 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8 +
        (60 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 -
        (42 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
        (20 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
        (3 : ℂ) * ((x : ℂ) - (n : ℂ)))
  let u' : ℝ → ℂ := fun x =>
    ((x : ℂ) - (n : ℂ)) ^ 8 -
      (4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 +
      (14 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 -
      (7 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
      (2 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 - (30 : ℂ)⁻¹
  let v : ℝ → ℂ := (fun x : ℝ => ((x : ℂ) + z)⁻¹) ^ 9
  let v' : ℝ → ℂ := fun x =>
    (9 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (9 - 1) *
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_nine :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 9)
          ((9 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8) x := by
      simpa using h_sub.pow 9
    have h_eight :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 8)
          ((8 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7) x := by
      simpa using h_sub.pow 8
    have h_seven :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 7)
          ((7 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6) x := by
      simpa using h_sub.pow 7
    have h_five :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 5)
          ((5 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4) x := by
      simpa using h_sub.pow 5
    have h_cube :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3)
          ((3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2) x := by
      simpa using h_sub.pow 3
    have h_poly :
        HasDerivAt
          (fun x : ℝ =>
            (10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 9 -
              (45 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8 +
              (60 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 -
              (42 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
              (20 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
              (3 : ℂ) * ((x : ℂ) - (n : ℂ)))
          ((90 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8 -
            (360 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 +
            (420 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 -
            (210 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
            (60 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 - (3 : ℂ)) x := by
      have h :=
        (((((h_nine.const_mul (10 : ℂ)).sub (h_eight.const_mul (45 : ℂ))).add
          (h_seven.const_mul (60 : ℂ))).sub
          (h_five.const_mul (42 : ℂ))).add
          (h_cube.const_mul (20 : ℂ))).sub (h_sub.const_mul (3 : ℂ))
      convert h using 1 <;> ring
    have h_scaled := h_poly.const_mul ((90 : ℂ)⁻¹)
    have hderiv :
        (90 : ℂ)⁻¹ *
            ((90 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8 -
              (360 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 +
              (420 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 -
              (210 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
              (60 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 - (3 : ℂ)) =
          u' x := by
      field_simp [u']
      ring
    simpa [u, hderiv] using h_scaled
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    simpa [v, v'] using h_inv.pow 9
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_eight : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 8 :=
        hcont_sub.pow 8
      have hcont_seven : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 7 :=
        hcont_sub.pow 7
      have hcont_six : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 6 :=
        hcont_sub.pow 6
      have hcont_four : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4 :=
        hcont_sub.pow 4
      have hcont_square : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2 :=
        hcont_sub.pow 2
      have hcont_poly :
          Continuous fun x : ℝ =>
            ((x : ℂ) - (n : ℂ)) ^ 8 -
              (4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 +
              (14 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 -
              (7 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
              (2 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 - (30 : ℂ)⁻¹ := by
        exact (((((hcont_eight.sub (continuous_const.mul hcont_seven)).add
          (continuous_const.mul hcont_six)).sub
          (continuous_const.mul hcont_four)).add
          (continuous_const.mul hcont_square)).sub continuous_const)
      simpa [u', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcont_poly
    simpa [u'] using
      (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_inv_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ (9 - 1)) x :=
        hcont_inv.pow (9 - 1)
      have hcont_pow2 :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne2 : ((x : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
      have hcont_pow2_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow2 hne2)
      have hcont_neg_div :
          ContinuousAt (fun x : ℝ => -(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
        simpa [div_eq_mul_inv] using hcont_pow2_inv.const_mul (-(1 : ℂ))
      have hcont_left :
          ContinuousAt (fun x : ℝ => (9 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (9 - 1)) x :=
        continuous_const.continuousAt.mul hcont_inv_pow
      have hcont_mul := hcont_left.mul hcont_neg_div
      simpa [v', mul_assoc] using hcont_mul.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have hu_left : u (n : ℝ) = 0 := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = 0 := by
    norm_num [u, Nat.cast_add, Nat.cast_one]
  have hparts' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    simpa [hu_left, hu_right] using hparts
  have hrel :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        -∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    rw [hparts']
    simp
  have h_left :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa using hx
    have hcell := bernoulli8Diff_eq_cell_on_Icc n hx'
    simp [u', v, hcell, div_eq_mul_inv]
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(1 / 10 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10 := by
    have h_int :
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (-(1 / 10 : ℂ)) *
              ((bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        simpa using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      simp [u, v', bernoulli10DiffCellDeriv, div_eq_mul_inv, one_div]
      field_simp [hneq]
      ring
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x
          = ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (-(1 / 10 : ℂ)) *
                ((bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10) := h_int
      _ = (-(1 / 10 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10 := by
        simpa using
          (intervalIntegral.integral_const_mul (c := (-(1 / 10 : ℂ)))
            (f := fun x : ℝ => (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10)
            (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9
        = ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := h_left
    _ = -∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hrel
    _ = (1 / 10 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10 := by
          rw [h_uv']
          ring

lemma stieltjes_interval_B6CellDeriv_to_B6Diff (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6 =
      (42 : ℂ)⁻¹ *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 6 - (((n : ℂ) + z)⁻¹) ^ 6) +
        (6 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
  classical
  let u : ℝ → ℂ := fun x =>
    ((x : ℂ) - (n : ℂ)) ^ 6 -
      (3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
      (5 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
      (1 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 + (42 : ℂ)⁻¹
  let u' : ℝ → ℂ := fun x => (bernoulli6DiffCellDeriv n x : ℂ)
  let v : ℝ → ℂ := (fun x : ℝ => ((x : ℂ) + z)⁻¹) ^ 6
  let v' : ℝ → ℂ := fun x =>
    (6 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (6 - 1) *
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_six :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 6)
          ((6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5) x := by
      simpa using h_sub.pow 6
    have h_five :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 5)
          ((5 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4) x := by
      simpa using h_sub.pow 5
    have h_four :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4)
          ((4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3) x := by
      simpa using h_sub.pow 4
    have h_square :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2)
          ((2 : ℂ) * ((x : ℂ) - (n : ℂ))) x := by
      simpa using h_sub.pow 2
    have h_poly :
        HasDerivAt
          (fun x : ℝ =>
            ((x : ℂ) - (n : ℂ)) ^ 6 -
              (3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
              (5 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
              (1 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 + (42 : ℂ)⁻¹)
          ((6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 -
            (15 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
            (10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
            ((x : ℂ) - (n : ℂ))) x := by
      have h :=
        ((((h_six.sub (h_five.const_mul (3 : ℂ))).add
          (h_four.const_mul (5 / 2 : ℂ))).sub
          (h_square.const_mul (1 / 2 : ℂ))).add_const (42 : ℂ)⁻¹)
      convert h using 1 <;> ring
    convert h_poly using 1 <;>
      simp [u, u', bernoulli6DiffCellDeriv, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] <;> ring
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    simpa [v, v'] using h_inv.pow 6
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_five : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 5 :=
        hcont_sub.pow 5
      have hcont_four : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4 :=
        hcont_sub.pow 4
      have hcont_cube : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3 :=
        hcont_sub.pow 3
      have hcont_poly :
          Continuous fun x : ℝ =>
            (6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 -
              (15 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
              (10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
              ((x : ℂ) - (n : ℂ)) := by
        exact (((continuous_const.mul hcont_five).sub
          (continuous_const.mul hcont_four)).add
          (continuous_const.mul hcont_cube)).sub hcont_sub
      simpa [u', bernoulli6DiffCellDeriv, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hcont_poly
    simpa [u'] using
      (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_inv_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ (6 - 1)) x :=
        hcont_inv.pow (6 - 1)
      have hcont_pow2 :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne2 : ((x : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
      have hcont_pow2_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow2 hne2)
      have hcont_neg_div :
          ContinuousAt (fun x : ℝ => -(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
        simpa [div_eq_mul_inv] using hcont_pow2_inv.const_mul (-(1 : ℂ))
      have hcont_left :
          ContinuousAt (fun x : ℝ => (6 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (6 - 1)) x :=
        continuous_const.continuousAt.mul hcont_inv_pow
      have hcont_mul := hcont_left.mul hcont_neg_div
      simpa [v', mul_assoc] using hcont_mul.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have h_left :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [u', v, div_eq_mul_inv]
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(6 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
    have h_int :
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (-(6 : ℂ)) * ((bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        simpa using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcell := bernoulli6Diff_eq_cell_on_Icc n hx'
      simp [u, v', hcell, div_eq_mul_inv, one_div]
      field_simp [hneq]
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x
          = ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (-(6 : ℂ)) * ((bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7) := h_int
      _ = (-(6 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
        simpa using
          (intervalIntegral.integral_const_mul (c := (-(6 : ℂ)))
            (f := fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
            (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hu_left : u (n : ℝ) = (42 : ℂ)⁻¹ := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = (42 : ℂ)⁻¹ := by
    norm_num [u, Nat.cast_add, Nat.cast_one]
  have hsum_parts :
      (∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
          u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) := by
    have hparts' := (eq_sub_iff_add_eq).1 hparts
    simpa [add_comm, add_left_comm, add_assoc] using hparts'
  have hparts_rev :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    refine (eq_sub_iff_add_eq).2 ?_
    simpa [add_comm, add_left_comm, add_assoc] using hsum_parts
  have hboundary :
      u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) =
        (42 : ℂ)⁻¹ *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 6 - (((n : ℂ) + z)⁻¹) ^ 6) := by
    rw [hu_right, hu_left]
    simp [v, sub_eq_add_neg, mul_sub, mul_add, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc]
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli6DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 6
        = ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := h_left
    _ = u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hparts_rev
    _ = (42 : ℂ)⁻¹ *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 6 - (((n : ℂ) + z)⁻¹) ^ 6) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
          rw [hboundary]
    _ = (42 : ℂ)⁻¹ *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 6 - (((n : ℂ) + z)⁻¹) ^ 6) +
        (6 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
          rw [h_uv']
          ring

lemma stieltjes_interval_B8CellDeriv_to_B8Diff (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8 =
      (-(30 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 8 - (((n : ℂ) + z)⁻¹) ^ 8) +
        (8 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
  classical
  let u : ℝ → ℂ := fun x =>
    ((x : ℂ) - (n : ℂ)) ^ 8 -
      (4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 +
      (14 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 -
      (7 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
      (2 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 - (30 : ℂ)⁻¹
  let u' : ℝ → ℂ := fun x => (bernoulli8DiffCellDeriv n x : ℂ)
  let v : ℝ → ℂ := (fun x : ℝ => ((x : ℂ) + z)⁻¹) ^ 8
  let v' : ℝ → ℂ := fun x =>
    (8 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (8 - 1) *
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_eight :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 8)
          ((8 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7) x := by
      simpa using h_sub.pow 8
    have h_seven :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 7)
          ((7 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6) x := by
      simpa using h_sub.pow 7
    have h_six :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 6)
          ((6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5) x := by
      simpa using h_sub.pow 6
    have h_four :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4)
          ((4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3) x := by
      simpa using h_sub.pow 4
    have h_square :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2)
          ((2 : ℂ) * ((x : ℂ) - (n : ℂ))) x := by
      simpa using h_sub.pow 2
    have h_poly :
        HasDerivAt
          (fun x : ℝ =>
            ((x : ℂ) - (n : ℂ)) ^ 8 -
              (4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 +
              (14 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 -
              (7 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 +
              (2 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 - (30 : ℂ)⁻¹)
          ((8 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 -
            (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 +
            (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 -
            (28 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
            (4 / 3 : ℂ) * ((x : ℂ) - (n : ℂ))) x := by
      have h :=
        (((((h_eight.sub (h_seven.const_mul (4 : ℂ))).add
          (h_six.const_mul (14 / 3 : ℂ))).sub
          (h_four.const_mul (7 / 3 : ℂ))).add
          (h_square.const_mul (2 / 3 : ℂ))).sub_const (30 : ℂ)⁻¹)
      convert h using 1 <;> ring
    convert h_poly using 1 <;>
      simp [u, u', bernoulli8DiffCellDeriv, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] <;> ring
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    simpa [v, v'] using h_inv.pow 8
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_seven : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 7 :=
        hcont_sub.pow 7
      have hcont_six : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 6 :=
        hcont_sub.pow 6
      have hcont_five : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 5 :=
        hcont_sub.pow 5
      have hcont_cube : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3 :=
        hcont_sub.pow 3
      have hcont_poly :
          Continuous fun x : ℝ =>
            (8 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 -
              (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 +
              (28 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 -
              (28 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 +
              (4 / 3 : ℂ) * ((x : ℂ) - (n : ℂ)) := by
        exact ((((continuous_const.mul hcont_seven).sub
          (continuous_const.mul hcont_six)).add
          (continuous_const.mul hcont_five)).sub
          (continuous_const.mul hcont_cube)).add (continuous_const.mul hcont_sub)
      simpa [u', bernoulli8DiffCellDeriv, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hcont_poly
    simpa [u'] using
      (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_inv_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ (8 - 1)) x :=
        hcont_inv.pow (8 - 1)
      have hcont_pow2 :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne2 : ((x : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
      have hcont_pow2_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow2 hne2)
      have hcont_neg_div :
          ContinuousAt (fun x : ℝ => -(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
        simpa [div_eq_mul_inv] using hcont_pow2_inv.const_mul (-(1 : ℂ))
      have hcont_left :
          ContinuousAt (fun x : ℝ => (8 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (8 - 1)) x :=
        continuous_const.continuousAt.mul hcont_inv_pow
      have hcont_mul := hcont_left.mul hcont_neg_div
      simpa [v', mul_assoc] using hcont_mul.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have h_left :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [u', v, div_eq_mul_inv]
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(8 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
    have h_int :
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (-(8 : ℂ)) * ((bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        simpa using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcell := bernoulli8Diff_eq_cell_on_Icc n hx'
      simp [u, v', hcell, div_eq_mul_inv, one_div]
      field_simp [hneq]
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x
          = ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (-(8 : ℂ)) * ((bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9) := h_int
      _ = (-(8 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
        simpa using
          (intervalIntegral.integral_const_mul (c := (-(8 : ℂ)))
            (f := fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
            (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hu_left : u (n : ℝ) = (-(30 : ℂ)⁻¹) := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = (-(30 : ℂ)⁻¹) := by
    norm_num [u, Nat.cast_add, Nat.cast_one]
  have hsum_parts :
      (∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
          u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) := by
    have hparts' := (eq_sub_iff_add_eq).1 hparts
    simpa [add_comm, add_left_comm, add_assoc] using hparts'
  have hparts_rev :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    refine (eq_sub_iff_add_eq).2 ?_
    simpa [add_comm, add_left_comm, add_assoc] using hsum_parts
  have hboundary :
      u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) =
        (-(30 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 8 - (((n : ℂ) + z)⁻¹) ^ 8) := by
    rw [hu_right, hu_left]
    simp [v, sub_eq_add_neg, mul_sub, mul_add, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc]
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8
        = ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := h_left
    _ = u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hparts_rev
    _ = (-(30 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 8 - (((n : ℂ) + z)⁻¹) ^ 8) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
          rw [hboundary]
    _ = (-(30 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 8 - (((n : ℂ) + z)⁻¹) ^ 8) +
        (8 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
          rw [h_uv']
          ring

lemma stieltjes_interval_B10CellDeriv_to_B10Diff (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10 =
      (5 / 66 : ℂ) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 10 - (((n : ℂ) + z)⁻¹) ^ 10) +
        (10 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
  classical
  let u : ℝ → ℂ := fun x =>
    ((x : ℂ) - (n : ℂ)) ^ 10 -
      (5 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 9 +
      (15 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8 -
      (7 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 +
      (5 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
      (3 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 + (5 / 66 : ℂ)
  let u' : ℝ → ℂ := fun x => (bernoulli10DiffCellDeriv n x : ℂ)
  let v : ℝ → ℂ := (fun x : ℝ => ((x : ℂ) + z)⁻¹) ^ 10
  let v' : ℝ → ℂ := fun x =>
    (10 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (10 - 1) *
      (-(1 : ℂ) / ((x : ℂ) + z) ^ 2)
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    have h_id : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
    have h_sub : HasDerivAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) (1 : ℂ) x := by
      simpa using h_id.sub_const (n : ℂ)
    have h_ten :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 10)
          ((10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 9) x := by
      simpa using h_sub.pow 10
    have h_nine :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 9)
          ((9 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8) x := by
      simpa using h_sub.pow 9
    have h_eight :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 8)
          ((8 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7) x := by
      simpa using h_sub.pow 8
    have h_six :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 6)
          ((6 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5) x := by
      simpa using h_sub.pow 6
    have h_four :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 4)
          ((4 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3) x := by
      simpa using h_sub.pow 4
    have h_square :
        HasDerivAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2)
          ((2 : ℂ) * ((x : ℂ) - (n : ℂ))) x := by
      simpa using h_sub.pow 2
    have h_poly :
        HasDerivAt
          (fun x : ℝ =>
            ((x : ℂ) - (n : ℂ)) ^ 10 -
              (5 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 9 +
              (15 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8 -
              (7 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 6 +
              (5 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 4 -
              (3 / 2 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 2 + (5 / 66 : ℂ))
          ((10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 9 -
            (45 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8 +
            (60 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 -
            (42 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
            (20 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
            (3 : ℂ) * ((x : ℂ) - (n : ℂ))) x := by
      have h1 := h_ten.sub (h_nine.const_mul (5 : ℂ))
      have h2 := h1.add (h_eight.const_mul (15 / 2 : ℂ))
      have h3 := h2.sub (h_six.const_mul (7 : ℂ))
      have h4 := h3.add (h_four.const_mul (5 : ℂ))
      have h5 := h4.sub (h_square.const_mul (3 / 2 : ℂ))
      have h := h5.add_const (5 / 66 : ℂ)
      convert h using 1 <;> ring
    convert h_poly using 1 <;>
      simp [u, u', bernoulli10DiffCellDeriv, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] <;> ring
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      have hle : (n : ℝ) ≤ n + 1 := by nlinarith
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv : HasDerivAt (fun x : ℝ => ((x : ℂ) + z)⁻¹)
        (-(1 : ℂ) / ((x : ℂ) + z) ^ 2) x :=
      hasDerivAt_inv_add z hneq
    simpa [v, v'] using h_inv.pow 10
  have hu' : IntervalIntegrable u' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : Continuous u' := by
      have hcont_sub : Continuous fun x : ℝ => (x : ℂ) - (n : ℂ) :=
        Complex.continuous_ofReal.sub continuous_const
      have hcont_nine : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 9 :=
        hcont_sub.pow 9
      have hcont_eight : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 8 :=
        hcont_sub.pow 8
      have hcont_seven : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 7 :=
        hcont_sub.pow 7
      have hcont_five : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 5 :=
        hcont_sub.pow 5
      have hcont_cube : Continuous fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 3 :=
        hcont_sub.pow 3
      have hcont_poly :
          Continuous fun x : ℝ =>
            (10 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 9 -
              (45 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 8 +
              (60 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 7 -
              (42 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 5 +
              (20 : ℂ) * ((x : ℂ) - (n : ℂ)) ^ 3 -
              (3 : ℂ) * ((x : ℂ) - (n : ℂ)) := by
        exact (((((continuous_const.mul hcont_nine).sub
          (continuous_const.mul hcont_eight)).add
          (continuous_const.mul hcont_seven)).sub
          (continuous_const.mul hcont_five)).add
          (continuous_const.mul hcont_cube)).sub (continuous_const.mul hcont_sub)
      simpa [u', bernoulli10DiffCellDeriv, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hcont_poly
    simpa [u'] using
      (hcont.intervalIntegrable (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hv' : IntervalIntegrable v' volume (n : ℝ) (n + 1 : ℝ) := by
    have hcont : ContinuousOn v' (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        have hle : (n : ℝ) ≤ n + 1 := by nlinarith
        simpa [Set.uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcont_add :
          ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
        simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
      have hcont_inv :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_add hneq)
      have hcont_inv_pow :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹ ^ (10 - 1)) x :=
        hcont_inv.pow (10 - 1)
      have hcont_pow2 :
          ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 2) x := hcont_add.pow 2
      have hne2 : ((x : ℂ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
      have hcont_pow2_inv :
          ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 2)⁻¹) x :=
        (ContinuousAt.inv₀ hcont_pow2 hne2)
      have hcont_neg_div :
          ContinuousAt (fun x : ℝ => -(1 : ℂ) / ((x : ℂ) + z) ^ 2) x := by
        simpa [div_eq_mul_inv] using hcont_pow2_inv.const_mul (-(1 : ℂ))
      have hcont_left :
          ContinuousAt (fun x : ℝ => (10 : ℂ) * ((x : ℂ) + z)⁻¹ ^ (10 - 1)) x :=
        continuous_const.continuousAt.mul hcont_inv_pow
      have hcont_mul := hcont_left.mul hcont_neg_div
      simpa [v', mul_assoc] using hcont_mul.continuousWithinAt
    exact hcont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (n : ℝ)) (b := (n + 1 : ℝ))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu' hv'
  have h_left :
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10 =
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [u', v, div_eq_mul_inv]
  have h_uv' :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
        (-(10 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
    have h_int :
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (-(10 : ℂ)) * ((bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        simpa using hx
      have hx0 : 0 ≤ x := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        exact le_trans hn0 hx'.1
      have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
      have hcell := bernoulli10Diff_eq_cell_on_Icc n hx'
      simp [u, v', hcell, div_eq_mul_inv, one_div]
      field_simp [hneq]
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x
          = ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (-(10 : ℂ)) * ((bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11) := h_int
      _ = (-(10 : ℂ)) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
        simpa using
          (intervalIntegral.integral_const_mul (c := (-(10 : ℂ)))
            (f := fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
            (a := (n : ℝ)) (b := (n + 1 : ℝ)) (μ := volume))
  have hu_left : u (n : ℝ) = (5 / 66 : ℂ) := by
    simp [u]
  have hu_right : u (n + 1 : ℝ) = (5 / 66 : ℂ) := by
    norm_num [u, Nat.cast_add, Nat.cast_one]
  have hsum_parts :
      (∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
          u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) := by
    have hparts' := (eq_sub_iff_add_eq).1 hparts
    simpa [add_comm, add_left_comm, add_assoc] using hparts'
  have hparts_rev :
      ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x =
        u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
    refine (eq_sub_iff_add_eq).2 ?_
    simpa [add_comm, add_left_comm, add_assoc] using hsum_parts
  have hboundary :
      u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) =
        (5 / 66 : ℂ) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 10 - (((n : ℂ) + z)⁻¹) ^ 10) := by
    rw [hu_right, hu_left]
    simp [v, sub_eq_add_neg, mul_sub, mul_add, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc]
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10
        = ∫ x in (n : ℝ)..(n + 1 : ℝ), u' x * v x := h_left
    _ = u (n + 1 : ℝ) * v (n + 1 : ℝ) - u (n : ℝ) * v (n : ℝ) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := hparts_rev
    _ = (5 / 66 : ℂ) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 10 - (((n : ℂ) + z)⁻¹) ^ 10) -
          ∫ x in (n : ℝ)..(n + 1 : ℝ), u x * v' x := by
          rw [hboundary]
    _ = (5 / 66 : ℂ) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 10 - (((n : ℂ) + z)⁻¹) ^ 10) +
        (10 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
          rw [h_uv']
          ring

lemma stieltjes_interval_B8Diff_to_B10Diff (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 =
      (132 : ℂ)⁻¹ *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 10 - (((n : ℂ) + z)⁻¹) ^ 10) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
  have h1 := stieltjes_interval_B8Diff_to_B10CellDeriv z hz n
  have h2 := stieltjes_interval_B10CellDeriv_to_B10Diff z hz n
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9
        = (1 / 10 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 10 := h1
    _ = (132 : ℂ)⁻¹ *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 10 - (((n : ℂ) + z)⁻¹) ^ 10) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
          rw [h2]
          ring

lemma stieltjes_interval_B6Diff_to_B8Diff (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 =
      (-(240 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 8 - (((n : ℂ) + z)⁻¹) ^ 8) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
  have h1 := stieltjes_interval_B6Diff_to_B8CellDeriv z hz n
  have h2 := stieltjes_interval_B8CellDeriv_to_B8Diff z hz n
  calc
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
        = (1 / 8 : ℂ) * ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 8 := h1
    _ = (-(240 : ℂ)⁻¹) *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 8 - (((n : ℂ) + z)⁻¹) ^ 8) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
          rw [h2]
          ring

lemma stieltjes_interval_B4Diff_to_B6Diff (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 =
      (252 : ℂ)⁻¹ *
          ((((n + 1 : ℂ) + z)⁻¹) ^ 6 - (((n : ℂ) + z)⁻¹) ^ 6) +
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
  have h1 := stieltjes_interval_B4Diff_to_B6CellDeriv z hz n
  have h2 := stieltjes_interval_B6CellDeriv_to_B6Diff z hz n
  rw [h1, h2]
  ring

lemma sum_b4_boundary_telescope (z : ℂ) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n => ((((n + 1 : ℂ) + z)⁻¹) ^ 4 - (((n : ℂ) + z)⁻¹) ^ 4)) =
      (((N : ℂ) + z)⁻¹) ^ 4 - (z⁻¹) ^ 4 := by
  classical
  let a : ℕ → ℂ := fun n => (((n : ℂ) + z)⁻¹) ^ 4
  have htel :
      Finset.sum (Finset.range N) (fun n => a (n + 1) - a n) = a N - a 0 := by
    induction N with
    | zero =>
        simp [a]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  simpa [a, add_comm, add_left_comm, add_assoc] using htel

lemma sum_b6_boundary_telescope (z : ℂ) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n => ((((n + 1 : ℂ) + z)⁻¹) ^ 6 - (((n : ℂ) + z)⁻¹) ^ 6)) =
      (((N : ℂ) + z)⁻¹) ^ 6 - (z⁻¹) ^ 6 := by
  classical
  let a : ℕ → ℂ := fun n => (((n : ℂ) + z)⁻¹) ^ 6
  have htel :
      Finset.sum (Finset.range N) (fun n => a (n + 1) - a n) = a N - a 0 := by
    induction N with
    | zero =>
        simp [a]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  simpa [a, add_comm, add_left_comm, add_assoc] using htel

lemma sum_b8_boundary_telescope (z : ℂ) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n => ((((n + 1 : ℂ) + z)⁻¹) ^ 8 - (((n : ℂ) + z)⁻¹) ^ 8)) =
      (((N : ℂ) + z)⁻¹) ^ 8 - (z⁻¹) ^ 8 := by
  classical
  let a : ℕ → ℂ := fun n => (((n : ℂ) + z)⁻¹) ^ 8
  have htel :
      Finset.sum (Finset.range N) (fun n => a (n + 1) - a n) = a N - a 0 := by
    induction N with
    | zero =>
        simp [a]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  simpa [a, add_comm, add_left_comm, add_assoc] using htel

lemma sum_b10_boundary_telescope (z : ℂ) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n => ((((n + 1 : ℂ) + z)⁻¹) ^ 10 - (((n : ℂ) + z)⁻¹) ^ 10)) =
      (((N : ℂ) + z)⁻¹) ^ 10 - (z⁻¹) ^ 10 := by
  classical
  let a : ℕ → ℂ := fun n => (((n : ℂ) + z)⁻¹) ^ 10
  have htel :
      Finset.sum (Finset.range N) (fun n => a (n + 1) - a n) = a N - a 0 := by
    induction N with
    | zero =>
        simp [a]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  simpa [a, add_comm, add_left_comm, add_assoc] using htel

lemma intervalIntegral_inv_eq_log (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹ =
      Complex.log (z + (N : ℂ)) - Complex.log z := by
  classical
  let f : ℝ → ℂ := fun x => Complex.log ((x : ℂ) + z)
  let f' : ℝ → ℂ := fun x => ((x : ℂ) + z)⁻¹
  have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ), DifferentiableAt ℝ f x := by
    intro x hx
    have hle : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.cast_nonneg N)
    have hx' : x ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := hx'.1
    have hslit : (x : ℂ) + z ∈ Complex.slitPlane :=
      add_mem_slitPlane_of_re_pos hz hx0
    simpa [f] using (hasDerivAt_log_add z hslit).differentiableAt
  have hderiv_eq : EqOn (fun x => deriv f x) f' (Set.uIcc (0 : ℝ) (N : ℝ)) := by
    intro x hx
    have hle : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.cast_nonneg N)
    have hx' : x ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := hx'.1
    have hslit : (x : ℂ) + z ∈ Complex.slitPlane :=
      add_mem_slitPlane_of_re_pos hz hx0
    simpa [f, f'] using (hasDerivAt_log_add z hslit).deriv
  have hcont : ContinuousOn f' (Set.uIcc (0 : ℝ) (N : ℝ)) := by
    intro x hx
    have hle : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.cast_nonneg N)
    have hx' : x ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_inv :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_add hneq)
    simpa [f'] using hcont_inv.continuousWithinAt
  have h_int_f' : IntervalIntegrable f' volume (0 : ℝ) (N : ℝ) :=
    hcont.intervalIntegrable
  have h_eq_uIoc :
      EqOn (fun x => deriv f x) f' (Set.uIoc (0 : ℝ) (N : ℝ)) := by
    intro x hx
    have hle : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.cast_nonneg N)
    have hx' : x ∈ Set.uIcc (0 : ℝ) (N : ℝ) := by
      have hxIoc : x ∈ Set.Ioc (0 : ℝ) (N : ℝ) := by
        simpa [Set.uIoc_of_le hle] using hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) (N : ℝ) :=
        ⟨le_of_lt hxIoc.1, hxIoc.2⟩
      simpa [Set.uIcc_of_le hle] using hxIcc
    exact hderiv_eq hx'
  have h_int_deriv : IntervalIntegrable (deriv f) volume (0 : ℝ) (N : ℝ) := by
    have hiff := (intervalIntegrable_congr (μ := volume) (a := (0 : ℝ)) (b := (N : ℝ))
      (f := deriv f) (g := f') h_eq_uIoc)
    exact (hiff.mpr h_int_f')
  have hFTC :
      ∫ x in (0 : ℝ)..(N : ℝ), deriv f x = f (N : ℝ) - f (0 : ℝ) :=
    intervalIntegral.integral_deriv_eq_sub hdiff h_int_deriv
  have h_int_eq :
      ∫ x in (0 : ℝ)..(N : ℝ), deriv f x =
        ∫ x in (0 : ℝ)..(N : ℝ), f' x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    exact hderiv_eq hx
  calc
    ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹
        = ∫ x in (0 : ℝ)..(N : ℝ), f' x := by rfl
    _ = ∫ x in (0 : ℝ)..(N : ℝ), deriv f x := by
          simpa using h_int_eq.symm
    _ = f (N : ℝ) - f (0 : ℝ) := hFTC
    _ = Complex.log (z + (N : ℂ)) - Complex.log z := by
          simp [f, add_comm, add_left_comm, add_assoc]

lemma intervalIntegrable_inv_add_nat (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) + z)⁻¹) volume (n : ℝ) (n + 1 : ℝ) := by
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + z)⁻¹)
      (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_inv :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_add hneq)
    simpa using hcont_inv.continuousWithinAt
  exact hcont.intervalIntegrable

lemma intervalIntegrable_b2diff_div_nat (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
      volume (n : ℝ) (n + 1 : ℝ) := by
  have h_eq :
      EqOn
        (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
        (fun x : ℝ =>
          (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hxIoc : x ∈ Set.Ioc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIoc_of_le hle] using hx
    by_cases hx1 : x = n + 1
    · simp [hx1, bernoulli2Diff, bernoulli2]
    have hx' : x ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := by
      refine ⟨hxIoc.1, ?_⟩
      exact lt_of_le_of_ne hxIoc.2 hx1
    have hreal : bernoulli2Diff x = (x - n) - (x - n) ^ 2 :=
      bernoulli2Diff_eq_on_Ioo n hx'
    simp [hreal]
  have hcont_poly :
      ContinuousOn
        (fun x : ℝ =>
          (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3)
        (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_num :
        ContinuousAt
          (fun x : ℝ => (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ)) x := by
      have hcont_id : ContinuousAt (fun x : ℝ => (x : ℂ)) x := by
        simpa using (Complex.continuous_ofReal.continuousAt)
      have hcont_sub : ContinuousAt (fun x : ℝ => (x : ℂ) - (n : ℂ)) x := by
        simpa using hcont_id.sub_const (n : ℂ)
      have hcont_sq :
          ContinuousAt (fun x : ℝ => ((x : ℂ) - (n : ℂ)) ^ 2) x := by
        simpa using hcont_sub.pow 2
      have hcont_diff :
          ContinuousAt (fun x : ℝ => (x : ℂ) - (n : ℂ) - ((x : ℂ) - (n : ℂ)) ^ 2) x := by
        simpa [sub_eq_add_neg, add_assoc] using hcont_sub.sub hcont_sq
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcont_diff
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_pow :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 3) x := hcont_add.pow 3
    have hne : ((x : ℂ) + z) ^ 3 ≠ 0 := pow_ne_zero 3 hneq
    have hcont_inv :
        ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 3)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_pow hne)
    have hcont_mul :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) * (((x : ℂ) + z) ^ 3)⁻¹) x :=
      hcont_num.mul hcont_inv
    simpa [div_eq_mul_inv] using hcont_mul.continuousWithinAt
  have h_int_poly :
      IntervalIntegrable
        (fun x : ℝ =>
          (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3)
        volume (n : ℝ) (n + 1 : ℝ) :=
    hcont_poly.intervalIntegrable
  have h_eq_uIoc :
      EqOn
        (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
        (fun x : ℝ =>
          (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := h_eq
  have hiff := (intervalIntegrable_congr (μ := volume) (a := (n : ℝ)) (b := (n + 1 : ℝ))
    (f := fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
    (g := fun x : ℝ =>
      (((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + z) ^ 3) h_eq_uIoc)
  exact hiff.mpr h_int_poly

lemma intervalIntegrable_b2fract_div_nat (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3)
      volume (n : ℝ) (n + 1 : ℝ) := by
  have h_eq :
      EqOn
        (fun x : ℝ => (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 3)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hxIoc : x ∈ Set.Ioc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIoc_of_le hle] using hx
    have hxIcc : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hreal := bernoulli2Fract_eq_cell_on_Icc n hxIcc
    simp [hreal]
  have hcont_poly :
      ContinuousOn
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 3)
        (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_num :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ)) x := by
      have hshift : ContinuousAt (fun y : ℝ => y - (n : ℝ)) x := by
        simpa using (continuousAt_id.sub continuous_const.continuousAt)
      have h2 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 2) x := hshift.pow 2
      have hcont_real :
          ContinuousAt
            (fun y : ℝ => (y - (n : ℝ)) ^ 2 - (y - (n : ℝ)) + (6 : ℝ)⁻¹) x :=
        (h2.sub hshift).add continuous_const.continuousAt
      simpa [Function.comp_def] using (Complex.continuous_ofReal.continuousAt.comp hcont_real)
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_pow :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 3) x := hcont_add.pow 3
    have hne : ((x : ℂ) + z) ^ 3 ≠ 0 := pow_ne_zero 3 hneq
    have hcont_inv :
        ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 3)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_pow hne)
    have hcont_mul :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) *
              (((x : ℂ) + z) ^ 3)⁻¹) x :=
      hcont_num.mul hcont_inv
    simpa [div_eq_mul_inv] using hcont_mul.continuousWithinAt
  have h_int_poly :
      IntervalIntegrable
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 3)
        volume (n : ℝ) (n + 1 : ℝ) :=
    hcont_poly.intervalIntegrable
  have h_eq_uIoc :
      EqOn
        (fun x : ℝ => (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 3)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := h_eq
  have hiff := (intervalIntegrable_congr (μ := volume) (a := (n : ℝ)) (b := (n + 1 : ℝ))
    (f := fun x : ℝ => (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3)
    (g := fun x : ℝ =>
      (((x - (n : ℝ)) ^ 2 - (x - (n : ℝ)) + (6 : ℝ)⁻¹ : ℝ) : ℂ) /
        ((x : ℂ) + z) ^ 3) h_eq_uIoc)
  exact hiff.mpr h_int_poly

lemma intervalIntegrable_b4diff_div_nat (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
      volume (n : ℝ) (n + 1 : ℝ) := by
  have h_eq :
      EqOn
        (fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 4 - 2 * (x - (n : ℝ)) ^ 3 +
              (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 5)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hxIoc : x ∈ Set.Ioc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIoc_of_le hle] using hx
    have hxIcc : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hreal := bernoulli4Diff_eq_cell_on_Icc n hxIcc
    simp [hreal]
  have hcont_poly :
      ContinuousOn
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 4 - 2 * (x - (n : ℝ)) ^ 3 +
              (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 5)
        (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_num :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 4 - 2 * (x - (n : ℝ)) ^ 3 +
                (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ)) x := by
      have hcont_real :
          ContinuousAt
            (fun x : ℝ =>
              (x - (n : ℝ)) ^ 4 - 2 * (x - (n : ℝ)) ^ 3 +
                (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹) x := by
        have hshift : ContinuousAt (fun y : ℝ => y - (n : ℝ)) x := by
          simpa using (continuousAt_id.sub continuous_const.continuousAt)
        have h4 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 4) x := hshift.pow 4
        have h3 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 3) x := hshift.pow 3
        have h2 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 2) x := hshift.pow 2
        have h2mul : ContinuousAt (fun y : ℝ => (2 : ℝ) * (y - (n : ℝ)) ^ 3) x :=
          continuous_const.continuousAt.mul h3
        simpa [sub_eq_add_neg, add_assoc] using ((h4.sub h2mul).add h2).sub
          continuous_const.continuousAt
      simpa [Function.comp_def] using (Complex.continuous_ofReal.continuousAt.comp hcont_real)
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_pow :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 5) x := hcont_add.pow 5
    have hne : ((x : ℂ) + z) ^ 5 ≠ 0 := pow_ne_zero 5 hneq
    have hcont_inv :
        ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 5)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_pow hne)
    have hcont_mul :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 4 - 2 * (x - (n : ℝ)) ^ 3 +
                (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) *
              (((x : ℂ) + z) ^ 5)⁻¹) x :=
      hcont_num.mul hcont_inv
    simpa [div_eq_mul_inv] using hcont_mul.continuousWithinAt
  have h_int_poly :
      IntervalIntegrable
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 4 - 2 * (x - (n : ℝ)) ^ 3 +
              (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 5)
        volume (n : ℝ) (n + 1 : ℝ) :=
    hcont_poly.intervalIntegrable
  have h_eq_uIoc :
      EqOn
        (fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 4 - 2 * (x - (n : ℝ)) ^ 3 +
              (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 5)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := h_eq
  have hiff := (intervalIntegrable_congr (μ := volume) (a := (n : ℝ)) (b := (n + 1 : ℝ))
    (f := fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
    (g := fun x : ℝ =>
      (((x - (n : ℝ)) ^ 4 - 2 * (x - (n : ℝ)) ^ 3 +
          (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
        ((x : ℂ) + z) ^ 5) h_eq_uIoc)
  exact hiff.mpr h_int_poly

lemma intervalIntegrable_b6diff_div_nat (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
      volume (n : ℝ) (n + 1 : ℝ) := by
  have h_eq :
      EqOn
        (fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 6 - 3 * (x - (n : ℝ)) ^ 5 +
              (5 / 2 : ℝ) * (x - (n : ℝ)) ^ 4 -
              (1 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (42 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 7)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hxIoc : x ∈ Set.Ioc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIoc_of_le hle] using hx
    have hxIcc : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hreal := bernoulli6Diff_eq_cell_on_Icc n hxIcc
    simp [hreal]
  have hcont_poly :
      ContinuousOn
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 6 - 3 * (x - (n : ℝ)) ^ 5 +
              (5 / 2 : ℝ) * (x - (n : ℝ)) ^ 4 -
              (1 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (42 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 7)
        (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_num :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 6 - 3 * (x - (n : ℝ)) ^ 5 +
                (5 / 2 : ℝ) * (x - (n : ℝ)) ^ 4 -
                (1 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (42 : ℝ)⁻¹ : ℝ) : ℂ)) x := by
      have hcont_real :
          ContinuousAt
            (fun x : ℝ =>
              (x - (n : ℝ)) ^ 6 - 3 * (x - (n : ℝ)) ^ 5 +
                (5 / 2 : ℝ) * (x - (n : ℝ)) ^ 4 -
                (1 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (42 : ℝ)⁻¹) x := by
        have hshift : ContinuousAt (fun y : ℝ => y - (n : ℝ)) x := by
          simpa using (continuousAt_id.sub continuous_const.continuousAt)
        have h6 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 6) x := hshift.pow 6
        have h5 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 5) x := hshift.pow 5
        have h4 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 4) x := hshift.pow 4
        have h2 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 2) x := hshift.pow 2
        have h3mul : ContinuousAt (fun y : ℝ => (3 : ℝ) * (y - (n : ℝ)) ^ 5) x :=
          continuous_const.continuousAt.mul h5
        have h5half :
            ContinuousAt (fun y : ℝ => (5 / 2 : ℝ) * (y - (n : ℝ)) ^ 4) x :=
          continuous_const.continuousAt.mul h4
        have hhalf :
            ContinuousAt (fun y : ℝ => (1 / 2 : ℝ) * (y - (n : ℝ)) ^ 2) x :=
          continuous_const.continuousAt.mul h2
        simpa [sub_eq_add_neg, add_assoc] using
          ((((h6.sub h3mul).add h5half).sub hhalf).add continuous_const.continuousAt)
      simpa [Function.comp_def] using (Complex.continuous_ofReal.continuousAt.comp hcont_real)
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_pow :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 7) x := hcont_add.pow 7
    have hne : ((x : ℂ) + z) ^ 7 ≠ 0 := pow_ne_zero 7 hneq
    have hcont_inv :
        ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 7)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_pow hne)
    have hcont_mul :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 6 - 3 * (x - (n : ℝ)) ^ 5 +
                (5 / 2 : ℝ) * (x - (n : ℝ)) ^ 4 -
                (1 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (42 : ℝ)⁻¹ : ℝ) : ℂ) *
              (((x : ℂ) + z) ^ 7)⁻¹) x :=
      hcont_num.mul hcont_inv
    simpa [div_eq_mul_inv] using hcont_mul.continuousWithinAt
  have h_int_poly :
      IntervalIntegrable
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 6 - 3 * (x - (n : ℝ)) ^ 5 +
              (5 / 2 : ℝ) * (x - (n : ℝ)) ^ 4 -
              (1 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (42 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 7)
        volume (n : ℝ) (n + 1 : ℝ) :=
    hcont_poly.intervalIntegrable
  have h_eq_uIoc :
      EqOn
        (fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 6 - 3 * (x - (n : ℝ)) ^ 5 +
              (5 / 2 : ℝ) * (x - (n : ℝ)) ^ 4 -
              (1 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (42 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 7)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := h_eq
  have hiff := (intervalIntegrable_congr (μ := volume) (a := (n : ℝ)) (b := (n + 1 : ℝ))
    (f := fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
    (g := fun x : ℝ =>
      (((x - (n : ℝ)) ^ 6 - 3 * (x - (n : ℝ)) ^ 5 +
          (5 / 2 : ℝ) * (x - (n : ℝ)) ^ 4 -
          (1 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (42 : ℝ)⁻¹ : ℝ) : ℂ) /
        ((x : ℂ) + z) ^ 7) h_eq_uIoc)
  exact hiff.mpr h_int_poly

lemma intervalIntegrable_b8diff_div_nat (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
      volume (n : ℝ) (n + 1 : ℝ) := by
  have h_eq :
      EqOn
        (fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 8 - 4 * (x - (n : ℝ)) ^ 7 +
              (14 / 3 : ℝ) * (x - (n : ℝ)) ^ 6 -
              (7 / 3 : ℝ) * (x - (n : ℝ)) ^ 4 +
              (2 / 3 : ℝ) * (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 9)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hxIoc : x ∈ Set.Ioc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIoc_of_le hle] using hx
    have hxIcc : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hreal := bernoulli8Diff_eq_cell_on_Icc n hxIcc
    simp [hreal]
  have hcont_poly :
      ContinuousOn
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 8 - 4 * (x - (n : ℝ)) ^ 7 +
              (14 / 3 : ℝ) * (x - (n : ℝ)) ^ 6 -
              (7 / 3 : ℝ) * (x - (n : ℝ)) ^ 4 +
              (2 / 3 : ℝ) * (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 9)
        (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_num :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 8 - 4 * (x - (n : ℝ)) ^ 7 +
                (14 / 3 : ℝ) * (x - (n : ℝ)) ^ 6 -
                (7 / 3 : ℝ) * (x - (n : ℝ)) ^ 4 +
                (2 / 3 : ℝ) * (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ)) x := by
      have hcont_real :
          ContinuousAt
            (fun x : ℝ =>
              (x - (n : ℝ)) ^ 8 - 4 * (x - (n : ℝ)) ^ 7 +
                (14 / 3 : ℝ) * (x - (n : ℝ)) ^ 6 -
                (7 / 3 : ℝ) * (x - (n : ℝ)) ^ 4 +
                (2 / 3 : ℝ) * (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹) x := by
        have hshift : ContinuousAt (fun y : ℝ => y - (n : ℝ)) x := by
          simpa using (continuousAt_id.sub continuous_const.continuousAt)
        have h8 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 8) x := hshift.pow 8
        have h7 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 7) x := hshift.pow 7
        have h6 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 6) x := hshift.pow 6
        have h4 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 4) x := hshift.pow 4
        have h2 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 2) x := hshift.pow 2
        have h4mul : ContinuousAt (fun y : ℝ => (4 : ℝ) * (y - (n : ℝ)) ^ 7) x :=
          continuous_const.continuousAt.mul h7
        have h14third :
            ContinuousAt (fun y : ℝ => (14 / 3 : ℝ) * (y - (n : ℝ)) ^ 6) x :=
          continuous_const.continuousAt.mul h6
        have h7third :
            ContinuousAt (fun y : ℝ => (7 / 3 : ℝ) * (y - (n : ℝ)) ^ 4) x :=
          continuous_const.continuousAt.mul h4
        have h2third :
            ContinuousAt (fun y : ℝ => (2 / 3 : ℝ) * (y - (n : ℝ)) ^ 2) x :=
          continuous_const.continuousAt.mul h2
        simpa [sub_eq_add_neg, add_assoc] using
          (((((h8.sub h4mul).add h14third).sub h7third).add h2third).sub
            continuous_const.continuousAt)
      simpa [Function.comp_def] using (Complex.continuous_ofReal.continuousAt.comp hcont_real)
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_pow :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 9) x := hcont_add.pow 9
    have hne : ((x : ℂ) + z) ^ 9 ≠ 0 := pow_ne_zero 9 hneq
    have hcont_inv :
        ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 9)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_pow hne)
    have hcont_mul :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 8 - 4 * (x - (n : ℝ)) ^ 7 +
                (14 / 3 : ℝ) * (x - (n : ℝ)) ^ 6 -
                (7 / 3 : ℝ) * (x - (n : ℝ)) ^ 4 +
                (2 / 3 : ℝ) * (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) *
              (((x : ℂ) + z) ^ 9)⁻¹) x :=
      hcont_num.mul hcont_inv
    simpa [div_eq_mul_inv] using hcont_mul.continuousWithinAt
  have h_int_poly :
      IntervalIntegrable
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 8 - 4 * (x - (n : ℝ)) ^ 7 +
              (14 / 3 : ℝ) * (x - (n : ℝ)) ^ 6 -
              (7 / 3 : ℝ) * (x - (n : ℝ)) ^ 4 +
              (2 / 3 : ℝ) * (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 9)
        volume (n : ℝ) (n + 1 : ℝ) :=
    hcont_poly.intervalIntegrable
  have h_eq_uIoc :
      EqOn
        (fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 8 - 4 * (x - (n : ℝ)) ^ 7 +
              (14 / 3 : ℝ) * (x - (n : ℝ)) ^ 6 -
              (7 / 3 : ℝ) * (x - (n : ℝ)) ^ 4 +
              (2 / 3 : ℝ) * (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 9)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := h_eq
  have hiff := (intervalIntegrable_congr (μ := volume) (a := (n : ℝ)) (b := (n + 1 : ℝ))
    (f := fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
    (g := fun x : ℝ =>
      (((x - (n : ℝ)) ^ 8 - 4 * (x - (n : ℝ)) ^ 7 +
          (14 / 3 : ℝ) * (x - (n : ℝ)) ^ 6 -
          (7 / 3 : ℝ) * (x - (n : ℝ)) ^ 4 +
          (2 / 3 : ℝ) * (x - (n : ℝ)) ^ 2 - (30 : ℝ)⁻¹ : ℝ) : ℂ) /
        ((x : ℂ) + z) ^ 9) h_eq_uIoc)
  exact hiff.mpr h_int_poly

lemma intervalIntegrable_b10diff_div_nat (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
      volume (n : ℝ) (n + 1 : ℝ) := by
  have h_eq :
      EqOn
        (fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 10 - 5 * (x - (n : ℝ)) ^ 9 +
              (15 / 2 : ℝ) * (x - (n : ℝ)) ^ 8 -
              7 * (x - (n : ℝ)) ^ 6 + 5 * (x - (n : ℝ)) ^ 4 -
              (3 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (5 / 66 : ℝ) : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 11)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hxIoc : x ∈ Set.Ioc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIoc_of_le hle] using hx
    have hxIcc : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hreal := bernoulli10Diff_eq_cell_on_Icc n hxIcc
    simp [hreal]
  have hcont_poly :
      ContinuousOn
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 10 - 5 * (x - (n : ℝ)) ^ 9 +
              (15 / 2 : ℝ) * (x - (n : ℝ)) ^ 8 -
              7 * (x - (n : ℝ)) ^ 6 + 5 * (x - (n : ℝ)) ^ 4 -
              (3 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (5 / 66 : ℝ) : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 11)
        (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
    intro x hx
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
      exact le_trans hn0 hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_num :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 10 - 5 * (x - (n : ℝ)) ^ 9 +
                (15 / 2 : ℝ) * (x - (n : ℝ)) ^ 8 -
                7 * (x - (n : ℝ)) ^ 6 + 5 * (x - (n : ℝ)) ^ 4 -
                (3 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (5 / 66 : ℝ) : ℝ) : ℂ)) x := by
      have hcont_real :
          ContinuousAt
            (fun x : ℝ =>
              (x - (n : ℝ)) ^ 10 - 5 * (x - (n : ℝ)) ^ 9 +
                (15 / 2 : ℝ) * (x - (n : ℝ)) ^ 8 -
                7 * (x - (n : ℝ)) ^ 6 + 5 * (x - (n : ℝ)) ^ 4 -
                (3 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (5 / 66 : ℝ)) x := by
        have hshift : ContinuousAt (fun y : ℝ => y - (n : ℝ)) x := by
          simpa using (continuousAt_id.sub continuous_const.continuousAt)
        have h10 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 10) x := hshift.pow 10
        have h9 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 9) x := hshift.pow 9
        have h8 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 8) x := hshift.pow 8
        have h6 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 6) x := hshift.pow 6
        have h4 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 4) x := hshift.pow 4
        have h2 : ContinuousAt (fun y : ℝ => (y - (n : ℝ)) ^ 2) x := hshift.pow 2
        have h5nine : ContinuousAt (fun y : ℝ => (5 : ℝ) * (y - (n : ℝ)) ^ 9) x :=
          continuous_const.continuousAt.mul h9
        have h15half :
            ContinuousAt (fun y : ℝ => (15 / 2 : ℝ) * (y - (n : ℝ)) ^ 8) x :=
          continuous_const.continuousAt.mul h8
        have h7six : ContinuousAt (fun y : ℝ => (7 : ℝ) * (y - (n : ℝ)) ^ 6) x :=
          continuous_const.continuousAt.mul h6
        have h5four : ContinuousAt (fun y : ℝ => (5 : ℝ) * (y - (n : ℝ)) ^ 4) x :=
          continuous_const.continuousAt.mul h4
        have h3half :
            ContinuousAt (fun y : ℝ => (3 / 2 : ℝ) * (y - (n : ℝ)) ^ 2) x :=
          continuous_const.continuousAt.mul h2
        simpa [sub_eq_add_neg, add_assoc] using
          ((((((h10.sub h5nine).add h15half).sub h7six).add h5four).sub h3half).add
            continuous_const.continuousAt)
      simpa [Function.comp_def] using (Complex.continuous_ofReal.continuousAt.comp hcont_real)
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_pow :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 11) x := hcont_add.pow 11
    have hne : ((x : ℂ) + z) ^ 11 ≠ 0 := pow_ne_zero 11 hneq
    have hcont_inv :
        ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 11)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_pow hne)
    have hcont_mul :
        ContinuousAt
          (fun x : ℝ =>
            (((x - (n : ℝ)) ^ 10 - 5 * (x - (n : ℝ)) ^ 9 +
                (15 / 2 : ℝ) * (x - (n : ℝ)) ^ 8 -
                7 * (x - (n : ℝ)) ^ 6 + 5 * (x - (n : ℝ)) ^ 4 -
                (3 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (5 / 66 : ℝ) : ℝ) : ℂ) *
              (((x : ℂ) + z) ^ 11)⁻¹) x :=
      hcont_num.mul hcont_inv
    simpa [div_eq_mul_inv] using hcont_mul.continuousWithinAt
  have h_int_poly :
      IntervalIntegrable
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 10 - 5 * (x - (n : ℝ)) ^ 9 +
              (15 / 2 : ℝ) * (x - (n : ℝ)) ^ 8 -
              7 * (x - (n : ℝ)) ^ 6 + 5 * (x - (n : ℝ)) ^ 4 -
              (3 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (5 / 66 : ℝ) : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 11)
        volume (n : ℝ) (n + 1 : ℝ) :=
    hcont_poly.intervalIntegrable
  have h_eq_uIoc :
      EqOn
        (fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
        (fun x : ℝ =>
          (((x - (n : ℝ)) ^ 10 - 5 * (x - (n : ℝ)) ^ 9 +
              (15 / 2 : ℝ) * (x - (n : ℝ)) ^ 8 -
              7 * (x - (n : ℝ)) ^ 6 + 5 * (x - (n : ℝ)) ^ 4 -
              (3 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (5 / 66 : ℝ) : ℝ) : ℂ) /
            ((x : ℂ) + z) ^ 11)
        (Set.uIoc (n : ℝ) (n + 1 : ℝ)) := h_eq
  have hiff := (intervalIntegrable_congr (μ := volume) (a := (n : ℝ)) (b := (n + 1 : ℝ))
    (f := fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
    (g := fun x : ℝ =>
      (((x - (n : ℝ)) ^ 10 - 5 * (x - (n : ℝ)) ^ 9 +
          (15 / 2 : ℝ) * (x - (n : ℝ)) ^ 8 -
          7 * (x - (n : ℝ)) ^ 6 + 5 * (x - (n : ℝ)) ^ 4 -
          (3 / 2 : ℝ) * (x - (n : ℝ)) ^ 2 + (5 / 66 : ℝ) : ℝ) : ℂ) /
        ((x : ℂ) + z) ^ 11) h_eq_uIoc)
  exact hiff.mpr h_int_poly

lemma sum_trapezoid_eq_sum (z : ℂ) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n =>
          (1 / 2 : ℂ) * (((z + (n : ℂ))⁻¹) + ((z + (n + 1 : ℂ))⁻¹))) =
      Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹) +
        (1 / 2 : ℂ) * (((z + (N : ℂ))⁻¹) - (z : ℂ)⁻¹) := by
  classical
  let a : ℕ → ℂ := fun n => (z + (n : ℂ))⁻¹
  have hshift :
      Finset.sum (Finset.range N) (fun n => a (n + 1)) =
        Finset.sum (Finset.range N) (fun n => a n) + a N - a 0 := by
    have hsum_shift :
        Finset.sum (Finset.range (N + 1)) (fun n => a n) =
          Finset.sum (Finset.range N) (fun n => a (n + 1)) + a 0 := by
      simpa using (Finset.sum_range_succ' a N)
    have hsum_range :
        Finset.sum (Finset.range (N + 1)) (fun n => a n) =
          Finset.sum (Finset.range N) (fun n => a n) + a N := by
      simpa using (Finset.sum_range_succ a N)
    calc
      Finset.sum (Finset.range N) (fun n => a (n + 1))
          = Finset.sum (Finset.range (N + 1)) (fun n => a n) - a 0 := by
              refine (eq_sub_iff_add_eq).2 ?_
              simpa [add_comm, add_left_comm, add_assoc] using hsum_shift.symm
      _ = (Finset.sum (Finset.range N) (fun n => a n) + a N) - a 0 := by
              simpa [hsum_range]
      _ = Finset.sum (Finset.range N) (fun n => a n) + a N - a 0 := by
              ring
  have hsum_pair :
      Finset.sum (Finset.range N) (fun n => a n + a (n + 1)) =
        (2 : ℂ) * (Finset.sum (Finset.range N) (fun n => a n)) + a N - a 0 := by
    calc
      Finset.sum (Finset.range N) (fun n => a n + a (n + 1))
          = Finset.sum (Finset.range N) (fun n => a n) +
              Finset.sum (Finset.range N) (fun n => a (n + 1)) := by
              simp [Finset.sum_add_distrib]
      _ = Finset.sum (Finset.range N) (fun n => a n) +
            (Finset.sum (Finset.range N) (fun n => a n) + a N - a 0) := by
              simp [hshift]
      _ = (2 : ℂ) * (Finset.sum (Finset.range N) (fun n => a n)) + a N - a 0 := by
              ring
  calc
    Finset.sum (Finset.range N)
        (fun n =>
          (1 / 2 : ℂ) * (((z + (n : ℂ))⁻¹) + ((z + (n + 1 : ℂ))⁻¹)))
        = Finset.sum (Finset.range N) (fun n => (1 / 2 : ℂ) * (a n + a (n + 1))) := by
            simp [a]
    _ = (1 / 2 : ℂ) * Finset.sum (Finset.range N) (fun n => a n + a (n + 1)) := by
          simpa [mul_comm] using
            (Finset.mul_sum (a := (1 / 2 : ℂ)) (s := Finset.range N)
              (f := fun n => a n + a (n + 1))).symm
    _ = (1 / 2 : ℂ) * ((2 : ℂ) * (Finset.sum (Finset.range N) (fun n => a n)) + a N - a 0) := by
            simp [hsum_pair]
    _ = (Finset.sum (Finset.range N) (fun n => a n)) + (1 / 2 : ℂ) * (a N - a 0) := by
            ring
  -- unfold `a` at the end
  simp [a]

lemma sum_interval_integral_inv (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n => ∫ x in (n : ℝ)..(n + 1 : ℝ), ((x : ℂ) + z)⁻¹) =
      ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹ := by
  classical
  have hint :
      ∀ k < N,
        IntervalIntegrable (fun x : ℝ => ((x : ℂ) + z)⁻¹) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_inv_add_nat z hz k
  simpa [Nat.cast_add, Nat.cast_one] using
    (intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => ((x : ℂ) + z)⁻¹)
      (a := fun k : ℕ => (k : ℝ)) (n := N) (μ := volume) hint)

lemma sum_interval_integral_b2diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n =>
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) =
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
  classical
  have hint :
      ∀ k < N,
        IntervalIntegrable (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
          volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_b2diff_div_nat z hz k
  simpa [Nat.cast_add, Nat.cast_one] using
    (intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
      (a := fun k : ℕ => (k : ℝ)) (n := N) (μ := volume) hint)

lemma sum_interval_integral_b2fract (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n =>
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3) =
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3 := by
  classical
  have hint :
      ∀ k < N,
        IntervalIntegrable (fun x : ℝ => (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3)
          volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_b2fract_div_nat z hz k
  simpa [Nat.cast_add, Nat.cast_one] using
    (intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3)
      (a := fun k : ℕ => (k : ℝ)) (n := N) (μ := volume) hint)

lemma sum_interval_integral_b4diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n =>
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5) =
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
  classical
  have hint :
      ∀ k < N,
        IntervalIntegrable (fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
          volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_b4diff_div_nat z hz k
  simpa [Nat.cast_add, Nat.cast_one] using
    (intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
      (a := fun k : ℕ => (k : ℝ)) (n := N) (μ := volume) hint)

lemma sum_interval_integral_b6diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n =>
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7) =
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
  classical
  have hint :
      ∀ k < N,
        IntervalIntegrable (fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
          volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_b6diff_div_nat z hz k
  simpa [Nat.cast_add, Nat.cast_one] using
    (intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
      (a := fun k : ℕ => (k : ℝ)) (n := N) (μ := volume) hint)

lemma sum_interval_integral_b8diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n =>
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9) =
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
  classical
  have hint :
      ∀ k < N,
        IntervalIntegrable (fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
          volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_b8diff_div_nat z hz k
  simpa [Nat.cast_add, Nat.cast_one] using
    (intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
      (a := fun k : ℕ => (k : ℝ)) (n := N) (μ := volume) hint)

lemma sum_interval_integral_b10diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n =>
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11) =
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
  classical
  have hint :
      ∀ k < N,
        IntervalIntegrable (fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
          volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_b10diff_div_nat z hz k
  simpa [Nat.cast_add, Nat.cast_one] using
    (intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
      (a := fun k : ℕ => (k : ℝ)) (n := N) (μ := volume) hint)

lemma finite_stieltjes_B4Diff_to_B6Diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 =
      (252 : ℂ)⁻¹ * ((((N : ℂ) + z)⁻¹) ^ 6 - (z⁻¹) ^ 6) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
  classical
  let A : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5
  let B : ℕ → ℂ := fun n =>
    ((((n + 1 : ℂ) + z)⁻¹) ^ 6 - (((n : ℂ) + z)⁻¹) ^ 6)
  let C : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
  have hsum_cells :
      Finset.sum (Finset.range N) A =
        Finset.sum (Finset.range N) (fun n => (252 : ℂ)⁻¹ * B n + C n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simpa [A, B, C] using stieltjes_interval_B4Diff_to_B6Diff z hz n
  have hsum_split :
      Finset.sum (Finset.range N) (fun n => (252 : ℂ)⁻¹ * B n + C n) =
        (252 : ℂ)⁻¹ * Finset.sum (Finset.range N) B +
          Finset.sum (Finset.range N) C := by
    calc
      Finset.sum (Finset.range N) (fun n => (252 : ℂ)⁻¹ * B n + C n)
          = Finset.sum (Finset.range N) (fun n => (252 : ℂ)⁻¹ * B n) +
              Finset.sum (Finset.range N) C := by
              simp [Finset.sum_add_distrib]
      _ = (252 : ℂ)⁻¹ * Finset.sum (Finset.range N) B +
              Finset.sum (Finset.range N) C := by
              rw [← Finset.mul_sum]
  calc
    ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5
        = Finset.sum (Finset.range N) A := by
          simpa [A] using (sum_interval_integral_b4diff z hz N).symm
    _ = Finset.sum (Finset.range N) (fun n => (252 : ℂ)⁻¹ * B n + C n) := hsum_cells
    _ = (252 : ℂ)⁻¹ * Finset.sum (Finset.range N) B +
          Finset.sum (Finset.range N) C := hsum_split
    _ = (252 : ℂ)⁻¹ * ((((N : ℂ) + z)⁻¹) ^ 6 - (z⁻¹) ^ 6) +
          Finset.sum (Finset.range N) C := by
          rw [show Finset.sum (Finset.range N) B =
            ((((N : ℂ) + z)⁻¹) ^ 6 - (z⁻¹) ^ 6) by
              simpa [B] using sum_b6_boundary_telescope z N]
    _ = (252 : ℂ)⁻¹ * ((((N : ℂ) + z)⁻¹) ^ 6 - (z⁻¹) ^ 6) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
          rw [show Finset.sum (Finset.range N) C =
            ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 by
              simpa [C] using sum_interval_integral_b6diff z hz N]

lemma finite_stieltjes_B6Diff_to_B8Diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 =
      (-(240 : ℂ)⁻¹) * ((((N : ℂ) + z)⁻¹) ^ 8 - (z⁻¹) ^ 8) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
  classical
  let A : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
  let B : ℕ → ℂ := fun n =>
    ((((n + 1 : ℂ) + z)⁻¹) ^ 8 - (((n : ℂ) + z)⁻¹) ^ 8)
  let C : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9
  have hsum_cells :
      Finset.sum (Finset.range N) A =
        Finset.sum (Finset.range N) (fun n => (-(240 : ℂ)⁻¹) * B n + C n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simpa [A, B, C] using stieltjes_interval_B6Diff_to_B8Diff z hz n
  have hsum_split :
      Finset.sum (Finset.range N) (fun n => (-(240 : ℂ)⁻¹) * B n + C n) =
        (-(240 : ℂ)⁻¹) * Finset.sum (Finset.range N) B +
          Finset.sum (Finset.range N) C := by
    calc
      Finset.sum (Finset.range N) (fun n => (-(240 : ℂ)⁻¹) * B n + C n)
          = Finset.sum (Finset.range N) (fun n => (-(240 : ℂ)⁻¹) * B n) +
              Finset.sum (Finset.range N) C := by
              simp [Finset.sum_add_distrib]
      _ = (-(240 : ℂ)⁻¹) * Finset.sum (Finset.range N) B +
              Finset.sum (Finset.range N) C := by
              rw [← Finset.mul_sum]
  calc
    ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
        = Finset.sum (Finset.range N) A := by
          simpa [A] using (sum_interval_integral_b6diff z hz N).symm
    _ = Finset.sum (Finset.range N) (fun n => (-(240 : ℂ)⁻¹) * B n + C n) := hsum_cells
    _ = (-(240 : ℂ)⁻¹) * Finset.sum (Finset.range N) B +
          Finset.sum (Finset.range N) C := hsum_split
    _ = (-(240 : ℂ)⁻¹) * ((((N : ℂ) + z)⁻¹) ^ 8 - (z⁻¹) ^ 8) +
          Finset.sum (Finset.range N) C := by
          rw [show Finset.sum (Finset.range N) B =
            ((((N : ℂ) + z)⁻¹) ^ 8 - (z⁻¹) ^ 8) by
              simpa [B] using sum_b8_boundary_telescope z N]
    _ = (-(240 : ℂ)⁻¹) * ((((N : ℂ) + z)⁻¹) ^ 8 - (z⁻¹) ^ 8) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
          rw [show Finset.sum (Finset.range N) C =
            ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 by
              simpa [C] using sum_interval_integral_b8diff z hz N]

lemma finite_stieltjes_B8Diff_to_B10Diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 =
      (132 : ℂ)⁻¹ * ((((N : ℂ) + z)⁻¹) ^ 10 - (z⁻¹) ^ 10) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
  classical
  let A : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9
  let B : ℕ → ℂ := fun n =>
    ((((n + 1 : ℂ) + z)⁻¹) ^ 10 - (((n : ℂ) + z)⁻¹) ^ 10)
  let C : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11
  have hsum_cells :
      Finset.sum (Finset.range N) A =
        Finset.sum (Finset.range N) (fun n => (132 : ℂ)⁻¹ * B n + C n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simpa [A, B, C] using stieltjes_interval_B8Diff_to_B10Diff z hz n
  have hsum_split :
      Finset.sum (Finset.range N) (fun n => (132 : ℂ)⁻¹ * B n + C n) =
        (132 : ℂ)⁻¹ * Finset.sum (Finset.range N) B +
          Finset.sum (Finset.range N) C := by
    calc
      Finset.sum (Finset.range N) (fun n => (132 : ℂ)⁻¹ * B n + C n)
          = Finset.sum (Finset.range N) (fun n => (132 : ℂ)⁻¹ * B n) +
              Finset.sum (Finset.range N) C := by
              simp [Finset.sum_add_distrib]
      _ = (132 : ℂ)⁻¹ * Finset.sum (Finset.range N) B +
              Finset.sum (Finset.range N) C := by
              rw [← Finset.mul_sum]
  calc
    ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9
        = Finset.sum (Finset.range N) A := by
          simpa [A] using (sum_interval_integral_b8diff z hz N).symm
    _ = Finset.sum (Finset.range N) (fun n => (132 : ℂ)⁻¹ * B n + C n) := hsum_cells
    _ = (132 : ℂ)⁻¹ * Finset.sum (Finset.range N) B +
          Finset.sum (Finset.range N) C := hsum_split
    _ = (132 : ℂ)⁻¹ * ((((N : ℂ) + z)⁻¹) ^ 10 - (z⁻¹) ^ 10) +
          Finset.sum (Finset.range N) C := by
          rw [show Finset.sum (Finset.range N) B =
            ((((N : ℂ) + z)⁻¹) ^ 10 - (z⁻¹) ^ 10) by
              simpa [B] using sum_b10_boundary_telescope z N]
    _ = (132 : ℂ)⁻¹ * ((((N : ℂ) + z)⁻¹) ^ 10 - (z⁻¹) ^ 10) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
          rw [show Finset.sum (Finset.range N) C =
            ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 by
              simpa [C] using sum_interval_integral_b10diff z hz N]

lemma finite_sum_B2Fract_to_B4Diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N)
        (fun n =>
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3) =
      (1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) *
            (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4)) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
  classical
  let A : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3
  let C : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli4DiffCellDeriv n x : ℂ) / ((x : ℂ) + z) ^ 4
  let D : ℕ → ℂ := fun n =>
    ((((n + 1 : ℂ) + z)⁻¹) ^ 4 - (((n : ℂ) + z)⁻¹) ^ 4)
  let B : ℕ → ℂ := fun n =>
    ∫ x in (n : ℝ)..(n + 1 : ℝ),
      (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5
  have hA :
      Finset.sum (Finset.range N) A =
        Finset.sum (Finset.range N) (fun n => (1 / 4 : ℂ) * C n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simpa [A, C] using stieltjes_interval_B2Fract_to_B4CellDeriv z hz n
  have hC :
      Finset.sum (Finset.range N) C =
        Finset.sum (Finset.range N)
          (fun n => (-(30 : ℂ)⁻¹) * D n + (4 : ℂ) * B n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simpa [C, D, B] using stieltjes_interval_B4CellDeriv_to_B4Diff z hz n
  have hD := sum_b4_boundary_telescope z N
  have hB := sum_interval_integral_b4diff z hz N
  calc
    Finset.sum (Finset.range N)
        (fun n =>
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3)
        = Finset.sum (Finset.range N) A := by simp [A]
    _ = Finset.sum (Finset.range N) (fun n => (1 / 4 : ℂ) * C n) := hA
    _ = (1 / 4 : ℂ) * Finset.sum (Finset.range N) C := by
          simpa [mul_comm] using
            (Finset.mul_sum (a := (1 / 4 : ℂ)) (s := Finset.range N) (f := C)).symm
    _ = (1 / 4 : ℂ) *
          Finset.sum (Finset.range N)
            (fun n => (-(30 : ℂ)⁻¹) * D n + (4 : ℂ) * B n) := by
          rw [hC]
    _ = (1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) * Finset.sum (Finset.range N) D +
            (4 : ℂ) * Finset.sum (Finset.range N) B) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) *
              (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4) +
            (4 : ℂ) * ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5) := by
          rw [hD, hB]
    _ = (1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) *
            (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4)) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
          ring

lemma finite_stieltjes_B2Fract_to_B4Diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3 =
      (1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) *
            (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4)) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
  have hleft := sum_interval_integral_b2fract z hz N
  rw [← hleft]
  exact finite_sum_B2Fract_to_B4Diff z hz N

lemma intervalIntegrable_inv_add_pow_three_zero_nat
    (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    IntervalIntegrable (fun x : ℝ => (1 : ℂ) / ((x : ℂ) + z) ^ 3)
      volume (0 : ℝ) (N : ℝ) := by
  have hcont : ContinuousOn (fun x : ℝ => (1 : ℂ) / ((x : ℂ) + z) ^ 3)
      (Set.uIcc (0 : ℝ) (N : ℝ)) := by
    intro x hx
    have hle : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.cast_nonneg N)
    have hx' : x ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have hcont_add :
        ContinuousAt (fun x : ℝ => (x : ℂ) + z) x := by
      simpa using (Complex.continuous_ofReal.continuousAt.add continuous_const.continuousAt)
    have hcont_pow :
        ContinuousAt (fun x : ℝ => ((x : ℂ) + z) ^ 3) x := hcont_add.pow 3
    have hne : ((x : ℂ) + z) ^ 3 ≠ 0 := pow_ne_zero 3 hneq
    have hcont_inv :
        ContinuousAt (fun x : ℝ => (((x : ℂ) + z) ^ 3)⁻¹) x :=
      (ContinuousAt.inv₀ hcont_pow hne)
    simpa [one_div, div_eq_mul_inv] using hcont_inv.continuousWithinAt
  exact hcont.intervalIntegrable

lemma intervalIntegral_inv_add_pow_three_zero_nat
    (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∫ x in (0 : ℝ)..(N : ℝ), (1 : ℂ) / ((x : ℂ) + z) ^ 3 =
      (1 / 2 : ℂ) * ((z⁻¹) ^ 2 - ((((N : ℂ) + z)⁻¹) ^ 2)) := by
  let f : ℝ → ℂ := fun x => (-(1 / 2 : ℂ)) * (((x : ℂ) + z)⁻¹) ^ 2
  let f' : ℝ → ℂ := fun x => (1 : ℂ) / ((x : ℂ) + z) ^ 3
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    have hle : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.cast_nonneg N)
    have hx' : x ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    have hx0 : 0 ≤ x := hx'.1
    have hneq : (x : ℂ) + z ≠ 0 := add_ne_zero_of_re_pos hz hx0
    have h_inv := hasDerivAt_inv_add z hneq
    have h_sq := h_inv.pow 2
    have h_scaled := h_sq.const_mul (-(1 / 2 : ℂ))
    convert h_scaled using 1
    simp [f', one_div, div_eq_mul_inv]
    field_simp [hneq]
  have hInt : IntervalIntegrable f' volume (0 : ℝ) (N : ℝ) := by
    simpa [f'] using intervalIntegrable_inv_add_pow_three_zero_nat z hz N
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (N : ℝ)) (f := f) (f' := f') hderiv hInt
  calc
    ∫ x in (0 : ℝ)..(N : ℝ), (1 : ℂ) / ((x : ℂ) + z) ^ 3
        = f (N : ℝ) - f (0 : ℝ) := by
          simpa [f'] using hftc
    _ = (1 / 2 : ℂ) * ((z⁻¹) ^ 2 - ((((N : ℂ) + z)⁻¹) ^ 2)) := by
          simp [f, sub_eq_add_neg, mul_add, mul_comm, mul_left_comm, mul_assoc,
            add_comm, add_left_comm, add_assoc]

lemma finite_stieltjes_B2Diff_to_B4Diff (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 =
      (1 / 6 : ℂ) *
          ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - ((((N : ℂ) + z)⁻¹) ^ 2))) -
        ((1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) *
            (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4)) +
          ∫ x in (0 : ℝ)..(N : ℝ),
            (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5) := by
  have hpoint :
      ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
        (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 =
          (1 / 6 : ℂ) * ((1 : ℂ) / ((x : ℂ) + z) ^ 3) -
            (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3 := by
    intro x hx
    have hrel := bernoulli2Diff_eq_const_sub_fract x
    simp [hrel, sub_eq_add_neg, div_eq_mul_inv, mul_add, mul_comm, mul_left_comm,
      mul_assoc, add_comm, add_left_comm, add_assoc]
  have hcongr :
      ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 =
        ∫ x in (0 : ℝ)..(N : ℝ),
          (1 / 6 : ℂ) * ((1 : ℂ) / ((x : ℂ) + z) ^ 3) -
            (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3 := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hle : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.cast_nonneg N)
    have hx' : x ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      simpa [Set.uIcc_of_le hle] using hx
    exact hpoint x hx'
  have hIntInv := intervalIntegrable_inv_add_pow_three_zero_nat z hz N
  have hIntB2Fract : IntervalIntegrable
      (fun x : ℝ => (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3)
      volume (0 : ℝ) (N : ℝ) := by
    simpa using IntervalIntegrable.trans_iterate_Ico (a := fun k : ℕ => (k : ℝ))
      (m := 0) (n := N) (μ := volume) (f := fun x : ℝ =>
        (bernoulli2Fract x : ℂ) / ((x : ℂ) + z) ^ 3) (zero_le N) (by
        intro k hk
        simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_b2fract_div_nat z hz k)
  rw [hcongr]
  rw [intervalIntegral.integral_sub (hIntInv.const_mul (1 / 6 : ℂ)) hIntB2Fract]
  rw [intervalIntegral.integral_const_mul (r := (1 / 6 : ℂ))
    (f := fun x : ℝ => (1 : ℂ) / ((x : ℂ) + z) ^ 3)
    (a := (0 : ℝ)) (b := (N : ℝ)) (μ := volume)]
  rw [intervalIntegral_inv_add_pow_three_zero_nat z hz N]
  rw [finite_stieltjes_B2Fract_to_B4Diff z hz N]

lemma sum_inv_eq_log_plus_integral (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹) =
      Complex.log (z + (N : ℂ)) - Complex.log z
        + (1 / 2 : ℂ) * (z⁻¹ - (z + (N : ℂ))⁻¹)
        + ∫ x in (0 : ℝ)..(N : ℝ), (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
  classical
  have hsum_identity :
      Finset.sum (Finset.range N)
          (fun n => ∫ x in (n : ℝ)..(n + 1 : ℝ), ((x : ℂ) + z)⁻¹) =
        Finset.sum (Finset.range N) (fun n =>
          (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) -
            ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hpos := stieltjes_interval_identity_pos z hz n
    have hB := stieltjes_interval_B1_to_B2Diff z hz n
    calc
      ∫ x in (n : ℝ)..(n + 1 : ℝ), ((x : ℂ) + z)⁻¹
          = (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) +
              ∫ x in (n : ℝ)..(n + 1 : ℝ),
                ((x - (n : ℝ) - (1 / 2 : ℝ) : ℂ) * (((x : ℂ) + z) ^ 2)⁻¹) := hpos
      _ = (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) +
            (-∫ x in (n : ℝ)..(n + 1 : ℝ),
                (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) := by
            simpa using
              (congrArg
                (fun t =>
                  (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) + t) hB)
      _ = (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) -
            ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
            simp [sub_eq_add_neg]
  have hsum_identity' :
      ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹ =
        Finset.sum (Finset.range N) (fun n =>
            (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹)) -
          ∫ x in (0 : ℝ)..(N : ℝ),
            (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
    have hsum_identity'1 :
        ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹ =
          Finset.sum (Finset.range N) (fun n =>
              (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹)) -
            Finset.sum (Finset.range N) (fun n =>
              ∫ x in (n : ℝ)..(n + 1 : ℝ),
                (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) := by
      calc
        ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹
            = Finset.sum (Finset.range N)
                (fun n => ∫ x in (n : ℝ)..(n + 1 : ℝ), ((x : ℂ) + z)⁻¹) := by
                  simpa using (sum_interval_integral_inv z hz N).symm
        _ = Finset.sum (Finset.range N) (fun n =>
              (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹) -
                ∫ x in (n : ℝ)..(n + 1 : ℝ),
                  (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) := by
              simpa using hsum_identity
        _ = Finset.sum (Finset.range N) (fun n =>
              (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹)) -
            Finset.sum (Finset.range N) (fun n =>
              ∫ x in (n : ℝ)..(n + 1 : ℝ),
                (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) := by
              simpa [Finset.sum_sub_distrib]
    have hsum_b2 := sum_interval_integral_b2diff z hz N
    calc
      ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹
          =
        Finset.sum (Finset.range N) (fun n =>
            (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹)) -
          Finset.sum (Finset.range N) (fun n =>
            ∫ x in (n : ℝ)..(n + 1 : ℝ),
              (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) := hsum_identity'1
      _ =
        Finset.sum (Finset.range N) (fun n =>
            (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹)) -
          ∫ x in (0 : ℝ)..(N : ℝ),
            (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
            simpa using
              (congrArg
                (fun t =>
                  Finset.sum (Finset.range N) (fun n =>
                      (1 / 2 : ℂ) * (((n : ℂ) + z)⁻¹ + ((n + 1 : ℂ) + z)⁻¹)) - t)
                hsum_b2)
  have hsum_identity'' :
      ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹ =
        (Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹)) +
          (1 / 2 : ℂ) * (((z + (N : ℂ))⁻¹) - (z : ℂ)⁻¹) -
          ∫ x in (0 : ℝ)..(N : ℝ),
            (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
    have hsum_trap := sum_trapezoid_eq_sum z N
    have hsum_trap' :
        Finset.sum (Finset.range N)
            (fun n =>
              (1 / 2 : ℂ) * (((z + (n : ℂ))⁻¹) + ((z + (n + 1 : ℂ))⁻¹))) -
            ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3
          =
        (Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹)) +
            (1 / 2 : ℂ) * (((z + (N : ℂ))⁻¹) - (z : ℂ)⁻¹) -
            ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
      exact
        (congrArg
          (fun t =>
            t - ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) hsum_trap)
    calc
      ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹
          =
        Finset.sum (Finset.range N) (fun n =>
            (1 / 2 : ℂ) * (((z + (n : ℂ))⁻¹) + ((z + (n + 1 : ℂ))⁻¹))) -
          ∫ x in (0 : ℝ)..(N : ℝ),
            (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
          -- align with the `sum_trapezoid_eq_sum` shape
          simpa [add_comm, add_left_comm, add_assoc, Nat.cast_add, Nat.cast_one, one_div]
            using hsum_identity'
      _ =
        (Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹)) +
          (1 / 2 : ℂ) * (((z + (N : ℂ))⁻¹) - (z : ℂ)⁻¹) -
          ∫ x in (0 : ℝ)..(N : ℝ),
            (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
          simpa using hsum_trap'
  set Iint : ℂ := ∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + z)⁻¹
  set Jint : ℂ := ∫ x in (0 : ℝ)..(N : ℝ),
    (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3
  have hsum_main :
      Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹) =
        Iint + Jint -
          (2⁻¹ : ℂ) * ((z + (N : ℂ))⁻¹ + -z⁻¹) := by
    have h := congrArg (fun t => t + Jint) (by simpa [Iint, Jint] using hsum_identity'')
    have h' :
        Iint + Jint =
          (2⁻¹ : ℂ) * ((z + (N : ℂ))⁻¹ + -z⁻¹) +
            (Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹)) := by
      simpa [Iint, Jint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    have h'' :
        Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹) =
          Iint + Jint -
            (2⁻¹ : ℂ) * ((z + (N : ℂ))⁻¹ + -z⁻¹) := by
      refine (eq_sub_iff_add_eq).2 ?_
      simpa [add_comm, add_left_comm, add_assoc] using h'.symm
    simpa using h''
  have hsum_main' :
      Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹) =
        Iint + Jint + (1 / 2 : ℂ) * (z⁻¹ - (z + (N : ℂ))⁻¹) := by
    calc
      Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹)
          = Iint + Jint -
              (2⁻¹ : ℂ) * ((z + (N : ℂ))⁻¹ + -z⁻¹) := hsum_main
      _ = Iint + Jint + (1 / 2 : ℂ) * (z⁻¹ - (z + (N : ℂ))⁻¹) := by
          ring
  have hlog := intervalIntegral_inv_eq_log z hz N
  calc
    Finset.sum (Finset.range N) (fun n => (z + (n : ℂ))⁻¹)
        = (Complex.log (z + (N : ℂ)) - Complex.log z) +
            (1 / 2 : ℂ) * (z⁻¹ - (z + (N : ℂ))⁻¹) +
            ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
          -- rearrange `hsum_main` into the desired shape
          simpa [Iint, Jint, hlog, add_assoc, add_left_comm, add_comm] using hsum_main'

lemma digammaSeq_eq_stieltjes (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    _root_.digammaSeq z N =
      (Real.log N : ℂ) - Complex.log (z + (N : ℂ)) + Complex.log z
        - (1 / 2 : ℂ) * z⁻¹ - (1 / 2 : ℂ) * (z + (N : ℂ))⁻¹
        - ∫ x in (0 : ℝ)..(N : ℝ), (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
  classical
  have hsum_range :
      Finset.sum (Finset.range (N + 1)) (fun k => (z + (k : ℂ))⁻¹) =
        Finset.sum (Finset.range N) (fun k => (z + (k : ℂ))⁻¹) + (z + (N : ℂ))⁻¹ := by
    simpa using
      (Finset.sum_range_succ (f := fun k => (z + (k : ℂ))⁻¹) N)
  have hsum := sum_inv_eq_log_plus_integral z hz N
  calc
    _root_.digammaSeq z N
        = (Real.log N : ℂ) -
            ((Finset.sum (Finset.range N) (fun k => (z + (k : ℂ))⁻¹)) + (z + (N : ℂ))⁻¹) := by
            simp [digammaSeq, one_div, hsum_range, sub_eq_add_neg, add_assoc]
    _ = (Real.log N : ℂ) - (Finset.sum (Finset.range N) (fun k => (z + (k : ℂ))⁻¹)) -
            (z + (N : ℂ))⁻¹ := by
            ring
    _ = (Real.log N : ℂ) -
          (Complex.log (z + (N : ℂ)) - Complex.log z
            + (1 / 2 : ℂ) * (z⁻¹ - (z + (N : ℂ))⁻¹)
            + ∫ x in (0 : ℝ)..(N : ℝ),
                (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) -
          (z + (N : ℂ))⁻¹ := by
            simpa [hsum] using rfl
    _ = (Real.log N : ℂ) - Complex.log (z + (N : ℂ)) + Complex.log z
          - (1 / 2 : ℂ) * z⁻¹ - (1 / 2 : ℂ) * (z + (N : ℂ))⁻¹
          - ∫ x in (0 : ℝ)..(N : ℝ), (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 := by
          ring_nf
/-!
Stieltjes (N=1) swap-derivative lemma (parameter differentiation under the integral).
This is the analytic core needed to remove `digamma_stieltjes_identity`.
-/
abbrev stieltjesF (w : ℂ) (x : ℝ) : ℂ :=
  (bernoulli2Diff x : ℂ) / (2 * (x + w) ^ 2)

abbrev stieltjesF' (w : ℂ) (x : ℝ) : ℂ :=
  -((bernoulli2Diff x : ℂ) / (x + w) ^ 3)

abbrev stieltjesBound (ε : ℝ) (x : ℝ) : ℝ :=
  (4 : ℝ)⁻¹ * ((x + ε) ^ 3)⁻¹

set_option maxHeartbeats 3000000 in
lemma stieltjes_integral_hasDerivAt (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt
      (fun w => ∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (2 * (x + w) ^ 2))
      (-∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (x + z) ^ 3) z := by
  classical
  -- Measure restricted to (0,∞)
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  -- Normalize integral notation to match the parametric integral lemma.
  change
    HasDerivAt (fun w => ∫ x, stieltjesF w x ∂μ)
      (-∫ x, (bernoulli2Diff x : ℂ) / (x + z) ^ 3 ∂μ) z
  -- Neighborhood radius
  let ε : ℝ := z.re / 2
  have hε : 0 < ε := by
    dsimp [ε]
    nlinarith [hz]
  have hball_re : ∀ {w : ℂ}, w ∈ Metric.ball z ε → ε ≤ w.re := by
    intro w hw
    have hdist : ‖w - z‖ < ε := by
      simpa [Metric.ball, dist_eq_norm] using hw
    have hrew : |w.re - z.re| ≤ ‖w - z‖ := by
      have h := RCLike.abs_re_le_norm (z := w - z)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    have habs : |w.re - z.re| < ε := lt_of_le_of_lt hrew hdist
    have hlow : z.re - ε < w.re := by
      have h := (abs_lt.mp habs).1
      linarith
    dsimp [ε] at hlow ⊢
    linarith [hz, hlow]
  -- measurability for F near z
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (stieltjesF w) μ := by
    refine Filter.Eventually.of_forall ?_
    intro w
    have hmeas : Measurable (fun x => stieltjesF w x) := by
      have hcoe : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
      have h_add : Measurable (fun x : ℝ => (x : ℂ) + w) := hcoe.add measurable_const
      have h_pow : Measurable (fun x : ℝ => ((x : ℂ) + w) ^ 2) := h_add.pow_const 2
      have h_den : Measurable (fun x : ℝ => (2 : ℂ) * ((x : ℂ) + w) ^ 2) :=
        measurable_const.mul h_pow
      have h_num : Measurable (fun x : ℝ => (bernoulli2Diff x : ℂ)) :=
        (Complex.measurable_ofReal.comp measurable_bernoulli2Diff)
      exact h_num.div h_den
    simpa [μ] using hmeas.aestronglyMeasurable
  -- integrability of F at z using a crude (x+ε)^{-2} bound
  have hF_int : Integrable (stieltjesF z) μ := by
    -- |F z x| ≤ (1/8) * (x+ε)^{-2}
    have hbound :
        ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖stieltjesF z x‖ ≤ (1 / 8 : ℝ) * (1 / (x + ε) ^ 2) := by
      intro x hx
      have hxpos : 0 < x := by simpa using hx
      have hxεpos : 0 < x + ε := by nlinarith [hxpos, hε]
      have hb0 : 0 ≤ bernoulli2Diff x := (bernoulli2Diff_bounds x).1
      have hb1 : bernoulli2Diff x ≤ (1 / 4 : ℝ) := (bernoulli2Diff_bounds x).2
      have hnorm_b : ‖(bernoulli2Diff x : ℂ)‖ ≤ (1 / 4 : ℝ) := by
        have habs : |bernoulli2Diff x| = bernoulli2Diff x := by
          simp [abs_of_nonneg hb0]
        have hnorm : ‖(bernoulli2Diff x : ℂ)‖ = |bernoulli2Diff x| := by
          simp
        simpa [hnorm, habs] using hb1
      have hεle : ε ≤ z.re := by
        dsimp [ε]
        exact half_le_self (le_of_lt hz)
      have hre : x + ε ≤ x + z.re := by nlinarith [hεle]
      have hnorm_ge : x + ε ≤ ‖(x : ℂ) + z‖ := by
        have h' : |x + z.re| ≤ ‖(x : ℂ) + z‖ := by
          simpa using (RCLike.abs_re_le_norm ((x : ℂ) + z))
        have hpos_re : 0 ≤ x + z.re := by nlinarith [hxpos, hz]
        have habs : |x + z.re| = x + z.re := by simp [abs_of_nonneg hpos_re]
        have h'' : x + z.re ≤ ‖(x : ℂ) + z‖ := by
          simpa [abs_of_nonneg hpos_re] using h'
        exact le_trans hre h''
      have hpow : (x + ε) ^ 2 ≤ ‖(x : ℂ) + z‖ ^ 2 := by
        have hpos : 0 ≤ x + ε := by linarith [hxεpos]
        have hpos' : 0 ≤ ‖(x : ℂ) + z‖ := by positivity
        have hmul := mul_le_mul hnorm_ge hnorm_ge hpos hpos'
        simpa [pow_two] using hmul
      have hle_inv : 1 / ‖(x : ℂ) + z‖ ^ 2 ≤ 1 / (x + ε) ^ 2 := by
        have hpos : 0 < (x + ε) ^ 2 := by nlinarith [hxεpos]
        exact one_div_le_one_div_of_le hpos hpow
      calc
      ‖stieltjesF z x‖
            = ‖(bernoulli2Diff x : ℂ)‖ / ‖2 * ((x : ℂ) + z) ^ 2‖ := by
                simp [stieltjesF]
        _ ≤ (1 / 4 : ℝ) / ‖2 * ((x : ℂ) + z) ^ 2‖ := by
                exact (div_le_div_of_nonneg_right hnorm_b (by positivity))
        _ = (1 / 8 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 2) := by
                have hnorm : ‖2 * ((x : ℂ) + z) ^ 2‖ = (2:ℝ) * ‖(x : ℂ) + z‖ ^ 2 := by
                  simp [norm_pow]
                calc
                  (1 / 4 : ℝ) / ‖2 * ((x : ℂ) + z) ^ 2‖
                      = (1 / 4 : ℝ) / ((2:ℝ) * ‖(x : ℂ) + z‖ ^ 2) := by simp
                  _ = (1 / 8 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 2) := by ring_nf
        _ ≤ (1 / 8 : ℝ) * (1 / (x + ε) ^ 2) := by
                exact mul_le_mul_of_nonneg_left hle_inv (by positivity)
    -- integrability of the bound (x+ε)^(-2)
    have h_int : IntegrableOn (fun x : ℝ => (x + ε) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) := by
      have hlt : (-2 : ℝ) < -1 := by linarith
      have hc : -ε < (0 : ℝ) := by nlinarith [hε]
      simpa using (integrableOn_add_rpow_Ioi_of_lt hlt hc)
    have h_int' : IntegrableOn (fun x : ℝ => 1 / (x + ε) ^ 2) (Set.Ioi (0 : ℝ)) := by
      refine h_int.congr_fun ?_ measurableSet_Ioi
      intro x hx
      have hpow :
          (x + ε) ^ (-2 : ℝ) = 1 / (x + ε) ^ 2 := by
        calc
          (x + ε) ^ (-2 : ℝ) = (x + ε)⁻¹ ^ (2 : ℝ) := by
            simpa using (rpow_neg_eq_inv_rpow (x + ε) (2 : ℝ))
          _ = (x + ε)⁻¹ ^ (2 : ℕ) := by
            simp
          _ = (1 / (x + ε)) ^ 2 := by
            simp [one_div]
          _ = 1 / (x + ε) ^ 2 := by
            simp [one_div, inv_pow]
      exact hpow
    have h_int'' : Integrable (fun x : ℝ => 1 / (x + ε) ^ 2) μ := by
      simpa [IntegrableOn, μ] using h_int'
    have hF_meas_z : AEStronglyMeasurable (stieltjesF z) μ := by
      have hmeas : Measurable (fun x => stieltjesF z x) := by
        have hcoe : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
        have h_add : Measurable (fun x : ℝ => (x : ℂ) + z) := hcoe.add measurable_const
        have h_pow : Measurable (fun x : ℝ => ((x : ℂ) + z) ^ 2) := h_add.pow_const 2
        have h_den : Measurable (fun x : ℝ => (2 : ℂ) * ((x : ℂ) + z) ^ 2) :=
          measurable_const.mul h_pow
        have h_num : Measurable (fun x : ℝ => (bernoulli2Diff x : ℂ)) :=
          (Complex.measurable_ofReal.comp measurable_bernoulli2Diff)
        exact h_num.div h_den
      simpa [μ] using hmeas.aestronglyMeasurable
    refine (h_int''.const_mul (1 / 8 : ℝ)).mono' hF_meas_z ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    exact hbound x hx
  -- measurability of F' at z
  have hF'_meas : AEStronglyMeasurable (stieltjesF' z) μ := by
    have hmeas : Measurable (fun x => stieltjesF' z x) := by
      have hcoe : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
      have h_add : Measurable (fun x : ℝ => (x : ℂ) + z) := hcoe.add measurable_const
      have h_pow : Measurable (fun x : ℝ => ((x : ℂ) + z) ^ 3) := h_add.pow_const 3
      have h_den : Measurable (fun x : ℝ => ((x : ℂ) + z) ^ 3) := h_pow
      have h_num : Measurable (fun x : ℝ => (bernoulli2Diff x : ℂ)) :=
        (Complex.measurable_ofReal.comp measurable_bernoulli2Diff)
      have h_div : Measurable (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) :=
        h_num.div h_den
      have h_neg :
          Measurable (fun x : ℝ => -((bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)) :=
        h_div.neg
      simpa [stieltjesF'] using h_neg
    simpa [μ] using hmeas.aestronglyMeasurable
  -- bound on F' on half-plane s
  have h_bound :
      ∀ᵐ x ∂μ, ∀ w ∈ Metric.ball z ε, ‖stieltjesF' w x‖ ≤ stieltjesBound ε x := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx w hw
    have hεle : ε ≤ w.re := hball_re hw
    have hx0 : 0 < x := by simpa using hx
    have hxε : 0 < x + ε := by nlinarith [hx0, hε]
    have hb0 : 0 ≤ bernoulli2Diff x := (bernoulli2Diff_bounds x).1
    have hb1 : bernoulli2Diff x ≤ (1 / 4 : ℝ) := (bernoulli2Diff_bounds x).2
    have hnorm_b : ‖(bernoulli2Diff x : ℂ)‖ ≤ (1 / 4 : ℝ) := by
      have habs : |bernoulli2Diff x| = bernoulli2Diff x := by
        simp [abs_of_nonneg hb0]
      have hnorm : ‖(bernoulli2Diff x : ℂ)‖ = |bernoulli2Diff x| := by
        simp
      simpa [hnorm, habs] using hb1
    have h_re_nonneg : 0 ≤ x + w.re := by nlinarith [hx0, hεle]
    have hnorm_ge : x + w.re ≤ ‖(x : ℂ) + w‖ := by
      have habs : |((x : ℂ) + w).re| ≤ ‖(x : ℂ) + w‖ := by
        simpa using (RCLike.abs_re_le_norm ((x : ℂ) + w))
      have hrew : ((x : ℂ) + w).re = x + w.re := by simp
      simpa [hrew, abs_of_nonneg h_re_nonneg] using habs
    have hnorm_ge_eps : x + ε ≤ ‖(x : ℂ) + w‖ := by
      have : x + ε ≤ x + w.re := by nlinarith [hεle]
      exact le_trans this hnorm_ge
    have hpow2 : (x + ε) ^ 2 ≤ ‖(x : ℂ) + w‖ ^ 2 := by
      have h0 : 0 ≤ x + ε := by nlinarith [hxε]
      have h0n : 0 ≤ ‖(x : ℂ) + w‖ := by positivity
      have hmul := mul_le_mul hnorm_ge_eps hnorm_ge_eps h0 h0n
      simpa [pow_two] using hmul
    have hpow3 : (x + ε) ^ 3 ≤ ‖(x : ℂ) + w‖ ^ 3 := by
      have h0 : 0 ≤ x + ε := by nlinarith [hxε]
      have h0n2 : 0 ≤ ‖(x : ℂ) + w‖ ^ 2 := by positivity
      have hmul := mul_le_mul hpow2 hnorm_ge_eps (by nlinarith [h0]) h0n2
      simpa [pow_succ, pow_two, mul_assoc] using hmul
    have hpos' : 0 < x + ε := by nlinarith [hxε]
    have hpos : 0 < (x + ε) ^ 3 := by
      simpa using (pow_pos hpos' 3)
    have hle_inv' : 1 / ‖(x : ℂ) + w‖ ^ 3 ≤ 1 / (x + ε) ^ 3 :=
      one_div_le_one_div_of_le hpos hpow3
    calc
      ‖stieltjesF' w x‖
          = ‖(bernoulli2Diff x : ℂ)‖ / ‖(x + w : ℂ) ^ 3‖ := by
              simp [stieltjesF']
      _ = ‖(bernoulli2Diff x : ℂ)‖ / ‖(x : ℂ) + w‖ ^ 3 := by
              simp [norm_pow]
      _ ≤ (1 / 4 : ℝ) / ‖(x : ℂ) + w‖ ^ 3 := by
              exact (div_le_div_of_nonneg_right hnorm_b (by positivity))
      _ ≤ (1 / 4 : ℝ) / (x + ε) ^ 3 := by
              have hmul :
                  (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + w‖ ^ 3) ≤
                    (1 / 4 : ℝ) * (1 / (x + ε) ^ 3) :=
                mul_le_mul_of_nonneg_left hle_inv' (by positivity)
              calc
                (1 / 4 : ℝ) / ‖(x : ℂ) + w‖ ^ 3
                    = (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + w‖ ^ 3) := by
                        simp [div_eq_mul_inv]
                _ ≤ (1 / 4 : ℝ) * (1 / (x + ε) ^ 3) := hmul
                _ = (1 / 4 : ℝ) / (x + ε) ^ 3 := by
                        simp [div_eq_mul_inv]
      _ = stieltjesBound ε x := by
              simp [stieltjesBound, div_eq_mul_inv]
  -- integrability of bound
  have h_bound_int : Integrable (stieltjesBound ε) μ := by
    have h_int : IntegrableOn (fun x : ℝ => (x + ε) ^ (-3 : ℝ)) (Set.Ioi (0 : ℝ)) := by
      have hlt : (-3 : ℝ) < -1 := by linarith
      have hc : -ε < (0 : ℝ) := by nlinarith [hε]
      simpa using (integrableOn_add_rpow_Ioi_of_lt hlt hc)
    have h_int' : Integrable (fun x : ℝ => (x + ε) ^ (-3 : ℝ)) μ := by
      simpa [IntegrableOn, μ] using h_int
    have h_int'' : Integrable (fun x : ℝ => ((x + ε) ^ 3)⁻¹) μ := by
      simpa [rpow_neg_eq_inv_rpow, rpow_natCast, one_div] using h_int'
    change Integrable (fun x : ℝ => (4 : ℝ)⁻¹ * ((x + ε) ^ 3)⁻¹) μ
    exact h_int''.const_mul ((4 : ℝ)⁻¹)
  -- pointwise derivative in w (for ae x)
  have h_diff :
      ∀ᵐ x ∂μ, ∀ w ∈ Metric.ball z ε, HasDerivAt (fun w => stieltjesF w x) (stieltjesF' w x) w := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx w hw
    have hεle : ε ≤ w.re := hball_re hw
    have hx0 : 0 < x := by simpa using hx
    have hneq : (x : ℂ) + w ≠ 0 := by
      intro hzero
      have hxwpos : 0 < x + w.re := by nlinarith [hx0, hεle, hε]
      have hzero' : x + w.re = 0 := by
        have hrew : ((x : ℂ) + w).re = x + w.re := by simp
        simpa [hrew] using congrArg Complex.re hzero
      nlinarith [hxwpos, hzero']
    -- derivative calculation
    have h1 : HasDerivAt (fun w => (x : ℂ) + w) 1 w := by
      simpa [add_comm] using (hasDerivAt_id w).const_add (x : ℂ)
    have h2 : HasDerivAt (fun w => ((x : ℂ) + w) ^ 2) (2 * ((x : ℂ) + w)) w := by
      simpa [pow_two] using (h1.pow 2)
    have h3 :
        HasDerivAt (fun w => ((x : ℂ) + w) ^ 2) (2 * ((x : ℂ) + w)) w := h2
    have h4 :
        HasDerivAt (fun w => (((x : ℂ) + w) ^ 2)⁻¹)
          (-(2 * ((x : ℂ) + w)) / (((x : ℂ) + w) ^ 2) ^ 2) w := by
      simpa [one_div] using (h3.inv (by
        have : ((x : ℂ) + w) ^ 2 ≠ 0 := by
          exact pow_ne_zero 2 hneq
        exact this))
    have h5 :
        HasDerivAt (fun w => (1 / (2 : ℂ)) * (((x : ℂ) + w) ^ 2)⁻¹)
          ((1 / (2 : ℂ)) * (-(2 * ((x : ℂ) + w)) / (((x : ℂ) + w) ^ 2) ^ 2)) w := by
      simpa using h4.const_mul (1 / (2 : ℂ))
    have h6 :
        HasDerivAt (fun w => stieltjesF w x)
          (((1 / (2 : ℂ)) * (-(2 * ((x : ℂ) + w)) / (((x : ℂ) + w) ^ 2) ^ 2)) *
            (bernoulli2Diff x : ℂ)) w := by
      simpa [stieltjesF, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (h5.const_mul (bernoulli2Diff x : ℂ))
    have hcalc :
        ((1 / (2 : ℂ)) * (-(2 * ((x : ℂ) + w)) / (((x : ℂ) + w) ^ 2) ^ 2)) *
            (bernoulli2Diff x : ℂ) =
          -((bernoulli2Diff x : ℂ) / ((x : ℂ) + w) ^ 3) := by
      field_simp [hneq]
    have hcalc' :
        ((1 / (2 : ℂ)) * (-(2 * ((x : ℂ) + w)) / (((x : ℂ) + w) ^ 2) ^ 2)) *
            (bernoulli2Diff x : ℂ) = stieltjesF' w x := by
      simpa [stieltjesF'] using hcalc
    -- rewrite the derivative target using hcalc'
    have h6' : HasDerivAt (fun w => stieltjesF w x) (stieltjesF' w x) w := by
      convert h6 using 1
      exact hcalc'.symm
    exact h6'
  -- apply dominated differentiation lemma
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := stieltjesF)
      (x₀ := z) (bound := stieltjesBound ε) hε
      hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  rcases hmain with ⟨_, hmain⟩
  -- Convert ∫ stieltjesF' to the target `-∫ ...` form.
  have hneg :
      ∫ x, stieltjesF' z x ∂μ =
        -∫ x, (bernoulli2Diff x : ℂ) / (x + z) ^ 3 ∂μ := by
    change ∫ x, -((bernoulli2Diff x : ℂ) / (x + z) ^ 3) ∂μ =
      -∫ x, (bernoulli2Diff x : ℂ) / (x + z) ^ 3 ∂μ
    simpa using
      (integral_neg (μ := μ) (f := fun x : ℝ => (bernoulli2Diff x : ℂ) / (x + z) ^ 3))
  have hmain' :
      HasDerivAt (fun w => ∫ x, stieltjesF w x ∂μ)
        (-∫ x, (bernoulli2Diff x : ℂ) / (x + z) ^ 3 ∂μ) z := by
    exact hmain.congr_deriv hneg
  simpa [stieltjesF, stieltjesF', μ] using hmain'

lemma stieltjes_integral_deriv (z : ℂ) (hz : 0 < z.re) :
    deriv (fun w => ∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (2 * (x + w) ^ 2)) z =
      -∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (x + z) ^ 3 := by
  simpa using (stieltjes_integral_hasDerivAt z hz).deriv

/-!
Kernel integral. The full calculus proof is being formalized; we keep the
exact evaluation as a local theorem and use it for the analytic tail bounds.
-/

lemma integral_kernel_eq (σ τ : ℝ) (hσ : 0 < σ) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / ((x + σ) ^ 2 + τ ^ 2) ^ (3 / 2 : ℝ) =
      1 / (Real.sqrt (σ ^ 2 + τ ^ 2) * (Real.sqrt (σ ^ 2 + τ ^ 2) + σ)) := by
  classical
  by_cases hτ : τ = 0
  · subst hτ
    have hσ' : 0 < σ := hσ
    let g : ℝ → ℝ := fun x => (-1 / 2 : ℝ) * ((x + σ) ^ 2)⁻¹
    let g' : ℝ → ℝ := fun x => 1 / ((x + σ) ^ 2) ^ (3 / 2 : ℝ)
    have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g (g' x) x := by
      intro x hx
      have hx0 : 0 ≤ x := hx
      have hxpos : 0 < x + σ := by linarith [hx0, hσ']
      have hsq : 0 ≤ (x + σ) ^ 2 := by nlinarith
      have hpow :
          ((x + σ) ^ 2) ^ (3 / 2 : ℝ) = (x + σ) ^ 3 := by
        calc
          ((x + σ) ^ 2) ^ (3 / 2 : ℝ)
              = ((x + σ) ^ 2) ^ ((1 / 2 : ℝ) * (3 : ℝ)) := by ring_nf
          _ = (((x + σ) ^ 2) ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
            simp [Real.rpow_mul hsq]
          _ = (Real.sqrt ((x + σ) ^ 2)) ^ (3 : ℝ) := by
            simp [Real.sqrt_eq_rpow]
          _ = (x + σ) ^ (3 : ℝ) := by
            have hsqrt : Real.sqrt ((x + σ) ^ 2) = x + σ := by
              simp [Real.sqrt_sq_eq_abs, abs_of_pos hxpos]
            simp [hsqrt]
          _ = (x + σ) ^ 3 := by simp
      have hderiv0 :
          HasDerivAt g (1 / (x + σ) ^ 3) x := by
        have h1 : HasDerivAt (fun x => x + σ) 1 x := by
          simpa using (hasDerivAt_id x).add_const σ
        have h2 : HasDerivAt (fun x => (x + σ) ^ 2) (2 * (x + σ)) x := by
          simpa [pow_two] using (h1.pow 2)
        have hne : (x + σ) ^ 2 ≠ 0 := by nlinarith [hxpos]
        have h3 :
            HasDerivAt (fun x => ((x + σ) ^ 2)⁻¹)
              (-(2 * (x + σ)) / ((x + σ) ^ 2) ^ 2) x := by
          simpa [one_div] using (h2.inv hne)
        have h4 :
            HasDerivAt (fun x => (-1 / 2 : ℝ) * ((x + σ) ^ 2)⁻¹)
              ((-1 / 2 : ℝ) * (-(2 * (x + σ)) / ((x + σ) ^ 2) ^ 2)) x := by
          simpa using h3.const_mul (-1 / 2 : ℝ)
        have h5 :
            HasDerivAt g ((-1 / 2 : ℝ) * (-(2 * (x + σ)) / ((x + σ) ^ 2) ^ 2)) x := by
          simpa [g, mul_comm, mul_left_comm, mul_assoc] using h4
        have h6 :
            (-1 / 2 : ℝ) * (-(2 * (x + σ)) / ((x + σ) ^ 2) ^ 2) =
              1 / (x + σ) ^ 3 := by
          field_simp [pow_two]
        simpa [h6] using h5
      exact (by simpa [g', hpow] using hderiv0)
    have g'pos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g' x := by
      intro x hx
      have hsq : 0 ≤ (x + σ) ^ 2 := by nlinarith
      have hpow : 0 ≤ ((x + σ) ^ 2) ^ (3 / 2 : ℝ) := by
        exact Real.rpow_nonneg hsq _
      exact one_div_nonneg.mpr hpow
    have hlim : Tendsto g atTop (𝓝 (0 : ℝ)) := by
      have hlim_add : Tendsto (fun x => x + σ) atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro b
        refine (eventually_atTop.2 ?_)
        refine ⟨b - σ, ?_⟩
        intro x hx
        linarith
      have hlim_sq : Tendsto (fun x => (x + σ) ^ 2) atTop atTop := by
        have hpow : Tendsto (fun y : ℝ => y ^ 2) atTop atTop := by
          exact tendsto_pow_atTop (α := ℝ) (n := 2) (by simp)
        exact hpow.comp hlim_add
      have hlim_inv :
          Tendsto (fun x => ((x + σ) ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
        exact tendsto_inv_atTop_zero.comp hlim_sq
      have hlim_inv' : Tendsto (fun x => 1 / (x + σ) ^ 2) atTop (𝓝 (0 : ℝ)) := by
        simpa [one_div] using hlim_inv
      have hlim_mul :
          Tendsto (fun x => (-1 / 2 : ℝ) * (1 / (x + σ) ^ 2)) atTop (𝓝 (0 : ℝ)) := by
        have hconst : Tendsto (fun _ : ℝ => (-1 / 2 : ℝ)) atTop (𝓝 (-1 / 2 : ℝ)) :=
          tendsto_const_nhds
        simpa [mul_comm, mul_left_comm, mul_assoc] using hconst.mul hlim_inv'
      simpa [g, mul_comm, mul_left_comm, mul_assoc] using hlim_mul
    have hmain :=
      integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ)) hderiv g'pos hlim
    have hF0 : g 0 = (-1 / 2 : ℝ) * (σ ^ 2)⁻¹ := by
      simp [g]
    have hsqrt : Real.sqrt (σ ^ 2) = σ := by
      simp [Real.sqrt_sq_eq_abs, abs_of_pos hσ]
    calc
      ∫ x in Set.Ioi (0 : ℝ), 1 / ((x + σ) ^ 2 + (0 : ℝ) ^ 2) ^ (3 / 2 : ℝ)
          = ∫ x in Set.Ioi (0 : ℝ), g' x := by simp [g']
      _ = (0 : ℝ) - g 0 := hmain
      _ = 1 / (2 * σ ^ 2) := by
        simp [hF0, div_eq_mul_inv, mul_comm]
      _ =
          1 / (Real.sqrt (σ ^ 2 + (0 : ℝ) ^ 2) *
            (Real.sqrt (σ ^ 2 + (0 : ℝ) ^ 2) + σ)) := by
        have hσne : σ ≠ 0 := by linarith [hσ]
        field_simp [hσne]
        simp [hsqrt]
        ring_nf
  ·
    have hτ2 : τ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 hτ
    let u : ℝ → ℝ := fun x => (x + σ) ^ 2 + τ ^ 2
    let s : ℝ → ℝ := fun x => Real.sqrt (u x)
    let sinv : ℝ → ℝ := s⁻¹
    let c : ℝ := (τ ^ 2)⁻¹
    let g : ℝ → ℝ := fun x => c * ((x + σ) / s x)
    let g' : ℝ → ℝ := fun x => 1 / ((x + σ) ^ 2 + τ ^ 2) ^ (3 / 2 : ℝ)
    have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g (g' x) x := by
      intro x hx
      have hx0 : 0 ≤ x := hx
      have hxpos : 0 < x + σ := by linarith [hσ, hx0]
      have hpos : 0 < u x := by
        have hpos' : 0 < (x + σ) ^ 2 := by nlinarith [hxpos]
        have ht : 0 ≤ τ ^ 2 := by nlinarith
        have : 0 < (x + σ) ^ 2 + τ ^ 2 := add_pos_of_pos_of_nonneg hpos' ht
        simpa [u] using this
      have hsq : 0 ≤ u x := le_of_lt hpos
      have h1 : HasDerivAt (fun x => x + σ) 1 x := by
        simpa using (hasDerivAt_id x).add_const σ
      have h2 : HasDerivAt (fun x => (x + σ) ^ 2) (2 * (x + σ)) x := by
        simpa [pow_two] using (h1.pow 2)
      have h3 : HasDerivAt u (2 * (x + σ)) x := by
        simpa [u] using h2.const_add (τ ^ 2)
      have h4 :
          HasDerivAt s ((2 * (x + σ)) / (2 * s x)) x := by
        have hne : u x ≠ 0 := by exact ne_of_gt hpos
        simpa [s] using h3.sqrt hne
      have h5 :
          HasDerivAt sinv
            (-(2 * (x + σ) / (2 * s x)) / (s x) ^ 2) x := by
        have hsne : s x ≠ 0 := by
          have hspos : 0 < s x := by
            exact Real.sqrt_pos.mpr hpos
          exact ne_of_gt hspos
        simpa [sinv] using h4.inv hsne
      have h6 :
          HasDerivAt (fun x => (x + σ) / s x)
            (sinv x + (x + σ) * (-(2 * (x + σ) / (2 * s x)) / (s x) ^ 2)) x := by
        simpa [sinv, div_eq_mul_inv] using h1.mul h5
      have h7 :
          HasDerivAt g
            (c *
              (sinv x + (x + σ) * (-(2 * (x + σ) / (2 * s x)) / (s x) ^ 2))) x := by
        simpa [g, c, sinv, mul_comm, mul_left_comm, mul_assoc] using h6.const_mul c
      have hsq' : (s x) ^ 2 = u x := by
        simpa [s] using (Real.sq_sqrt hsq)
      have hA :
          c *
              (sinv x + (x + σ) * (-(2 * (x + σ) / (2 * s x)) / (s x) ^ 2)) =
          g' x := by
        have hnum : (s x) ^ 2 - (x + σ) ^ 2 = τ ^ 2 := by
          calc
            (s x) ^ 2 - (x + σ) ^ 2 = u x - (x + σ) ^ 2 := by
              simp [hsq']
            _ = τ ^ 2 := by simp [u]
        have hA' :
            c *
                (sinv x + (x + σ) * (-(2 * (x + σ) / (2 * s x)) / (s x) ^ 2)) =
          1 / (s x) ^ 3 := by
          have hspos : 0 < s x := by
            exact Real.sqrt_pos.mpr hpos
          have hsne : s x ≠ 0 := ne_of_gt hspos
          have htwo : (2 * (x + σ)) / (2 * s x) = (x + σ) / s x := by
            field_simp [hsne]
          simp [sinv, c, div_eq_mul_inv, mul_comm, mul_assoc]
          field_simp [hτ2, hsne]
          nlinarith [hnum]
        have hg' : g' x = 1 / (s x) ^ 3 := by
          have hspos : 0 ≤ s x := by exact Real.sqrt_nonneg _
          calc
            g' x = 1 / ((x + σ) ^ 2 + τ ^ 2) ^ (3 / 2 : ℝ) := rfl
            _ = 1 / (u x) ^ (3 / 2 : ℝ) := by simp [u]
            _ = 1 / ((s x) ^ 2) ^ (3 / 2 : ℝ) := by simp [hsq']
            _ = 1 / (s x) ^ (2 * (3 / 2 : ℝ)) := by
              have h := (Real.rpow_mul (x := s x) hspos 2 (3 / 2 : ℝ))
              -- h : (s x)^(2*(3/2)) = ((s x)^2)^(3/2)
              simpa [mul_comm] using h.symm
            _ = 1 / (s x) ^ (3 : ℝ) := by ring_nf
            _ = 1 / (s x) ^ 3 := by simp
        simpa [hg'] using hA'
      simpa [hA] using h7
    have g'pos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g' x := by
      intro x hx
      have hsq : 0 ≤ (x + σ) ^ 2 + τ ^ 2 := by
        have h1 : 0 ≤ (x + σ) ^ 2 := by nlinarith
        have h2 : 0 ≤ τ ^ 2 := by nlinarith
        exact add_nonneg h1 h2
      have hpow : 0 ≤ ((x + σ) ^ 2 + τ ^ 2) ^ (3 / 2 : ℝ) := by
        exact Real.rpow_nonneg hsq _
      exact one_div_nonneg.mpr hpow
    have hlim_add : Tendsto (fun x => x + σ) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      refine (eventually_atTop.2 ?_)
      refine ⟨b - σ, ?_⟩
      intro x hx
      linarith
    have hlim_sq : Tendsto (fun x => (x + σ) ^ 2) atTop atTop := by
      have hpow : Tendsto (fun y : ℝ => y ^ 2) atTop atTop := by
        exact tendsto_pow_atTop (α := ℝ) (n := 2) (by simp)
      exact hpow.comp hlim_add
    have hlim_inv : Tendsto (fun x => 1 / (x + σ) ^ 2) atTop (𝓝 (0 : ℝ)) := by
      have hlim_inv' : Tendsto (fun x => ((x + σ) ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) :=
        tendsto_inv_atTop_zero.comp hlim_sq
      simpa [one_div] using hlim_inv'
    let term : ℝ → ℝ := fun x => (s x * (s x + (x + σ)))⁻¹
    have hlim_den : Tendsto (fun x => s x * (s x + (x + σ))) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      have hlim_sq' := (tendsto_atTop.1 hlim_sq) b
      have hx0event : ∀ᶠ x in atTop, (0 : ℝ) ≤ x := by
        refine (eventually_atTop.2 ?_)
        refine ⟨0, ?_⟩
        intro x hx
        exact hx
      filter_upwards [hlim_sq', hx0event] with x hx hx0
      have hspos : 0 ≤ s x := by exact Real.sqrt_nonneg _
      have hxpos : 0 ≤ x + σ := by nlinarith [hσ, hx0]
      have hsq : 0 ≤ u x := by
        have h1 : 0 ≤ (x + σ) ^ 2 := by nlinarith
        have h2 : 0 ≤ τ ^ 2 := by nlinarith
        have : 0 ≤ (x + σ) ^ 2 + τ ^ 2 := add_nonneg h1 h2
        simpa [u] using this
      have hsq' : (s x) ^ 2 = u x := by
        simpa [s] using (Real.sq_sqrt hsq)
      have hbig :
          (x + σ) ^ 2 ≤ s x * (s x + (x + σ)) := by
        have hbig2 : u x = (x + σ) ^ 2 + τ ^ 2 := by simp [u]
        have hbig3 : (x + σ) ^ 2 ≤ u x := by
          have ht : 0 ≤ τ ^ 2 := by nlinarith
          nlinarith [hbig2, ht]
        calc
          s x * (s x + (x + σ)) = (s x) ^ 2 + s x * (x + σ) := by ring_nf
          _ ≥ (s x) ^ 2 := by nlinarith [mul_nonneg hspos hxpos]
          _ = u x := by simp [hsq']
          _ ≥ (x + σ) ^ 2 := hbig3
      exact le_trans hx hbig
    have hlim_term : Tendsto term atTop (𝓝 (0 : ℝ)) := by
      change Tendsto (fun x => (s x * (s x + (x + σ)))⁻¹) atTop (𝓝 (0 : ℝ))
      exact tendsto_inv_atTop_zero.comp hlim_den
    have hlim_ratio :
        Tendsto (fun x => (x + σ) / s x) atTop (𝓝 (1 : ℝ)) := by
      have hdec :
          ∀ x, 1 - (x + σ) / s x = τ ^ 2 * term x := by
        intro x
        have hsq : 0 ≤ u x := by
          have h1 : 0 ≤ (x + σ) ^ 2 := by nlinarith
          have h2 : 0 ≤ τ ^ 2 := by nlinarith
          have : 0 ≤ (x + σ) ^ 2 + τ ^ 2 := add_nonneg h1 h2
          simpa [u] using this
        have hsq' : (s x) ^ 2 = u x := by
          simpa [s] using (Real.sq_sqrt hsq)
        have hnum : (s x) ^ 2 - (x + σ) ^ 2 = τ ^ 2 := by
          calc
            (s x) ^ 2 - (x + σ) ^ 2 = u x - (x + σ) ^ 2 := by
              simp [hsq']
            _ = τ ^ 2 := by simp [u]
        have hspos : 0 < s x := by
          have ht' : τ ≠ 0 := hτ
          have ht : 0 < τ ^ 2 := by
            have hmul : 0 < τ * τ := by simpa using mul_self_pos.mpr ht'
            simpa [pow_two] using hmul
          have h1 : 0 ≤ (x + σ) ^ 2 := by nlinarith
          have : 0 < (x + σ) ^ 2 + τ ^ 2 := add_pos_of_nonneg_of_pos h1 ht
          have hpos' : 0 < u x := by simpa [u] using this
          exact Real.sqrt_pos.mpr hpos'
        have hsne : s x ≠ 0 := ne_of_gt hspos
        have hsumne : s x + (x + σ) ≠ 0 := by
          intro hsum
          have hs : s x = -(x + σ) := by linarith
          have hsqeq : (s x) ^ 2 = (x + σ) ^ 2 := by nlinarith [hs]
          have htz : τ ^ 2 = 0 := by nlinarith [hnum, hsqeq]
          exact hτ (by nlinarith [htz])
        calc
          1 - (x + σ) / s x = (s x - (x + σ)) / s x := by
            field_simp [hsne]
          _ = ((s x) ^ 2 - (x + σ) ^ 2) / (s x * (s x + (x + σ))) := by
            field_simp [hsne, hsumne]
            ring_nf
          _ = τ ^ 2 * term x := by
            simp [term, hnum, div_eq_mul_inv, mul_comm]
      have hlim_diff : Tendsto (fun x => 1 - (x + σ) / s x) atTop (𝓝 (0 : ℝ)) := by
        have hconst : Tendsto (fun _ : ℝ => τ ^ 2) atTop (𝓝 (τ ^ 2 : ℝ)) :=
          tendsto_const_nhds
        have hmul : Tendsto (fun x => τ ^ 2 * term x) atTop (𝓝 (0 : ℝ)) := by
          simpa using (hconst.mul hlim_term)
        simpa [hdec] using hmul
      have hlim_ratio' :
          Tendsto (fun x => (1 : ℝ) + (-(1 - (x + σ) / s x))) atTop (𝓝 (1 : ℝ)) := by
        have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
          tendsto_const_nhds
        simpa using (hconst.add hlim_diff.neg)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlim_ratio'
    have hlim : Tendsto g atTop (𝓝 (1 / τ ^ 2 : ℝ)) := by
      have hconst : Tendsto (fun _ : ℝ => (1 / τ ^ 2 : ℝ)) atTop (𝓝 (1 / τ ^ 2 : ℝ)) :=
        tendsto_const_nhds
      have hmul : Tendsto (fun x => (1 / τ ^ 2 : ℝ) * ((x + σ) / s x)) atTop
          (𝓝 (1 / τ ^ 2 : ℝ)) := by
        simpa [c, one_div] using (hconst.mul hlim_ratio)
      simpa [g, c, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hmain :=
      integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ)) hderiv g'pos hlim
    have hF0 : g 0 = c * (σ / s 0) := by
      simp [g, c]
    have hsq0 : s 0 = Real.sqrt (σ ^ 2 + τ ^ 2) := by
      simp [s, u]
    have hfinal :
        (1 / τ ^ 2 : ℝ) - (1 / τ ^ 2 : ℝ) * (σ / Real.sqrt (σ ^ 2 + τ ^ 2)) =
          1 / (Real.sqrt (σ ^ 2 + τ ^ 2) * (Real.sqrt (σ ^ 2 + τ ^ 2) + σ)) := by
      have hsq : 0 ≤ σ ^ 2 + τ ^ 2 := by nlinarith
      have hsq' : (Real.sqrt (σ ^ 2 + τ ^ 2)) ^ 2 = σ ^ 2 + τ ^ 2 := by
        simpa using (Real.sq_sqrt hsq)
      have hpos : 0 < Real.sqrt (σ ^ 2 + τ ^ 2) := by
        have hpos' : 0 < σ ^ 2 + τ ^ 2 := by nlinarith [hσ]
        simpa using (Real.sqrt_pos.mpr hpos')
      have hden : Real.sqrt (σ ^ 2 + τ ^ 2) + σ ≠ 0 := by nlinarith [hpos, hσ]
      field_simp [hτ2, hden]
      nlinarith [hsq']
    calc
      ∫ x in Set.Ioi (0 : ℝ), 1 / ((x + σ) ^ 2 + τ ^ 2) ^ (3 / 2 : ℝ)
          = ∫ x in Set.Ioi (0 : ℝ), g' x := by
        rfl
      _ = (1 / τ ^ 2 : ℝ) - g 0 := hmain
      _ = (1 / τ ^ 2 : ℝ) - (1 / τ ^ 2 : ℝ) * (σ / Real.sqrt (σ ^ 2 + τ ^ 2)) := by
        simp [hF0, hsq0, c, one_div]
      _ = 1 / (Real.sqrt (σ ^ 2 + τ ^ 2) * (Real.sqrt (σ ^ 2 + τ ^ 2) + σ)) := hfinal

lemma integral_kernel_bound (σ τ : ℝ) (hσ : 0 < σ) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / ((x + σ) ^ 2 + τ ^ 2) ^ (3 / 2 : ℝ) ≤
      1 / (σ ^ 2 + τ ^ 2) := by
  have h := integral_kernel_eq σ τ hσ
  have hpos : 0 < Real.sqrt (σ ^ 2 + τ ^ 2) := by
    have hsq : 0 < σ ^ 2 + τ ^ 2 := by nlinarith
    simpa using Real.sqrt_pos.mpr hsq
  have hle : 1 / (Real.sqrt (σ ^ 2 + τ ^ 2) * (Real.sqrt (σ ^ 2 + τ ^ 2) + σ)) ≤
      1 / (Real.sqrt (σ ^ 2 + τ ^ 2) ^ 2) := by
    have hsum : Real.sqrt (σ ^ 2 + τ ^ 2) ≤
        Real.sqrt (σ ^ 2 + τ ^ 2) + σ := by nlinarith [hσ.le]
    have hpos2 : 0 < Real.sqrt (σ ^ 2 + τ ^ 2) * (Real.sqrt (σ ^ 2 + τ ^ 2) + σ) := by
      nlinarith [hpos]
    have hpos3 : 0 < Real.sqrt (σ ^ 2 + τ ^ 2) ^ 2 := by
      nlinarith [hpos]
    exact one_div_le_one_div_of_le hpos3 (by
      nlinarith [hsum])
  have hsq : Real.sqrt (σ ^ 2 + τ ^ 2) ^ 2 = σ ^ 2 + τ ^ 2 := by
    have hsq : 0 ≤ σ ^ 2 + τ ^ 2 := by nlinarith
    simpa using (Real.sq_sqrt hsq)
  calc
    ∫ x in Set.Ioi (0 : ℝ), 1 / ((x + σ) ^ 2 + τ ^ 2) ^ (3 / 2 : ℝ)
        = 1 / (Real.sqrt (σ ^ 2 + τ ^ 2) * (Real.sqrt (σ ^ 2 + τ ^ 2) + σ)) := h
    _ ≤ 1 / (Real.sqrt (σ ^ 2 + τ ^ 2) ^ 2) := hle
    _ = 1 / (σ ^ 2 + τ ^ 2) := by simp [hsq]

/-- Pointwise right-half-plane domination for the order-15 kernel that appears
in the first omitted term of the M6 digamma Euler-Maclaurin remainder. -/
lemma kernel_norm_pow15_le_re (z : ℂ) (hz : 0 < z.re)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    1 / ‖(x : ℂ) + z‖ ^ 15 ≤ 1 / (x + z.re) ^ 15 := by
  have hxpos : 0 < x := hx
  have hxre_pos : 0 < x + z.re := by
    linarith [hxpos, hz]
  have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
  have hnorm_ge : x + z.re ≤ ‖(x : ℂ) + z‖ := by
    have h := Complex.abs_re_le_norm ((x : ℂ) + z)
    have hre : (((x : ℂ) + z).re) = x + z.re := by
      simp
    have habs : |(((x : ℂ) + z).re)| = x + z.re := by
      rw [hre, abs_of_nonneg hxre_nonneg]
    rwa [habs] at h
  have hpow :
      (x + z.re) ^ 15 ≤ ‖(x : ℂ) + z‖ ^ 15 :=
    pow_le_pow_left₀ hxre_nonneg hnorm_ge 15
  exact one_div_le_one_div_of_le (pow_pos hxre_pos 15) hpow

/-- Integrability of the order-15 kernel used by the M6 first-omitted
Euler-Maclaurin remainder. -/
lemma integrable_kernel_norm_pow15 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 15))
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hdomOn :
      IntegrableOn (fun x : ℝ => (x + z.re) ^ (-15 : ℝ))
        (Set.Ioi (0 : ℝ)) := by
    have hlt : (-15 : ℝ) < -1 := by norm_num
    have hc : -z.re < (0 : ℝ) := by linarith [hz]
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-15 : ℝ))
        (c := (0 : ℝ)) (m := z.re) hlt hc)
  have hdomOn' :
      IntegrableOn (fun x : ℝ => 1 / (x + z.re) ^ 15)
        (Set.Ioi (0 : ℝ)) := by
    refine hdomOn.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hxre_pos : 0 < x + z.re := by
      linarith [hxpos, hz]
    have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
    calc
      (x + z.re) ^ (-15 : ℝ)
          = ((x + z.re) ^ (15 : ℝ))⁻¹ := by
              simpa using (rpow_neg_eq_inv_rpow (x + z.re) (15 : ℝ))
      _ = ((x + z.re) ^ 15)⁻¹ := by
              simp [Real.rpow_natCast, hxre_nonneg]
      _ = 1 / (x + z.re) ^ 15 := by
              simp [one_div]
  have hdom :
      Integrable (fun x : ℝ => 1 / (x + z.re) ^ 15)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hdomOn'
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => 1 / ‖(x : ℂ) + z‖ ^ 15)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hcoe : Measurable (fun x : ℝ => (x : ℂ)) :=
      Complex.measurable_ofReal
    have hadd : Measurable (fun x : ℝ => (x : ℂ) + z) :=
      hcoe.add measurable_const
    have hnorm : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖) :=
      hadd.norm
    have hpow : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖ ^ 15) :=
      hnorm.pow_const 15
    have hinv : Measurable (fun x : ℝ => (‖(x : ℂ) + z‖ ^ 15)⁻¹) :=
      hpow.inv
    simpa [one_div] using hinv.aestronglyMeasurable
  have hbound :
      ∀ᵐ x : ℝ ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(1 / ‖(x : ℂ) + z‖ ^ 15 : ℝ)‖ ≤
          1 / (x + z.re) ^ 15 := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    have hnonneg : 0 ≤ (1 / ‖(x : ℂ) + z‖ ^ 15 : ℝ) := by
      exact one_div_nonneg.mpr (pow_nonneg (norm_nonneg _) 15)
    have hnorm_abs :
        ‖(1 / ‖(x : ℂ) + z‖ ^ 15 : ℝ)‖ =
          1 / ‖(x : ℂ) + z‖ ^ 15 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [hnorm_abs] using kernel_norm_pow15_le_re z hz hx
  exact Integrable.mono' hdom hmeas hbound

/-- Exact real tail integral for the order-15 right-half-plane majorant. -/
lemma integral_one_div_add_pos_pow15 (a : ℝ) (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / (x + a) ^ 15 =
      1 / (14 * a ^ 14) := by
  let g : ℝ → ℝ := fun x => -(1 / 14 : ℝ) * (x + a) ^ (-14 : ℝ)
  let g' : ℝ → ℝ := fun x => 1 / (x + a) ^ 15
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (g' x) x := by
    intro x hx
    have hx0 : 0 ≤ x := by simpa [Set.mem_Ici] using hx
    have hxapos : 0 < x + a := by nlinarith [hx0, ha]
    have hxane : x + a ≠ 0 := ne_of_gt hxapos
    have hlin : HasDerivAt (fun y : ℝ => y + a) 1 x := by
      simpa using (hasDerivAt_id x).add_const a
    have hrpow :
        HasDerivAt (fun y : ℝ => (y + a) ^ (-14 : ℝ))
          ((-14 : ℝ) * (x + a) ^ ((-14 : ℝ) - 1)) x := by
      simpa using
        (Real.hasDerivAt_rpow_const (x := x + a) (p := (-14 : ℝ))
          (Or.inl hxane)).comp x hlin
    have hmul := hrpow.const_mul (-(1 / 14 : ℝ))
    have hderiv_value :
        (x + a) ^ ((-14 : ℝ) - 1) = g' x := by
      rw [show ((-14 : ℝ) - 1) = (-15 : ℝ) by norm_num]
      have hxanonneg : 0 ≤ x + a := le_of_lt hxapos
      calc
        (x + a) ^ (-15 : ℝ)
            = ((x + a) ^ (15 : ℝ))⁻¹ := by
              simpa using (rpow_neg_eq_inv_rpow (x + a) (15 : ℝ))
        _ = ((x + a) ^ 15)⁻¹ := by
              simp [Real.rpow_natCast, hxanonneg]
        _ = 1 / (x + a) ^ 15 := by
              simp [one_div]
    simpa [g, hderiv_value] using hmul
  have g'pos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ g' x := by
    intro x hx
    have hxpos : 0 < x := hx
    have hxapos : 0 < x + a := by nlinarith [hxpos, ha]
    dsimp [g']
    exact one_div_nonneg.mpr (pow_nonneg (le_of_lt hxapos) 15)
  have hlim : Tendsto g atTop (𝓝 (0 : ℝ)) := by
    have hshift : Tendsto (fun x : ℝ => x + a) atTop atTop :=
      tendsto_atTop_add_const_right atTop a tendsto_id
    have hrpow : Tendsto (fun x : ℝ => (x + a) ^ (-14 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 14)).comp hshift
    simpa [g] using hrpow.const_mul (-(1 / 14 : ℝ))
  have hmain :=
    integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ)) hderiv g'pos hlim
  calc
    ∫ x in Set.Ioi (0 : ℝ), 1 / (x + a) ^ 15 =
        ∫ x in Set.Ioi (0 : ℝ), g' x := by rfl
    _ = (0 : ℝ) - g 0 := hmain
    _ = 1 / (14 * a ^ 14) := by
          dsimp [g]
          rw [show (0 : ℝ) + a = a by ring]
          rw [rpow_neg_eq_inv_rpow a (14 : ℝ)]
          simp [Real.rpow_natCast, le_of_lt ha, one_div]
          field_simp [show (14 : ℝ) ≠ 0 by norm_num,
            pow_ne_zero 14 (ne_of_gt ha)]

/-- Integral bound for the order-15 complex kernel by the right-half-plane
real majorant. -/
lemma integral_kernel_norm_pow15_le_re (z : ℂ) (hz : 0 < z.re) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / ‖(x : ℂ) + z‖ ^ 15 ≤
      1 / (14 * z.re ^ 14) := by
  have hkernel : Integrable (fun x : ℝ => 1 / ‖(x : ℂ) + z‖ ^ 15)
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    integrable_kernel_norm_pow15 z hz
  have hdomOn :
      IntegrableOn (fun x : ℝ => (x + z.re) ^ (-15 : ℝ))
        (Set.Ioi (0 : ℝ)) := by
    have hlt : (-15 : ℝ) < -1 := by norm_num
    have hc : -z.re < (0 : ℝ) := by linarith [hz]
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-15 : ℝ))
        (c := (0 : ℝ)) (m := z.re) hlt hc)
  have hdomOn' :
      IntegrableOn (fun x : ℝ => 1 / (x + z.re) ^ 15)
        (Set.Ioi (0 : ℝ)) := by
    refine hdomOn.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hxre_pos : 0 < x + z.re := by
      linarith [hxpos, hz]
    have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
    calc
      (x + z.re) ^ (-15 : ℝ)
          = ((x + z.re) ^ (15 : ℝ))⁻¹ := by
              simpa using (rpow_neg_eq_inv_rpow (x + z.re) (15 : ℝ))
      _ = ((x + z.re) ^ 15)⁻¹ := by
              simp [Real.rpow_natCast, hxre_nonneg]
      _ = 1 / (x + z.re) ^ 15 := by
              simp [one_div]
  have hdom : Integrable (fun x : ℝ => 1 / (x + z.re) ^ 15)
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hdomOn'
  have hmono :
      ∫ x in Set.Ioi (0 : ℝ), 1 / ‖(x : ℂ) + z‖ ^ 15 ≤
        ∫ x in Set.Ioi (0 : ℝ), 1 / (x + z.re) ^ 15 := by
    refine integral_mono_ae hkernel hdom ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    exact kernel_norm_pow15_le_re z hz hx
  calc
    ∫ x in Set.Ioi (0 : ℝ), 1 / ‖(x : ℂ) + z‖ ^ 15
        ≤ ∫ x in Set.Ioi (0 : ℝ), 1 / (x + z.re) ^ 15 := hmono
    _ = 1 / (14 * z.re ^ 14) := integral_one_div_add_pos_pow15 z.re hz

/-- The `m = 6` Bernoulli asymptotic main term for the digamma function.

The next Step33 endpoint proof only needs a theorem bounding the difference
between `Q3.digamma z` and this expression by the standard order-15
Euler-Maclaurin remainder. -/
def digammaM6AsymptoticMain (z : ℂ) : ℂ :=
  Complex.log z
    - ((1 : ℂ) / (2 : ℂ)) * z⁻¹
    - ((1 : ℂ) / (12 : ℂ)) * (z ^ 2)⁻¹
    + ((1 : ℂ) / (120 : ℂ)) * (z ^ 4)⁻¹
    - ((1 : ℂ) / (252 : ℂ)) * (z ^ 6)⁻¹
    + ((1 : ℂ) / (240 : ℂ)) * (z ^ 8)⁻¹
    - ((1 : ℂ) / (132 : ℂ)) * (z ^ 10)⁻¹
    + (((691 : ℂ) / (32760 : ℂ)) * (z ^ 12)⁻¹)

/-- The standard order-15 integral-remainder estimate for the `m = 6`
digamma asymptotic main term.  This is the remaining analytic source theorem
for the current Step33A.1-A endpoint route. -/
def digammaM6IntegralRemainderBound (z : ℂ) : Prop :=
  ‖Q3.digamma z - digammaM6AsymptoticMain z‖ ≤
    ((7 : ℝ) / (6 : ℝ)) *
      ∫ x in Set.Ioi (0 : ℝ), 1 / ‖(x : ℂ) + z‖ ^ 15

/-- Once the `m = 6` digamma remainder has the standard order-15 integral
form, the first-omitted bound in terms of `z.re` follows from the checked
kernel majorant. -/
lemma digamma_m6_re_first_omitted_bound_of_integral_remainder
    (z : ℂ) (hz : 0 < z.re)
    (hIntegral : digammaM6IntegralRemainderBound z) :
    ‖Q3.digamma z - digammaM6AsymptoticMain z‖ ≤
      ((1 : ℝ) / (12 : ℝ)) * (z.re⁻¹) ^ 14 := by
  have hIntegralBound :
      ∫ x in Set.Ioi (0 : ℝ), 1 / ‖(x : ℂ) + z‖ ^ 15 ≤
        1 / (14 * z.re ^ 14) :=
    integral_kernel_norm_pow15_le_re z hz
  have hScaled :
      ((7 : ℝ) / (6 : ℝ)) *
          ∫ x in Set.Ioi (0 : ℝ), 1 / ‖(x : ℂ) + z‖ ^ 15 ≤
        ((7 : ℝ) / (6 : ℝ)) * (1 / (14 * z.re ^ 14)) := by
    exact mul_le_mul_of_nonneg_left hIntegralBound (by norm_num)
  have hScalar :
      ((7 : ℝ) / (6 : ℝ)) * (1 / (14 * z.re ^ 14)) =
        ((1 : ℝ) / (12 : ℝ)) * (z.re⁻¹) ^ 14 := by
    rw [inv_pow]
    field_simp [show (6 : ℝ) ≠ 0 by norm_num,
      show (7 : ℝ) ≠ 0 by norm_num,
      show (12 : ℝ) ≠ 0 by norm_num,
      show (14 : ℝ) ≠ 0 by norm_num,
      pow_ne_zero 14 (ne_of_gt hz)]
    ring
  exact hIntegral.trans (hScaled.trans_eq hScalar)

/-- The one-step defect of the `m = 6` asymptotic main under the digamma
recurrence.  This is the finite algebraic object left after shifting the
digamma remainder to the right. -/
def digammaM6StepDefect (z : ℂ) : ℂ :=
  digammaM6AsymptoticMain (z + 1) - digammaM6AsymptoticMain z - z⁻¹

/-- Finite telescoping identity for the `m = 6` main-term step defects. -/
lemma digammaM6StepDefect_sum_range (z : ℂ) (N : ℕ) :
    (Finset.range N).sum
        (fun n : ℕ => digammaM6StepDefect (z + (n : ℂ))) =
      digammaM6AsymptoticMain (z + (N : ℂ)) -
        digammaM6AsymptoticMain z -
        (Finset.range N).sum (fun n : ℕ => (z + (n : ℂ))⁻¹) := by
  induction N with
  | zero =>
      simp [digammaM6StepDefect]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have harg :
          z + (N : ℂ) + 1 = z + (((N + 1 : ℕ) : ℂ)) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      rw [digammaM6StepDefect, harg, Finset.sum_range_succ]
      abel

/-- Finite right-shift receiver for the `m = 6` digamma remainder.  It reduces
the remainder at `z` to the remainder at `z + N` plus a finite sum of checked
main-term step defects. -/
lemma digamma_m6_remainder_finite_telescope
    (z : ℂ) (N : ℕ) (hz : 0 < z.re) :
    Q3.digamma z - digammaM6AsymptoticMain z =
      Q3.digamma (z + (N : ℂ)) -
        digammaM6AsymptoticMain (z + (N : ℂ)) +
        (Finset.range N).sum
          (fun n : ℕ => digammaM6StepDefect (z + (n : ℂ))) := by
  have hrec := digamma_add_nat_of_re_pos z N hz
  have hpsi :
      Q3.digamma z =
        Q3.digamma (z + (N : ℂ)) -
          (Finset.range N).sum (fun n : ℕ => (z + (n : ℂ))⁻¹) :=
    eq_sub_of_add_eq hrec.symm
  have hdefects := digammaM6StepDefect_sum_range z N
  rw [hpsi, hdefects]
  abel

/-- Norm receiver for the finite right-shift M6 remainder identity.  A bound
for the shifted remainder plus a bound for the finite step-defect sum gives a
bound at the original point. -/
lemma digamma_m6_remainder_norm_le_of_finite_telescope
    (z : ℂ) (N : ℕ) (hz : 0 < z.re) (shiftRad defectRad : ℝ)
    (hShift :
      ‖Q3.digamma (z + (N : ℂ)) -
          digammaM6AsymptoticMain (z + (N : ℂ))‖ ≤ shiftRad)
    (hDefects :
      (Finset.range N).sum
          (fun n : ℕ => ‖digammaM6StepDefect (z + (n : ℂ))‖) ≤ defectRad) :
    ‖Q3.digamma z - digammaM6AsymptoticMain z‖ ≤
      shiftRad + defectRad := by
  rw [digamma_m6_remainder_finite_telescope z N hz]
  have hsumNorm :
      ‖(Finset.range N).sum
          (fun n : ℕ => digammaM6StepDefect (z + (n : ℂ)))‖ ≤
        (Finset.range N).sum
          (fun n : ℕ => ‖digammaM6StepDefect (z + (n : ℂ))‖) := by
    exact norm_sum_le _ _
  calc
    ‖Q3.digamma (z + (N : ℂ)) -
          digammaM6AsymptoticMain (z + (N : ℂ)) +
        (Finset.range N).sum
          (fun n : ℕ => digammaM6StepDefect (z + (n : ℂ)))‖
        ≤ ‖Q3.digamma (z + (N : ℂ)) -
            digammaM6AsymptoticMain (z + (N : ℂ))‖ +
          ‖(Finset.range N).sum
            (fun n : ℕ => digammaM6StepDefect (z + (n : ℂ)))‖ :=
            norm_add_le _ _
    _ ≤ shiftRad +
          (Finset.range N).sum
            (fun n : ℕ => ‖digammaM6StepDefect (z + (n : ℂ))‖) :=
            add_le_add hShift hsumNorm
    _ ≤ shiftRad + defectRad :=
            add_le_add (le_refl shiftRad) hDefects

/-- Finite-telescope receiver for the standard `m = 6` integral-remainder
surface.  This keeps the analytic source theorem local: it suffices to bound a
far-right remainder and the explicit finite M6 step-defect sum. -/
lemma digammaM6IntegralRemainderBound_of_finite_telescope
    (z : ℂ) (N : ℕ) (hz : 0 < z.re) (shiftRad defectRad : ℝ)
    (hShift :
      ‖Q3.digamma (z + (N : ℂ)) -
          digammaM6AsymptoticMain (z + (N : ℂ))‖ ≤ shiftRad)
    (hDefects :
      (Finset.range N).sum
          (fun n : ℕ => ‖digammaM6StepDefect (z + (n : ℂ))‖) ≤ defectRad)
    (hTotal :
      shiftRad + defectRad ≤
        ((7 : ℝ) / (6 : ℝ)) *
          ∫ x in Set.Ioi (0 : ℝ), 1 / ‖(x : ℂ) + z‖ ^ 15) :
    digammaM6IntegralRemainderBound z := by
  exact
    (digamma_m6_remainder_norm_le_of_finite_telescope
      z N hz shiftRad defectRad hShift hDefects).trans hTotal

lemma integrable_kernel_norm (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 3))
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hnorm_sq :
      ∀ x : ℝ, ‖(x : ℂ) + z‖ ^ 2 = (x + z.re) ^ 2 + z.im ^ 2 := by
    intro x
    have h' : Complex.normSq ((x : ℂ) + z) =
        (x + z.re) * (x + z.re) + z.im * z.im := by
      simp [Complex.normSq_apply]
    have h'' : ‖(x : ℂ) + z‖ ^ 2 = Complex.normSq ((x : ℂ) + z) := by
      simpa using (Complex.sq_norm ((x : ℂ) + z))
    simpa [pow_two] using (h''.trans h')
  have hpow :
      ∀ x : ℝ, (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ) = ‖(x : ℂ) + z‖ ^ 3 := by
    intro x
    have hbase : 0 ≤ ‖(x : ℂ) + z‖ ^ 2 := by positivity
    calc
      (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ)
          = (‖(x : ℂ) + z‖ ^ 2) ^ ((1 / 2 : ℝ) * (3 : ℝ)) := by ring_nf
      _ = ((‖(x : ℂ) + z‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
            simpa using
              (Real.rpow_mul (x := ‖(x : ℂ) + z‖ ^ 2) hbase (1 / 2 : ℝ) (3 : ℝ))
      _ = (Real.sqrt (‖(x : ℂ) + z‖ ^ 2)) ^ (3 : ℝ) := by
            simp [Real.sqrt_eq_rpow]
      _ = ‖(x : ℂ) + z‖ ^ (3 : ℝ) := by
            simp
      _ = ‖(x : ℂ) + z‖ ^ 3 := by
            simp
  have hrewrite :
      ∀ x : ℝ,
        1 / ‖(x : ℂ) + z‖ ^ 3 =
          1 / ((x + z.re) ^ 2 + z.im ^ 2) ^ (3 / 2 : ℝ) := by
    intro x
    calc
      1 / ‖(x : ℂ) + z‖ ^ 3
          = 1 / (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ) := by
              simp [hpow x]
      _ = 1 / ((x + z.re) ^ 2 + z.im ^ 2) ^ (3 / 2 : ℝ) := by
            simp [hnorm_sq x]
  have hkernel_eq :
      ∫ x in Set.Ioi (0 : ℝ), (1 / ‖(x : ℂ) + z‖ ^ 3) =
        1 / (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) := by
    have hbound := integral_kernel_eq (σ := z.re) (τ := z.im) hz
    simpa [hrewrite] using hbound
  have hkernel_ne :
      (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) ≠ 0 := by
    have hpos : 0 < Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      have hsq : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [hz]
      simpa using Real.sqrt_pos.mpr hsq
    have hpos2 : 0 < Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re := by
      nlinarith [hpos, hz]
    nlinarith [hpos, hpos2]
  set c : ℝ :=
    1 / (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re))
  have hc : c ≠ 0 := by
    have : (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) ≠ 0 :=
      hkernel_ne
    simpa [c] using (one_div_ne_zero this)
  have hscaled :
      ∫ x in Set.Ioi (0 : ℝ), (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) = (1 : ℝ) := by
    calc
      ∫ x in Set.Ioi (0 : ℝ), (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3)
          = (1 / c : ℝ) * ∫ x in Set.Ioi (0 : ℝ), (1 / ‖(x : ℂ) + z‖ ^ 3) := by
              simp [MeasureTheory.integral_const_mul]
      _ = (1 / c : ℝ) * c := by
            simpa using (congrArg (fun t => (1 / c : ℝ) * t) hkernel_eq)
      _ = (1 : ℝ) := by
            field_simp [hc]
  have hscaled_int :
      Integrable (fun x : ℝ => (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    exact MeasureTheory.integrable_of_integral_eq_one hscaled
  have hgi :
      Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 3))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hgi' := hscaled_int.smul c
    refine hgi'.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have :
        c * ((1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3)) =
          (1 / ‖(x : ℂ) + z‖ ^ 3) := by
      field_simp [hc, mul_comm, mul_left_comm, mul_assoc]
    simpa [Pi.smul_apply, smul_eq_mul] using this
  exact hgi

lemma integrable_bernoulli2Diff_div (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hkernel :
      Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 3))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    integrable_kernel_norm z hz
  have hkernel' :
      Integrable (fun x : ℝ => (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    hkernel.const_mul (1 / 4 : ℝ)
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hmeas : Measurable (fun x => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) := by
      have hcoe : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
      have h_add : Measurable (fun x : ℝ => (x : ℂ) + z) := hcoe.add measurable_const
      have h_pow : Measurable (fun x : ℝ => ((x : ℂ) + z) ^ 3) := h_add.pow_const 3
      have h_num : Measurable (fun x : ℝ => (bernoulli2Diff x : ℂ)) :=
        (Complex.measurable_ofReal.comp measurable_bernoulli2Diff)
      exact h_num.div h_pow
    simpa using hmeas.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3‖ ≤
          (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hnorm_pow : ‖(x + z : ℂ) ^ 3‖ = ‖(x + z : ℂ)‖ ^ 3 := by
      simp [norm_pow]
    have hpos : 0 ≤ ‖(x : ℂ) + z‖ ^ 3 := by positivity
    calc
      ‖(bernoulli2Diff x : ℂ) / (x + z) ^ 3‖
          = ‖(bernoulli2Diff x : ℂ)‖ / ‖(x + z : ℂ) ^ 3‖ := by
            simp
      _ = ‖(bernoulli2Diff x : ℂ)‖ / ‖(x : ℂ) + z‖ ^ 3 := by
            simp [hnorm_pow]
      _ ≤ (1 / 4 : ℝ) / ‖(x : ℂ) + z‖ ^ 3 := by
            exact (div_le_div_of_nonneg_right (bernoulli2Diff_norm_le x) hpos)
      _ = (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
            field_simp
  exact Integrable.mono' hkernel' hmeas hbound

/-- Pointwise right-half-plane domination for the order-5 kernel used by the
B4/power-5 Stieltjes tail ledger. -/
lemma kernel_norm_pow5_le_re (z : ℂ) (hz : 0 < z.re)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    1 / ‖(x : ℂ) + z‖ ^ 5 ≤ 1 / (x + z.re) ^ 5 := by
  have hxpos : 0 < x := hx
  have hxre_pos : 0 < x + z.re := by
    linarith [hxpos, hz]
  have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
  have hnorm_ge : x + z.re ≤ ‖(x : ℂ) + z‖ := by
    have h := Complex.abs_re_le_norm ((x : ℂ) + z)
    have hre : (((x : ℂ) + z).re) = x + z.re := by
      simp
    have habs : |(((x : ℂ) + z).re)| = x + z.re := by
      rw [hre, abs_of_nonneg hxre_nonneg]
    rwa [habs] at h
  have hpow :
      (x + z.re) ^ 5 ≤ ‖(x : ℂ) + z‖ ^ 5 :=
    pow_le_pow_left₀ hxre_nonneg hnorm_ge 5
  exact one_div_le_one_div_of_le (pow_pos hxre_pos 5) hpow

/-- Integrability of the order-5 kernel used by the B4/power-5 Stieltjes tail
ledger. -/
lemma integrable_kernel_norm_pow5 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 5))
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hdomOn :
      IntegrableOn (fun x : ℝ => (x + z.re) ^ (-5 : ℝ))
        (Set.Ioi (0 : ℝ)) := by
    have hlt : (-5 : ℝ) < -1 := by norm_num
    have hc : -z.re < (0 : ℝ) := by linarith [hz]
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-5 : ℝ))
        (c := (0 : ℝ)) (m := z.re) hlt hc)
  have hdomOn' :
      IntegrableOn (fun x : ℝ => 1 / (x + z.re) ^ 5)
        (Set.Ioi (0 : ℝ)) := by
    refine hdomOn.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hxre_pos : 0 < x + z.re := by
      linarith [hxpos, hz]
    have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
    calc
      (x + z.re) ^ (-5 : ℝ)
          = ((x + z.re) ^ (5 : ℝ))⁻¹ := by
              simpa using (rpow_neg_eq_inv_rpow (x + z.re) (5 : ℝ))
      _ = ((x + z.re) ^ 5)⁻¹ := by
              simp [Real.rpow_natCast, hxre_nonneg]
      _ = 1 / (x + z.re) ^ 5 := by
              simp [one_div]
  have hdom :
      Integrable (fun x : ℝ => 1 / (x + z.re) ^ 5)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hdomOn'
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => 1 / ‖(x : ℂ) + z‖ ^ 5)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hcoe : Measurable (fun x : ℝ => (x : ℂ)) :=
      Complex.measurable_ofReal
    have hadd : Measurable (fun x : ℝ => (x : ℂ) + z) :=
      hcoe.add measurable_const
    have hnorm : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖) :=
      hadd.norm
    have hpow : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖ ^ 5) :=
      hnorm.pow_const 5
    have hinv : Measurable (fun x : ℝ => (‖(x : ℂ) + z‖ ^ 5)⁻¹) :=
      hpow.inv
    simpa [one_div] using hinv.aestronglyMeasurable
  have hbound :
      ∀ᵐ x : ℝ ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(1 / ‖(x : ℂ) + z‖ ^ 5 : ℝ)‖ ≤
          1 / (x + z.re) ^ 5 := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    have hnonneg : 0 ≤ (1 / ‖(x : ℂ) + z‖ ^ 5 : ℝ) := by
      exact one_div_nonneg.mpr (pow_nonneg (norm_nonneg _) 5)
    have hnorm_abs :
        ‖(1 / ‖(x : ℂ) + z‖ ^ 5 : ℝ)‖ =
          1 / ‖(x : ℂ) + z‖ ^ 5 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [hnorm_abs] using kernel_norm_pow5_le_re z hz hx
  exact Integrable.mono' hdom hmeas hbound

lemma integrable_bernoulli4Diff_div_pow5 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hkernel :
      Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 5))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    integrable_kernel_norm_pow5 z hz
  have hkernel' :
      Integrable (fun x : ℝ => (1 / 30 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 5))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    hkernel.const_mul (1 / 30 : ℝ)
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hmeas : Measurable
        (fun x => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5) := by
      have hcoe : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
      have h_add : Measurable (fun x : ℝ => (x : ℂ) + z) := hcoe.add measurable_const
      have h_pow : Measurable (fun x : ℝ => ((x : ℂ) + z) ^ 5) := h_add.pow_const 5
      have h_num : Measurable (fun x : ℝ => (bernoulli4Diff x : ℂ)) :=
        (Complex.measurable_ofReal.comp measurable_bernoulli4Diff)
      exact h_num.div h_pow
    simpa using hmeas.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5‖ ≤
          (1 / 30 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 5) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hnorm_pow : ‖(x + z : ℂ) ^ 5‖ = ‖(x + z : ℂ)‖ ^ 5 := by
      simp [norm_pow]
    have hpos : 0 ≤ ‖(x : ℂ) + z‖ ^ 5 := by positivity
    calc
      ‖(bernoulli4Diff x : ℂ) / (x + z) ^ 5‖
          = ‖(bernoulli4Diff x : ℂ)‖ / ‖(x + z : ℂ) ^ 5‖ := by
            simp
      _ = ‖(bernoulli4Diff x : ℂ)‖ / ‖(x : ℂ) + z‖ ^ 5 := by
            simp [hnorm_pow]
      _ ≤ (1 / 30 : ℝ) / ‖(x : ℂ) + z‖ ^ 5 := by
            exact (div_le_div_of_nonneg_right (bernoulli4Diff_norm_le x) hpos)
      _ = (1 / 30 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 5) := by
            field_simp
  exact Integrable.mono' hkernel' hmeas hbound

/-- Pointwise right-half-plane domination for the order-7 kernel used by the
B6/power-7 Stieltjes tail ledger. -/
lemma kernel_norm_pow7_le_re (z : ℂ) (hz : 0 < z.re)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    1 / ‖(x : ℂ) + z‖ ^ 7 ≤ 1 / (x + z.re) ^ 7 := by
  have hxpos : 0 < x := hx
  have hxre_pos : 0 < x + z.re := by
    linarith [hxpos, hz]
  have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
  have hnorm_ge : x + z.re ≤ ‖(x : ℂ) + z‖ := by
    have h := Complex.abs_re_le_norm ((x : ℂ) + z)
    have hre : (((x : ℂ) + z).re) = x + z.re := by
      simp
    have habs : |(((x : ℂ) + z).re)| = x + z.re := by
      rw [hre, abs_of_nonneg hxre_nonneg]
    rwa [habs] at h
  have hpow :
      (x + z.re) ^ 7 ≤ ‖(x : ℂ) + z‖ ^ 7 :=
    pow_le_pow_left₀ hxre_nonneg hnorm_ge 7
  exact one_div_le_one_div_of_le (pow_pos hxre_pos 7) hpow

/-- Integrability of the order-7 kernel used by the B6/power-7 Stieltjes tail
ledger. -/
lemma integrable_kernel_norm_pow7 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 7))
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hdomOn :
      IntegrableOn (fun x : ℝ => (x + z.re) ^ (-7 : ℝ))
        (Set.Ioi (0 : ℝ)) := by
    have hlt : (-7 : ℝ) < -1 := by norm_num
    have hc : -z.re < (0 : ℝ) := by linarith [hz]
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-7 : ℝ))
        (c := (0 : ℝ)) (m := z.re) hlt hc)
  have hdomOn' :
      IntegrableOn (fun x : ℝ => 1 / (x + z.re) ^ 7)
        (Set.Ioi (0 : ℝ)) := by
    refine hdomOn.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hxre_pos : 0 < x + z.re := by
      linarith [hxpos, hz]
    have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
    calc
      (x + z.re) ^ (-7 : ℝ)
          = ((x + z.re) ^ (7 : ℝ))⁻¹ := by
              simpa using (rpow_neg_eq_inv_rpow (x + z.re) (7 : ℝ))
      _ = ((x + z.re) ^ 7)⁻¹ := by
              simp [Real.rpow_natCast, hxre_nonneg]
      _ = 1 / (x + z.re) ^ 7 := by
              simp [one_div]
  have hdom :
      Integrable (fun x : ℝ => 1 / (x + z.re) ^ 7)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hdomOn'
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => 1 / ‖(x : ℂ) + z‖ ^ 7)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hcoe : Measurable (fun x : ℝ => (x : ℂ)) :=
      Complex.measurable_ofReal
    have hadd : Measurable (fun x : ℝ => (x : ℂ) + z) :=
      hcoe.add measurable_const
    have hnorm : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖) :=
      hadd.norm
    have hpow : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖ ^ 7) :=
      hnorm.pow_const 7
    have hinv : Measurable (fun x : ℝ => (‖(x : ℂ) + z‖ ^ 7)⁻¹) :=
      hpow.inv
    simpa [one_div] using hinv.aestronglyMeasurable
  have hbound :
      ∀ᵐ x : ℝ ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(1 / ‖(x : ℂ) + z‖ ^ 7 : ℝ)‖ ≤
          1 / (x + z.re) ^ 7 := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    have hnonneg : 0 ≤ (1 / ‖(x : ℂ) + z‖ ^ 7 : ℝ) := by
      exact one_div_nonneg.mpr (pow_nonneg (norm_nonneg _) 7)
    have hnorm_abs :
        ‖(1 / ‖(x : ℂ) + z‖ ^ 7 : ℝ)‖ =
          1 / ‖(x : ℂ) + z‖ ^ 7 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [hnorm_abs] using kernel_norm_pow7_le_re z hz hx
  exact Integrable.mono' hdom hmeas hbound

lemma integrable_bernoulli6Diff_div_pow7 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hkernel :
      Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 7))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    integrable_kernel_norm_pow7 z hz
  have hkernel' :
      Integrable (fun x : ℝ => (8 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 7))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    hkernel.const_mul (8 : ℝ)
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hmeas : Measurable
        (fun x => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7) := by
      have hcoe : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
      have h_add : Measurable (fun x : ℝ => (x : ℂ) + z) := hcoe.add measurable_const
      have h_pow : Measurable (fun x : ℝ => ((x : ℂ) + z) ^ 7) := h_add.pow_const 7
      have h_num : Measurable (fun x : ℝ => (bernoulli6Diff x : ℂ)) :=
        (Complex.measurable_ofReal.comp measurable_bernoulli6Diff)
      exact h_num.div h_pow
    simpa using hmeas.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7‖ ≤
          (8 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 7) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hnorm_pow : ‖(x + z : ℂ) ^ 7‖ = ‖(x + z : ℂ)‖ ^ 7 := by
      simp [norm_pow]
    have hpos : 0 ≤ ‖(x : ℂ) + z‖ ^ 7 := by positivity
    calc
      ‖(bernoulli6Diff x : ℂ) / (x + z) ^ 7‖
          = ‖(bernoulli6Diff x : ℂ)‖ / ‖(x + z : ℂ) ^ 7‖ := by
            simp
      _ = ‖(bernoulli6Diff x : ℂ)‖ / ‖(x : ℂ) + z‖ ^ 7 := by
            simp [hnorm_pow]
      _ ≤ (8 : ℝ) / ‖(x : ℂ) + z‖ ^ 7 := by
            exact (div_le_div_of_nonneg_right (bernoulli6Diff_norm_le x) hpos)
      _ = (8 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 7) := by
            field_simp
  exact Integrable.mono' hkernel' hmeas hbound

/-- Pointwise right-half-plane domination for the order-9 kernel used by the
B8/power-9 Stieltjes tail ledger. -/
lemma kernel_norm_pow9_le_re (z : ℂ) (hz : 0 < z.re)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    1 / ‖(x : ℂ) + z‖ ^ 9 ≤ 1 / (x + z.re) ^ 9 := by
  have hxpos : 0 < x := hx
  have hxre_pos : 0 < x + z.re := by
    linarith [hxpos, hz]
  have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
  have hnorm_ge : x + z.re ≤ ‖(x : ℂ) + z‖ := by
    have h := Complex.abs_re_le_norm ((x : ℂ) + z)
    have hre : (((x : ℂ) + z).re) = x + z.re := by
      simp
    have habs : |(((x : ℂ) + z).re)| = x + z.re := by
      rw [hre, abs_of_nonneg hxre_nonneg]
    rwa [habs] at h
  have hpow :
      (x + z.re) ^ 9 ≤ ‖(x : ℂ) + z‖ ^ 9 :=
    pow_le_pow_left₀ hxre_nonneg hnorm_ge 9
  exact one_div_le_one_div_of_le (pow_pos hxre_pos 9) hpow

/-- Integrability of the order-9 kernel used by the B8/power-9 Stieltjes tail
ledger. -/
lemma integrable_kernel_norm_pow9 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 9))
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hdomOn :
      IntegrableOn (fun x : ℝ => (x + z.re) ^ (-9 : ℝ))
        (Set.Ioi (0 : ℝ)) := by
    have hlt : (-9 : ℝ) < -1 := by norm_num
    have hc : -z.re < (0 : ℝ) := by linarith [hz]
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-9 : ℝ))
        (c := (0 : ℝ)) (m := z.re) hlt hc)
  have hdomOn' :
      IntegrableOn (fun x : ℝ => 1 / (x + z.re) ^ 9)
        (Set.Ioi (0 : ℝ)) := by
    refine hdomOn.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hxre_pos : 0 < x + z.re := by
      linarith [hxpos, hz]
    have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
    calc
      (x + z.re) ^ (-9 : ℝ)
          = ((x + z.re) ^ (9 : ℝ))⁻¹ := by
              simpa using (rpow_neg_eq_inv_rpow (x + z.re) (9 : ℝ))
      _ = ((x + z.re) ^ 9)⁻¹ := by
              simp [Real.rpow_natCast, hxre_nonneg]
      _ = 1 / (x + z.re) ^ 9 := by
              simp [one_div]
  have hdom :
      Integrable (fun x : ℝ => 1 / (x + z.re) ^ 9)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hdomOn'
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => 1 / ‖(x : ℂ) + z‖ ^ 9)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hcoe : Measurable (fun x : ℝ => (x : ℂ)) :=
      Complex.measurable_ofReal
    have hadd : Measurable (fun x : ℝ => (x : ℂ) + z) :=
      hcoe.add measurable_const
    have hnorm : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖) :=
      hadd.norm
    have hpow : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖ ^ 9) :=
      hnorm.pow_const 9
    have hinv : Measurable (fun x : ℝ => (‖(x : ℂ) + z‖ ^ 9)⁻¹) :=
      hpow.inv
    simpa [one_div] using hinv.aestronglyMeasurable
  have hbound :
      ∀ᵐ x : ℝ ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(1 / ‖(x : ℂ) + z‖ ^ 9 : ℝ)‖ ≤
          1 / (x + z.re) ^ 9 := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    have hnonneg : 0 ≤ (1 / ‖(x : ℂ) + z‖ ^ 9 : ℝ) := by
      exact one_div_nonneg.mpr (pow_nonneg (norm_nonneg _) 9)
    have hnorm_abs :
        ‖(1 / ‖(x : ℂ) + z‖ ^ 9 : ℝ)‖ =
          1 / ‖(x : ℂ) + z‖ ^ 9 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [hnorm_abs] using kernel_norm_pow9_le_re z hz hx
  exact Integrable.mono' hdom hmeas hbound

lemma integrable_bernoulli8Diff_div_pow9 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hkernel :
      Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 9))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    integrable_kernel_norm_pow9 z hz
  have hkernel' :
      Integrable (fun x : ℝ => (8 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 9))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    hkernel.const_mul (8 : ℝ)
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hmeas : Measurable
        (fun x => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9) := by
      have hcoe : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
      have h_add : Measurable (fun x : ℝ => (x : ℂ) + z) := hcoe.add measurable_const
      have h_pow : Measurable (fun x : ℝ => ((x : ℂ) + z) ^ 9) := h_add.pow_const 9
      have h_num : Measurable (fun x : ℝ => (bernoulli8Diff x : ℂ)) :=
        (Complex.measurable_ofReal.comp measurable_bernoulli8Diff)
      exact h_num.div h_pow
    simpa using hmeas.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9‖ ≤
          (8 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 9) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hnorm_pow : ‖(x + z : ℂ) ^ 9‖ = ‖(x + z : ℂ)‖ ^ 9 := by
      simp [norm_pow]
    have hpos : 0 ≤ ‖(x : ℂ) + z‖ ^ 9 := by positivity
    calc
      ‖(bernoulli8Diff x : ℂ) / (x + z) ^ 9‖
          = ‖(bernoulli8Diff x : ℂ)‖ / ‖(x + z : ℂ) ^ 9‖ := by
            simp
      _ = ‖(bernoulli8Diff x : ℂ)‖ / ‖(x : ℂ) + z‖ ^ 9 := by
            simp [hnorm_pow]
      _ ≤ (8 : ℝ) / ‖(x : ℂ) + z‖ ^ 9 := by
            exact (div_le_div_of_nonneg_right (bernoulli8Diff_norm_le x) hpos)
      _ = (8 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 9) := by
            field_simp
  exact Integrable.mono' hkernel' hmeas hbound

/-- Pointwise right-half-plane domination for the order-11 kernel used by the
B10/power-11 Stieltjes tail ledger. -/
lemma kernel_norm_pow11_le_re (z : ℂ) (hz : 0 < z.re)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    1 / ‖(x : ℂ) + z‖ ^ 11 ≤ 1 / (x + z.re) ^ 11 := by
  have hxpos : 0 < x := hx
  have hxre_pos : 0 < x + z.re := by
    linarith [hxpos, hz]
  have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
  have hnorm_ge : x + z.re ≤ ‖(x : ℂ) + z‖ := by
    have h := Complex.abs_re_le_norm ((x : ℂ) + z)
    have hre : (((x : ℂ) + z).re) = x + z.re := by
      simp
    have habs : |(((x : ℂ) + z).re)| = x + z.re := by
      rw [hre, abs_of_nonneg hxre_nonneg]
    rwa [habs] at h
  have hpow :
      (x + z.re) ^ 11 ≤ ‖(x : ℂ) + z‖ ^ 11 :=
    pow_le_pow_left₀ hxre_nonneg hnorm_ge 11
  exact one_div_le_one_div_of_le (pow_pos hxre_pos 11) hpow

/-- Integrability of the order-11 kernel used by the B10/power-11 Stieltjes
tail ledger. -/
lemma integrable_kernel_norm_pow11 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 11))
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hdomOn :
      IntegrableOn (fun x : ℝ => (x + z.re) ^ (-11 : ℝ))
        (Set.Ioi (0 : ℝ)) := by
    have hlt : (-11 : ℝ) < -1 := by norm_num
    have hc : -z.re < (0 : ℝ) := by linarith [hz]
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-11 : ℝ))
        (c := (0 : ℝ)) (m := z.re) hlt hc)
  have hdomOn' :
      IntegrableOn (fun x : ℝ => 1 / (x + z.re) ^ 11)
        (Set.Ioi (0 : ℝ)) := by
    refine hdomOn.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hxre_pos : 0 < x + z.re := by
      linarith [hxpos, hz]
    have hxre_nonneg : 0 ≤ x + z.re := le_of_lt hxre_pos
    calc
      (x + z.re) ^ (-11 : ℝ)
          = ((x + z.re) ^ (11 : ℝ))⁻¹ := by
              simpa using (rpow_neg_eq_inv_rpow (x + z.re) (11 : ℝ))
      _ = ((x + z.re) ^ 11)⁻¹ := by
              simp [Real.rpow_natCast, hxre_nonneg]
      _ = 1 / (x + z.re) ^ 11 := by
              simp [one_div]
  have hdom :
      Integrable (fun x : ℝ => 1 / (x + z.re) ^ 11)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hdomOn'
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => 1 / ‖(x : ℂ) + z‖ ^ 11)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hcoe : Measurable (fun x : ℝ => (x : ℂ)) :=
      Complex.measurable_ofReal
    have hadd : Measurable (fun x : ℝ => (x : ℂ) + z) :=
      hcoe.add measurable_const
    have hnorm : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖) :=
      hadd.norm
    have hpow : Measurable (fun x : ℝ => ‖(x : ℂ) + z‖ ^ 11) :=
      hnorm.pow_const 11
    have hinv : Measurable (fun x : ℝ => (‖(x : ℂ) + z‖ ^ 11)⁻¹) :=
      hpow.inv
    simpa [one_div] using hinv.aestronglyMeasurable
  have hbound :
      ∀ᵐ x : ℝ ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(1 / ‖(x : ℂ) + z‖ ^ 11 : ℝ)‖ ≤
          1 / (x + z.re) ^ 11 := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    have hnonneg : 0 ≤ (1 / ‖(x : ℂ) + z‖ ^ 11 : ℝ) := by
      exact one_div_nonneg.mpr (pow_nonneg (norm_nonneg _) 11)
    have hnorm_abs :
        ‖(1 / ‖(x : ℂ) + z‖ ^ 11 : ℝ)‖ =
          1 / ‖(x : ℂ) + z‖ ^ 11 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [hnorm_abs] using kernel_norm_pow11_le_re z hz hx
  exact Integrable.mono' hdom hmeas hbound

lemma integrable_bernoulli10Diff_div_pow11 (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
      (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hkernel :
      Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 11))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    integrable_kernel_norm_pow11 z hz
  have hkernel' :
      Integrable (fun x : ℝ => (32 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 11))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) :=
    hkernel.const_mul (32 : ℝ)
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    have hmeas : Measurable
        (fun x => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11) := by
      have hcoe : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
      have h_add : Measurable (fun x : ℝ => (x : ℂ) + z) := hcoe.add measurable_const
      have h_pow : Measurable (fun x : ℝ => ((x : ℂ) + z) ^ 11) := h_add.pow_const 11
      have h_num : Measurable (fun x : ℝ => (bernoulli10Diff x : ℂ)) :=
        (Complex.measurable_ofReal.comp measurable_bernoulli10Diff)
      exact h_num.div h_pow
    simpa using hmeas.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ‖(bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11‖ ≤
          (32 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 11) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hnorm_pow : ‖(x + z : ℂ) ^ 11‖ = ‖(x + z : ℂ)‖ ^ 11 := by
      simp [norm_pow]
    have hpos : 0 ≤ ‖(x : ℂ) + z‖ ^ 11 := by positivity
    calc
      ‖(bernoulli10Diff x : ℂ) / (x + z) ^ 11‖
          = ‖(bernoulli10Diff x : ℂ)‖ / ‖(x + z : ℂ) ^ 11‖ := by
            simp
      _ = ‖(bernoulli10Diff x : ℂ)‖ / ‖(x : ℂ) + z‖ ^ 11 := by
            simp [hnorm_pow]
      _ ≤ (32 : ℝ) / ‖(x : ℂ) + z‖ ^ 11 := by
            exact (div_le_div_of_nonneg_right (bernoulli10Diff_norm_le x) hpos)
      _ = (32 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 11) := by
            field_simp
  exact Integrable.mono' hkernel' hmeas hbound

lemma tendsto_intervalIntegral_b2diff_div_Ioi (z : ℂ) (hz : 0 < z.re) :
    Tendsto
      (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
      atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ),
        (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)) := by
  have h_int :
      IntegrableOn
        (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
        (Set.Ioi (0 : ℝ)) volume := by
    simpa [IntegrableOn] using integrable_bernoulli2Diff_div z hz
  simpa using
    (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      (f := fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
      (μ := volume) (b := fun N : ℕ => (N : ℝ)) (l := atTop)
      h_int (tendsto_natCast_atTop_atTop))

lemma tendsto_intervalIntegral_b4diff_div_pow5_Ioi (z : ℂ) (hz : 0 < z.re) :
    Tendsto
      (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
      atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)) := by
  have h_int :
      IntegrableOn
        (fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
        (Set.Ioi (0 : ℝ)) volume := by
    simpa [IntegrableOn] using integrable_bernoulli4Diff_div_pow5 z hz
  simpa using
    (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      (f := fun x : ℝ => (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
      (μ := volume) (b := fun N : ℕ => (N : ℝ)) (l := atTop)
      h_int (tendsto_natCast_atTop_atTop))

lemma tendsto_intervalIntegral_b6diff_div_pow7_Ioi (z : ℂ) (hz : 0 < z.re) :
    Tendsto
      (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
      atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)) := by
  have h_int :
      IntegrableOn
        (fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
        (Set.Ioi (0 : ℝ)) volume := by
    simpa [IntegrableOn] using integrable_bernoulli6Diff_div_pow7 z hz
  simpa using
    (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      (f := fun x : ℝ => (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
      (μ := volume) (b := fun N : ℕ => (N : ℝ)) (l := atTop)
      h_int (tendsto_natCast_atTop_atTop))

lemma tendsto_intervalIntegral_b8diff_div_pow9_Ioi (z : ℂ) (hz : 0 < z.re) :
    Tendsto
      (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
      atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)) := by
  have h_int :
      IntegrableOn
        (fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
        (Set.Ioi (0 : ℝ)) volume := by
    simpa [IntegrableOn] using integrable_bernoulli8Diff_div_pow9 z hz
  simpa using
    (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      (f := fun x : ℝ => (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
      (μ := volume) (b := fun N : ℕ => (N : ℝ)) (l := atTop)
      h_int (tendsto_natCast_atTop_atTop))

lemma tendsto_intervalIntegral_b10diff_div_pow11_Ioi (z : ℂ) (hz : 0 < z.re) :
    Tendsto
      (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
      atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ),
        (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)) := by
  have h_int :
      IntegrableOn
        (fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
        (Set.Ioi (0 : ℝ)) volume := by
    simpa [IntegrableOn] using integrable_bernoulli10Diff_div_pow11 z hz
  simpa using
    (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      (f := fun x : ℝ => (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
      (μ := volume) (b := fun N : ℕ => (N : ℝ)) (l := atTop)
      h_int (tendsto_natCast_atTop_atTop))

lemma tendsto_nat_add_complex_inv (z : ℂ) :
    Tendsto (fun N : ℕ => (((N : ℂ) + z)⁻¹)) atTop (𝓝 (0 : ℂ)) := by
  have h_inv_nat : Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 (0 : ℂ)) := by
    have hreal : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    have hreal' : Tendsto (fun N : ℕ => (Complex.ofReal ((N : ℝ)⁻¹))) atTop (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hreal
    simpa using hreal'
  have h_div : Tendsto (fun N : ℕ => z / (N : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul h_inv_nat)
  have h_one_add : Tendsto (fun N : ℕ => (1 : ℂ) + z / (N : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa using (tendsto_const_nhds.add h_div)
  have h_inv_one_add :
      Tendsto (fun N : ℕ => ((1 : ℂ) + z / (N : ℂ))⁻¹) atTop (𝓝 (1 : ℂ)⁻¹) := by
    exact (tendsto_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).comp h_one_add
  have hmul_inv :
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ((1 : ℂ) + z / (N : ℂ))⁻¹)
        atTop (𝓝 (0 : ℂ)) := by
    simpa using (h_inv_nat.mul h_inv_one_add)
  have h_event_inv :
      ∀ᶠ N : ℕ in atTop,
        ((N : ℂ) + z)⁻¹ = (N : ℂ)⁻¹ * ((1 : ℂ) + z / (N : ℂ))⁻¹ := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro N hN
    have hNne : (N : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.succ_le_iff.mp hN))
    have hmul : ((N : ℂ) + z) = (N : ℂ) * (1 + z / (N : ℂ)) := by
      symm
      calc
        (N : ℂ) * (1 + z / (N : ℂ))
            = (N : ℂ) * 1 + (N : ℂ) * (z / (N : ℂ)) := by
                simp [mul_add]
        _ = (N : ℂ) + (N : ℂ) * (z / (N : ℂ)) := by simp
        _ = (N : ℂ) + z := by
            simp [div_eq_mul_inv, hNne, mul_assoc, mul_left_comm, mul_comm]
    calc
      ((N : ℂ) + z)⁻¹
          = ((N : ℂ) * (1 + z / (N : ℂ)))⁻¹ := by simpa [hmul]
      _ = (1 + z / (N : ℂ))⁻¹ * (N : ℂ)⁻¹ := by
            simpa using (mul_inv_rev (N : ℂ) (1 + z / (N : ℂ)))
      _ = (N : ℂ)⁻¹ * (1 + z / (N : ℂ))⁻¹ := by
            ring
  exact (tendsto_congr' h_event_inv).2 hmul_inv

lemma stieltjes_B2Diff_to_B4Diff_Ioi_raw (z : ℂ) (hz : 0 < z.re) :
    ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3 =
      (1 / 6 : ℂ) *
          ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - 0)) -
        ((1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) * (0 - (z⁻¹) ^ 4)) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5) := by
  let L : ℕ → ℂ := fun N =>
    ∫ x in (0 : ℝ)..(N : ℝ),
      (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3
  let R : ℕ → ℂ := fun N =>
    (1 / 6 : ℂ) *
        ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - ((((N : ℂ) + z)⁻¹) ^ 2))) -
      ((1 / 4 : ℂ) *
        ((-(30 : ℂ)⁻¹) *
          (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4)) +
        ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
  have hLR : ∀ N, L N = R N := by
    intro N
    simpa [L, R] using finite_stieltjes_B2Diff_to_B4Diff z hz N
  have hL :
      Tendsto L atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ),
          (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)) := by
    simpa [L] using tendsto_intervalIntegral_b2diff_div_Ioi z hz
  have h_inv : Tendsto (fun N : ℕ => (((N : ℂ) + z)⁻¹)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_nat_add_complex_inv z
  have h_inv2 :
      Tendsto (fun N : ℕ => ((((N : ℂ) + z)⁻¹) ^ 2)) atTop (𝓝 ((0 : ℂ) ^ 2)) := by
    simpa using h_inv.pow 2
  have h_inv4 :
      Tendsto (fun N : ℕ => ((((N : ℂ) + z)⁻¹) ^ 4)) atTop (𝓝 ((0 : ℂ) ^ 4)) := by
    simpa using h_inv.pow 4
  have hB4 :
      Tendsto
        (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
        atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)) :=
    tendsto_intervalIntegral_b4diff_div_pow5_Ioi z hz
  have hA :
      Tendsto
        (fun N : ℕ =>
          (1 / 6 : ℂ) *
            ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - ((((N : ℂ) + z)⁻¹) ^ 2))))
        atTop
        (𝓝 ((1 / 6 : ℂ) * ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - 0)))) := by
    have hsub :
        Tendsto (fun N : ℕ => (z⁻¹) ^ 2 - ((((N : ℂ) + z)⁻¹) ^ 2))
          atTop (𝓝 ((z⁻¹) ^ 2 - (0 : ℂ) ^ 2)) := by
      exact tendsto_const_nhds.sub h_inv2
    have hmul :
        Tendsto
          (fun N : ℕ =>
            (1 / 2 : ℂ) * ((z⁻¹) ^ 2 - ((((N : ℂ) + z)⁻¹) ^ 2)))
          atTop
          (𝓝 ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - (0 : ℂ) ^ 2))) := by
      simpa using hsub.const_mul (1 / 2 : ℂ)
    simpa using hmul.const_mul (1 / 6 : ℂ)
  have hEndpoint :
      Tendsto
        (fun N : ℕ =>
          (-(30 : ℂ)⁻¹) * (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4))
        atTop
        (𝓝 ((-(30 : ℂ)⁻¹) * (0 - (z⁻¹) ^ 4))) := by
    have hsub :
        Tendsto
          (fun N : ℕ => (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4))
          atTop (𝓝 ((0 : ℂ) ^ 4 - (z⁻¹) ^ 4)) := by
      exact h_inv4.sub tendsto_const_nhds
    simpa using hsub.const_mul (-(30 : ℂ)⁻¹)
  have hB :
      Tendsto
        (fun N : ℕ =>
          (1 / 4 : ℂ) *
            ((-(30 : ℂ)⁻¹) *
              (((((N : ℂ) + z)⁻¹) ^ 4) - (z⁻¹) ^ 4)) +
            ∫ x in (0 : ℝ)..(N : ℝ),
              (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)
        atTop
        (𝓝 ((1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) * (0 - (z⁻¹) ^ 4)) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)) := by
    simpa using hEndpoint.const_mul (1 / 4 : ℂ) |>.add hB4
  have hR :
      Tendsto R atTop
        (𝓝 ((1 / 6 : ℂ) *
          ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - 0)) -
        ((1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) * (0 - (z⁻¹) ^ 4)) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5))) := by
    simpa [R] using hA.sub hB
  have hL_to_rhs :
      Tendsto L atTop
        (𝓝 ((1 / 6 : ℂ) *
          ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - 0)) -
        ((1 / 4 : ℂ) *
          ((-(30 : ℂ)⁻¹) * (0 - (z⁻¹) ^ 4)) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5))) := by
    exact (tendsto_congr' (Filter.Eventually.of_forall hLR)).2 hR
  exact tendsto_nhds_unique hL hL_to_rhs

lemma stieltjes_B4Diff_to_B6Diff_Ioi_raw (z : ℂ) (hz : 0 < z.re) :
    ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 =
      (252 : ℂ)⁻¹ * ((0 : ℂ) ^ 6 - (z⁻¹) ^ 6) +
        ∫ x in Set.Ioi (0 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
  let L : ℕ → ℂ := fun N =>
    ∫ x in (0 : ℝ)..(N : ℝ),
      (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5
  let R : ℕ → ℂ := fun N =>
    (252 : ℂ)⁻¹ * (((((N : ℂ) + z)⁻¹) ^ 6) - (z⁻¹) ^ 6) +
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
  have hLR : ∀ N, L N = R N := by
    intro N
    simpa [L, R] using finite_stieltjes_B4Diff_to_B6Diff z hz N
  have hL :
      Tendsto L atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ),
          (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5)) := by
    simpa [L] using tendsto_intervalIntegral_b4diff_div_pow5_Ioi z hz
  have h_inv : Tendsto (fun N : ℕ => (((N : ℂ) + z)⁻¹)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_nat_add_complex_inv z
  have h_inv6 :
      Tendsto (fun N : ℕ => ((((N : ℂ) + z)⁻¹) ^ 6)) atTop (𝓝 ((0 : ℂ) ^ 6)) := by
    simpa using h_inv.pow 6
  have hB6 :
      Tendsto
        (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)
        atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)) :=
    tendsto_intervalIntegral_b6diff_div_pow7_Ioi z hz
  have hEndpoint :
      Tendsto
        (fun N : ℕ =>
          (252 : ℂ)⁻¹ * (((((N : ℂ) + z)⁻¹) ^ 6) - (z⁻¹) ^ 6))
        atTop
        (𝓝 ((252 : ℂ)⁻¹ * ((0 : ℂ) ^ 6 - (z⁻¹) ^ 6))) := by
    have hsub :
        Tendsto
          (fun N : ℕ => (((((N : ℂ) + z)⁻¹) ^ 6) - (z⁻¹) ^ 6))
          atTop (𝓝 ((0 : ℂ) ^ 6 - (z⁻¹) ^ 6)) := by
      exact h_inv6.sub tendsto_const_nhds
    simpa using hsub.const_mul (252 : ℂ)⁻¹
  have hR :
      Tendsto R atTop
        (𝓝 ((252 : ℂ)⁻¹ * ((0 : ℂ) ^ 6 - (z⁻¹) ^ 6) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)) := by
    simpa [R] using hEndpoint.add hB6
  have hL_to_rhs :
      Tendsto L atTop
        (𝓝 ((252 : ℂ)⁻¹ * ((0 : ℂ) ^ 6 - (z⁻¹) ^ 6) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)) := by
    exact (tendsto_congr' (Filter.Eventually.of_forall hLR)).2 hR
  exact tendsto_nhds_unique hL hL_to_rhs

lemma stieltjes_B6Diff_to_B8Diff_Ioi_raw (z : ℂ) (hz : 0 < z.re) :
    ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 =
      (-(240 : ℂ)⁻¹) * ((0 : ℂ) ^ 8 - (z⁻¹) ^ 8) +
        ∫ x in Set.Ioi (0 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
  let L : ℕ → ℂ := fun N =>
    ∫ x in (0 : ℝ)..(N : ℝ),
      (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
  let R : ℕ → ℂ := fun N =>
    (-(240 : ℂ)⁻¹) * (((((N : ℂ) + z)⁻¹) ^ 8) - (z⁻¹) ^ 8) +
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9
  have hLR : ∀ N, L N = R N := by
    intro N
    simpa [L, R] using finite_stieltjes_B6Diff_to_B8Diff z hz N
  have hL :
      Tendsto L atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ),
          (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7)) := by
    simpa [L] using tendsto_intervalIntegral_b6diff_div_pow7_Ioi z hz
  have h_inv : Tendsto (fun N : ℕ => (((N : ℂ) + z)⁻¹)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_nat_add_complex_inv z
  have h_inv8 :
      Tendsto (fun N : ℕ => ((((N : ℂ) + z)⁻¹) ^ 8)) atTop (𝓝 ((0 : ℂ) ^ 8)) := by
    simpa using h_inv.pow 8
  have hB8 :
      Tendsto
        (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)
        atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)) :=
    tendsto_intervalIntegral_b8diff_div_pow9_Ioi z hz
  have hEndpoint :
      Tendsto
        (fun N : ℕ =>
          (-(240 : ℂ)⁻¹) * (((((N : ℂ) + z)⁻¹) ^ 8) - (z⁻¹) ^ 8))
        atTop
        (𝓝 ((-(240 : ℂ)⁻¹) * ((0 : ℂ) ^ 8 - (z⁻¹) ^ 8))) := by
    have hsub :
        Tendsto
          (fun N : ℕ => (((((N : ℂ) + z)⁻¹) ^ 8) - (z⁻¹) ^ 8))
          atTop (𝓝 ((0 : ℂ) ^ 8 - (z⁻¹) ^ 8)) := by
      exact h_inv8.sub tendsto_const_nhds
    simpa using hsub.const_mul (-(240 : ℂ)⁻¹)
  have hR :
      Tendsto R atTop
        (𝓝 ((-(240 : ℂ)⁻¹) * ((0 : ℂ) ^ 8 - (z⁻¹) ^ 8) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)) := by
    simpa [R] using hEndpoint.add hB8
  have hL_to_rhs :
      Tendsto L atTop
        (𝓝 ((-(240 : ℂ)⁻¹) * ((0 : ℂ) ^ 8 - (z⁻¹) ^ 8) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)) := by
    exact (tendsto_congr' (Filter.Eventually.of_forall hLR)).2 hR
  exact tendsto_nhds_unique hL hL_to_rhs

lemma stieltjes_B8Diff_to_B10Diff_Ioi_raw (z : ℂ) (hz : 0 < z.re) :
    ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 =
      (132 : ℂ)⁻¹ * ((0 : ℂ) ^ 10 - (z⁻¹) ^ 10) +
        ∫ x in Set.Ioi (0 : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11 := by
  let L : ℕ → ℂ := fun N =>
    ∫ x in (0 : ℝ)..(N : ℝ),
      (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9
  let R : ℕ → ℂ := fun N =>
    (132 : ℂ)⁻¹ * (((((N : ℂ) + z)⁻¹) ^ 10) - (z⁻¹) ^ 10) +
      ∫ x in (0 : ℝ)..(N : ℝ),
        (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11
  have hLR : ∀ N, L N = R N := by
    intro N
    simpa [L, R] using finite_stieltjes_B8Diff_to_B10Diff z hz N
  have hL :
      Tendsto L atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ),
          (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9)) := by
    simpa [L] using tendsto_intervalIntegral_b8diff_div_pow9_Ioi z hz
  have h_inv : Tendsto (fun N : ℕ => (((N : ℂ) + z)⁻¹)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_nat_add_complex_inv z
  have h_inv10 :
      Tendsto (fun N : ℕ => ((((N : ℂ) + z)⁻¹) ^ 10)) atTop
        (𝓝 ((0 : ℂ) ^ 10)) := by
    simpa using h_inv.pow 10
  have hB10 :
      Tendsto
        (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)
        atTop
        (𝓝 (∫ x in Set.Ioi (0 : ℝ),
          (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)) :=
    tendsto_intervalIntegral_b10diff_div_pow11_Ioi z hz
  have hEndpoint :
      Tendsto
        (fun N : ℕ =>
          (132 : ℂ)⁻¹ * (((((N : ℂ) + z)⁻¹) ^ 10) - (z⁻¹) ^ 10))
        atTop
        (𝓝 ((132 : ℂ)⁻¹ * ((0 : ℂ) ^ 10 - (z⁻¹) ^ 10))) := by
    have hsub :
        Tendsto
          (fun N : ℕ => (((((N : ℂ) + z)⁻¹) ^ 10) - (z⁻¹) ^ 10))
          atTop (𝓝 ((0 : ℂ) ^ 10 - (z⁻¹) ^ 10)) := by
      exact h_inv10.sub tendsto_const_nhds
    simpa using hsub.const_mul (132 : ℂ)⁻¹
  have hR :
      Tendsto R atTop
        (𝓝 ((132 : ℂ)⁻¹ * ((0 : ℂ) ^ 10 - (z⁻¹) ^ 10) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)) := by
    simpa [R] using hEndpoint.add hB10
  have hL_to_rhs :
      Tendsto L atTop
        (𝓝 ((132 : ℂ)⁻¹ * ((0 : ℂ) ^ 10 - (z⁻¹) ^ 10) +
          ∫ x in Set.Ioi (0 : ℝ),
            (bernoulli10Diff x : ℂ) / ((x : ℂ) + z) ^ 11)) := by
    exact (tendsto_congr' (Filter.Eventually.of_forall hLR)).2 hR
  exact tendsto_nhds_unique hL hL_to_rhs

/-!
Final real-part bound for the Stieltjes remainder.
The proof uses the N=1 Stieltjes identity + `integral_kernel_bound`.
-/

lemma digamma_stieltjes_identity (z : ℂ) (hz : 0 < z.re) :
    Q3.digamma z - Complex.log z + (1 / (2 : ℂ)) * z⁻¹ =
      -∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (x + z) ^ 3 := by
  classical
  set Iinf : ℂ :=
    ∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (x + z) ^ 3
  let A : ℕ → ℂ := fun N => (Real.log N : ℂ) - Complex.log (z + (N : ℂ))
  let B : ℂ := Complex.log z - (1 / 2 : ℂ) * z⁻¹
  let C : ℕ → ℂ := fun N => (1 / 2 : ℂ) * (z + (N : ℂ))⁻¹
  let D : ℕ → ℂ :=
    fun N => ∫ x in (0 : ℝ)..(N : ℝ),
      (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3
  let F : ℕ → ℂ := fun N => A N + B - C N - D N
  have hF_eq : ∀ N, _root_.digammaSeq z N = F N := by
    intro N
    have h := digammaSeq_eq_stieltjes z hz N
    simpa [F, A, B, C, D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hF_tendsto : Tendsto F atTop (𝓝 (Q3.digamma z)) := by
    have hdigamma := digammaSeq_tendsto_Q3_digamma z hz
    have hF_eq' : (fun N => _root_.digammaSeq z N) = F := by
      funext N
      exact hF_eq N
    simpa [hF_eq'] using hdigamma
  have h_inv_nat : Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 (0 : ℂ)) := by
    have hreal : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    have hreal' : Tendsto (fun N : ℕ => (Complex.ofReal ((N : ℝ)⁻¹))) atTop (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hreal
    simpa using hreal'
  have h_div : Tendsto (fun N : ℕ => z / (N : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul h_inv_nat)
  have h_one_add : Tendsto (fun N : ℕ => (1 : ℂ) + z / (N : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa using (tendsto_const_nhds.add h_div)
  have hslit1 : (1 : ℂ) ∈ Complex.slitPlane := by
    have hnot : ¬ (1 : ℂ) ≤ 0 := by
      intro hle
      have hle' : (1 : ℂ).re ≤ 0 := by
        simpa using (Complex.re_le_re hle)
      linarith
    exact (Complex.mem_slitPlane_iff_not_le_zero).2 hnot
  have hlog1 :
      Tendsto (fun N : ℕ => Complex.log (1 + z / (N : ℂ))) atTop (𝓝 (0 : ℂ)) := by
    simpa using (Filter.Tendsto.clog h_one_add hslit1)
  have h_event :
      ∀ᶠ N : ℕ in atTop,
        Complex.log (z + (N : ℂ)) - (Real.log N : ℂ) =
          Complex.log (1 + z / (N : ℂ)) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hN)
    have hNne : (N : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.succ_le_iff.mp hN))
    have hmul : (z + (N : ℂ)) = ((N : ℝ) : ℂ) * (1 + z / (N : ℂ)) := by
      symm
      calc
        ((N : ℝ) : ℂ) * (1 + z / (N : ℂ))
            = (N : ℂ) * 1 + (N : ℂ) * (z / (N : ℂ)) := by
                simp [mul_add]
        _ = (N : ℂ) + (N : ℂ) * (z / (N : ℂ)) := by simp
        _ = (N : ℂ) + z := by
              simp [div_eq_mul_inv, hNne, mul_assoc, mul_left_comm, mul_comm]
        _ = z + (N : ℂ) := by ring
    have hRe_div : (z / (N : ℂ)).re = z.re / (N : ℝ) := by
      simpa using (Complex.div_ofReal_re z (N : ℝ))
    have hxpos : 0 < (1 + z / (N : ℂ)).re := by
      have hRe : (1 + z / (N : ℂ)).re = 1 + z.re / (N : ℝ) := by
        simp [Complex.add_re, hRe_div]
      have hdiv : 0 < z.re / (N : ℝ) := by
        exact div_pos hz hNpos
      have hpos : 0 < 1 + z.re / (N : ℝ) := by linarith
      simpa [hRe] using hpos
    have hx : (1 + z / (N : ℂ)) ≠ 0 := by
      intro hzero
      have hzero' : (1 + z / (N : ℂ)).re = 0 := by
        simpa using congrArg Complex.re hzero
      linarith [hxpos, hzero']
    have hlog :
        Complex.log (z + (N : ℂ)) = Real.log (N : ℝ) + Complex.log (1 + z / (N : ℂ)) := by
      calc
        Complex.log (z + (N : ℂ)) =
            Complex.log (((N : ℝ) : ℂ) * (1 + z / (N : ℂ))) := by
              simpa [hmul]
        _ = Real.log (N : ℝ) + Complex.log (1 + z / (N : ℂ)) := by
              simpa using (Complex.log_ofReal_mul hNpos hx)
    calc
      Complex.log (z + (N : ℂ)) - (Real.log N : ℂ)
          = (Real.log (N : ℝ) : ℂ) + Complex.log (1 + z / (N : ℂ)) - (Real.log N : ℂ) := by
              simpa [hlog]
      _ = Complex.log (1 + z / (N : ℂ)) := by ring
  have hlog' :
      Tendsto (fun N : ℕ => Complex.log (z + (N : ℂ)) - (Real.log N : ℂ)) atTop (𝓝 (0 : ℂ)) :=
    (tendsto_congr' h_event).2 hlog1
  have hlog :
      Tendsto (fun N : ℕ => (Real.log N : ℂ) - Complex.log (z + (N : ℂ)))
        atTop (𝓝 (0 : ℂ)) := by
    simpa [sub_eq_add_neg] using hlog'.neg
  have h_inv_one_add :
      Tendsto (fun N : ℕ => (1 + z / (N : ℂ))⁻¹) atTop (𝓝 (1 : ℂ)⁻¹) := by
    exact (tendsto_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).comp h_one_add
  have hmul_inv :
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * (1 + z / (N : ℂ))⁻¹) atTop (𝓝 (0 : ℂ)) := by
    simpa using (h_inv_nat.mul h_inv_one_add)
  have h_event_inv :
      ∀ᶠ N : ℕ in atTop,
        (z + (N : ℂ))⁻¹ = (N : ℂ)⁻¹ * (1 + z / (N : ℂ))⁻¹ := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro N hN
    have hNne : (N : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.succ_le_iff.mp hN))
    have hmul : (z + (N : ℂ)) = (N : ℂ) * (1 + z / (N : ℂ)) := by
      symm
      calc
        (N : ℂ) * (1 + z / (N : ℂ))
            = (N : ℂ) * 1 + (N : ℂ) * (z / (N : ℂ)) := by
                simp [mul_add]
        _ = (N : ℂ) + (N : ℂ) * (z / (N : ℂ)) := by simp
        _ = (N : ℂ) + z := by
            simp [div_eq_mul_inv, hNne, mul_assoc, mul_left_comm, mul_comm]
        _ = z + (N : ℂ) := by ring
    calc
      (z + (N : ℂ))⁻¹
          = ((N : ℂ) * (1 + z / (N : ℂ)))⁻¹ := by simpa [hmul]
      _ = (1 + z / (N : ℂ))⁻¹ * (N : ℂ)⁻¹ := by
            simpa using (mul_inv_rev (N : ℂ) (1 + z / (N : ℂ)))
      _ = (N : ℂ)⁻¹ * (1 + z / (N : ℂ))⁻¹ := by
            ring
  have h_inv_add :
      Tendsto (fun N : ℕ => (z + (N : ℂ))⁻¹) atTop (𝓝 (0 : ℂ)) :=
    (tendsto_congr' h_event_inv).2 hmul_inv
  have h_inv_add_half :
      Tendsto (fun N : ℕ => (1 / 2 : ℂ) * (z + (N : ℂ))⁻¹) atTop (𝓝 (0 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul h_inv_add)
  have hI :
      Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
          (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3) atTop (𝓝 Iinf) := by
    have h_int :
        IntegrableOn (fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
          (Set.Ioi (0 : ℝ)) volume := by
      simpa [IntegrableOn] using (integrable_bernoulli2Diff_div z hz)
    simpa [Iinf] using
      (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
        (f := fun x : ℝ => (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3)
        (μ := volume) (b := fun N : ℕ => (N : ℝ)) (l := atTop)
        h_int (tendsto_natCast_atTop_atTop))
  have hF_lim :
      Tendsto F atTop (𝓝 (B - Iinf)) := by
    have hAB : Tendsto (fun N => A N + B) atTop (𝓝 (0 + B)) :=
      hlog.add tendsto_const_nhds
    have hABC : Tendsto (fun N => A N + B - C N) atTop (𝓝 (B - 0)) :=
      by
        simpa [C] using (hAB.sub h_inv_add_half)
    have hABCD : Tendsto (fun N => A N + B - C N - D N) atTop (𝓝 (B - 0 - Iinf)) :=
      hABC.sub hI
    simpa [F, A, B, C, D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hABCD
  have hlim : Q3.digamma z = B - Iinf := tendsto_nhds_unique hF_tendsto hF_lim
  have hlim' :
      Q3.digamma z - (Complex.log z - (1 / 2 : ℂ) * z⁻¹) = -Iinf := by
    have h := congrArg (fun t => t - (Complex.log z - (1 / 2 : ℂ) * z⁻¹)) hlim
    simpa [B, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  calc
    Q3.digamma z - Complex.log z + (1 / 2 : ℂ) * z⁻¹
        = Q3.digamma z - (Complex.log z - (1 / 2 : ℂ) * z⁻¹) := by
            ring
    _ = -Iinf := hlim'

/-- Normalized B4/power-5 Stieltjes remainder identity for digamma.  This is
the checked bridge from the first Stieltjes identity and the raw B2Diff-to-B4
`Ioi` tail ledger; it is not yet the M6/order-15 source theorem. -/
lemma digamma_stieltjes_B4Diff_Ioi_raw (z : ℂ) (hz : 0 < z.re) :
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z⁻¹) ^ 2 +
          (1 / 120 : ℂ) * (z⁻¹) ^ 4) =
      ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
  let I2 : ℂ :=
    ∫ x in Set.Ioi (0 : ℝ),
      (bernoulli2Diff x : ℂ) / ((x : ℂ) + z) ^ 3
  let I4 : ℂ :=
    ∫ x in Set.Ioi (0 : ℝ),
      (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5
  have hst :
      Q3.digamma z - Complex.log z + (1 / 2 : ℂ) * z⁻¹ = -I2 := by
    simpa [I2] using digamma_stieltjes_identity z hz
  have hraw :
      I2 =
        (1 / 12 : ℂ) * (z⁻¹) ^ 2 -
          (1 / 120 : ℂ) * (z⁻¹) ^ 4 - I4 := by
    have h := stieltjes_B2Diff_to_B4Diff_Ioi_raw z hz
    rw [show I2 =
        (1 / 6 : ℂ) * ((1 / 2 : ℂ) * ((z⁻¹) ^ 2 - 0)) -
          ((1 / 4 : ℂ) *
            ((-(30 : ℂ)⁻¹) * (0 - (z⁻¹) ^ 4)) + I4) by
      simpa [I2, I4] using h]
    ring
  calc
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z⁻¹) ^ 2 +
          (1 / 120 : ℂ) * (z⁻¹) ^ 4)
        =
          (Q3.digamma z - Complex.log z + (1 / 2 : ℂ) * z⁻¹) +
            (1 / 12 : ℂ) * (z⁻¹) ^ 2 -
            (1 / 120 : ℂ) * (z⁻¹) ^ 4 := by
            ring
    _ = -I2 +
            (1 / 12 : ℂ) * (z⁻¹) ^ 2 -
            (1 / 120 : ℂ) * (z⁻¹) ^ 4 := by
            rw [hst]
    _ = I4 := by
            rw [hraw]
            ring

/-- Same B4/power-5 digamma remainder identity, normalized to the inverse-power
surface used by `digammaM6AsymptoticMain`. -/
lemma digamma_stieltjes_B4Diff_Ioi_mainPrefix (z : ℂ) (hz : 0 < z.re) :
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z ^ 2)⁻¹ +
          (1 / 120 : ℂ) * (z ^ 4)⁻¹) =
      ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5 := by
  simpa [inv_pow] using digamma_stieltjes_B4Diff_Ioi_raw z hz

lemma digamma_stieltjes_B6Diff_Ioi_raw (z : ℂ) (hz : 0 < z.re) :
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z⁻¹) ^ 2 +
          (1 / 120 : ℂ) * (z⁻¹) ^ 4 -
          (1 / 252 : ℂ) * (z⁻¹) ^ 6) =
      ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
  let I4 : ℂ :=
    ∫ x in Set.Ioi (0 : ℝ),
      (bernoulli4Diff x : ℂ) / ((x : ℂ) + z) ^ 5
  let I6 : ℂ :=
    ∫ x in Set.Ioi (0 : ℝ),
      (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
  let A : ℂ :=
    Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
      (1 / 12 : ℂ) * (z⁻¹) ^ 2 +
      (1 / 120 : ℂ) * (z⁻¹) ^ 4
  have hB4 : Q3.digamma z - A = I4 := by
    simpa [A, I4] using digamma_stieltjes_B4Diff_Ioi_raw z hz
  have hbridge : I4 = -(1 / 252 : ℂ) * (z⁻¹) ^ 6 + I6 := by
    have h := stieltjes_B4Diff_to_B6Diff_Ioi_raw z hz
    rw [show I4 =
        (252 : ℂ)⁻¹ * ((0 : ℂ) ^ 6 - (z⁻¹) ^ 6) + I6 by
      simpa [I4, I6] using h]
    ring
  calc
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z⁻¹) ^ 2 +
          (1 / 120 : ℂ) * (z⁻¹) ^ 4 -
          (1 / 252 : ℂ) * (z⁻¹) ^ 6)
        = (Q3.digamma z - A) + (1 / 252 : ℂ) * (z⁻¹) ^ 6 := by
            ring
    _ = I4 + (1 / 252 : ℂ) * (z⁻¹) ^ 6 := by
            rw [hB4]
    _ = I6 := by
            rw [hbridge]
            ring

lemma digamma_stieltjes_B6Diff_Ioi_mainPrefix (z : ℂ) (hz : 0 < z.re) :
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z ^ 2)⁻¹ +
          (1 / 120 : ℂ) * (z ^ 4)⁻¹ -
          (1 / 252 : ℂ) * (z ^ 6)⁻¹) =
      ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7 := by
  simpa [inv_pow] using digamma_stieltjes_B6Diff_Ioi_raw z hz

lemma digamma_stieltjes_B8Diff_Ioi_raw (z : ℂ) (hz : 0 < z.re) :
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z⁻¹) ^ 2 +
          (1 / 120 : ℂ) * (z⁻¹) ^ 4 -
          (1 / 252 : ℂ) * (z⁻¹) ^ 6 +
          (1 / 240 : ℂ) * (z⁻¹) ^ 8) =
      ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
  let I6 : ℂ :=
    ∫ x in Set.Ioi (0 : ℝ),
      (bernoulli6Diff x : ℂ) / ((x : ℂ) + z) ^ 7
  let I8 : ℂ :=
    ∫ x in Set.Ioi (0 : ℝ),
      (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9
  let A : ℂ :=
    Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
      (1 / 12 : ℂ) * (z⁻¹) ^ 2 +
      (1 / 120 : ℂ) * (z⁻¹) ^ 4 -
      (1 / 252 : ℂ) * (z⁻¹) ^ 6
  have hB6 : Q3.digamma z - A = I6 := by
    simpa [A, I6] using digamma_stieltjes_B6Diff_Ioi_raw z hz
  have hbridge : I6 = (1 / 240 : ℂ) * (z⁻¹) ^ 8 + I8 := by
    have h := stieltjes_B6Diff_to_B8Diff_Ioi_raw z hz
    rw [show I6 =
        (-(240 : ℂ)⁻¹) * ((0 : ℂ) ^ 8 - (z⁻¹) ^ 8) + I8 by
      simpa [I6, I8] using h]
    ring
  calc
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z⁻¹) ^ 2 +
          (1 / 120 : ℂ) * (z⁻¹) ^ 4 -
          (1 / 252 : ℂ) * (z⁻¹) ^ 6 +
          (1 / 240 : ℂ) * (z⁻¹) ^ 8)
        = (Q3.digamma z - A) - (1 / 240 : ℂ) * (z⁻¹) ^ 8 := by
            ring
    _ = I6 - (1 / 240 : ℂ) * (z⁻¹) ^ 8 := by
            rw [hB6]
    _ = I8 := by
            rw [hbridge]
            ring

lemma digamma_stieltjes_B8Diff_Ioi_mainPrefix (z : ℂ) (hz : 0 < z.re) :
    Q3.digamma z -
        (Complex.log z - (1 / 2 : ℂ) * z⁻¹ -
          (1 / 12 : ℂ) * (z ^ 2)⁻¹ +
          (1 / 120 : ℂ) * (z ^ 4)⁻¹ -
          (1 / 252 : ℂ) * (z ^ 6)⁻¹ +
          (1 / 240 : ℂ) * (z ^ 8)⁻¹) =
      ∫ x in Set.Ioi (0 : ℝ),
        (bernoulli8Diff x : ℂ) / ((x : ℂ) + z) ^ 9 := by
  simpa [inv_pow] using digamma_stieltjes_B8Diff_Ioi_raw z hz

/-- Complex-norm form of the first Stieltjes/Euler-Maclaurin digamma
remainder.  The real-part theorem below is a projection of this bound, while
future high-order endpoint receivers can target the same main/error shape. -/
lemma digamma_stieltjes_complex_remainder_bound (z : ℂ) (hz : 0 < z.re) :
    ‖Q3.digamma z - Complex.log z + (1 / (2 : ℂ)) * z⁻¹‖ ≤
      1 / (4 * ‖z‖^2) := by
  classical
  set E : ℂ := Q3.digamma z - Complex.log z + (1 / (2 : ℂ)) * z⁻¹
  have hE : E = -∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (x + z) ^ 3 := by
    simpa [E] using (digamma_stieltjes_identity z hz)
  have hB : ∀ x : ℝ, ‖(bernoulli2Diff x : ℂ)‖ ≤ (1 / 4 : ℝ) := by
    intro x
    have hb0 : 0 ≤ bernoulli2Diff x := (bernoulli2Diff_bounds x).1
    have hb1 : bernoulli2Diff x ≤ (1 / 4 : ℝ) := (bernoulli2Diff_bounds x).2
    have habs : |bernoulli2Diff x| = bernoulli2Diff x := by simp [abs_of_nonneg hb0]
    have hnorm : ‖(bernoulli2Diff x : ℂ)‖ = |bernoulli2Diff x| := by
      simp
    simpa [hnorm, habs] using hb1
  have hF_bound :
      ∀ x : ℝ,
        ‖(bernoulli2Diff x : ℂ) / (x + z) ^ 3‖
          ≤ (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
    intro x
    have hnorm_pow : ‖(x + z : ℂ) ^ 3‖ = ‖(x + z : ℂ)‖ ^ 3 := by
      simp [norm_pow]
    have hpos : 0 ≤ ‖(x : ℂ) + z‖ ^ 3 := by positivity
    calc
      ‖(bernoulli2Diff x : ℂ) / (x + z) ^ 3‖
          = ‖(bernoulli2Diff x : ℂ)‖ / ‖(x + z : ℂ) ^ 3‖ := by
            simp
      _ = ‖(bernoulli2Diff x : ℂ)‖ / ‖(x : ℂ) + z‖ ^ 3 := by
            simp [hnorm_pow]
      _ ≤ (1 / 4 : ℝ) / ‖(x : ℂ) + z‖ ^ 3 := by
            exact (div_le_div_of_nonneg_right (hB x) hpos)
      _ = (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
            field_simp
  have hnorm_sq :
      ∀ x : ℝ, ‖(x : ℂ) + z‖ ^ 2 = (x + z.re) ^ 2 + z.im ^ 2 := by
    intro x
    have h' : Complex.normSq ((x : ℂ) + z) =
        (x + z.re) * (x + z.re) + z.im * z.im := by
      simp [Complex.normSq_apply]
    have h'' : ‖(x : ℂ) + z‖ ^ 2 = Complex.normSq ((x : ℂ) + z) := by
      simpa using (Complex.sq_norm ((x : ℂ) + z))
    simpa [pow_two] using (h''.trans h')
  have hpow :
      ∀ x : ℝ, (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ) = ‖(x : ℂ) + z‖ ^ 3 := by
    intro x
    have hbase : 0 ≤ ‖(x : ℂ) + z‖ ^ 2 := by positivity
    calc
      (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ)
          = (‖(x : ℂ) + z‖ ^ 2) ^ ((1 / 2 : ℝ) * (3 : ℝ)) := by ring_nf
      _ = ((‖(x : ℂ) + z‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
            simpa using
              (Real.rpow_mul (x := ‖(x : ℂ) + z‖ ^ 2) hbase (1 / 2 : ℝ) (3 : ℝ))
      _ = (Real.sqrt (‖(x : ℂ) + z‖ ^ 2)) ^ (3 : ℝ) := by
            simp [Real.sqrt_eq_rpow]
      _ = ‖(x : ℂ) + z‖ ^ (3 : ℝ) := by
            simp
      _ = ‖(x : ℂ) + z‖ ^ 3 := by
            simp
  have hrewrite :
      ∀ x : ℝ,
        1 / ‖(x : ℂ) + z‖ ^ 3 =
          1 / ((x + z.re) ^ 2 + z.im ^ 2) ^ (3 / 2 : ℝ) := by
    intro x
    calc
      1 / ‖(x : ℂ) + z‖ ^ 3
          = 1 / (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ) := by
              simp [hpow x]
      _ = 1 / ((x + z.re) ^ 2 + z.im ^ 2) ^ (3 / 2 : ℝ) := by
            simp [hnorm_sq x]
  have hkernel_eq :
      ∫ x in Set.Ioi (0 : ℝ), (1 / ‖(x : ℂ) + z‖ ^ 3) =
        1 / (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) := by
    have hbound := integral_kernel_eq (σ := z.re) (τ := z.im) hz
    simpa [hrewrite] using hbound
  have hkernel_ne :
      (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) ≠ 0 := by
    have hpos : 0 < Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      have hsq : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [hz]
      simpa using Real.sqrt_pos.mpr hsq
    have hpos2 : 0 < Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re := by
      nlinarith [hpos, hz]
    nlinarith [hpos, hpos2]
  have hkernel_integrable :
      Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 3))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    set c : ℝ :=
      1 / (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re))
    have hc : c ≠ 0 := by
      have : (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) ≠ 0 :=
        hkernel_ne
      simpa [c] using (one_div_ne_zero this)
    have hscaled :
        ∫ x in Set.Ioi (0 : ℝ), (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) = (1 : ℝ) := by
      calc
        ∫ x in Set.Ioi (0 : ℝ), (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3)
            = (1 / c : ℝ) * ∫ x in Set.Ioi (0 : ℝ), (1 / ‖(x : ℂ) + z‖ ^ 3) := by
                simp [MeasureTheory.integral_const_mul]
        _ = (1 / c : ℝ) * c := by
              simpa using (congrArg (fun t => (1 / c : ℝ) * t) hkernel_eq)
        _ = (1 : ℝ) := by
              field_simp [hc]
    have hscaled_int :
        Integrable (fun x : ℝ => (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3))
          (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
      exact MeasureTheory.integrable_of_integral_eq_one hscaled
    have hgi :
        Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 3))
          (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
      have hgi' := hscaled_int.smul c
      refine hgi'.congr ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have :
          c * (c⁻¹ * (‖(x : ℂ) + z‖ ^ 3)⁻¹) =
            (‖(x : ℂ) + z‖ ^ 3)⁻¹ := by
        field_simp [hc, mul_comm, mul_left_comm, mul_assoc]
      simpa [Pi.smul_apply, smul_eq_mul] using this
    exact hgi
  have hE_norm' :
      ‖E‖ ≤ ∫ x in Set.Ioi (0 : ℝ), (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
    have hle :
        ∀ᵐ x ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
          ‖(bernoulli2Diff x : ℂ) / (x + z) ^ 3‖
            ≤ (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
      exact Filter.Eventually.of_forall hF_bound
    have hgi :
        Integrable (fun x : ℝ => (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3))
          (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
      simpa using hkernel_integrable.smul (1 / 4 : ℝ)
    have hnorm :
        ‖E‖ = ‖∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (x + z) ^ 3‖ := by
      simp [hE, norm_neg]
    have h' :=
      (MeasureTheory.norm_integral_le_of_norm_le
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) hgi hle)
    simpa [hnorm] using h'
  have hkernel :
      ∫ x in Set.Ioi (0 : ℝ), (1 / ‖(x : ℂ) + z‖ ^ 3)
        ≤ 1 / ‖z‖ ^ 2 := by
    have hnormsq : (z.re ^ 2 + z.im ^ 2) = ‖z‖ ^ 2 := by
      have h1 : (z.re ^ 2 + z.im ^ 2) = Complex.normSq z := by
        simp [Complex.normSq_apply, pow_two]
      have h2 : Complex.normSq z = ‖z‖ ^ 2 := by
        simpa using (Complex.normSq_eq_norm_sq z)
      exact h1.trans h2
    have hbound := integral_kernel_bound (σ := z.re) (τ := z.im) hz
    simpa [hrewrite, hnormsq] using hbound
  have hE_final :
      ‖E‖ ≤ 1 / (4 * ‖z‖ ^ 2) := by
    have hE_norm'' :
        ‖E‖ ≤ ∫ x in Set.Ioi (0 : ℝ), (4⁻¹ : ℝ) * (‖(x : ℂ) + z‖ ^ 3)⁻¹ := by
      simpa [one_div] using hE_norm'
    have hkernel' :
        ∫ x in Set.Ioi (0 : ℝ), (‖(x : ℂ) + z‖ ^ 3)⁻¹ ≤ (‖z‖ ^ 2)⁻¹ := by
      simpa [one_div] using hkernel
    have h' :
        (4⁻¹ : ℝ) * ∫ x in Set.Ioi (0 : ℝ), (‖(x : ℂ) + z‖ ^ 3)⁻¹
          ≤ (4⁻¹ : ℝ) * (‖z‖ ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hkernel' (by norm_num : (0 : ℝ) ≤ (4⁻¹ : ℝ))
    refine le_trans hE_norm'' ?_
    calc
      ∫ x in Set.Ioi (0 : ℝ), (4⁻¹ : ℝ) * (‖(x : ℂ) + z‖ ^ 3)⁻¹
          = (4⁻¹ : ℝ) * ∫ x in Set.Ioi (0 : ℝ), (‖(x : ℂ) + z‖ ^ 3)⁻¹ := by
              simp [MeasureTheory.integral_const_mul]
      _ ≤ (4⁻¹ : ℝ) * (‖z‖ ^ 2)⁻¹ := h'
      _ = 1 / (4 * ‖z‖ ^ 2) := by
            field_simp
  simpa [E] using hE_final

lemma re_digamma_remainder_bound_stieltjes (z : ℂ) (hz : 0 < z.re) :
    |(Q3.digamma z).re - Real.log ‖z‖ + z.re / (2 * ‖z‖^2)| ≤
      1 / (4 * ‖z‖^2) := by
  classical
  set E : ℂ := Q3.digamma z - Complex.log z + (1 / (2 : ℂ)) * z⁻¹
  have hE : E = -∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (x + z) ^ 3 := by
    simpa [E] using (digamma_stieltjes_identity z hz)
  have hB : ∀ x : ℝ, ‖(bernoulli2Diff x : ℂ)‖ ≤ (1 / 4 : ℝ) := by
    intro x
    have hb0 : 0 ≤ bernoulli2Diff x := (bernoulli2Diff_bounds x).1
    have hb1 : bernoulli2Diff x ≤ (1 / 4 : ℝ) := (bernoulli2Diff_bounds x).2
    have habs : |bernoulli2Diff x| = bernoulli2Diff x := by simp [abs_of_nonneg hb0]
    have hnorm : ‖(bernoulli2Diff x : ℂ)‖ = |bernoulli2Diff x| := by
      simp
    simpa [hnorm, habs] using hb1
  have hF_bound :
      ∀ x : ℝ,
        ‖(bernoulli2Diff x : ℂ) / (x + z) ^ 3‖
          ≤ (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
    intro x
    have hnorm_pow : ‖(x + z : ℂ) ^ 3‖ = ‖(x + z : ℂ)‖ ^ 3 := by
      simp [norm_pow]
    have hpos : 0 ≤ ‖(x : ℂ) + z‖ ^ 3 := by positivity
    calc
      ‖(bernoulli2Diff x : ℂ) / (x + z) ^ 3‖
          = ‖(bernoulli2Diff x : ℂ)‖ / ‖(x + z : ℂ) ^ 3‖ := by
            simp
      _ = ‖(bernoulli2Diff x : ℂ)‖ / ‖(x : ℂ) + z‖ ^ 3 := by
            simp [hnorm_pow]
      _ ≤ (1 / 4 : ℝ) / ‖(x : ℂ) + z‖ ^ 3 := by
            exact (div_le_div_of_nonneg_right (hB x) hpos)
      _ = (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
            field_simp
  -- Build integrability for the kernel via scaling of the exact integral value.
  have hnorm_sq :
      ∀ x : ℝ, ‖(x : ℂ) + z‖ ^ 2 = (x + z.re) ^ 2 + z.im ^ 2 := by
    intro x
    have h' : Complex.normSq ((x : ℂ) + z) =
        (x + z.re) * (x + z.re) + z.im * z.im := by
      simp [Complex.normSq_apply]
    have h'' : ‖(x : ℂ) + z‖ ^ 2 = Complex.normSq ((x : ℂ) + z) := by
      simpa using (Complex.sq_norm ((x : ℂ) + z))
    simpa [pow_two] using (h''.trans h')
  have hpow :
      ∀ x : ℝ, (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ) = ‖(x : ℂ) + z‖ ^ 3 := by
    intro x
    have hbase : 0 ≤ ‖(x : ℂ) + z‖ ^ 2 := by positivity
    have hpos : 0 ≤ ‖(x : ℂ) + z‖ := by positivity
    calc
      (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ)
          = (‖(x : ℂ) + z‖ ^ 2) ^ ((1 / 2 : ℝ) * (3 : ℝ)) := by ring_nf
      _ = ((‖(x : ℂ) + z‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
            simpa using
              (Real.rpow_mul (x := ‖(x : ℂ) + z‖ ^ 2) hbase (1 / 2 : ℝ) (3 : ℝ))
      _ = (Real.sqrt (‖(x : ℂ) + z‖ ^ 2)) ^ (3 : ℝ) := by
            simp [Real.sqrt_eq_rpow]
      _ = ‖(x : ℂ) + z‖ ^ (3 : ℝ) := by
            simp
      _ = ‖(x : ℂ) + z‖ ^ 3 := by
            simp
  have hrewrite :
      ∀ x : ℝ,
        1 / ‖(x : ℂ) + z‖ ^ 3 =
          1 / ((x + z.re) ^ 2 + z.im ^ 2) ^ (3 / 2 : ℝ) := by
    intro x
    calc
      1 / ‖(x : ℂ) + z‖ ^ 3
          = 1 / (‖(x : ℂ) + z‖ ^ 2) ^ (3 / 2 : ℝ) := by
              simp [hpow x]
      _ = 1 / ((x + z.re) ^ 2 + z.im ^ 2) ^ (3 / 2 : ℝ) := by
            simp [hnorm_sq x]
  have hkernel_eq :
      ∫ x in Set.Ioi (0 : ℝ), (1 / ‖(x : ℂ) + z‖ ^ 3) =
        1 / (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) := by
    have hbound := integral_kernel_eq (σ := z.re) (τ := z.im) hz
    simpa [hrewrite] using hbound
  have hkernel_ne :
      (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) ≠ 0 := by
    have hpos : 0 < Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      have hsq : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [hz]
      simpa using Real.sqrt_pos.mpr hsq
    have hpos2 : 0 < Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re := by
      nlinarith [hpos, hz]
    nlinarith [hpos, hpos2]
  have hkernel_integrable :
      Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 3))
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    set c : ℝ :=
      1 / (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re))
    have hc : c ≠ 0 := by
      have : (Real.sqrt (z.re ^ 2 + z.im ^ 2) * (Real.sqrt (z.re ^ 2 + z.im ^ 2) + z.re)) ≠ 0 :=
        hkernel_ne
      simpa [c] using (one_div_ne_zero this)
    have hscaled :
        ∫ x in Set.Ioi (0 : ℝ), (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) = (1 : ℝ) := by
      calc
        ∫ x in Set.Ioi (0 : ℝ), (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3)
            = (1 / c : ℝ) * ∫ x in Set.Ioi (0 : ℝ), (1 / ‖(x : ℂ) + z‖ ^ 3) := by
                simp [MeasureTheory.integral_const_mul]
        _ = (1 / c : ℝ) * c := by
              simpa using (congrArg (fun t => (1 / c : ℝ) * t) hkernel_eq)
        _ = (1 : ℝ) := by
              field_simp [hc]
    have hscaled_int :
        Integrable (fun x : ℝ => (1 / c : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3))
          (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
      exact MeasureTheory.integrable_of_integral_eq_one hscaled
    have hgi :
        Integrable (fun x : ℝ => (1 / ‖(x : ℂ) + z‖ ^ 3))
          (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
      have hgi' := hscaled_int.smul c
      refine hgi'.congr ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have :
          c * (c⁻¹ * (‖(x : ℂ) + z‖ ^ 3)⁻¹) =
            (‖(x : ℂ) + z‖ ^ 3)⁻¹ := by
        field_simp [hc, mul_comm, mul_left_comm, mul_assoc]
      simpa [Pi.smul_apply, smul_eq_mul] using this
    exact hgi
  have hE_norm' :
      ‖E‖ ≤ ∫ x in Set.Ioi (0 : ℝ), (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
    have hle :
        ∀ᵐ x ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
          ‖(bernoulli2Diff x : ℂ) / (x + z) ^ 3‖
            ≤ (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3) := by
      exact Filter.Eventually.of_forall hF_bound
    have hgi :
        Integrable (fun x : ℝ => (1 / 4 : ℝ) * (1 / ‖(x : ℂ) + z‖ ^ 3))
          (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
      simpa using hkernel_integrable.smul (1 / 4 : ℝ)
    have hnorm :
        ‖E‖ = ‖∫ x in Set.Ioi (0 : ℝ), (bernoulli2Diff x : ℂ) / (x + z) ^ 3‖ := by
      simp [hE, norm_neg]
    have h' :=
      (MeasureTheory.norm_integral_le_of_norm_le
        (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) hgi hle)
    simpa [hnorm] using h'
  have hkernel :
      ∫ x in Set.Ioi (0 : ℝ), (1 / ‖(x : ℂ) + z‖ ^ 3)
        ≤ 1 / ‖z‖ ^ 2 := by
    have hnormsq : (z.re ^ 2 + z.im ^ 2) = ‖z‖ ^ 2 := by
      have h1 : (z.re ^ 2 + z.im ^ 2) = Complex.normSq z := by
        simp [Complex.normSq_apply, pow_two]
      have h2 : Complex.normSq z = ‖z‖ ^ 2 := by
        simpa using (Complex.normSq_eq_norm_sq z)
      exact h1.trans h2
    have hbound := integral_kernel_bound (σ := z.re) (τ := z.im) hz
    simpa [hrewrite, hnormsq] using hbound
  have hE_final :
      ‖E‖ ≤ 1 / (4 * ‖z‖ ^ 2) := by
    have hE_norm'' :
        ‖E‖ ≤ ∫ x in Set.Ioi (0 : ℝ), (4⁻¹ : ℝ) * (‖(x : ℂ) + z‖ ^ 3)⁻¹ := by
      simpa [one_div] using hE_norm'
    have hkernel' :
        ∫ x in Set.Ioi (0 : ℝ), (‖(x : ℂ) + z‖ ^ 3)⁻¹ ≤ (‖z‖ ^ 2)⁻¹ := by
      simpa [one_div] using hkernel
    have h' :
        (4⁻¹ : ℝ) * ∫ x in Set.Ioi (0 : ℝ), (‖(x : ℂ) + z‖ ^ 3)⁻¹
          ≤ (4⁻¹ : ℝ) * (‖z‖ ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hkernel' (by norm_num : (0 : ℝ) ≤ (4⁻¹ : ℝ))
    refine le_trans hE_norm'' ?_
    calc
      ∫ x in Set.Ioi (0 : ℝ), (4⁻¹ : ℝ) * (‖(x : ℂ) + z‖ ^ 3)⁻¹
          = (4⁻¹ : ℝ) * ∫ x in Set.Ioi (0 : ℝ), (‖(x : ℂ) + z‖ ^ 3)⁻¹ := by
              simp [MeasureTheory.integral_const_mul]
      _ ≤ (4⁻¹ : ℝ) * (‖z‖ ^ 2)⁻¹ := h'
      _ = 1 / (4 * ‖z‖ ^ 2) := by
            field_simp
  have hlog : (Complex.log z).re = Real.log ‖z‖ := by
    simp [Complex.log_re]
  have hinv : (z⁻¹).re = z.re / Complex.normSq z := by
    simp [Complex.inv_re]
  have hnormsq : Complex.normSq z = ‖z‖ ^ 2 := by
    simp [Complex.normSq_eq_norm_sq]
  have hRe :
      E.re = (Q3.digamma z).re - Real.log ‖z‖ + z.re / (2 * ‖z‖ ^ 2) := by
    have hhalf : ((1 / (2 : ℂ)) * z⁻¹).re = (1 / 2 : ℝ) * (z⁻¹).re := by
      simp
    have hdiv : (1 / (2 : ℂ)) * z⁻¹ = (1 / (2 * z) : ℂ) := by
      field_simp [mul_comm, mul_left_comm, mul_assoc]
    calc
      E.re
          = (Q3.digamma z).re - (Complex.log z).re + ((1 / (2 : ℂ)) * z⁻¹).re := by
            simp [E, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      _ = (Q3.digamma z).re - Real.log ‖z‖ + (1 / 2 : ℝ) * (z⁻¹).re := by
            simp [hlog, add_comm, add_assoc, sub_eq_add_neg]
      _ = (Q3.digamma z).re - Real.log ‖z‖ + z.re / (2 * ‖z‖ ^ 2) := by
            simp [hinv, hnormsq, mul_comm, mul_assoc, div_eq_mul_inv]
  have hRe_abs :
      |(Q3.digamma z).re - Real.log ‖z‖ + z.re / (2 * ‖z‖ ^ 2)| ≤ ‖E‖ := by
    simpa [hRe] using (RCLike.abs_re_le_norm E)
  exact le_trans hRe_abs hE_final

end Q3
