import Q3.Basic.Defs
import Q3.Proofs.PSD_BSplineAnalyticModel
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

noncomputable section

open MeasureTheory
open scoped BigOperators
open scoped ComplexConjugate

namespace Q3
namespace PSDpd

/-!
Concrete centered cardinal B-spline objects for Step 32F.

`PSD_BSplineAnalyticModel` proves the generic translated/scaled bump
transform and correlation identities.  This file introduces the actual
centered cardinal B-spline bump used by the PSD-pd finite blocks.

The closed-form analytic facts are intentionally left as explicit theorem
targets, not assumed:

* the sinc/sinh-power transform profile;
* the autocorrelation identity
  `r_k(x)=b_{2k+1}(s_k*x)/c_k`;
* positivity/nonzero facts for the normalization constants.
-/

/--
Truncated positive-part power.

For `n = 0` this uses the strict step convention.  Boundary values are
irrelevant for the integral identities, and the strict convention avoids the
spurious `0^0 = 1` endpoint contribution.
-/
def positivePartPower (n : ℕ) (x : ℝ) : ℝ :=
  if 0 < x then x ^ n else 0

@[simp] theorem positivePartPower_of_pos
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    positivePartPower n x = x ^ n := by
  simp [positivePartPower, hx]

@[simp] theorem positivePartPower_of_nonpos
    (n : ℕ) {x : ℝ} (hx : ¬ 0 < x) :
    positivePartPower n x = 0 := by
  simp [positivePartPower, hx]

@[simp] theorem positivePartPower_zero (x : ℝ) :
    positivePartPower 0 x = if 0 < x then 1 else 0 := by
  by_cases hx : 0 < x
  · simp [positivePartPower, hx]
  · simp [positivePartPower, hx]

/-- Positive-degree truncated powers agree with the continuous max-power
model. -/
theorem positivePartPower_succ_eq_max (n : ℕ) (x : ℝ) :
    positivePartPower (n + 1) x = (max x 0) ^ (n + 1) := by
  by_cases hx : 0 < x
  · have hmax : max x 0 = x := max_eq_left hx.le
    simp [positivePartPower, hx, hmax]
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hmax : max x 0 = 0 := max_eq_right hxle
    simp [positivePartPower, hx, hmax]

/-- Positive-degree truncated powers are continuous. -/
theorem continuous_positivePartPower_succ (n : ℕ) :
    Continuous (positivePartPower (n + 1)) := by
  rw [show positivePartPower (n + 1) = fun x : ℝ => (max x 0) ^ (n + 1) by
    funext x
    exact positivePartPower_succ_eq_max n x]
  exact (continuous_id.max continuous_const).pow (n + 1)

/-- The strict degree-zero truncated power is measurable. -/
theorem measurable_positivePartPower_zero : Measurable (positivePartPower 0) := by
  simpa [positivePartPower_zero, Set.mem_Ioi] using
    (Measurable.ite (p := fun x : ℝ => 0 < x) measurableSet_Ioi
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ)))
      (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ))))

/-- The strict degree-zero truncated power is interval-integrable. -/
theorem intervalIntegrable_positivePartPower_zero (a b : ℝ) :
    IntervalIntegrable (positivePartPower 0) volume a b := by
  have hle :
      ∀ {u v : ℝ}, u ≤ v →
        IntervalIntegrable (positivePartPower 0) volume u v := by
    intro u v huv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1)
      measure_Ioc_lt_top.ne ?_ ?_
    · exact measurable_positivePartPower_zero.aestronglyMeasurable
    · filter_upwards with x
      simp [positivePartPower_zero]
      split <;> norm_num
  by_cases hab : a ≤ b
  · exact hle hab
  · exact (hle (le_of_not_ge hab)).symm

/-- Every truncated positive-part power is interval-integrable. -/
theorem intervalIntegrable_positivePartPower (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (positivePartPower k) volume a b := by
  cases k with
  | zero =>
      exact intervalIntegrable_positivePartPower_zero a b
  | succ k =>
      exact (continuous_positivePartPower_succ k).intervalIntegrable a b

/-- Away from the kink at zero, the normalized next truncated power has
derivative equal to the current truncated power. -/
theorem hasDerivAt_positivePartPower_succ_div_off_zero
    (k : ℕ) {x : ℝ} (hx0 : x ≠ 0) :
    HasDerivAt
      (fun y : ℝ => positivePartPower (k + 1) y / (k + 1 : ℝ))
      (positivePartPower k x)
      x := by
  have hkne : (k + 1 : ℝ) ≠ 0 := by positivity
  by_cases hx : 0 < x
  · have heq :
        (fun y : ℝ => positivePartPower (k + 1) y / (k + 1 : ℝ))
          =ᶠ[nhds x]
        (fun y : ℝ => y ^ (k + 1) / (k + 1 : ℝ)) := by
      filter_upwards [(isOpen_Ioi.mem_nhds hx)] with y hy
      have hypos : 0 < y := hy
      simp [positivePartPower, hypos]
    have hpoly :
        HasDerivAt
          (fun y : ℝ => y ^ (k + 1) / (k + 1 : ℝ))
          (x ^ k) x := by
      have h := (hasDerivAt_pow (k + 1) x).div_const (k + 1 : ℝ)
      have hpowexp : k + 1 - 1 = k := by omega
      have hderiv :
          ((↑k + 1 : ℝ) * x ^ k / (↑k + 1 : ℝ)) = x ^ k := by
        field_simp [hkne]
      simpa [hpowexp, hderiv] using h
    have htarget := hpoly.congr_of_eventuallyEq heq
    simpa [positivePartPower, hx] using htarget
  · have hxlt : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
    have heq :
        (fun y : ℝ => positivePartPower (k + 1) y / (k + 1 : ℝ))
          =ᶠ[nhds x]
        (fun _ : ℝ => 0) := by
      filter_upwards [(isOpen_Iio.mem_nhds hxlt)] with y hy
      have hylt : y < 0 := hy
      have hy' : ¬ 0 < y := by linarith
      simp [positivePartPower, hy']
    have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x :=
      hasDerivAt_const x 0
    have htarget := hconst.congr_of_eventuallyEq heq
    have hxnonpos : ¬ 0 < x := by linarith
    simpa [positivePartPower, hxnonpos] using htarget

/-- Oriented interval integral of a truncated positive-part power. -/
theorem positivePartPower_intervalIntegral
    (k : ℕ) (a b : ℝ) :
    ∫ u in a..b, positivePartPower k u =
      (positivePartPower (k + 1) b - positivePartPower (k + 1) a) /
        (k + 1 : ℝ) := by
  have hftc :=
    MeasureTheory.integral_eq_of_hasDerivAt_off_countable
      (f := fun y : ℝ => positivePartPower (k + 1) y / (k + 1 : ℝ))
      (f' := positivePartPower k)
      (a := a) (b := b) (s := ({0} : Set ℝ))
      (Set.countable_singleton 0)
      ?hcont ?hderiv ?hint
  · simpa [sub_div] using hftc
  · exact ((continuous_positivePartPower_succ k).div_const (k + 1 : ℝ)).continuousOn
  · intro x hx
    exact hasDerivAt_positivePartPower_succ_div_off_zero k (by simpa using hx.2)
  · exact intervalIntegrable_positivePartPower k a b

/-- Centered interval form used in the box-convolution recurrence. -/
theorem positivePartPower_interval_integral_centered
    (k : ℕ) (x A : ℝ) :
    ∫ y in Set.Icc (-(1/2 : ℝ)) (1/2 : ℝ),
      positivePartPower k (x - y + A)
    =
    (positivePartPower (k + 1) (x + A + 1/2)
      - positivePartPower (k + 1) (x + A - 1/2)) /
      (k + 1 : ℝ) := by
  calc
    ∫ y in Set.Icc (-(1/2 : ℝ)) (1/2 : ℝ),
      positivePartPower k (x - y + A)
        = ∫ y in Set.Ioc (-(1/2 : ℝ)) (1/2 : ℝ),
            positivePartPower k (x - y + A) := by
            rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ y in (-(1/2 : ℝ))..(1/2 : ℝ),
            positivePartPower k (x - y + A) := by
            rw [intervalIntegral.integral_of_le]
            norm_num
    _ = ∫ u in x + A - 1/2..x + A + 1/2,
            positivePartPower k u := by
            have h := intervalIntegral.integral_comp_sub_left
              (f := positivePartPower k)
              (a := (-(1/2 : ℝ))) (b := (1/2 : ℝ)) (d := x + A)
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    _ = _ := by
            rw [positivePartPower_intervalIntegral]

/-- Shifted oriented interval integral of a truncated positive-part power. -/
theorem positivePartPower_intervalIntegral_add
    (k : ℕ) (a b C : ℝ) :
    ∫ y in a..b, positivePartPower k (y + C) =
      (positivePartPower (k + 1) (b + C)
        - positivePartPower (k + 1) (a + C)) / (k + 1 : ℝ) := by
  calc
    ∫ y in a..b, positivePartPower k (y + C)
        = ∫ u in a + C..b + C, positivePartPower k u := by
            exact intervalIntegral.integral_comp_add_right
              (f := positivePartPower k) (a := a) (b := b) (d := C)
    _ = _ := by
            rw [positivePartPower_intervalIntegral]

/-- Shifted/subtracted oriented interval integral form used by the spline
finite-sum expansion. -/
theorem positivePartPower_intervalIntegral_add_sub
    (k : ℕ) (a b C D : ℝ) :
    ∫ y in a..b, positivePartPower k (y + C - D) =
      (positivePartPower (k + 1) (b + C - D)
        - positivePartPower (k + 1) (a + C - D)) / (k + 1 : ℝ) := by
  simpa [sub_eq_add_neg, add_assoc] using
    positivePartPower_intervalIntegral_add k a b (C - D)

/--
Centered cardinal B-spline in truncated-power form.

This matches the Step 12/Python formula:

`b_n(x) = 1/n! * sum_j (-1)^j * choose(n+1,j) *
  (x + (n+1)/2 - j)_+^n`.
-/
def centeredCardinalBSpline (degree : ℕ) (x : ℝ) : ℝ :=
  ((Nat.factorial degree : ℝ)⁻¹) *
    ((Finset.range (degree + 2)).sum fun j =>
      ((-1 : ℝ) ^ j) *
        (Nat.choose (degree + 1) j : ℝ) *
          positivePartPower degree
            (x + (((degree + 1 : ℕ) : ℝ) / 2) - (j : ℝ)))

/-- Degree-zero centered cardinal B-spline, with endpoint convention fixed by
`positivePartPower`. -/
theorem centeredCardinalBSpline_zero (x : ℝ) :
    centeredCardinalBSpline 0 x =
      positivePartPower 0 (x + (1 / 2 : ℝ))
        - positivePartPower 0 (x - (1 / 2 : ℝ)) := by
  norm_num [centeredCardinalBSpline, Finset.sum_range_succ]
  by_cases h0 : (0 : ℝ) < x + (1 / 2 : ℝ)
  · by_cases hx : (1 / 2 : ℝ) < x
    · have hx' : (1 : ℝ) < x + (1 / 2 : ℝ) := by linarith
      simp only [h0, hx, hx', if_true]
      ring
    · have hx' : ¬ (1 : ℝ) < x + (1 / 2 : ℝ) := by linarith
      simp only [h0, hx, hx', if_true, if_false]
      ring
  · by_cases hx : (1 / 2 : ℝ) < x
    · have hx' : (1 : ℝ) < x + (1 / 2 : ℝ) := by linarith
      simp only [h0, hx, hx', if_true, if_false]
      ring
    · have hx' : ¬ (1 : ℝ) < x + (1 / 2 : ℝ) := by linarith
      simp only [h0, hx, hx', if_false]
      ring

/-- The centered box spline \(b_0=\mathbf 1_{[-1/2,1/2]}\), with the same
endpoint convention as `centeredCardinalBSpline 0`. -/
def centeredBoxSpline (x : ℝ) : ℝ :=
  positivePartPower 0 (x + (1 / 2 : ℝ))
    - positivePartPower 0 (x - (1 / 2 : ℝ))

/-- The strict centered-box convention is exactly the half-open indicator
`Ico (x-1/2) (x+1/2)` after reflection around `x`. -/
theorem centeredBoxSpline_sub_eq_indicator_Ico (x y : ℝ) :
    centeredBoxSpline (x - y) =
      (Set.Ico (x - 1/2) (x + 1/2)).indicator (fun _ : ℝ => (1 : ℝ)) y := by
  unfold centeredBoxSpline
  simp only [positivePartPower_zero, Set.indicator]
  by_cases hA : 0 < x - y + 2⁻¹
  · by_cases hB : 2⁻¹ < x - y
    · have hC : ¬ (x ≤ y + 2⁻¹ ∧ y < x + 2⁻¹) := by
        intro h
        linarith
      simp [hA, hB, hC]
    · have hC : x ≤ y + 2⁻¹ ∧ y < x + 2⁻¹ := by
        constructor <;> linarith
      simp [hA, hB, hC]
  · have hB : ¬ (2⁻¹ : ℝ) < x - y := by linarith
    have hC : ¬ (x ≤ y + 2⁻¹ ∧ y < x + 2⁻¹) := by
      intro h
      linarith
    simp [hA, hB, hC]

/-- The strict centered box itself is the half-open indicator
`Ioc (-1/2) (1/2)`. -/
theorem centeredBoxSpline_eq_indicator_Ioc (x : ℝ) :
    centeredBoxSpline x =
      (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (fun _ : ℝ => (1 : ℝ)) x := by
  unfold centeredBoxSpline
  simp only [positivePartPower_zero, Set.indicator]
  by_cases hleft : -(1 / 2 : ℝ) < x
  · by_cases hright : x ≤ (1 / 2 : ℝ)
    · have hA : 0 < x + (1 / 2 : ℝ) := by linarith
      have hB : ¬ 0 < x - (1 / 2 : ℝ) := by linarith
      have hmem : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) :=
        ⟨hleft, hright⟩
      norm_num [hA, hB, hmem]
    · have hA : 0 < x + (1 / 2 : ℝ) := by linarith
      have hB : 0 < x - (1 / 2 : ℝ) := by linarith
      have hmem : x ∉ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
        intro h
        exact hright h.2
      norm_num [hA, hB, hmem]
  · have hA : ¬ 0 < x + (1 / 2 : ℝ) := by linarith
    have hB : ¬ 0 < x - (1 / 2 : ℝ) := by linarith
    have hmem : x ∉ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      intro h
      exact hleft h.1
    norm_num [hA, hB, hmem]

/-- The truncated-power degree-zero spline is the centered box. -/
theorem centeredCardinalBSpline_zero_eq_centeredBoxSpline :
    centeredCardinalBSpline 0 = centeredBoxSpline := by
  funext x
  exact centeredCardinalBSpline_zero x

/--
Left endpoint value for the strict centered-box convention.

This records the measure-zero endpoint convention explicitly.  It is harmless
for integral identities, but it means the degree-zero box is not pointwise even.
-/
@[simp] theorem centeredBoxSpline_neg_half :
    centeredBoxSpline (-(1 / 2 : ℝ)) = 0 := by
  simp [centeredBoxSpline]

/--
Right endpoint value for the strict centered-box convention.

Together with `centeredBoxSpline_neg_half`, this shows that the box is only
even up to a null endpoint convention.
-/
@[simp] theorem centeredBoxSpline_pos_half :
    centeredBoxSpline (1 / 2 : ℝ) = 1 := by
  simp [centeredBoxSpline]

/-- The PSD-pd packet scale `s_k=(k+1)/2`. -/
def bsplineScale (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) / 2)

theorem bsplineScale_pos (k : ℕ) : 0 < bsplineScale k := by
  unfold bsplineScale
  positivity

theorem bsplineScale_ne_zero (k : ℕ) : bsplineScale k ≠ 0 :=
  (bsplineScale_pos k).ne'

/-- Degree of the autocorrelation spline `b_{2k+1}`. -/
def bsplineAutocorrDegree (k : ℕ) : ℕ :=
  2 * k + 1

/-- Normalizing constant `c_k=b_{2k+1}(0)`. -/
def bsplineAutocorrNorm (k : ℕ) : ℝ :=
  centeredCardinalBSpline (bsplineAutocorrDegree k) 0

/--
The concrete scaled centered cardinal B-spline bump

`eta_k(x)=sqrt(s_k/c_k) * b_k(s_k*x)`.
-/
def centeredBSplineEta (k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (bsplineScale k / bsplineAutocorrNorm k) *
    centeredCardinalBSpline k (bsplineScale k * x)

/--
The expected autocorrelation profile

`r_k(x)=b_{2k+1}(s_k*x)/c_k`.
-/
def centeredBSplineR (k : ℕ) (x : ℝ) : ℝ :=
  centeredCardinalBSpline (bsplineAutocorrDegree k) (bsplineScale k * x) /
    bsplineAutocorrNorm k

/-- Evenness target for the concrete centered cardinal B-spline. -/
def CenteredCardinalBSplineEven (k : ℕ) : Prop :=
  ∀ x : ℝ, centeredCardinalBSpline k (-x) = centeredCardinalBSpline k x

/--
The current strict endpoint convention prevents degree-zero pointwise evenness.

The B-spline integral identities still see the centered box as even almost
everywhere, so later convolution arguments should use an a.e./integral
evenness form rather than pointwise evenness at degree zero.
-/
theorem not_CenteredCardinalBSplineEven_zero :
    ¬ CenteredCardinalBSplineEven 0 := by
  intro h
  have hbad := h (1 / 2 : ℝ)
  rw [centeredCardinalBSpline_zero_eq_centeredBoxSpline] at hbad
  norm_num at hbad

/--
Away from the two endpoints, the strict centered-box convention is even.

This is the pointwise core behind the later a.e. evenness theorem.
-/
theorem centeredBoxSpline_neg_eq_of_ne_endpoints
    {t : ℝ}
    (hleft : t ≠ -(1 / 2 : ℝ))
    (hright : t ≠ (1 / 2 : ℝ)) :
    centeredBoxSpline (-t) = centeredBoxSpline t := by
  unfold centeredBoxSpline
  simp only [positivePartPower_zero]
  by_cases hlt : t < -(1 / 2 : ℝ)
  · have h1 : 0 < -t + (1 / 2 : ℝ) := by linarith
    have h2 : 0 < -t - (1 / 2 : ℝ) := by linarith
    have h3 : ¬ 0 < t + (1 / 2 : ℝ) := by linarith
    have h4 : ¬ 0 < t - (1 / 2 : ℝ) := by linarith
    simp only [h1, h2, h3, h4, if_true, if_false]
    ring
  · have hge : -(1 / 2 : ℝ) < t := by
      have hle : -(1 / 2 : ℝ) ≤ t := by linarith
      exact lt_of_le_of_ne hle hleft.symm
    by_cases hmid : t < (1 / 2 : ℝ)
    · have h1 : 0 < -t + (1 / 2 : ℝ) := by linarith
      have h2 : ¬ 0 < -t - (1 / 2 : ℝ) := by linarith
      have h3 : 0 < t + (1 / 2 : ℝ) := by linarith
      have h4 : ¬ 0 < t - (1 / 2 : ℝ) := by linarith
      simp only [h1, h2, h3, h4, if_true, if_false]
    · have hgt : (1 / 2 : ℝ) < t := by
        have hle : (1 / 2 : ℝ) ≤ t := by linarith
        exact lt_of_le_of_ne hle hright.symm
      have h1 : ¬ 0 < -t + (1 / 2 : ℝ) := by linarith
      have h2 : ¬ 0 < -t - (1 / 2 : ℝ) := by linarith
      have h3 : 0 < t + (1 / 2 : ℝ) := by linarith
      have h4 : 0 < t - (1 / 2 : ℝ) := by linarith
      simp only [h1, h2, h3, h4, if_true, if_false]
      ring

/-- Evenness of `b_k` transfers to evenness of the scaled normalized bump. -/
theorem centeredBSplineEta_even_of_cardinal_even
    (k : ℕ) (heven : CenteredCardinalBSplineEven k) :
    ∀ y : ℝ, centeredBSplineEta k (-y) = centeredBSplineEta k y := by
  intro y
  unfold centeredBSplineEta
  have harg : bsplineScale k * (-y) = -(bsplineScale k * y) := by ring
  rw [harg, heven]

/-- Actual generic-bump correlation profile of `eta_k`. -/
def centeredBSplineCorrelationProfile (k : ℕ) (x : ℝ) : ℝ :=
  realBumpCorrelationProfile (centeredBSplineEta k) x

/-- Real convolution with the sign convention `(f*g)(x)=∫ y, f y * g (x-y)`. -/
def realConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f y * g (x - y)

/-- Convolution with the strict centered box is integration over the translated
unit interval.  The proof uses the exact half-open convention and then removes
endpoint differences by the no-atoms property of Lebesgue measure. -/
theorem realConvolution_centeredBoxSpline (f : ℝ → ℝ) (x : ℝ) :
    realConvolution f centeredBoxSpline x =
      ∫ y in x - 1/2..x + 1/2, f y := by
  unfold realConvolution
  calc
    ∫ y : ℝ, f y * centeredBoxSpline (x - y)
        = ∫ y : ℝ, (Set.Ico (x - 1/2) (x + 1/2)).indicator f y := by
            apply integral_congr_ae
            filter_upwards with y
            rw [centeredBoxSpline_sub_eq_indicator_Ico]
            simp [Set.indicator]
    _ = ∫ y in Set.Ico (x - 1/2) (x + 1/2), f y := by
            rw [MeasureTheory.integral_indicator measurableSet_Ico]
    _ = ∫ y in Set.Ioc (x - 1/2) (x + 1/2), f y := by
            exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ico_ae_eq_Ioc
    _ = ∫ y in x - 1/2..x + 1/2, f y := by
            rw [intervalIntegral.integral_of_le]
            linarith

/-- The strict centered box is Lebesgue-integrable. -/
theorem centeredBoxSpline_integrable : Integrable centeredBoxSpline := by
  have hI :
      Integrable
        ((Set.Ico (-(1/2 : ℝ)) (1/2 : ℝ)).indicator
          (fun _ : ℝ => (1 : ℝ))) := by
    rw [integrable_indicator_iff measurableSet_Ico]
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ico_lt_top.ne ?_ ?_
    · exact (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).aestronglyMeasurable
    · filter_upwards with x
      simp
  have hfun :
      (fun y : ℝ => centeredBoxSpline (-y)) =
        (Set.Ico (-(1/2 : ℝ)) (1/2 : ℝ)).indicator
          (fun _ : ℝ => (1 : ℝ)) := by
    funext y
    simpa using centeredBoxSpline_sub_eq_indicator_Ico (0 : ℝ) y
  have hneg : Integrable (fun y : ℝ => centeredBoxSpline (-y)) := by
    simpa [hfun] using hI
  simpa using hneg.comp_neg

/--
Right-box associativity for `realConvolution` under the exact Fubini
integrability condition needed on the kernel over the finite box interval.

This is deliberately narrower than global convolution associativity: the only
special right factor is `centeredBoxSpline`, and the proof uses
`realConvolution_centeredBoxSpline` plus `intervalIntegral_integral_swap`.
-/
theorem realConvolution_assoc_right_centeredBox_of_integrable_kernel
    (f g : ℝ → ℝ) (x : ℝ)
    (h_int :
      Integrable
        (Function.uncurry fun u t : ℝ => f t * g (u - t))
        (volume.prod volume)) :
    realConvolution f (realConvolution g centeredBoxSpline) x =
      realConvolution (realConvolution f g) centeredBoxSpline x := by
  have h_int_restrict :
      Integrable
        (Function.uncurry fun u t : ℝ => f t * g (u - t))
        ((volume.restrict (Set.uIoc (x - 1/2) (x + 1/2))).prod volume) := by
    have hprod := Measure.prod_restrict
      (μ := volume) (ν := volume)
      (s := Set.uIoc (x - 1/2) (x + 1/2)) (t := (Set.univ : Set ℝ))
    rw [Measure.restrict_univ] at hprod
    rw [hprod]
    exact h_int.mono_measure Measure.restrict_le_self
  calc
    realConvolution f (realConvolution g centeredBoxSpline) x
        = ∫ t : ℝ, f t * ∫ u in x - 1/2..x + 1/2, g (u - t) := by
            change (∫ t : ℝ, f t * realConvolution g centeredBoxSpline (x - t)) = _
            apply integral_congr_ae
            filter_upwards with t
            rw [realConvolution_centeredBoxSpline]
            congr 1
            have hshift := (intervalIntegral.integral_comp_sub_right
              (f := g) (a := x - 1/2) (b := x + 1/2) (d := t)).symm
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] at hshift ⊢
    _ = ∫ t : ℝ, ∫ u in x - 1/2..x + 1/2, f t * g (u - t) := by
            apply integral_congr_ae
            filter_upwards with t
            rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in x - 1/2..x + 1/2, ∫ t : ℝ, f t * g (u - t) := by
            exact (MeasureTheory.intervalIntegral_integral_swap
              (f := fun u t : ℝ => f t * g (u - t)) h_int_restrict).symm
    _ = realConvolution (realConvolution f g) centeredBoxSpline x := by
            rw [realConvolution_centeredBoxSpline]
            apply intervalIntegral.integral_congr
            intro u hu
            rfl

/--
Convolution-power model of the centered cardinal B-splines.

This is the proof-friendly version:
`convPower 0 = centered box` and
`convPower (k+1)=convPower k * centered box`.
-/
def centeredCardinalBSplineConvPower : ℕ → ℝ → ℝ
  | 0 => centeredBoxSpline
  | k + 1 => realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline

/-- The convolution-power model starts with the centered box. -/
theorem centeredCardinalBSplineConvPower_zero :
    centeredCardinalBSplineConvPower 0 = centeredBoxSpline := rfl

/-- One convolution step in the convolution-power model. -/
theorem centeredCardinalBSplineConvPower_succ (k : ℕ) :
    centeredCardinalBSplineConvPower (k + 1) =
      realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline := rfl

/-- Every centered-box convolution power is Lebesgue-integrable. -/
theorem centeredCardinalBSplineConvPower_integrable
    (k : ℕ) :
    Integrable (centeredCardinalBSplineConvPower k) := by
  induction k with
  | zero =>
      simpa [centeredCardinalBSplineConvPower_zero] using centeredBoxSpline_integrable
  | succ k ih =>
      change Integrable (realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline)
      have hconv := MeasureTheory.Integrable.integrable_convolution
        (L := ContinuousLinearMap.mul ℝ ℝ)
        (μ := volume)
        ih
        centeredBoxSpline_integrable
      simpa [realConvolution, MeasureTheory.convolution_def] using hconv

/--
Bridge target between the executable truncated-power spline and the
proof-friendly convolution-power spline.
-/
def CenteredCardinalBSplineMatchesConvPower (k : ℕ) : Prop :=
  ∀ x : ℝ,
    centeredCardinalBSpline k x = centeredCardinalBSplineConvPower k x

/--
Almost-everywhere bridge between the executable truncated-power spline and
the proof-friendly convolution-power spline.

This is the right strength for identities used under the autocorrelation
integral.  Pointwise agreement is still needed when a spline value appears
outside an integral.
-/
def CenteredCardinalBSplineMatchesConvPowerAE (k : ℕ) : Prop :=
  centeredCardinalBSpline k =ᵐ[volume] centeredCardinalBSplineConvPower k

/--
Shifted a.e. agreement between the truncated-power and convolution-power
models.

This is the exact form needed for the reflected second factor in
`realConvolution ... (-x)`.
-/
def CenteredCardinalBSplineMatchesConvPowerShiftAE (k : ℕ) : Prop :=
  ∀ x : ℝ, ∀ᵐ y : ℝ,
    centeredCardinalBSpline k (-(y + x)) =
      centeredCardinalBSplineConvPower k (-(y + x))

/-- The bridge target is closed in degree zero. -/
theorem CenteredCardinalBSplineMatchesConvPower_zero :
    CenteredCardinalBSplineMatchesConvPower 0 := by
  intro x
  rw [centeredCardinalBSpline_zero_eq_centeredBoxSpline]
  rfl

/-- Degree-zero a.e. agreement follows from the pointwise degree-zero bridge. -/
theorem CenteredCardinalBSplineMatchesConvPowerAE_zero :
    CenteredCardinalBSplineMatchesConvPowerAE 0 := by
  filter_upwards with x
  exact CenteredCardinalBSplineMatchesConvPower_zero x

/-- Degree-zero shifted a.e. agreement follows from pointwise agreement. -/
theorem CenteredCardinalBSplineMatchesConvPowerShiftAE_zero :
    CenteredCardinalBSplineMatchesConvPowerShiftAE 0 := by
  intro x
  filter_upwards with y
  exact CenteredCardinalBSplineMatchesConvPower_zero (-(y + x))

/-- Pointwise agreement implies a.e. agreement. -/
theorem CenteredCardinalBSplineMatchesConvPowerAE_of_pointwise
    (k : ℕ)
    (hmatch : CenteredCardinalBSplineMatchesConvPower k) :
    CenteredCardinalBSplineMatchesConvPowerAE k := by
  filter_upwards with x
  exact hmatch x

/-- Pointwise agreement implies shifted a.e. agreement. -/
theorem CenteredCardinalBSplineMatchesConvPowerShiftAE_of_pointwise
    (k : ℕ)
    (hmatch : CenteredCardinalBSplineMatchesConvPower k) :
    CenteredCardinalBSplineMatchesConvPowerShiftAE k := by
  intro x
  filter_upwards with y
  exact hmatch (-(y + x))

/--
Self-convolution theorem target in the convolution-power model.

This is the pure convolution-algebra statement:
the `(k+1)`-fold box convolution convolved with itself is the `(2k+2)`-fold
box convolution, hence degree `2*k+1`.
-/
def CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm (k : ℕ) : Prop :=
  ∀ x : ℝ,
    realConvolution
        (centeredCardinalBSplineConvPower k)
        (centeredCardinalBSplineConvPower k) (-x) =
      centeredCardinalBSplineConvPower (bsplineAutocorrDegree k) x

/--
Associativity target for the real convolution convention used in this file.

This is separated from the B-spline algebra because the analytic proof lives in
measure theory/Fubini bookkeeping, while the spline-degree arithmetic below is
purely formal once associativity is available.
-/
def RealConvolutionAssociative : Prop :=
  ∀ f g h : ℝ → ℝ, ∀ x : ℝ,
    realConvolution f (realConvolution g h) x =
      realConvolution (realConvolution f g) h x

/--
Full convolution-power law for the proof-friendly centered-cardinal model:

`F_k * F_l = F_{k+l+1}`.
-/
def CenteredCardinalBSplineConvPowerConvolutionLaw : Prop :=
  ∀ k l : ℕ, ∀ x : ℝ,
    realConvolution
        (centeredCardinalBSplineConvPower k)
        (centeredCardinalBSplineConvPower l) x =
      centeredCardinalBSplineConvPower (k + l + 1) x

/--
The exact local associativity step needed to prove the convolution-power law.

This is much narrower than global associativity of `realConvolution`: it only
asks to reassociate a rightmost convolution with the centered box inside the
B-spline convolution-power family.
-/
def CenteredCardinalBSplineConvPowerAssocRightBox : Prop :=
  ∀ k l : ℕ, ∀ x : ℝ,
    realConvolution
        (centeredCardinalBSplineConvPower k)
        (realConvolution (centeredCardinalBSplineConvPower l) centeredBoxSpline) x =
      realConvolution
        (realConvolution
          (centeredCardinalBSplineConvPower k)
          (centeredCardinalBSplineConvPower l))
        centeredBoxSpline x

/--
The convolution-power law follows formally from associativity.

This is the degree-bookkeeping core of `b_k*b_l=b_{k+l+1}` for the
convolution-defined spline family.
-/
theorem CenteredCardinalBSplineConvPowerConvolutionLaw_of_assoc
    (hassoc : RealConvolutionAssociative) :
    CenteredCardinalBSplineConvPowerConvolutionLaw := by
  intro k l
  induction l with
  | zero =>
      intro x
      simpa using
        (show
          realConvolution
              (centeredCardinalBSplineConvPower k)
              centeredBoxSpline x =
            centeredCardinalBSplineConvPower (k + 1) x from rfl)
  | succ l ih =>
      intro x
      calc
        realConvolution
            (centeredCardinalBSplineConvPower k)
            (centeredCardinalBSplineConvPower (l + 1)) x
            =
          realConvolution
            (realConvolution
              (centeredCardinalBSplineConvPower k)
              (centeredCardinalBSplineConvPower l))
            centeredBoxSpline x := by
              rw [centeredCardinalBSplineConvPower_succ]
              exact hassoc
                (centeredCardinalBSplineConvPower k)
                (centeredCardinalBSplineConvPower l)
                centeredBoxSpline x
        _ =
          realConvolution
            (centeredCardinalBSplineConvPower (k + l + 1))
            centeredBoxSpline x := by
              have ihfun :
                  realConvolution
                      (centeredCardinalBSplineConvPower k)
                      (centeredCardinalBSplineConvPower l) =
                    centeredCardinalBSplineConvPower (k + l + 1) := by
                funext t
                exact ih t
              rw [ihfun]
        _ = centeredCardinalBSplineConvPower ((k + l + 1) + 1) x := by
              rfl
        _ = centeredCardinalBSplineConvPower (k + (l + 1) + 1) x := by
              have hnat : (k + l + 1) + 1 = k + (l + 1) + 1 := by
                omega
              rw [hnat]

/--
The B-spline convolution-power law follows from the local right-box
associativity step.

This is the preferred Step 32F theorem shape: it avoids the global
`RealConvolutionAssociative` target and isolates exactly the induction step
needed by the family `B_{n+1}=B_n*b_0`.
-/
theorem CenteredCardinalBSplineConvPowerConvolutionLaw_of_assocRightBox
    (hbox : CenteredCardinalBSplineConvPowerAssocRightBox) :
    CenteredCardinalBSplineConvPowerConvolutionLaw := by
  intro k l
  induction l with
  | zero =>
      intro x
      simpa using
        (show
          realConvolution
              (centeredCardinalBSplineConvPower k)
              centeredBoxSpline x =
            centeredCardinalBSplineConvPower (k + 1) x from rfl)
  | succ l ih =>
      intro x
      calc
        realConvolution
            (centeredCardinalBSplineConvPower k)
            (centeredCardinalBSplineConvPower (l + 1)) x
            =
          realConvolution
            (centeredCardinalBSplineConvPower k)
            (realConvolution (centeredCardinalBSplineConvPower l) centeredBoxSpline) x := by
              rw [centeredCardinalBSplineConvPower_succ]
        _ =
          realConvolution
            (realConvolution
              (centeredCardinalBSplineConvPower k)
              (centeredCardinalBSplineConvPower l))
            centeredBoxSpline x := by
              exact hbox k l x
        _ =
          realConvolution
            (centeredCardinalBSplineConvPower (k + l + 1))
            centeredBoxSpline x := by
              have ihfun :
                  realConvolution
                      (centeredCardinalBSplineConvPower k)
                      (centeredCardinalBSplineConvPower l) =
                    centeredCardinalBSplineConvPower (k + l + 1) := by
                funext t
                exact ih t
              rw [ihfun]
        _ = centeredCardinalBSplineConvPower ((k + l + 1) + 1) x := by
              rfl
        _ = centeredCardinalBSplineConvPower (k + (l + 1) + 1) x := by
              have hnat : (k + l + 1) + 1 = k + (l + 1) + 1 := by
                omega
              rw [hnat]

/-- The local right-box associativity step is closed for centered-box
convolution powers. -/
theorem CenteredCardinalBSplineConvPowerAssocRightBox_all :
    CenteredCardinalBSplineConvPowerAssocRightBox := by
  intro k l x
  refine realConvolution_assoc_right_centeredBox_of_integrable_kernel
    (centeredCardinalBSplineConvPower k)
    (centeredCardinalBSplineConvPower l)
    x ?_
  have hglobal := MeasureTheory.Integrable.convolution_integrand
    (L := ContinuousLinearMap.mul ℝ ℝ)
    (μ := volume) (ν := volume)
    (centeredCardinalBSplineConvPower_integrable k)
    (centeredCardinalBSplineConvPower_integrable l)
  simpa [Function.uncurry, ContinuousLinearMap.mul_apply] using hglobal

/-- Closed convolution-power degree-additivity law for the proof-friendly
centered-cardinal model. -/
theorem CenteredCardinalBSplineConvPowerConvolutionLaw_all :
    CenteredCardinalBSplineConvPowerConvolutionLaw :=
  CenteredCardinalBSplineConvPowerConvolutionLaw_of_assocRightBox
    CenteredCardinalBSplineConvPowerAssocRightBox_all

/-- Evenness target for the convolution-power model. -/
def CenteredCardinalBSplineConvPowerEven (k : ℕ) : Prop :=
  ∀ x : ℝ,
    centeredCardinalBSplineConvPower k (-x) =
      centeredCardinalBSplineConvPower k x

/--
The full convolution-power law gives the self-convolution closed form once the
target autocorrelation degree is even.
-/
theorem CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_convolutionLaw
    (k : ℕ)
    (hevenAuto : CenteredCardinalBSplineConvPowerEven (bsplineAutocorrDegree k))
    (hlaw : CenteredCardinalBSplineConvPowerConvolutionLaw) :
    CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k := by
  intro x
  calc
    realConvolution
        (centeredCardinalBSplineConvPower k)
        (centeredCardinalBSplineConvPower k) (-x)
        =
      centeredCardinalBSplineConvPower (k + k + 1) (-x) := by
        exact hlaw k k (-x)
    _ =
      centeredCardinalBSplineConvPower (bsplineAutocorrDegree k) (-x) := by
        congr 1
        unfold bsplineAutocorrDegree
        omega
    _ =
      centeredCardinalBSplineConvPower (bsplineAutocorrDegree k) x := by
        exact hevenAuto x

/--
Associativity plus evenness of the target convolution power closes the
convolution-power self-convolution target.
-/
theorem CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_assoc
    (k : ℕ)
    (hassoc : RealConvolutionAssociative)
    (hevenAuto : CenteredCardinalBSplineConvPowerEven (bsplineAutocorrDegree k)) :
    CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k :=
  CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_convolutionLaw
    k hevenAuto
      (CenteredCardinalBSplineConvPowerConvolutionLaw_of_assoc hassoc)

/--
Unnormalized base autocorrelation closed form for the centered cardinal spline.

This is the exact classical B-spline theorem
`corr(b_k)(x)=b_{2k+1}(x)`.
-/
def CenteredCardinalBSplineBaseCorrelationClosedForm (k : ℕ) : Prop :=
  ∀ x : ℝ,
    realBumpCorrelationProfile (centeredCardinalBSpline k) x =
      centeredCardinalBSpline (bsplineAutocorrDegree k) x

/--
Unnormalized self-convolution closed form for the centered cardinal spline.

With our convolution convention this is the sign-sensitive version needed for
the autocorrelation profile.
-/
def CenteredCardinalBSplineSelfConvolutionClosedForm (k : ℕ) : Prop :=
  ∀ x : ℝ,
    realConvolution (centeredCardinalBSpline k) (centeredCardinalBSpline k) (-x) =
      centeredCardinalBSpline (bsplineAutocorrDegree k) x

/--
Transfer self-convolution from the proof-friendly convolution-power model to
the executable truncated-power model.
-/
theorem CenteredCardinalBSplineSelfConvolutionClosedForm_of_convPower
    (k : ℕ)
    (hmatch : CenteredCardinalBSplineMatchesConvPower k)
    (hmatchAuto : CenteredCardinalBSplineMatchesConvPower (bsplineAutocorrDegree k))
    (hconv : CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k) :
    CenteredCardinalBSplineSelfConvolutionClosedForm k := by
  intro x
  unfold realConvolution
  calc
    (∫ y : ℝ, centeredCardinalBSpline k y *
        centeredCardinalBSpline k (-x - y))
        = ∫ y : ℝ, centeredCardinalBSplineConvPower k y *
            centeredCardinalBSplineConvPower k (-x - y) := by
            apply integral_congr_ae
            filter_upwards with y
            rw [hmatch y, hmatch (-x - y)]
    _ = centeredCardinalBSplineConvPower (bsplineAutocorrDegree k) x := by
            simpa [realConvolution] using hconv x
    _ = centeredCardinalBSpline (bsplineAutocorrDegree k) x := by
            exact (hmatchAuto x).symm

/--
Transfer self-convolution from the convolution-power model to the
truncated-power model using only a.e. agreement for the two factors under the
integral.

The target degree still needs pointwise agreement because it is evaluated at a
single point `x`, outside the integral.
-/
theorem CenteredCardinalBSplineSelfConvolutionClosedForm_of_convPowerAE
    (k : ℕ)
    (hmatchAE : CenteredCardinalBSplineMatchesConvPowerAE k)
    (hmatchShiftAE : CenteredCardinalBSplineMatchesConvPowerShiftAE k)
    (hmatchAuto : CenteredCardinalBSplineMatchesConvPower (bsplineAutocorrDegree k))
    (hconv : CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k) :
    CenteredCardinalBSplineSelfConvolutionClosedForm k := by
  intro x
  unfold realConvolution
  calc
    (∫ y : ℝ, centeredCardinalBSpline k y *
        centeredCardinalBSpline k (-x - y))
        = ∫ y : ℝ, centeredCardinalBSplineConvPower k y *
            centeredCardinalBSplineConvPower k (-x - y) := by
            apply integral_congr_ae
            have hleft :
                ∀ᵐ y : ℝ,
                  centeredCardinalBSpline k y =
                    centeredCardinalBSplineConvPower k y := hmatchAE
            have hright :
                ∀ᵐ y : ℝ,
                  centeredCardinalBSpline k (-x - y) =
                    centeredCardinalBSplineConvPower k (-x - y) := by
              filter_upwards [hmatchShiftAE x] with y hy
              have harg : -x - y = -(y + x) := by ring
              simpa [harg] using hy
            filter_upwards [hleft, hright] with y hyLeft hyRight
            rw [hyLeft, hyRight]
    _ = centeredCardinalBSplineConvPower (bsplineAutocorrDegree k) x := by
            simpa [realConvolution] using hconv x
    _ = centeredCardinalBSpline (bsplineAutocorrDegree k) x := by
            exact (hmatchAuto x).symm

/--
Autocorrelation is convolution at the reflected argument for even functions.

This is the sign bookkeeping needed before applying the cardinal B-spline
convolution-power identity.
-/
theorem realBumpCorrelationProfile_eq_realConvolution_neg_of_even
    (f : ℝ → ℝ) (hf_even : ∀ y : ℝ, f (-y) = f y) (x : ℝ) :
    realBumpCorrelationProfile f x = realConvolution f f (-x) := by
  unfold realBumpCorrelationProfile realConvolution
  apply integral_congr_ae
  filter_upwards with y
  have harg : (-x - y) = -(y + x) := by ring
  calc
    f y * f (y + x)
        = f y * f (-(y + x)) := by rw [hf_even (y + x)]
    _ = f y * f (-x - y) := by rw [harg]

/--
Shifted a.e. evenness, exactly in the form needed to turn autocorrelation into
convolution under the integral.

This is weaker than pointwise evenness and is the right shape for the
degree-zero centered-box endpoint convention.
-/
def RealFunctionShiftEvenAE (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ∀ᵐ y : ℝ, f (-(y + x)) = f (y + x)

/--
The strict centered box is shifted-even almost everywhere.

The only failures are the two translated endpoints `y+x=±1/2`, both null
sets.  This is the degree-zero base fact for the endpoint-safe route.
-/
theorem centeredBoxSpline_shiftEvenAE :
    RealFunctionShiftEvenAE centeredBoxSpline := by
  intro x
  have hleft :
      ∀ᵐ y : ℝ, y ≠ (-(1 / 2 : ℝ)) - x :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
      (MeasureTheory.measure_singleton ((-(1 / 2 : ℝ)) - x))
  have hright :
      ∀ᵐ y : ℝ, y ≠ (1 / 2 : ℝ) - x :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
      (MeasureTheory.measure_singleton ((1 / 2 : ℝ) - x))
  filter_upwards [hleft, hright] with y hyLeft hyRight
  apply centeredBoxSpline_neg_eq_of_ne_endpoints
  · intro hy
    apply hyLeft
    linarith
  · intro hy
    apply hyRight
    linarith

/--
Autocorrelation is convolution at the reflected argument under shifted a.e.
evenness.

This is the integral-safe replacement for pointwise evenness when endpoint
conventions differ on null sets.
-/
theorem realBumpCorrelationProfile_eq_realConvolution_neg_of_shiftEvenAE
    (f : ℝ → ℝ) (hf_even : RealFunctionShiftEvenAE f) (x : ℝ) :
    realBumpCorrelationProfile f x = realConvolution f f (-x) := by
  unfold realBumpCorrelationProfile realConvolution
  apply integral_congr_ae
  filter_upwards [hf_even x] with y hy
  have harg : (-x - y) = -(y + x) := by ring
  calc
    f y * f (y + x)
        = f y * f (-(y + x)) := by rw [← hy]
    _ = f y * f (-x - y) := by rw [harg]

/--
The user-facing convolution-power route:

evenness of \(b_k\) plus the unnormalized self-convolution identity implies
the unnormalized base autocorrelation identity.
-/
theorem CenteredCardinalBSplineBaseCorrelationClosedForm_of_even_selfConvolution
    (k : ℕ)
    (heven : CenteredCardinalBSplineEven k)
    (hconv : CenteredCardinalBSplineSelfConvolutionClosedForm k) :
    CenteredCardinalBSplineBaseCorrelationClosedForm k := by
  intro x
  rw [realBumpCorrelationProfile_eq_realConvolution_neg_of_even
    (centeredCardinalBSpline k) heven x]
  exact hconv x

/-- Shifted a.e. evenness target for the centered cardinal spline. -/
def CenteredCardinalBSplineShiftEvenAE (k : ℕ) : Prop :=
  RealFunctionShiftEvenAE (centeredCardinalBSpline k)

/-- Degree-zero shifted a.e. evenness follows from the endpoint-safe box fact. -/
theorem CenteredCardinalBSplineShiftEvenAE_zero :
    CenteredCardinalBSplineShiftEvenAE 0 := by
  change RealFunctionShiftEvenAE (centeredCardinalBSpline 0)
  rw [centeredCardinalBSpline_zero_eq_centeredBoxSpline]
  exact centeredBoxSpline_shiftEvenAE

/--
Integral-safe route from self-convolution to base autocorrelation.

This avoids the false degree-zero pointwise-evenness requirement caused by the
strict box endpoint convention.
-/
theorem CenteredCardinalBSplineBaseCorrelationClosedForm_of_shiftEvenAE_selfConvolution
    (k : ℕ)
    (hevenAE : CenteredCardinalBSplineShiftEvenAE k)
    (hconv : CenteredCardinalBSplineSelfConvolutionClosedForm k) :
    CenteredCardinalBSplineBaseCorrelationClosedForm k := by
  intro x
  rw [realBumpCorrelationProfile_eq_realConvolution_neg_of_shiftEvenAE
    (centeredCardinalBSpline k) hevenAE x]
  exact hconv x

/--
Exact remaining convolution theorem for the concrete normalized bump.

Together with `realBumpCorrelationProfile_eq_realConvolution_neg_of_even`,
this is equivalent to `CenteredBSplineAutocorrelationClosedForm`.
-/
def CenteredBSplineSelfConvolutionClosedForm (k : ℕ) : Prop :=
  ∀ x : ℝ,
    realConvolution (centeredBSplineEta k) (centeredBSplineEta k) (-x) =
      centeredBSplineR k x

/--
The exact autocorrelation theorem still needed to close the prime-entry side of
Step 32F.
-/
def CenteredBSplineAutocorrelationClosedForm (k : ℕ) : Prop :=
  ∀ x : ℝ,
    centeredBSplineCorrelationProfile k x = centeredBSplineR k x

/--
Normalization/scaling reduction for the centered B-spline autocorrelation.

After this lemma, the only concrete B-spline theorem still needed for the
prime-side closed form is the unnormalized base identity

`corr(b_k)(x)=b_{2k+1}(x)`.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_baseCorrelation
    (k : ℕ)
    (hc_pos : 0 < bsplineAutocorrNorm k)
    (hbase : CenteredCardinalBSplineBaseCorrelationClosedForm k) :
    CenteredBSplineAutocorrelationClosedForm k := by
  intro x
  let s : ℝ := bsplineScale k
  let c : ℝ := bsplineAutocorrNorm k
  let b : ℝ → ℝ := centeredCardinalBSpline k
  let α : ℝ := Real.sqrt (s / c)
  have hs_pos : 0 < s := by
    simpa [s] using bsplineScale_pos k
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hc_ne : c ≠ 0 := by
    exact hc_pos.ne'
  have hsc_nonneg : 0 ≤ s / c := by
    exact div_nonneg hs_pos.le hc_pos.le
  have hα_sq : α * α = s / c := by
    calc
      α * α = α ^ 2 := by ring
      _ = s / c := by
        simpa [α] using Real.sq_sqrt hsc_nonneg
  let G : ℝ → ℝ := fun t => b t * b (t + s * x)
  have hmul :
      (∫ y : ℝ, b (s * y) * b (s * y + s * x)) =
        |s⁻¹| • (∫ t : ℝ, b t * b (t + s * x)) := by
    calc
      (∫ y : ℝ, b (s * y) * b (s * y + s * x))
          = ∫ y : ℝ, G (s * y) := by
              apply integral_congr_ae
              filter_upwards with y
              simp [G]
      _ = |s⁻¹| • (∫ t : ℝ, G t) := by
              exact MeasureTheory.Measure.integral_comp_mul_left G s
      _ = |s⁻¹| • (∫ t : ℝ, b t * b (t + s * x)) := by
              rfl
  calc
    centeredBSplineCorrelationProfile k x
        = ∫ y : ℝ, (α * b (s * y)) * (α * b (s * y + s * x)) := by
            unfold centeredBSplineCorrelationProfile realBumpCorrelationProfile
            simp [centeredBSplineEta, α, b, s, c, mul_add]
    _ = (α * α) * (∫ y : ℝ, b (s * y) * b (s * y + s * x)) := by
            rw [← MeasureTheory.integral_const_mul]
            apply integral_congr_ae
            filter_upwards with y
            ring
    _ = (s / c) * (|s⁻¹| * (∫ t : ℝ, b t * b (t + s * x))) := by
            rw [hα_sq, hmul]
            rfl
    _ = (1 / c) * realBumpCorrelationProfile b (s * x) := by
            unfold realBumpCorrelationProfile
            have habs : |s⁻¹| = s⁻¹ := by
              rw [abs_of_pos]
              exact inv_pos.mpr hs_pos
            rw [habs]
            field_simp [hs_ne, hc_ne]
    _ = (1 / c) * centeredCardinalBSpline (bsplineAutocorrDegree k) (s * x) := by
            rw [hbase (s * x)]
    _ = centeredBSplineR k x := by
            simp [centeredBSplineR, s, c]
            ring

/--
The self-convolution closed form implies the autocorrelation closed form once
the concrete bump is even.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_selfConvolution
    (k : ℕ)
    (heta_even : ∀ y : ℝ, centeredBSplineEta k (-y) = centeredBSplineEta k y)
    (hconv : CenteredBSplineSelfConvolutionClosedForm k) :
    CenteredBSplineAutocorrelationClosedForm k := by
  intro x
  rw [centeredBSplineCorrelationProfile,
    realBumpCorrelationProfile_eq_realConvolution_neg_of_even
      (centeredBSplineEta k) heta_even x]
  exact hconv x

/--
Concrete two-lemma route to the autocorrelation closed form:

1. the centered cardinal spline is even;
2. the normalized bump has the expected self-convolution profile.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_cardinalEven_selfConvolution
    (k : ℕ)
    (heven : CenteredCardinalBSplineEven k)
    (hconv : CenteredBSplineSelfConvolutionClosedForm k) :
    CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_of_selfConvolution
    k (centeredBSplineEta_even_of_cardinal_even k heven) hconv

/--
Canonical Step 32F route for the prime-side profile:

1. prove \(0<c_k\);
2. prove centered-cardinal evenness;
3. prove the centered-cardinal self-convolution profile.

Then the normalized autocorrelation closed form follows.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_cardinalEven_cardinalSelfConvolution
    (k : ℕ)
    (hc_pos : 0 < bsplineAutocorrNorm k)
    (heven : CenteredCardinalBSplineEven k)
    (hconv : CenteredCardinalBSplineSelfConvolutionClosedForm k) :
    CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_of_baseCorrelation
    k hc_pos
      (CenteredCardinalBSplineBaseCorrelationClosedForm_of_even_selfConvolution
        k heven hconv)

/--
Integral-safe canonical Step 32F route:

1. prove \(0<c_k\);
2. prove shifted a.e. evenness of the centered-cardinal spline;
3. prove the centered-cardinal self-convolution profile.

Then the normalized autocorrelation closed form follows.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_cardinalShiftEvenAE_cardinalSelfConvolution
    (k : ℕ)
    (hc_pos : 0 < bsplineAutocorrNorm k)
    (hevenAE : CenteredCardinalBSplineShiftEvenAE k)
    (hconv : CenteredCardinalBSplineSelfConvolutionClosedForm k) :
    CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_of_baseCorrelation
    k hc_pos
      (CenteredCardinalBSplineBaseCorrelationClosedForm_of_shiftEvenAE_selfConvolution
        k hevenAE hconv)

/--
Fully factored convolution-power route to the normalized Step 32F
autocorrelation closed form.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_convPowerRoute
    (k : ℕ)
    (hc_pos : 0 < bsplineAutocorrNorm k)
    (heven : CenteredCardinalBSplineEven k)
    (hmatch : CenteredCardinalBSplineMatchesConvPower k)
    (hmatchAuto : CenteredCardinalBSplineMatchesConvPower (bsplineAutocorrDegree k))
    (hconv : CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k) :
    CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_of_cardinalEven_cardinalSelfConvolution
    k hc_pos heven
      (CenteredCardinalBSplineSelfConvolutionClosedForm_of_convPower
        k hmatch hmatchAuto hconv)

/--
Endpoint-safe convolution-power route to the normalized Step 32F
autocorrelation closed form.

Compared with `CenteredBSplineAutocorrelationClosedForm_of_convPowerRoute`,
the spline factors under the integral only require a.e./shifted-a.e.
agreement with the convolution-power model.  The autocorrelation degree still
requires pointwise agreement because it is evaluated at the external point
`x`.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute
    (k : ℕ)
    (hc_pos : 0 < bsplineAutocorrNorm k)
    (hevenAE : CenteredCardinalBSplineShiftEvenAE k)
    (hmatchAE : CenteredCardinalBSplineMatchesConvPowerAE k)
    (hmatchShiftAE : CenteredCardinalBSplineMatchesConvPowerShiftAE k)
    (hmatchAuto : CenteredCardinalBSplineMatchesConvPower (bsplineAutocorrDegree k))
    (hconv : CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k) :
    CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_of_cardinalShiftEvenAE_cardinalSelfConvolution
    k hc_pos hevenAE
      (CenteredCardinalBSplineSelfConvolutionClosedForm_of_convPowerAE
        k hmatchAE hmatchShiftAE hmatchAuto hconv)

/--
Endpoint-safe route when the executable/convolution-power agreement is already
available pointwise for the degree `k` factors.

The pointwise agreement is immediately downgraded to the a.e. and shifted-a.e.
forms needed under the autocorrelation integral.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_pointwise
    (k : ℕ)
    (hc_pos : 0 < bsplineAutocorrNorm k)
    (hevenAE : CenteredCardinalBSplineShiftEvenAE k)
    (hmatch : CenteredCardinalBSplineMatchesConvPower k)
    (hmatchAuto : CenteredCardinalBSplineMatchesConvPower (bsplineAutocorrDegree k))
    (hconv : CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k) :
    CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute
    k hc_pos hevenAE
      (CenteredCardinalBSplineMatchesConvPowerAE_of_pointwise k hmatch)
      (CenteredCardinalBSplineMatchesConvPowerShiftAE_of_pointwise k hmatch)
      hmatchAuto hconv

/--
Endpoint-safe route with the convolution-power self-convolution discharged
from associativity and target evenness.
-/
theorem CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_assoc
    (k : ℕ)
    (hc_pos : 0 < bsplineAutocorrNorm k)
    (hevenAE : CenteredCardinalBSplineShiftEvenAE k)
    (hmatch : CenteredCardinalBSplineMatchesConvPower k)
    (hmatchAuto : CenteredCardinalBSplineMatchesConvPower (bsplineAutocorrDegree k))
    (hassoc : RealConvolutionAssociative)
    (hevenAuto : CenteredCardinalBSplineConvPowerEven (bsplineAutocorrDegree k)) :
    CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_pointwise
    k hc_pos hevenAE hmatch hmatchAuto
      (CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_assoc
        k hassoc hevenAuto)

/-!
## Step 32F recurrence algebra

The next analytic target is the box-convolution recurrence
`b_{k+1}=b_k*b_0`.  Its finite-sum part is independent of integration:
after the positive-part interval integral produces `T_j - T_(j+1)`, Pascal's
identity converts the alternating degree-`k+1` sum into the degree-`k+2`
centered-cardinal sum.
-/

/--
Shift an alternating binomial sum by one index.

This is the boundary bookkeeping used by the Pascal telescope below.
-/
theorem centeredCardinalBSpline_altChoose_shift_sum
    (n : ℕ) (T : ℕ → ℝ) :
    ((Finset.range (n + 1)).sum fun j =>
      ((-1 : ℝ) ^ j) * (Nat.choose n j : ℝ) * T j)
    =
      T 0 -
        ((Finset.range (n + 1)).sum fun j =>
          ((-1 : ℝ) ^ j) * (Nat.choose n (j + 1) : ℝ) * T (j + 1)) := by
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ]
  simp [pow_succ, add_comm, mul_comm]
  abel

/--
Pascal telescope for the centered-cardinal recurrence.

Mathematically:

`sum_j (-1)^j choose(n,j) (T_j - T_(j+1))
 = sum_j (-1)^j choose(n+1,j) T_j`.
-/
theorem centeredCardinalBSpline_pascal_telescope
    (n : ℕ) (T : ℕ → ℝ) :
    ((Finset.range (n + 1)).sum fun j =>
      ((-1 : ℝ) ^ j) * (Nat.choose n j : ℝ) *
        (T j - T (j + 1)))
    =
    ((Finset.range (n + 2)).sum fun j =>
      ((-1 : ℝ) ^ j) * (Nat.choose (n + 1) j : ℝ) * T j) := by
  calc
    ((Finset.range (n + 1)).sum fun j =>
      ((-1 : ℝ) ^ j) * (Nat.choose n j : ℝ) *
        (T j - T (j + 1)))
        = ((Finset.range (n + 1)).sum fun j =>
            ((-1 : ℝ) ^ j) * (Nat.choose n j : ℝ) * T j)
          - ((Finset.range (n + 1)).sum fun j =>
            ((-1 : ℝ) ^ j) * (Nat.choose n j : ℝ) * T (j + 1)) := by
            simp [mul_sub, Finset.sum_sub_distrib]
    _ = T 0 -
          ((Finset.range (n + 1)).sum fun j =>
            ((-1 : ℝ) ^ j) * (Nat.choose n (j + 1) : ℝ) * T (j + 1))
          - ((Finset.range (n + 1)).sum fun j =>
            ((-1 : ℝ) ^ j) * (Nat.choose n j : ℝ) * T (j + 1)) := by
            rw [centeredCardinalBSpline_altChoose_shift_sum n T]
    _ = ((Finset.range (n + 2)).sum fun j =>
          ((-1 : ℝ) ^ j) * (Nat.choose (n + 1) j : ℝ) * T j) := by
          conv_rhs =>
            rw [Finset.sum_range_succ' (f := fun j =>
              ((-1 : ℝ) ^ j) * (Nat.choose (n + 1) j : ℝ) * T j) (n + 1)]
          simp [Nat.choose_succ_succ, pow_succ, add_comm, mul_comm]
          ring_nf
          rw [Finset.sum_add_distrib]
          ring_nf

/-- Expand the box convolution of a truncated-power centered cardinal spline
as a finite sum of positive-part interval integrals. -/
theorem centeredCardinalBSpline_conv_box_expanded
    (k : ℕ) (x : ℝ) :
    realConvolution (centeredCardinalBSpline k) centeredBoxSpline x =
      ((Nat.factorial k : ℝ)⁻¹) *
        ((Finset.range (k + 2)).sum fun j =>
          ((-1 : ℝ) ^ j) * (Nat.choose (k + 1) j : ℝ) *
            ∫ y in x - 1/2..x + 1/2,
              positivePartPower k
                (y + (((k + 1 : ℕ) : ℝ) / 2) - (j : ℝ))) := by
  rw [realConvolution_centeredBoxSpline]
  unfold centeredCardinalBSpline
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finset_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_const_mul]
  · intro j hj
    let C : ℝ := (((k + 1 : ℕ) : ℝ) / 2) - (j : ℝ)
    have hshift :
        IntervalIntegrable (fun y : ℝ => positivePartPower k (y + C)) volume
          (x - 1/2) (x + 1/2) := by
      have h := (intervalIntegrable_positivePartPower k
        ((x - 1/2) + C) ((x + 1/2) + C)).comp_add_right C
      simpa [C, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    simpa [C, sub_eq_add_neg, add_assoc] using
      hshift.const_mul (((-1 : ℝ) ^ j) * (Nat.choose (k + 1) j : ℝ))

/-- Apply the positive-part interval integral to the expanded box convolution,
producing exactly the `T_j - T_(j+1)` finite sum consumed by the Pascal
telescope. -/
theorem centeredCardinalBSpline_conv_box_after_integral
    (k : ℕ) (x : ℝ) :
    realConvolution (centeredCardinalBSpline k) centeredBoxSpline x =
      ((Nat.factorial (k + 1) : ℝ)⁻¹) *
        ((Finset.range (k + 2)).sum fun j =>
          ((-1 : ℝ) ^ j) * (Nat.choose (k + 1) j : ℝ) *
            (positivePartPower (k + 1)
                (x + (((k + 2 : ℕ) : ℝ) / 2) - (j : ℝ))
             - positivePartPower (k + 1)
                (x + (((k + 2 : ℕ) : ℝ) / 2) - ((j + 1 : ℕ) : ℝ)))) := by
  calc
    realConvolution (centeredCardinalBSpline k) centeredBoxSpline x
        =
      ((Nat.factorial k : ℝ)⁻¹) *
        ((Finset.range (k + 2)).sum fun j =>
          ((-1 : ℝ) ^ j) * (Nat.choose (k + 1) j : ℝ) *
            ((positivePartPower (k + 1)
                (x + (((k + 2 : ℕ) : ℝ) / 2) - (j : ℝ))
             - positivePartPower (k + 1)
                (x + (((k + 2 : ℕ) : ℝ) / 2) - ((j + 1 : ℕ) : ℝ))) /
              (k + 1 : ℝ))) := by
            rw [centeredCardinalBSpline_conv_box_expanded]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            rw [positivePartPower_intervalIntegral_add_sub]
            congr 1
            apply congrArg₂ (fun a b : ℝ => a - b)
            · apply congrArg (positivePartPower (k + 1))
              norm_num
              ring
            · apply congrArg (positivePartPower (k + 1))
              norm_num
              ring
    _ = _ := by
            rw [Nat.factorial_succ]
            norm_num
            simp [div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/-- The centered cardinal B-spline recurrence: convolving degree `k` with the
centered box gives degree `k+1`. -/
theorem centeredCardinalBSpline_succ_eq_conv_box
    (k : ℕ) :
    centeredCardinalBSpline (k + 1) =
      realConvolution (centeredCardinalBSpline k) centeredBoxSpline := by
  funext x
  rw [centeredCardinalBSpline_conv_box_after_integral]
  unfold centeredCardinalBSpline
  have htel := centeredCardinalBSpline_pascal_telescope
    (k + 1)
    (fun j => positivePartPower (k + 1)
      (x + (((k + 2 : ℕ) : ℝ) / 2) - (j : ℝ)))
  rw [← htel]

/-!
## Step 32F assembly layer

The next analytic brick is the recurrence
`b_{k+1}=b_k*b_0`.  The theorems below isolate the purely formal fallout of
that brick: once the recurrence is proved, pointwise agreement with the
convolution-power model follows by induction, and the endpoint-safe
autocorrelation closed form is reduced to the remaining positivity,
shifted-a.e. symmetry, and convolution-power self-convolution inputs.
-/

/--
If the truncated-power centered B-splines satisfy the box-convolution
recurrence, then they agree pointwise with the convolution-power model in every
degree.
-/
theorem CenteredCardinalBSplineMatchesConvPower_all_of_succ_eq_conv_box
    (hrec : ∀ k : ℕ,
      centeredCardinalBSpline (k + 1) =
        realConvolution (centeredCardinalBSpline k) centeredBoxSpline) :
    ∀ k : ℕ, CenteredCardinalBSplineMatchesConvPower k := by
  intro k
  induction k with
  | zero =>
      exact CenteredCardinalBSplineMatchesConvPower_zero
  | succ k ih =>
      intro x
      have hfun :
          centeredCardinalBSpline k =
            centeredCardinalBSplineConvPower k := by
        funext y
        exact ih y
      calc
        centeredCardinalBSpline (k + 1) x
            = realConvolution (centeredCardinalBSpline k) centeredBoxSpline x := by
                rw [hrec k]
        _ = realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline x := by
                rw [hfun]
        _ = centeredCardinalBSplineConvPower (k + 1) x := by
                rfl

/-- The truncated-power centered B-splines agree pointwise with the
convolution-power model in every degree. -/
theorem CenteredCardinalBSplineMatchesConvPower_all
    (k : ℕ) :
    CenteredCardinalBSplineMatchesConvPower k :=
  CenteredCardinalBSplineMatchesConvPower_all_of_succ_eq_conv_box
    centeredCardinalBSpline_succ_eq_conv_box
    k

/-- The all-degree pointwise bridge also gives the a.e. bridge used under
integrals. -/
theorem CenteredCardinalBSplineMatchesConvPowerAE_all
    (k : ℕ) :
    CenteredCardinalBSplineMatchesConvPowerAE k :=
  CenteredCardinalBSplineMatchesConvPowerAE_of_pointwise
    k
    (CenteredCardinalBSplineMatchesConvPower_all k)

/-- The all-degree pointwise bridge also gives shifted a.e. bridge used for the
reflected factor in the autocorrelation integral. -/
theorem CenteredCardinalBSplineMatchesConvPowerShiftAE_all
    (k : ℕ) :
    CenteredCardinalBSplineMatchesConvPowerShiftAE k :=
  CenteredCardinalBSplineMatchesConvPowerShiftAE_of_pointwise
    k
    (CenteredCardinalBSplineMatchesConvPower_all k)

/-- If `f` is even a.e., then its convolution with the strict centered box is
pointwise even.  The endpoint convention is absorbed by
`realConvolution_centeredBoxSpline`, so the proof is just the interval
substitution `y ↦ -y`. -/
theorem realConvolution_centeredBoxSpline_even_of_ae_even
    (f : ℝ → ℝ)
    (hf_even : ∀ᵐ t : ℝ, f (-t) = f t) :
    ∀ z : ℝ,
      realConvolution f centeredBoxSpline (-z) =
        realConvolution f centeredBoxSpline z := by
  intro z
  rw [realConvolution_centeredBoxSpline, realConvolution_centeredBoxSpline]
  calc
    ∫ y in -z - 1 / 2..-z + 1 / 2, f y
        = ∫ y in z - 1 / 2..z + 1 / 2, f (-y) := by
            have hneg := intervalIntegral.integral_comp_neg
              (f := f) (a := z - 1 / 2) (b := z + 1 / 2)
            rw [hneg]
            congr 2 <;> ring
    _ = ∫ y in z - 1 / 2..z + 1 / 2, f y := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [hf_even] with y hy hy_mem
            exact hy

/-- Convolution powers of the strict centered box are shifted-even a.e. in every
degree. -/
theorem centeredCardinalBSplineConvPower_shiftEvenAE_all
    (k : ℕ) :
    RealFunctionShiftEvenAE (centeredCardinalBSplineConvPower k) := by
  induction k with
  | zero =>
      rw [centeredCardinalBSplineConvPower_zero]
      exact centeredBoxSpline_shiftEvenAE
  | succ k ih =>
      intro x
      have h_even0 : ∀ᵐ t : ℝ,
          centeredCardinalBSplineConvPower k (-t) =
            centeredCardinalBSplineConvPower k t := by
        simpa using ih 0
      have hpoint := realConvolution_centeredBoxSpline_even_of_ae_even
        (centeredCardinalBSplineConvPower k) h_even0
      filter_upwards with y
      change realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline
          (-(y + x)) =
        realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline
          (y + x)
      exact hpoint (y + x)

/-- The executable truncated-power centered B-splines are shifted-even a.e. in
every degree. -/
theorem CenteredCardinalBSplineShiftEvenAE_all
    (k : ℕ) :
    CenteredCardinalBSplineShiftEvenAE k := by
  intro x
  filter_upwards [centeredCardinalBSplineConvPower_shiftEvenAE_all k x] with y hy
  rw [CenteredCardinalBSplineMatchesConvPower_all k (-(y + x))]
  rw [CenteredCardinalBSplineMatchesConvPower_all k (y + x)]
  exact hy

/-- Every positive convolution power is pointwise even. -/
theorem centeredCardinalBSplineConvPower_even_succ
    (k : ℕ) :
    CenteredCardinalBSplineConvPowerEven (k + 1) := by
  intro z
  change realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline (-z) =
    realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline z
  have h_even0 : ∀ᵐ t : ℝ,
      centeredCardinalBSplineConvPower k (-t) =
        centeredCardinalBSplineConvPower k t := by
    simpa using centeredCardinalBSplineConvPower_shiftEvenAE_all k 0
  exact realConvolution_centeredBoxSpline_even_of_ae_even
    (centeredCardinalBSplineConvPower k) h_even0 z

/-- The autocorrelation target convolution power has odd positive degree, hence
it is pointwise even. -/
theorem CenteredCardinalBSplineConvPowerEven_autocorrDegree
    (k : ℕ) :
    CenteredCardinalBSplineConvPowerEven (bsplineAutocorrDegree k) := by
  unfold bsplineAutocorrDegree
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    centeredCardinalBSplineConvPower_even_succ (2 * k)

/-- Once real convolution associativity is available, the convolution-power
self-convolution closed form is available in every degree. -/
theorem CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all_of_assoc
    (hassoc : RealConvolutionAssociative) :
    ∀ k : ℕ, CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k := by
  intro k
  exact
    CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_assoc
      k
      hassoc
      (CenteredCardinalBSplineConvPowerEven_autocorrDegree k)

/--
The narrower Step 32F self-convolution package.

This avoids making the global `RealConvolutionAssociative` theorem the live
frontier: it is enough to prove the convolution-power law on the B-spline
family itself.
-/
theorem CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all_of_convolutionLaw
    (hlaw : CenteredCardinalBSplineConvPowerConvolutionLaw) :
    ∀ k : ℕ, CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k := by
  intro k
  exact
    CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_convolutionLaw
      k
      (CenteredCardinalBSplineConvPowerEven_autocorrDegree k)
      hlaw

/-- The self-convolution package follows from the B-spline-local right-box
associativity step. -/
theorem CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all_of_assocRightBox
    (hbox : CenteredCardinalBSplineConvPowerAssocRightBox) :
    ∀ k : ℕ, CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k :=
  CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all_of_convolutionLaw
    (CenteredCardinalBSplineConvPowerConvolutionLaw_of_assocRightBox hbox)

/-- Closed self-convolution package for all centered-cardinal convolution
powers: `B_k * B_k = B_{2k+1}` in the endpoint-safe formulation. -/
theorem CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all :
    ∀ k : ℕ, CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k :=
  CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all_of_assocRightBox
    CenteredCardinalBSplineConvPowerAssocRightBox_all

/--
Package the endpoint-safe Step 32F autocorrelation closure once all remaining
degreewise inputs have been supplied.
-/
theorem CenteredBSplineAutocorrelationClosedForm_all_of_convPower_inputs
    (hc_pos : ∀ k : ℕ, 0 < bsplineAutocorrNorm k)
    (hevenAE : ∀ k : ℕ, CenteredCardinalBSplineShiftEvenAE k)
    (hmatch : ∀ k : ℕ, CenteredCardinalBSplineMatchesConvPower k)
    (hconv : ∀ k : ℕ, CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k) :
    ∀ k : ℕ, CenteredBSplineAutocorrelationClosedForm k := by
  intro k
  exact
    CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_pointwise
      k
      (hc_pos k)
      (hevenAE k)
      (hmatch k)
      (hmatch (bsplineAutocorrDegree k))
      (hconv k)

/--
Single assembly theorem for the current Step 32F route: the recurrence closes
the executable/convolution-power agreement, and the other degreewise inputs
then close the concrete normalized autocorrelation profile.
-/
theorem CenteredBSplineAutocorrelationClosedForm_all_of_recurrence_package
    (hrec : ∀ k : ℕ,
      centeredCardinalBSpline (k + 1) =
        realConvolution (centeredCardinalBSpline k) centeredBoxSpline)
    (hc_pos : ∀ k : ℕ, 0 < bsplineAutocorrNorm k)
    (hevenAE : ∀ k : ℕ, CenteredCardinalBSplineShiftEvenAE k)
    (hconv : ∀ k : ℕ, CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k) :
    ∀ k : ℕ, CenteredBSplineAutocorrelationClosedForm k := by
  exact
    CenteredBSplineAutocorrelationClosedForm_all_of_convPower_inputs
      hc_pos
      hevenAE
      (CenteredCardinalBSplineMatchesConvPower_all_of_succ_eq_conv_box hrec)
      hconv

/-- Current reduced Step 32F endpoint-safe package: after the recurrence work,
the remaining normalized autocorrelation closure is reduced to associativity of
`realConvolution` and positivity of the normalizer. -/
theorem CenteredBSplineAutocorrelationClosedForm_all_of_assoc_and_norm_pos
    (hassoc : RealConvolutionAssociative)
    (hc_pos : ∀ k : ℕ, 0 < bsplineAutocorrNorm k) :
    ∀ k : ℕ, CenteredBSplineAutocorrelationClosedForm k := by
  exact
    CenteredBSplineAutocorrelationClosedForm_all_of_convPower_inputs
      hc_pos
      CenteredCardinalBSplineShiftEvenAE_all
      CenteredCardinalBSplineMatchesConvPower_all
      (CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all_of_assoc
        hassoc)

/-- Same endpoint-safe closure, but with the live frontier narrowed from global
associativity to the B-spline convolution-power law. -/
theorem CenteredBSplineAutocorrelationClosedForm_all_of_convolutionLaw_and_norm_pos
    (hlaw : CenteredCardinalBSplineConvPowerConvolutionLaw)
    (hc_pos : ∀ k : ℕ, 0 < bsplineAutocorrNorm k) :
    ∀ k : ℕ, CenteredBSplineAutocorrelationClosedForm k := by
  exact
    CenteredBSplineAutocorrelationClosedForm_all_of_convPower_inputs
      hc_pos
      CenteredCardinalBSplineShiftEvenAE_all
      CenteredCardinalBSplineMatchesConvPower_all
      (CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all_of_convolutionLaw
        hlaw)

/-- Endpoint-safe closure using only the local right-box associativity step for
the B-spline convolution-power family, plus positivity of the normalizer. -/
theorem CenteredBSplineAutocorrelationClosedForm_all_of_assocRightBox_and_norm_pos
    (hbox : CenteredCardinalBSplineConvPowerAssocRightBox)
    (hc_pos : ∀ k : ℕ, 0 < bsplineAutocorrNorm k) :
    ∀ k : ℕ, CenteredBSplineAutocorrelationClosedForm k := by
  exact
    CenteredBSplineAutocorrelationClosedForm_all_of_convPower_inputs
      hc_pos
      CenteredCardinalBSplineShiftEvenAE_all
      CenteredCardinalBSplineMatchesConvPower_all
      (CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all_of_assocRightBox
        hbox)

/-- With right-box associativity now closed, the remaining normalized
autocorrelation package depends only on positivity of the normalizer. -/
theorem CenteredBSplineAutocorrelationClosedForm_all_of_norm_pos
    (hc_pos : ∀ k : ℕ, 0 < bsplineAutocorrNorm k) :
    ∀ k : ℕ, CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_all_of_assocRightBox_and_norm_pos
    CenteredCardinalBSplineConvPowerAssocRightBox_all
    hc_pos

/-- The strict centered box is compactly supported in `[-1/2,1/2]`. -/
theorem centeredBoxSpline_hasCompactSupport :
    HasCompactSupport centeredBoxSpline := by
  have hIcc : IsCompact (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := isCompact_Icc
  refine HasCompactSupport.of_support_subset_isCompact hIcc ?_
  intro x hx
  have hx_support : centeredBoxSpline x ≠ 0 := hx
  constructor
  · by_contra hxlt
    have hleft : ¬ 0 < x + (2⁻¹ : ℝ) := by norm_num; linarith
    have hright : ¬ (2⁻¹ : ℝ) < x := by norm_num; linarith
    have hzero : centeredBoxSpline x = 0 := by
      simp [centeredBoxSpline, hleft, hright]
    exact hx_support hzero
  · by_contra hxgt
    have hleft : 0 < x + (2⁻¹ : ℝ) := by norm_num; linarith
    have hright : (2⁻¹ : ℝ) < x := by norm_num; linarith
    have hzero : centeredBoxSpline x = 0 := by
      simp [centeredBoxSpline, hleft, hright]
    exact hx_support hzero

/-- Every centered-box convolution power is compactly supported. -/
theorem centeredCardinalBSplineConvPower_hasCompactSupport
    (k : ℕ) :
    HasCompactSupport (centeredCardinalBSplineConvPower k) := by
  induction k with
  | zero =>
      simpa [centeredCardinalBSplineConvPower_zero] using centeredBoxSpline_hasCompactSupport
  | succ k ih =>
      change HasCompactSupport
        (realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline)
      have hconv := ih.convolution
        (L := ContinuousLinearMap.mul ℝ ℝ)
        (μ := volume)
        centeredBoxSpline_hasCompactSupport
      simpa [realConvolution, MeasureTheory.convolution_def] using hconv

/-- Positive-degree executable centered-cardinal B-splines are continuous. -/
theorem centeredCardinalBSpline_continuous_succ
    (k : ℕ) :
    Continuous (centeredCardinalBSpline (k + 1)) := by
  unfold centeredCardinalBSpline
  refine Continuous.mul continuous_const ?_
  refine continuous_finset_sum _ fun j _ => ?_
  have harg :
      Continuous fun x : ℝ =>
        x + ((((k + 1) + 1 : ℕ) : ℝ) / 2) - (j : ℝ) := by
    continuity
  have hpp := (continuous_positivePartPower_succ k).comp harg
  exact continuous_const.mul hpp

/-- Positive-degree executable centered-cardinal B-splines are continuous. -/
theorem centeredCardinalBSpline_continuous_of_pos
    (k : ℕ) (hk : 0 < k) :
    Continuous (centeredCardinalBSpline k) := by
  cases k with
  | zero =>
      cases hk
  | succ k =>
      simpa using centeredCardinalBSpline_continuous_succ k

/-- The left interior point of a positive-degree centered cardinal spline is
strictly positive. -/
theorem centeredCardinalBSpline_left_interior_pos
    (k : ℕ) (_hk : 0 < k) :
    0 < centeredCardinalBSpline k (-(k : ℝ) / 2) := by
  unfold centeredCardinalBSpline
  have hsum :
      ((Finset.range (k + 2)).sum fun j =>
        ((-1 : ℝ) ^ j) * (Nat.choose (k + 1) j : ℝ) *
        positivePartPower k
            (-(k : ℝ) / 2 + (((k + 1 : ℕ) : ℝ) / 2) - (j : ℝ))) =
        (1 / 2 : ℝ) ^ k := by
    rw [Finset.sum_eq_single 0]
    · have harg0 :
          (-(k : ℝ) / 2 + (((k + 1 : ℕ) : ℝ) / 2)) = (1 / 2 : ℝ) := by
        norm_num [Nat.cast_add]
        ring
      rw [harg0]
      rw [positivePartPower_of_pos k (by norm_num)]
      simp
    · intro j hj hj0
      have hjpos_nat : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
      have hjpos : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjpos_nat
      have harg :
          ¬ 0 <
            (-(k : ℝ) / 2 + (((k + 1 : ℕ) : ℝ) / 2) - (j : ℝ)) := by
        have hcalc :
            (-(k : ℝ) / 2 + (((k + 1 : ℕ) : ℝ) / 2) - (j : ℝ)) =
              (1 / 2 : ℝ) - (j : ℝ) := by
          norm_num [Nat.cast_add]
          ring
        rw [hcalc]
        linarith
      rw [positivePartPower_of_nonpos k harg]
      ring
    · intro hnot
      simp at hnot
  rw [hsum]
  exact mul_pos (inv_pos.mpr (by positivity)) (pow_pos (by norm_num) k)

/-- Positive convolution powers are continuous, via the executable
truncated-power model. -/
theorem centeredCardinalBSplineConvPower_continuous_of_pos
    (k : ℕ) (hk : 0 < k) :
    Continuous (centeredCardinalBSplineConvPower k) := by
  have hfun :
      centeredCardinalBSplineConvPower k = centeredCardinalBSpline k := by
    funext x
    exact (CenteredCardinalBSplineMatchesConvPower_all k x).symm
  rw [hfun]
  exact centeredCardinalBSpline_continuous_of_pos k hk

/-- Every positive convolution power is nonzero. -/
theorem centeredCardinalBSplineConvPower_nonzero_of_pos
    (k : ℕ) (hk : 0 < k) :
    ∃ x : ℝ, centeredCardinalBSplineConvPower k x ≠ 0 := by
  refine ⟨-(k : ℝ) / 2, ?_⟩
  have hpos := centeredCardinalBSpline_left_interior_pos k hk
  have hmatch := CenteredCardinalBSplineMatchesConvPower_all k (-(k : ℝ) / 2)
  intro hzero
  rw [hmatch, hzero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- At zero, self-convolution of a centered convolution power is the integral
of its square, using endpoint-safe a.e. evenness. -/
theorem realConvolution_convPower_self_zero_eq_squareIntegral
    (k : ℕ) :
    realConvolution
        (centeredCardinalBSplineConvPower k)
        (centeredCardinalBSplineConvPower k) 0 =
      ∫ y : ℝ,
        centeredCardinalBSplineConvPower k y *
          centeredCardinalBSplineConvPower k y := by
  unfold realConvolution
  apply integral_congr_ae
  filter_upwards [centeredCardinalBSplineConvPower_shiftEvenAE_all k 0] with y hy
  have hy' :
      centeredCardinalBSplineConvPower k (-y) =
        centeredCardinalBSplineConvPower k y := by
    simpa using hy
  simp [hy']

/-- The square of any positive convolution power has strictly positive
Lebesgue integral. -/
theorem centeredCardinalBSplineConvPower_squareIntegral_pos_of_pos
    (k : ℕ) (hk : 0 < k) :
    0 <
      ∫ y : ℝ,
        centeredCardinalBSplineConvPower k y *
          centeredCardinalBSplineConvPower k y := by
  let B : ℝ → ℝ := centeredCardinalBSplineConvPower k
  have hcontB : Continuous B := centeredCardinalBSplineConvPower_continuous_of_pos k hk
  have hcontSq : Continuous fun y : ℝ => B y * B y := hcontB.mul hcontB
  have hcompB : HasCompactSupport B := centeredCardinalBSplineConvPower_hasCompactSupport k
  have hcompSq : HasCompactSupport fun y : ℝ => B y * B y := by
    have hmul : HasCompactSupport (B * B) := hcompB.mul_right
    simpa [B, Pi.mul_apply] using hmul
  have hnonneg : 0 ≤ fun y : ℝ => B y * B y := by
    intro y
    exact mul_self_nonneg (B y)
  rcases centeredCardinalBSplineConvPower_nonzero_of_pos k hk with ⟨x, hx⟩
  have hxSq : B x * B x ≠ 0 := by
    exact mul_self_ne_zero.mpr (by simpa [B] using hx)
  exact hcontSq.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hcompSq hnonneg hxSq

/-- The degree-zero autocorrelation normalizer is positive. -/
theorem bsplineAutocorrNorm_pos_zero :
    0 < bsplineAutocorrNorm 0 := by
  norm_num [bsplineAutocorrNorm, bsplineAutocorrDegree,
    centeredCardinalBSpline, positivePartPower]

/-- The centered B-spline autocorrelation normalizer is positive in every
degree. -/
theorem bsplineAutocorrNorm_pos
    (k : ℕ) :
    0 < bsplineAutocorrNorm k := by
  cases k with
  | zero =>
      exact bsplineAutocorrNorm_pos_zero
  | succ k =>
      unfold bsplineAutocorrNorm
      rw [CenteredCardinalBSplineMatchesConvPower_all (bsplineAutocorrDegree (k + 1)) 0]
      have hconv := CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_all (k + 1) 0
      rw [← hconv]
      simp only [neg_zero]
      rw [realConvolution_convPower_self_zero_eq_squareIntegral]
      exact centeredCardinalBSplineConvPower_squareIntegral_pos_of_pos (k + 1)
        (Nat.succ_pos k)

/-- Endpoint-safe centered B-spline autocorrelation closed form in every
degree. -/
theorem CenteredBSplineAutocorrelationClosedForm_all :
    ∀ k : ℕ, CenteredBSplineAutocorrelationClosedForm k :=
  CenteredBSplineAutocorrelationClosedForm_all_of_norm_pos bsplineAutocorrNorm_pos

/-- Name the exact transform profile still needed to close the Arch/boundary
side of Step 32F. -/
def centeredBSplineRealTransformProfile (k : ℕ) (ell z : ℝ) : ℝ :=
  realBumpTransformProfile (centeredBSplineEta k) ell z

/--
Regularized hyperbolic sinc.

The B-spline Laplace profile is a power of `sinh x / x`, but the transform is
regular at `x = 0`.  This definition records the removable value explicitly so
the closed-form target is well-typed and correct at the origin.
-/
def realSinhc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

@[simp] theorem realSinhc_zero :
    realSinhc 0 = 1 := by
  simp [realSinhc]

theorem realSinhc_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    realSinhc x = Real.sinh x / x := by
  simp [realSinhc, hx]

/--
Regularized trigonometric sinc.

The imaginary-axis B-spline transform is a power of `sin x / x`, with the
removable value at the origin recorded explicitly.
-/
def realSinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin x / x

@[simp] theorem realSinc_zero :
    realSinc 0 = 1 := by
  simp [realSinc]

theorem realSinc_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    realSinc x = Real.sin x / x := by
  simp [realSinc, hx]

/-- The centered interval exponential integral is the regularized hyperbolic
sinc factor. -/
theorem intervalIntegral_exp_mul_centered_eq_realSinhc (a : ℝ) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.exp (a * x)) =
      realSinhc (a / 2) := by
  by_cases ha : a = 0
  · subst a
    simp [realSinhc]
    norm_num
  · have hmul := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.exp) (c := a)
      (a := (-(1 / 2 : ℝ))) (b := (1 / 2 : ℝ))
    have hmul' :
        a * (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          Real.exp (a * x)) =
          ∫ x in (a * (-(1 / 2 : ℝ)))..(a * (1 / 2 : ℝ)),
            Real.exp x := by
      exact hmul
    rw [integral_exp] at hmul'
    have hmul'' :
        a * (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          Real.exp (a * x)) =
          Real.exp (a / 2) - Real.exp (-(a / 2)) := by
      convert hmul' using 1
      ring_nf
    have hI :
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.exp (a * x)) =
          (Real.exp (a / 2) - Real.exp (-(a / 2))) / a := by
      field_simp [ha] at hmul'' ⊢
      exact hmul''
    rw [hI]
    have ha2 : a / 2 ≠ 0 := by
      exact div_ne_zero ha (by norm_num)
    rw [realSinhc_of_ne_zero ha2]
    rw [Real.sinh_eq]
    field_simp [ha]

/-- The centered interval cosine integral is the regularized sinc factor. -/
theorem intervalIntegral_cos_mul_centered_eq_realSinc (a : ℝ) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.cos (a * x)) =
      realSinc (a / 2) := by
  by_cases ha : a = 0
  · subst a
    simp [realSinc]
    norm_num
  · have hmul := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.cos) (c := a)
      (a := (-(1 / 2 : ℝ))) (b := (1 / 2 : ℝ))
    have hmul' :
        a * (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          Real.cos (a * x)) =
          ∫ x in (a * (-(1 / 2 : ℝ)))..(a * (1 / 2 : ℝ)),
            Real.cos x := by
      exact hmul
    rw [integral_cos] at hmul'
    have hmul'' :
        a * (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          Real.cos (a * x)) =
          2 * Real.sin (a / 2) := by
      calc
        a * (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
            Real.cos (a * x))
            = Real.sin (a * (1 / 2 : ℝ)) -
                Real.sin (a * (-(1 / 2 : ℝ))) := by
              exact hmul'
        _ = 2 * Real.sin (a / 2) := by
              have hleft : a * (1 / 2 : ℝ) = a / 2 := by ring
              have hright : a * (-(1 / 2 : ℝ)) = -(a / 2) := by ring
              rw [hleft, hright, Real.sin_neg]
              ring
    have hI :
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.cos (a * x)) =
          (2 * Real.sin (a / 2)) / a := by
      field_simp [ha] at hmul'' ⊢
      exact hmul''
    rw [hI]
    have ha2 : a / 2 ≠ 0 := by
      exact div_ne_zero ha (by norm_num)
    rw [realSinc_of_ne_zero ha2]
    field_simp [ha]

/-- The centered interval sine integral vanishes by symmetry. -/
theorem intervalIntegral_sin_mul_centered_eq_zero (a : ℝ) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.sin (a * x)) = 0 := by
  by_cases ha : a = 0
  · subst a
    simp
  · have hmul := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.sin) (c := a)
      (a := (-(1 / 2 : ℝ))) (b := (1 / 2 : ℝ))
    have hmul' :
        a * (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          Real.sin (a * x)) =
          ∫ x in (a * (-(1 / 2 : ℝ)))..(a * (1 / 2 : ℝ)),
            Real.sin x := by
      exact hmul
    rw [integral_sin] at hmul'
    have hmul'' :
        a * (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          Real.sin (a * x)) = 0 := by
      calc
        a * (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
            Real.sin (a * x))
            = Real.cos (a * (-(1 / 2 : ℝ))) -
                Real.cos (a * (1 / 2 : ℝ)) := by
              exact hmul'
        _ = 0 := by
              have hleft : a * (1 / 2 : ℝ) = a / 2 := by ring
              have hright : a * (-(1 / 2 : ℝ)) = -(a / 2) := by ring
              rw [hleft, hright, Real.cos_neg]
              ring
    exact (mul_eq_zero.mp hmul'').resolve_left ha

/-- The centered interval complex exponential integral on the imaginary axis is
the regularized sinc factor. -/
theorem intervalIntegral_complex_exp_I_mul_centered_eq_realSinc (a : ℝ) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) =
      (realSinc (a / 2) : ℂ) := by
  have hfun :
      (fun x : ℝ => Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) =
        fun x : ℝ => Complex.exp (((a * x : ℝ) : ℂ) * Complex.I) := by
    funext x
    congr 1
    norm_num
    ring
  rw [hfun]
  by_cases ha : a = 0
  · subst a
    simp [realSinc]
    norm_num
  · have hcomp := intervalIntegral.integral_comp_mul_left
      (f := fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (a := (-(1 / 2 : ℝ))) (b := (1 / 2 : ℝ)) ha
    have hleft : a * (-(1 / 2 : ℝ)) = -(a / 2) := by ring
    have hright : a * (1 / 2 : ℝ) = a / 2 := by ring
    rw [hleft, hright] at hcomp
    rw [hcomp]
    rw [integral_exp_mul_I_eq_sin]
    have ha2 : a / 2 ≠ 0 := div_ne_zero ha (by norm_num)
    rw [realSinc_of_ne_zero ha2]
    norm_num
    field_simp [ha]

/-- Degree-zero centered box real transform. -/
theorem centeredBoxSpline_realTransform_eq_realSinhc (a : ℝ) :
    (∫ x : ℝ, centeredBoxSpline x * Real.exp (a * x)) =
      realSinhc (a / 2) := by
  calc
    (∫ x : ℝ, centeredBoxSpline x * Real.exp (a * x))
        = ∫ x : ℝ, (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
            (fun x : ℝ => Real.exp (a * x)) x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [centeredBoxSpline_eq_indicator_Ioc x]
            by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) <;>
              simp [Set.indicator]
    _ = ∫ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), Real.exp (a * x) := by
            rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.exp (a * x) := by
            rw [intervalIntegral.integral_of_le]
            linarith
    _ = realSinhc (a / 2) :=
            intervalIntegral_exp_mul_centered_eq_realSinhc a

/-- Degree-zero centered box cosine transform on the imaginary axis. -/
theorem centeredBoxSpline_cosTransform_eq_realSinc (a : ℝ) :
    (∫ x : ℝ, centeredBoxSpline x * Real.cos (a * x)) =
      realSinc (a / 2) := by
  calc
    (∫ x : ℝ, centeredBoxSpline x * Real.cos (a * x))
        = ∫ x : ℝ, (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
            (fun x : ℝ => Real.cos (a * x)) x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [centeredBoxSpline_eq_indicator_Ioc x]
            by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) <;>
              simp [Set.indicator]
    _ = ∫ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), Real.cos (a * x) := by
            rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.cos (a * x) := by
            rw [intervalIntegral.integral_of_le]
            linarith
    _ = realSinc (a / 2) :=
            intervalIntegral_cos_mul_centered_eq_realSinc a

/-- Degree-zero centered box sine transform vanishes on the imaginary axis. -/
theorem centeredBoxSpline_sinTransform_eq_zero (a : ℝ) :
    (∫ x : ℝ, centeredBoxSpline x * Real.sin (a * x)) = 0 := by
  calc
    (∫ x : ℝ, centeredBoxSpline x * Real.sin (a * x))
        = ∫ x : ℝ, (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
            (fun x : ℝ => Real.sin (a * x)) x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [centeredBoxSpline_eq_indicator_Ioc x]
            by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) <;>
              simp [Set.indicator]
    _ = ∫ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), Real.sin (a * x) := by
            rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.sin (a * x) := by
            rw [intervalIntegral.integral_of_le]
            linarith
    _ = 0 :=
            intervalIntegral_sin_mul_centered_eq_zero a

/-- Degree-zero centered box complex transform on the imaginary axis. -/
theorem centeredBoxSpline_complexBumpLaplace_imag_eq_realSinc (a : ℝ) :
    complexBumpLaplace
      (fun x : ℝ => (centeredBoxSpline x : ℂ)) (Complex.I * (a : ℂ)) =
      (realSinc (a / 2) : ℂ) := by
  unfold complexBumpLaplace
  calc
    (∫ x : ℝ, (centeredBoxSpline x : ℂ) *
        Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ)))
        = ∫ x : ℝ, (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
            (fun x : ℝ => Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [centeredBoxSpline_eq_indicator_Ioc x]
            by_cases hcond :
                -((2 : ℝ)⁻¹) < x ∧ x ≤ (2 : ℝ)⁻¹ <;>
              simp [Set.indicator, Set.mem_Ioc, hcond]
    _ = ∫ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
          Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ)) := by
            rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ)) := by
            rw [intervalIntegral.integral_of_le]
            linarith
    _ = (realSinc (a / 2) : ℂ) :=
            intervalIntegral_complex_exp_I_mul_centered_eq_realSinc a

/-- Laplace transform of the real convolution is the product of weighted
Laplace transforms, under the exact weighted-integrability hypotheses. -/
theorem realBumpLaplace_realConvolution_eq_mul
    (f g : ℝ → ℝ) (a : ℝ)
    (hf : Integrable (fun x : ℝ => f x * Real.exp (a * x)))
    (hg : Integrable (fun x : ℝ => g x * Real.exp (a * x))) :
    realBumpLaplace (realConvolution f g) a =
      realBumpLaplace f a * realBumpLaplace g a := by
  let F : ℝ → ℝ := fun x => f x * Real.exp (a * x)
  let G : ℝ → ℝ := fun x => g x * Real.exp (a * x)
  have hpoint : ∀ x : ℝ,
      realConvolution f g x * Real.exp (a * x) =
        MeasureTheory.convolution F G (ContinuousLinearMap.mul ℝ ℝ) volume x := by
    intro x
    rw [MeasureTheory.convolution_def]
    unfold realConvolution
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    simp [F, G]
    have hx : a * x = a * y + a * (x - y) := by ring
    rw [hx, Real.exp_add]
    ring_nf
  calc
    realBumpLaplace (realConvolution f g) a
        = ∫ x : ℝ,
            MeasureTheory.convolution F G (ContinuousLinearMap.mul ℝ ℝ) volume x := by
            unfold realBumpLaplace
            apply integral_congr_ae
            filter_upwards with x
            exact hpoint x
    _ = (∫ x : ℝ, F x) * (∫ x : ℝ, G x) := by
            have hconv := MeasureTheory.integral_convolution
              (L := ContinuousLinearMap.mul ℝ ℝ)
              (μ := volume) (ν := volume) hf hg
            simpa [ContinuousLinearMap.mul_apply] using hconv
    _ = realBumpLaplace f a * realBumpLaplace g a := by
            simp [F, G, realBumpLaplace]

/-- Complex Laplace transform of the real convolution is the product of the
complex weighted transforms, under the exact weighted-integrability
hypotheses. -/
theorem complexBumpLaplace_realConvolution_eq_mul
    (f g : ℝ → ℝ) (z : ℂ)
    (hf : Integrable
      (fun x : ℝ => (f x : ℂ) * Complex.exp (z * (x : ℂ))))
    (hg : Integrable
      (fun x : ℝ => (g x : ℂ) * Complex.exp (z * (x : ℂ)))) :
    complexBumpLaplace (fun x : ℝ => (realConvolution f g x : ℂ)) z =
      complexBumpLaplace (fun x : ℝ => (f x : ℂ)) z *
        complexBumpLaplace (fun x : ℝ => (g x : ℂ)) z := by
  let F : ℝ → ℂ := fun x => (f x : ℂ) * Complex.exp (z * (x : ℂ))
  let G : ℝ → ℂ := fun x => (g x : ℂ) * Complex.exp (z * (x : ℂ))
  have hpoint : ∀ x : ℝ,
      (realConvolution f g x : ℂ) * Complex.exp (z * (x : ℂ)) =
        MeasureTheory.convolution F G (ContinuousLinearMap.mul ℂ ℂ) volume x := by
    intro x
    rw [MeasureTheory.convolution_def]
    unfold realConvolution
    rw [← integral_complex_ofReal]
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    simp only [F, G, Complex.ofReal_mul]
    change (f y : ℂ) * (g (x - y) : ℂ) * Complex.exp (z * (x : ℂ)) =
      ((f y : ℂ) * Complex.exp (z * (y : ℂ))) *
        ((g (x - y) : ℂ) * Complex.exp (z * ((x - y : ℝ) : ℂ)))
    have hx : z * (y : ℂ) + z * ((x - y : ℝ) : ℂ) = z * (x : ℂ) := by
      norm_num
      ring
    have hexp : Complex.exp (z * (x : ℂ)) =
        Complex.exp (z * (y : ℂ)) *
          Complex.exp (z * ((x - y : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, hx]
    rw [hexp]
    ring
  calc
    complexBumpLaplace (fun x : ℝ => (realConvolution f g x : ℂ)) z
        = ∫ x : ℝ,
            MeasureTheory.convolution F G (ContinuousLinearMap.mul ℂ ℂ) volume x := by
            unfold complexBumpLaplace
            apply integral_congr_ae
            filter_upwards with x
            exact hpoint x
    _ = (∫ x : ℝ, F x) * (∫ x : ℝ, G x) := by
            have hconv := MeasureTheory.integral_convolution
              (L := ContinuousLinearMap.mul ℂ ℂ)
              (μ := volume) (ν := volume) hf hg
            simpa [ContinuousLinearMap.mul_apply] using hconv
    _ =
      complexBumpLaplace (fun x : ℝ => (f x : ℂ)) z *
        complexBumpLaplace (fun x : ℝ => (g x : ℂ)) z := by
            simp [F, G, complexBumpLaplace]

/-- The exponentially weighted centered box is integrable. -/
theorem centeredBoxSpline_realBumpLaplace_integrable (a : ℝ) :
    Integrable (fun x : ℝ => centeredBoxSpline x * Real.exp (a * x)) := by
  have hfun :
      (fun x : ℝ => centeredBoxSpline x * Real.exp (a * x)) =
        (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun x : ℝ => Real.exp (a * x)) := by
    funext x
    rw [centeredBoxSpline_eq_indicator_Ioc x]
    by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) <;>
      simp [Set.indicator]
  rw [hfun]
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (Real.continuous_exp.comp
    (continuous_const.mul continuous_id)).integrableOn_Ioc

/-- The imaginary-axis complex weighted centered box is integrable. -/
theorem centeredBoxSpline_complexBumpLaplace_imag_integrable (a : ℝ) :
    Integrable
      (fun x : ℝ => (centeredBoxSpline x : ℂ) *
        Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) := by
  have hfun :
      (fun x : ℝ => (centeredBoxSpline x : ℂ) *
        Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) =
        (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun x : ℝ => Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) := by
    funext x
    rw [centeredBoxSpline_eq_indicator_Ioc x]
    by_cases hcond : -((2 : ℝ)⁻¹) < x ∧ x ≤ (2 : ℝ)⁻¹ <;>
      simp [Set.indicator, Set.mem_Ioc, hcond]
  rw [hfun]
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal)).integrableOn_Ioc

/-- Every centered-box convolution power has an exponentially weighted
Laplace-integrable profile. -/
theorem centeredCardinalBSplineConvPower_realBumpLaplace_integrable
    (k : ℕ) (a : ℝ) :
    Integrable
      (fun x : ℝ => centeredCardinalBSplineConvPower k x * Real.exp (a * x)) := by
  cases k with
  | zero =>
      simpa [centeredCardinalBSplineConvPower_zero] using
        centeredBoxSpline_realBumpLaplace_integrable a
  | succ k =>
      let B : ℝ → ℝ := centeredCardinalBSplineConvPower (k + 1)
      have hcontB : Continuous B :=
        centeredCardinalBSplineConvPower_continuous_of_pos (k + 1) (Nat.succ_pos k)
      have hcont : Continuous (fun x : ℝ => B x * Real.exp (a * x)) := by
        exact hcontB.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      have hcompB : HasCompactSupport B :=
        centeredCardinalBSplineConvPower_hasCompactSupport (k + 1)
      have hcomp : HasCompactSupport (fun x : ℝ => B x * Real.exp (a * x)) := by
        have hmul :
            HasCompactSupport (B * fun x : ℝ => Real.exp (a * x)) :=
          hcompB.mul_right
        simpa [B, Pi.mul_apply] using hmul
      exact hcont.integrable_of_hasCompactSupport hcomp

/-- Every centered-box convolution power has an imaginary-axis complex
weighted-integrable profile. -/
theorem centeredCardinalBSplineConvPower_complexBumpLaplace_imag_integrable
    (k : ℕ) (a : ℝ) :
    Integrable
      (fun x : ℝ => (centeredCardinalBSplineConvPower k x : ℂ) *
        Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) := by
  cases k with
  | zero =>
      simpa [centeredCardinalBSplineConvPower_zero] using
        centeredBoxSpline_complexBumpLaplace_imag_integrable a
  | succ k =>
      let B : ℝ → ℝ := centeredCardinalBSplineConvPower (k + 1)
      have hcontB : Continuous B :=
        centeredCardinalBSplineConvPower_continuous_of_pos (k + 1) (Nat.succ_pos k)
      have hcontCast : Continuous (fun x : ℝ => (B x : ℂ)) :=
        Complex.continuous_ofReal.comp hcontB
      have hcont : Continuous
          (fun x : ℝ => (B x : ℂ) *
            Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) := by
        exact hcontCast.mul
          (Complex.continuous_exp.comp
            (continuous_const.mul Complex.continuous_ofReal))
      have hcompB : HasCompactSupport B :=
        centeredCardinalBSplineConvPower_hasCompactSupport (k + 1)
      have hcompCast : HasCompactSupport (fun x : ℝ => (B x : ℂ)) := by
        have hcast :
            HasCompactSupport ((fun r : ℝ => (r : ℂ)) ∘ B) :=
          hcompB.comp_left (by simp)
        simpa [Function.comp_def] using hcast
      have hcomp : HasCompactSupport
          (fun x : ℝ => (B x : ℂ) *
            Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) := by
        have hmul :
            HasCompactSupport
              ((fun x : ℝ => (B x : ℂ)) *
                fun x : ℝ =>
                  Complex.exp ((Complex.I * (a : ℂ)) * (x : ℂ))) :=
          hcompCast.mul_right
        simpa [Pi.mul_apply] using hmul
      exact hcont.integrable_of_hasCompactSupport hcomp

/-- One convolution-power transform step: convolving once more with the
centered box multiplies the transform by the box `realSinhc` factor. -/
theorem centeredCardinalBSplineConvPower_realBumpLaplace_succ
    (k : ℕ) (a : ℝ) :
    realBumpLaplace (centeredCardinalBSplineConvPower (k + 1)) a =
      realBumpLaplace (centeredCardinalBSplineConvPower k) a *
        realSinhc (a / 2) := by
  rw [centeredCardinalBSplineConvPower_succ]
  rw [realBumpLaplace_realConvolution_eq_mul]
  have hbox : realBumpLaplace centeredBoxSpline a = realSinhc (a / 2) := by
    simpa [realBumpLaplace] using centeredBoxSpline_realTransform_eq_realSinhc a
  rw [hbox]
  · exact centeredCardinalBSplineConvPower_realBumpLaplace_integrable k a
  · exact centeredBoxSpline_realBumpLaplace_integrable a

/-- One convolution-power imaginary-axis transform step: convolving once more
with the centered box multiplies the complex transform by the box sinc factor. -/
theorem centeredCardinalBSplineConvPower_complexBumpLaplace_imag_succ
    (k : ℕ) (a : ℝ) :
    complexBumpLaplace
        (fun x : ℝ => (centeredCardinalBSplineConvPower (k + 1) x : ℂ))
        (Complex.I * (a : ℂ)) =
      complexBumpLaplace
        (fun x : ℝ => (centeredCardinalBSplineConvPower k x : ℂ))
        (Complex.I * (a : ℂ)) *
        (realSinc (a / 2) : ℂ) := by
  rw [centeredCardinalBSplineConvPower_succ]
  rw [complexBumpLaplace_realConvolution_eq_mul]
  have hbox :
      complexBumpLaplace (fun x : ℝ => (centeredBoxSpline x : ℂ))
          (Complex.I * (a : ℂ)) =
        (realSinc (a / 2) : ℂ) :=
    centeredBoxSpline_complexBumpLaplace_imag_eq_realSinc a
  rw [hbox]
  · exact centeredCardinalBSplineConvPower_complexBumpLaplace_imag_integrable k a
  · exact centeredBoxSpline_complexBumpLaplace_imag_integrable a

/-- Closed transform of the convolution-power centered-cardinal model. -/
theorem centeredCardinalBSplineConvPower_realBumpLaplace_eq_realSinhc_pow
    (k : ℕ) (a : ℝ) :
    realBumpLaplace (centeredCardinalBSplineConvPower k) a =
      (realSinhc (a / 2)) ^ (k + 1) := by
  induction k with
  | zero =>
      simpa [centeredCardinalBSplineConvPower_zero, realBumpLaplace] using
        centeredBoxSpline_realTransform_eq_realSinhc a
  | succ k ih =>
      rw [centeredCardinalBSplineConvPower_realBumpLaplace_succ, ih]
      rw [pow_succ]
      ring

/-- Closed imaginary-axis transform of the convolution-power centered-cardinal
model. -/
theorem centeredCardinalBSplineConvPower_complexBumpLaplace_imag_eq_realSinc_pow
    (k : ℕ) (a : ℝ) :
    complexBumpLaplace
        (fun x : ℝ => (centeredCardinalBSplineConvPower k x : ℂ))
        (Complex.I * (a : ℂ)) =
      ((realSinc (a / 2) : ℂ)) ^ (k + 1) := by
  induction k with
  | zero =>
      simpa [centeredCardinalBSplineConvPower_zero] using
        centeredBoxSpline_complexBumpLaplace_imag_eq_realSinc a
  | succ k ih =>
      rw [centeredCardinalBSplineConvPower_complexBumpLaplace_imag_succ, ih]
      rw [pow_succ]
      ring

/-- Closed imaginary-axis transform of the executable centered-cardinal model,
obtained by pointwise agreement with the convolution-power model. -/
theorem centeredCardinalBSpline_complexBumpLaplace_imag_eq_realSinc_pow
    (k : ℕ) (a : ℝ) :
    complexBumpLaplace
        (fun x : ℝ => (centeredCardinalBSpline k x : ℂ))
        (Complex.I * (a : ℂ)) =
      ((realSinc (a / 2) : ℂ)) ^ (k + 1) := by
  have hfun :
      (fun x : ℝ => (centeredCardinalBSpline k x : ℂ)) =
        fun x : ℝ => (centeredCardinalBSplineConvPower k x : ℂ) := by
    funext x
    rw [CenteredCardinalBSplineMatchesConvPower_all k x]
  rw [hfun]
  exact centeredCardinalBSplineConvPower_complexBumpLaplace_imag_eq_realSinc_pow k a

/-- Closed transform of the executable centered-cardinal model, obtained by
the pointwise agreement with the convolution-power model. -/
theorem centeredCardinalBSpline_realBumpLaplace_eq_realSinhc_pow
    (k : ℕ) (a : ℝ) :
    realBumpLaplace (centeredCardinalBSpline k) a =
      (realSinhc (a / 2)) ^ (k + 1) := by
  have hfun : centeredCardinalBSpline k = centeredCardinalBSplineConvPower k := by
    funext x
    exact CenteredCardinalBSplineMatchesConvPower_all k x
  rw [hfun]
  exact centeredCardinalBSplineConvPower_realBumpLaplace_eq_realSinhc_pow k a

/-- Closed-form RHS for the normalized centered B-spline real transform. -/
def centeredBSplineRealTransformClosedForm (k : ℕ) (ell z : ℝ) : ℝ :=
  (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
    (realSinhc (ell * z / (2 * bsplineScale k))) ^ (k + 1)

/-- Normalization coefficient in the scaled `eta_k` transform. -/
private theorem centeredBSpline_transform_normalization_coeff
    (k : ℕ) :
    |(bsplineScale k)⁻¹| *
      Real.sqrt (bsplineScale k / bsplineAutocorrNorm k) =
        (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ := by
  have hs : 0 < bsplineScale k := bsplineScale_pos k
  have hc : 0 < bsplineAutocorrNorm k := bsplineAutocorrNorm_pos k
  have hsle : 0 ≤ bsplineScale k := le_of_lt hs
  rw [abs_of_pos (inv_pos.mpr hs)]
  rw [Real.sqrt_div hsle]
  rw [Real.sqrt_mul hsle (bsplineAutocorrNorm k)]
  have hsqrts : Real.sqrt (bsplineScale k) ≠ 0 :=
    (Real.sqrt_pos.mpr hs).ne'
  have hsqrtc : Real.sqrt (bsplineAutocorrNorm k) ≠ 0 :=
    (Real.sqrt_pos.mpr hc).ne'
  field_simp [hs.ne', hsqrts, hsqrtc]
  exact Real.sq_sqrt hsle

/-- Closed normalized real transform profile for the concrete centered
B-spline packet. -/
theorem centeredBSplineRealTransformProfile_eq_closedForm
    (k : ℕ) (ell z : ℝ) :
    centeredBSplineRealTransformProfile k ell z =
      centeredBSplineRealTransformClosedForm k ell z := by
  let s : ℝ := bsplineScale k
  let C : ℝ := Real.sqrt (s / bsplineAutocorrNorm k)
  let G : ℝ → ℝ := fun u =>
    C * centeredCardinalBSpline k u * Real.exp ((z * ell / s) * u)
  unfold centeredBSplineRealTransformProfile realBumpTransformProfile centeredBSplineEta
  calc
    (∫ x : ℝ,
        Real.sqrt (bsplineScale k / bsplineAutocorrNorm k) *
            centeredCardinalBSpline k (bsplineScale k * x) *
          Real.exp (z * (ell * x)))
        = ∫ x : ℝ, G (s * x) := by
            apply integral_congr_ae
            filter_upwards with x
            have harg :
                z * (ell * x) =
                  (z * ell / bsplineScale k) * (bsplineScale k * x) := by
              field_simp [bsplineScale_ne_zero k]
            change
              Real.sqrt (bsplineScale k / bsplineAutocorrNorm k) *
                  centeredCardinalBSpline k (bsplineScale k * x) *
                Real.exp (z * (ell * x)) =
              C * centeredCardinalBSpline k (s * x) *
                Real.exp ((z * ell / s) * (s * x))
            rw [harg]
    _ = |s⁻¹| * ∫ u : ℝ, G u := by
            simpa using Measure.integral_comp_mul_left G s
    _ =
      |s⁻¹| *
        (C * realBumpLaplace (centeredCardinalBSpline k) (z * ell / s)) := by
            congr 1
            unfold G realBumpLaplace
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with u
            ring
    _ =
      |s⁻¹| *
        (C * (realSinhc ((z * ell / s) / 2)) ^ (k + 1)) := by
            rw [centeredCardinalBSpline_realBumpLaplace_eq_realSinhc_pow]
    _ =
      (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
        (realSinhc (ell * z / (2 * bsplineScale k))) ^ (k + 1) := by
            have harg :
                (z * ell / s) / 2 = ell * z / (2 * bsplineScale k) := by
              simp [s]
              ring
            rw [harg]
            calc
              |s⁻¹| *
                    (C * (realSinhc (ell * z / (2 * bsplineScale k))) ^ (k + 1))
                  =
                (|s⁻¹| * C) *
                    (realSinhc (ell * z / (2 * bsplineScale k))) ^ (k + 1) := by
                  ring
              _ =
                (Real.sqrt (s * bsplineAutocorrNorm k))⁻¹ *
                    (realSinhc (ell * z / (2 * bsplineScale k))) ^ (k + 1) := by
                  have hcoeff := centeredBSpline_transform_normalization_coeff k
                  simpa [s, C] using
                    congrArg
                      (fun r : ℝ =>
                        r * (realSinhc (ell * z / (2 * bsplineScale k))) ^ (k + 1))
                      hcoeff
              _ =
                (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
                    (realSinhc (ell * z / (2 * bsplineScale k))) ^ (k + 1) := by
                  simp [s]
    _ = centeredBSplineRealTransformClosedForm k ell z := by
            rfl

/-- Imaginary-axis complex transform profile for the normalized centered
B-spline packet. -/
def centeredBSplineImagTransformProfile (k : ℕ) (ell t : ℝ) : ℂ :=
  complexBumpTransformProfile (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell
    (Complex.I * (t : ℂ))

/-- Closed-form RHS for the normalized centered B-spline imaginary-axis
transform. -/
def centeredBSplineImagTransformClosedForm (k : ℕ) (ell t : ℝ) : ℂ :=
  (((Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ : ℝ) : ℂ) *
    ((realSinc (ell * t / (2 * bsplineScale k)) : ℂ) ^ (k + 1))

/-- Real-valued scalar behind the normalized imaginary-axis closed form. -/
def centeredBSplineImagTransformRealClosedForm (k : ℕ) (ell t : ℝ) : ℝ :=
  (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
    (realSinc (ell * t / (2 * bsplineScale k))) ^ (k + 1)

/-- The complex closed form is just the real scalar embedded in `ℂ`. -/
theorem centeredBSplineImagTransformClosedForm_eq_ofReal
    (k : ℕ) (ell t : ℝ) :
    centeredBSplineImagTransformClosedForm k ell t =
      (centeredBSplineImagTransformRealClosedForm k ell t : ℂ) := by
  unfold centeredBSplineImagTransformClosedForm
    centeredBSplineImagTransformRealClosedForm
  norm_num

/-- The normalized imaginary-axis closed form is real-valued. -/
theorem centeredBSplineImagTransformClosedForm_conj
    (k : ℕ) (ell t : ℝ) :
    star (centeredBSplineImagTransformClosedForm k ell t) =
      centeredBSplineImagTransformClosedForm k ell t := by
  unfold centeredBSplineImagTransformClosedForm
  simp

/-- Closed normalized imaginary-axis transform profile for the concrete
centered B-spline packet. -/
theorem centeredBSplineImagTransformProfile_eq_closedForm
    (k : ℕ) (ell t : ℝ) :
    centeredBSplineImagTransformProfile k ell t =
      centeredBSplineImagTransformClosedForm k ell t := by
  let s : ℝ := bsplineScale k
  let C : ℝ := Real.sqrt (s / bsplineAutocorrNorm k)
  let a : ℝ := ell * t / s
  let G : ℝ → ℂ := fun u =>
    ((C * centeredCardinalBSpline k u : ℝ) : ℂ) *
      Complex.exp ((Complex.I * (a : ℂ)) * (u : ℂ))
  unfold centeredBSplineImagTransformProfile complexBumpTransformProfile centeredBSplineEta
  calc
    (∫ x : ℝ,
        ↑(Real.sqrt (bsplineScale k / bsplineAutocorrNorm k) *
            centeredCardinalBSpline k (bsplineScale k * x)) *
          Complex.exp (Complex.I * ↑t * (↑ell * ↑x)))
        = ∫ x : ℝ, G (s * x) := by
            apply integral_congr_ae
            filter_upwards with x
            have harg :
                Complex.I * (t : ℂ) * ((ell : ℂ) * (x : ℂ)) =
                  (Complex.I * (a : ℂ)) * ((s * x : ℝ) : ℂ) := by
              simp [a, s]
              field_simp [bsplineScale_ne_zero k]
            change
              ((Real.sqrt (bsplineScale k / bsplineAutocorrNorm k) *
                  centeredCardinalBSpline k (bsplineScale k * x) : ℝ) : ℂ) *
                Complex.exp (Complex.I * (t : ℂ) * ((ell : ℂ) * (x : ℂ))) =
              G (s * x)
            dsimp [G, C, s]
            rw [harg]
    _ = |s⁻¹| * ∫ u : ℝ, G u := by
            simpa using Measure.integral_comp_mul_left G s
    _ =
      |s⁻¹| *
        (((C : ℂ) *
          complexBumpLaplace
            (fun u : ℝ => (centeredCardinalBSpline k u : ℂ))
            (Complex.I * (a : ℂ)))) := by
            congr 1
            unfold G complexBumpLaplace
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with u
            simp [Complex.ofReal_mul]
            ring
    _ =
      |s⁻¹| *
        ((C : ℂ) *
          (((realSinc ((ell * t / s) / 2) : ℂ)) ^ (k + 1))) := by
            rw [centeredCardinalBSpline_complexBumpLaplace_imag_eq_realSinc_pow]
    _ =
      (((Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ : ℝ) : ℂ) *
        ((realSinc (ell * t / (2 * bsplineScale k)) : ℂ) ^ (k + 1)) := by
            have harg :
                (ell * t / s) / 2 = ell * t / (2 * bsplineScale k) := by
              simp [s]
              ring
            rw [harg]
            calc
              |s⁻¹| *
                    ((C : ℂ) *
                      ((realSinc (ell * t / (2 * bsplineScale k)) : ℂ) ^ (k + 1)))
                  =
                (((|s⁻¹| * C : ℝ) : ℂ) *
                    ((realSinc (ell * t / (2 * bsplineScale k)) : ℂ) ^ (k + 1))) := by
                  norm_num
                  ring
              _ =
                (((Real.sqrt (s * bsplineAutocorrNorm k))⁻¹ : ℝ) : ℂ) *
                    ((realSinc (ell * t / (2 * bsplineScale k)) : ℂ) ^ (k + 1)) := by
                  have hcoeff := centeredBSpline_transform_normalization_coeff k
                  have hcoeffC :
                      ((|s⁻¹| * C : ℝ) : ℂ) =
                        (((Real.sqrt (s * bsplineAutocorrNorm k))⁻¹ : ℝ) : ℂ) := by
                    exact_mod_cast (by simpa [s, C] using hcoeff)
                  rw [hcoeffC]
              _ =
                (((Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ : ℝ) : ℂ) *
                    ((realSinc (ell * t / (2 * bsplineScale k)) : ℂ) ^ (k + 1)) := by
                  simp [s]
    _ = centeredBSplineImagTransformClosedForm k ell t := by
            rfl

/-- Imaginary-axis transform of a translated/scaled normalized centered
B-spline packet.  This is the concrete phase factor used by the Arch entry
formulas. -/
theorem centeredBSplineImagTransform_scaledTranslated_eq_closedForm
    (k : ℕ) (ell center t : ℝ) (hell : 0 < ell) :
    complexBumpLaplace
        (complexScaledTranslatedBump
          (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell center)
        (Complex.I * (t : ℂ)) =
      (Real.sqrt ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * (center : ℂ)) *
          centeredBSplineImagTransformClosedForm k ell t := by
  calc
    complexBumpLaplace
        (complexScaledTranslatedBump
          (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell center)
        (Complex.I * (t : ℂ))
        =
      (Real.sqrt ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * (center : ℂ)) *
          centeredBSplineImagTransformProfile k ell t := by
            simpa [centeredBSplineImagTransformProfile] using
              complexBumpLaplace_scaledTranslated
                (fun x : ℝ => (centeredBSplineEta k x : ℂ))
                ell center (Complex.I * (t : ℂ)) hell
    _ =
      (Real.sqrt ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * (center : ℂ)) *
          centeredBSplineImagTransformClosedForm k ell t := by
            rw [centeredBSplineImagTransformProfile_eq_closedForm]

/-- Product of translated imaginary-axis transforms, before folding the two
phase factors into a single difference phase.  This is the local algebraic
payload used by the Arch pairings. -/
theorem centeredBSplineImagTransform_scaledTranslated_pair_raw
    (k : ℕ) (ell ui uj t : ℝ) (hell : 0 < ell) :
    complexBumpLaplace
        (complexScaledTranslatedBump
          (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell uj)
        (Complex.I * (t : ℂ)) *
      star
        (complexBumpLaplace
          (complexScaledTranslatedBump
            (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell ui)
          (Complex.I * (t : ℂ))) =
      ((Real.sqrt ell : ℂ) *
          Complex.exp ((Complex.I * (t : ℂ)) * (uj : ℂ)) *
            centeredBSplineImagTransformClosedForm k ell t) *
        star
          ((Real.sqrt ell : ℂ) *
            Complex.exp ((Complex.I * (t : ℂ)) * (ui : ℂ)) *
              centeredBSplineImagTransformClosedForm k ell t) := by
  rw [centeredBSplineImagTransform_scaledTranslated_eq_closedForm k ell uj t hell]
  rw [centeredBSplineImagTransform_scaledTranslated_eq_closedForm k ell ui t hell]

/-- Product of translated imaginary-axis transforms with the phase folded into
the center difference.  This is the concrete kernel factor that the Arch entry
integral consumes. -/
theorem centeredBSplineImagTransform_scaledTranslated_pair_phase_closedForm
    (k : ℕ) (ell ui uj t : ℝ) (hell : 0 < ell) :
    complexBumpLaplace
        (complexScaledTranslatedBump
          (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell uj)
        (Complex.I * (t : ℂ)) *
      star
        (complexBumpLaplace
          (complexScaledTranslatedBump
            (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell ui)
          (Complex.I * (t : ℂ))) =
      (ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * ((uj - ui : ℝ) : ℂ)) *
          (centeredBSplineImagTransformClosedForm k ell t) ^ 2 := by
  rw [centeredBSplineImagTransform_scaledTranslated_pair_raw k ell ui uj t hell]
  have hsqrt_sq :
      (Real.sqrt ell : ℂ) * (Real.sqrt ell : ℂ) = (ell : ℂ) := by
    have hsqrt_sq_real : Real.sqrt ell * Real.sqrt ell = ell := by
      simpa [pow_two] using Real.sq_sqrt (le_of_lt hell)
    exact_mod_cast hsqrt_sq_real
  have hphase :
      Complex.exp ((Complex.I * (t : ℂ)) * (uj : ℂ)) *
          star (Complex.exp ((Complex.I * (t : ℂ)) * (ui : ℂ))) =
        Complex.exp ((Complex.I * (t : ℂ)) * ((uj : ℂ) - (ui : ℂ))) := by
    rw [Complex.star_def]
    rw [← Complex.exp_conj]
    rw [← Complex.exp_add]
    congr 1
    simp
    ring
  have hE := centeredBSplineImagTransformClosedForm_conj k ell t
  simp [hE]
  calc
    (Real.sqrt ell : ℂ) *
          Complex.exp ((Complex.I * (t : ℂ)) * (uj : ℂ)) *
            centeredBSplineImagTransformClosedForm k ell t *
        ((Real.sqrt ell : ℂ) *
          star (Complex.exp ((Complex.I * (t : ℂ)) * (ui : ℂ))) *
            centeredBSplineImagTransformClosedForm k ell t)
        =
      ((Real.sqrt ell : ℂ) * (Real.sqrt ell : ℂ)) *
        (Complex.exp ((Complex.I * (t : ℂ)) * (uj : ℂ)) *
          star (Complex.exp ((Complex.I * (t : ℂ)) * (ui : ℂ)))) *
          (centeredBSplineImagTransformClosedForm k ell t) ^ 2 := by
            ring
    _ =
      (ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * ((uj : ℂ) - (ui : ℂ))) *
          (centeredBSplineImagTransformClosedForm k ell t) ^ 2 := by
            rw [hsqrt_sq, hphase]

/-- Real part of the translated Arch pair factor.  This is the real kernel
payload used by the Arch matrix entries: phase becomes cosine and the
imaginary-axis profile contributes its square. -/
theorem centeredBSplineImagTransform_scaledTranslated_pair_re_closedForm
    (k : ℕ) (ell ui uj t : ℝ) (hell : 0 < ell) :
    (complexBumpLaplace
        (complexScaledTranslatedBump
          (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell uj)
        (Complex.I * (t : ℂ)) *
      star
        (complexBumpLaplace
          (complexScaledTranslatedBump
            (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell ui)
          (Complex.I * (t : ℂ)))).re =
      ell * Real.cos (t * (uj - ui)) *
        (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2 := by
  rw [centeredBSplineImagTransform_scaledTranslated_pair_phase_closedForm
    k ell ui uj t hell]
  rw [centeredBSplineImagTransformClosedForm_eq_ofReal]
  have hphase :
      (Complex.I * (t : ℂ)) * ((uj - ui : ℝ) : ℂ) =
        ((t * (uj - ui) : ℝ) : ℂ) * Complex.I := by
    norm_num
    ring
  rw [hphase]
  simp [Complex.mul_re, Complex.exp_re, Complex.exp_im, pow_two]

/-- Unbundled real Arch pairing associated to imaginary-axis packet
transforms.  This is the analytic pairing that later gets bundled into the
finite `LinearMap` API after the relevant linearity laws are supplied. -/
def centeredBSplineArchPairing (f g : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, Q3.a_star t *
    (complexBumpLaplace f (Complex.I * (t : ℂ)) *
      star (complexBumpLaplace g (Complex.I * (t : ℂ)))).re

/-- Concrete real Arch profile for translated normalized B-spline packets.

The argument is the center difference.  The profile integrates the real
translated pair factor against the Archimedean weight `a_star`. -/
def centeredBSplineArchKernelProfile (k : ℕ) (ell x : ℝ) : ℝ :=
  ∫ t : ℝ, Q3.a_star t *
    (ell * Real.cos (t * x) *
      (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)

/-- The real translated Arch pair product is exactly the Arch profile at the
center difference. -/
theorem centeredBSplineArchKernelProfile_pair_laplace_closed
    (k : ℕ) (ell u v : ℝ) (hell : 0 < ell) :
    (∫ t : ℝ, Q3.a_star t *
      (complexBumpLaplace
          (complexScaledTranslatedBump
            (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell u)
          (Complex.I * (t : ℂ)) *
        star
          (complexBumpLaplace
            (complexScaledTranslatedBump
              (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell v)
            (Complex.I * (t : ℂ)))).re) =
      centeredBSplineArchKernelProfile k ell (u - v) := by
  unfold centeredBSplineArchKernelProfile
  apply integral_congr_ae
  filter_upwards with t
  rw [centeredBSplineImagTransform_scaledTranslated_pair_re_closedForm
    k ell v u t hell]

/-- The unbundled Arch pairing of two translated normalized B-spline packets is
the concrete Arch profile at the center difference. -/
theorem centeredBSplineArchPairing_scaledTranslated_closed
    (k : ℕ) (ell u v : ℝ) (hell : 0 < ell) :
    centeredBSplineArchPairing
        (complexScaledTranslatedBump
          (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell u)
        (complexScaledTranslatedBump
          (fun x : ℝ => (centeredBSplineEta k x : ℂ)) ell v) =
      centeredBSplineArchKernelProfile k ell (u - v) := by
  exact centeredBSplineArchKernelProfile_pair_laplace_closed k ell u v hell

/-- Wiring helper: once an Arch bilinear form is known to agree with the
concrete Arch profile on translated copies of the base packet, it instantiates
the abstract translated-kernel receiver. -/
def centeredBSplinePacketTranslationArchData
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (ell : ℝ)
    (center : ι → ℝ)
    (basisExpansion : PacketBasisExpansion ι V)
    (base : V)
    (translate : ℝ → V → V)
    (form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (basis_eq_translate :
      ∀ i : ι, basisExpansion.basis i = translate (center i) base)
    (pairing_translate_ident :
      ∀ u v : ℝ,
        form (translate u base) (translate v base) =
          centeredBSplineArchKernelProfile k ell (u - v)) :
    PacketTranslationKernelData ι V where
  center := center
  basisExpansion := basisExpansion
  base := base
  translate := translate
  form := form
  profile := centeredBSplineArchKernelProfile k ell
  basis_eq_translate := basis_eq_translate
  pairing_translate_ident := pairing_translate_ident

/-- Arch wiring helper from an unbundled real bilinear pairing.  The analytic
side usually proves the translated-packet identity for a concrete pairing
function first; this packages that pairing into the curried `LinearMap` form
needed by the finite receiver. -/
def centeredBSplinePacketTranslationArchData_ofPairing
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (ell : ℝ)
    (center : ι → ℝ)
    (basisExpansion : PacketBasisExpansion ι V)
    (base : V)
    (translate : ℝ → V → V)
    (B : V → V → ℝ)
    (map_add_left : ∀ x y z : V, B (x + y) z = B x z + B y z)
    (map_smul_left : ∀ (c : ℝ) (x z : V), B (c • x) z = c * B x z)
    (map_add_right : ∀ x y z : V, B x (y + z) = B x y + B x z)
    (map_smul_right : ∀ (c : ℝ) (x y : V), B x (c • y) = c * B x y)
    (basis_eq_translate :
      ∀ i : ι, basisExpansion.basis i = translate (center i) base)
    (pairing_translate_ident :
      ∀ u v : ℝ,
        B (translate u base) (translate v base) =
          centeredBSplineArchKernelProfile k ell (u - v)) :
    PacketTranslationKernelData ι V :=
  PacketTranslationKernelData.ofPairing
    center basisExpansion base translate B
    (centeredBSplineArchKernelProfile k ell)
    map_add_left map_smul_left map_add_right map_smul_right
    basis_eq_translate pairing_translate_ident

/-- The plus boundary scale for the concrete bump. -/
def centeredBSplineBoundaryPlusScale (k : ℕ) (ell : ℝ) : ℝ :=
  Real.sqrt ell * centeredBSplineRealTransformProfile k ell (1 / 2)

/-- The minus boundary scale for the concrete bump. -/
def centeredBSplineBoundaryMinusScale (k : ℕ) (ell : ℝ) : ℝ :=
  Real.sqrt ell * centeredBSplineRealTransformProfile k ell (-(1 / 2))

/-- Closed-form RHS for the plus boundary scale. -/
def centeredBSplineBoundaryPlusScaleClosedForm (k : ℕ) (ell : ℝ) : ℝ :=
  Real.sqrt ell *
    (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
      (realSinhc (ell / (4 * bsplineScale k))) ^ (k + 1)

/-- Closed-form RHS for the minus boundary scale. -/
def centeredBSplineBoundaryMinusScaleClosedForm (k : ℕ) (ell : ℝ) : ℝ :=
  Real.sqrt ell *
    (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹ *
      (realSinhc (-(ell / (4 * bsplineScale k)))) ^ (k + 1)

/-- The plus boundary scale is the normalized B-spline transform at `1 / 2`,
hence the `realSinhc` closed form at `ell / (4 * s_k)`. -/
theorem centeredBSplineBoundaryPlusScale_eq_closedForm
    (k : ℕ) (ell : ℝ) :
    centeredBSplineBoundaryPlusScale k ell =
      centeredBSplineBoundaryPlusScaleClosedForm k ell := by
  unfold centeredBSplineBoundaryPlusScale
    centeredBSplineBoundaryPlusScaleClosedForm
  rw [centeredBSplineRealTransformProfile_eq_closedForm]
  unfold centeredBSplineRealTransformClosedForm
  have harg :
      ell * (1 / 2 : ℝ) / (2 * bsplineScale k) =
        ell / (4 * bsplineScale k) := by
    ring
  rw [harg]
  ring

/-- The minus boundary scale is the normalized B-spline transform at `-1 / 2`,
hence the `realSinhc` closed form at `-ell / (4 * s_k)`. -/
theorem centeredBSplineBoundaryMinusScale_eq_closedForm
    (k : ℕ) (ell : ℝ) :
    centeredBSplineBoundaryMinusScale k ell =
      centeredBSplineBoundaryMinusScaleClosedForm k ell := by
  unfold centeredBSplineBoundaryMinusScale
    centeredBSplineBoundaryMinusScaleClosedForm
  rw [centeredBSplineRealTransformProfile_eq_closedForm]
  unfold centeredBSplineRealTransformClosedForm
  have harg :
      ell * (-(1 / 2 : ℝ)) / (2 * bsplineScale k) =
        -(ell / (4 * bsplineScale k)) := by
    ring
  rw [harg]
  ring

/-- The strict centered box is nonnegative. -/
theorem centeredBoxSpline_nonneg (x : ℝ) :
    0 ≤ centeredBoxSpline x := by
  unfold centeredBoxSpline
  simp only [positivePartPower_zero]
  split_ifs with hleft hright
  · norm_num
  · norm_num
  · linarith
  · norm_num

/-- Every centered-box convolution power is nonnegative. -/
theorem centeredCardinalBSplineConvPower_nonneg
    (k : ℕ) (x : ℝ) :
    0 ≤ centeredCardinalBSplineConvPower k x := by
  induction k generalizing x with
  | zero =>
      simpa [centeredCardinalBSplineConvPower_zero] using centeredBoxSpline_nonneg x
  | succ k ih =>
      change 0 ≤ realConvolution (centeredCardinalBSplineConvPower k) centeredBoxSpline x
      unfold realConvolution
      exact integral_nonneg fun y =>
        mul_nonneg (ih y) (centeredBoxSpline_nonneg (x - y))

/-- Executable centered-cardinal B-splines are nonnegative. -/
theorem centeredCardinalBSpline_nonneg
    (k : ℕ) (x : ℝ) :
    0 ≤ centeredCardinalBSpline k x := by
  rw [CenteredCardinalBSplineMatchesConvPower_all k x]
  exact centeredCardinalBSplineConvPower_nonneg k x

/-- Every centered-cardinal B-spline is positive somewhere. -/
theorem centeredCardinalBSpline_exists_pos
    (k : ℕ) :
    ∃ x : ℝ, 0 < centeredCardinalBSpline k x := by
  cases k with
  | zero =>
      refine ⟨0, ?_⟩
      rw [centeredCardinalBSpline_zero_eq_centeredBoxSpline]
      norm_num [centeredBoxSpline, positivePartPower]
  | succ k =>
      exact ⟨-((k + 1 : ℕ) : ℝ) / 2,
        centeredCardinalBSpline_left_interior_pos (k + 1) (Nat.succ_pos k)⟩

/-- The normalized centered B-spline bump is nonnegative. -/
theorem centeredBSplineEta_nonneg
    (k : ℕ) (x : ℝ) :
    0 ≤ centeredBSplineEta k x := by
  unfold centeredBSplineEta
  exact mul_nonneg (Real.sqrt_nonneg _)
    (centeredCardinalBSpline_nonneg k (bsplineScale k * x))

/-- The normalized centered B-spline bump is positive somewhere. -/
theorem centeredBSplineEta_exists_pos
    (k : ℕ) :
    ∃ x : ℝ, 0 < centeredBSplineEta k x := by
  rcases centeredCardinalBSpline_exists_pos k with ⟨y, hy⟩
  refine ⟨y / bsplineScale k, ?_⟩
  unfold centeredBSplineEta
  have harg : bsplineScale k * (y / bsplineScale k) = y := by
    field_simp [bsplineScale_ne_zero k]
  rw [harg]
  exact mul_pos
    (Real.sqrt_pos.mpr
      (div_pos (bsplineScale_pos k) (bsplineAutocorrNorm_pos k)))
    hy

/-- Positive-degree normalized centered B-spline bumps are continuous. -/
theorem centeredBSplineEta_continuous_of_pos
    (k : ℕ) (hk : 0 < k) :
    Continuous (centeredBSplineEta k) := by
  unfold centeredBSplineEta
  refine continuous_const.mul ?_
  exact (centeredCardinalBSpline_continuous_of_pos k hk).comp
    (continuous_const.mul continuous_id)

/-- Executable centered-cardinal B-splines are compactly supported. -/
theorem centeredCardinalBSpline_hasCompactSupport
    (k : ℕ) :
    HasCompactSupport (centeredCardinalBSpline k) := by
  have hfun :
      centeredCardinalBSpline k = centeredCardinalBSplineConvPower k := by
    funext x
    exact CenteredCardinalBSplineMatchesConvPower_all k x
  rw [hfun]
  exact centeredCardinalBSplineConvPower_hasCompactSupport k

/-- The normalized centered B-spline bump is compactly supported. -/
theorem centeredBSplineEta_hasCompactSupport
    (k : ℕ) :
    HasCompactSupport (centeredBSplineEta k) := by
  have hcard := centeredCardinalBSpline_hasCompactSupport k
  have hscaled :
      HasCompactSupport
        (fun x : ℝ => centeredCardinalBSpline k (bsplineScale k • x)) :=
    hcard.comp_smul (bsplineScale_ne_zero k)
  have hmul :
      HasCompactSupport
        ((fun _ : ℝ =>
            Real.sqrt (bsplineScale k / bsplineAutocorrNorm k)) *
          fun x : ℝ => centeredCardinalBSpline k (bsplineScale k * x)) :=
    hscaled.mul_left
  simpa [centeredBSplineEta, Pi.mul_apply, smul_eq_mul] using hmul

/-- Positive-degree boundary transform profiles are strictly positive at every
real spectral parameter. -/
theorem centeredBSplineRealTransformProfile_pos_of_pos_degree
    (k : ℕ) (hk : 0 < k) (ell z : ℝ) :
    0 < centeredBSplineRealTransformProfile k ell z := by
  unfold centeredBSplineRealTransformProfile realBumpTransformProfile
  let F : ℝ → ℝ :=
    fun x => centeredBSplineEta k x * Real.exp (z * (ell * x))
  have heta_cont := centeredBSplineEta_continuous_of_pos k hk
  have hcont : Continuous F := by
    exact heta_cont.mul
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.mul continuous_id)))
  have heta_comp := centeredBSplineEta_hasCompactSupport k
  have hcomp : HasCompactSupport F := by
    have hmul :
        HasCompactSupport
          ((centeredBSplineEta k) *
            fun x : ℝ => Real.exp (z * (ell * x))) :=
      heta_comp.mul_right
    simpa [F, Pi.mul_apply] using hmul
  have hnonneg : 0 ≤ F := by
    intro x
    exact mul_nonneg (centeredBSplineEta_nonneg k x) (le_of_lt (Real.exp_pos _))
  rcases centeredBSplineEta_exists_pos k with ⟨x, hx⟩
  have hxF : F x ≠ 0 := by
    exact ne_of_gt (mul_pos hx (Real.exp_pos _))
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hcomp hnonneg hxF

/-- The plus boundary row scale is positive for positive-degree concrete
B-spline packets. -/
theorem centeredBSplineBoundaryPlusScale_pos_of_pos_degree
    (k : ℕ) (ell : ℝ) (hk : 0 < k) (hell : 0 < ell) :
    0 < centeredBSplineBoundaryPlusScale k ell := by
  unfold centeredBSplineBoundaryPlusScale
  exact mul_pos (Real.sqrt_pos.mpr hell)
    (centeredBSplineRealTransformProfile_pos_of_pos_degree k hk ell (1 / 2))

/-- The minus boundary row scale is positive for positive-degree concrete
B-spline packets. -/
theorem centeredBSplineBoundaryMinusScale_pos_of_pos_degree
    (k : ℕ) (ell : ℝ) (hk : 0 < k) (hell : 0 < ell) :
    0 < centeredBSplineBoundaryMinusScale k ell := by
  unfold centeredBSplineBoundaryMinusScale
  exact mul_pos (Real.sqrt_pos.mpr hell)
    (centeredBSplineRealTransformProfile_pos_of_pos_degree k hk ell (-(1 / 2)))

/-- The plus boundary row scale is nonzero for positive-degree concrete
B-spline packets. -/
theorem centeredBSplineBoundaryPlusScale_ne_zero_of_pos_degree
    (k : ℕ) (ell : ℝ) (hk : 0 < k) (hell : 0 < ell) :
    centeredBSplineBoundaryPlusScale k ell ≠ 0 :=
  (centeredBSplineBoundaryPlusScale_pos_of_pos_degree k ell hk hell).ne'

/-- The minus boundary row scale is nonzero for positive-degree concrete
B-spline packets. -/
theorem centeredBSplineBoundaryMinusScale_ne_zero_of_pos_degree
    (k : ℕ) (ell : ℝ) (hk : 0 < k) (hell : 0 < ell) :
    centeredBSplineBoundaryMinusScale k ell ≠ 0 :=
  (centeredBSplineBoundaryMinusScale_pos_of_pos_degree k ell hk hell).ne'

/--
Concrete boundary row formula for the centered cardinal B-spline packet.

This is an immediate specialization of the generic transform identity from
`PSD_BSplineAnalyticModel`.
-/
theorem centeredBSplineBoundaryPlus_basis
    (k : ℕ) (ell center : ℝ) (hell : 0 < ell) :
    realBumpLaplace
      (realScaledTranslatedBump (centeredBSplineEta k) ell center) (1 / 2) =
      centeredBSplineBoundaryPlusScale k ell * Real.exp (center / 2) := by
  simpa [centeredBSplineBoundaryPlusScale] using
    realBumpLaplace_scaledTranslated_plus (centeredBSplineEta k) ell center hell

/--
Concrete minus boundary row formula for the centered cardinal B-spline packet.
-/
theorem centeredBSplineBoundaryMinus_basis
    (k : ℕ) (ell center : ℝ) (hell : 0 < ell) :
    realBumpLaplace
      (realScaledTranslatedBump (centeredBSplineEta k) ell center) (-(1 / 2)) =
      centeredBSplineBoundaryMinusScale k ell * Real.exp (-(center) / 2) := by
  simpa [centeredBSplineBoundaryMinusScale] using
    realBumpLaplace_scaledTranslated_minus (centeredBSplineEta k) ell center hell

/--
Positive-degree concrete boundary scales feed the translated-packet boundary
receiver.

This is the small wiring step between the concrete centered B-spline boundary
scale facts and the abstract `PacketTranslationBoundaryData` contract.  The
actual translation covariance and base scale identities are supplied by the
caller; the new content here is that the base scales are now known to be
nonzero for `0 < k` and `0 < ell`.
-/
def centeredBSplinePacketTranslationBoundaryData_of_pos_degree
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (ell : ℝ) (hk : 0 < k) (hell : 0 < ell)
    (center : ι → ℝ)
    (basisExpansion : PacketBasisExpansion ι V)
    (boundary : BoundaryPair V)
    (base : V)
    (translate : ℝ → V → V)
    (basis_eq_translate :
      ∀ i : ι, basisExpansion.basis i = translate (center i) base)
    (boundaryPlus_translate :
      ∀ (u : ℝ) (f : V),
        boundary.evalPlus (translate u f) =
          Real.exp (u / 2) * boundary.evalPlus f)
    (boundaryMinus_translate :
      ∀ (u : ℝ) (f : V),
        boundary.evalMinus (translate u f) =
          Real.exp (-(u) / 2) * boundary.evalMinus f)
    (basePlus_eq :
      boundary.evalPlus base = centeredBSplineBoundaryPlusScale k ell)
    (baseMinus_eq :
      boundary.evalMinus base = centeredBSplineBoundaryMinusScale k ell) :
    PacketTranslationBoundaryData ι V where
  center := center
  basisExpansion := basisExpansion
  boundary := boundary
  base := base
  translate := translate
  basis_eq_translate := basis_eq_translate
  boundaryPlus_translate := boundaryPlus_translate
  boundaryMinus_translate := boundaryMinus_translate
  basePlus_ne_zero := by
    rw [basePlus_eq]
    exact centeredBSplineBoundaryPlusScale_ne_zero_of_pos_degree k ell hk hell
  baseMinus_ne_zero := by
    rw [baseMinus_eq]
    exact centeredBSplineBoundaryMinusScale_ne_zero_of_pos_degree k ell hk hell

/--
Concrete packet-shift correlation reduces to the actual correlation profile of
`eta_k`.

The remaining closed-form theorem is
`CenteredBSplineAutocorrelationClosedForm`, which rewrites this profile to
`centeredBSplineR`.
-/
theorem centeredBSplineCorrelation_scaledTranslated_shift
    (k : ℕ) (ell ui uj a : ℝ) (hell : 0 < ell) :
    (∫ u : ℝ,
        realScaledTranslatedBump (centeredBSplineEta k) ell uj u *
          realShift a (realScaledTranslatedBump (centeredBSplineEta k) ell ui) u) =
      centeredBSplineCorrelationProfile k ((uj - ui - a) / ell) := by
  simpa [centeredBSplineCorrelationProfile] using
    realBumpCorrelation_scaledTranslated_shift
      (centeredBSplineEta k) ell ui uj a hell

/--
If the centered-cardinal autocorrelation closed form is available, the concrete
packet-shift correlation becomes exactly the PSD-pd `r_k` profile.
-/
theorem centeredBSplineCorrelation_scaledTranslated_shift_closed
    (k : ℕ) (ell ui uj a : ℝ) (hell : 0 < ell)
    (hclosed : CenteredBSplineAutocorrelationClosedForm k) :
    (∫ u : ℝ,
        realScaledTranslatedBump (centeredBSplineEta k) ell uj u *
          realShift a (realScaledTranslatedBump (centeredBSplineEta k) ell ui) u) =
      centeredBSplineR k ((uj - ui - a) / ell) := by
  rw [centeredBSplineCorrelation_scaledTranslated_shift k ell ui uj a hell]
  exact hclosed ((uj - ui - a) / ell)

end PSDpd
end Q3
