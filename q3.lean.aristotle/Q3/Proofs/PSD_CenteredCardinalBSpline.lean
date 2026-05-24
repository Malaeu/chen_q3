import Q3.Basic.Defs
import Q3.Axioms
import Q3.Proofs.PSD_BSplineAnalyticModel
import Q3.Proofs.PSD_CertificateFamily
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

noncomputable section

open MeasureTheory
open Set
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

/-- The local `realSinc` convention agrees with Mathlib's `Real.sinc`. -/
theorem realSinc_eq_sinc :
    realSinc = Real.sinc := by
  funext x
  by_cases hx : x = 0
  · simp [realSinc, Real.sinc, hx]
  · simp [realSinc, Real.sinc, hx]

/-- The regularized sinc factor has absolute value at most one. -/
theorem realSinc_abs_le_one (x : ℝ) :
    |realSinc x| ≤ 1 := by
  rw [realSinc_eq_sinc]
  exact Real.abs_sinc_le_one x

/-- Away from zero, the regularized sinc factor is bounded by `1 / |x|`. -/
theorem realSinc_le_inv_abs {x : ℝ} (hx : x ≠ 0) :
    realSinc x ≤ |x|⁻¹ := by
  rw [realSinc_eq_sinc]
  exact Real.sinc_le_inv_abs hx

/-- Away from zero, the absolute value of the regularized sinc is bounded by
`1 / |x|`. -/
theorem realSinc_abs_le_inv_abs {x : ℝ} (hx : x ≠ 0) :
    |realSinc x| ≤ |x|⁻¹ := by
  rw [realSinc_of_ne_zero hx, abs_div]
  have hsin : |Real.sin x| ≤ (1 : ℝ) := Real.abs_sin_le_one x
  have hxnonneg : 0 ≤ |x| := abs_nonneg x
  calc
    |Real.sin x| / |x| ≤ 1 / |x| :=
      div_le_div_of_nonneg_right hsin hxnonneg
    _ = |x|⁻¹ := by ring

/-- The regularized sinc factor is even. -/
theorem realSinc_neg (x : ℝ) :
    realSinc (-x) = realSinc x := by
  rw [realSinc_eq_sinc]
  exact Real.sinc_neg x

/-- The regularized sinc factor is continuous. -/
theorem realSinc_continuous :
    Continuous realSinc := by
  rw [realSinc_eq_sinc]
  exact Real.continuous_sinc

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

/-- The real imaginary-axis closed form is continuous in the spectral variable. -/
theorem centeredBSplineImagTransformRealClosedForm_continuous
    (k : ℕ) (ell : ℝ) :
    Continuous (fun t : ℝ => centeredBSplineImagTransformRealClosedForm k ell t) := by
  unfold centeredBSplineImagTransformRealClosedForm
  refine continuous_const.mul ?_
  exact (realSinc_continuous.comp (by continuity)).pow (k + 1)

/-- The real imaginary-axis closed form is even in the spectral variable. -/
theorem centeredBSplineImagTransformRealClosedForm_neg
    (k : ℕ) (ell t : ℝ) :
    centeredBSplineImagTransformRealClosedForm k ell (-t) =
      centeredBSplineImagTransformRealClosedForm k ell t := by
  unfold centeredBSplineImagTransformRealClosedForm
  have harg :
      ell * (-t) / (2 * bsplineScale k) =
        -(ell * t / (2 * bsplineScale k)) := by
    ring
  rw [harg, realSinc_neg]

/-- Positive-tail bound for the `a_star`-weighted square of the closed
imaginary-axis B-spline transform.  For positive spline degree the sinc power
contains at least four powers of `sinc`, so the linear growth of `a_star` is
dominated by a `t^-3` tail. -/
theorem a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_tail_bound
    (k : ℕ) (ell t C0 C1 : ℝ)
    (hk : 0 < k) (hell : 0 < ell)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hgrowth : |Q3.a_star t| ≤ C0 + C1 * |t|) (ht : 1 ≤ t) :
    ‖Q3.a_star t * (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2‖ ≤
      ((C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
        (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4) * t ^ (-3 : ℝ) := by
  let D : ℝ := (Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹
  let c : ℝ := ell / (2 * bsplineScale k)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hc_ne : c ≠ 0 := by
    unfold c
    exact div_ne_zero hell.ne'
      (mul_ne_zero (by norm_num) (bsplineScale_ne_zero k))
  have harg :
      ell * t / (2 * bsplineScale k) = c * t := by
    unfold c
    ring
  have hsinc4 :
      |realSinc (c * t)| ^ 4 ≤ (|c|⁻¹) ^ 4 * t ^ (-4 : ℝ) := by
    have hct : c * t ≠ 0 := mul_ne_zero hc_ne htpos.ne'
    have hsinc := realSinc_abs_le_inv_abs hct
    have hpow :
        |realSinc (c * t)| ^ 4 ≤ (|c * t|⁻¹) ^ 4 := by
      exact pow_le_pow_left₀ (abs_nonneg _) hsinc 4
    calc
      |realSinc (c * t)| ^ 4 ≤ (|c * t|⁻¹) ^ 4 := hpow
      _ = (|c|⁻¹) ^ 4 * t ^ (-4 : ℝ) := by
        rw [abs_mul, abs_of_pos htpos]
        have hcabs : |c| ≠ 0 := abs_ne_zero.mpr hc_ne
        have htne : t ≠ 0 := htpos.ne'
        rw [Real.rpow_neg (le_of_lt htpos)]
        field_simp [hcabs, htne]
        norm_num [Real.rpow_natCast]
  have hsincpow_le :
      |realSinc (c * t)| ^ (2 * (k + 1)) ≤
        |realSinc (c * t)| ^ 4 := by
    have hx0 : 0 ≤ |realSinc (c * t)| := abs_nonneg _
    have hx1 : |realSinc (c * t)| ≤ 1 := realSinc_abs_le_one _
    have hpow : 4 ≤ 2 * (k + 1) := by
      have hk1 : 2 ≤ k + 1 := Nat.succ_le_succ hk
      nlinarith
    exact pow_le_pow_of_le_one hx0 hx1 hpow
  have hEabs :
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 ≤
        |D| ^ 2 * |realSinc (c * t)| ^ (2 * (k + 1)) := by
    apply le_of_eq
    unfold centeredBSplineImagTransformRealClosedForm D
    rw [harg]
    rw [abs_mul]
    rw [abs_pow]
    rw [mul_pow]
    ring_nf
  have hEabs4 :
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 ≤
        |D| ^ 2 * ((|c|⁻¹) ^ 4 * t ^ (-4 : ℝ)) := by
    calc
      |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 ≤
          |D| ^ 2 * |realSinc (c * t)| ^ (2 * (k + 1)) := hEabs
      _ ≤ |D| ^ 2 * |realSinc (c * t)| ^ 4 := by
        exact mul_le_mul_of_nonneg_left hsincpow_le (sq_nonneg |D|)
      _ ≤ |D| ^ 2 * ((|c|⁻¹) ^ 4 * t ^ (-4 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsinc4 (sq_nonneg |D|)
  have ha : |Q3.a_star t| ≤ (C0 + C1) * t := by
    calc
      |Q3.a_star t| ≤ C0 + C1 * |t| := hgrowth
      _ = C0 + C1 * t := by rw [abs_of_pos htpos]
      _ ≤ (C0 + C1) * t := by
        nlinarith [hC0, hC1, ht]
  have ht_rpow :
      t * t ^ (-4 : ℝ) = t ^ (-3 : ℝ) := by
    calc
      t * t ^ (-4 : ℝ) =
          t ^ (1 : ℝ) * t ^ (-4 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (-4 : ℝ)) := by rw [Real.rpow_add htpos]
      _ = t ^ (-3 : ℝ) := by norm_num
  have hmain :
      |Q3.a_star t| *
          |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 ≤
        ((C0 + C1) * |D| ^ 2 * (|c|⁻¹) ^ 4) * t ^ (-3 : ℝ) := by
    calc
      |Q3.a_star t| *
          |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 ≤
        ((C0 + C1) * t) *
          (|D| ^ 2 * ((|c|⁻¹) ^ 4 * t ^ (-4 : ℝ))) := by
            exact mul_le_mul ha hEabs4 (sq_nonneg _) (by positivity)
      _ = ((C0 + C1) * |D| ^ 2 * (|c|⁻¹) ^ 4) * t ^ (-3 : ℝ) := by
        rw [← ht_rpow]
        ring
  calc
    ‖Q3.a_star t * (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2‖
        = |Q3.a_star t| *
            |centeredBSplineImagTransformRealClosedForm k ell t| ^ 2 := by
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
    _ ≤ ((C0 + C1) * |D| ^ 2 * (|c|⁻¹) ^ 4) * t ^ (-3 : ℝ) := hmain
    _ = ((C0 + C1) *
          |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
        (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4) * t ^ (-3 : ℝ) := by
          simp [D, c]

/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side-adjacent Arch form
- role: Step32F Arch t-side tail integrability
- input: closed imaginary-axis B-spline transform, realSinc decay bounds, a_star linear growth
- output: a_star-weighted square of centered B-spline imaginary transform is integrable for 0 < k
- reviewer question answered: is the Arch pairing an actual L¹ analytic integral, rather than a formal translated-profile wrapper?
-/
set_option maxHeartbeats 800000 in
theorem a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
    (k : ℕ) (ell : ℝ) (hk : 0 < k) (hell : 0 < ell) :
    Integrable (fun t : ℝ =>
      Q3.a_star t * (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2) := by
  let f : ℝ → ℝ := fun t =>
    Q3.a_star t * (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2
  rcases Q3.a_star_linear_growth with ⟨C0, C1, hC0, hC1, hgrowth⟩
  let M : ℝ :=
    (C0 + C1) * |(Real.sqrt (bsplineScale k * bsplineAutocorrNorm k))⁻¹| ^ 2 *
      (|(ell / (2 * bsplineScale k))|⁻¹) ^ 4
  have hcontE := centeredBSplineImagTransformRealClosedForm_continuous k ell
  have hcont : Continuous f := by
    dsimp [f]
    exact Q3.a_star_continuous.mul (hcontE.pow 2)
  have htail_bound :
      ∀ t ∈ Ioi (1 : ℝ), ‖f t‖ ≤ M * t ^ (-3 : ℝ) := by
    intro t ht
    dsimp [f, M]
    exact a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_tail_bound
      k ell t C0 C1 hk hell hC0 hC1 (hgrowth t)
      (le_of_lt (show (1 : ℝ) < t from ht))
  have htail_majorant :
      Integrable (fun t : ℝ => M * t ^ (-3 : ℝ))
        (volume.restrict (Ioi (1 : ℝ))) := by
    have h :
        IntegrableOn (fun t : ℝ => M * t ^ (-3 : ℝ))
          (Ioi (1 : ℝ)) := by
      exact (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-3 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul M
    simpa [IntegrableOn] using h
  have htail : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))) :=
      hcont.aestronglyMeasurable
    have htail_int : Integrable f (volume.restrict (Ioi (1 : ℝ))) := by
      refine htail_majorant.mono' hf_meas ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono ?_
      intro t ht
      exact htail_bound t ht
    simpa [IntegrableOn] using htail_int
  have hcompact : IntegrableOn f (Icc (0 : ℝ) 1) := by
    exact hcont.integrableOn_Icc
  have hpos : IntegrableOn f (Ici (0 : ℝ)) := by
    have hunion : IntegrableOn f (Icc (0 : ℝ) 1 ∪ Ioi (1 : ℝ)) :=
      hcompact.union htail
    have hset : Icc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ici (0 : ℝ) := by
      ext x
      constructor
      · intro hx
        rcases hx with hx | hx
        · exact hx.1
        · exact le_trans zero_le_one
            (le_of_lt (show (1 : ℝ) < x from hx))
      · intro hx0
        by_cases hx1 : x ≤ 1
        · exact Or.inl ⟨hx0, hx1⟩
        · exact Or.inr (lt_of_not_ge hx1)
    simpa [hset] using hunion
  have hneg_pre : IntegrableOn (fun x : ℝ => f (-x)) (Iic (0 : ℝ)) := by
    have hpos0 : IntegrableOn f (Ici (-(0 : ℝ))) := by
      simpa using hpos
    simpa using (hpos0.comp_neg_Iic (c := (0 : ℝ)))
  have hneg : IntegrableOn f (Iic (0 : ℝ)) := by
    refine hneg_pre.congr_fun ?_ measurableSet_Iic
    intro x _hx
    dsimp [f]
    rw [Q3.a_star_even x]
    rw [centeredBSplineImagTransformRealClosedForm_neg]
  have hall : IntegrableOn f univ := by
    have hunion : IntegrableOn f (Iic (0 : ℝ) ∪ Ici (0 : ℝ)) :=
      hneg.union hpos
    simpa [Set.Iic_union_Ici] using hunion
  have hfinal : Integrable f := by
    simpa [integrableOn_univ] using hall
  simpa [f]

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

/-- Integrand used by the concrete Arch pairing. -/
def centeredBSplineArchIntegrand (f g : ℝ → ℂ) (t : ℝ) : ℝ :=
  Q3.a_star t *
    (complexBumpLaplace f (Complex.I * (t : ℂ)) *
      star (complexBumpLaplace g (Complex.I * (t : ℂ)))).re

/-- Additivity of the complex packet transform under the exact weighted
integrability hypotheses required by the Bochner integral. -/
theorem complexBumpLaplace_add_of_integrable
    (f g : ℝ → ℂ) (z : ℂ)
    (hf : Integrable (fun x : ℝ => f x * Complex.exp (z * (x : ℂ))))
    (hg : Integrable (fun x : ℝ => g x * Complex.exp (z * (x : ℂ)))) :
    complexBumpLaplace (fun x : ℝ => f x + g x) z =
      complexBumpLaplace f z + complexBumpLaplace g z := by
  unfold complexBumpLaplace
  rw [← integral_add hf hg]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- Real scalar homogeneity of the complex packet transform. -/
theorem complexBumpLaplace_smul
    (c : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    complexBumpLaplace (c • f) z =
      (c : ℂ) * complexBumpLaplace f z := by
  unfold complexBumpLaplace
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp [Pi.smul_apply]
  ring

/-- Left additivity of the concrete Arch pairing, separated from the remaining
packet-span integrability obligations. -/
theorem centeredBSplineArchPairing_add_left
    (f₁ f₂ g : ℝ → ℂ)
    (hf₁ : ∀ t : ℝ,
      Integrable
        (fun x : ℝ =>
          f₁ x * Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))))
    (hf₂ : ∀ t : ℝ,
      Integrable
        (fun x : ℝ =>
          f₂ x * Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))))
    (hI₁ : Integrable (centeredBSplineArchIntegrand f₁ g))
    (hI₂ : Integrable (centeredBSplineArchIntegrand f₂ g)) :
    centeredBSplineArchPairing (fun x => f₁ x + f₂ x) g =
      centeredBSplineArchPairing f₁ g + centeredBSplineArchPairing f₂ g := by
  unfold centeredBSplineArchPairing
  change
    (∫ t : ℝ, centeredBSplineArchIntegrand (fun x => f₁ x + f₂ x) g t) =
      (∫ t : ℝ, centeredBSplineArchIntegrand f₁ g t) +
        ∫ t : ℝ, centeredBSplineArchIntegrand f₂ g t
  rw [← integral_add hI₁ hI₂]
  apply integral_congr_ae
  filter_upwards with t
  unfold centeredBSplineArchIntegrand
  rw [complexBumpLaplace_add_of_integrable]
  · rw [add_mul, Complex.add_re]
    ring
  · exact hf₁ t
  · exact hf₂ t

/-- Left real homogeneity of the concrete Arch pairing. -/
theorem centeredBSplineArchPairing_smul_left
    (c : ℝ) (f g : ℝ → ℂ) :
    centeredBSplineArchPairing (c • f) g =
      c * centeredBSplineArchPairing f g := by
  unfold centeredBSplineArchPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [complexBumpLaplace_smul]
  change
    Q3.a_star t *
        (((c : ℂ) * complexBumpLaplace f (Complex.I * (t : ℂ))) *
          star (complexBumpLaplace g (Complex.I * (t : ℂ)))).re =
      c *
        (Q3.a_star t *
          (complexBumpLaplace f (Complex.I * (t : ℂ)) *
            star (complexBumpLaplace g (Complex.I * (t : ℂ)))).re)
  simp
  ring

/-- Right additivity of the concrete Arch pairing, separated from the remaining
packet-span integrability obligations. -/
theorem centeredBSplineArchPairing_add_right
    (f g₁ g₂ : ℝ → ℂ)
    (hg₁ : ∀ t : ℝ,
      Integrable
        (fun x : ℝ =>
          g₁ x * Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))))
    (hg₂ : ∀ t : ℝ,
      Integrable
        (fun x : ℝ =>
          g₂ x * Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))))
    (hI₁ : Integrable (centeredBSplineArchIntegrand f g₁))
    (hI₂ : Integrable (centeredBSplineArchIntegrand f g₂)) :
    centeredBSplineArchPairing f (fun x => g₁ x + g₂ x) =
      centeredBSplineArchPairing f g₁ + centeredBSplineArchPairing f g₂ := by
  unfold centeredBSplineArchPairing
  change
    (∫ t : ℝ, centeredBSplineArchIntegrand f (fun x => g₁ x + g₂ x) t) =
      (∫ t : ℝ, centeredBSplineArchIntegrand f g₁ t) +
        ∫ t : ℝ, centeredBSplineArchIntegrand f g₂ t
  rw [← integral_add hI₁ hI₂]
  apply integral_congr_ae
  filter_upwards with t
  unfold centeredBSplineArchIntegrand
  rw [complexBumpLaplace_add_of_integrable]
  · rw [star_add, mul_add, Complex.add_re]
    ring
  · exact hg₁ t
  · exact hg₂ t

/-- Right real homogeneity of the concrete Arch pairing. -/
theorem centeredBSplineArchPairing_smul_right
    (c : ℝ) (f g : ℝ → ℂ) :
    centeredBSplineArchPairing f (c • g) =
      c * centeredBSplineArchPairing f g := by
  unfold centeredBSplineArchPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [complexBumpLaplace_smul]
  change
    Q3.a_star t *
        (complexBumpLaplace f (Complex.I * (t : ℂ)) *
          star ((c : ℂ) * complexBumpLaplace g (Complex.I * (t : ℂ)))).re =
      c *
        (Q3.a_star t *
          (complexBumpLaplace f (Complex.I * (t : ℂ)) *
            star (complexBumpLaplace g (Complex.I * (t : ℂ)))).re)
  rw [star_mul]
  simp
  ring

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
/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side-adjacent Arch form / Coordinate
- role: tactical Step32F Arch assembly
- input: concrete centeredBSplineArchPairing, translated profile identity, ofPairing bundling layer
- output: concrete Arch PacketTranslationKernelData for centered B-spline packets
- reviewer question answered: is the Arch matrix entry produced by an actual analytic bilinear form, not just by a profile-level formula or receiver wrapper?
-/
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

/-- A translated/scaled positive-degree normalized B-spline packet has an
imaginary-axis weighted transform integrand in `L¹`.  This is the local
Bochner-integrability fact needed when linearity of the concrete Arch pairing
is applied to finite packet spans. -/
theorem centeredBSplineTranslatedPacket_complexBumpLaplace_imag_integrable
    (k : ℕ) (ell center t : ℝ) (hk : 0 < k) (hell : 0 < ell) :
    Integrable
      (fun x : ℝ =>
        complexScaledTranslatedBump
            (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell center x *
          Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))) := by
  have heta_cont_real : Continuous (centeredBSplineEta k) :=
    centeredBSplineEta_continuous_of_pos k hk
  have heta_cont : Continuous (fun y : ℝ => (centeredBSplineEta k y : ℂ)) :=
    Complex.continuous_ofReal.comp heta_cont_real
  have harg_cont : Continuous (fun x : ℝ => (x - center) / ell) := by
    continuity
  have hpacket_cont : Continuous
      (complexScaledTranslatedBump
        (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell center) := by
    unfold complexScaledTranslatedBump
    exact continuous_const.mul (heta_cont.comp harg_cont)
  have heta_comp_real : HasCompactSupport (centeredBSplineEta k) :=
    centeredBSplineEta_hasCompactSupport k
  have heta_comp : HasCompactSupport (fun y : ℝ => (centeredBSplineEta k y : ℂ)) := by
    have hcast : HasCompactSupport ((fun r : ℝ => (r : ℂ)) ∘ centeredBSplineEta k) :=
      heta_comp_real.comp_left (by simp)
    simpa [Function.comp_def] using hcast
  have hscale : HasCompactSupport
      (fun x : ℝ => (centeredBSplineEta k ((ell⁻¹) • x) : ℂ)) := by
    simpa using heta_comp.comp_smul (inv_ne_zero hell.ne')
  have htrans : HasCompactSupport
      (fun x : ℝ => (centeredBSplineEta k ((ell⁻¹) • (x + -center)) : ℂ)) := by
    have h := hscale.comp_homeomorph (Homeomorph.addRight (-center))
    simpa [Function.comp_def] using h
  have hpacket_comp : HasCompactSupport
      (complexScaledTranslatedBump
        (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell center) := by
    unfold complexScaledTranslatedBump
    have htrans' : HasCompactSupport
        (fun x : ℝ => (centeredBSplineEta k ((x - center) / ell) : ℂ)) := by
      convert htrans using 1
      ext x
      simp [sub_eq_add_neg, div_eq_mul_inv, smul_eq_mul, mul_comm]
    have hconst : HasCompactSupport
        ((fun _ : ℝ => ((Real.sqrt ell : ℂ)⁻¹)) *
          fun x : ℝ => (centeredBSplineEta k ((x - center) / ell) : ℂ)) :=
      htrans'.mul_left
    simpa [Pi.mul_apply] using hconst
  have hcont : Continuous
      (fun x : ℝ =>
        complexScaledTranslatedBump
            (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell center x *
          Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))) := by
    exact hpacket_cont.mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))
  have hcomp : HasCompactSupport
      (fun x : ℝ =>
        complexScaledTranslatedBump
            (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell center x *
          Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))) := by
    have hmul : HasCompactSupport
        (complexScaledTranslatedBump
            (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell center *
          fun x : ℝ => Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))) :=
      hpacket_comp.mul_right
    simpa [Pi.mul_apply] using hmul
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- Finite complex linear combinations of translated/scaled positive-degree
normalized B-spline packets have imaginary-axis weighted transform integrands in
`L¹`.  This packages the exact finite packet-span hypothesis consumed by
`complexBumpLaplace_add_of_integrable`. -/
theorem centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell t : ℝ) (coeff : ι → ℂ) (center : ι → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    Integrable
      (fun x : ℝ =>
        ((Finset.univ.sum fun i : ι =>
            coeff i *
              complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x) *
          Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ)))) := by
  have hsum : Integrable
      (fun x : ℝ =>
        Finset.univ.sum fun i : ι =>
          coeff i *
            (complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x *
              Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ)))) := by
    apply integrable_finset_sum
    intro i _hi
    have hi :=
      centeredBSplineTranslatedPacket_complexBumpLaplace_imag_integrable
        k ell (center i) t hk hell
    simpa [mul_assoc] using hi.const_mul (coeff i)
  simpa [Finset.sum_mul, mul_assoc] using hsum

/-- The imaginary-axis transform of a finite translated/scaled B-spline packet
sum is the corresponding finite sum of packet transforms.  This is the finite
packet-span transform linearity bridge used before the remaining Arch `t`-side
decay estimate. -/
theorem centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_eq_sum
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell t : ℝ) (coeff : ι → ℂ) (center : ι → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    complexBumpLaplace
        (fun x : ℝ =>
          Finset.univ.sum fun i : ι =>
            coeff i *
              complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x)
        (Complex.I * (t : ℂ)) =
      Finset.univ.sum fun i : ι =>
        coeff i *
          complexBumpLaplace
            (complexScaledTranslatedBump
              (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i))
            (Complex.I * (t : ℂ)) := by
  unfold complexBumpLaplace
  calc
    (∫ x : ℝ,
        (Finset.univ.sum fun i : ι =>
          coeff i *
            complexScaledTranslatedBump
              (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x) *
          Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ)))
        =
      ∫ x : ℝ,
        Finset.univ.sum fun i : ι =>
          coeff i *
            (complexScaledTranslatedBump
              (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x *
                Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ =
      Finset.univ.sum fun i : ι =>
        ∫ x : ℝ,
          coeff i *
            (complexScaledTranslatedBump
              (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x *
                Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ))) := by
          refine integral_finset_sum Finset.univ ?_
          intro i _hi
          have hi :=
            centeredBSplineTranslatedPacket_complexBumpLaplace_imag_integrable
              k ell (center i) t hk hell
          simpa [mul_assoc] using hi.const_mul (coeff i)
    _ =
      Finset.univ.sum fun i : ι =>
        coeff i *
          ∫ x : ℝ,
            complexScaledTranslatedBump
              (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x *
                Complex.exp ((Complex.I * (t : ℂ)) * (x : ℂ)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [integral_const_mul]

/-- Closed finite-sum form of the imaginary-axis transform of a translated
B-spline packet sum. -/
theorem centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell t : ℝ) (coeff : ι → ℂ) (center : ι → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    complexBumpLaplace
        (fun x : ℝ =>
          Finset.univ.sum fun i : ι =>
            coeff i *
              complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x)
        (Complex.I * (t : ℂ)) =
      Finset.univ.sum fun i : ι =>
        coeff i *
          ((Real.sqrt ell : ℂ) *
            Complex.exp ((Complex.I * (t : ℂ)) * (center i : ℂ)) *
              centeredBSplineImagTransformClosedForm k ell t) := by
  rw [centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_eq_sum
    k ell t coeff center hk hell]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [centeredBSplineImagTransform_scaledTranslated_eq_closedForm k ell (center i) t hell]

/-- Complex continuity of the normalized imaginary-axis closed form. -/
theorem centeredBSplineImagTransformClosedForm_continuous
    (k : ℕ) (ell : ℝ) :
    Continuous (fun t : ℝ => centeredBSplineImagTransformClosedForm k ell t) := by
  rw [show (fun t : ℝ => centeredBSplineImagTransformClosedForm k ell t) =
      fun t => (centeredBSplineImagTransformRealClosedForm k ell t : ℂ) by
    funext t
    rw [centeredBSplineImagTransformClosedForm_eq_ofReal]]
  exact Complex.continuous_ofReal.comp
    (centeredBSplineImagTransformRealClosedForm_continuous k ell)

/-- Norm bound for finite translated packet sums on the imaginary axis. -/
theorem centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_norm_bound
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell t : ℝ) (coeff : ι → ℂ) (center : ι → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    ‖complexBumpLaplace
        (fun x : ℝ =>
          Finset.univ.sum fun i : ι =>
            coeff i *
              complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x)
        (Complex.I * (t : ℂ))‖ ≤
      ((Finset.univ.sum fun i : ι => ‖coeff i‖) * Real.sqrt ell) *
        |centeredBSplineImagTransformRealClosedForm k ell t| := by
  rw [centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum
    k ell t coeff center hk hell]
  calc
    ‖Finset.univ.sum fun i : ι =>
        coeff i *
          ((Real.sqrt ell : ℂ) * Complex.exp ((Complex.I * (t : ℂ)) * (center i : ℂ)) *
            centeredBSplineImagTransformClosedForm k ell t)‖
        ≤ Finset.univ.sum fun i : ι =>
            ‖coeff i *
              ((Real.sqrt ell : ℂ) * Complex.exp ((Complex.I * (t : ℂ)) * (center i : ℂ)) *
                centeredBSplineImagTransformClosedForm k ell t)‖ := by
          simpa using norm_sum_le Finset.univ (fun i : ι =>
            coeff i *
              ((Real.sqrt ell : ℂ) * Complex.exp ((Complex.I * (t : ℂ)) * (center i : ℂ)) *
                centeredBSplineImagTransformClosedForm k ell t))
    _ = Finset.univ.sum fun i : ι =>
          ‖coeff i‖ * Real.sqrt ell *
            |centeredBSplineImagTransformRealClosedForm k ell t| := by
          apply Finset.sum_congr rfl
          intro i _hi
          have harg : (Complex.I * (t : ℂ)) * (center i : ℂ) =
              Complex.I * ((t * center i : ℝ) : ℂ) := by
            norm_num
            ring
          rw [norm_mul, norm_mul, norm_mul]
          rw [harg, Complex.norm_exp_I_mul_ofReal]
          rw [centeredBSplineImagTransformClosedForm_eq_ofReal]
          have hsqrt : ‖(Real.sqrt ell : ℂ)‖ = Real.sqrt ell := by
            simp [abs_of_nonneg (Real.sqrt_nonneg ell)]
          rw [hsqrt]
          simp [mul_assoc]
    _ = ((Finset.univ.sum fun i : ι => ‖coeff i‖) * Real.sqrt ell) *
          |centeredBSplineImagTransformRealClosedForm k ell t| := by
          rw [Finset.sum_mul]
          rw [Finset.sum_mul]

/-- Closed finite-packet Arch integrand is continuous. -/
theorem centeredBSplineArchIntegrandClosed_translatedPacketSum_continuous
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ℕ) (ell : ℝ) (coeffF : ι → ℂ) (centerF : ι → ℝ)
    (coeffG : κ → ℂ) (centerG : κ → ℝ) :
    Continuous (fun t : ℝ =>
      Q3.a_star t *
        ((Finset.univ.sum fun i : ι =>
          coeffF i * ((Real.sqrt ell : ℂ) *
            Complex.exp ((Complex.I * (t : ℂ)) * (centerF i : ℂ)) *
            centeredBSplineImagTransformClosedForm k ell t)) *
        star (Finset.univ.sum fun j : κ =>
          coeffG j * ((Real.sqrt ell : ℂ) *
            Complex.exp ((Complex.I * (t : ℂ)) * (centerG j : ℂ)) *
            centeredBSplineImagTransformClosedForm k ell t))).re) := by
  have hE := centeredBSplineImagTransformClosedForm_continuous k ell
  have hF : Continuous (fun t : ℝ => Finset.univ.sum fun i : ι =>
      coeffF i * ((Real.sqrt ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * (centerF i : ℂ)) *
        centeredBSplineImagTransformClosedForm k ell t)) := by
    refine continuous_finset_sum Finset.univ ?_
    intro i _hi
    exact continuous_const.mul
      ((continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))).mul hE)
  have hG : Continuous (fun t : ℝ => Finset.univ.sum fun j : κ =>
      coeffG j * ((Real.sqrt ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * (centerG j : ℂ)) *
        centeredBSplineImagTransformClosedForm k ell t)) := by
    refine continuous_finset_sum Finset.univ ?_
    intro j _hj
    exact continuous_const.mul
      ((continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))).mul hE)
  exact Q3.a_star_continuous.mul (Complex.continuous_re.comp (hF.mul hG.star))

/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side-adjacent Arch form
- role: Step32F Arch t-side well-definedness
- input: x-side packet Laplace integrability, finite packet closed form, a_star-weighted sinc-tail integrability
- output: Arch integrand for finite translated B-spline packet sums is integrable in t
- reviewer question answered: is the Arch pairing an actual analytic L¹ form on packet sums, rather than a formal profile wrapper?
-/
theorem centeredBSplineArchIntegrand_translatedPacketSum_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ℕ) (ell : ℝ) (coeffF : ι → ℂ) (centerF : ι → ℝ)
    (coeffG : κ → ℂ) (centerG : κ → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    Integrable
      (centeredBSplineArchIntegrand
        (fun x : ℝ =>
          Finset.univ.sum fun i : ι =>
            coeffF i *
              complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (centerF i) x)
        (fun x : ℝ =>
          Finset.univ.sum fun j : κ =>
            coeffG j *
              complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (centerG j) x)) := by
  let F : ℝ → ℂ := fun x =>
    Finset.univ.sum fun i : ι =>
      coeffF i *
        complexScaledTranslatedBump
          (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (centerF i) x
  let G : ℝ → ℂ := fun x =>
    Finset.univ.sum fun j : κ =>
      coeffG j *
        complexScaledTranslatedBump
          (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (centerG j) x
  let FC : ℝ → ℂ := fun t =>
    Finset.univ.sum fun i : ι =>
      coeffF i * ((Real.sqrt ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * (centerF i : ℂ)) *
        centeredBSplineImagTransformClosedForm k ell t)
  let GC : ℝ → ℂ := fun t =>
    Finset.univ.sum fun j : κ =>
      coeffG j * ((Real.sqrt ell : ℂ) *
        Complex.exp ((Complex.I * (t : ℂ)) * (centerG j : ℂ)) *
        centeredBSplineImagTransformClosedForm k ell t)
  let E : ℝ → ℝ := fun t => centeredBSplineImagTransformRealClosedForm k ell t
  let CF : ℝ := (Finset.univ.sum fun i : ι => ‖coeffF i‖) * Real.sqrt ell
  let CG : ℝ := (Finset.univ.sum fun j : κ => ‖coeffG j‖) * Real.sqrt ell
  let C : ℝ := CF * CG
  have hbase :=
    a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
      k ell hk hell
  have hmajor : Integrable (fun t : ℝ => C * ‖Q3.a_star t * (E t) ^ 2‖) := by
    simpa [E] using hbase.norm.const_mul C
  have hclosed_cont : Continuous (fun t : ℝ => Q3.a_star t * ((FC t) * star (GC t)).re) := by
    simpa [FC, GC] using
      centeredBSplineArchIntegrandClosed_translatedPacketSum_continuous
        k ell coeffF centerF coeffG centerG
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, CF, CG]
    positivity
  have hclosed_integrable : Integrable (fun t : ℝ => Q3.a_star t * ((FC t) * star (GC t)).re) := by
    refine hmajor.mono' hclosed_cont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    have hF_bound : ‖FC t‖ ≤ CF * |E t| := by
      have hF_eq :
          complexBumpLaplace F (Complex.I * (t : ℂ)) = FC t := by
        dsimp [F, FC]
        rw [centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum
          k ell t coeffF centerF hk hell]
      rw [← hF_eq]
      simpa [F, E, CF] using
        centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_norm_bound
          k ell t coeffF centerF hk hell
    have hG_bound : ‖GC t‖ ≤ CG * |E t| := by
      have hG_eq :
          complexBumpLaplace G (Complex.I * (t : ℂ)) = GC t := by
        dsimp [G, GC]
        rw [centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum
          k ell t coeffG centerG hk hell]
      rw [← hG_eq]
      simpa [G, E, CG] using
        centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_norm_bound
          k ell t coeffG centerG hk hell
    have hCF_nonneg : 0 ≤ CF := by
      dsimp [CF]
      positivity
    have hCG_nonneg : 0 ≤ CG := by
      dsimp [CG]
      positivity
    have hprod : ‖FC t * star (GC t)‖ ≤ C * |E t| ^ 2 := by
      calc
        ‖FC t * star (GC t)‖ = ‖FC t‖ * ‖GC t‖ := by
          rw [norm_mul, norm_star]
        _ ≤ (CF * |E t|) * (CG * |E t|) := by
          exact mul_le_mul hF_bound hG_bound
            (norm_nonneg _) (mul_nonneg hCF_nonneg (abs_nonneg _))
        _ = C * |E t| ^ 2 := by
          dsimp [C]
          ring
    have hreal : |((FC t) * star (GC t)).re| ≤ C * |E t| ^ 2 := by
      exact (Complex.abs_re_le_norm ((FC t) * star (GC t))).trans hprod
    have hleft :
        ‖Q3.a_star t * ((FC t) * star (GC t)).re‖ ≤
          C * (|Q3.a_star t| * |E t| ^ 2) := by
      calc
        ‖Q3.a_star t * ((FC t) * star (GC t)).re‖
            = |Q3.a_star t| * |((FC t) * star (GC t)).re| := by
              rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |Q3.a_star t| * (C * |E t| ^ 2) := by
              exact mul_le_mul_of_nonneg_left hreal (abs_nonneg _)
        _ = C * (|Q3.a_star t| * |E t| ^ 2) := by ring
    calc
      ‖Q3.a_star t * ((FC t) * star (GC t)).re‖
          ≤ C * (|Q3.a_star t| * |E t| ^ 2) := hleft
      _ = C * ‖Q3.a_star t * (E t) ^ 2‖ := by
          have hbaseabs : |Q3.a_star t * (E t) ^ 2| =
              |Q3.a_star t| * |E t| ^ 2 := by
            rw [abs_mul, abs_pow]
          rw [Real.norm_eq_abs, hbaseabs]
  have hclosed_ae :
      (fun t : ℝ => Q3.a_star t * ((FC t) * star (GC t)).re) =ᵐ[volume]
        centeredBSplineArchIntegrand F G := by
    refine Filter.Eventually.of_forall ?_
    intro t
    unfold centeredBSplineArchIntegrand
    dsimp [F, G, FC, GC]
    rw [centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum
      k ell t coeffF centerF hk hell]
    rw [centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum
      k ell t coeffG centerG hk hell]
  have hfinal : Integrable (centeredBSplineArchIntegrand F G) :=
    hclosed_integrable.congr hclosed_ae
  simpa [F, G] using hfinal

/-- Finite complex packet sum built from translated normalized centered
B-spline packets.  The coefficient space is a real vector space via the usual
real scalar action on complex coefficients. -/
noncomputable def centeredBSplineTranslatedPacketSum
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (coeff : ι → ℂ) (center : ι → ℝ) : ℝ → ℂ :=
  fun x : ℝ =>
    Finset.univ.sum fun i : ι =>
      coeff i *
        complexScaledTranslatedBump
          (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) x

/-- Packet sums are additive in their coefficient vector. -/
theorem centeredBSplineTranslatedPacketSum_add_coeff
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (a b : ι → ℂ) (center : ι → ℝ) :
    centeredBSplineTranslatedPacketSum k ell (a + b) center =
      fun x => centeredBSplineTranslatedPacketSum k ell a center x +
        centeredBSplineTranslatedPacketSum k ell b center x := by
  funext x
  simp [centeredBSplineTranslatedPacketSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Packet sums are homogeneous for real scalar multiplication of coefficients. -/
theorem centeredBSplineTranslatedPacketSum_smul_coeff
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell c : ℝ) (a : ι → ℂ) (center : ι → ℝ) :
    centeredBSplineTranslatedPacketSum k ell (c • a) center =
      c • centeredBSplineTranslatedPacketSum k ell a center := by
  funext x
  simp [centeredBSplineTranslatedPacketSum, Pi.smul_apply, Finset.mul_sum]
  ring_nf

/-- Arch pairing pulled back to the finite coefficient space of translated
centered B-spline packets. -/
noncomputable def centeredBSplineArchPacketCoeffPairing
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (a b : ι → ℂ) : ℝ :=
  centeredBSplineArchPairing
    (centeredBSplineTranslatedPacketSum k ell a center)
    (centeredBSplineTranslatedPacketSum k ell b center)

/-- Left additivity of the concrete Arch pairing on finite B-spline packet
coefficient vectors. -/
theorem centeredBSplineArchPacketCoeffPairing_add_left
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (a b z : ι → ℂ)
    (hk : 0 < k) (hell : 0 < ell) :
    centeredBSplineArchPacketCoeffPairing k ell center (a + b) z =
      centeredBSplineArchPacketCoeffPairing k ell center a z +
        centeredBSplineArchPacketCoeffPairing k ell center b z := by
  unfold centeredBSplineArchPacketCoeffPairing
  rw [centeredBSplineTranslatedPacketSum_add_coeff k ell a b center]
  apply centeredBSplineArchPairing_add_left
  · intro t
    simpa [centeredBSplineTranslatedPacketSum] using
      centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
        k ell t a center hk hell
  · intro t
    simpa [centeredBSplineTranslatedPacketSum] using
      centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
        k ell t b center hk hell
  · simpa [centeredBSplineTranslatedPacketSum] using
      centeredBSplineArchIntegrand_translatedPacketSum_integrable
        k ell a center z center hk hell
  · simpa [centeredBSplineTranslatedPacketSum] using
      centeredBSplineArchIntegrand_translatedPacketSum_integrable
        k ell b center z center hk hell

/-- Left real homogeneity of the concrete Arch pairing on finite B-spline packet
coefficient vectors. -/
theorem centeredBSplineArchPacketCoeffPairing_smul_left
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (c : ℝ) (a z : ι → ℂ) :
    centeredBSplineArchPacketCoeffPairing k ell center (c • a) z =
      c * centeredBSplineArchPacketCoeffPairing k ell center a z := by
  unfold centeredBSplineArchPacketCoeffPairing
  rw [centeredBSplineTranslatedPacketSum_smul_coeff k ell c a center]
  exact centeredBSplineArchPairing_smul_left c _ _

/-- Right additivity of the concrete Arch pairing on finite B-spline packet
coefficient vectors. -/
theorem centeredBSplineArchPacketCoeffPairing_add_right
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (a b z : ι → ℂ)
    (hk : 0 < k) (hell : 0 < ell) :
    centeredBSplineArchPacketCoeffPairing k ell center z (a + b) =
      centeredBSplineArchPacketCoeffPairing k ell center z a +
        centeredBSplineArchPacketCoeffPairing k ell center z b := by
  unfold centeredBSplineArchPacketCoeffPairing
  rw [centeredBSplineTranslatedPacketSum_add_coeff k ell a b center]
  apply centeredBSplineArchPairing_add_right
  · intro t
    simpa [centeredBSplineTranslatedPacketSum] using
      centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
        k ell t a center hk hell
  · intro t
    simpa [centeredBSplineTranslatedPacketSum] using
      centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
        k ell t b center hk hell
  · simpa [centeredBSplineTranslatedPacketSum] using
      centeredBSplineArchIntegrand_translatedPacketSum_integrable
        k ell z center a center hk hell
  · simpa [centeredBSplineTranslatedPacketSum] using
      centeredBSplineArchIntegrand_translatedPacketSum_integrable
        k ell z center b center hk hell

/-- Right real homogeneity of the concrete Arch pairing on finite B-spline packet
coefficient vectors. -/
theorem centeredBSplineArchPacketCoeffPairing_smul_right
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (c : ℝ) (a z : ι → ℂ) :
    centeredBSplineArchPacketCoeffPairing k ell center z (c • a) =
      c * centeredBSplineArchPacketCoeffPairing k ell center z a := by
  unfold centeredBSplineArchPacketCoeffPairing
  rw [centeredBSplineTranslatedPacketSum_smul_coeff k ell c a center]
  exact centeredBSplineArchPairing_smul_right c _ _

/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side-adjacent Arch form / Coordinate
- role: Step32F Arch packet-span bilinear wiring
- input: packet-sum x-side Laplace integrability, packet-sum t-side Arch integrability, unbundled centeredBSplineArchPairing laws
- output: real-bilinear Arch form on finite centered B-spline packet coefficient space
- reviewer question answered: can the concrete Arch pairing be used as an actual bilinear form on packet spans, not merely as individual translated-profile identities?
-/
noncomputable def centeredBSplineArchPacketCoeffBilinearForm
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (hk : 0 < k) (hell : 0 < ell) :
    (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ :=
  realBilinearFormOfPairing
    (centeredBSplineArchPacketCoeffPairing k ell center)
    (fun x y z =>
      centeredBSplineArchPacketCoeffPairing_add_left
        k ell center x y z hk hell)
    (fun c x z =>
      centeredBSplineArchPacketCoeffPairing_smul_left
        k ell center c x z)
    (fun x y z =>
      centeredBSplineArchPacketCoeffPairing_add_right
        k ell center y z x hk hell)
    (fun c x y =>
      centeredBSplineArchPacketCoeffPairing_smul_right
        k ell center c y x)

/-- The standard coefficient vector selecting the packet indexed by `i`. -/
noncomputable def centeredBSplineCoeffBasis
    {ι : Type*} [Fintype ι] (i : ι) : ι → ℂ := by
  classical
  exact fun j => if j = i then 1 else 0

/-- Coefficient-space packet basis expansion.  Synthesizing a real vector
coerces its coefficients to complex coefficients. -/
noncomputable def centeredBSplineCoeffBasisExpansion
    {ι : Type*} [Fintype ι] :
    PacketBasisExpansion ι (ι → ℂ) where
  basis := centeredBSplineCoeffBasis
  synth := fun v => fun i => (v i : ℂ)
  synth_eq_sum := by
    intro v
    funext i
    classical
    simp [centeredBSplineCoeffBasis]

/-- A standard coefficient basis vector synthesizes exactly one translated
centered B-spline packet. -/
theorem centeredBSplineTranslatedPacketSum_coeffBasis
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (i : ι) :
    centeredBSplineTranslatedPacketSum k ell
        (centeredBSplineCoeffBasis i) center =
      complexScaledTranslatedBump
        (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (center i) := by
  funext x
  classical
  unfold centeredBSplineTranslatedPacketSum centeredBSplineCoeffBasis
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-- Basis entries of the coefficient-space Arch pairing are the centered
B-spline Arch kernel profile at center differences. -/
theorem centeredBSplineArchPacketCoeffPairing_basis_closed
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (hell : 0 < ell) (i j : ι) :
    centeredBSplineArchPacketCoeffPairing k ell center
      (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i) =
      centeredBSplineArchKernelProfile k ell (center j - center i) := by
  unfold centeredBSplineArchPacketCoeffPairing
  rw [centeredBSplineTranslatedPacketSum_coeffBasis k ell center j]
  rw [centeredBSplineTranslatedPacketSum_coeffBasis k ell center i]
  exact centeredBSplineArchPairing_scaledTranslated_closed
    k ell (center j) (center i) hell

/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side-adjacent Arch form / Coordinate
- role: Step32F Arch coefficient-space receiver bridge
- input: packet-span bilinear form, standard coefficient basis, translated packet profile identity
- output: Arch PacketKernelPairingData and finite quadratic matrix expansion on coefficient space
- reviewer question answered: do the finite Arch matrix entries come from the actual bundled packet-span bilinear form on coordinates?
-/
noncomputable def centeredBSplineArchPacketCoeffKernelData
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (hk : 0 < k) (hell : 0 < ell) :
    PacketKernelPairingData ι (ι → ℂ) where
  basisExpansion := centeredBSplineCoeffBasisExpansion
  form := centeredBSplineArchPacketCoeffBilinearForm k ell center hk hell
  kernel := fun i j => centeredBSplineArchKernelProfile k ell (center j - center i)
  pairing_ident := by
    intro i j
    dsimp [centeredBSplineCoeffBasisExpansion]
    change centeredBSplineArchKernelProfile k ell (center j - center i) =
      centeredBSplineArchPacketCoeffPairing k ell center
        (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i)
    rw [centeredBSplineArchPacketCoeffPairing_basis_closed
      k ell center hell i j]

/-- The concrete Arch packet coefficient form expands to the finite kernel
quadratic form. -/
theorem centeredBSplineArchPacketCoeffBilinearForm_synth_eq_quadForm
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (hk : 0 < k) (hell : 0 < ell)
    (v : ι → ℝ) :
    (centeredBSplineArchPacketCoeffBilinearForm k ell center hk hell)
        (centeredBSplineCoeffBasisExpansion.synth v)
        (centeredBSplineCoeffBasisExpansion.synth v) =
      Q3.Proofs.quadForm
        (centeredBSplineArchPacketCoeffKernelData k ell center hk hell).matrix
        v :=
  (centeredBSplineArchPacketCoeffKernelData
    k ell center hk hell).form_synth_eq_quadForm v

/-- Prime-shift pairing on finite B-spline packet coefficients.  This is the
coordinate receiver for one translated autocorrelation shift. -/
noncomputable def centeredBSplinePrimeShiftPacketCoeffPairing
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a : ℝ) (center : ι → ℝ) (x y : ι → ℂ) : ℝ :=
  ∑ i, ∑ j,
    ((x j) * star (y i)).re *
      centeredBSplineR k ((center j - center i - a) / ell)

/-- Left additivity of the prime-shift coefficient pairing. -/
theorem centeredBSplinePrimeShiftPacketCoeffPairing_add_left
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a : ℝ) (center : ι → ℝ) (x y z : ι → ℂ) :
    centeredBSplinePrimeShiftPacketCoeffPairing k ell a center (x + y) z =
      centeredBSplinePrimeShiftPacketCoeffPairing k ell a center x z +
        centeredBSplinePrimeShiftPacketCoeffPairing k ell a center y z := by
  unfold centeredBSplinePrimeShiftPacketCoeffPairing
  simp only [Pi.add_apply, add_mul, Complex.add_re]
  simp only [Finset.sum_add_distrib]

/-- Left real homogeneity of the prime-shift coefficient pairing. -/
theorem centeredBSplinePrimeShiftPacketCoeffPairing_smul_left
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a c : ℝ) (center : ι → ℝ) (x z : ι → ℂ) :
    centeredBSplinePrimeShiftPacketCoeffPairing k ell a center (c • x) z =
      c * centeredBSplinePrimeShiftPacketCoeffPairing k ell a center x z := by
  unfold centeredBSplinePrimeShiftPacketCoeffPairing
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp
  ring_nf

/-- Right additivity of the prime-shift coefficient pairing. -/
theorem centeredBSplinePrimeShiftPacketCoeffPairing_add_right
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a : ℝ) (center : ι → ℝ) (x y z : ι → ℂ) :
    centeredBSplinePrimeShiftPacketCoeffPairing k ell a center z (x + y) =
      centeredBSplinePrimeShiftPacketCoeffPairing k ell a center z x +
        centeredBSplinePrimeShiftPacketCoeffPairing k ell a center z y := by
  unfold centeredBSplinePrimeShiftPacketCoeffPairing
  simp only [Pi.add_apply, star_add, mul_add, Complex.add_re, add_mul]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]

/-- Right real homogeneity of the prime-shift coefficient pairing. -/
theorem centeredBSplinePrimeShiftPacketCoeffPairing_smul_right
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a c : ℝ) (center : ι → ℝ) (x z : ι → ℂ) :
    centeredBSplinePrimeShiftPacketCoeffPairing k ell a center z (c • x) =
      c * centeredBSplinePrimeShiftPacketCoeffPairing k ell a center z x := by
  unfold centeredBSplinePrimeShiftPacketCoeffPairing
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp
  ring_nf

/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side receiver
- role: Step32F Prime-shift coefficient-space receiver bridge
- input: centered B-spline autocorrelation profile, coefficient basis receiver
- output: real-bilinear Prime-shift form on finite centered B-spline packet coefficients
- reviewer question answered: do the finite Prime-shift entries live in the same coefficient receiver model as the Arch entries?
-/
noncomputable def centeredBSplinePrimeShiftPacketCoeffBilinearForm
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a : ℝ) (center : ι → ℝ) :
    (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ :=
  realBilinearFormOfPairing
    (centeredBSplinePrimeShiftPacketCoeffPairing k ell a center)
    (fun x y z =>
      centeredBSplinePrimeShiftPacketCoeffPairing_add_left
        k ell a center x y z)
    (fun c x z =>
      centeredBSplinePrimeShiftPacketCoeffPairing_smul_left
        k ell a c center x z)
    (fun x y z =>
      centeredBSplinePrimeShiftPacketCoeffPairing_add_right
        k ell a center y z x)
    (fun c x y =>
      centeredBSplinePrimeShiftPacketCoeffPairing_smul_right
        k ell a c center y x)

/-- Basis entries of the prime-shift coefficient pairing are exactly the
closed centered B-spline autocorrelation profile for that shift. -/
theorem centeredBSplinePrimeShiftPacketCoeffPairing_basis_closed
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a : ℝ) (center : ι → ℝ) (i j : ι) :
    centeredBSplinePrimeShiftPacketCoeffPairing k ell a center
      (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i) =
      centeredBSplineR k ((center j - center i - a) / ell) := by
  classical
  unfold centeredBSplinePrimeShiftPacketCoeffPairing centeredBSplineCoeffBasis
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _hj' hj'
      simp [hj']
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  · intro i' _hi' hi'
    simp [hi']
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side receiver
- role: Step32F Prime-shift coefficient-space kernel data
- input: centered B-spline autocorrelation closed form, shifted packet correlation identity, coefficient basis receiver
- output: Prime-shift PacketKernelPairingData and finite quadratic matrix expansion on coefficient space
- reviewer question answered: do the finite Prime-shift matrix entries come from the actual B-spline autocorrelation profile on packet coordinates?
-/
noncomputable def centeredBSplinePrimeShiftPacketCoeffKernelData
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a : ℝ) (center : ι → ℝ) :
    PacketKernelPairingData ι (ι → ℂ) where
  basisExpansion := centeredBSplineCoeffBasisExpansion
  form := centeredBSplinePrimeShiftPacketCoeffBilinearForm k ell a center
  kernel := fun i j => centeredBSplineR k ((center j - center i - a) / ell)
  pairing_ident := by
    intro i j
    dsimp [centeredBSplineCoeffBasisExpansion]
    change centeredBSplineR k ((center j - center i - a) / ell) =
      centeredBSplinePrimeShiftPacketCoeffPairing k ell a center
        (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i)
    rw [centeredBSplinePrimeShiftPacketCoeffPairing_basis_closed]

/-- The concrete Prime-shift packet coefficient form expands to the finite
kernel quadratic form. -/
theorem centeredBSplinePrimeShiftPacketCoeffBilinearForm_synth_eq_quadForm
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a : ℝ) (center : ι → ℝ) (v : ι → ℝ) :
    (centeredBSplinePrimeShiftPacketCoeffBilinearForm k ell a center)
        (centeredBSplineCoeffBasisExpansion.synth v)
        (centeredBSplineCoeffBasisExpansion.synth v) =
      Q3.Proofs.quadForm
        (centeredBSplinePrimeShiftPacketCoeffKernelData k ell a center).matrix
        v :=
  (centeredBSplinePrimeShiftPacketCoeffKernelData k ell a center).form_synth_eq_quadForm v

/-- Symmetric finite Prime packet pairing assembled from finitely many weighted
positive/negative shifts.  A concrete prime block supplies `shift n = r log p`
and `weight n = log p / p^(r/2)`. -/
noncomputable def centeredBSplineFinitePrimePacketCoeffPairing
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (x y : ι → ℂ) : ℝ :=
  ∑ n, weight n *
    (centeredBSplinePrimeShiftPacketCoeffPairing k ell (shift n) center x y +
      centeredBSplinePrimeShiftPacketCoeffPairing k ell (-(shift n)) center x y)

/-- Symmetric finite Prime kernel profile induced by the weighted shift list. -/
def centeredBSplineFinitePrimeKernelProfile
    {ν : Type*} [Fintype ν]
    (k : ℕ) (ell : ℝ) (weight shift : ν → ℝ) (d : ℝ) : ℝ :=
  ∑ n, weight n *
    (centeredBSplineR k ((d - shift n) / ell) +
      centeredBSplineR k ((d + shift n) / ell))

/-- Left additivity of the finite Prime packet coefficient pairing. -/
theorem centeredBSplineFinitePrimePacketCoeffPairing_add_left
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (x y z : ι → ℂ) :
    centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift (x + y) z =
      centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift x z +
        centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift y z := by
  unfold centeredBSplineFinitePrimePacketCoeffPairing
  simp [centeredBSplinePrimeShiftPacketCoeffPairing_add_left,
    Finset.sum_add_distrib, mul_add, add_assoc, add_left_comm]

/-- Left real homogeneity of the finite Prime packet coefficient pairing. -/
theorem centeredBSplineFinitePrimePacketCoeffPairing_smul_left
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell c : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (x z : ι → ℂ) :
    centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift (c • x) z =
      c * centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift x z := by
  unfold centeredBSplineFinitePrimePacketCoeffPairing
  simp [centeredBSplinePrimeShiftPacketCoeffPairing_smul_left,
    Finset.mul_sum, mul_add, mul_left_comm]

/-- Right additivity of the finite Prime packet coefficient pairing. -/
theorem centeredBSplineFinitePrimePacketCoeffPairing_add_right
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (x y z : ι → ℂ) :
    centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift z (x + y) =
      centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift z x +
        centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift z y := by
  unfold centeredBSplineFinitePrimePacketCoeffPairing
  simp [centeredBSplinePrimeShiftPacketCoeffPairing_add_right,
    Finset.sum_add_distrib, mul_add, add_assoc, add_left_comm]

/-- Right real homogeneity of the finite Prime packet coefficient pairing. -/
theorem centeredBSplineFinitePrimePacketCoeffPairing_smul_right
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell c : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (x z : ι → ℂ) :
    centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift z (c • x) =
      c * centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift z x := by
  unfold centeredBSplineFinitePrimePacketCoeffPairing
  simp [centeredBSplinePrimeShiftPacketCoeffPairing_smul_right,
    Finset.mul_sum, mul_add, mul_left_comm]

/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side finite receiver
- role: Step32F finite Prime-sum coefficient-space assembly
- input: single-shift Prime receivers, finite prime weights/shifts, coefficient basis receiver
- output: one finite Prime PacketKernelPairingData assembled from all weighted positive/negative shifts
- reviewer question answered: does the Prime packet matrix come from one real-bilinear finite form, not just disconnected single-shift identities?
-/
noncomputable def centeredBSplineFinitePrimePacketCoeffBilinearForm
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ) :
    (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ :=
  realBilinearFormOfPairing
    (centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift)
    (fun x y z =>
      centeredBSplineFinitePrimePacketCoeffPairing_add_left
        k ell center weight shift x y z)
    (fun c x z =>
      centeredBSplineFinitePrimePacketCoeffPairing_smul_left
        k ell c center weight shift x z)
    (fun x y z =>
      centeredBSplineFinitePrimePacketCoeffPairing_add_right
        k ell center weight shift y z x)
    (fun c x y =>
      centeredBSplineFinitePrimePacketCoeffPairing_smul_right
        k ell c center weight shift y x)

/-- Basis entries of the finite Prime packet coefficient pairing are the
weighted finite Prime kernel profile. -/
theorem centeredBSplineFinitePrimePacketCoeffPairing_basis_closed
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ) (i j : ι) :
    centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift
      (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i) =
      centeredBSplineFinitePrimeKernelProfile k ell weight shift (center j - center i) := by
  unfold centeredBSplineFinitePrimePacketCoeffPairing centeredBSplineFinitePrimeKernelProfile
  simp [centeredBSplinePrimeShiftPacketCoeffPairing_basis_closed,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Concrete finite Prime packet-kernel data assembled from all weighted
positive/negative shifts. -/
noncomputable def centeredBSplineFinitePrimePacketCoeffKernelData
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ) :
    PacketKernelPairingData ι (ι → ℂ) where
  basisExpansion := centeredBSplineCoeffBasisExpansion
  form := centeredBSplineFinitePrimePacketCoeffBilinearForm k ell center weight shift
  kernel := fun i j =>
    centeredBSplineFinitePrimeKernelProfile k ell weight shift (center j - center i)
  pairing_ident := by
    intro i j
    dsimp [centeredBSplineCoeffBasisExpansion]
    change centeredBSplineFinitePrimeKernelProfile k ell weight shift (center j - center i) =
      centeredBSplineFinitePrimePacketCoeffPairing k ell center weight shift
        (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i)
    rw [centeredBSplineFinitePrimePacketCoeffPairing_basis_closed]

/-- The concrete finite Prime packet coefficient form expands to the finite
kernel quadratic form. -/
theorem centeredBSplineFinitePrimePacketCoeffBilinearForm_synth_eq_quadForm
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ) (v : ι → ℝ) :
    (centeredBSplineFinitePrimePacketCoeffBilinearForm k ell center weight shift)
        (centeredBSplineCoeffBasisExpansion.synth v)
        (centeredBSplineCoeffBasisExpansion.synth v) =
      Q3.Proofs.quadForm
        (centeredBSplineFinitePrimePacketCoeffKernelData
          k ell center weight shift).matrix
        v :=
  (centeredBSplineFinitePrimePacketCoeffKernelData
    k ell center weight shift).form_synth_eq_quadForm v

/-- Plus boundary functional on the coefficient model.  It is the concrete
row `exp(center i / 2)` applied to the real parts of complex coefficients. -/
noncomputable def centeredBSplineCoeffBoundaryPlusFunctional
    {ι : Type*} [Fintype ι] (center : ι → ℝ) :
    (ι → ℂ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, bsplineBoundaryPlusRow center i * (x i).re
  map_add' := by
    intro x y
    simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [Pi.smul_apply, Finset.mul_sum, mul_assoc, mul_comm]

/-- Minus boundary functional on the coefficient model. -/
noncomputable def centeredBSplineCoeffBoundaryMinusFunctional
    {ι : Type*} [Fintype ι] (center : ι → ℝ) :
    (ι → ℂ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, bsplineBoundaryMinusRow center i * (x i).re
  map_add' := by
    intro x y
    simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [Pi.smul_apply, Finset.mul_sum, mul_assoc, mul_comm]

/-- Boundary pair for the concrete coefficient-space B-spline packet model. -/
noncomputable def centeredBSplineCoeffBoundaryPair
    {ι : Type*} [Fintype ι] (center : ι → ℝ) :
    BoundaryPair (ι → ℂ) where
  evalPlus := centeredBSplineCoeffBoundaryPlusFunctional center
  evalMinus := centeredBSplineCoeffBoundaryMinusFunctional center

/-- Coefficient plus boundary on a basis vector gives the plus exponential row. -/
theorem centeredBSplineCoeffBoundaryPair_evalPlus_basis
    {ι : Type*} [Fintype ι] (center : ι → ℝ) (i : ι) :
    (centeredBSplineCoeffBoundaryPair center).evalPlus
        (centeredBSplineCoeffBasis i) =
      bsplineBoundaryPlusRow center i := by
  classical
  change
    (∑ j : ι,
      bsplineBoundaryPlusRow center j *
        (if j = i then (1 : ℂ) else 0).re) =
      bsplineBoundaryPlusRow center i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-- Coefficient minus boundary on a basis vector gives the minus exponential row. -/
theorem centeredBSplineCoeffBoundaryPair_evalMinus_basis
    {ι : Type*} [Fintype ι] (center : ι → ℝ) (i : ι) :
    (centeredBSplineCoeffBoundaryPair center).evalMinus
        (centeredBSplineCoeffBasis i) =
      bsplineBoundaryMinusRow center i := by
  classical
  change
    (∑ j : ι,
      bsplineBoundaryMinusRow center j *
        (if j = i then (1 : ℂ) else 0).re) =
      bsplineBoundaryMinusRow center i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-
Q3 obstruction wall:
- wall: Matrix-identification / Step32F concrete contract assembly
- role: assemble coefficient-space boundary, Arch receiver, and finite Prime receiver
- input: Arch coefficient receiver, finite Prime coefficient receiver, exponential boundary rows
- output: one BSplineAnalyticKernelContract over the centered B-spline coefficient model
- reviewer question answered: do the boundary rows, Arch matrix, and finite Prime matrix now live in one finite analytic contract?
-/
noncomputable def centeredBSplineCoeffAnalyticKernelContract
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    BSplineAnalyticKernelContract ι (ι → ℂ) where
  center := center
  basisExpansion := centeredBSplineCoeffBasisExpansion
  boundary := centeredBSplineCoeffBoundaryPair center
  scalePlus := 1
  scaleMinus := 1
  scalePlus_ne_zero := by norm_num
  scaleMinus_ne_zero := by norm_num
  boundaryPlus_basis := by
    intro i
    simpa using centeredBSplineCoeffBoundaryPair_evalPlus_basis center i
  boundaryMinus_basis := by
    intro i
    simpa using centeredBSplineCoeffBoundaryPair_evalMinus_basis center i
  archKernel := centeredBSplineArchPacketCoeffKernelData k ell center hk hell
  primeKernel := centeredBSplineFinitePrimePacketCoeffKernelData k ell center weight shift
  arch_basisExpansion_eq := rfl
  prime_basisExpansion_eq := rfl
  archForm := fun x =>
    (centeredBSplineArchPacketCoeffBilinearForm k ell center hk hell) x x
  primeForm := fun x =>
    (centeredBSplineFinitePrimePacketCoeffBilinearForm k ell center weight shift) x x
  weilForm := fun x =>
    (centeredBSplineArchPacketCoeffBilinearForm k ell center hk hell) x x -
      (centeredBSplineFinitePrimePacketCoeffBilinearForm k ell center weight shift) x x
  archForm_eq := by
    intro v
    rfl
  primeForm_eq := by
    intro v
    rfl
  weil_split := by
    intro v
    rfl

/-- The assembled coefficient-space B-spline contract gives a finite Weil
matrix model with `C = A - P` and the two exponential boundary rows. -/
noncomputable def centeredBSplineCoeffFiniteWeilMatrixModel
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    FiniteWeilMatrixModel
      (V := ι → ℂ)
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.C
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.boundaryRows.Q :=
  (centeredBSplineCoeffAnalyticKernelContract
    k ell center weight shift hk hell).toFiniteWeilMatrixModel

/-- The assembled coefficient contract identifies the synthesized Weil form
with the finite Arch-minus-Prime matrix quadratic form. -/
theorem centeredBSplineCoeffAnalyticKernelContract_weil_ident
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    ∀ v : ι → ℝ,
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).weilForm
          (centeredBSplineCoeffBasisExpansion.synth v) =
        Q3.Proofs.quadForm
          (centeredBSplineCoeffAnalyticKernelContract
            k ell center weight shift hk hell).toFormulaContract.C v :=
  (centeredBSplineCoeffAnalyticKernelContract
    k ell center weight shift hk hell).weil_ident

/-
Q3 obstruction wall:
- wall: Matrix-identification / finite certificate handoff
- role: Step32F coefficient certified block wrapper
- input: coefficient analytic contract, interval-backed FinitePenaltyCert, matrix split identity
- output: CertifiedFiniteWeilModel for the centered B-spline coefficient model
- reviewer question answered: does the concrete coefficient contract feed the existing finite-certificate consumer, rather than stopping at a matrix-identification wrapper?
-/
structure CertifiedCenteredBSplineCoeffBlock
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    (k : ℕ) (ell : ℝ) (center : ι → ℝ) (weight shift : ν → ℝ)
    (hk : 0 < k) (hell : 0 < ell) where
  D : Matrix ι ι ℝ
  R : Matrix ι ι ℝ
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  cert :
    Q3.Proofs.FinitePenaltyCert
      D
      R
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.boundaryRows.Q
  split :
    ∀ v : ι → ℝ,
      Q3.Proofs.quadForm
          (centeredBSplineCoeffAnalyticKernelContract
            k ell center weight shift hk hell).toFormulaContract.C v =
        Q3.Proofs.quadForm D v + theta * Q3.Proofs.quadForm R v

namespace CertifiedCenteredBSplineCoeffBlock

/-- The finite matrix-to-Weil model supplied by the coefficient-space analytic
contract. -/
noncomputable def finiteWeilMatrixModel
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    {k : ℕ} {ell : ℝ} {center : ι → ℝ} {weight shift : ν → ℝ}
    {hk : 0 < k} {hell : 0 < ell}
    (B : CertifiedCenteredBSplineCoeffBlock k ell center weight shift hk hell) :
    FiniteWeilMatrixModel
      (V := ι → ℂ)
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.C
      (centeredBSplineCoeffAnalyticKernelContract
        k ell center weight shift hk hell).toFormulaContract.boundaryRows.Q :=
by
  cases B
  exact centeredBSplineCoeffFiniteWeilMatrixModel
    k ell center weight shift hk hell

/-- Coefficient analytic identity data plus an interval-backed finite penalty
certificate produce the packaged Step 31 finite analytic Weil model. -/
noncomputable def toCertifiedFiniteWeilModel
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    {k : ℕ} {ell : ℝ} {center : ι → ℝ} {weight shift : ν → ℝ}
    {hk : 0 < k} {hell : 0 < ell}
    (B : CertifiedCenteredBSplineCoeffBlock k ell center weight shift hk hell) :
    CertifiedFiniteWeilModel (Fin 2) ι (ι → ℂ) where
  C :=
    (centeredBSplineCoeffAnalyticKernelContract
      k ell center weight shift hk hell).toFormulaContract.C
  D := B.D
  R := B.R
  Q :=
    (centeredBSplineCoeffAnalyticKernelContract
      k ell center weight shift hk hell).toFormulaContract.boundaryRows.Q
  theta := B.theta
  theta_nonneg := B.theta_nonneg
  cert := B.cert
  split := B.split
  model := B.finiteWeilMatrixModel

/-- A certified coefficient B-spline block proves analytic Weil nonnegativity
on synthesized analytic boundary-null coefficient vectors. -/
theorem weil_nonneg_on_analyticBoundary
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    {k : ℕ} {ell : ℝ} {center : ι → ℝ} {weight shift : ν → ℝ}
    {hk : 0 < k} {hell : 0 < ell}
    (B : CertifiedCenteredBSplineCoeffBlock k ell center weight shift hk hell) :
    ∀ v : ι → ℝ,
      B.finiteWeilMatrixModel.boundary.evalPlus
          (B.finiteWeilMatrixModel.synth v) = 0 →
      B.finiteWeilMatrixModel.boundary.evalMinus
          (B.finiteWeilMatrixModel.synth v) = 0 →
        0 ≤ B.finiteWeilMatrixModel.weilForm
          (B.finiteWeilMatrixModel.synth v) :=
  B.toCertifiedFiniteWeilModel.weil_nonneg_on_analyticBoundary

/-- The same certified coefficient block exposes the strengthened lower bound
against the certified base matrix `R`. -/
theorem weil_ge_theta_R_on_analyticBoundary
    {ι ν : Type*} [Fintype ι] [Fintype ν]
    {k : ℕ} {ell : ℝ} {center : ι → ℝ} {weight shift : ν → ℝ}
    {hk : 0 < k} {hell : 0 < ell}
    (B : CertifiedCenteredBSplineCoeffBlock k ell center weight shift hk hell) :
    ∀ v : ι → ℝ,
      B.finiteWeilMatrixModel.boundary.evalPlus
          (B.finiteWeilMatrixModel.synth v) = 0 →
      B.finiteWeilMatrixModel.boundary.evalMinus
          (B.finiteWeilMatrixModel.synth v) = 0 →
        B.theta * Q3.Proofs.quadForm B.R v ≤
          B.finiteWeilMatrixModel.weilForm
            (B.finiteWeilMatrixModel.synth v) :=
  B.toCertifiedFiniteWeilModel.weil_ge_theta_R_on_analyticBoundary

/-- Expose a certified coefficient B-spline block as a Step 27 finite
certificate ledger row.

The ledger object intentionally remembers only the finite matrices and the
`FinitePenaltyCert`; the analytic matrix-identification payload remains in
`toCertifiedFiniteWeilModel`.  The universe is restricted to ordinary `Type`
because `CertifiedFiniteBlock` is a manifest/ledger carrier for concrete finite
index types such as `Fin n`. -/
noncomputable def toCertifiedFiniteBlock
    {ι ν : Type} [Fintype ι] [Fintype ν]
    {k : ℕ} {ell : ℝ} {center : ι → ℝ} {weight shift : ν → ℝ}
    {hk : 0 < k} {hell : 0 < ell}
    (B : CertifiedCenteredBSplineCoeffBlock k ell center weight shift hk hell)
    (label : FiniteSpaceLabel) :
    CertifiedFiniteBlock where
  label := label
  rho := Fin 2
  iota := ι
  rhoFinite := inferInstance
  iotaFinite := inferInstance
  D := B.D
  R := B.R
  Q :=
    (centeredBSplineCoeffAnalyticKernelContract
      k ell center weight shift hk hell).toFormulaContract.boundaryRows.Q
  cert := B.cert

/-- Expose one certified coefficient B-spline block as a degenerate directed
certificate family.

This is intentionally only the singleton ledger adapter.  Exhaustion and real
directed refinement remain separate analytic obligations. -/
noncomputable def toSingletonDirectedCertFamily
    {ι ν : Type} [Fintype ι] [Fintype ν]
    {k : ℕ} {ell : ℝ} {center : ι → ℝ} {weight shift : ν → ℝ}
    {hk : 0 < k} {hell : 0 < ell}
    (B : CertifiedCenteredBSplineCoeffBlock k ell center weight shift hk hell)
    (label : FiniteSpaceLabel) :
    DirectedCertFamily :=
  (B.toCertifiedFiniteBlock label).singletonDirectedFamily

end CertifiedCenteredBSplineCoeffBlock

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

/-- The Prime-shift coefficient receiver basis entry agrees with the actual
translated-packet autocorrelation integral. -/
theorem centeredBSplinePrimeShiftPacketCoeffPairing_basis_correlation_closed
    {ι : Type*} [Fintype ι]
    (k : ℕ) (ell a : ℝ) (center : ι → ℝ) (hell : 0 < ell) (i j : ι) :
    (∫ u : ℝ,
        realScaledTranslatedBump (centeredBSplineEta k) ell (center j) u *
          realShift a (realScaledTranslatedBump (centeredBSplineEta k) ell (center i)) u) =
      centeredBSplinePrimeShiftPacketCoeffPairing k ell a center
        (centeredBSplineCoeffBasis j) (centeredBSplineCoeffBasis i) := by
  rw [centeredBSplineCorrelation_scaledTranslated_shift_closed
    k ell (center i) (center j) a hell
    (CenteredBSplineAutocorrelationClosedForm_all k)]
  rw [centeredBSplinePrimeShiftPacketCoeffPairing_basis_closed]

end PSDpd
end Q3
