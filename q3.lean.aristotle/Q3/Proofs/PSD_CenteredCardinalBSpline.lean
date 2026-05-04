import Q3.Proofs.PSD_BSplineAnalyticModel
import Mathlib.Analysis.Convolution
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

noncomputable section

open MeasureTheory
open scoped BigOperators

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
    (hbase :
      ∀ x : ℝ,
        realBumpCorrelationProfile (centeredCardinalBSpline k) x =
          centeredCardinalBSpline (bsplineAutocorrDegree k) x) :
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

/-- Name the exact transform profile still needed to close the Arch/boundary
side of Step 32F. -/
def centeredBSplineRealTransformProfile (k : ℕ) (ell z : ℝ) : ℝ :=
  realBumpTransformProfile (centeredBSplineEta k) ell z

/-- The plus boundary scale for the concrete bump. -/
def centeredBSplineBoundaryPlusScale (k : ℕ) (ell : ℝ) : ℝ :=
  Real.sqrt ell * centeredBSplineRealTransformProfile k ell (1 / 2)

/-- The minus boundary scale for the concrete bump. -/
def centeredBSplineBoundaryMinusScale (k : ℕ) (ell : ℝ) : ℝ :=
  Real.sqrt ell * centeredBSplineRealTransformProfile k ell (-(1 / 2))

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
