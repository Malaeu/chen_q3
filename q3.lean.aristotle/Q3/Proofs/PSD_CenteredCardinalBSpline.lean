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

/-- The centered box spline \(b_0=\mathbf 1_{[-1/2,1/2]}\), with the same
endpoint convention as `centeredCardinalBSpline 0`. -/
def centeredBoxSpline (x : ℝ) : ℝ :=
  positivePartPower 0 (x + (1 / 2 : ℝ))
    - positivePartPower 0 (x - (1 / 2 : ℝ))

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

/-- The degree-zero autocorrelation normalizer is positive. -/
theorem bsplineAutocorrNorm_pos_zero :
    0 < bsplineAutocorrNorm 0 := by
  norm_num [bsplineAutocorrNorm, bsplineAutocorrDegree,
    centeredCardinalBSpline, positivePartPower]

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
