import Q3.Proofs.PSD_BSplineAnalyticModel
import Mathlib.Tactic

set_option linter.mathlibStandardSet false

noncomputable section

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

/-- Actual generic-bump correlation profile of `eta_k`. -/
def centeredBSplineCorrelationProfile (k : ℕ) (x : ℝ) : ℝ :=
  realBumpCorrelationProfile (centeredBSplineEta k) x

/--
The exact autocorrelation theorem still needed to close the prime-entry side of
Step 32F.
-/
def CenteredBSplineAutocorrelationClosedForm (k : ℕ) : Prop :=
  ∀ x : ℝ,
    centeredBSplineCorrelationProfile k x = centeredBSplineR k x

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
