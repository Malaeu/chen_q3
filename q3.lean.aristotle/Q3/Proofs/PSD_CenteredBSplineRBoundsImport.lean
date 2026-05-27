import Q3.Proofs.PSD_CenteredCardinalBSpline

set_option linter.mathlibStandardSet false

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredBSplineRBoundsImport

/-!
Step32N basic bounds for the normalized autocorrelation profile.
-/

/-- One truncated-power summand in the centered cardinal B-spline formula. -/
def centeredCardinalBSplineSummand (degree : ℕ) (x : Real) (j : ℕ) : Real :=
  ((-1 : Real) ^ j) *
    (Nat.choose (degree + 1) j : Real) *
      positivePartPower degree
        (x + (((degree + 1 : ℕ) : Real) / 2) - (j : Real))

/-- A generated positive-part-power hbox gives the corresponding centered
cardinal B-spline summand hbox after applying the signed binomial
coefficient. -/
theorem centeredCardinalBSplineSummand_hbox_of_positivePartPower_hbox
    (degree : ℕ) (x : Real) (j : ℕ)
    (ppMid ppRad mid rad : Real)
    (hpp :
      |positivePartPower degree
          (x + (((degree + 1 : ℕ) : Real) / 2) - (j : Real)) -
        ppMid| ≤ ppRad)
    (hmid :
      (((-1 : Real) ^ j) *
        (Nat.choose (degree + 1) j : Real)) * ppMid = mid)
    (hrad :
      |((-1 : Real) ^ j) *
        (Nat.choose (degree + 1) j : Real)| * ppRad ≤ rad) :
    |centeredCardinalBSplineSummand degree x j - mid| ≤ rad := by
  unfold centeredCardinalBSplineSummand
  rw [← hmid]
  calc
    |(((-1 : Real) ^ j) *
          (Nat.choose (degree + 1) j : Real) *
          positivePartPower degree
            (x + (((degree + 1 : ℕ) : Real) / 2) - (j : Real))) -
        (((-1 : Real) ^ j) *
          (Nat.choose (degree + 1) j : Real)) * ppMid| =
        |((-1 : Real) ^ j) *
          (Nat.choose (degree + 1) j : Real)| *
          |positivePartPower degree
            (x + (((degree + 1 : ℕ) : Real) / 2) - (j : Real)) -
            ppMid| := by
          rw [← mul_sub, abs_mul]
    _ ≤
        |((-1 : Real) ^ j) *
          (Nat.choose (degree + 1) j : Real)| * ppRad := by
          exact mul_le_mul_of_nonneg_left hpp (abs_nonneg _)
    _ ≤ rad := hrad

/-- Summand midpoint/radius hboxes imply a centered cardinal B-spline hbox. -/
theorem centeredCardinalBSpline_hbox_of_summand_hboxes
    (degree : ℕ) (x mid rad : Real)
    (termMid termRad : ℕ -> Real)
    (hterm :
      ∀ j, j ∈ Finset.range (degree + 2) ->
        |centeredCardinalBSplineSummand degree x j - termMid j| ≤
          termRad j)
    (hmid :
      ((Nat.factorial degree : Real)⁻¹) *
        ((Finset.range (degree + 2)).sum fun j => termMid j) = mid)
    (hrad :
      |((Nat.factorial degree : Real)⁻¹)| *
        ((Finset.range (degree + 2)).sum fun j => termRad j) ≤ rad) :
    |centeredCardinalBSpline degree x - mid| ≤ rad := by
  have hsum :
      |(Finset.range (degree + 2)).sum fun j =>
          (centeredCardinalBSplineSummand degree x j - termMid j)| ≤
        (Finset.range (degree + 2)).sum fun j => termRad j := by
    calc
      |(Finset.range (degree + 2)).sum fun j =>
          (centeredCardinalBSplineSummand degree x j - termMid j)| ≤
          (Finset.range (degree + 2)).sum fun j =>
            |centeredCardinalBSplineSummand degree x j - termMid j| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.range (degree + 2)).sum fun j => termRad j := by
            exact Finset.sum_le_sum hterm
  have hdiff :
      centeredCardinalBSpline degree x - mid =
        ((Nat.factorial degree : Real)⁻¹) *
          ((Finset.range (degree + 2)).sum fun j =>
            (centeredCardinalBSplineSummand degree x j - termMid j)) := by
    rw [← hmid]
    unfold centeredCardinalBSpline centeredCardinalBSplineSummand
    rw [Finset.sum_sub_distrib]
    ring
  calc
    |centeredCardinalBSpline degree x - mid| =
        |((Nat.factorial degree : Real)⁻¹) *
          ((Finset.range (degree + 2)).sum fun j =>
            (centeredCardinalBSplineSummand degree x j - termMid j))| := by
          rw [hdiff]
    _ =
        |((Nat.factorial degree : Real)⁻¹)| *
          |(Finset.range (degree + 2)).sum fun j =>
            (centeredCardinalBSplineSummand degree x j - termMid j)| := by
          rw [abs_mul]
    _ ≤
        |((Nat.factorial degree : Real)⁻¹)| *
          ((Finset.range (degree + 2)).sum fun j => termRad j) := by
          exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ rad := hrad

/-- Dividing a midpoint/radius enclosure by a positive scalar. -/
theorem div_pos_abs_sub_le
    (a am ar c : Real) (hc : 0 < c)
    (h : |a - am| ≤ ar) :
    |a / c - am / c| ≤ ar / c := by
  calc
    |a / c - am / c| = |a - am| / c := by
      have hdiff : a / c - am / c = (a - am) / c := by ring
      rw [hdiff, abs_div, abs_of_pos hc]
    _ ≤ ar / c := div_le_div_of_nonneg_right h (le_of_lt hc)

/-- A cardinal B-spline hbox gives the corresponding normalized
`centeredBSplineR` hbox. -/
theorem centeredBSplineR_hbox_of_cardinal_hbox
    (k : ℕ) (x mid rad : Real)
    (hcard :
      |centeredCardinalBSpline (bsplineAutocorrDegree k)
          (bsplineScale k * x) - mid| ≤ rad) :
    |centeredBSplineR k x - mid / bsplineAutocorrNorm k| ≤
      rad / bsplineAutocorrNorm k := by
  unfold centeredBSplineR
  exact div_pos_abs_sub_le
    (centeredCardinalBSpline (bsplineAutocorrDegree k)
      (bsplineScale k * x))
    mid rad (bsplineAutocorrNorm k) (bsplineAutocorrNorm_pos k) hcard

/-- The normalized autocorrelation profile `centeredBSplineR` is nonnegative. -/
theorem centeredBSplineR_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ centeredBSplineR k x := by
  unfold centeredBSplineR
  exact div_nonneg
    (centeredCardinalBSpline_nonneg (bsplineAutocorrDegree k)
      (bsplineScale k * x))
    (le_of_lt (bsplineAutocorrNorm_pos k))

end CenteredBSplineRBoundsImport
end PSDpd
end Q3
