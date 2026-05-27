import Q3.Proofs.PSD_CenteredCardinalBSpline

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredBSplineRBoundsImport

/-!
Step32N basic bounds for the normalized autocorrelation profile.
-/

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
