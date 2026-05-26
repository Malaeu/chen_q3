import Q3.Proofs.PSD_CenteredCardinalBSpline

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredBSplineRBoundsImport

/-!
Step32N basic bounds for the normalized autocorrelation profile.
-/

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
