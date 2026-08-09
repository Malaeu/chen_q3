import Q3.Proofs.RouteB.D0PstarExactArchSymbolLowerBound
import Q3.Proofs.A_Star_Properties

noncomputable section

open scoped Real

namespace Q3.RouteB.D0Pstar

private theorem sourceArchimedeanMultiplier_continuous_for_shiftedSqrt :
    Continuous sourceArchimedeanMultiplier := by
  have hrepr :
      sourceArchimedeanMultiplier =
        fun t : ℝ => -Q3.a_star t / (2 * Real.pi) := by
    funext t
    exact sourceArchimedeanMultiplier_eq_neg_aStar_scaled t
  rw [hrepr]
  exact Q3.a_star_continuous_thm.neg.div_const (2 * Real.pi)

/-- The nonnegative square-root weight attached to the exact finite shift of
B3.0N.  This is form-domain data only; it is not an ambient source form or an
associated operator. -/
noncomputable def sourceArchimedeanShiftedSqrtWeight (t : ℝ) : ℝ :=
  Real.sqrt
    (sourceArchimedeanMultiplier t +
      (|Real.log Real.pi| + Real.log 4 + 6))

theorem sourceArchimedeanShiftedSqrtWeight_continuous :
    Continuous sourceArchimedeanShiftedSqrtWeight := by
  simpa [sourceArchimedeanShiftedSqrtWeight] using
    Real.continuous_sqrt.comp
      (sourceArchimedeanMultiplier_continuous_for_shiftedSqrt.add
        continuous_const)

theorem sourceArchimedeanShiftedSqrtWeight_measurable :
    Measurable sourceArchimedeanShiftedSqrtWeight :=
  sourceArchimedeanShiftedSqrtWeight_continuous.measurable

theorem sourceArchimedeanShiftedSqrtWeight_nonneg
    (t : ℝ) :
    0 ≤ sourceArchimedeanShiftedSqrtWeight t := by
  exact Real.sqrt_nonneg _

theorem sourceArchimedeanShiftedSqrtWeight_sq
    (t : ℝ) :
    sourceArchimedeanShiftedSqrtWeight t ^ 2 =
      sourceArchimedeanMultiplier t +
        (|Real.log Real.pi| + Real.log 4 + 6) := by
  unfold sourceArchimedeanShiftedSqrtWeight
  exact Real.sq_sqrt
    (sourceArchimedeanMultiplier_add_explicitShift_nonneg t)

#print axioms sourceArchimedeanShiftedSqrtWeight
#print axioms sourceArchimedeanShiftedSqrtWeight_continuous
#print axioms sourceArchimedeanShiftedSqrtWeight_measurable
#print axioms sourceArchimedeanShiftedSqrtWeight_nonneg
#print axioms sourceArchimedeanShiftedSqrtWeight_sq

end Q3.RouteB.D0Pstar
