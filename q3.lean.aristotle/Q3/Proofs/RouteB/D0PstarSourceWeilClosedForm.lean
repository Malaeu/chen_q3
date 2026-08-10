import Q3.Proofs.RouteB.D0PstarShiftedArchClosedForm
import Q3.Proofs.RouteB.D0PstarSourceWeilSesquilinearForm

noncomputable section

open Complex MeasureTheory Topology
open scoped ENNReal ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-- The bounded part of the shifted source-Weil diagonal.  The two operator
norm terms are exactly the additional shift needed for the W02 and Prime
perturbations; the archimedean shift is already built into the positive
closed-form parent. -/
noncomputable def sourceWeilBoundedShiftedDiagonal
    (i : PairIndex) (x : H_m i) : ℝ :=
  (sourceW02AmbientContinuousSesquilinearForm i x x).re -
    (sourcePrimeContinuousSesquilinearForm i x x).re +
    (‖sourceW02AmbientContinuousSesquilinearForm i‖ +
      ‖sourcePrimeContinuousSesquilinearForm i‖) * ‖x‖ ^ 2

theorem sourceWeilBoundedShiftedDiagonal_continuous
    (i : PairIndex) :
    Continuous (sourceWeilBoundedShiftedDiagonal i) := by
  unfold sourceWeilBoundedShiftedDiagonal
  exact
    (Complex.continuous_re.comp
        ((sourceW02AmbientContinuousSesquilinearForm i).continuous.clm_apply
          continuous_id)).sub
      (Complex.continuous_re.comp
        ((sourcePrimeContinuousSesquilinearForm i).continuous.clm_apply
          continuous_id)) |>.add
      (continuous_const.mul (continuous_norm.pow 2))

theorem sourceWeilBoundedShiftedDiagonal_nonneg
    (i : PairIndex) (x : H_m i) :
    0 ≤ sourceWeilBoundedShiftedDiagonal i x := by
  have hwNorm :=
    norm_sourceW02AmbientContinuousSesquilinearForm_apply_le i x x
  have hpNorm :
      ‖sourcePrimeContinuousSesquilinearForm i x x‖ ≤
        ‖sourcePrimeContinuousSesquilinearForm i‖ * ‖x‖ * ‖x‖ := by
    rw [sourcePrimeContinuousSesquilinearForm_apply]
    exact norm_sourcePrimeSesquilinearForm_apply_le i x x
  have hwLower :
      -(‖sourceW02AmbientContinuousSesquilinearForm i‖ * ‖x‖ ^ 2) ≤
        (sourceW02AmbientContinuousSesquilinearForm i x x).re := by
    have hre :=
      (abs_le.mp
        (Complex.abs_re_le_norm
          (sourceW02AmbientContinuousSesquilinearForm i x x))).1
    have hneg := neg_le_neg hwNorm
    simpa [pow_two, mul_assoc] using hneg.trans hre
  have hpUpper :
      (sourcePrimeContinuousSesquilinearForm i x x).re ≤
        ‖sourcePrimeContinuousSesquilinearForm i‖ * ‖x‖ ^ 2 := by
    simpa [pow_two, mul_assoc] using
      (Complex.re_le_norm _).trans hpNorm
  unfold sourceWeilBoundedShiftedDiagonal
  nlinarith

/-- The nonnegative shifted extended source-Weil quadratic form on all `H_m`.
It is finite exactly on the shifted archimedean form domain.  This is the
closed-form energy layer, not an associated operator or graph definition. -/
noncomputable def sourceWeilShiftedExtendedQuadraticForm
    (i : PairIndex) (x : H_m i) : ℝ≥0∞ :=
  sourceArchimedeanShiftedExtendedQuadraticForm i x +
    ENNReal.ofReal (sourceWeilBoundedShiftedDiagonal i x)

theorem sourceWeilShiftedExtendedQuadraticForm_lowerSemicontinuous
    (i : PairIndex) :
    LowerSemicontinuous (sourceWeilShiftedExtendedQuadraticForm i) := by
  unfold sourceWeilShiftedExtendedQuadraticForm
  exact
    (sourceArchimedeanShiftedExtendedQuadraticForm_lowerSemicontinuous i).add
      ((ENNReal.continuous_ofReal.comp
        (sourceWeilBoundedShiftedDiagonal_continuous i)).lowerSemicontinuous)

theorem mem_sourceArchimedeanShiftedFormDomain_iff_sourceWeilShifted_lt_top
    (i : PairIndex) (x : H_m i) :
    x ∈ sourceArchimedeanShiftedFormDomain i ↔
      sourceWeilShiftedExtendedQuadraticForm i x < ∞ := by
  rw [mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top]
  unfold sourceWeilShiftedExtendedQuadraticForm
  simp only [ENNReal.add_lt_top, ENNReal.ofReal_lt_top, and_true]

/-- On the exact form domain, the shifted extended energy agrees with the
real diagonal of the complete source-Weil form plus its explicit lower-bound
shift. -/
theorem sourceWeilShiftedExtendedQuadraticForm_toReal_eq_re_add_shift
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    (sourceWeilShiftedExtendedQuadraticForm i x.1).toReal =
      (sourceWeilSesquilinearForm i x x).re +
        sourceWeilLowerBoundConstant i * ‖(x : H_m i)‖ ^ 2 := by
  have hArchLt :
      sourceArchimedeanShiftedExtendedQuadraticForm i x.1 < ∞ :=
    (mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top
      i x.1).mp x.2
  rw [sourceWeilShiftedExtendedQuadraticForm,
    ENNReal.toReal_add (ne_of_lt hArchLt)
      (ne_of_lt ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal (sourceWeilBoundedShiftedDiagonal_nonneg i x.1),
    sourceArchimedeanShiftedExtendedQuadraticForm_toReal_eq_re]
  have hinner : (inner ℂ x x).re = ‖(x : H_m i)‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  rw [sourceWeilSesquilinearForm_apply,
    sourceArchPrimeSesquilinearForm_apply,
    sourceArchimedeanSesquilinearForm_apply]
  simp only [sourceWeilBoundedShiftedDiagonal, add_re, sub_re, mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [sourcePrimeContinuousSesquilinearForm_apply]
  rw [hinner]
  dsimp only [sourceWeilLowerBoundConstant]
  ring

#print axioms sourceWeilBoundedShiftedDiagonal
#print axioms sourceWeilBoundedShiftedDiagonal_continuous
#print axioms sourceWeilBoundedShiftedDiagonal_nonneg
#print axioms sourceWeilShiftedExtendedQuadraticForm
#print axioms sourceWeilShiftedExtendedQuadraticForm_lowerSemicontinuous
#print axioms mem_sourceArchimedeanShiftedFormDomain_iff_sourceWeilShifted_lt_top
#print axioms sourceWeilShiftedExtendedQuadraticForm_toReal_eq_re_add_shift

end Q3.RouteB.D0Pstar
