import Q3.Proofs.RouteB.D0PstarShiftedArchSesquilinearForm

noncomputable section

open Complex MeasureTheory
open scoped ENNReal

namespace Q3.RouteB.D0Pstar

/-- The shifted archimedean form is the exact whole-line multiplier integral
with the explicit B3.0N lower-bound shift. -/
theorem sourceArchimedeanShiftedSesquilinearForm_eq_integral
    (i : PairIndex) (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceArchimedeanShiftedSesquilinearForm i x y =
      ∫ t : ℝ,
        star
            (((sourceLogWindowFourierL2Isometry i x.1 :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) *
          ((sourceArchimedeanMultiplier t +
            (|Real.log Real.pi| + Real.log 4 + 6) : ℝ) : ℂ) *
          (((sourceLogWindowFourierL2Isometry i y.1 :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) := by
  rw [sourceArchimedeanShiftedSesquilinearForm_apply]
  change
    inner ℂ (sourceArchimedeanShiftedWeightedLpLinearMap i x)
        (sourceArchimedeanShiftedWeightedLpLinearMap i y) = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i x,
      coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i y] with t hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply']
  have hsq := sourceArchimedeanShiftedSqrtWeight_sq t
  have hsqC :
      (sourceArchimedeanShiftedSqrtWeight t : ℂ) ^ 2 =
        ((sourceArchimedeanMultiplier t +
          (|Real.log Real.pi| + Real.log 4 + 6) : ℝ) : ℂ) := by
    exact_mod_cast hsq
  rw [map_mul]
  have hstar :
      (starRingEnd ℂ) (sourceArchimedeanShiftedSqrtWeight t : ℂ) =
        (sourceArchimedeanShiftedSqrtWeight t : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [hstar, starRingEnd_apply]
  calc
    _ = star
          (((sourceLogWindowFourierL2Isometry i x.1 :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) *
        (sourceArchimedeanShiftedSqrtWeight t : ℂ) ^ 2 *
        (((sourceLogWindowFourierL2Isometry i y.1 :
            MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) := by
      ring
    _ = _ := by rw [hsqC]

/-- The unshifted archimedean sesquilinear form on the same exact form-domain
carrier, obtained by removing precisely the explicit B3.0N shift. -/
noncomputable def sourceArchimedeanSesquilinearForm
    (i : PairIndex) :
    sourceArchimedeanShiftedFormDomain i →ₗ⋆[ℂ]
      sourceArchimedeanShiftedFormDomain i →ₗ[ℂ] ℂ :=
  sourceArchimedeanShiftedSesquilinearForm i -
    ((|Real.log Real.pi| + Real.log 4 + 6 : ℝ) : ℂ) •
      (innerₛₗ ℂ)

@[simp]
theorem sourceArchimedeanSesquilinearForm_apply
    (i : PairIndex) (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceArchimedeanSesquilinearForm i x y =
      sourceArchimedeanShiftedSesquilinearForm i x y -
        ((|Real.log Real.pi| + Real.log 4 + 6 : ℝ) : ℂ) *
          inner ℂ x y := by
  rfl

/-- Hermitian symmetry survives exact removal of the real scalar shift. -/
theorem sourceArchimedeanSesquilinearForm_conj_symm
    (i : PairIndex) (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceArchimedeanSesquilinearForm i x y =
      star (sourceArchimedeanSesquilinearForm i y x) := by
  rw [sourceArchimedeanSesquilinearForm_apply,
    sourceArchimedeanSesquilinearForm_apply]
  change
    sourceArchimedeanShiftedSesquilinearForm i x y -
        ((|Real.log Real.pi| + Real.log 4 + 6 : ℝ) : ℂ) * inner ℂ x y =
      (starRingEnd ℂ)
        (sourceArchimedeanShiftedSesquilinearForm i y x -
          ((|Real.log Real.pi| + Real.log 4 + 6 : ℝ) : ℂ) * inner ℂ y x)
  rw [map_sub, map_mul, Complex.conj_ofReal, inner_conj_symm]
  have h := sourceArchimedeanShiftedSesquilinearForm_conj_symm i x y
  change
    sourceArchimedeanShiftedSesquilinearForm i x y =
      (starRingEnd ℂ) (sourceArchimedeanShiftedSesquilinearForm i y x) at h
  rw [← h]

/-- The unshifted form is exactly the original source archimedean multiplier
integral; the B3.0N shift is removed once and only once. -/
theorem sourceArchimedeanSesquilinearForm_eq_integral
    (i : PairIndex) (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceArchimedeanSesquilinearForm i x y =
      ∫ t : ℝ,
        star
            (((sourceLogWindowFourierL2Isometry i x.1 :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) *
          (sourceArchimedeanMultiplier t : ℂ) *
          (((sourceLogWindowFourierL2Isometry i y.1 :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) := by
  rw [sourceArchimedeanSesquilinearForm_apply,
    sourceArchimedeanShiftedSesquilinearForm_apply]
  change
    inner ℂ (sourceArchimedeanShiftedWeightedLpLinearMap i x)
          (sourceArchimedeanShiftedWeightedLpLinearMap i y) -
        ((|Real.log Real.pi| + Real.log 4 + 6 : ℝ) : ℂ) *
          inner ℂ x.1 y.1 = _
  rw [← (sourceLogWindowFourierL2Isometry i).inner_map_map x.1 y.1]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  rw [← integral_const_mul]
  rw [← integral_sub
    (MeasureTheory.L2.integrable_inner
      (sourceArchimedeanShiftedWeightedLpLinearMap i x)
      (sourceArchimedeanShiftedWeightedLpLinearMap i y))
    ((MeasureTheory.L2.integrable_inner
      (sourceLogWindowFourierL2Isometry i x.1)
      (sourceLogWindowFourierL2Isometry i y.1)).const_mul
        (((|Real.log Real.pi| + Real.log 4 + 6 : ℝ) : ℂ)))]
  apply integral_congr_ae
  filter_upwards
    [coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i x,
      coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i y] with t hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply']
  have hsq := sourceArchimedeanShiftedSqrtWeight_sq t
  have hsqC :
      (sourceArchimedeanShiftedSqrtWeight t : ℂ) ^ 2 =
        ((sourceArchimedeanMultiplier t +
          (|Real.log Real.pi| + Real.log 4 + 6) : ℝ) : ℂ) := by
    exact_mod_cast hsq
  rw [map_mul]
  have hstar :
      (starRingEnd ℂ) (sourceArchimedeanShiftedSqrtWeight t : ℂ) =
        (sourceArchimedeanShiftedSqrtWeight t : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [hstar, starRingEnd_apply]
  ring_nf
  rw [hsqC]
  push_cast
  ring

#print axioms sourceArchimedeanShiftedSesquilinearForm_eq_integral
#print axioms sourceArchimedeanSesquilinearForm
#print axioms sourceArchimedeanSesquilinearForm_apply
#print axioms sourceArchimedeanSesquilinearForm_conj_symm
#print axioms sourceArchimedeanSesquilinearForm_eq_integral

end Q3.RouteB.D0Pstar
