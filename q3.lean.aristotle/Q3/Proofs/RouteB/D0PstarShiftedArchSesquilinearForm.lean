import Q3.Proofs.RouteB.D0PstarShiftedArchFormDomain

noncomputable section

open Complex MeasureTheory
open scoped ENNReal

namespace Q3.RouteB.D0Pstar

private noncomputable def shiftedWeightedImage
    (i : PairIndex) (x : H_m i) : ℝ → ℂ :=
  fun t : ℝ =>
    (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
      ((sourceLogWindowFourierL2Isometry i x :
          MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t

private theorem shiftedWeightedImage_memLp
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    MemLp (shiftedWeightedImage i x.1) 2 volume := by
  exact (mem_sourceArchimedeanShiftedFormDomain_iff i x.1).mp x.2

private noncomputable def shiftedWeightedLp
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) :=
  (shiftedWeightedImage_memLp i x).toLp (shiftedWeightedImage i x.1)

private theorem shiftedWeightedLp_add
    (i : PairIndex)
    (x y : sourceArchimedeanShiftedFormDomain i) :
    shiftedWeightedLp i (x + y) = shiftedWeightedLp i x + shiftedWeightedLp i y := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [(shiftedWeightedImage_memLp i (x + y)).coeFn_toLp,
      (shiftedWeightedImage_memLp i x).coeFn_toLp,
      (shiftedWeightedImage_memLp i y).coeFn_toLp,
      MeasureTheory.Lp.coeFn_add (shiftedWeightedLp i x) (shiftedWeightedLp i y),
      MeasureTheory.Lp.coeFn_add
        (sourceLogWindowFourierL2Isometry i x.1)
        (sourceLogWindowFourierL2Isometry i y.1)] with t hxy hx hy hadd hfourier
  simp only [shiftedWeightedLp] at hxy hx hy hadd ⊢
  rw [hxy, hadd]
  simp only [Pi.add_apply]
  rw [hx, hy]
  simp only [shiftedWeightedImage, Submodule.coe_add, map_add, hfourier,
    Pi.add_apply]
  ring

private theorem shiftedWeightedLp_smul
    (i : PairIndex) (c : ℂ)
    (x : sourceArchimedeanShiftedFormDomain i) :
    shiftedWeightedLp i (c • x) = c • shiftedWeightedLp i x := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [(shiftedWeightedImage_memLp i (c • x)).coeFn_toLp,
      (shiftedWeightedImage_memLp i x).coeFn_toLp,
      MeasureTheory.Lp.coeFn_smul c (shiftedWeightedLp i x),
      MeasureTheory.Lp.coeFn_smul c
        (sourceLogWindowFourierL2Isometry i x.1)] with t hcx hx hsmul hfourier
  simp only [shiftedWeightedLp] at hcx hx hsmul ⊢
  rw [hcx, hsmul]
  simp only [Pi.smul_apply]
  rw [hx]
  simp only [shiftedWeightedImage, Submodule.coe_smul_of_tower, map_smul,
    hfourier, Pi.smul_apply, smul_eq_mul]
  ring

/-- Multiplication by the exact nonnegative square-root of the shifted
archimedean multiplier, on the locked shifted form domain. -/
noncomputable def sourceArchimedeanShiftedWeightedLpLinearMap
    (i : PairIndex) :
    sourceArchimedeanShiftedFormDomain i →ₗ[ℂ]
      MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) where
  toFun := shiftedWeightedLp i
  map_add' := shiftedWeightedLp_add i
  map_smul' := shiftedWeightedLp_smul i

/-- The weighted linear map has the literal square-root multiplier as an
almost-everywhere representative. -/
theorem coeFn_sourceArchimedeanShiftedWeightedLpLinearMap
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    ((sourceArchimedeanShiftedWeightedLpLinearMap i x :
        MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume]
        (fun t : ℝ =>
          (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
            ((sourceLogWindowFourierL2Isometry i x.1 :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) := by
  exact (shiftedWeightedImage_memLp i x).coeFn_toLp

/-- The positive shifted archimedean sesquilinear form on its exact form-domain
carrier.  This is a form, not an associated operator or an operator-domain
claim. -/
noncomputable def sourceArchimedeanShiftedSesquilinearForm
    (i : PairIndex) :
    sourceArchimedeanShiftedFormDomain i →ₗ⋆[ℂ]
      sourceArchimedeanShiftedFormDomain i →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y =>
      (innerₛₗ ℂ)
        (sourceArchimedeanShiftedWeightedLpLinearMap i x)
        (sourceArchimedeanShiftedWeightedLpLinearMap i y))
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
    (fun x y z => by
      change
        (innerₛₗ ℂ) (sourceArchimedeanShiftedWeightedLpLinearMap i x)
            (sourceArchimedeanShiftedWeightedLpLinearMap i (y + z)) =
          (innerₛₗ ℂ) (sourceArchimedeanShiftedWeightedLpLinearMap i x)
              (sourceArchimedeanShiftedWeightedLpLinearMap i y) +
            (innerₛₗ ℂ) (sourceArchimedeanShiftedWeightedLpLinearMap i x)
              (sourceArchimedeanShiftedWeightedLpLinearMap i z)
      rw [map_add]
      exact
        ((innerₛₗ ℂ) (sourceArchimedeanShiftedWeightedLpLinearMap i x)).map_add
          (sourceArchimedeanShiftedWeightedLpLinearMap i y)
          (sourceArchimedeanShiftedWeightedLpLinearMap i z))
    (fun _ _ _ => by simp)

@[simp]
theorem sourceArchimedeanShiftedSesquilinearForm_apply
    (i : PairIndex) (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceArchimedeanShiftedSesquilinearForm i x y =
      (innerₛₗ ℂ)
        (sourceArchimedeanShiftedWeightedLpLinearMap i x)
        (sourceArchimedeanShiftedWeightedLpLinearMap i y) := by
  rfl

/-- Hermitian symmetry of the shifted archimedean form. -/
theorem sourceArchimedeanShiftedSesquilinearForm_conj_symm
    (i : PairIndex) (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceArchimedeanShiftedSesquilinearForm i x y =
      star (sourceArchimedeanShiftedSesquilinearForm i y x) := by
  rw [sourceArchimedeanShiftedSesquilinearForm_apply,
    sourceArchimedeanShiftedSesquilinearForm_apply]
  change
    inner ℂ (sourceArchimedeanShiftedWeightedLpLinearMap i x)
        (sourceArchimedeanShiftedWeightedLpLinearMap i y) =
      star (inner ℂ (sourceArchimedeanShiftedWeightedLpLinearMap i y)
        (sourceArchimedeanShiftedWeightedLpLinearMap i x))
  exact
    (inner_conj_symm
      (𝕜 := ℂ)
      (E := MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))
      (sourceArchimedeanShiftedWeightedLpLinearMap i x)
      (sourceArchimedeanShiftedWeightedLpLinearMap i y)).symm

/-- The real diagonal of the shifted archimedean form is nonnegative. -/
theorem sourceArchimedeanShiftedSesquilinearForm_re_self_nonneg
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    0 ≤ (sourceArchimedeanShiftedSesquilinearForm i x x).re := by
  rw [sourceArchimedeanShiftedSesquilinearForm_apply]
  change
    0 ≤ (inner ℂ (sourceArchimedeanShiftedWeightedLpLinearMap i x)
      (sourceArchimedeanShiftedWeightedLpLinearMap i x)).re
  exact inner_self_nonneg
    (𝕜 := ℂ)
    (E := MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))

#print axioms sourceArchimedeanShiftedWeightedLpLinearMap
#print axioms coeFn_sourceArchimedeanShiftedWeightedLpLinearMap
#print axioms sourceArchimedeanShiftedSesquilinearForm
#print axioms sourceArchimedeanShiftedSesquilinearForm_apply
#print axioms sourceArchimedeanShiftedSesquilinearForm_conj_symm
#print axioms sourceArchimedeanShiftedSesquilinearForm_re_self_nonneg

end Q3.RouteB.D0Pstar
