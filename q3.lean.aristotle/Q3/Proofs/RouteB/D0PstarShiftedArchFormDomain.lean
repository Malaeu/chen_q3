import Q3.Proofs.RouteB.D0PstarShiftedArchSqrtWeight
import Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry

noncomputable section

open Complex MeasureTheory
open scoped ENNReal

namespace Q3.RouteB.D0Pstar

private noncomputable def sourceArchimedeanShiftedWeightedImage
    (i : PairIndex) (x : H_m i) : ℝ → ℂ :=
  fun t : ℝ =>
    (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
      ((sourceLogWindowFourierL2Isometry i x :
          MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t

/-- The exact shifted archimedean form domain pulled back to `H_m i` through
B3.0L.  Membership means square-root-weighted whole-line `L²` integrability.
This is not the full-multiplier operator domain and is not identified here with
D0.2's source form domain. -/
noncomputable def sourceArchimedeanShiftedFormDomain
    (i : PairIndex) : Submodule ℂ (H_m i) where
  carrier :=
    {x | MemLp (sourceArchimedeanShiftedWeightedImage i x) 2 volume}
  zero_mem' := by
    have hEq :
        (0 : ℝ → ℂ) =ᵐ[volume]
          sourceArchimedeanShiftedWeightedImage i 0 := by
      filter_upwards
        [MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht
      simp [sourceArchimedeanShiftedWeightedImage, ht]
    exact MemLp.ae_eq hEq MemLp.zero
  add_mem' := by
    intro x y hx hy
    have hEq :
        sourceArchimedeanShiftedWeightedImage i x +
            sourceArchimedeanShiftedWeightedImage i y
          =ᵐ[volume]
        sourceArchimedeanShiftedWeightedImage i (x + y) := by
      filter_upwards
        [MeasureTheory.Lp.coeFn_add
          (sourceLogWindowFourierL2Isometry i x)
          (sourceLogWindowFourierL2Isometry i y)] with t ht
      simp only [sourceArchimedeanShiftedWeightedImage, Pi.add_apply,
        map_add, ht]
      ring
    exact MemLp.ae_eq hEq (hx.add hy)
  smul_mem' := by
    intro c x hx
    have hEq :
        c • sourceArchimedeanShiftedWeightedImage i x
          =ᵐ[volume]
        sourceArchimedeanShiftedWeightedImage i (c • x) := by
      filter_upwards
        [MeasureTheory.Lp.coeFn_smul c
          (sourceLogWindowFourierL2Isometry i x)] with t ht
      simp only [sourceArchimedeanShiftedWeightedImage, Pi.smul_apply,
        smul_eq_mul, map_smul, ht]
      ring
    exact MemLp.ae_eq hEq (hx.const_smul c)

@[simp]
theorem mem_sourceArchimedeanShiftedFormDomain_iff
    (i : PairIndex) (x : H_m i) :
    x ∈ sourceArchimedeanShiftedFormDomain i ↔
      MemLp
        (fun t : ℝ =>
          (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
            ((sourceLogWindowFourierL2Isometry i x :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
        2 volume := by
  rfl

#print axioms sourceArchimedeanShiftedFormDomain
#print axioms mem_sourceArchimedeanShiftedFormDomain_iff

end Q3.RouteB.D0Pstar
