import Q3.Proofs.RouteB.D0PstarShiftedArchFormDomainDensity
import Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual
import Q3.Proofs.RouteB.D0PstarSourceArchFiniteFormCCMWRCrosswalk

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

noncomputable def sourceArchimedeanShiftedWeightedLpLinearMap
    (i : PairIndex) :
    sourceArchimedeanShiftedFormDomain i →ₗ[ℂ]
      MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) where
  toFun := shiftedWeightedLp i
  map_add' := shiftedWeightedLp_add i
  map_smul' := shiftedWeightedLp_smul i

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

/-- Scratch preflight: remove the explicit B3.0N lower-bound shift from the
shifted positive form, on the same exact form-domain carrier. -/
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

noncomputable def sourceArchimedeanModeInShiftedFormDomain
    (i : PairIndex) (n : ℤ) :
    sourceArchimedeanShiftedFormDomain i :=
  ⟨V_n_m i n, V_n_m_mem_sourceArchimedeanShiftedFormDomain i n⟩

theorem sourceArchimedeanSesquilinearForm_apply_mode
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanSesquilinearForm i
        (sourceArchimedeanModeInShiftedFormDomain i n)
        (sourceArchimedeanModeInShiftedFormDomain i r) =
      sourceArchimedeanModePairing i n r := by
  rw [sourceArchimedeanSesquilinearForm_eq_integral,
    sourceArchimedeanModePairing]
  apply integral_congr_ae
  filter_upwards
    [coeFn_sourceLogWindowFourierL2Isometry_apply_mode i n,
      coeFn_sourceLogWindowFourierL2Isometry_apply_mode i r] with t hn hr
  change
    star
          (((sourceLogWindowFourierL2Isometry i (V_n_m i n) :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) *
        (sourceArchimedeanMultiplier t : ℂ) *
        (((sourceLogWindowFourierL2Isometry i (V_n_m i r) :
            MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) = _
  rw [hn, hr]
  rw [starRingEnd_apply]

noncomputable def ccmFiniteShiftedFormDomainSynthesis
    (i : PairIndex) :
    (CCMModeFinite i.N → ℂ) →ₗ[ℂ]
      sourceArchimedeanShiftedFormDomain i where
  toFun c :=
    ∑ j, c j •
      sourceArchimedeanModeInShiftedFormDomain i (ccmModeFinite i.N j)
  map_add' := by
    intro c d
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      smul_smul, Finset.smul_sum]

theorem coe_ccmFiniteShiftedFormDomainSynthesis
    (i : PairIndex) (c : CCMModeFinite i.N → ℂ) :
    (ccmFiniteShiftedFormDomainSynthesis i c : H_m i) =
      ccmFiniteSynthesis i c := by
  simp [ccmFiniteShiftedFormDomainSynthesis,
    sourceArchimedeanModeInShiftedFormDomain, ccmFiniteSynthesis]

theorem sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourceArchimedeanSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          sourceArchimedeanModePairing i
            (ccmModeFinite i.N j) (ccmModeFinite i.N k) *
          d k := by
  classical
  change
    sourceArchimedeanSesquilinearForm i
        (∑ j, c j • sourceArchimedeanModeInShiftedFormDomain i
          (ccmModeFinite i.N j))
        (∑ k, d k • sourceArchimedeanModeInShiftedFormDomain i
          (ccmModeFinite i.N k)) = _
  simp_rw [map_sum, map_smul, map_smulₛₗ]
  simp only [starRingEnd_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, smul_eq_mul,
    sourceArchimedeanSesquilinearForm_apply_mode, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis_eq_neg_ccmWR
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourceArchimedeanSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) =
      -(∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWREntry
            (L_m i) (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ) *
          d k) := by
  rw [sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis,
    sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm]

#print axioms sourceArchimedeanSesquilinearForm
#print axioms sourceArchimedeanSesquilinearForm_apply
#print axioms sourceArchimedeanSesquilinearForm_conj_symm
#print axioms sourceArchimedeanSesquilinearForm_eq_integral
#print axioms sourceArchimedeanSesquilinearForm_apply_mode
#print axioms ccmFiniteShiftedFormDomainSynthesis
#print axioms sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis
#print axioms sourceArchimedeanSesquilinearForm_apply_ccmFiniteSynthesis_eq_neg_ccmWR

#print axioms coeFn_sourceArchimedeanShiftedWeightedLpLinearMap
#print axioms sourceArchimedeanShiftedSesquilinearForm_conj_symm
#print axioms sourceArchimedeanShiftedSesquilinearForm_re_self_nonneg
#print axioms sourceArchimedeanShiftedSesquilinearForm_eq_integral

#print axioms sourceArchimedeanShiftedWeightedLpLinearMap
#print axioms sourceArchimedeanShiftedSesquilinearForm
#print axioms sourceArchimedeanShiftedSesquilinearForm_apply

end Q3.RouteB.D0Pstar
