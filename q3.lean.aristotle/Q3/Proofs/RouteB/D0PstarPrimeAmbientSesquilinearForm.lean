import Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry
import Q3.Proofs.RouteB.D0PstarSourcePrimeModePairing
import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual
import Q3.Proofs.RouteB.D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk
import Mathlib.MeasureTheory.Function.Holder

noncomputable section

open Complex MeasureTheory
open scoped BigOperators ENNReal FourierTransform ComplexConjugate

namespace Q3.RouteB.D0Pstar

private noncomputable def sourcePrimeCosineLInf
    (k : ℕ) :
    MeasureTheory.Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound
      (show AEStronglyMeasurable
          (fun t : ℝ => (Real.cos (2 * Real.pi * t * Real.log (k : ℝ)) : ℂ))
          volume by fun_prop)
      1
      (Filter.Eventually.of_forall fun t => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)).toLp
    (fun t : ℝ => (Real.cos (2 * Real.pi * t * Real.log (k : ℝ)) : ℂ))

private theorem coeFn_sourcePrimeCosineLInf
    (k : ℕ) :
    ((sourcePrimeCosineLInf k :
        MeasureTheory.Lp ℂ ∞ (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume]
        (fun t : ℝ =>
          (Real.cos (2 * Real.pi * t * Real.log (k : ℝ)) : ℂ)) := by
  exact MemLp.coeFn_toLp _

private noncomputable def sourcePrimeCosineLpLinearMap
    (k : ℕ) :
    MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => sourcePrimeCosineLInf k • f
      map_add' := fun _ _ => MeasureTheory.Lp.add_smul _ _ _
      map_smul' := fun c f => (MeasureTheory.Lp.smul_comm c _ f).symm }
    ‖sourcePrimeCosineLInf k‖
    (fun _ => MeasureTheory.Lp.norm_smul_le _ _)

private theorem coeFn_sourcePrimeCosineLpLinearMap
    (k : ℕ) (f : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) :
    ((sourcePrimeCosineLpLinearMap k f :
        MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume]
        (fun t : ℝ =>
          (Real.cos (2 * Real.pi * t * Real.log (k : ℝ)) : ℂ) * f t) := by
  change
    (((sourcePrimeCosineLInf k • f :
        MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] _
  exact (MeasureTheory.Lp.coeFn_lpSMul (sourcePrimeCosineLInf k) f).trans
    ((coeFn_sourcePrimeCosineLInf k).fun_mul
      (Filter.EventuallyEq.rfl : (f : ℝ → ℂ) =ᵐ[volume] f))

private theorem sourcePrimeCosineLpLinearMap_inner_swap
    (k : ℕ)
    (f g : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ f (sourcePrimeCosineLpLinearMap k g) =
      inner ℂ (sourcePrimeCosineLpLinearMap k f) g := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [coeFn_sourcePrimeCosineLpLinearMap k g,
      coeFn_sourcePrimeCosineLpLinearMap k f] with t hg hf
  rw [hg, hf]
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring_nf

private noncomputable def sourcePrimeCosineSesquilinearForm
    (i : PairIndex) (k : ℕ) :
    H_m i →ₗ⋆[ℂ] H_m i →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y =>
      (innerₛₗ ℂ)
        (sourceLogWindowFourierL2Isometry i x)
        (sourcePrimeCosineLpLinearMap k
          (sourceLogWindowFourierL2Isometry i y)))
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
    (fun x y z => by
      change
        (innerₛₗ ℂ) (sourceLogWindowFourierL2Isometry i x)
            (sourcePrimeCosineLpLinearMap k
              (sourceLogWindowFourierL2Isometry i (y + z))) = _
      rw [map_add, map_add]
      exact ((innerₛₗ ℂ) (sourceLogWindowFourierL2Isometry i x)).map_add _ _)
    (fun _ _ _ => by simp)

@[simp]
private theorem sourcePrimeCosineSesquilinearForm_apply
    (i : PairIndex) (k : ℕ) (x y : H_m i) :
    sourcePrimeCosineSesquilinearForm i k x y =
      (innerₛₗ ℂ)
        (sourceLogWindowFourierL2Isometry i x)
        (sourcePrimeCosineLpLinearMap k
          (sourceLogWindowFourierL2Isometry i y)) := by
  rfl

private theorem sourcePrimeCosineSesquilinearForm_conj_symm
    (i : PairIndex) (k : ℕ) (x y : H_m i) :
    sourcePrimeCosineSesquilinearForm i k x y =
      star (sourcePrimeCosineSesquilinearForm i k y x) := by
  rw [sourcePrimeCosineSesquilinearForm_apply,
    sourcePrimeCosineSesquilinearForm_apply]
  change
    inner ℂ
        (sourceLogWindowFourierL2Isometry i x)
        (sourcePrimeCosineLpLinearMap k
          (sourceLogWindowFourierL2Isometry i y)) =
      (starRingEnd ℂ) (inner ℂ
        (sourceLogWindowFourierL2Isometry i y)
        (sourcePrimeCosineLpLinearMap k
          (sourceLogWindowFourierL2Isometry i x)))
  rw [inner_conj_symm]
  exact sourcePrimeCosineLpLinearMap_inner_swap k _ _

private noncomputable def sourcePrimeCosineContinuousSesquilinearForm
    (i : PairIndex) (k : ℕ) :
    H_m i →L⋆[ℂ] H_m i →L[ℂ] ℂ :=
  (ContinuousLinearMap.toSesqForm
      ((sourcePrimeCosineLpLinearMap k).comp
        (sourceLogWindowFourierL2Isometry i).toContinuousLinearMap)).comp
    (sourceLogWindowFourierL2Isometry i).toContinuousLinearMap

@[simp]
private theorem sourcePrimeCosineContinuousSesquilinearForm_apply
    (i : PairIndex) (k : ℕ) (x y : H_m i) :
    sourcePrimeCosineContinuousSesquilinearForm i k x y =
      (innerₛₗ ℂ)
        (sourceLogWindowFourierL2Isometry i x)
        (sourcePrimeCosineLpLinearMap k
          (sourceLogWindowFourierL2Isometry i y)) := by
  rfl

noncomputable def sourcePrimeSesquilinearForm
    (i : PairIndex) :
    H_m i →ₗ⋆[ℂ] H_m i →ₗ[ℂ] ℂ :=
  ∑ k ∈ Finset.Icc 2 i.m,
    (((ArithmeticFunction.vonMangoldt k *
        (Real.sqrt (k : ℝ))⁻¹ : ℝ) : ℂ) * 2) •
      sourcePrimeCosineSesquilinearForm i k

noncomputable def sourcePrimeContinuousSesquilinearForm
    (i : PairIndex) :
    H_m i →L⋆[ℂ] H_m i →L[ℂ] ℂ :=
  ∑ k ∈ Finset.Icc 2 i.m,
    (((ArithmeticFunction.vonMangoldt k *
        (Real.sqrt (k : ℝ))⁻¹ : ℝ) : ℂ) * 2) •
      sourcePrimeCosineContinuousSesquilinearForm i k

@[simp]
theorem sourcePrimeContinuousSesquilinearForm_apply
    (i : PairIndex) (x y : H_m i) :
    sourcePrimeContinuousSesquilinearForm i x y =
      sourcePrimeSesquilinearForm i x y := by
  classical
  simp [sourcePrimeContinuousSesquilinearForm,
    sourcePrimeSesquilinearForm]

@[simp]
theorem sourcePrimeSesquilinearForm_apply
    (i : PairIndex) (x y : H_m i) :
    sourcePrimeSesquilinearForm i x y =
      ∑ k ∈ Finset.Icc 2 i.m,
        ((ArithmeticFunction.vonMangoldt k *
            (Real.sqrt (k : ℝ))⁻¹ : ℝ) : ℂ) *
          (2 *
            (innerₛₗ ℂ)
              (sourceLogWindowFourierL2Isometry i x)
              (sourcePrimeCosineLpLinearMap k
                (sourceLogWindowFourierL2Isometry i y))) := by
  classical
  simp [sourcePrimeSesquilinearForm]
  ring

theorem sourcePrimeSesquilinearForm_conj_symm
    (i : PairIndex) (x y : H_m i) :
    sourcePrimeSesquilinearForm i x y =
      star (sourcePrimeSesquilinearForm i y x) := by
  classical
  rw [sourcePrimeSesquilinearForm_apply,
    sourcePrimeSesquilinearForm_apply]
  change
    (∑ k ∈ Finset.Icc 2 i.m,
      ((ArithmeticFunction.vonMangoldt k *
          (Real.sqrt (k : ℝ))⁻¹ : ℝ) : ℂ) *
        (2 *
          (innerₛₗ ℂ)
            (sourceLogWindowFourierL2Isometry i x)
            (sourcePrimeCosineLpLinearMap k
              (sourceLogWindowFourierL2Isometry i y)))) =
      (starRingEnd ℂ) (∑ k ∈ Finset.Icc 2 i.m,
        ((ArithmeticFunction.vonMangoldt k *
            (Real.sqrt (k : ℝ))⁻¹ : ℝ) : ℂ) *
          (2 *
            (innerₛₗ ℂ)
              (sourceLogWindowFourierL2Isometry i y)
              (sourcePrimeCosineLpLinearMap k
                (sourceLogWindowFourierL2Isometry i x))))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h := sourcePrimeCosineSesquilinearForm_conj_symm i k x y
  rw [sourcePrimeCosineSesquilinearForm_apply,
    sourcePrimeCosineSesquilinearForm_apply] at h
  simp only [map_mul, map_ofNat, Complex.conj_ofReal]
  rw [h]
  simp only [starRingEnd_apply]

theorem sourcePrimeSesquilinearForm_im_self_eq_zero
    (i : PairIndex) (x : H_m i) :
    (sourcePrimeSesquilinearForm i x x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (sourcePrimeSesquilinearForm i x x) =
    sourcePrimeSesquilinearForm i x x
  exact (sourcePrimeSesquilinearForm_conj_symm i x x).symm

private theorem sourcePrimeCosineSesquilinearForm_apply_mode_eq_integral
    (i : PairIndex) (k : ℕ) (n r : ℤ) :
    sourcePrimeCosineSesquilinearForm i k (V_n_m i n) (V_n_m i r) =
      ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * Real.log (k : ℝ)) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t := by
  rw [sourcePrimeCosineSesquilinearForm_apply]
  change
    inner ℂ
        (sourceLogWindowFourierL2Isometry i (V_n_m i n))
        (sourcePrimeCosineLpLinearMap k
          (sourceLogWindowFourierL2Isometry i (V_n_m i r))) = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [coeFn_sourceLogWindowFourierL2Isometry_apply_mode i n,
      coeFn_sourcePrimeCosineLpLinearMap k
        (sourceLogWindowFourierL2Isometry i (V_n_m i r)),
      coeFn_sourceLogWindowFourierL2Isometry_apply_mode i r] with t hn hkr hr
  rw [hn, hkr, hr]
  simp only [RCLike.inner_apply']
  ring

theorem sourcePrimeSesquilinearForm_apply_mode
    (i : PairIndex) (n r : ℤ) :
    sourcePrimeSesquilinearForm i (V_n_m i n) (V_n_m i r) =
      sourcePrimeModePairing i n r := by
  classical
  rw [sourcePrimeSesquilinearForm_apply]
  unfold sourcePrimeModePairing
  apply Finset.sum_congr rfl
  intro k _
  rw [← sourcePrimeCosineSesquilinearForm_apply i k,
    sourcePrimeCosineSesquilinearForm_apply_mode_eq_integral]

theorem sourcePrimeSesquilinearForm_apply_ccmFiniteSynthesis
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourcePrimeSesquilinearForm i
        (ccmFiniteSynthesis i c)
        (ccmFiniteSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          sourcePrimeModePairing i
            (ccmModeFinite i.N j) (ccmModeFinite i.N k) *
          d k := by
  classical
  change
    sourcePrimeSesquilinearForm i
        (∑ j, c j • V_n_m i (ccmModeFinite i.N j))
        (∑ k, d k • V_n_m i (ccmModeFinite i.N k)) = _
  simp_rw [map_sum, map_smul, map_smulₛₗ]
  simp only [starRingEnd_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, smul_eq_mul,
    sourcePrimeSesquilinearForm_apply_mode, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sourcePrimeSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmPrime
    (i : PairIndex) (c d : CCMModeFinite i.N → ℂ) :
    sourcePrimeSesquilinearForm i
        (ccmFiniteSynthesis i c)
        (ccmFiniteSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmPrimeEntryN1
            i.m (ccmModeFinite i.N j) (ccmModeFinite i.N k) : ℂ) *
          d k := by
  rw [sourcePrimeSesquilinearForm_apply_ccmFiniteSynthesis,
    sourcePrimeFiniteForm_eq_ccmPrimeMatrixForm]

#print axioms sourcePrimeSesquilinearForm
#print axioms sourcePrimeContinuousSesquilinearForm
#print axioms sourcePrimeContinuousSesquilinearForm_apply
#print axioms sourcePrimeSesquilinearForm_apply
#print axioms sourcePrimeSesquilinearForm_conj_symm
#print axioms sourcePrimeSesquilinearForm_im_self_eq_zero
#print axioms sourcePrimeSesquilinearForm_apply_mode
#print axioms sourcePrimeSesquilinearForm_apply_ccmFiniteSynthesis
#print axioms sourcePrimeSesquilinearForm_apply_ccmFiniteSynthesis_eq_ccmPrime

end Q3.RouteB.D0Pstar
