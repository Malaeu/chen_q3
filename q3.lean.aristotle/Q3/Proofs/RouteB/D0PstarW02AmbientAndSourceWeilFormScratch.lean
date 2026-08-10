import Q3.Proofs.RouteB.D0PstarW02EndpointFunctionalsScratch
import Q3.Proofs.RouteB.D0PstarW02RankTwoFormScratch
import Q3.Proofs.RouteB.D0PstarArchPrimeSesquilinearFormScratch
import Q3.Proofs.RouteB.D0PstarSourceWeilFiniteFormCCMWeilCrosswalk

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-- Literal positive endpoint value already used privately by the source-W02
proof. -/
noncomputable def sourceW02EndpointPlusModeValue
    (i : PairIndex) (n : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    logWindowZeroExtendedMode i n x *
      (Real.exp (x / 2) : ℂ)

/-- Literal negative endpoint value already used privately by the source-W02
proof. -/
noncomputable def sourceW02EndpointMinusModeValue
    (i : PairIndex) (n : ℤ) : ℂ :=
  ∫ x in Set.Icc 0 (L_m i),
    logWindowZeroExtendedMode i n x *
      (Real.exp (-x / 2) : ℂ)

theorem sourceW02PhysicalEndpointPlusFunctional_apply_modeValue
    (i : PairIndex) (n : ℤ) :
    sourceW02PhysicalEndpointPlusFunctional i (V_n_m i n) =
      sourceW02EndpointPlusModeValue i n := by
  simpa [sourceW02EndpointPlusModeValue] using
    sourceW02PhysicalEndpointPlusFunctional_apply_mode i n

theorem sourceW02PhysicalEndpointMinusFunctional_apply_modeValue
    (i : PairIndex) (n : ℤ) :
    sourceW02PhysicalEndpointMinusFunctional i (V_n_m i n) =
      sourceW02EndpointMinusModeValue i n := by
  simpa [sourceW02EndpointMinusModeValue] using
    sourceW02PhysicalEndpointMinusFunctional_apply_mode i n

/-- Bounded ambient W02 form assembled from the two explicit endpoint
functionals.  Its construction does not use the finite CCM matrix. -/
noncomputable def sourceW02AmbientContinuousSesquilinearForm
    (i : PairIndex) :
    H_m i →L⋆[ℂ] H_m i →L[ℂ] ℂ :=
  endpointRankTwoContinuousSesquilinearForm
    (sourceW02PhysicalEndpointPlusFunctional i)
    (sourceW02PhysicalEndpointMinusFunctional i)

@[simp]
theorem sourceW02AmbientContinuousSesquilinearForm_apply
    (i : PairIndex) (x y : H_m i) :
    sourceW02AmbientContinuousSesquilinearForm i x y =
      star (sourceW02PhysicalEndpointMinusFunctional i x) *
          sourceW02PhysicalEndpointPlusFunctional i y +
        star (sourceW02PhysicalEndpointPlusFunctional i x) *
          sourceW02PhysicalEndpointMinusFunctional i y := by
  rfl

theorem sourceW02AmbientContinuousSesquilinearForm_conj_symm
    (i : PairIndex) (x y : H_m i) :
    sourceW02AmbientContinuousSesquilinearForm i x y =
      star (sourceW02AmbientContinuousSesquilinearForm i y x) := by
  exact endpointRankTwoContinuousSesquilinearForm_conj_symm
    (sourceW02PhysicalEndpointPlusFunctional i)
    (sourceW02PhysicalEndpointMinusFunctional i) x y

theorem sourceW02AmbientContinuousSesquilinearForm_apply_mode
    (i : PairIndex)
    (hpair : ∀ n r,
      sourceW02ModePairing i n r =
        star (sourceW02EndpointMinusModeValue i n) *
            sourceW02EndpointPlusModeValue i r +
          star (sourceW02EndpointPlusModeValue i n) *
            sourceW02EndpointMinusModeValue i r)
    (n r : ℤ) :
    sourceW02AmbientContinuousSesquilinearForm i
        (V_n_m i n) (V_n_m i r) =
      sourceW02ModePairing i n r := by
  exact endpointRankTwoContinuousSesquilinearForm_apply_mode_eq_sourceW02
    i
    (sourceW02PhysicalEndpointPlusFunctional i)
    (sourceW02PhysicalEndpointMinusFunctional i)
    (sourceW02EndpointPlusModeValue i)
    (sourceW02EndpointMinusModeValue i)
    (sourceW02PhysicalEndpointPlusFunctional_apply_modeValue i)
    (sourceW02PhysicalEndpointMinusFunctional_apply_modeValue i)
    hpair n r

/-- Ambient W02 form restricted to the dense shifted archimedean form
domain. -/
noncomputable def sourceW02ShiftedDomainSesquilinearForm
    (i : PairIndex) :
    sourceArchimedeanShiftedFormDomain i →ₗ⋆[ℂ]
      sourceArchimedeanShiftedFormDomain i →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => sourceW02AmbientContinuousSesquilinearForm i x.1 y.1)
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
    (fun x y z => by
      change
        sourceW02AmbientContinuousSesquilinearForm i x.1 (y + z).1 =
          sourceW02AmbientContinuousSesquilinearForm i x.1 y.1 +
            sourceW02AmbientContinuousSesquilinearForm i x.1 z.1
      rw [Submodule.coe_add, map_add])
    (fun _ _ _ => by simp)

@[simp]
theorem sourceW02ShiftedDomainSesquilinearForm_apply
    (i : PairIndex)
    (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceW02ShiftedDomainSesquilinearForm i x y =
      sourceW02AmbientContinuousSesquilinearForm i x.1 y.1 := by
  rfl

/-- Exact dense-domain source Weil form: W02 + Arch - Prime. -/
noncomputable def sourceWeilSesquilinearForm
    (i : PairIndex) :
    sourceArchimedeanShiftedFormDomain i →ₗ⋆[ℂ]
      sourceArchimedeanShiftedFormDomain i →ₗ[ℂ] ℂ :=
  sourceW02ShiftedDomainSesquilinearForm i +
    sourceArchPrimeSesquilinearForm i

@[simp]
theorem sourceWeilSesquilinearForm_apply
    (i : PairIndex)
    (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceWeilSesquilinearForm i x y =
      sourceW02AmbientContinuousSesquilinearForm i x.1 y.1 +
        sourceArchPrimeSesquilinearForm i x y := by
  rfl

theorem sourceWeilSesquilinearForm_conj_symm
    (i : PairIndex)
    (x y : sourceArchimedeanShiftedFormDomain i) :
    sourceWeilSesquilinearForm i x y =
      star (sourceWeilSesquilinearForm i y x) := by
  rw [sourceWeilSesquilinearForm_apply,
    sourceWeilSesquilinearForm_apply]
  change
    sourceW02AmbientContinuousSesquilinearForm i x.1 y.1 +
        sourceArchPrimeSesquilinearForm i x y =
      (starRingEnd ℂ)
        (sourceW02AmbientContinuousSesquilinearForm i y.1 x.1 +
          sourceArchPrimeSesquilinearForm i y x)
  rw [map_add]
  have hw := sourceW02AmbientContinuousSesquilinearForm_conj_symm i x.1 y.1
  change
    sourceW02AmbientContinuousSesquilinearForm i x.1 y.1 =
      (starRingEnd ℂ)
        (sourceW02AmbientContinuousSesquilinearForm i y.1 x.1) at hw
  have ha := sourceArchPrimeSesquilinearForm_conj_symm i x y
  change
    sourceArchPrimeSesquilinearForm i x y =
      (starRingEnd ℂ) (sourceArchPrimeSesquilinearForm i y x) at ha
  rw [← hw, ← ha]

theorem sourceWeilSesquilinearForm_im_self_eq_zero
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    (sourceWeilSesquilinearForm i x x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (sourceWeilSesquilinearForm i x x) =
    sourceWeilSesquilinearForm i x x
  exact (sourceWeilSesquilinearForm_conj_symm i x x).symm

theorem sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis
    (i : PairIndex)
    (hpair : ∀ n r,
      sourceW02ModePairing i n r =
        star (sourceW02EndpointMinusModeValue i n) *
            sourceW02EndpointPlusModeValue i r +
          star (sourceW02EndpointPlusModeValue i n) *
            sourceW02EndpointMinusModeValue i r)
    (c d : CCMModeFinite i.N → ℂ) :
    sourceWeilSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWeilMatFinite i.m i.N j k : ℂ) *
          d k := by
  rw [sourceWeilSesquilinearForm_apply]
  have hw :=
    endpointRankTwoContinuousSesquilinearForm_apply_ccmFiniteSynthesis
      i
      (sourceW02PhysicalEndpointPlusFunctional i)
      (sourceW02PhysicalEndpointMinusFunctional i)
      (sourceW02EndpointPlusModeValue i)
      (sourceW02EndpointMinusModeValue i)
      (sourceW02PhysicalEndpointPlusFunctional_apply_modeValue i)
      (sourceW02PhysicalEndpointMinusFunctional_apply_modeValue i)
      hpair c d
  rw [coe_ccmFiniteShiftedFormDomainSynthesis,
    coe_ccmFiniteShiftedFormDomainSynthesis]
  change
    endpointRankTwoContinuousSesquilinearForm
        (sourceW02PhysicalEndpointPlusFunctional i)
        (sourceW02PhysicalEndpointMinusFunctional i)
        (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i d) +
      sourceArchPrimeSesquilinearForm i
        (ccmFiniteShiftedFormDomainSynthesis i c)
        (ccmFiniteShiftedFormDomainSynthesis i d) = _
  rw [hw]
  rw [sourceArchPrimeSesquilinearForm_apply_ccmFiniteSynthesis_eq_modeLedger]
  simpa only [sub_eq_add_neg, add_assoc] using
    sourceWeilFiniteForm_eq_ccmWeilMatrixForm i c d

theorem norm_sourceW02AmbientContinuousSesquilinearForm_apply_le
    (i : PairIndex) (x y : H_m i) :
    ‖sourceW02AmbientContinuousSesquilinearForm i x y‖ ≤
      ‖sourceW02AmbientContinuousSesquilinearForm i‖ * ‖x‖ * ‖y‖ := by
  calc
    ‖sourceW02AmbientContinuousSesquilinearForm i x y‖ ≤
        ‖sourceW02AmbientContinuousSesquilinearForm i x‖ * ‖y‖ :=
      (sourceW02AmbientContinuousSesquilinearForm i x).le_opNorm y
    _ ≤
        (‖sourceW02AmbientContinuousSesquilinearForm i‖ * ‖x‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right
        ((sourceW02AmbientContinuousSesquilinearForm i).le_opNorm x)
        (norm_nonneg y)

theorem norm_sourcePrimeSesquilinearForm_apply_le
    (i : PairIndex) (x y : H_m i) :
    ‖sourcePrimeSesquilinearForm i x y‖ ≤
      ‖sourcePrimeContinuousSesquilinearForm i‖ * ‖x‖ * ‖y‖ := by
  rw [← sourcePrimeContinuousSesquilinearForm_apply]
  calc
    ‖sourcePrimeContinuousSesquilinearForm i x y‖ ≤
        ‖sourcePrimeContinuousSesquilinearForm i x‖ * ‖y‖ :=
      (sourcePrimeContinuousSesquilinearForm i x).le_opNorm y
    _ ≤ (‖sourcePrimeContinuousSesquilinearForm i‖ * ‖x‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right
        ((sourcePrimeContinuousSesquilinearForm i).le_opNorm x)
        (norm_nonneg y)

/-- Explicit lower-bound constant supplied by the B3.0N archimedean shift
and the operator norms of the two bounded perturbations. -/
noncomputable def sourceWeilLowerBoundConstant (i : PairIndex) : ℝ :=
  |Real.log Real.pi| + Real.log 4 + 6 +
    ‖sourceW02AmbientContinuousSesquilinearForm i‖ +
    ‖sourcePrimeContinuousSesquilinearForm i‖

theorem sourceWeilLowerBoundConstant_nonneg (i : PairIndex) :
    0 ≤ sourceWeilLowerBoundConstant i := by
  dsimp only [sourceWeilLowerBoundConstant]
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

/-- The complete source-Weil diagonal is lower bounded on the exact dense
shifted form domain.  This is not a positivity statement. -/
theorem sourceWeilSesquilinearForm_re_self_lowerBound
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    -(sourceWeilLowerBoundConstant i * ‖(x : H_m i)‖ ^ 2) ≤
      (sourceWeilSesquilinearForm i x x).re := by
  have hwNorm :=
    norm_sourceW02AmbientContinuousSesquilinearForm_apply_le i x.1 x.1
  have hpNorm := norm_sourcePrimeSesquilinearForm_apply_le i x.1 x.1
  have hwLower :
      -(‖sourceW02AmbientContinuousSesquilinearForm i‖ *
          ‖(x : H_m i)‖ ^ 2) ≤
        (sourceW02AmbientContinuousSesquilinearForm i x.1 x.1).re := by
    have hre :=
      (abs_le.mp
        (Complex.abs_re_le_norm
          (sourceW02AmbientContinuousSesquilinearForm i x.1 x.1))).1
    have hneg := neg_le_neg hwNorm
    simpa [pow_two, mul_assoc] using hneg.trans hre
  have hpUpper :
      (sourcePrimeSesquilinearForm i x.1 x.1).re ≤
        ‖sourcePrimeContinuousSesquilinearForm i‖ *
          ‖(x : H_m i)‖ ^ 2 := by
    simpa [pow_two, mul_assoc] using
      (Complex.re_le_norm _).trans hpNorm
  have haNonneg :=
    sourceArchimedeanShiftedSesquilinearForm_re_self_nonneg i x
  have hinner :
      (inner ℂ x x).re = ‖(x : H_m i)‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  rw [sourceWeilSesquilinearForm_apply,
    sourceArchPrimeSesquilinearForm_apply,
    sourceArchimedeanSesquilinearForm_apply]
  simp only [add_re, sub_re, mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [hinner]
  dsimp only [sourceWeilLowerBoundConstant]
  nlinarith

#print axioms sourceW02AmbientContinuousSesquilinearForm
#print axioms sourceW02AmbientContinuousSesquilinearForm_conj_symm
#print axioms sourceW02AmbientContinuousSesquilinearForm_apply_mode
#print axioms sourceWeilSesquilinearForm
#print axioms sourceWeilSesquilinearForm_conj_symm
#print axioms sourceWeilSesquilinearForm_im_self_eq_zero
#print axioms sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis
#print axioms sourceWeilLowerBoundConstant_nonneg
#print axioms sourceWeilSesquilinearForm_re_self_lowerBound

end Q3.RouteB.D0Pstar
